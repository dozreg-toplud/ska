import lemmas.Ska.CompUnproxyFill
import lemmas.Ska.CompNestFinalP
import lemmas.Ska.CompFragX
import lemmas.Ska.CompSevenOne

/-!
# The final pass for runs that make proxies

`RunOKU` is `RunOKP` for a run that may make proxy registers: `cond` grows
only by fresh entries (`CondFresh`, in place of `RunOKP.cnd`), no register of
a need of the result (the sure need, and the need of every lazy entry) is a
key of the run's final `cond` (fact (ii) of README Gaps 12.2), and `sem`
compares the program with the Gen blocks unproxied by that `cond`
(`AgreeU`).  `RunOKP.toU`: a run that makes no proxy from a state with an
empty `cond` meets it, so everything the `R` theorems cover is covered here.

`finishLF_compDoneU`: the final pass with the whole of `+to-straight`
(`toStraightF`, proxies or not) meets the relation at the entry for any nomm
whose run for `%done` from `gen0` meets `RunOKU`.  The fill ops of the final
pass mention only the input registers (above every key, `CondBelow`), the
needs of the result (no keys, by `ncond` and `econd`) and fresh registers
(`coerceLazyL_regs`), so unproxying leaves them unchanged (`unproxy_ops`),
which is the lazy-block clause of `AgreeU` and the `hag` of
`toStraightF_entryU`.  The program the code is compared with is the Gen
blocks unproxied (`mapVals`), with the entry block taken without its fill
ops.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## A map with every value mapped -/

/-- One step of `mapVals`. -/
def mapStep {ν μ : Type} (u : ν → μ) (m : Map ν) (acc : Map μ) (k : Nat) : Map μ :=
  match HoonMap.get m k with
  | some b => HoonMap.put acc k (u b)
  | none => acc

/-- A map with every value mapped, built over the keys. -/
def mapVals {ν μ : Type} (u : ν → μ) (m : Map ν) : Map μ :=
  (HoonMapKeys.keys m).foldl (mapStep u m) HoonMap.empty

theorem get_foldl_mapStep {ν μ : Type} (u : ν → μ) (m : Map ν) : ∀ (ks : List Nat) (acc : Map μ) (k : Nat),
    HoonMap.get (ks.foldl (mapStep u m) acc) k =
      if k ∈ ks ∧ (HoonMap.get m k).isSome then (HoonMap.get m k).map u else HoonMap.get acc k
  | [], acc, k => by simp
  | k' :: ks, acc, k => by
    rw [List.foldl_cons, get_foldl_mapStep u m ks]
    by_cases hs : (HoonMap.get m k).isSome
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
      by_cases hk : k ∈ ks
      · simp [hk, hb]
      · by_cases e : k = k'
        · subst e; simp [mapStep, hb, HoonMap.get_put]
        · simp only [hk, false_and, if_false, List.mem_cons, e, false_or, hb, Option.isSome_some, and_true]
          cases hm : HoonMap.get m k' <;> simp [mapStep, hm, HoonMap.get_put, e]
    · have hn : HoonMap.get m k = Option.none := by simpa using hs
      simp only [hn, Option.isSome_none, Bool.false_eq_true, and_false, if_false]
      cases hm : HoonMap.get m k' with
      | none => simp [mapStep, hm]
      | some b' =>
        have e : k ≠ k' := fun e => by rw [e, hm] at hn; cases hn
        simp [mapStep, hm, HoonMap.get_put, e]

/-- **The mapped map holds the mapped values.** -/
theorem get_mapVals {ν μ : Type} (u : ν → μ) (m : Map ν) (k : Nat) :
    HoonMap.get (mapVals u m) k = (HoonMap.get m k).map u := by
  rw [mapVals, get_foldl_mapStep]
  by_cases hs : (HoonMap.get m k).isSome
  · rw [if_pos ⟨(HoonMapKeys.mem_keys m k).mpr hs, hs⟩]
  · have hn : HoonMap.get m k = Option.none := by simpa using hs
    rw [if_neg (fun h => hs h.2), hn, HoonMap.get_empty]; rfl

/-- The jumps of an unproxied block are those of the block, renamed. -/
theorem downRk_unproxy {ρ : Nat → Nat} {k : Nat} {b : Blob} (cond : Map (Nat × List Nat))
    (h : 1 ≤ k ∧ ∀ j ∈ finJumps b.fin, 1 ≤ j.there ∧ ρ j.there < ρ k) :
    1 ≤ k ∧ ∀ j ∈ finJumps (unproxyBlob cond b).fin, 1 ≤ j.there ∧ ρ j.there < ρ k := by
  refine ⟨h.1, fun j hj => ?_⟩
  simp only [unproxyBlob, renBlob, finJumps_renFin, List.mem_map] at hj
  obtain ⟨j0, hj0, rfl⟩ := hj
  exact h.2 j0 hj0

/-! ## `RunOKU` -/

/-- **The relation for one run of `runL` for `%done` or `%pick` that may
make proxies.** -/
structure RunOKU (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t g1.cond ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s)

/-- **A run that makes no proxy, from a state with an empty `cond`, meets
`RunOKU`.** -/
theorem RunOKP.toU {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKP lib nm goal g0 g1 nex) (hc : ∀ k, HoonMap.get g0.cond k = Option.none) :
    RunOKU lib nm goal g0 g1 nex := by
  have hc1 : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by rw [R.cnd]; exact hc k
  exact ⟨R.ext, R.grow, condFresh_of_eq R.ext.1 R.cnd, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs,
    R.nodup, R.size, R.nec, fun r _ => hc1 r, fun _ _ r _ => hc1 r,
    fun c ned σ O st t gul s0 s ag => R.sem c ned σ O st t gul s0 s ((agreeU_empty hc1).mp ag)⟩

/-! ## The final pass -/

/-- **The final pass meets the relation at the entry**, for any nomm whose
run for `%done` from `gen0` meets `RunOKU`, proxies or not. -/
theorem finishLF_compDoneU (lib : Lib) {nm : Nomm}
    (hR : ∀ {nex : NextL S} {g4 : Gen Map}, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g4) →
      RunOKU (Map := Map) lib nm CGoal.done gen0 g4 nex)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord less bake = some c') : CompDoneOn lib c' nm (CapeAxes less) := by
  unfold finishLF at h
  obtain ⟨⟨nex, g4⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  have R := hR h1
  simp only at h
  split at h
  · cases h
  rename_i hargs
  simp only [ne_eq, Decidable.not_not] at hargs
  obtain ⟨⟨nedF, g5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [hbake, List.map_nil] at h
  obtain ⟨⟨u8, g8⟩, h8, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u9, g9⟩, h9, hts⟩ := Option.bind_eq_some_iff.mp h
  have hrun := isRun_needOrdAllocRegs h5
  have c5 := (kc_needOrdAllocRegs ord).keep g4 nedF g5 h5
  have c8 := (kc_coerceLazyL nedF less _ _).keep g5 u8 g8 h8
  have c9 := (KC.addOps' _ _).keep g8 u9 g9 h9
  have hc9 : g9.cond = g4.cond := by rw [c9, c8, c5]
  rw [hc9] at hts
  have d4 : g4.drop = false := R.ext.2.2.1
  obtain ⟨⟨k5, rfl⟩, l5, dist5, mem5⟩ := needOrdAllocRegs_spec ord g4 _ nedF h5
  simp only at l5 mem5
  -- the keys of `cond` lie below `g4.re`
  have cb4 : CondBelow g4 := R.cfr.below (fun k hk => by simp [gen0, HoonMap.get_empty] at hk)
  have nk : ∀ x, g4.re ≤ x → HoonMap.get g4.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g4.cond x with
    | none => rfl
    | some _ => have := cb4 x (by simp [e]); omega
  have PA : ∀ (L : Need), (∀ r, NMem L r → HoonMap.get g4.cond r = Option.none) → ∀ A : List Pole,
      RegsIn (fun x => NMem nedF x ∨ NMem L x ∨ g4.re ≤ x) A → A.map (renPole (unproxy g4.cond)) = A :=
    fun L hL A hA => unproxy_ops (hA.mono fun x hx => by
      rcases hx with hx | hx | hx
      · exact nk x (mem5 x hx).1
      · exact hL x hx
      · exact nk x hx)
  obtain ⟨B, fin, hB⟩ : ∃ B fin, HoonMap.get g4.blocks nex.th.there = some ⟨[], B, fin⟩ := by
    rcases R.ent with ⟨b, hb, hp, _⟩ | e
    · exact ⟨b.body, b.fin, by rw [hb, ← hp]⟩
    · exact e.elim
  have regs4 : ∀ r, NMem nex.laz.sure.ned r → r < g4.re := fun r hr => (R.regs r hr).2
  have hnd : (nex.th.there :: (entries nex.laz).map Prod.fst).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨e, he, he'⟩ := List.mem_map.mp hm
      have := (R.labs e he).2.1; omega, R.nodup⟩
  -- `+coerce-lazy`
  obtain ⟨bo8, dr8, re8, oth8, Froot, Fents⟩ := coerceLazyL_spec h8 d4 dist5 (fun r hr => (mem5 r hr).2)
    ⟨R.dist, fun r hr => Nat.lt_of_lt_of_le (regs4 r hr) l5,
      fun r hr hl => by have := (mem5 r hr).1; have := regs4 r hl; omega⟩
    (fun e he => ⟨(R.eregs e he).1, fun r hr => Nat.lt_of_lt_of_le ((R.eregs e he).2 r hr).2 l5,
      fun r hr hl => by have := (mem5 r hr).1; have := ((R.eregs e he).2 r hl).2; omega⟩) hnd
  obtain ⟨Rroot, Rents⟩ := coerceLazyL_regs h8 d4 hnd
  have d8 : g8.drop = false := dr8.trans d4
  have F9 := front_addOps h9 d8
  obtain ⟨A0, hA0, semA0⟩ := Froot B fin hB
  have uA0 : A0.map (renPole (unproxy g4.cond)) = A0 := by
    obtain ⟨A0', hA0', RA0⟩ := Rroot B fin hB
    rw [hA0] at hA0'
    simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hA0'
    rw [List.append_cancel_right hA0'.1]
    exact PA _ R.ncond A0' (RA0.mono fun x hx => hx.elim Or.inl fun hx => hx.elim (fun h => Or.inr (Or.inl h))
      fun h => Or.inr (Or.inr (Nat.le_trans l5 h)))
  have hB9 : HoonMap.get g9.blocks nex.th.there = some ⟨[], A0 ++ B, fin⟩ := by
    have := F9.blk _ _ hA0; simpa using this
  have hents : ∀ e ∈ entries nex.laz, ∃ A th, HoonMap.get g4.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
      HoonMap.get g9.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧ A.map (renPole (unproxy g4.cond)) = A ∧
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t s,
        CapeAxes less s → FillSem lib O c gul st t nedF k5 e.2.sure A s s := by
    intro e he
    obtain ⟨_, lt, th, hth⟩ := R.labs e he
    obtain ⟨A, hA, sA⟩ := Fents e he [] (Termin.hop th) hth
    obtain ⟨A', hA', RA⟩ := Rents e he [] (Termin.hop th) hth
    rw [hA] at hA'
    simp only [Option.some.injEq, Blob.mk.injEq, true_and, List.append_nil] at hA'
    refine ⟨A, th, hth, ?_, ?_, sA⟩
    · rw [F9.other _ (by omega), hA, List.append_nil]
    · rw [hA'.1]
      exact PA _ (R.econd e he) A' (RA.mono fun x hx => hx.elim Or.inl fun hx => hx.elim
        (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr (Nat.le_trans l5 h)))
  have oth9 : ∀ o, o ≠ nex.th.there → o ∉ (entries nex.laz).map Prod.fst →
      HoonMap.get g9.blocks o = HoonMap.get g4.blocks o := fun o h1 h2 =>
    (F9.other o h1).trans (oth8 o h1 h2)
  -- every block goes down
  have D4 : DownRk (upRk g4.blocks) g4.blocks := downRk_gen0 R.grow
  have D9 : DownRk (upRk g4.blocks) g9.blocks := downRk_of_fins D4 fun k b' hk => by
    by_cases e1 : k = nex.th.there
    · subst e1; rw [hB9] at hk; cases hk; exact ⟨_, hB, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e2
      obtain ⟨A, th, h4, h9', _⟩ := hents e he
      rw [h9'] at hk; cases hk; exact ⟨_, h4, rfl⟩
    · rw [oth9 k e1 e2] at hk; exact ⟨b', hk, rfl⟩
  -- the program: the unproxied blocks, with the entry block of the run
  let c1 : Straight Map := ⟨NeedOrd.none, 0, HoonMap.put (mapVals (unproxyBlob g4.cond) g9.blocks) nex.th.there
    (unproxyBlob g4.cond ⟨[], B, fin⟩)⟩
  have hc1o : HoonMap.get c1.blocks nex.th.there = some (unproxyBlob g4.cond ⟨[], B, fin⟩) := by
    simp [c1, HoonMap.get_put]
  have hag : ∀ k, k ≠ nex.th.there → HoonMap.get c1.blocks k = (HoonMap.get g9.blocks k).map (unproxyBlob g4.cond) :=
    fun k hk => by simp [c1, HoonMap.get_put, hk, get_mapVals]
  have D1 : DownRk (upRk g4.blocks) c1.blocks := by
    intro k b hk
    by_cases e : k = nex.th.there
    · subst e; rw [hc1o] at hk; cases hk; exact downRk_unproxy _ (D4 _ _ hB)
    · rw [hag k e] at hk
      obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact downRk_unproxy _ (D9 k b0 hb0)
  obtain ⟨_, start, hst, hent⟩ := toStraightF_entryU hts hrun D9 D1 hag
  rw [hB9] at hst; cases hst
  intro σ O st s args t gul hP hsp
  obtain ⟨R0, hR0, he⟩ := hent lib O st s args t gul hsp
  rw [he]
  have hub : unproxyBlob g4.cond ⟨[], A0 ++ B, fin⟩ =
      ⟨[], A0 ++ B.map (renPole (unproxy g4.cond)), renFin (unproxy g4.cond) fin⟩ := by
    simp only [unproxyBlob, renBlob, List.map_append, uA0, List.map_nil]
  rw [hub]
  have hj : nex.th = jmp0 nex.th.there := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hargs; simp at hargs; subst hargs; rfl
  have ag : AgreeU lib O c1 gul st t g4.cond nedF gen0 g4 nex.laz s s := by
    refine ⟨fun o _ _ hnl => ?_, fun e he => ?_⟩
    · by_cases e : o = nex.th.there
      · subst e; rw [hc1o, hB]; rfl
      · rw [hag o e, oth9 o e hnl]
    · obtain ⟨A, th, h4, h9', uA, sA⟩ := hents e he
      refine ⟨A, th, h4, ?_, (sA lib σ O c1 gul st t s hP).mono l5⟩
      rw [hag _ (by have := (R.labs e he).2.1; omega), h9']
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, uA, renFin]
  have dj : ∀ x, NMem nedF x → ¬ NMem nex.laz.sure.ned x := fun x hx hl => by
    have := (mem5 x hx).1; have := regs4 x hl; omega
  obtain ⟨SoF, SoC⟩ := semA0 lib σ O c1 gul st t s hP R0 hR0
  rw [pureTone]
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := SoF fo
    rw [hr1]
    have hn1 : HoldsN nedF R1 s := HoldsN.agree nedF (fun x hx => kr1 x (Or.inl hx) (dj x hx)) hR0
    have := R.sem c1 nedF σ O st t gul s s ag (fun r hr => (mem5 r hr).1) R1 hh1 hn1
    simp only [GoalSem] at this
    rw [hj, goJ_jmp0 _ _ _ _ hc1o] at this
    exact this
  · rw [SoC fo, R.nec s fo]; rfl

/-- **The final pass meets the contract**, for any nomm whose run for
`%done` from `gen0` meets `RunOKU`, when nothing is baked and the bell's cape
has no `[| |]`. -/
theorem finishLF_bellContractU {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hR : ∀ {nex : NextL S} {g4 : Gen Map}, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g4) →
      RunOKU (Map := Map) lib nm CGoal.done gen0 g4 nex)
    {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' := by
  have hc' := finishLF_compDoneU lib hR hbake h
  refine bellContract_of_compDoneOn hok hp hA (fun σ O st s args t gul hs hsp => ?_) N
  rw [hbl] at hs
  exact hc' σ O st s args t gul (fun axe h1 ha => capeAxes_of_fits axe h1 cape data s hn hs ha) hsp

theorem gen0_cond_none (k : Nat) : HoonMap.get (gen0 : Gen Map).cond k = Option.none := by
  simp [gen0, HoonMap.get_empty]

/-- **`finishLF_bellContractR` from the `U` theorem**: every run that meets
`RunOKP` from `gen0` meets `RunOKU`. -/
theorem finishLF_bellContractR_U {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hR : ∀ {nex : NextL S} {g4 : Gen Map}, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g4) →
      RunOKP (Map := Map) lib nm CGoal.done gen0 g4 nex)
    {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractU hok hp hA (fun h1 => (hR h1).toU gen0_cond_none) hbl hn hbake h N

/-- **`finishLF_bellContractX` through `RunOKU`.** -/
theorem finishLF_bellContractXU {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragX (S := S) nm) (hcount : sixCount nm ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractR_U hok hp hA
    (fun h1 => (runX_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h1) hbl hn hbake h N

/-- **`finishLF_bellContract71` through `RunOKU`.** -/
theorem finishLF_bellContract71U {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {k : Noun} {q : Nomm} (hp : (Nomm.n7 (Nomm.n1 k) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n1 k) q))
    (hf : FragX (S := S) q) (hcount : sixCount q ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n1 k) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' :=
  finishLF_bellContractR_U hok hp hA
    (fun h1 => runOKP_seven1 lib (runX_ok lib hf).1 hcount (by simp [gen0]) rfl upBelow_gen0 h1) hbl hn hbake h N

end Comp
end SkaModel
end Formalization
