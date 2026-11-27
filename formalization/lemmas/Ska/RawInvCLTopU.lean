import lemmas.Ska.RawInvCLRunL
import lemmas.Ska.RawInvStX
import lemmas.Ska.CompDirectMEq

/-!
# Raw `+comp` output with calls: the whole-subject pass

README Gaps 14 (b), track D.  `finishLUC` (`+compile-unary` with `runLC`)
on `PlainN`: the run under `%done` from `gen0`, `+kerf` (a hop block `o`,
`+kern` from a fresh register `sub`), then `+to-straight`, which on the
input run `[sub]` renames by `renReg sub 1 ∘ unproxy` (`toStraightF_run`).
The proof goes through the unproxied blocks `unpM g2` of the state after
`+kerf`, as `optIn_finishLUX` does on `FragX`:

* the liveness comes from the run-level spec: `liveRun_plain_topOfL` (the
  top run's `JL` and `LiveC` under `%done`, from `SplitSpecL` and
  `IntoSpecL`) and `kerfSpecL` (`+kerf` gives `IL` of "`sub` at `o`", and
  what is live at `o` with `sub` killed is what the run's result leaves
  live, which is nothing): only `sub` is live at `o` (`tu_live`);
* `Down`, `ArityOK`, `TwoNA` come from `ATS` of the state after `+kerf`
  (`IL.ats`), through the renaming (`tu_down`, `tu_arity`, `tu_twoNA`);
* unproxying fixes every defined register (a key of `cond` is defined by no
  block, `IL.cond`), so the definitions of the unproxied blocks are the raw
  ones (`tu_defs`).

**Open (checked, not proved): `TopSAU`**, the single-assignment facts of the
raw blocks after the top `+kerf`: every register has at most one definition
in the whole map (`BlkNodup`, `Cross`), no op is a trace hint (`NoTr`), and
every jump argument is defined by its own block (`ArgsHere`; it gives
`DownPar` with `Cross` and `Down`, `tu_downPar`).  No run-level invariant of
`runLC` carries them yet (track C's `SIP` is for `runL`).  Checked on all
2,856 `PlainN` nomms of `enumCX` (`chkSA` of `RawInvCLCheckSA.lean`:
2,856 hold, 0 fail; the same at the end of the run; 528 of them have a jump
with an argument, 1,927 have proxies).

* **`optIn_finishLUC_of`**: `OptIn` of the output, from `SplitSpecL`,
  `IntoSpecL` and `TopSAU`.
* **`readsIn_finishLUC_of`**: `ReadsIn` at the argument count `1`.
* `plainN_noDirect` (so `finishLUCM` is `finishLUC` on `PlainN`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `PlainN` has no direct call -/

theorem plainN_noDirect : ∀ (nm : Nomm), PlainN nm → nm.noDirect = true
  | Nomm.n0 _, _ => rfl
  | Nomm.n1 _, _ => rfl
  | Nomm.n3 p, h => by simp only [Nomm.noDirect]; exact plainN_noDirect p h
  | Nomm.n4 p, h => by simp only [Nomm.noDirect]; exact plainN_noDirect p h
  | Nomm.n5 p q, h => by simp only [Nomm.noDirect, plainN_noDirect p h.1, plainN_noDirect q h.2, Bool.and_self]
  | Nomm.cons p q, h => by simp only [Nomm.noDirect, plainN_noDirect p h.1, plainN_noDirect q h.2, Bool.and_self]
  | Nomm.n7 p q, h => by simp only [Nomm.noDirect, plainN_noDirect p h.1, plainN_noDirect q h.2, Bool.and_self]
  | Nomm.n10 _ v q, h => by simp only [Nomm.noDirect, plainN_noDirect v h.1, plainN_noDirect q h.2, Bool.and_self]
  | Nomm.n2 p q Option.none, h => by
    simp only [Nomm.noDirect, Option.isNone_none, plainN_noDirect p h.1, plainN_noDirect q h.2, Bool.and_self]
  | Nomm.n2 _ _ (some _), h => h.elim
  | Nomm.n6 _ _ _, h => h.elim
  | Nomm.n11s _ _ _, h => h.elim
  | Nomm.n11d _ _ _ _, h => h.elim
  | Nomm.n12 _ _, h => h.elim
  | Nomm.mean _ _ _ _ _, h => h.elim

/-! ## The open facts -/

/-- **Single assignment of a map of blocks**, with no trace op and every
jump argument defined by its own block. -/
structure SAB (bl : Map Blob) : Prop where
  nd : BlkNodup bl
  cr : Cross bl
  tr : NoTr bl
  args : ∀ k b j a, HoonMap.get bl k = some b → j ∈ getJmps b.fin → some a ∈ j.args → a ∈ blockDefs b

/-- **Open (checked on `PlainN`): `SAB` of the raw blocks after the top run
and its `+kerf`.** -/
def TopSAU (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (nm : Nomm) : Prop :=
  ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
    (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2) → SAB g2.blocks

/-! ## Renamed blocks -/

section Ren

variable {u : Nat → Nat} {bl : Map Blob}

theorem tu_get {k : Nat} {b : Blob} (h : HoonMap.get (mapVals (renBlob u) bl) k = some b) :
    ∃ b0, HoonMap.get bl k = some b0 ∧ b = renBlob u b0 := by
  rw [get_mapVals] at h
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b0, hb0, rfl⟩

theorem tu_jmp {b0 : Blob} {j : Jmp} (h : j ∈ getJmps (renBlob u b0).fin) :
    ∃ j0 ∈ getJmps b0.fin, j = renJmp u j0 := by
  simp only [renBlob, getJmps_renFin, List.mem_map] at h
  obtain ⟨j0, h0, rfl⟩ := h
  exact ⟨j0, h0, rfl⟩

theorem tu_down (h : Down bl) (u : Nat → Nat) : Down (mapVals (renBlob u) bl) := by
  intro k b hb
  obtain ⟨b0, hb0, rfl⟩ := tu_get hb
  obtain ⟨l1, J⟩ := h k b0 hb0
  refine ⟨l1, fun j hj => ?_⟩
  rw [← getJmps_eq] at hj
  obtain ⟨j0, h0, rfl⟩ := tu_jmp hj
  exact J j0 (by rw [← getJmps_eq]; exact h0)

theorem tu_arity (h : Compiler.ArityOK bl) (u : Nat → Nat) : Compiler.ArityOK (mapVals (renBlob u) bl) := by
  intro o b j b2 hb hj hb2
  obtain ⟨b0, hb0, rfl⟩ := tu_get hb
  obtain ⟨j0, h0, rfl⟩ := tu_jmp hj
  obtain ⟨b20, hb20, rfl⟩ := tu_get hb2
  have := h o b0 j0 b20 hb0 h0 hb20
  simp only [renJmp, renBlob, List.length_map]
  exact this

theorem twoWay_renFin (u : Nat → Nat) (f : Termin) : Compiler.twoWay (renFin u f) = Compiler.twoWay f := by
  cases f <;> rfl

theorem tu_twoNA (h : Compiler.TwoNA bl) (u : Nat → Nat) : Compiler.TwoNA (mapVals (renBlob u) bl) := by
  intro o b j hb ht hj
  obtain ⟨b0, hb0, rfl⟩ := tu_get hb
  obtain ⟨j0, h0, rfl⟩ := tu_jmp hj
  have ht0 : Compiler.twoWay b0.fin = true := by rw [← twoWay_renFin u]; exact ht
  simp only [renJmp, h o b0 j0 hb0 ht0 h0, List.map_nil]

/-- The definitions of a renamed block are the raw ones when the renaming
fixes every defined register. -/
theorem tu_defs (uD : ∀ x, Defd bl x → u x = x) {k : Nat} {b0 : Blob} (hb0 : HoonMap.get bl k = some b0) :
    blockDefs (renBlob u b0) = blockDefs b0 := by
  rw [blockDefs_renBlob]; exact map_fix (fun x hx => uD x (defd_iff.mpr ⟨k, b0, hb0, hx⟩))

theorem tu_defd (uD : ∀ x, Defd bl x → u x = x) {y : Nat} (h : Defd (mapVals (renBlob u) bl) y) : Defd bl y := by
  obtain ⟨k, b, hk, hm⟩ := defd_iff.mp h
  obtain ⟨b0, hb0, rfl⟩ := tu_get hk
  rw [tu_defs uD hb0] at hm
  exact defd_iff.mpr ⟨k, b0, hb0, hm⟩

theorem tu_nodup (uD : ∀ x, Defd bl x → u x = x) (h : BlkNodup bl) : BlkNodup (mapVals (renBlob u) bl) := by
  intro k b hk
  obtain ⟨b0, hb0, rfl⟩ := tu_get hk
  rw [tu_defs uD hb0]; exact h k b0 hb0

theorem tu_cross (uD : ∀ x, Defd bl x → u x = x) (h : Cross bl) : Cross (mapVals (renBlob u) bl) := by
  intro k k' b b' y hk hk' hne m m'
  obtain ⟨b0, hb0, rfl⟩ := tu_get hk
  obtain ⟨b0', hb0', rfl⟩ := tu_get hk'
  rw [tu_defs uD hb0] at m; rw [tu_defs uD hb0'] at m'
  exact h k k' b0 b0' y hb0 hb0' hne m m'

theorem tu_noTr (h : NoTr bl) (u : Nat → Nat) : NoTr (mapVals (renBlob u) bl) := by
  intro k b hk op hop
  obtain ⟨b0, hb0, rfl⟩ := tu_get hk
  simp only [renBlob, List.mem_map] at hop
  obtain ⟨op0, h0, rfl⟩ := hop
  rw [tr_ren]; exact h k b0 hb0 op0 h0

/-- **`DownPar` from single assignment**: a jump argument is defined by the
jumping block, a parameter by its own block, and a block reached from the
target lies below the jumping block. -/
theorem tu_downPar (uD : ∀ x, Defd bl x → u x = x) (hD : Down bl) (hx : Cross bl)
    (ha : ∀ k b j a, HoonMap.get bl k = some b → j ∈ getJmps b.fin → some a ∈ j.args → a ∈ blockDefs b) :
    DownPar (mapVals (renBlob u) bl) := by
  intro y b j hb hj r hr z bz hz hbz hpar
  obtain ⟨b0, hb0, rfl⟩ := tu_get hb
  obtain ⟨j0, h0, rfl⟩ := tu_jmp hj
  simp only [renJmp, List.mem_map] at hr
  obtain ⟨oa, hoa, ea⟩ := hr
  cases oa with
  | none => cases ea
  | some a =>
    simp only [Option.map_some, Option.some.injEq] at ea
    subst ea
    have ad : a ∈ blockDefs b0 := ha y b0 j0 a hb0 h0 hoa
    have ua : u a = a := uD a (defd_iff.mpr ⟨y, b0, hb0, ad⟩)
    obtain ⟨bz0, hbz0, rfl⟩ := tu_get hbz
    simp only [renBlob, List.mem_map] at hpar
    obtain ⟨x, hxp, ex⟩ := hpar
    have xd : x ∈ blockDefs bz0 := mem_blockDefs.mpr (Or.inl hxp)
    have ux : u x = x := uD x (defd_iff.mpr ⟨z, bz0, hbz0, xd⟩)
    rw [ux, ua] at ex
    subst ex
    have JD : JDown (mapVals (renBlob u) bl) := fun k b hk j hj => by
      have := (tu_down hD u k b hk).2 j (by rw [← getJmps_eq]; exact hj)
      exact this.2
    have hzle : z ≤ j0.there := rFrom_le JD hz
    have hlt : j0.there < y := ((hD y b0 hb0).2 j0 (by rw [← getJmps_eq]; exact h0)).2
    exact hx y z b0 bz0 x hb0 hbz0 (by omega) ad xd

end Ren

/-- With no kill on `r`, `Live` is `LiveK`. -/
theorem tu_liveK {bl : Map Blob} {K : Nat → Nat → Prop} {k r : Nat} (h : Live bl k r) (hK : ∀ x, ¬ K x r) :
    LiveK bl K k r := by
  induction h with
  | here hb hr => exact LiveK.here hb hr (hK _)
  | next hb hj _ hd ih => exact LiveK.next hb hj (ih hK) hd (hK _)

theorem tu_hasProxies_false {cond : Map (Nat × List Nat)} (h : hasProxies cond = false) (x : Nat) :
    HoonMap.get cond x = Option.none := by
  cases e : HoonMap.get cond x with
  | none => rfl
  | some v =>
    have hm := (HoonMapKeys.mem_keys cond x).mpr (by simp [e])
    unfold hasProxies at h
    cases e' : HoonMapKeys.keys cond with
    | nil => rw [e'] at hm; cases hm
    | cons _ _ => rw [e'] at h; cases h

theorem tu_proxRen (cond : Map (Nat × List Nat)) (f : Nat → Nat) :
    proxRen cond (hasProxies cond) f = f ∘ unproxy cond := by
  funext x
  show f (if hasProxies cond then unproxy cond x else x) = f (unproxy cond x)
  cases hp : hasProxies cond
  · simp only [Bool.false_eq_true, if_false]
    rw [unproxy_none (tu_hasProxies_false hp x)]
  · rfl

/-! ## The whole-subject pass -/

/-- What the final pass needs of the state after the top `+kerf`. -/
structure TopU (g2 : Comp.Gen Map) (o sub : Nat) : Prop where
  il : IL (fun _ _ => False) (CGoalL.next (ofSure (lazyReg (S := S) sub)) (jmp0 o)) g2
  live : ∀ r, Live (unpM g2) o r → r = sub

theorem topU_of (env : CallEnv) (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {nm : Nomm} (hp : PlainN nm)
    {nex : NextL S} {g1 g2 : Comp.Gen Map} {o sub : Nat}
    (h1 : runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1))
    (h2 : (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2)) : TopU (S := S) g2 o sub := by
  obtain ⟨J1, L1⟩ := liveRun_plain_topOfL env (armsLL_of env hS hI) hp h1
  obtain ⟨I2, L2⟩ := kerfSpecL (fun _ _ => False) nex g1 g2 o sub J1 h2
  refine ⟨I2, fun r hl => ?_⟩
  apply Classical.byContradiction
  intro hr
  have hk : LiveK (unpM g2) (fun x y => (fun _ _ => False) x y ∨ lazK (jmp0 o).there (ofSure (lazyReg (S := S) sub)) x y)
      (jmp0 o).there r := by
    refine tu_liveK hl fun x hx => ?_
    rcases hx with hx | ⟨e, he, -, hm⟩
    · exact hx
    · simp only [ofSure, entries, List.mem_cons] at he
      rcases he with rfl | he
      · exact hr hm
      · simp [bondEntries, forkEntries] at he
  exact L1 r (L2 r hk)

variable [MapKeys Map]

theorem tu_final {env : CallEnv} {nm : Nomm} {c : Straight Map}
    (h : finishLUC (S := S) (Map := Map) env nm = some c) :
    ∃ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
      runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) ∧
      (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2) ∧
      toStraightF g2.cond g2.blocks (Need.this sub) o = some c := by
  unfold finishLUC at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨nex, g1, g2, o, sub, h1, h2, h⟩

/-- **The final pass from the facts of the state after `+kerf`**: `OptIn`
and the liveness at the new entry. -/
theorem tu_out {g2 : Comp.Gen Map} {o sub : Nat} (T : TopU (S := S) g2 o sub) (SA : SAB g2.blocks)
    {c : Straight Map} (h : toStraightF g2.cond g2.blocks (Need.this sub) o = some c) :
    OptIn c.blocks ∧ Compiler.ReadsIn c.nargs c.blocks := by
  have I2 := T.il
  have A2 := I2.ats
  have D2 : Down g2.blocks := down_of_ats A2
  obtain ⟨C2, R2, W2⟩ := stIn_of_ats A2
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at h
  simp only [flattenNeed, List.headD, List.length] at h
  obtain ⟨start, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [tu_proxRen] at hnew
  have uD : ∀ x, Defd g2.blocks x → unproxy g2.cond x = x := fun x d => by
    apply unproxy_none
    cases e : HoonMap.get g2.cond x with
    | none => rfl
    | some v => exact absurd d (I2.cond x v e).2.1
  have o1 : 1 ≤ o := (D2 o start hst).1
  have o0 : o ≠ 0 := by omega
  have RD := rankDown_start (Down.rank D2) hst
  have gs8 := get_mapVals (renBlob (unproxy g2.cond)) (HoonMap.put (HoonMap.del g2.blocks o) 0 start)
  have hnew8 : ∀ k b', HoonMap.get new k = some b' →
      ∃ b, HoonMap.get (mapVals (renBlob (unproxy g2.cond)) (HoonMap.put (HoonMap.del g2.blocks o) 0 start)) k = some b ∧
        keepBlock (mapVals (renBlob (unproxy g2.cond)) (HoonMap.put (HoonMap.del g2.blocks o) 0 start))
          (renReg sub 1) k b = some (some b') := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := renameBlocks_get hnew hk
    refine ⟨renBlob (unproxy g2.cond) b, by rw [gs8, hb]; rfl, ?_⟩
    rw [keepBlock_ren RD gs8]; exact hkb
  have hst8 : HoonMap.get (unpM g2) o = some (renBlob (unproxy g2.cond) start) := by
    simp only [unpM]; rw [get_mapVals, hst]; rfl
  have hbs0 : HoonMap.get (mapVals (renBlob (unproxy g2.cond)) (HoonMap.put (HoonMap.del g2.blocks o) 0 start)) 0 =
      some (renBlob (unproxy g2.cond) start) := by rw [gs8]; simp [HoonMap.get_put]
  have hbso : HoonMap.get (mapVals (renBlob (unproxy g2.cond)) (HoonMap.put (HoonMap.del g2.blocks o) 0 start)) o =
      Option.none := by rw [gs8]; simp [HoonMap.get_put, HoonMap.get_del, o0]
  have hbsk : ∀ k, k ≠ 0 → k ≠ o →
      HoonMap.get (mapVals (renBlob (unproxy g2.cond)) (HoonMap.put (HoonMap.del g2.blocks o) 0 start)) k =
        HoonMap.get (unpM g2) k := fun k k0 ko => by
    simp only [unpM]; rw [gs8, get_mapVals]; simp [HoonMap.get_put, HoonMap.get_del, k0, ko]
  have hdB : DownRk id (unpM g2) := Down.rank (tu_down D2 _)
  have hl : ∀ r, Live (unpM g2) o r → NMem (Need.this sub) r := fun r hr => T.live r hr
  have hin : ∀ r, NMem (Need.this sub) r → ¬ Defd (unpM g2) r := by
    intro r hr d
    simp only [NMem] at hr
    subst hr
    have hent := (I2.goal : GoalL g2 (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 o))).2.2
      ((jmp0 o).there, ofSure (lazyReg (S := S) r)) List.mem_cons_self
    exact (hent.2.2 r (by simp [ofSure, lazyReg, NMem])).2 (tu_defd uD d)
  refine ⟨optIn_renOutR hst8 hbs0 hbso hbsk (renReg_inj _ _) (renReg_surj _ _) hnew8 hdB
    (tu_nodup uD SA.nd) (tu_cross uD SA.cr) (tu_noTr SA.tr _) (tu_downPar uD D2 SA.cr SA.args) hl hin, ?_⟩
  obtain ⟨-, -, -, -, c5⟩ := stOut_ren hst8 hbs0 hbso hbsk (renReg_inj _ _) (renReg_surj _ _) hnew8
    (renameBlocks_ren RD gs8 hnew) hdB (tu_arity R2 _) (tu_twoNA W2 _) hl
  refine readsIn_of_live fun r' hlv _ => ?_
  obtain ⟨r, rfl, hr⟩ := c5 r' hlv
  simp only [NMem] at hr
  subst hr
  simp [renReg, needToOrd, countArgs]

/-- **`OptIn` of the whole-subject code with indirect calls on `PlainN`**,
from the specs of `+split` and `+into` and the open `TopSAU`. -/
theorem optIn_finishLUC_of (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm}
    (hp : PlainN nm) (hsa : TopSAU S Map env nm) {c : Straight Map}
    (h : finishLUC (S := S) (Map := Map) env nm = some c) : OptIn c.blocks := by
  obtain ⟨nex, g1, g2, o, sub, h1, h2, h3⟩ := tu_final h
  exact (tu_out (topU_of env hS hI hp h1 h2) (hsa nex g1 g2 o sub h1 h2) h3).1

/-- **`ReadsIn` of the whole-subject code with indirect calls on `PlainN`**
at its argument count. -/
theorem readsIn_finishLUC_of (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm}
    (hp : PlainN nm) (hsa : TopSAU S Map env nm) {c : Straight Map}
    (h : finishLUC (S := S) (Map := Map) env nm = some c) : Compiler.ReadsIn c.nargs c.blocks := by
  obtain ⟨nex, g1, g2, o, sub, h1, h2, h3⟩ := tu_final h
  exact (tu_out (topU_of env hS hI hp h1 h2) (hsa nex g1 g2 o sub h1 h2) h3).2

/-- The same at `finishLUCM` (the version `+compile-unary` runs, with
`mono` `&`), which is `finishLUC` on `PlainN`. -/
theorem optIn_finishLUCM_of (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm}
    (hp : PlainN nm) (hsa : TopSAU S Map env nm) {c : Straight Map}
    (h : finishLUCM (S := S) (Map := Map) env nm = some c) : OptIn c.blocks := by
  rw [finishLUCM_eq env (plainN_noDirect nm hp)] at h
  exact optIn_finishLUC_of hS hI hp hsa h

theorem readsIn_finishLUCM_of (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm}
    (hp : PlainN nm) (hsa : TopSAU S Map env nm) {c : Straight Map}
    (h : finishLUCM (S := S) (Map := Map) env nm = some c) : Compiler.ReadsIn c.nargs c.blocks := by
  rw [finishLUCM_eq env (plainN_noDirect nm hp)] at h
  exact readsIn_finishLUC_of hS hI hp hsa h

end Raw
end SkaModel
end Formalization
