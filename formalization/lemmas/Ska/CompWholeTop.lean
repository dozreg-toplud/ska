import lemmas.Ska.CompWholeKern
import lemmas.Ska.CompFragUJ

/-!
# The whole-subject version meets the contract

README Gaps 12.10.  `finishLU_compDone`: for a nomm whose run for `%done`
from `gen0` meets `RunOKV`, the code of `+compile-unary` (`finishLU`) has the
input need `this` and, entered on the subject whole in register `0`, returns
the tone of the nomm, on every subject (the taking apart of `+kern` checks
every cell it opens, so no cape is needed).  `finishLU_bellContractFU`: on
`FragU` it meets `BellContract lib N bl true` (the subject whole as the one
argument), the contract that `%dire` with `mono` `&` and `%full` (through
`+eval-top`, `topBody`) need.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- Every block that hops up hops below `bo`, after a run from `gen0`. -/
theorem upBelow_of_growU {g : Gen Map} (hg : GrowU gen0 g) : UpBelow g := by
  intro u t ⟨b, j, hb, hf, ht, hlt⟩
  rcases hg.new u b hb with ⟨b0, h0, _⟩ | ⟨_, _, J⟩
  · simp [gen0, HoonMap.get_empty] at h0
  · rcases J j (by rw [hf]; simp [finJumps]) with ⟨_, ⟨a, _⟩ | ⟨_, _, c, _⟩⟩
    · omega
    · omega

/-- **The whole-subject code at its entry**: the input need is `this`, and
on the subject whole it returns the tone of the nomm. -/
theorem finishLU_compDone (lib : Lib) {nm : Nomm}
    (hR : ∀ {nex : NextL S} {g1 : Gen Map}, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g1) →
      RunOKV (Map := Map) lib nm CGoal.done gen0 g1 nex)
    {c' : Straight Map} (h : finishLU (S := S) nm = some c') :
    c'.need = NeedOrd.this ∧ ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (t : Trace) (gul : Noun),
      execEntry lib O st c' [s] t gul = some (pureTone t nm s, st) := by
  unfold finishLU at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  have R := hR h1
  obtain ⟨⟨⟨o, sub⟩, g3⟩, h2, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  have d1 : g1.drop = false := R.ext.2.2.1
  have cb1 : CondBelow g1 := R.cfr.below condBelow_gen0
  -- `+kerf`: the hop block, then `+kern`
  unfold kerf at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, g4, h3, h4⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have lt0 : nex.th.there < g1.bo := R.hi
  have hlab : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => Nat.lt_trans (R.labs e he).2.1 lt0
  have hn : (((g1.bo, nex.laz) :: entries nex.laz).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := hlab e he; omega, R.nodup⟩
  have cbe : CondBelow (g1.emitted ⟨[], [], Termin.hop nex.th⟩) := cb1
  obtain ⟨hr, W⟩ := kern_spec h3 d1 cbe hn
  simp only [Gen.emitted] at hr
  subst hr
  have eblk : ∀ k, HoonMap.get (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  -- the blocks after `+kern`
  obtain ⟨A0, hA0, P0⟩ := W.at_ (g1.bo, nex.laz) List.mem_cons_self
  have hB0 : HoonMap.get g4.blocks g1.bo = some ⟨[], A0, Termin.hop nex.th⟩ := by
    have := hA0 [] (Termin.hop nex.th) (by simp only [eblk]; simp)
    simpa using this
  have hE : ∀ e ∈ entries nex.laz, ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
      HoonMap.get g4.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧
      KernP g1.re g4.cond (g1.re + 1) g4.re e.1 e.2.sure A := by
    intro e he
    obtain ⟨_, _, th, hth⟩ := R.labs e he
    obtain ⟨A, hA, P⟩ := W.at_ e (List.mem_cons_of_mem _ he)
    refine ⟨A, th, hth, ?_, P⟩
    have := hA [] (Termin.hop th) (by
      have ne : e.1 ≠ g1.bo := by have := hlab e he; omega
      simp only [eblk, ne, ↓reduceIte]; exact hth)
    simpa using this
  have hO : ∀ k, k ≠ g1.bo → k ∉ (entries nex.laz).map Prod.fst → HoonMap.get g4.blocks k = HoonMap.get g1.blocks k := by
    intro k k1 k2
    rw [W.other k (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨k1, k2⟩)]
    simp only [eblk, k1, ↓reduceIte]
  -- the program: the blocks unproxied
  let c1 : Straight Map := ⟨NeedOrd.none, 0, mapVals (unproxyBlob g4.cond) g4.blocks⟩
  have hag : ∀ k, HoonMap.get c1.blocks k = (HoonMap.get g4.blocks k).map (unproxyBlob g4.cond) :=
    fun k => get_mapVals _ _ k
  have D1 := downRk_gen0 (R.grow.trans (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩)
    (fun j hj => by simp [finJumps] at hj; subst hj; exact ⟨R.lo, lt0⟩) (upBelow_of_growU R.grow)))
  have D4 := downRk_of_fins D1 (bs' := g4.blocks) fun k b' hk => by
    by_cases e1 : k = g1.bo
    · subst e1; rw [hB0] at hk; cases hk; exact ⟨⟨[], [], Termin.hop nex.th⟩, by rw [eblk]; simp, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e2
      obtain ⟨A, th, h1', h4', _⟩ := hE e he
      rw [h4'] at hk; cases hk
      exact ⟨⟨[], [], Termin.hop th⟩, by rw [eblk, if_neg e1]; exact h1', rfl⟩
    · rw [hO k e1 e2] at hk; exact ⟨b', by rw [eblk, if_neg e1]; exact hk, rfl⟩
  have Dc : DownRk (upRk (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks) c1.blocks := by
    intro k b hk
    rw [hag k] at hk
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact downRk_unproxy _ (D4 k b0 hb0)
  obtain ⟨hneed, start, hst, hent⟩ := toStraightF_entryU hts (by simp [flattenNeed, isRun]) D4 Dc
    (fun k _ => hag k)
  rw [hB0] at hst; cases hst
  refine ⟨hneed, fun σ O st s t gul => ?_⟩
  obtain ⟨R0, hR0, he⟩ := hent lib O st s [s] t gul (by rw [hneed]; rfl)
  rw [he]
  have ag4 : ∀ k, k < g1.re + 1 → HoonMap.get g4.cond k = HoonMap.get g1.cond k := fun k hk => W.cnd.1.get_lt hk
  have u4r : HoonMap.get g4.cond g1.re = Option.none := by
    rw [ag4 _ (Nat.lt_succ_self _)]; exact condBelow_none cb1 (Nat.le_refl _)
  have regs1 : ∀ x, NMem nex.laz.sure.ned x → x < g1.re := fun x hx => (R.regs x hx).2
  have hj : nex.th.args = [] := by
    rcases R.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  have hrj : renJmp (unproxy g4.cond) nex.th = nex.th := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hj; simp only at hj; subst hj; rfl
  -- the agreement of the program with the run's blocks
  have ag : AgreeU lib O c1 gul st t g4.cond (Need.this g1.re) gen0 g1 nex.laz s s := by
    refine ⟨fun o' _ u hnl => ?_, fun e he => ?_⟩
    · rw [hag o', hO o' (by omega) hnl]
    · obtain ⟨A, th, h1', h4', P⟩ := hE e he
      refine ⟨A.map (renPole (unproxy g4.cond)), th, h1', ?_, ?_⟩
      · rw [hag, h4']; simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin]
      · obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P
        have l0' : g1.re + 1 ≤ lo0 := l0
        have regsE : ∀ x, NMem e.2.sure.ned x → x < g1.re := fun x hx => ((R.eregs e he).2 x hx).2
        have KS := sem (by omega) (R.eregs e he).1 regsE (unproxy g4.cond) (unproxy_none u4r)
          (fun x hx => unproxy_none (by rw [ag4 x (by have := regsE x hx; omega)]; exact R.econd e he x hx))
          (fun _ _ => rfl)
        intro R hR
        obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st t R s hR
        refine ⟨fun f => ?_, S2⟩
        obtain ⟨R', a, b, k⟩ := S1 f
        exact ⟨R', a, b, fun x hx hn => k x (by
          rcases hx with hx | hx
          · simp only [NMem] at hx; omega
          · omega) hn⟩
  -- the ops at the hop block, then the run
  obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P0
  have l0' : g1.re + 1 ≤ lo0 := l0
  have KS := sem (by omega) R.dist regs1 (unproxy g4.cond) (unproxy_none u4r)
    (fun x hx => unproxy_none (by rw [ag4 x (by have := regs1 x hx; omega)]; exact R.ncond x hx))
    (fun _ _ => rfl)
  obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st t R0 s hR0
  simp only [unproxyBlob, renBlob, List.map_nil, renFin, hrj]
  rw [pureTone]
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := S1 fo
    have e1 := hr1 [] (Termin.hop nex.th)
    simp only [List.append_nil] at e1
    rw [e1, execBlob_hop]
    have hn1 : HoldsN (Need.this g1.re) R1 s := by
      show SkaModel.read g1.re R1 = some s
      rw [kr1 g1.re (by omega) (fun hm => by have := regs1 _ hm; omega)]; exact hR0
    have := R.sem g4.cond (fun k hk => ag4 k (by omega)) c1 (Need.this g1.re) σ O st t gul s s ag
      (fun x hx => by simp only [NMem] at hx; omega) R1 hh1 hn1
    simp only [GoalSem] at this
    exact this
  · have e2 := S2 fo [] (Termin.hop nex.th)
    simp only [List.append_nil] at e2
    rw [e2, R.nec s fo]; rfl

/-- `+to-straight` counts the arguments of the input need it returns. -/
theorem toStraightF_nargs {cond : Map (Nat × List Nat)} {blocks : Map Blob} {ned : Need} {o : Nat}
    {c' : Straight Map} (h : toStraightF cond blocks ned o = some c') : c'.nargs = countArgs c'.need := by
  unfold toStraightF at h
  obtain ⟨start, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨input, st⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  split at h
  · obtain ⟨new, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  · obtain ⟨new, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl

/-- The whole-subject code has one argument. -/
theorem finishLU_nargs {nm : Nomm} {c' : Straight Map} (h : finishLU (S := S) (Map := Map) nm = some c')
    (hn : c'.need = NeedOrd.this) : c'.nargs = 1 := by
  unfold finishLU at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  rw [toStraightF_nargs h, hn]; rfl

/-- **The whole-subject code meets the contract of its bell with the subject
whole as the one argument** (`mono` `&`), for any nomm whose run for
`%done` from `gen0` meets `RunOKV`.  No hypothesis on the cape: the code
takes the subject apart with a check at every cell. -/
theorem finishLU_bellContractV {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hR : ∀ {nex : NextL S} {g1 : Gen Map}, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g1) →
      RunOKV (Map := Map) lib nm CGoal.done gen0 g1 nex)
    {c' : Straight Map} (h : finishLU (S := S) nm = some c') (N : Needs) : BellContract lib N bl true c' := by
  obtain ⟨_, hc⟩ := finishLU_compDone lib hR h
  intro s hs args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  refine ⟨?_, ?_⟩
  · intro σ Inv ν O n gul ti tm r _ _ _ hm st _ htr
    have e := (mink_pure hok hp hA hs gul tm r).mp ⟨n, hm⟩
    subst e
    exact ⟨pureTone ti nm s, st, hc σ O st s ti gul, toneRel_pureTone htr nm s⟩
  · intro σ Inv ν O gul ti tm _ _ _ st ton st' _ htr hrun
    rw [hc σ O st s ti gul] at hrun
    cases hrun
    exact ⟨pureTone tm nm s, (mink_pure hok hp hA hs gul tm _).mpr rfl, toneRel_pureTone htr nm s⟩

/-- **The whole-subject version meets the contract on `FragU`**
(`BellContract … true`), with at most 255 `%6`. -/
theorem finishLU_bellContractFU {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragU (S := S) nm) (hcount : sixCount nm ≤ 255) {c' : Straight Map}
    (h : finishLU (S := S) nm = some c') (N : Needs) : BellContract lib N bl true c' :=
  finishLU_bellContractV hok (runU_uok (Map := Map) lib hf).pure hA
    (fun h1 => (runU_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0
      condBelow_gen0 h1) h N

/-- **What `%full` must answer, on `FragU`** (the clause `full_code` of
`Sound`, for the bell `bl` of the formula): one argument, the input need
`this`, and both halves of the contract on the subject whole, for every
subject that fits the bell. -/
theorem finishLU_fullCode {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragU (S := S) nm) (hcount : sixCount nm ≤ 255) {c' : Straight Map}
    (h : finishLU (S := S) nm = some c') (N : Needs) :
    c'.nargs = 1 ∧ c'.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s →
      ContractFwd lib N s bl.fol [s] c' ∧ ContractBwd lib N s bl.fol [s] c' := by
  have hn := (finishLU_compDone lib (fun h1 => (runU_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 h1) h).1
  exact ⟨finishLU_nargs h hn, hn, fun s hs => finishLU_bellContractFU hok hA hf hcount h N s hs [s] rfl⟩

end Comp
end SkaModel
end Formalization
