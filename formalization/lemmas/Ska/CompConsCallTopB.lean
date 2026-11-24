import lemmas.Ska.CompConsCallTop
import lemmas.Ska.CompIndirectOutB

/-!
# The backward half at the top, from `SemNCB`

README Gaps 12.16 (nineteenth session).

* `finishLUC_bwdC`: the backward contract of the whole-subject code of any
  nomm whose run for `%done` is the block `[don 0]` and `RunOKNC` with
  `SemNCB` under `%next (lazy-from-reg 0)` into it, and whose formula
  crashes where the run's pure part does (the counterpart of
  `finishLUC_fwdC`).
* `finishLUC_contractC`: both halves, `BellContract` of the whole-subject
  version.
* `indirectTop_bwdC`, `indirectTop_bwd'`: the backward half of the
  indirect call re-derived from `indirect_runDB` (a check of `SemNCB`
  against `indirectTop_bwd`, on every formula with `MinkN2`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The backward contract of the whole-subject code from `SemNCB`**: for
a nomm whose run for `%done` from `gen0` is the block `[don 0]` at `1` and a
run that calls under `%next (lazy-from-reg 0)` into it (`RunOKNC` and
`SemNCB` for the formula `f` on the subjects of `P`), and whose formula's
`+mink` crashes where the run's pure part `pq` has no value (`MnecB`), the
code has the need `this` and meets `ContractBwd` on every subject of `P`. -/
theorem finishLUC_bwdC (lib : Lib) {nm pq : Nomm} {P : Noun → Prop} {f : Noun} {env : CallEnv}
    (hrun : ∀ {nex : NextL S} {g' : Gen Map},
      runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g') →
      HoonMap.get g'.blocks (gen0 : Gen Map).bo = some ⟨[], [], Termin.don (gen0 : Gen Map).re⟩ ∧
      RunOKNC lib P f pq (lazyReg (gen0 : Gen Map).re) (jmp0 (gen0 : Gen Map).bo)
        ({ (gen0 : Gen Map) with re := (gen0 : Gen Map).re + 1 }.emitted ⟨[], [], Termin.don (gen0 : Gen Map).re⟩)
        g' nex ∧
      SemNCB lib P f (lazyReg (gen0 : Gen Map).re) (jmp0 (gen0 : Gen Map).bo)
        ({ (gen0 : Gen Map) with re := (gen0 : Gen Map).re + 1 }.emitted ⟨[], [], Termin.don (gen0 : Gen Map).re⟩)
        g' nex)
    (MnecB : ∀ {s gul : Noun} {tm : Trace}, P s → pureEval pq s = none → Mink lib gul tm s f (Tone.two tm))
    {c : Straight Map} (h : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractBwd lib N s f [s] c := by
  unfold finishLUC at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  obtain ⟨hb1, R, RB⟩ := hrun hr
  have l1 := R.ext.1
  have l2 := R.ext.2.1
  simp only [Gen.emitted, gen0] at l1 l2
  have T : TopS gE nex :=
    { ext := ((ext_re _).trans (ext_emit _ _)).trans R.ext
      grow := (((grow_re (gen0 : Gen Map)).trans (grow_emit (fun j hj => by simp [finJumps] at hj))).toU
        upBelow_gen0).trans R.grow
      cfr := (condFresh_of_eq (g0 := (gen0 : Gen Map)) (g1 := { (gen0 : Gen Map) with
        re := (gen0 : Gen Map).re + 1 }.emitted ⟨[], [], Termin.don (gen0 : Gen Map).re⟩)
        (by simp [Gen.emitted]) rfl).trans R.cfr
      lo := R.lo
      hi := R.hi
      args := nextArgs_nil R.ent rfl
      regs := fun r hr => ⟨Nat.zero_le _, by
        rcases R.regs r hr with e | ⟨_, e⟩
        · simp only [lazyReg, NMem] at e; simp only [gen0] at e; omega
        · exact e⟩
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Nat.zero_le _, ((R.eregs e he).2 r hr).2⟩⟩
      labs := fun e he => ⟨by have := (R.labs e he).1; simp only [Gen.emitted, gen0] at this ⊢; omega,
        (R.labs e he).2⟩
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have F := finishTop_genA lib T (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs _ hS hB hI htr ton st'' hx => by
      have ag' : ∀ st' : σ, AgreeU lib O c gul st' t cf ned
          ({ (gen0 : Gen Map) with re := (gen0 : Gen Map).re + 1 }.emitted
            ⟨[], [], Termin.don (gen0 : Gen Map).re⟩) gE nex.laz s s := fun st' =>
        AgreeU.part (ag st') (by simp [Gen.emitted]) (Ext.refl gE) (fun e he => he) (fun k _ _ hk => hk)
          (fun e he => Nat.lt_trans (R.labs e he).2.1 R.hi)
      obtain ⟨r, hm, G⟩ := RB cf hcf c ned σ Inv ν O gul hS hB st t tm s s hI htr hs ag' hned regs hh hn _ hx
      have c0 : HoonMap.get cf (gen0 : Gen Map).re = Option.none := by
        rw [hcf _ (by simp only [gen0]; omega), R.cfr.get_lt (by simp [Gen.emitted])]
        exact HoonMap.get_empty _
      have hb : HoonMap.get c.blocks (gen0 : Gen Map).bo = some ⟨[], [], Termin.don (gen0 : Gen Map).re⟩ := by
        rw [(ag st).1 _ (Nat.le_refl _) (by simp only [gen0]; omega) (fun hm => by
          obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
          have := (R.labs e he).1; simp only [Gen.emitted, gen0] at this e1; omega), hb1]
        simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0]
      obtain ⟨ton', st', -, -, he, hrel⟩ := returnsC_done hb G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      exact ⟨_, MnecB hs (R.nec s hfs), ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩
  exact F.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The backward half of the indirect call from `SemNCB`**: the
whole-subject code of `[2 p q]` with `p`, `q` meeting `UOK`, at most 255
`%6`, for any formula with `MinkN2`, meets `ContractBwd` (`indirect_runD`,
`indirect_runDB`, `finishLUC_bwdC`). -/
theorem indirectTop_bwdC {lib : Lib} {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {c : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractBwd lib N s f [s] c :=
  finishLUC_bwdC lib (pq := Nomm.cons p q)
    (fun hr => ⟨(indirect_runD lib up uq M hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1,
      (indirect_runD lib up uq M hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).2,
      indirect_runDB lib up uq M hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr⟩)
    (fun hs e => M.crash hs (by rw [pureEval_cons] at e; exact e)) h N

/-- **`indirectTop_bwd` re-derived from `SemNCB`** (the same statement). -/
theorem indirectTop_bwd' {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {fb fc : Noun} {p q : Nomm} (hfol : bl.fol = n3 (A 2) fb fc)
    (hAp : Annot lib code (SkaModel.Fits bl.less) fb p) (hAq : Annot lib code (SkaModel.Fits bl.less) fc q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s → ContractBwd lib N s bl.fol [s] c := by
  rw [hfol]
  exact indirectTop_bwdC (runU_uok lib hp) (runU_uok lib hq)
    (minkN2_indirect hok (fragU_pure hp) (fragU_pure hq) hAp hAq) hcount h N

end Comp
end SkaModel
end Formalization
