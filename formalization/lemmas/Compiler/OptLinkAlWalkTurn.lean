import lemmas.Compiler.OptLinkAlWalk
import lemmas.Compiler.OptLinkAlWalkHyp

/-!
# `+alias`: one turn of the walk (README Gaps 13, phases 9 to 15 composed)

The phases still open elsewhere are named hypotheses (`OptLinkAlWalkHyp.lean`),
in the form the link needs (each on the model's `g.rev o`, the Hoon's `pre`
any list with no duplicates and the members of `g.rev o`):

* `AlStartLink`: phases 9 and 10, the statement of `al_start` fixed in
  `OptLinkAlStartAll.lean` (track B): `alStartF K` runs to `K` on `[imms
  [info [pre WALK]]]` with `gen` `GenRelL g info imms`.
* `AlParsLink`: phase 12, `=^  par-new  gen` (`alPars`) returns
  `[par.bob gen]` with `info-local` `InfoMapRel` to `aliasPars g b.par
  edges info`, `edges` of `aliasEdges g o (g.rev o)`.
* `AlBodyLink`: the statement of `al_body_gen` (phase 13, proved in
  `OptLinkAlBodyGate.lean`) for `pick = Ana.pickR FinMap`.  It is a
  hypothesis here only because `OptLinkAlBody.lean` and `OptLinkAlFin.lean`
  both declare `alRnArm` and `alBat_rn`, so no file can import both
  `al_body_gen` and `al_fin`; `al_body_link` (`OptLinkAlWalkBody.lean`)
  proves it.

* `alW1_start`: the branch of a reached block is `alStartF [8 alBob alW4]`;
  `al_reach_comp`: the Nock from `bob` to `alTail`, from the product of
  each phase.
* `al_walk_step`: the walk on `o :: t` is the unreachable branch or `alW1`.
* **`al_turn`**: one turn of the walk, for a reached or an unreachable
  block: on `gen` `GenRel g` (with `RevNodup`, `BrzInv`, `NoLti` of
  `g.new`), where `aliasBlock` returns `g1`, the walk on `o :: t` is the walk
  on `t` from a `gen` `GenRel g1`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local instance] SkaModel.Ana.tkeyNat

/-! ## The Nock of a turn -/

theorem alW1_start : alW1 = alStartF (C (A 8) (C alBob alW4)) := rfl

/-- The Nock of a reached block from `bob` to `alTail`, from the product of
each phase. -/
theorem al_reach_comp (PREN IN IM BOBN PARN BODYN FINN GEN' GEN5 GEN6 GEN7 NA BL RV TOPO : Noun)
    (hB : nock (C IM (C IN (C PREN (alWS GEN' NA BL RV TOPO)))) alBob = some BOBN)
    (hP : nock (C BOBN (C IM (C IN (C PREN (alWS GEN' NA BL RV TOPO))))) alPars = some (C PARN GEN5))
    (hBd : nock (C PARN (C BOBN (C IM (C IN (C PREN (alWS GEN5 NA BL RV TOPO)))))) alBody = some (C BODYN GEN6))
    (hF : nock (alFS BODYN PARN BOBN IM IN PREN (alWS GEN6 NA BL RV TOPO)) alFin = some (C FINN GEN7)) :
    nock (C IM (C IN (C PREN (alWS GEN' NA BL RV TOPO)))) (C (A 8) (C alBob alW4))
      = nock (C (C FINN GEN7) (alFS BODYN PARN BOBN IM IN PREN (alWS GEN6 NA BL RV TOPO))) alTail := by
  unfold alWS alFS at *
  simp [nock_exec, alW4, alW5, alW6, hB, hP, hBd, hF]

/-- The walk on `o :: t`: the test of an unreachable block on the Hoon's `pre`. -/
theorem al_walk_step (GEN NA BL RV T : Noun) (o : Nat) (pre : List Nat)
    (hpre : nock (alWS GEN NA BL RV (C (A o) T)) alPre = some (listNoun A pre)) :
    nock (alWS GEN NA BL RV (C (A o) T)) alWalk
      = if pre = [] ∧ o ≠ 0 then nock (C (listNoun A pre) (alWS GEN NA BL RV (C (A o) T))) alUnB
        else nock (C (listNoun A pre) (alWS GEN NA BL RV (C (A o) T))) alW1 := by
  have hu := al_unt GEN NA BL RV T pre o
  conv => lhs; arg 2; rw [alWalk_cut]
  unfold alWS at hu hpre ⊢
  by_cases e : pre = [] ∧ o ≠ 0
  · simp only [e, flag] at hu
    simp [nock_exec, alWalkC, hpre, hu, e]
  · have e' : decide (pre = [] ∧ o ≠ 0) = false := by simpa using e
    simp only [flag, e'] at hu
    simp [nock_exec, alWalkC, hpre, hu, e]

/-- `pre` is empty exactly where `g.rev o` is. -/
theorem pre_nil_iff {pre l : List Nat} (hm : ∀ x, x ∈ pre ↔ x ∈ l) : pre = [] ↔ l = [] := by
  constructor <;> intro e
  · cases h' : l with
    | nil => rfl
    | cons x t => exact absurd ((hm x).2 (by simp [h'])) (by simp [e])
  · cases h' : pre with
    | nil => rfl
    | cons x t => exact absurd ((hm x).1 (by simp [h'])) (by simp [e])

/-- **One turn of the walk**: where `aliasBlock` returns `g1`, the walk on
`o :: t` from `gen` `GenRel g` is the walk on `t` from `gen` `GenRel g1`. -/
theorem al_turn (h9 : AlStartLink) (h12 : AlParsLink) (h13 : AlBodyLink)
    {g g1 : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (hn : Opt.RevNodup g.rev)
    (hz : Opt.BrzInv g) (hnl : NoLti g.new) (nargs : Nat) (bl : TreapMap mugF Blob) (hbl : NoLti bl)
    (RV T : Noun) (o : Nat) (h : Opt.aliasBlock (Ana.pickR FinMap) nargs bl g o = some g1) :
    ∃ GEN1, GenRel g1 GEN1 ∧
      nock (alWS GEN (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV (C (A o) T)) alWalk
        = nock (alWS GEN1 (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV T) alWalk := by
  obtain ⟨pre, hpre, hd, hm⟩ := al_pre hg (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV T o
  rw [al_walk_step _ _ _ _ _ o pre hpre]
  have hpe := pre_nil_iff hm
  by_cases hw : pre = [] ∧ o ≠ 0
  · rw [if_pos hw]
    obtain ⟨b, hb, rfl⟩ := Opt.aliasBlock_dropped h ⟨hpe.1 hw.1, hw.2⟩
    exact al_unreach hg hn (A nargs) RV T (listNoun A pre) bl hbl o b hb
  · rw [if_neg hw]
    have hw' : ¬(g.rev o = [] ∧ o ≠ 0) := fun e => hw ⟨hpe.2 e.1, e.2⟩
    unfold Opt.aliasBlock at h
    rw [if_neg hw'] at h
    obtain ⟨info, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨imms, hj, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨edges, he, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨loc0, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rb, hbd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rf, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨GEN', INFO, IMMS, hG', hI, hM, hS⟩ :=
      h9 hg hz hn nargs (HoonMap.toNoun Blob.toNoun bl) RV T o pre hd hm hi hj (C (A 8) (C alBob alW4))
    rw [alW1_start, hS]
    have hB := al_bob IMMS INFO (listNoun A pre) GEN' (A nargs) RV T bl o
    rw [hb, Option.map_some] at hB
    obtain ⟨GEN5, hP, hG5⟩ := h12 g info imms GEN' hG' hn hnl nargs bl RV T IMMS INFO o pre hd hm b edges loc0
      hb he hp
    obtain ⟨GEN6, hBd, hG6⟩ := h13 g loc0 imms GEN5 hG5 (listNoun A b.par) IMMS INFO (listNoun A pre) (A nargs)
      (HoonMap.toNoun Blob.toNoun bl) RV (C (A o) T) b rb.1 rb.2 hbd
    obtain ⟨GEN7, hF, hG7⟩ := al_fin b.fin { g with old := rb.2.old } rb.2.loc rb.2.imml GEN6 hG6 hn
      (listNoun Pole.toNoun rb.1) (listNoun A b.par) (listNoun A b.par) (listNoun Pole.toNoun b.body) IMMS INFO
      (listNoun A pre) (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV T o rf hf
    obtain ⟨GEN8, hG8, hT⟩ := al_tail hG7 ⟨b.par, rb.1, rf.1⟩ b.toNoun IMMS INFO (listNoun A pre) GEN6 (A nargs)
      (HoonMap.toNoun Blob.toNoun bl) RV T o
    refine ⟨GEN8, hG8, ?_⟩
    rw [al_reach_comp (listNoun A pre) INFO IMMS b.toNoun (listNoun A b.par) (listNoun Pole.toNoun rb.1)
      (Termin.toNoun rf.1) GEN' GEN5 GEN6 GEN7 (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV (C (A o) T) hB hP hBd hF]
    exact hT

end Compiler
end Formalization
