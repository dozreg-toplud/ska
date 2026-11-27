import lemmas.Compiler.OptLinkAlWalk

/-!
# `+alias`: one turn of the walk (README Gaps 13, phases 9 to 15 composed)

The phases still open elsewhere are stated as named hypotheses, in the form
the link needs (each on the model's `g.rev o`, the Hoon's `pre` any list
with no duplicates and the members of `g.rev o`):

* `AlInfoLink`: phase 9, `=^  info  gen` (`alInfo`) returns `[info gen]`
  with `gen` unchanged and `info` `InfoMapRel` to `entryInfo` (no
  predecessors) or `aliasStart g o (g.rev o)`.
* `AlParsLink`: phase 12, `=^  par-new  gen` (`alPars`) returns
  `[par.bob gen]` with `info-local` `InfoMapRel` to `aliasPars g b.par
  edges info`, `edges` of `aliasEdges g o (g.rev o)`.
* `AlBodyLink`: the statement of `al_body_gen` (phase 13, proved in
  `OptLinkAlBodyGate.lean`) for `pick = Ana.pickR FinMap`.  It is a
  hypothesis here only because `OptLinkAlBody.lean` and `OptLinkAlFin.lean`
  both declare `alRnArm` and `alBat_rn`, so no file can import both
  `al_body_gen` and `al_fin`; `al_body_link` (`OptLinkAlWalkBody.lean`)
  proves it.

Phase 10 (`imms` and the two `=.`) is done here: `al_imms` on the Hoon's
`pre`, moved to `g.rev o` by `aliasStartImms_perm` and `immsRel_of_immsEq`.

* `al_reach_comp`: the Nock of a reached block from `alW1` to `alTail`,
  from the product of each phase.
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

/-! ## The phases open elsewhere, as hypotheses -/

/-- **Phase 9** (`alInfo`), as the link needs it. -/
def AlInfoLink : Prop :=
  ∀ (g : Opt.AGen (TreapMap mugF)) (GEN : Noun), GenRel g GEN → Opt.RevNodup g.rev → Opt.BrzInv g →
    ∀ (nargs : Nat) (bl : TreapMap mugF Blob) (RV T : Noun) (o : Nat) (pre : List Nat), pre.Nodup →
    (∀ x, x ∈ pre ↔ x ∈ g.rev o) → ∀ info : Opt.AInfo,
    (if g.rev o = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o (g.rev o)) = some info →
    ∃ IN, nock (C (listNoun A pre) (alWS GEN (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV (C (A o) T))) alInfo
        = some (C IN GEN) ∧ InfoMapRel IN info

/-- **Phase 12** (`alPars`), as the link needs it. -/
def AlParsLink : Prop :=
  ∀ (g : Opt.AGen (TreapMap mugF)) (info : Opt.AInfo) (imms : Opt.AImms) (GEN : Noun), GenRelL g info imms GEN →
    Opt.RevNodup g.rev → NoLti g.new →
    ∀ (nargs : Nat) (bl : TreapMap mugF Blob) (RV T IM IN : Noun) (o : Nat) (pre : List Nat), pre.Nodup →
    (∀ x, x ∈ pre ↔ x ∈ g.rev o) → ∀ (b : Blob) (edges : List (Nat × List (Option Nat))) (loc0 : Opt.AInfo),
    HoonMap.get bl o = some b → Opt.aliasEdges g o (g.rev o) = some edges →
    Opt.aliasPars g b.par edges info = some loc0 →
    ∃ GEN', nock (C b.toNoun (C IM (C IN (C (listNoun A pre)
        (alWS GEN (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV (C (A o) T)))))) alPars
        = some (C (listNoun A b.par) GEN') ∧ GenRelL g loc0 imms GEN'

/-- **Phase 13**: the statement of `al_body_gen` for `Ana.pickR FinMap`. -/
def AlBodyLink : Prop :=
  ∀ (g : Opt.AGen (TreapMap mugF)) (loc : Opt.AInfo) (imml : Opt.AImms) (GEN : Noun), GenRelL g loc imml GEN →
    ∀ (PN IM IN PRE NA BL REV TOPO : Noun) (b : Blob) (ops : List Pole) (st' : Opt.ABody),
    Opt.aliasBody (Ana.pickR FinMap) b.body { old := g.old, loc := loc, imml := imml } = some (ops, st') →
    ∃ GEN', nock (C PN (C b.toNoun (C IM (C IN (C PRE (alWS GEN NA BL REV TOPO)))))) alBody
      = some (C (listNoun Pole.toNoun ops) GEN') ∧ GenRelL { g with old := st'.old } st'.loc st'.imml GEN'

/-! ## The Nock of a turn -/

/-- The Nock of a reached block from `alW1` to `alTail`, from the product
of each phase. -/
theorem al_reach_comp (PREN IN IM BOBN PARN BODYN FINN GEN5 GEN6 GEN7 NEW OLD INFO IMMS LOC IMML REV F NA BL RV
    TOPO : Noun)
    (hI : nock (C PREN (alWS (genN NEW OLD INFO IMMS LOC IMML REV F) NA BL RV TOPO)) alInfo
      = some (C IN (genN NEW OLD INFO IMMS LOC IMML REV F)))
    (hM : nock (C IN (C PREN (alWS (genN NEW OLD INFO IMMS LOC IMML REV F) NA BL RV TOPO))) alImms = some IM)
    (hB : nock (C IM (C IN (C PREN (alWS (genN NEW OLD INFO IMMS IN IM REV F) NA BL RV TOPO)))) alBob = some BOBN)
    (hP : nock (C BOBN (C IM (C IN (C PREN (alWS (genN NEW OLD INFO IMMS IN IM REV F) NA BL RV TOPO))))) alPars
      = some (C PARN GEN5))
    (hBd : nock (C PARN (C BOBN (C IM (C IN (C PREN (alWS GEN5 NA BL RV TOPO)))))) alBody = some (C BODYN GEN6))
    (hF : nock (alFS BODYN PARN BOBN IM IN PREN (alWS GEN6 NA BL RV TOPO)) alFin = some (C FINN GEN7)) :
    nock (C PREN (alWS (genN NEW OLD INFO IMMS LOC IMML REV F) NA BL RV TOPO)) alW1
      = nock (C (C FINN GEN7) (alFS BODYN PARN BOBN IM IN PREN (alWS GEN6 NA BL RV TOPO))) alTail := by
  unfold alWS alFS genN at *
  simp [nock_exec, alW1, alW2, alW3, alW4, alW5, alW6, hI, hM, hB, hP, hBd, hF]

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

end Compiler
end Formalization
