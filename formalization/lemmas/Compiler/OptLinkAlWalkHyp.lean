import lemmas.Compiler.OptLinkAlStartAll

/-!
# `+alias`: the phases the walk takes as hypotheses (README Gaps 13)

This file imports neither `OptLinkAlFin.lean` nor `OptLinkAlBody.lean`
(both declare `alRnArm` and `alBat_rn`, so no file can import both), so
each hypothesis can be proved where its phase is.

* `AlStartLink`: phases 9 and 10, the statement of `al_start` fixed in
  `OptLinkAlStartAll.lean`.
* `AlParsLink`: phase 12 (`alPars`).
* `AlBodyLink`: the statement of `al_body_gen` (phase 13) for `Ana.pickR
  FinMap`; proved by `al_body_link` (`OptLinkAlWalkBody.lean`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedVariables false

attribute [local instance] SkaModel.Ana.tkeyNat

/-! ## The phases open elsewhere, as hypotheses -/

/-- **Phases 9 and 10** (`alStartF`, from `=^  info  gen` through the two
`=.`): the statement of `al_start` that `OptLinkAlStartAll.lean` fixes. -/
def AlStartLink : Prop :=
  ∀ {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (hb : Opt.BrzInv g) (hn : Opt.RevNodup g.rev)
    (nargs : Nat) (BL REV T : Noun) (o : Nat) (preH : List Nat) (hd : preH.Nodup)
    (hm : ∀ x, x ∈ preH ↔ x ∈ g.rev o) {info : Opt.AInfo} {imms : Opt.AImms}
    (hi : (if g.rev o = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o (g.rev o)) = some info)
    (hj : Opt.aliasStartImms g (g.rev o) = some imms) (K : Noun),
    ∃ GEN' INFO IMMS, GenRelL g info imms GEN' ∧ InfoMapRel INFO info ∧ ImmsRel IMMS imms ∧
      nock (C (listNoun A preH) (alWS GEN (A nargs) BL REV (C (A o) T))) (alStartF K)
        = nock (C IMMS (C INFO (C (listNoun A preH) (alWS GEN' (A nargs) BL REV (C (A o) T))))) K

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

end Compiler
end Formalization
