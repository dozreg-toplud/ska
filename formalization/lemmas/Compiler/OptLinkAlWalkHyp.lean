import lemmas.Compiler.OptLinkAlStartImms

/-!
# `+alias`: the phases the walk takes as hypotheses (README Gaps 13)

The turn and the walk are proved from these (`al_link_of`), and each is
proved from its phase in `OptLinkAlWalkBody.lean` (`al_start_link`,
`al_pars_link`, `al_body_link`), so that the composition does not depend on
the files of the phases.

* `alStartW`: the noun `alStartF` of `OptLinkAlStartAll.lean`, copied
  (`al_start_link` checks the copy by `rfl`).
* `AlStartLink`: phases 9 and 10, the statement of `al_start`.
* `AlParsLink`: phase 12 (`alPars`), `al_pars` with `NoLti` of `g.new`.
* `AlBodyLink`: the statement of `al_body_gen` (phase 13) for `Ana.pickR
  FinMap`.
* `noLti_opt`, `noLti_of_opt`: `NoLti` of `OptLinkBase.lean` is `Opt.NoLti`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedVariables false

attribute [local instance] SkaModel.Ana.tkeyNat

/-! ## The phases open elsewhere, as hypotheses -/

/-- `alStartF` of `OptLinkAlStartAll.lean`: from `=^  info  gen` through the
two `=.`, then `K`. -/
def alStartW (K : Noun) : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alInfo (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1))))
    (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C alImms (C (A 7) (C (C (A 10) (C (C (A 2014)
    (C (A 0) (A 6))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 4030) (C (A 0) (A 2))) (C (A 0) (A 1))))
    K)))))))))))))

/-- The two forms of "no `%lti`" agree. -/
theorem noLti_opt {bl : TreapMap mugF Blob} (h : NoLti bl) : Opt.NoLti bl := by
  intro o b hb n s z o' e
  have := h o b hb
  rw [e] at this
  cases this

theorem noLti_of_opt {bl : TreapMap mugF Blob} (h : Opt.NoLti bl) : NoLti bl := by
  intro o b hb
  cases e : b.fin with
  | lti n s z o' => exact absurd e (h o b hb n s z o')
  | _ => rfl


/-- **Phases 9 and 10** (`alStartW`, from `=^  info  gen` through the two
`=.`): the statement of `al_start` that `OptLinkAlStartAll.lean` fixes. -/
def AlStartLink : Prop :=
  ∀ {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (hb : Opt.BrzInv g) (hn : Opt.RevNodup g.rev)
    (nargs : Nat) (BL REV T : Noun) (o : Nat) (preH : List Nat) (hd : preH.Nodup)
    (hm : ∀ x, x ∈ preH ↔ x ∈ g.rev o) {info : Opt.AInfo} {imms : Opt.AImms}
    (hi : (if g.rev o = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o (g.rev o)) = some info)
    (hj : Opt.aliasStartImms g (g.rev o) = some imms) (K : Noun),
    ∃ GEN' INFO IMMS, GenRelL g info imms GEN' ∧ InfoMapRel INFO info ∧ ImmsRel IMMS imms ∧
      nock (C (listNoun A preH) (alWS GEN (A nargs) BL REV (C (A o) T))) (alStartW K)
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
