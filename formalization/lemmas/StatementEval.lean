import core.Statement
import lemmas.SpecEquiv

/-!
# The definitions of `core/Statement.lean` in the form the proofs use

`core/Statement.lean` is stated with `Nock`, `Fas` and `Hax` of
`core/Nock.lean`.  Each of its definitions that runs Nock is restated here
with `Eval`, `Slot` and `Edit` of `lemmas/Spec.lean`, or with the executor
`nock`, through `nock_iff_eval`, `nock_eq_some_iff_spec`, `fas_iff_slot` and
`hax_iff_edit` of `lemmas/SpecEquiv.lean`.
-/

namespace Formalization
namespace Ska

open Nock

theorem pull_iff_eval {core arm : Noun} {axis : Nat} :
    Pull core axis arm ↔ Eval core (n3 (A 9) (A axis) (slot 1)) arm :=
  nock_iff_eval

theorem pull_iff_nock {core arm : Noun} {axis : Nat} :
    Pull core axis arm ↔ nock core (n3 (A 9) (A axis) (slot 1)) = some arm :=
  nock_eq_some_iff_spec.symm

theorem slam_iff_eval {gate sam out : Noun} :
    Slam gate sam out ↔ ∃ battery bunt context, gate = C battery (C bunt context) ∧
      Eval (C battery (C sam context)) (n3 (A 9) (A 2) (slot 1)) out := by
  simp only [Slam, nock_iff_eval]

theorem slam_iff_nock {gate sam out : Noun} :
    Slam gate sam out ↔ ∃ battery bunt context, gate = C battery (C bunt context) ∧
      nock (C battery (C sam context)) (n3 (A 9) (A 2) (slot 1)) = some out := by
  simp only [Slam, nock_eq_some_iff_spec]

theorem fromPill_iff_eval {core : Noun} :
    FromPill core ↔ ∃ nok trap, cue pill = some (n4 (A steel) nok trap (A 0)) ∧
      Eval (C trap (A 0)) nok core := by
  simp only [FromPill, nock_iff_eval]

theorem top_iff_slot {core s f gul ton core' : Noun} :
    Top core s f gul ton core' ↔
      ∃ eval gate inner,
        Slot axEval core eval ∧ Pull eval axTop gate ∧ Slam gate (C (C s f) gul) (C ton inner) ∧
          Edit axInner inner core core' := by
  simp only [Top, fas_iff_slot, hax_iff_edit]

theorem mook_iff_slot {core ton toon core' : Noun} :
    Mook core ton toon core' ↔
      ∃ eval gate inner,
        Slot axEval core eval ∧ Pull eval axMook gate ∧ Slam gate ton (C toon inner) ∧
          Edit axInner inner core core' := by
  simp only [Mook, fas_iff_slot, hax_iff_edit]

theorem mock_iff_slot {core s f gul toon : Noun} :
    Mock core s f gul toon ↔
      ∃ hoon gate, Slot axHoon core hoon ∧ Pull hoon axMock gate ∧ Slam gate (C (C s f) gul) toon := by
  simp only [Mock, fas_iff_slot]

/-- `NockEquivalence`, with `Eval` for `Nock`. -/
theorem nockEquivalence_iff_eval :
    NockEquivalence ↔
      ∀ core₀ core s f p gul, FromPill core₀ → Reach core₀ core →
        Eval s f p → ∃ core', Top core s f gul (C (A 0) p) core' := by
  simp only [NockEquivalence, nock_iff_eval]

end Ska
end Formalization
