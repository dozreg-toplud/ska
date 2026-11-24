import lemmas.Compiler.FolLoopLink

/-!
# `+register-fast` as the pill's own run

The battery of `+register-fast` quotes the hoon core, so it is not written
out as a model.  For registrations kept as nouns (`R := Noun`), `Env.registerFast`
can be the pill's run of the gate, decoded into `[miss regs]`
(`registerFastP`).  `RegisterFastIs` then holds as soon as every return of
the gate is a cell whose head is a flag (`RegisterFastShape`,
`registerFastIs_of`).  The shape fact itself is not proved here.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-- The gate `+register-fast` of `ana` on the products `h` and `f` of the hint
and its formula and the registrations `r`. -/
noncomputable def regFastRun (h f : Sock) (r : Noun) : Option Noun :=
  nock (C register_fast.battery (C (C h.toNoun (C f.toNoun r)) ana)) register_fast.battery

/-- Every return of the gate is `[miss regs]` with a flag `miss`. -/
def RegisterFastShape : Prop :=
  ∀ h f r x, regFastRun h f r = some x → ∃ (b : Bool) (r' : Noun), x = C (flag b) r'

/-- `+register-fast` for registrations kept as nouns: the pill's run, decoded. -/
noncomputable def registerFastP (h f : Sock) (r : Noun) : Option (Bool × Noun) := by
  classical
  exact if hx : ∃ p : Bool × Noun, regFastRun h f r = some (C (flag p.1) p.2) then
    some (Classical.choose hx) else none

/-- `RegisterFastIs` for every `Env Noun` whose `registerFast` is the pill's
decoded run, from the shape fact. -/
theorem registerFastIs_of (hs : RegisterFastShape) (env : Env Noun)
    (he : env.registerFast = registerFastP) : RegisterFastIs (fun x : Noun => x) env := by
  intro h f r
  rw [he]
  show regFastRun h f r = _
  cases e : regFastRun h f r with
  | none =>
    have hn : ¬ ∃ p : Bool × Noun, regFastRun h f r = some (C (flag p.1) p.2) := by
      rintro ⟨p, hp⟩; rw [e] at hp; cases hp
    simp only [registerFastP, dif_neg hn, Option.map_none]
  | some x =>
    obtain ⟨b, r', rfl⟩ := hs h f r x e
    have hp : ∃ p : Bool × Noun, regFastRun h f r = some (C (flag p.1) p.2) := ⟨(b, r'), e⟩
    simp only [registerFastP, dif_pos hp, Option.map_some]
    exact e.symm.trans (Classical.choose_spec hp)

end Compiler
end Formalization
