import lemmas.Ska.CompHintWSound
import lemmas.Ska.CompHintClsGlue

/-!
# The wider class of hinted nomms in the glue's form (README Gaps 24.23)

The text of `CompHintClsGlue.lean` for `hcW`:

* `HintClsBW snd lib`: `(hcW snd bl.fol nm).top`, `HintTabW env N nm`,
  `FitHW lib env (Fits bl.less) bl.fol nm` (the fits, the battery reads and
  `+mack` of the constant `%mean`'s traps at the bell's own subjects).
* **`InFragHW`**: `MonoCalls` on hint-free nomms, or `HintClsBW`;
  `inFragHW_iff` (`hcV`'s members are `hcW`'s on every dumped entry, a
  `#guard` in `CompHintWTally.lean`, not a theorem).
* **`rawMonoH_inFragHW`**: `RawMonoH` of `InFragHW`, with no hypotheses
  (`hintClsW_contract`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
variable {S : Type} [Comp.HoonSet S]

/-- **The wider class at the bell.** -/
def HintClsBW (snd : Nomm → NeedOrd → Bool) (lib : Lib) : MonoClass := fun env N bl nm =>
  (Comp.hcW snd bl.fol nm).top = true ∧ Comp.HintTabW env N nm ∧
    Comp.FitHW lib env (SkaModel.Fits bl.less) bl.fol nm

/-- **The hinted analogue of the class of `inFragM`, wider.** -/
def InFragHW (S : Type) [Comp.HoonSet S] (snd : Nomm → NeedOrd → Bool) (lib : Lib) : MonoClass :=
  orM (noHintM (MonoCalls S lib)) (HintClsBW snd lib)

theorem inFragHW_iff {snd : Nomm → NeedOrd → Bool} {lib : Lib} {env : Comp.CallEnv} {N : Needs} {bl : Bell}
    {nm : Nomm} :
    InFragHW S snd lib env N bl nm ↔
      (MonoCalls S lib env N bl nm ∧ nm.noHint = true) ∨
        ((Comp.hcW snd bl.fol nm).top = true ∧ Comp.HintTabW env N nm ∧
          Comp.FitHW lib env (SkaModel.Fits bl.less) bl.fol nm) :=
  Iff.rfl

/-- **The raw whole-subject contract at `finishLUCH` on `HintClsBW`.** -/
theorem rawMonoH_hintClsW (lib : Lib) (snd : Nomm → NeedOrd → Bool) :
    RawMonoH S Map lib snd (HintClsBW snd lib) := by
  intro code bl nm env s N _ _ hf _ hs
  obtain ⟨hm, ht, hfit⟩ := hf
  have C := Comp.hintClsW_contract lib env snd N (SkaModel.Fits bl.less) hm ht hfit hs
  intro x hx args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact C.2 x hx

/-- **The wider hinted class at the glue's form**, unconditionally:
`RawMonoH` of `InFragHW`. -/
theorem rawMonoH_inFragHW [Opt.MapKeys Map] (lib : Lib) (snd : Nomm → NeedOrd → Bool) :
    RawMonoH S Map lib snd (InFragHW S snd lib) :=
  rawMonoH_or (rawMonoH_of_D snd (rawMonoD_calls lib)) (rawMonoH_hintClsW lib snd)

end Glue
end SkaModel
end Formalization
