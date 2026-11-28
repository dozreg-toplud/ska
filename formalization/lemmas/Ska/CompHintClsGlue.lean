import lemmas.Ska.CompHintClsSound
import lemmas.Glue.MonoCalls

/-!
# The class of hinted nomms in the glue's form (README Gaps 24.22, step 4)

The glue plugs a whole-subject class in as a `MonoClass` (`CallEnv → Needs →
Bell → Nomm → Prop`, `Glue/MonoCalls.lean`): the field `inFragM` of
`RefSideM` asks every real nomm to be in it, and `RawMonoD S Map lib FM` (the
raw contract on the class against `finishLUCM`) turns membership into the
`BellContract` of the bell.  With hints the compile is `finishLUCH env snd`
(track G's M16), so the statements here are their texts at `finishLUCH`:

* `RawMonoH`: `RawMonoD` with `finishLUCH env snd` in place of `finishLUCM`;
  `rawMonoH_or`; **`rawMonoH_of_D`** (a `RawMonoD` class restricted to
  hint-free nomms has it, `finishLUCH_eq`).
* `HintClsB snd lib`: the class `hcV` at the bell (the subjects `Fits bl.less`):
  `(hcV snd bl.fol nm).top`, `HintTab env N nm`, `FitH lib (Fits bl.less) bl.fol nm`.
* **`InFragH`**: the hinted analogue of the class of `inFragM`: `MonoCalls`
  on hint-free nomms, or `HintClsB`; `inFragH_iff` (its two halves);
  `inFragH_of_hcV` (membership from the Bool check and the two hypotheses).
* `HintContract`: the conclusion of `hintCls_contract`
  (`CompHintClsSound.lean`) as a predicate, so this file does not import it;
  **`rawMonoH_hintCls`**, **`rawMonoH_inFragH`**: the raw contract at
  `finishLUCH` on `HintClsB` and on `InFragH`, given it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]

/-- **(b) against `finishLUCH` on a class that sees `env`, `N`, the bell**
(the text of `RawMonoD` for the hinted compile). -/
def RawMonoH (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] (lib : Lib)
    (snd : Nomm → NeedOrd → Bool) (FM : MonoClass) : Prop :=
  ∀ (code : Bell → Option Nomm) (bl : Bell) (nm : Nomm) (env : Comp.CallEnv) (s : Straight Map) (N : Needs),
    CodeOK lib code → Annot lib code (SkaModel.Fits bl.less) bl.fol nm → FM env N bl nm → Comp.CalleeNeeds env N →
    Comp.finishLUCH (S := S) env snd nm = some s → BellContract lib N bl true s

variable {S : Type} [Comp.HoonSet S]

theorem rawMonoH_or {lib : Lib} {snd : Nomm → NeedOrd → Bool} {F G : MonoClass} (hF : RawMonoH S Map lib snd F)
    (hG : RawMonoH S Map lib snd G) : RawMonoH S Map lib snd (orM F G) := by
  intro code bl nm env s N hok hA hf hc h
  rcases hf with hf | hf
  · exact hF code bl nm env s N hok hA hf hc h
  · exact hG code bl nm env s N hok hA hf hc h

/-- A class on hint-free nomms. -/
def noHintM (F : MonoClass) : MonoClass := fun env N bl nm => F env N bl nm ∧ nm.noHint = true

/-- **A `RawMonoD` class, restricted to hint-free nomms, has `RawMonoH`**
(`finishLUCH_eq`: on them `finishLUCH env snd` is `finishLUCM`). -/
theorem rawMonoH_of_D {lib : Lib} (snd : Nomm → NeedOrd → Bool) {F : MonoClass} (h : RawMonoD S Map lib F) :
    RawMonoH S Map lib snd (noHintM F) := by
  intro code bl nm env s N hok hA hf hc hs
  rw [Comp.finishLUCH_eq env snd hf.2] at hs
  exact h code bl nm env s N hok hA hf.1 hc hs

/-- **The class of hinted nomms at the bell**: the check `hcV` at the bell's
formula, the code table at the callees, the fits of the callees' `less` at the
bell's subjects. -/
def HintClsB (snd : Nomm → NeedOrd → Bool) (lib : Lib) : MonoClass := fun env N bl nm =>
  (Comp.hcV snd bl.fol nm).top = true ∧ Comp.HintTab env N nm ∧ Comp.FitH lib (SkaModel.Fits bl.less) bl.fol nm

/-- **The hinted analogue of the class of `inFragM`**: the unhinted classes
of the glue (`MonoCalls`) on hint-free nomms, or the class of hinted nomms. -/
def InFragH (S : Type) [Comp.HoonSet S] (snd : Nomm → NeedOrd → Bool) (lib : Lib) : MonoClass :=
  orM (noHintM (MonoCalls S lib)) (HintClsB snd lib)

theorem inFragH_iff {snd : Nomm → NeedOrd → Bool} {lib : Lib} {env : Comp.CallEnv} {N : Needs} {bl : Bell}
    {nm : Nomm} :
    InFragH S snd lib env N bl nm ↔
      (MonoCalls S lib env N bl nm ∧ nm.noHint = true) ∨
        ((Comp.hcV snd bl.fol nm).top = true ∧ Comp.HintTab env N nm ∧
          Comp.FitH lib (SkaModel.Fits bl.less) bl.fol nm) :=
  Iff.rfl

/-- **Membership from the Bool check**: a nomm the check `hcV` takes at the
bell's formula is in `InFragH`, under the two named hypotheses. -/
theorem inFragH_of_hcV {snd : Nomm → NeedOrd → Bool} {lib : Lib} {env : Comp.CallEnv} {N : Needs} {bl : Bell}
    {nm : Nomm} (hm : (Comp.hcV snd bl.fol nm).top = true) (ht : Comp.HintTab env N nm)
    (hfit : Comp.FitH lib (SkaModel.Fits bl.less) bl.fol nm) : InFragH S snd lib env N bl nm :=
  Or.inr ⟨hm, ht, hfit⟩

/-- **The conclusion of `hintCls_contract`** (`CompHintClsSound.lean`) as a
predicate: every member of the check, under `HintTab` and `FitH` at `P`, has
both halves of the contract at the top on the subjects of `P`. -/
def HintContract (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] (lib : Lib)
    (snd : Nomm → NeedOrd → Bool) : Prop :=
  ∀ (env : Comp.CallEnv) (N : Needs) (P : Noun → Prop) {f : Noun} {nm : Nomm} {c : Straight Map},
    (Comp.hcV snd f nm).top = true → Comp.HintTab env N nm → Comp.FitH lib P f nm →
    Comp.finishLUCH (S := S) env snd nm = some c →
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c

/-- **The raw whole-subject contract at `finishLUCH` on `HintClsB`**, from
`HintContract` at the bell's subjects. -/
theorem rawMonoH_hintCls {lib : Lib} {snd : Nomm → NeedOrd → Bool} (H : HintContract S Map lib snd) :
    RawMonoH S Map lib snd (HintClsB snd lib) := by
  intro code bl nm env s N _ _ hf _ hs
  obtain ⟨hm, ht, hfit⟩ := hf
  have C := H env N (SkaModel.Fits bl.less) hm ht hfit hs
  intro x hx args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact C.2 x hx

/-- **The raw whole-subject contract at `finishLUCH` on `InFragH`**: the
unhinted classes through `rawMonoD_calls`, the hinted one through
`rawMonoH_hintCls`. -/
theorem rawMonoH_inFragH [Opt.MapKeys Map] {lib : Lib} {snd : Nomm → NeedOrd → Bool} (H : HintContract S Map lib snd) :
    RawMonoH S Map lib snd (InFragH S snd lib) :=
  rawMonoH_or (rawMonoH_of_D snd (rawMonoD_calls lib)) (rawMonoH_hintCls H)

/-- **`HintContract` holds** (`hintCls_contract`). -/
theorem hintContract_holds (lib : Lib) (snd : Nomm → NeedOrd → Bool) : HintContract S Map lib snd :=
  fun env N P _ _ _ hm ht hfit hc => Comp.hintCls_contract lib env snd N P hm ht hfit hc

/-- **The hinted class at the glue's form**, unconditionally: `RawMonoH` of
`InFragH` (the unhinted `MonoCalls` with `noHint`, or `hcV`'s `top` with
`HintTab` and `FitH` at the bell's own subjects). -/
theorem rawMonoH_inFragH' [Opt.MapKeys Map] (lib : Lib) (snd : Nomm → NeedOrd → Bool) :
    RawMonoH S Map lib snd (InFragH S snd lib) :=
  rawMonoH_inFragH (hintContract_holds lib snd)

end Glue
end SkaModel
end Formalization
