import lemmas.Glue.MonoCalls
import lemmas.Ska.CompGenClassM

/-!
# Glue: the unary contract of track C's one induction, in the glue's form

README Gaps 12.39, item 12.  `ContractConsFrag`: the unary contract under
`%done` (`finishLUC`) of every nomm of `ConsFrag` (`[0 a]` with `a ≥ 2`,
`[1 k]`, the cons, `[7 p q]`) at ITS OWN formula, on every subject: the form
`finishLUC_contractGD` gives (track C, `CompGenClassM.lean`).  Here it is
turned into the glue's raw whole-subject contract `RawMonoD`:

* `rawMonoD_consFragB`: `RawMonoD` on the class `ConsFragB` (the bell's
  formula is the nomm's own formula), from `ContractConsFrag`.  The raw
  contract asks the contract at `bl.fol` with `Annot … bl.fol nm`; on
  `ConsFragB` the two formulas are the same.
* `rawMonoD_consFragM`: `RawMonoD` on `liftMC (ConsFragM S)` (any formula the
  nomm annotates) holds ALREADY, with no premise, from `rawMonoM_fragX`:
  `ConsFrag ⊆ FragX` (`consFrag_fragX`, by `FragX.frag`: `Frag` holds of
  every nomm of `ConsFrag` at every goal), with no `%6`.

So on `ConsFrag` the new contract replaces no glue class: its fragment lies in
`FragX`, on which `classLeaves_fragX` proves every field.  Why
`ContractConsFrag` does not give `liftMC (ConsFragM S)` by itself:
`ContractFwd` is indexed by `+mink`'s fuel with `OracleFwd` at the SAME fuel,
and the nomm's own formula may need more fuel than the bell's formula it
annotates (`Annot.n8g` with `[0 1]` folded to a literal `v`: `[8 b c]`
annotates `[7 [p [1 v]] q]`, whose formula `[7 [fb [1 v]] fc]` runs `fb` one
level deeper), so the forward half does not move from one formula to the
other.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock

variable {S : Type} [Comp.HoonSet S] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]

/-- **The unary contract on `ConsFrag`, at the nomm's own formula** (the
form of `finishLUC_contractGD` with `P` true). -/
def ContractConsFrag (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    (lib : Lib) : Prop :=
  ∀ (env : Comp.CallEnv) (N : Needs) {f : Noun} {nm : Nomm}, Comp.ConsFrag f nm → ∀ {c : Straight Map},
    Comp.finishLUC (S := S) (Map := Map) env nm = some c →
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c

/-- **The nomms of `ConsFrag`**, read as a class of nomms (any formula). -/
def ConsFragM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := ∃ f, Comp.ConsFrag f nm

/-- **The nomms of `ConsFrag` at the bell's formula**: a class that sees the
bell. -/
def ConsFragB : MonoClass := fun _ _ bl nm => Comp.ConsFrag bl.fol nm

theorem cn2_frag {f : Noun} {nm : Nomm} (h : Comp.ConsFrag f nm) : ∀ goal : Comp.CGoal S, Comp.Frag nm goal := by
  induction h with
  | n0 _ => intro goal; simp only [Comp.Frag]
  | n1 _ => intro goal; simp only [Comp.Frag]
  | cons _ _ ihp ihq => intro goal; exact ⟨fun _ _ => ihp _, fun _ _ => ihq _⟩
  | n7 _ _ ihp ihq => intro goal; exact ⟨ihq goal, fun _ _ => ihp _⟩

theorem cn2_sixCount {f : Noun} {nm : Nomm} (h : Comp.ConsFrag f nm) : Comp.sixCount nm = 0 := by
  induction h with
  | n0 _ => rfl
  | n1 _ => rfl
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | n7 _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]

/-- **`ConsFrag` lies in `FragX`** (`FragX.frag`). -/
theorem consFrag_fragX {f : Noun} {nm : Nomm} (h : Comp.ConsFrag f nm) : Comp.FragX (S := S) nm :=
  Comp.FragX.frag (cn2_frag h)

theorem consFragM_fragXM {nm : Nomm} (h : ConsFragM S nm) : FragXM S nm :=
  let ⟨_, hf⟩ := h
  ⟨consFrag_fragX hf, by rw [cn2_sixCount hf]; omega⟩

/-- `ConsFragB` is inside the glue's `FragX` class. -/
theorem consFragB_sub {env : Comp.CallEnv} {N : Needs} {bl : Bell} {nm : Nomm} (h : ConsFragB env N bl nm) :
    liftMC (FragXM S) env N bl nm :=
  consFragM_fragXM ⟨bl.fol, h⟩

/-- **The raw contract on `ConsFragB` from track C's unary contract.** -/
theorem rawMonoD_consFragB (lib : Lib) (H : ContractConsFrag S Map lib) : RawMonoD S Map lib ConsFragB := by
  intro code bl nm env s N hok hA hf hc hs
  rw [Comp.finishLUCM_eq env (Comp.noDirect_of_fragX (consFrag_fragX (S := S) hf))] at hs
  obtain ⟨-, H2⟩ := H env N hf hs
  intro x hx args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H2 x

/-- **The raw contract on `ConsFragM`, any annotated formula, with no
premise**: `ConsFrag ⊆ FragX` and `rawMonoM_fragX`. -/
theorem rawMonoD_consFragM [Opt.MapKeys Map] (lib : Lib) : RawMonoD S Map lib (liftMC (ConsFragM S)) :=
  rawMonoD_of_M fun code bl nm env s N hok hA hf hc hs =>
    rawMonoM_fragX lib code bl nm env s N hok hA (consFragM_fragXM hf) hc hs

/-- **`ContractConsFrag` holds**: track C's `contract_consFrag`
(`CompGenClassM.lean`). -/
theorem contractConsFrag_holds (lib : Lib) : ContractConsFrag S Map lib :=
  fun env N _ _ hf _ h => Comp.contract_consFrag lib env N hf h

/-- **`RawMonoD` of `ConsFragB` through the new relation**, no premise. -/
theorem rawMonoD_consFragB_new (lib : Lib) : RawMonoD S Map lib ConsFragB :=
  rawMonoD_consFragB lib (contractConsFrag_holds lib)

end Glue
end SkaModel
end Formalization
