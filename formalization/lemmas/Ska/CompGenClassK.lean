import lemmas.Ska.CompGenClassH

/-!
# The fragment `GenFrag`: pure, a cell, `+mink` its pure value; the cons closed

README Gaps 12.39, item 12.  A nomm of the fragment is pure
(`genFrag_pure`), its formula is a cell (`genFrag_cell`), and `+mink` on
its formula is its pure value on every subject (`genFrag_minkEq`: the
fragment is a `CallTreeA`, whose annotation `mink_pure` reads).  So the
cons's closure in `NextGCS` needs only the two plumbing interfaces
(`closedS_cons_gen`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A nomm of the fragment is pure.** -/
theorem genFrag_pure {f : Noun} {nm : Nomm} (h : GenFrag f nm) : nm.pure = true := by
  induction h with
  | n0 _ => rfl
  | n1 _ => rfl
  | n3 _ ih => simp [Nomm.pure, ih]
  | n4 _ ih => simp [Nomm.pure, ih]
  | n5 _ _ ihp ihq => simp [Nomm.pure, ihp, ihq]
  | cons _ _ ihp ihq => simp [Nomm.pure, ihp, ihq]
  | n7 _ _ ihp ihq => simp [Nomm.pure, ihp, ihq]

/-- **The formula of a nomm of the fragment is a cell.** -/
theorem genFrag_cell {f : Noun} {nm : Nomm} (h : GenFrag f nm) : ∃ a b, f = C a b := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- **The fragment is annotated** at every subject predicate, for any code. -/
theorem ck2_annot {lib : Lib} {code : Bell → Option Nomm} {f : Noun} {nm : Nomm} (h : GenFrag f nm) :
    ∀ P, Annot lib code P f nm := by
  induction h with
  | n0 _ => exact fun _ => Annot.n0
  | n1 k => exact fun _ => Annot.n1
  | n3 _ ih => exact fun P => Annot.n3 (ih P)
  | n4 _ ih => exact fun P => Annot.n4 (ih P)
  | n5 _ _ ihp ihq => exact fun P => Annot.n5 (ihp P) (ihq P)
  | cons hp _ ihp ihq =>
    intro P
    obtain ⟨a1, a2, rfl⟩ := genFrag_cell hp
    exact Annot.cons (ihp P) (ihq P)
  | @n7 fb fc p q _ _ ihp ihq => exact fun P => Annot.n7 (ihp P) (ihq (Img lib P fb))

/-- **`+mink` on the formula of a nomm of the fragment is its pure value.** -/
theorem genFrag_minkEq {f : Noun} {nm : Nomm} (h : GenFrag f nm) (lib : Lib) (P : Noun → Prop) :
    MinkEq lib P f nm := fun s hs gul tm r =>
  mink_pure (codeOK_none lib) (genFrag_pure h) (ck2_annot h P) hs gul tm r

/-- **The cons is closed in `NextGCS`**, given the two plumbing interfaces. -/
theorem closedS_cons_gen (lib : Lib) (N : Needs) (env : CallEnv) (HX : ConsSemPreOf S Map lib)
    (HF : FrontsSGConsOf S Map) : ClosedSCons S Map lib N env :=
  fun hp hq Hp Hq => closedS_cons_of lib N env HX HF (genFrag_pure hp) (genFrag_pure hq) (genFrag_cell hp)
    (genFrag_minkEq hp lib) (genFrag_minkEq hq lib) Hp Hq

end Comp
end SkaModel
end Formalization
