import lemmas.Ska.CompHypOfUOKC
import lemmas.Ska.CompBondCall

/-!
# `RawMono` on the fragment with calls in the parts of calls `FragUD`

README Gaps 12.20.  (b) of `CompHypOf.lean` for the whole-subject version on
`FragUDG`: `FragUD` (the call-free `FragU`, and `FragD`: the indirect call
whose parts may call, the cons whose head calls, the cons whose tail calls
behind a head of `FragB`) with at most 255 `%6`, from the joint induction
`uokc_entNew_of_fragD` (`finishLUC_contractUD`).  It contains `FragUCG`
(`fragUCG_sub`), so `rawMono_fragUCG` is a corollary and the statement of
`RawMono` is unchanged.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-- The class of the whole-subject version on which (b) is proved by the
joint induction with calls in the parts of calls. -/
def FragUDG (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := Comp.FragUD S nm ∧ Comp.sixCount nm ≤ 255

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- **(b) for the whole-subject version on `FragUDG`**
(`finishLUC_contractUD`). -/
theorem rawMono_fragUDG (lib : Lib) : RawMono S Map lib (FragUDG S) := by
  intro code bl nm env cd N hok hA hf _ h
  exact (Comp.finishLUC_contractUD hok hA hf.1 hf.2 h N).2

/-- **`FragUCG` is inside `FragUDG`** (`fragC_fragD`). -/
theorem fragUCG_sub {nm : Nomm} (h : FragUCG S nm) : FragUDG S nm :=
  ⟨h.1.elim Or.inl (fun h' => Or.inr (Comp.fragC_fragD h')), h.2⟩

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`FragUDG`** (and the n-ary version's in `FragUN`): from `CompRest` alone. -/
theorem compHyp_of_fragUDG {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUDG S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragUDG lib, rawNary_fragU lib⟩

/-- `[2 [2 [0 3] [0 2]] [0 2]]` and `[2 [0 3] [2 [0 1] [0 2]]]` (calls in the
parts of a call) are in `FragUDG`. -/
example : FragUDG S (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) ∧
    FragUDG S (Nomm.n2 (Nomm.n0 3) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none) Option.none) :=
  ⟨⟨Or.inr (Comp.FragD.indS (Comp.FragD.ind (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
      (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl) (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl),
      by decide⟩,
    ⟨Or.inr (Comp.FragD.indF (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
      (Comp.FragD.ind (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
        (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl)), by decide⟩⟩

/-- The class with calls in both halves of a cons (`FragE`, README Gaps 12.20). -/
def FragUEG (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := Comp.FragUE S nm ∧ Comp.sixCount nm ≤ 255

/-- **(b) for the whole-subject version on `FragUEG`** (`finishLUC_contractUE`). -/
theorem rawMono_fragUEG (lib : Lib) : RawMono S Map lib (FragUEG S) := by
  intro code bl nm env cd N hok hA hf _ h
  exact (Comp.finishLUC_contractUE hok hA hf.1 hf.2 h N).2

/-- **`FragUDG` is inside `FragUEG`**, so `FragUCG` is too. -/
theorem fragUDG_subE {nm : Nomm} (h : FragUDG S nm) : FragUEG S nm :=
  ⟨h.1.elim Or.inl (fun h' => Or.inr (Comp.FragE.d h')), h.2⟩

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`FragUEG`** (and the n-ary version's in `FragUN`). -/
theorem compHyp_of_fragUEG {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUEG S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragUEG lib, rawNary_fragU lib⟩

/-- `[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` (calls in both halves) is in `FragUEG`. -/
example : FragUEG S (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
    (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) :=
  ⟨Or.inr (Comp.FragE.consI (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
    (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl (Comp.FragE.d (Comp.FragD.ind
      (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl))),
    by decide⟩

end PokeM
end SkaModel
end Formalization
