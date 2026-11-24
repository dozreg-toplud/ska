import lemmas.Ska.CompHypOfFragD
import lemmas.Ska.CompFragF

/-!
# `RawMono` on the fragment closed under `[7 p q]`: `FragUFG`

README Gaps 12.21.  (b) of `CompHypOf.lean` for the whole-subject version on
`FragUFG`: `FragUF` (the call-free `FragU`, and `FragI`: `FragE` with `[7 p
q]` where `p`, `q` or both call, in every `Annot` form, and the parents of
`FragE` with the new nomms as parts) with at most 255 `%6`, from the joint
induction `uokc_entNew_of_fragI` (`finishLUC_contractUF`).  It contains
`FragUEG` (`fragUEG_subF`), so `rawMono_fragUEG` and the earlier classes are
corollaries and the statement of `RawMono` is unchanged.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-- The class of the whole-subject version closed under `[7 p q]` with calls
(`FragUF`, README Gaps 12.21). -/
def FragUFG (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := Comp.FragUF S nm ∧ Comp.sixCount nm ≤ 255

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- **(b) for the whole-subject version on `FragUFG`** (`finishLUC_contractUF`). -/
theorem rawMono_fragUFG (lib : Lib) : RawMono S Map lib (FragUFG S) := by
  intro code bl nm env cd N hok hA hf _ h
  exact (Comp.finishLUC_contractUF hok hA hf.1 hf.2 h N).2

/-- **`FragUEG` is inside `FragUFG`**, so `FragUDG` and `FragUCG` are too. -/
theorem fragUEG_subF {nm : Nomm} (h : FragUEG S nm) : FragUFG S nm :=
  ⟨Comp.fragUE_fragUF h.1, h.2⟩

theorem fragUDG_subF {nm : Nomm} (h : FragUDG S nm) : FragUFG S nm := fragUEG_subF (fragUDG_subE h)

theorem fragUCG_subF {nm : Nomm} (h : FragUCG S nm) : FragUFG S nm := fragUDG_subF (fragUCG_sub h)

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`FragUFG`** (and the n-ary version's in `FragUN`). -/
theorem compHyp_of_fragUFG {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUFG S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragUFG lib, rawNary_fragU lib⟩

/-- `[7 [2 [0 3] [0 2]] [4 [0 1]]]`, `[7 [[0 1] [0 1]] [2 [0 3] [0 2]]]`,
the nomm of `[9 2 [2 [0 3] [0 2]]]` and `[[0 1] [7 [0 1] [2 [0 3] [0 2]]]]`
are in `FragUFG`. -/
example : FragUFG S (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) ∧
    FragUFG S (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) ∧
    FragUFG S (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) ∧
    FragUFG S (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))) :=
  ⟨⟨Or.inr (Comp.FragI.weak (Comp.FragI.sevenPU Comp.fragI_ind00
      (Comp.FragU.four (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))) (Comp.NoEntF.pure rfl rfl))), by decide⟩,
    ⟨Or.inr (Comp.FragI.sevenU (Comp.FragU.cons (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
      (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))) Comp.fragI_ind00 Comp.noEntF_ind00), by decide⟩,
    ⟨Or.inr (Comp.FragI.weak (Comp.FragI.sevenPF Comp.fragI_ind00 (Comp.fragI_ind00 (S := S))
      Comp.noEntF_ind00)), by decide⟩,
    ⟨Or.inr (Comp.FragI.weak (Comp.FragI.consT (Comp.FragB.n0 (by decide))
      (Comp.FragI.sevenJ Comp.JNewQ.n0 Comp.fragI_ind00 Comp.noEntF_ind00))), by decide⟩⟩

end PokeM
end SkaModel
end Formalization
