import lemmas.Ska.CompHypOfCons
import lemmas.Ska.CompFragUC

/-!
# `RawMono` on the fragment with calls `FragUC`

README Gaps 12.17 (twentieth session).  (b) of `CompHypOf.lean` for the
whole-subject version on `FragUCG`: `FragUC` (the call-free `FragU`, the
indirect call, the cons whose head calls) with at most 255 `%6`, from the
joint induction `UOKC` (`finishLUC_contractUC`).  It contains `FragUCCM`
(`fragUCCM_sub`), so `rawMono_fragUCC` is a corollary.  Since the twenty-second
session `FragC` has the cons whose tail is an indirect call (`FragC.consT`,
README Gaps 12.19), so `RawMono` covers `[[0 1] [2 [0 3] [0 2]]]` and
`[[4 [0 3]] [2 [0 3] [0 2]]]`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-- The class of the whole-subject version on which (b) is proved by the
joint induction. -/
def FragUCG (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := Comp.FragUC S nm ∧ Comp.sixCount nm ≤ 255

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- **(b) for the whole-subject version on `FragUCG`**
(`finishLUC_contractUC`). -/
theorem rawMono_fragUCG (lib : Lib) : RawMono S Map lib (FragUCG S) := by
  intro code bl nm env cd N hok hA hf _ h
  exact (Comp.finishLUC_contractUC hok hA hf.1 hf.2 h N).2

/-- **`FragUCCM` is inside `FragUCG`**: `FragUM` is `FragU` with at most 255
`%6`, `IndUM` the indirect call of `FragC`, `ConsUM` a cons of `FragC`. -/
theorem fragUCCM_sub {nm : Nomm} (h : FragUCCM S nm) : FragUCG S nm := by
  rcases h with (h | ⟨p, q, rfl, hp, hq, hc, hb⟩) | ⟨b, c, d, rfl, hb, hc, hd, hcount, hbl⟩
  · exact ⟨Or.inl h.1, h.2⟩
  · exact ⟨Or.inr (Comp.FragC.ind hp hq hb), hc⟩
  · exact ⟨Or.inr (Comp.FragC.consH (Comp.FragC.ind hb hc hbl) hd), by simp only [Comp.sixCount]; omega⟩

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`FragUCG`** (and the n-ary version's in `FragUN`): from `CompRest` alone. -/
theorem compHyp_of_fragUCG {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUCG S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragUCG lib, rawNary_fragU lib⟩

/-- `[[0 1] [2 [0 3] [0 2]]]` and `[[4 [0 3]] [2 [0 3] [0 2]]]` (a call in the
tail of a cons, README Gaps 12.19) are in `FragUCG`. -/
example : FragUCG S (Nomm.cons (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) ∧
    FragUCG S (Nomm.cons (Nomm.n4 (Nomm.n0 3)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) :=
  ⟨⟨Or.inr (Comp.FragC.consT (Comp.FragB.n0 (Nat.le_refl 1)) (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
      (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl), by decide⟩,
    ⟨Or.inr (Comp.FragC.consT (Comp.FragB.n4 (Comp.FragX.frag fun _ => trivial))
      (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl),
      by decide⟩⟩

/-- `[[[2 [0 3] [0 2]] [0 1]] [0 1]]` is in `FragUCG` and not in `FragUCCM`'s
shapes (its head is a cons). -/
example : FragUCG S (Nomm.cons (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n0 1)) :=
  ⟨Or.inr (Comp.FragC.consH (Comp.FragC.consH (Comp.FragC.ind (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))
    (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)) rfl) (Comp.FragU.x (Comp.FragX.frag fun _ => trivial)))
    (Comp.FragU.x (Comp.FragX.frag fun _ => trivial))), by decide⟩

end PokeM
end SkaModel
end Formalization
