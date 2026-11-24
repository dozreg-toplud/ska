import lemmas.Ska.CompHypOfCall
import lemmas.Ska.CompConsCallWrap

/-!
# `RawMono` with the cons whose head is an indirect call

README Gaps 12.16 (nineteenth session).  `rawMono_consU`: the raw contract
of the whole-subject version (`RawMono`, field (b) of `CompPieces`) on
`ConsUM`, the nomm `[[2 b c] d]` (no callee) with `b`, `c`, `d` in `FragU`,
at most 255 `%6`, and `c` not the literal of a `%bare` formula, through
`consCH_contract_of_annot` (every `Annot` of the nomm).  `FragUCCM` is
`FragUCM` or `ConsUM`, and `compHyp_of_fragCC` derives `CompHyp` from
`CompRest` with it.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-- The cons whose head is an indirect call, on which (b) is proved. -/
def ConsUM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop :=
  ∃ b c d, nm = Nomm.cons (Nomm.n2 b c Option.none) d ∧ Comp.FragU (S := S) b ∧ Comp.FragU (S := S) c ∧
    Comp.FragU (S := S) d ∧ Comp.sixCount b + Comp.sixCount c + Comp.sixCount d ≤ 255 ∧
    Comp.bareLitQ c = false

/-- The class of the whole-subject version with an indirect call at the top
or in the head of a cons. -/
def FragUCCM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := FragUCM S nm ∨ ConsUM S nm

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- **(b) for the whole-subject version on `ConsUM`**
(`consCH_contract_of_annot`). -/
theorem rawMono_consU (lib : Lib) : RawMono S Map lib (ConsUM S) := by
  intro code bl nm env cd N hok hA hf _ h
  obtain ⟨b, c, d, rfl, hb, hc, hd, hcount, hbl⟩ := hf
  have H := Comp.consCH_contract_of_annot hok hA rfl hb hc hd hcount hbl env cd h N
  intro s hs args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H s hs

/-- **(b) for the whole-subject version on `FragUCCM`**. -/
theorem rawMono_fragUCC (lib : Lib) : RawMono S Map lib (FragUCCM S) :=
  rawMono_or (rawMono_fragUC lib) (rawMono_consU lib)

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`FragUCCM`** (and the n-ary version's in `FragUN`): from `CompRest` alone. -/
theorem compHyp_of_fragCC {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUCCM S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragUCC lib, rawNary_fragU lib⟩

/-- `[[2 [0 3] [0 2]] [0 1]]` is in `ConsUM`. -/
example : ConsUM S (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) :=
  ⟨_, _, _, rfl, Comp.FragU.x (Comp.FragX.frag fun _ => trivial), Comp.FragU.x (Comp.FragX.frag fun _ => trivial),
    Comp.FragU.x (Comp.FragX.frag fun _ => trivial), by simp [Comp.sixCount], rfl⟩

end PokeM
end SkaModel
end Formalization
