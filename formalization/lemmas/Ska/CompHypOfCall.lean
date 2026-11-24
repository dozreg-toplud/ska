import lemmas.Ska.CompHypOf
import lemmas.Ska.CompIndirectWrapTop

/-!
# `RawMono` on a class with indirect calls

README Gaps 12.12 (sixteenth session).  `rawMono_fragUC`: the raw contract of
the whole-subject version (`RawMono`, field (b) of `CompPieces`) on
`FragUCM`, the union of `FragUM` (call-free) and `IndUM`: the indirect call
`[2 p q]` with no callee, `p` and `q` in `FragU`, at most 255 `%6`, and `q`
not the literal `[1 f]` of a `%bare` formula (`bareLitQ`).  `RawMono` quantifies over every
`Annot` of the bell's formula by the nomm, which `indirectTop_contractA`
covers through `minkN2_of_annot`.  `compHyp_of_fragC` is `compHyp_of_frag`
with this class for the whole-subject version.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-- The indirect calls on which (b) is proved: `[2 p q]` with no callee,
`p` and `q` in `FragU`, at most 255 `%6`, `q` not the literal of a `%bare`
formula. -/
def IndUM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop :=
  ∃ p q, nm = Nomm.n2 p q Option.none ∧ Comp.FragU (S := S) p ∧ Comp.FragU (S := S) q ∧
    Comp.sixCount nm ≤ 255 ∧ Comp.bareLitQ q = false

/-- The class of the whole-subject version with indirect calls. -/
def FragUCM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := FragUM S nm ∨ IndUM S nm

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- `RawMono` of a union. -/
theorem rawMono_or {lib : Lib} {F G : Nomm → Prop} (hF : RawMono S Map lib F) (hG : RawMono S Map lib G) :
    RawMono S Map lib (fun nm => F nm ∨ G nm) := by
  intro code bl nm env s N hok hA hf hc h
  rcases hf with hf | hf
  · exact hF code bl nm env s N hok hA hf hc h
  · exact hG code bl nm env s N hok hA hf hc h

/-- **(b) for the whole-subject version on the indirect calls `IndUM`**
(`indirectTop_contractA`). -/
theorem rawMono_indU (lib : Lib) : RawMono S Map lib (IndUM S) := by
  intro code bl nm env s N hok hA hf _ h
  obtain ⟨p, q, rfl, hp, hq, hc, hb⟩ := hf
  exact (Comp.indirectTop_contractA hok hA hp hq hc hb h N).2

/-- **(b) for the whole-subject version on `FragUCM`**: `FragU` with at most
255 `%6`, or one indirect call of two such parts. -/
theorem rawMono_fragUC (lib : Lib) : RawMono S Map lib (FragUCM S) :=
  rawMono_or (rawMono_fragU lib) (rawMono_indU lib)

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`FragUCM`** (and the n-ary version's in `FragUN`): from `CompRest` alone. -/
theorem compHyp_of_fragC {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUCM S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragUC lib, rawNary_fragU lib⟩

/-- The formula `[6 [1 0] [2 [0 3] [0 2]] [0 0]]` has the nomm
`[2 [0 3] [0 2]]` (`Annot.six0`), which `IndUM` covers and the formula
`[2 b c]` of `indirectTop_contract` does not. -/
example (lib : Lib) (code : Bell → Option Nomm) (P : Noun → Prop) :
    Annot lib code P (n4 (Nock.A 6) (quote (Nock.A 0)) (n3 (Nock.A 2) (slot 3) (slot 2)) (slot 0))
      (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) :=
  Annot.six0 (fun _ _ _ => ⟨1, rfl⟩) (Annot.indirect Annot.n0 Annot.n0)

example : Comp.bareLitQ (Nomm.n0 2) = false ∧
    Comp.bareLitQ (Nomm.n1 (C (Nock.A 11) (C (Nock.A Tag.bare) (C (Nock.A 0) (Nock.A 1))))) = true := by decide

end PokeM
end SkaModel
end Formalization
