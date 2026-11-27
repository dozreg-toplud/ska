import lemmas.Glue.GuardX
import lemmas.Glue.EntryFragX

/-!
# `GuardMonoX`, `GuardNaryX` from the final passes (track G, step 5)

LEDGER 2.c.  The run-level part of the two leaves is proved (`runX_blocksOK`:
the raw blocks of the top run of `FragX` meet `BlocksOK`, its result jump
passes no `~`).  What is left of each leaf is its final pass, stated here
exactly, from the run's end state:

* `GuardFinalU`: `+kerf` (a hop block to the run's entry, `+kern` from one
  fresh register) and `+to-straight` (its map path: unproxying, renaming,
  `+chase`) give code that passes no `~` and guards every split;
* `GuardFinalF`: the same of `+need-ord-alloc-regs`, `+coerce-lazy` at
  every lazy entry, the baked constants (none) and `+to-straight`.

`guardMonoX_of`, `guardNaryX_of`: the leaves from these; `compHyp_of_fragX''`:
`CompHyp` on `FragX` from `CompRestOE` and the two final passes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Opt Comp Raw

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

variable {S : Type} [Comp.HoonSet S]

/-- **Leaf: the final whole-subject pass keeps the guard**, from the end
state of a top run of `FragX` (`Inv`, a result jump with no `~`). -/
def GuardFinalU (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] : Prop :=
  ∀ nm (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat) (c : Straight Map),
    Comp.FragX (S := S) nm → Comp.sixCount nm ≤ 255 →
    runL nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) → Inv g1 → JOK nex.th →
    kerf nex g1 = some ((o, sub), g2) → toStraightF g2.cond g2.blocks (Need.this sub) o = some c →
    NoPoison c.blocks ∧ CelGuard c.blocks

/-- **Leaf: the final n-ary pass keeps the guard**, nothing baked. -/
def GuardFinalF (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] : Prop :=
  ∀ nm (ord : NeedOrd) (less : Cape) (bake : Need → Need × List (Nat × Noun)) (nex : NextL S)
    (g1 g2 g3 g4 : Comp.Gen Map) (nedFinal : Need) (c : Straight Map),
    Comp.FragX (S := S) nm → Comp.sixCount nm ≤ 255 → (∀ ned, bake ned = (ned, [])) →
    runL nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) → Inv g1 → JOK nex.th → nex.th.args = [] →
    needOrdAllocRegs ord g1 = some (nedFinal, g2) →
    coerceLazyL nedFinal less nex.th.there nex.laz g2 = some ((), g3) →
    addOps nex.th.there ((bake nedFinal).2.map fun (r, v) => Pole.imm v r) g3 = some ((), g4) →
    toStraightF g4.cond g4.blocks (bake nedFinal).1 nex.th.there = some c →
    NoPoison c.blocks ∧ CelGuard c.blocks

/-- **`GuardMonoX` from the final whole-subject pass.** -/
theorem guardMonoX_of (h : GuardFinalU S Map) : GuardMonoX S Map := by
  intro nm c hf hc hfin
  unfold Comp.finishLU at hfin
  obtain ⟨⟨nex, g1⟩, h1, hfin⟩ := Option.bind_eq_some_iff.mp hfin
  dsimp only at hfin
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, h3⟩ := Option.bind_eq_some_iff.mp hfin
  obtain ⟨I, J⟩ := runX_blocksOK hf hc h1
  exact h nm nex g1 g2 o sub c hf hc h1 I J h2 h3

/-- **`GuardNaryX` from the final n-ary pass.** -/
theorem guardNaryX_of (h : GuardFinalF S Map) : GuardNaryX S Map := by
  intro nm ord less bake c hf hc hbake hfin
  unfold Comp.finishLF at hfin
  obtain ⟨⟨nex, g1⟩, h1, hfin⟩ := Option.bind_eq_some_iff.mp hfin
  dsimp only at hfin
  by_cases ha : nex.th.args ≠ []
  · rw [if_pos ha] at hfin; cases hfin
  rw [if_neg ha] at hfin
  obtain ⟨⟨nedFinal, g2⟩, h2, hfin⟩ := Option.bind_eq_some_iff.mp hfin
  dsimp only at hfin
  obtain ⟨⟨u3, g3⟩, h3, hfin⟩ := Option.bind_eq_some_iff.mp hfin
  obtain ⟨⟨u4, g4⟩, h4, h5⟩ := Option.bind_eq_some_iff.mp hfin
  obtain ⟨I, J⟩ := runX_blocksOK hf hc h1
  exact h nm ord less bake nex g1 g2 g3 g4 nedFinal c hf hc hbake h1 I J (Classical.not_not.mp ha) h2 h3 h4 h5

section
variable (A : Arms M Map J H CR)

/-- **`CompHyp` when every nomm compiled is in `FragX`**, with the run-level
part of `rawEntry` proved: from `CompRestOE` and the two final passes. -/
theorem compHyp_of_fragX'' {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} (P : CompRestOE S M' A lib ref D (FragXM S) (FragXN S))
    (hu : GuardFinalU S Map) (hn : GuardFinalF S Map) : CompHyp A lib ref :=
  compHyp_of_fragX' A P (guardMonoX_of hu) (guardNaryX_of hn)

end

end Glue
end SkaModel
end Formalization
