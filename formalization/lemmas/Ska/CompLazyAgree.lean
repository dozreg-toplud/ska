import lemmas.Ska.CompLazyRun

/-!
# On fork-free needs, the model over `Lazy` is the fork-free model

Each arm of `CompLazyRun.lean` that takes or returns a `next`, on a
fork-free goal, is the arm of `CompModel.lean` with its result embedded by
`ofSure` (`*_toL`).  `runL_toL`: on a nomm that is pure and has no `%6`,
`runL` on a fork-free goal is `run`, whatever the region; so every theorem
about `run` on the fragment `Frag` holds of `runL` (`runL_ok`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem simpleNextL_toL (goal : CGoal S) :
    (simpleNextL (CGoal.toL goal) : CM Map (NextL S)) = Next.toL <$> simpleNext goal := by
  cases goal <;> simp [simpleNextL, simpleNext, CGoal.toL, Next.toL]

theorem bombL_toL (miss : Option Nat) : (bombL miss : CM Map (NextL S)) = Next.toL <$> bomb miss := by
  simp [bombL, bomb, Next.toL]

theorem splitL_toL (nex : Next S) :
    (splitL (Next.toL nex) : CM Map (Lazy S × Lazy S × Nat)) =
      (fun x => (ofSure x.1, ofSure x.2.1, x.2.2)) <$> split nex := by
  simp [splitL, split, Next.toL, splitLoop_ofSure]

theorem intoL_toL (nex : Next S) (axe : Nat) :
    (intoL (Next.toL nex) axe : CM Map (Lazy S × Lazy S × Nat)) =
      (fun x => (ofSure x.1, ofSure x.2.1, x.2.2)) <$> into nex axe := by
  simp [intoL, into, Next.toL, intoLoopL_ofSure]

theorem copyL_toL (first : Next S) (second : Sure S) :
    (copyL (Next.toL first) (ofSure second) : CM Map (NextL S)) = Next.toL <$> copy first second := by
  simp [copyL, copy, Next.toL, copyLazyL_ofSure]

theorem pastL_pure (cod : Bell → Option Bool) (nex : NextL S) {nom : Nomm} (h : nom.pure = true)
    (region : List Nat) : (pastL cod nex nom region : CM Map (NextL S)) = pure nex := by
  unfold pastL
  simp only [hinted_pure cod nom h]
  split <;> rfl

theorem medeL_toL (th : Jmp) (som : Noun) (s : Sure S) :
    (medeL th som (ofSure s) : CM Map Nat) = mede th som s := by
  simp [medeL, mede, walkLazy_ofSure]

theorem collapseLazyAtomL_toL (nex : Next S) :
    (collapseLazyAtomL (Next.toL nex) : CM Map (Option (Nat × Nat))) = collapseLazyAtom nex := by
  simp only [collapseLazyAtomL, collapseLazyAtom, Next.toL, noneEquivalentL_ofSure]
  split
  · rfl
  split
  · rfl
  refine congrArg (fun k => _ >>= k) (funext fun ned => ?_)
  refine congrArg (fun k => _ >>= k) (funext fun x => ?_)
  refine congrArg (fun k => _ >>= k) (funext fun g => ?_)
  split
  · rfl
  have : (mk ⟨Need.this x.1, (ofSure nex.laz).sure.lok⟩ (ofSure nex.laz).fork (ofSure nex.laz).bond : Lazy S) =
      ofSure ⟨Need.this x.1, nex.laz.lok⟩ := rfl
  rw [this, walkLazy_ofSure]
  simp only [collapseGate, if_true, bind_assoc]
  refine congrArg (fun k => _ >>= k) (funext fun ned' => ?_)
  cases ned' with
  | none => simp
  | this r' => by_cases e : x.1 = r' <;> simp [e]
  | pair p q => simp
  | both r h t => simp

end Comp
end SkaModel
end Formalization
