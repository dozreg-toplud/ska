module

public import lemmas.Sound
/-!
`nock` is the Nock evaluator as a partial function.  It is the same relation
as `Eval` (`nock_eq_some_iff`), in a form that `simp` can run: each opcode has
one rewrite rule, and a proof about an arm unfolds the arm's formula once and
lets those rules execute it on a subject that is partly symbolic.
-/

@[expose] public section

namespace Formalization
namespace Nock

/-- The branch of opcode 6: `test` picks the formula that runs next. -/
def pick (test yes no : Noun) : Option Noun :=
  match test with
  | Noun.atom 0 => some yes
  | Noun.atom 1 => some no
  | _ => none

/-- The increment of opcode 4, defined on atoms only. -/
def lus : Noun → Option Noun
  | Noun.atom atom => some (A (atom + 1))
  | Noun.cell _ _ => none

def nock (subject formula : Noun) : Option Noun :=
  match formula with
  | Noun.cell (Noun.cell b c) d => do
      let left ← nock subject (C b c)
      let right ← nock subject d
      pure (C left right)
  | Noun.cell (Noun.atom 0) (Noun.atom axis) => slot? axis subject
  | Noun.cell (Noun.atom 1) noun => some noun
  | Noun.cell (Noun.atom 2) (Noun.cell b c) => do
      let subject' ← nock subject b
      let formula' ← nock subject c
      nock subject' formula'
  | Noun.cell (Noun.atom 3) b => do
      let noun ← nock subject b
      pure (wut noun)
  | Noun.cell (Noun.atom 4) b => do
      let noun ← nock subject b
      lus noun
  | Noun.cell (Noun.atom 5) (Noun.cell b c) => do
      let left ← nock subject b
      let right ← nock subject c
      pure (eqCode left right)
  | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) => do
      let test ← nock subject b
      let next ← pick test c d
      nock subject next
  | Noun.cell (Noun.atom 7) (Noun.cell b c) => do
      let subject' ← nock subject b
      nock subject' c
  | Noun.cell (Noun.atom 8) (Noun.cell b c) => do
      let produced ← nock subject b
      nock (C produced subject) c
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom axis) c) => do
      let core ← nock subject c
      let arm ← slot? axis core
      nock core arm
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom axis) c) d) => do
      let replacement ← nock subject c
      let editedBase ← nock subject d
      edit? axis replacement editedBase
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell _ c) d) => do
      let _ ← nock subject c
      nock subject d
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) c) => nock subject c
  | _ => none
partial_fixpoint


/-! ## One rewrite rule per opcode -/

theorem nock_cell (s b c d : Noun) :
    nock s (C (C b c) d) =
      (nock s (C b c)).bind fun left => (nock s d).bind fun right => some (C left right) := by
  rw [nock]; rfl

theorem nock_op0 (s : Noun) (axis : Nat) : nock s (C (A 0) (A axis)) = slot? axis s := by
  rw [nock]

theorem nock_op1 (s noun : Noun) : nock s (C (A 1) noun) = some noun := by
  rw [nock]

theorem nock_op2 (s b c : Noun) :
    nock s (C (A 2) (C b c)) =
      (nock s b).bind fun subject' => (nock s c).bind fun formula' => nock subject' formula' := by
  rw [nock]; rfl

theorem nock_op3 (s b : Noun) :
    nock s (C (A 3) b) = (nock s b).bind fun noun => some (wut noun) := by
  rw [nock]; rfl

theorem nock_op4 (s b : Noun) : nock s (C (A 4) b) = (nock s b).bind lus := by
  rw [nock]; rfl

theorem nock_op5 (s b c : Noun) :
    nock s (C (A 5) (C b c)) =
      (nock s b).bind fun left => (nock s c).bind fun right => some (eqCode left right) := by
  rw [nock]; rfl

theorem nock_op6 (s b c d : Noun) :
    nock s (C (A 6) (C b (C c d))) =
      (nock s b).bind fun test => (pick test c d).bind fun next => nock s next := by
  rw [nock]; rfl

theorem nock_op7 (s b c : Noun) :
    nock s (C (A 7) (C b c)) = (nock s b).bind fun subject' => nock subject' c := by
  rw [nock]; rfl

theorem nock_op8 (s b c : Noun) :
    nock s (C (A 8) (C b c)) = (nock s b).bind fun produced => nock (C produced s) c := by
  rw [nock]; rfl

theorem nock_op9 (s c : Noun) (axis : Nat) :
    nock s (C (A 9) (C (A axis) c)) =
      (nock s c).bind fun core => (slot? axis core).bind fun arm => nock core arm := by
  rw [nock]; rfl

theorem nock_op10 (s c d : Noun) (axis : Nat) :
    nock s (C (A 10) (C (C (A axis) c) d)) =
      (nock s c).bind fun replacement =>
        (nock s d).bind fun editedBase => edit? axis replacement editedBase := by
  rw [nock]; rfl

theorem nock_op11_cell (s b c d : Noun) :
    nock s (C (A 11) (C (C b c) d)) = (nock s c).bind fun _ => nock s d := by
  rw [nock]; rfl

theorem nock_op11_atom (s c : Noun) (tag : Nat) :
    nock s (C (A 11) (C (A tag) c)) = nock s c := by
  rw [nock]

/-! ## Helpers of the rules -/

@[simp] theorem pick_zero (yes no : Noun) : pick (A 0) yes no = some yes := rfl

@[simp] theorem pick_one (yes no : Noun) : pick (A 1) yes no = some no := rfl

theorem pick_eqCode (left right yes no : Noun) :
    pick (eqCode left right) yes no = some (if left = right then yes else no) := by
  unfold eqCode
  split <;> rfl

theorem pick_eq_some {test yes no next : Noun} (h : pick test yes no = some next) :
    (test = A 0 ∧ next = yes) ∨ (test = A 1 ∧ next = no) := by
  unfold pick at h
  split at h
  · exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
  · simp at h

@[simp] theorem lus_atom (atom : Nat) : lus (A atom) = some (A (atom + 1)) := rfl

@[simp] theorem lus_cell (head tail : Noun) : lus (C head tail) = none := rfl

theorem lus_eq_some {noun out : Noun} (h : lus noun = some out) :
    ∃ atom, noun = A atom ∧ out = A (atom + 1) := by
  cases noun with
  | atom atom => exact ⟨atom, rfl, (Option.some.inj h).symm⟩
  | cell _ _ => simp [lus] at h

/-! ## `nock` and `Eval` are the same relation -/

theorem nock_of_eval {subject formula out : Noun} (h : Eval subject formula out) :
    nock subject formula = some out := by
  induction h with
  | cell _ _ ihl ihr => simp [nock_cell, ihl, ihr]
  | op0 hslot => rw [nock_op0]; exact slot?_complete hslot
  | op1 => exact nock_op1 _ _
  | op2 _ _ _ ihb ihc ih => simp [nock_op2, ihb, ihc, ih]
  | op3 _ ih => simp [nock_op3, ih]
  | op4 _ ih => simp [nock_op4, ih]
  | op5 _ _ ihb ihc => simp [nock_op5, ihb, ihc]
  | op6_zero _ _ ihb ih => simp [nock_op6, ihb, ih]
  | op6_one _ _ ihb ih => simp [nock_op6, ihb, ih]
  | op7 _ _ ihb ih => simp [nock_op7, ihb, ih]
  | op8 _ _ ihb ih => simp [nock_op8, ihb, ih]
  | op9 _ _ ihc ih =>
    simp only [nock_op2, nock_op0, slot?_one, Option.bind_some] at ih
    simp [nock_op9, ihc, ih]
  | op10 _ _ hedit ihc ihd => simp [nock_op10, ihc, ihd, edit?_complete hedit]
  | op11_cell _ _ _ ihc ihd ih =>
    rw [nock_op0, slot?_step 3 (by omega)] at ih
    simp only [Nat.reduceDiv, slot?_one, Option.bind_some, child, Nat.reduceMod, decide_true,
      if_true, Option.some.injEq] at ih
    subst ih
    simp [nock_op11_cell, ihc, ihd]
  | op11_atom _ ih => simp [nock_op11_atom, ih]

theorem eval_of_nock {subject formula out : Noun} (h : nock subject formula = some out) :
    Eval subject formula out := by
  refine nock.partial_correctness (fun subject formula out => Eval subject formula out)
    ?_ subject formula out h
  intro rec ih subject formula out h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨left, hl, right, hr, rfl⟩ := h
    exact Eval.cell (ih _ _ _ hl) (ih _ _ _ hr)
  · exact Eval.op0 (slot?_sound _ h)
  · cases h; exact Eval.op1
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨subject', hb, formula', hc, h⟩ := h
    exact Eval.op2 (ih _ _ _ hb) (ih _ _ _ hc) (ih _ _ _ h)
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨noun, hb, rfl⟩ := h
    exact Eval.op3 (ih _ _ _ hb)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨noun, hb, h⟩ := h
    obtain ⟨atom, rfl, rfl⟩ := lus_eq_some h
    exact Eval.op4 (ih _ _ _ hb)
  · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨left, hb, right, hc, rfl⟩ := h
    exact Eval.op5 (ih _ _ _ hb) (ih _ _ _ hc)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨test, hb, next, hpick, h⟩ := h
    rcases pick_eq_some hpick with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Eval.op6_zero (ih _ _ _ hb) (ih _ _ _ h)
    · exact Eval.op6_one (ih _ _ _ hb) (ih _ _ _ h)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨subject', hb, h⟩ := h
    exact Eval.op7 (ih _ _ _ hb) (ih _ _ _ h)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨produced, hb, h⟩ := h
    exact Eval.op8 (ih _ _ _ hb) (ih _ _ _ h)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨core, hc, arm, harm, h⟩ := h
    exact Eval.op9 (ih _ _ _ hc)
      (Eval.op2 (Eval.op0 Slot.one) (Eval.op0 (slot?_sound _ harm)) (ih _ _ _ h))
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨replacement, hc, editedBase, hd, h⟩ := h
    exact Eval.op10 (ih _ _ _ hc) (ih _ _ _ hd) (edit?_sound _ h)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨hint, hc, h⟩ := h
    exact Eval.op11_cell (ih _ _ _ hc) (ih _ _ _ h) (Eval.op0 (Slot.right Slot.one))
  · exact Eval.op11_atom (ih _ _ _ h)
  · simp at h

/-- The partial function and the big-step relation of the spec agree. -/
theorem nock_eq_some_iff {subject formula out : Noun} :
    nock subject formula = some out ↔ Eval subject formula out :=
  ⟨eval_of_nock, nock_of_eval⟩

theorem Eval.deterministic {subject formula out out' : Noun}
    (h : Eval subject formula out) (h' : Eval subject formula out') : out = out' := by
  have := nock_of_eval h
  rw [nock_of_eval h'] at this
  exact (Option.some.inj this).symm

/-- What the kernel computes with fuel is a fact about `nock`. -/
theorem nock_of_evalFuel {fuel : Nat} {subject formula out : Noun}
    (h : evalFuel fuel subject formula = some out) : nock subject formula = some out :=
  nock_of_eval (evalFuel_sound fuel h)

end Nock
end Formalization

end
