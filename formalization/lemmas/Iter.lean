module

public import lemmas.Exec
/-!
Nock by the depth of its calls.

`nockW call s f` runs the formula `f` on `s` like `nock`, by structural
recursion on `f`, except that the two opcodes that run a computed formula
(`2` and `9`) hand it to `call`.  So `nock` is `nockW nock` (`nock_eq_nockW`),
and `iterN k`, the `k`-th iterate of `nockW` from the function that always
crashes, is Nock with calls at most `k` deep.  What `iterN k` returns, `nock`
returns (`iterN_sound`), and what `nock` returns, some `iterN k` returns
(`iterN_complete`).

This gives an induction on the depth of calls: a proof that the Nock of a
loop computes a model may induct on `k` and meet the loop's calls to itself
at `iterN k`, while the calls to other gates are met by their theorems about
`nock`, through `iterN_sound`.
-/

@[expose] public section

namespace Formalization
namespace Nock

/-- `x` is below `y`: whatever `x` returns, `y` returns. -/
def Below? {α : Type} (x y : Option α) : Prop := ∀ a, x = some a → y = some a

theorem Below?.refl {α : Type} (x : Option α) : Below? x x := fun _ h => h

theorem Below?.bind {α β : Type} {x x' : Option α} {f f' : α → Option β}
    (hx : Below? x x') (hf : ∀ a, Below? (f a) (f' a)) : Below? (x.bind f) (x'.bind f') := by
  intro b h
  cases x with
  | none => simp at h
  | some a => rw [hx a rfl]; exact hf a b h

/-- One level of Nock: the formulas that opcodes `2` and `9` compute go to `call`. -/
def nockW (call : Noun → Noun → Option Noun) (subject formula : Noun) : Option Noun :=
  match formula with
  | Noun.cell (Noun.cell b c) d => do
      let left ← nockW call subject (C b c)
      let right ← nockW call subject d
      pure (C left right)
  | Noun.cell (Noun.atom 0) (Noun.atom axis) => slot? axis subject
  | Noun.cell (Noun.atom 1) noun => some noun
  | Noun.cell (Noun.atom 2) (Noun.cell b c) => do
      let subject' ← nockW call subject b
      let formula' ← nockW call subject c
      call subject' formula'
  | Noun.cell (Noun.atom 3) b => do
      let noun ← nockW call subject b
      pure (wut noun)
  | Noun.cell (Noun.atom 4) b => do
      let noun ← nockW call subject b
      lus noun
  | Noun.cell (Noun.atom 5) (Noun.cell b c) => do
      let left ← nockW call subject b
      let right ← nockW call subject c
      pure (eqCode left right)
  | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) => do
      let test ← nockW call subject b
      let next ← pick test c d
      nockW call subject next
  | Noun.cell (Noun.atom 7) (Noun.cell b c) => do
      let subject' ← nockW call subject b
      nockW call subject' c
  | Noun.cell (Noun.atom 8) (Noun.cell b c) => do
      let produced ← nockW call subject b
      nockW call (C produced subject) c
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom axis) c) => do
      let core ← nockW call subject c
      let arm ← slot? axis core
      call core arm
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom axis) c) d) => do
      let replacement ← nockW call subject c
      let editedBase ← nockW call subject d
      edit? axis replacement editedBase
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) c) d) => do
      let _ ← nockW call subject c
      nockW call subject d
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) c) => nockW call subject c
  | _ => none
partial_fixpoint

/-! ## One rule per opcode, for `simp` -/

section rules
variable (call : Noun → Noun → Option Noun) (s : Noun)

theorem nockW_cell (b c d : Noun) :
    nockW call s (C (C b c) d) =
      (nockW call s (C b c)).bind fun l => (nockW call s d).bind fun r => some (C l r) := by
  rw [nockW]; rfl
theorem nockW_op0 (axis : Nat) : nockW call s (C (A 0) (A axis)) = slot? axis s := by rw [nockW]; try rfl
theorem nockW_op1 (k : Noun) : nockW call s (C (A 1) k) = some k := by rw [nockW]; try rfl
theorem nockW_op2 (b c : Noun) :
    nockW call s (C (A 2) (C b c)) =
      (nockW call s b).bind fun s' => (nockW call s c).bind fun f' => call s' f' := by rw [nockW]; try rfl
theorem nockW_op3 (b : Noun) : nockW call s (C (A 3) b) = (nockW call s b).bind fun x => some (wut x) := by
  rw [nockW]; try rfl
theorem nockW_op4 (b : Noun) : nockW call s (C (A 4) b) = (nockW call s b).bind lus := by rw [nockW]; try rfl
theorem nockW_op5 (b c : Noun) :
    nockW call s (C (A 5) (C b c)) =
      (nockW call s b).bind fun x => (nockW call s c).bind fun y => some (eqCode x y) := by rw [nockW]; try rfl
theorem nockW_op6 (b c d : Noun) :
    nockW call s (C (A 6) (C b (C c d))) =
      (nockW call s b).bind fun t => (pick t c d).bind fun next => nockW call s next := by
  rw [nockW]; rfl
theorem nockW_op7 (b c : Noun) :
    nockW call s (C (A 7) (C b c)) = (nockW call s b).bind fun s' => nockW call s' c := by rw [nockW]; try rfl
theorem nockW_op8 (b c : Noun) :
    nockW call s (C (A 8) (C b c)) = (nockW call s b).bind fun h => nockW call (C h s) c := by
  rw [nockW]; try rfl
theorem nockW_op9 (axis : Nat) (c : Noun) :
    nockW call s (C (A 9) (C (A axis) c)) =
      (nockW call s c).bind fun core => (slot? axis core).bind fun arm => call core arm := by
  rw [nockW]; try rfl
theorem nockW_op10 (axis : Nat) (c d : Noun) :
    nockW call s (C (A 10) (C (C (A axis) c) d)) =
      (nockW call s c).bind fun r => (nockW call s d).bind fun b => edit? axis r b := by rw [nockW]; try rfl
theorem nockW_op11_cell (tag : Nat) (c d : Noun) :
    nockW call s (C (A 11) (C (C (A tag) c) d)) = (nockW call s c).bind fun _ => nockW call s d := by
  rw [nockW]; try rfl
theorem nockW_op11_ctag (x y c d : Noun) : nockW call s (C (A 11) (C (C (C x y) c) d)) = none := by
  rw [nockW.eq_def]; rfl
theorem nockW_op11_atom (tag : Nat) (c : Noun) :
    nockW call s (C (A 11) (C (A tag) c)) = nockW call s c := by rw [nockW]; try rfl

end rules

attribute [nock_exec] nockW_cell nockW_op0 nockW_op1 nockW_op2 nockW_op3 nockW_op4 nockW_op5
  nockW_op6 nockW_op7 nockW_op8 nockW_op9 nockW_op10 nockW_op11_cell nockW_op11_atom

theorem nockW_ite (call : Noun → Noun → Option Noun) (c : Prop) [Decidable c] (s f g : Noun) :
    nockW call s (if c then f else g) = if c then nockW call s f else nockW call s g := by
  split <;> rfl

/-! ## `nock` is `nockW nock` -/

theorem nock_atom (s : Noun) (a : Nat) : nock s (A a) = none := by rw [nock.eq_def]

theorem nock_eq_nockW : ∀ (s f : Noun), nock s f = nockW nock s f
  | s, Noun.atom a => by rw [nock_atom, nockW.eq_def]
  | s, Noun.cell (Noun.cell b c) d => by
    rw [nock_cell, nockW_cell, nock_eq_nockW s (C b c), nock_eq_nockW s d]
  | s, Noun.cell (Noun.atom 0) (Noun.atom ax) => by rw [nock_op0, nockW_op0]
  | s, Noun.cell (Noun.atom 1) k => by rw [nock_op1, nockW_op1]
  | s, Noun.cell (Noun.atom 2) (Noun.cell b c) => by
    rw [nock_op2, nockW_op2, nock_eq_nockW s b, nock_eq_nockW s c]
  | s, Noun.cell (Noun.atom 3) b => by rw [nock_op3, nockW_op3, nock_eq_nockW s b]
  | s, Noun.cell (Noun.atom 4) b => by rw [nock_op4, nockW_op4, nock_eq_nockW s b]
  | s, Noun.cell (Noun.atom 5) (Noun.cell b c) => by
    rw [nock_op5, nockW_op5, nock_eq_nockW s b, nock_eq_nockW s c]
  | s, Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) => by
    rw [nock_op6, nockW_op6, nock_eq_nockW s b]
    congr 1; funext t
    match t with
    | Noun.atom 0 => simp only [pick_zero, Option.bind_some, nock_eq_nockW s c]
    | Noun.atom 1 => simp only [pick_one, Option.bind_some, nock_eq_nockW s d]
    | Noun.atom (n + 2) => rfl
    | Noun.cell _ _ => rfl
  | s, Noun.cell (Noun.atom 7) (Noun.cell b c) => by
    rw [nock_op7, nockW_op7, nock_eq_nockW s b]
    congr 1; funext s'; rw [nock_eq_nockW s' c]
  | s, Noun.cell (Noun.atom 8) (Noun.cell b c) => by
    rw [nock_op8, nockW_op8, nock_eq_nockW s b]
    congr 1; funext h; rw [nock_eq_nockW (C h s) c]
  | s, Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom ax) c) => by
    rw [nock_op9, nockW_op9, nock_eq_nockW s c]
  | s, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom ax) c) d) => by
    rw [nock_op10, nockW_op10, nock_eq_nockW s c, nock_eq_nockW s d]
  | s, Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) c) d) => by
    rw [nock_op11_cell, nockW_op11_cell, nock_eq_nockW s c, nock_eq_nockW s d]
  | s, Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.cell x y) c) d) => by
    rw [nock_op11_ctag, nockW_op11_ctag]
  | s, Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag) c) => by
    rw [nock_op11_atom, nockW_op11_atom, nock_eq_nockW s c]
  | s, Noun.cell (Noun.atom 0) (Noun.cell _ _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 2) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 5) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 6) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 6) (Noun.cell _ (Noun.atom _)) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 7) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 8) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 9) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 9) (Noun.cell (Noun.cell _ _) _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 10) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 10) (Noun.cell (Noun.atom _) _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.cell _ _) _) _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom 11) (Noun.atom _) => by rw [nock.eq_def, nockW.eq_def]; rfl
  | s, Noun.cell (Noun.atom (n + 12)) _ => by rw [nock.eq_def, nockW.eq_def]; rfl
termination_by _ f => sizeOf f

theorem nockW_mono {c1 c2 : Noun → Noun → Option Noun} (h : ∀ s f, Below? (c1 s f) (c2 s f)) :
    ∀ (s f : Noun), Below? (nockW c1 s f) (nockW c2 s f)
  | s, Noun.atom a => fun x h => by rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.cell b c) d => by
    rw [nockW_cell, nockW_cell]
    exact Below?.bind (nockW_mono h s _) fun _ => Below?.bind (nockW_mono h s d) fun _ => Below?.refl _
  | _, Noun.cell (Noun.atom 0) (Noun.atom ax) => by rw [nockW_op0, nockW_op0]; exact Below?.refl _
  | _, Noun.cell (Noun.atom 0) (Noun.cell _ _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | _, Noun.cell (Noun.atom 1) _ => by rw [nockW_op1, nockW_op1]; exact Below?.refl _
  | s, Noun.cell (Noun.atom 2) (Noun.cell b c) => by
    rw [nockW_op2, nockW_op2]
    exact Below?.bind (nockW_mono h s b) fun _ => Below?.bind (nockW_mono h s c) fun _ => h _ _
  | s, Noun.cell (Noun.atom 3) b => by
    rw [nockW_op3, nockW_op3]; exact Below?.bind (nockW_mono h s b) fun _ => Below?.refl _
  | s, Noun.cell (Noun.atom 4) b => by
    rw [nockW_op4, nockW_op4]; exact Below?.bind (nockW_mono h s b) fun _ => Below?.refl _
  | s, Noun.cell (Noun.atom 5) (Noun.cell b c) => by
    rw [nockW_op5, nockW_op5]
    exact Below?.bind (nockW_mono h s b) fun _ => Below?.bind (nockW_mono h s c) fun _ => Below?.refl _
  | s, Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) => by
    rw [nockW_op6, nockW_op6]
    refine Below?.bind (nockW_mono h s b) fun t => ?_
    match t with
    | Noun.atom 0 => exact nockW_mono h s c
    | Noun.atom 1 => exact nockW_mono h s d
    | Noun.atom (n + 2) => exact Below?.refl _
    | Noun.cell _ _ => exact Below?.refl _
  | s, Noun.cell (Noun.atom 7) (Noun.cell b c) => by
    rw [nockW_op7, nockW_op7]; exact Below?.bind (nockW_mono h s b) fun s' => nockW_mono h s' c
  | s, Noun.cell (Noun.atom 8) (Noun.cell b c) => by
    rw [nockW_op8, nockW_op8]; exact Below?.bind (nockW_mono h s b) fun x => nockW_mono h _ c
  | s, Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom ax) c) => by
    rw [nockW_op9, nockW_op9]
    exact Below?.bind (nockW_mono h s c) fun _ => Below?.bind (Below?.refl _) fun _ => h _ _
  | s, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom ax) c) d) => by
    rw [nockW_op10, nockW_op10]
    exact Below?.bind (nockW_mono h s c) fun _ => Below?.bind (nockW_mono h s d) fun _ => Below?.refl _
  | s, Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) c) d) => by
    rw [nockW_op11_cell, nockW_op11_cell]
    exact Below?.bind (nockW_mono h s c) fun _ => nockW_mono h s d
  | s, Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.cell x y) c) d) => by
    rw [nockW_op11_ctag, nockW_op11_ctag]; exact Below?.refl _
  | s, Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag) c) => by
    rw [nockW_op11_atom, nockW_op11_atom]; exact nockW_mono h s c
  | s, Noun.cell (Noun.atom 2) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 5) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 6) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 6) (Noun.cell _ (Noun.atom _)) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 7) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 8) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 9) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 9) (Noun.cell (Noun.cell _ _) _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 10) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 10) (Noun.cell (Noun.atom _) _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.cell _ _) _) _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom 11) (Noun.atom _) => fun x h => by
    rw [nockW.eq_def] at h; simp at h
  | s, Noun.cell (Noun.atom (n + 12)) _ => fun x h => by
    rw [nockW.eq_def] at h; simp at h
termination_by _ f => sizeOf f

/-! ## Calls at most `k` deep -/

/-- Nock whose calls are at most `k` deep. -/
def iterN : Nat → Noun → Noun → Option Noun
  | 0 => fun _ _ => none
  | k + 1 => nockW (iterN k)

theorem iterN_succ (k : Nat) : iterN (k + 1) = nockW (iterN k) := rfl

theorem iterN_mono_succ : ∀ (k : Nat) (s f : Noun), Below? (iterN k s f) (iterN (k + 1) s f)
  | 0, _, _ => fun _ h => by simp [iterN] at h
  | k + 1, s, f => nockW_mono (fun s f => iterN_mono_succ k s f) s f

theorem iterN_mono {k k' : Nat} (hk : k ≤ k') (s f : Noun) : Below? (iterN k s f) (iterN k' s f) := by
  induction hk with
  | refl => exact Below?.refl _
  | step _ ih => exact fun r h => iterN_mono_succ _ s f r (ih r h)

theorem iterN_sound : ∀ (k : Nat) (s f : Noun), Below? (iterN k s f) (nock s f)
  | 0, _, _ => fun _ h => by simp [iterN] at h
  | k + 1, s, f => by
    rw [nock_eq_nockW]; exact nockW_mono (fun s f => iterN_sound k s f) s f

theorem iterN_complete {s f p : Noun} (h : nock s f = some p) : ∃ k, iterN k s f = some p := by
  have he := evalA_of_nock h
  clear h
  have L : ∀ {k k' : Nat}, k ≤ k' → ∀ {s f p}, iterN k s f = some p → iterN k' s f = some p :=
    fun {_ _} hk {s f p} h => iterN_mono hk s f p h
  induction he with
  | @cell s b c d l r _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_cell, e1, e2, Option.bind_some]
  | @op0 s ax out hs => exact ⟨1, by rw [iterN_succ, nockW_op0]; exact slot?_complete hs⟩
  | op1 => exact ⟨1, by rw [iterN_succ, nockW_op1]⟩
  | @op2 s b c s' f' out _ _ _ ih1 ih2 ih3 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    obtain ⟨k3, h3⟩ := ih3
    refine ⟨max k1 (max k2 k3) + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 (max k2 k3) + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 (max k2 k3) + 1 by omega) h2
    have e3 := L (show k3 ≤ max k1 (max k2 k3) by omega) h3
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op2, e1, e2, e3, Option.bind_some]
  | @op3 s b x _ ih =>
    obtain ⟨k1, h1⟩ := ih
    refine ⟨k1 + 1, ?_⟩
    have e1 := L (show k1 ≤ k1 + 1 by omega) h1
    rw [iterN_succ] at e1 ⊢
    simp only [nockW_op3, e1, Option.bind_some]
  | @op4 s b a _ ih =>
    obtain ⟨k1, h1⟩ := ih
    refine ⟨k1 + 1, ?_⟩
    have e1 := L (show k1 ≤ k1 + 1 by omega) h1
    rw [iterN_succ] at e1 ⊢
    simp only [nockW_op4, e1, Option.bind_some, lus_atom]
  | @op5 s b c x y _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op5, e1, e2, Option.bind_some]
  | @op6_zero s b c d out _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op6, e1, e2, Option.bind_some, pick_zero]
  | @op6_one s b c d out _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op6, e1, e2, Option.bind_some, pick_one]
  | @op7 s b c s' out _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op7, e1, e2, Option.bind_some]
  | @op8 s b c x out _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op8, e1, e2, Option.bind_some]
  | @op9 s ax c core out _ _ ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    cases k2 with
    | zero => simp [iterN] at h2
    | succ k2 =>
      rw [iterN_succ, nockW_op2, nockW_op0, nockW_op0, slot?_one] at h2
      simp only [Option.bind_some] at h2
      cases harm : slot? ax core with
      | none => rw [harm] at h2; simp at h2
      | some arm =>
        rw [harm, Option.bind_some] at h2
        refine ⟨max k1 k2 + 1, ?_⟩
        have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
        have e2 := L (show k2 ≤ max k1 k2 by omega) h2
        rw [iterN_succ] at e1 ⊢
        simp only [nockW_op9, e1, harm, e2, Option.bind_some]
  | @op10 s ax c d r b out _ _ he ih1 ih2 =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op10, e1, e2, Option.bind_some, edit?_complete he]
  | @op11_cell s tag c d hint pr out _ _ h3 ih1 ih2 _ =>
    obtain ⟨k1, h1⟩ := ih1
    obtain ⟨k2, h2⟩ := ih2
    have h3' := nock_of_evalA h3
    rw [nock_op0, slot?_step 3 (by omega)] at h3'
    simp only [Nat.reduceDiv, slot?_one, Option.bind_some, child, Nat.reduceMod, decide_true,
      if_true, Option.some.injEq] at h3'
    subst h3'
    refine ⟨max k1 k2 + 1, ?_⟩
    have e1 := L (show k1 ≤ max k1 k2 + 1 by omega) h1
    have e2 := L (show k2 ≤ max k1 k2 + 1 by omega) h2
    rw [iterN_succ] at e1 e2 ⊢
    simp only [nockW_op11_cell, e1, e2, Option.bind_some]
  | @op11_atom s tag c out _ ih =>
    obtain ⟨k1, h1⟩ := ih
    refine ⟨k1 + 1, ?_⟩
    have e1 := L (show k1 ≤ k1 + 1 by omega) h1
    rw [iterN_succ] at e1 ⊢
    simp only [nockW_op11_atom, e1]

end Nock
end Formalization

end
