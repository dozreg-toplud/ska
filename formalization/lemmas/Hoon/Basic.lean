module

public import lemmas.Exec
/-!
What the proofs about the arms of `hoon.hoon` share: flags, lists as nouns,
and the way a theorem states what an arm reads from its context.

## Contexts

A gate of the library is the core `[battery sample context]`, where the
context is the core that the arm was pulled from (a layer of the library, or
a door).  A theorem about a gate quantifies over the context `c` and assumes
only what the gate's Nock reads from it.  For each arm `x` there is a
predicate `XIn c`: the arm `x` sits at its axis in `c` (the generated
`x.axis`), and `c` satisfies what the gate of `x` reads in turn.  A gate of
the library's second layer that calls into the first reads the first layer as
the tail of its context: `Below P c` says that `c` is a cell whose tail
satisfies `P`.

The predicates are `abbrev`s, so `simp only [nock_exec, hc]` with a hypothesis
`hc : XIn c` rewrites every `slot? x.axis c` that the execution reaches.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock

/-! ## Flags -/

/-- A Hoon flag: `&` is `0` and `|` is `1`. -/
def loob (b : Bool) : Noun := if b then A 0 else A 1

@[nock_exec] theorem loob_true : loob true = A 0 := rfl

@[nock_exec] theorem loob_false : loob false = A 1 := rfl

@[nock_exec] theorem pick_loob (b : Bool) (yes no : Noun) :
    pick (loob b) yes no = some (if b then yes else no) := by
  cases b <;> rfl

/-! ## Contexts -/

/-- `c` is a core whose context (its tail) satisfies `P`. -/
def Below (P : Noun → Prop) : Noun → Prop
  | Noun.cell _ t => P t
  | Noun.atom _ => False

theorem Below.cell {P : Noun → Prop} {h t : Noun} (hp : P t) : Below P (C h t) := hp

/-- A proof about a context `c` with `Below P c` may take `c` apart. -/
theorem Below.elim {P : Noun → Prop} {c : Noun} (h : Below P c) :
    ∃ bat t, c = C bat t ∧ P t := by
  cases c with
  | atom _ => exact absurd h id
  | cell bat t => exact ⟨bat, t, rfl, h⟩

/-- A unit: `~` or `[~ u]`. -/
def unitN : Option Noun → Noun
  | none => A 0
  | some u => C (A 0) u

/-! ## Lists -/

/-- `l` followed by the noun `t`: `[l_0 l_1 ... t]`. -/
def appendN : List Noun → Noun → Noun
  | [], t => t
  | x :: xs, t => C x (appendN xs t)

/-- A Hoon list: `~` or `[i t]`. -/
def listN (l : List Noun) : Noun := appendN l (A 0)

@[simp] theorem appendN_nil (t : Noun) : appendN [] t = t := rfl

@[simp] theorem appendN_cons (x : Noun) (xs : List Noun) (t : Noun) :
    appendN (x :: xs) t = C x (appendN xs t) := rfl

@[simp] theorem listN_nil : listN [] = A 0 := rfl

@[simp] theorem listN_cons (x : Noun) (xs : List Noun) : listN (x :: xs) = C x (listN xs) := rfl

theorem appendN_listN (l l' : List Noun) : appendN l (listN l') = listN (l ++ l') := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- An atom is the noun of a list only for the empty list. -/
theorem listN_eq_atom {l : List Noun} {n : Nat} (h : listN l = A n) : l = [] ∧ n = 0 := by
  cases l with
  | nil => simp at h; exact ⟨rfl, h.symm⟩
  | cons x xs => simp at h

end Hoon
end Formalization

end
