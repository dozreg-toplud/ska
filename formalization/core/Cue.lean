module

public import core.Nock

/-!
`cue`: the noun that an atom decodes to.  It follows `+cue` and `+rub` of
hoon.hoon line by line, and it is written to be read, not to be run: the
table of the nouns decoded so far is a function.

The encoding, from the lowest bit:

* `0`, then a length-prefixed atom:        that atom
* `1 0`, then two nouns:                   the cell of them
* `1 1`, then a length-prefixed atom `q`:  the noun that started at bit `q`

A length-prefixed atom of `e` bits is `c` zeros, a one, the low `c - 1` bits
of `e` (its top bit is implied), and the `e` bits of the atom, where `c` is
the bit length of `e`.  The atom 0 is the single bit `1`.
-/

@[expose] public section

namespace Formalization
namespace Nock

/-- The `n` bits of `a` from bit `i` up, as a number: `(cut 0 [i n] a)`. -/
def bits (a i n : Nat) : Nat :=
  (a >>> i) % 2 ^ n

/-- How many zero bits `a` has from bit `i` up to its next one bit.  No bit
of `a` at or above `fuel` bits from `i` is looked at. -/
def zeros (a i : Nat) : (fuel : Nat) → Option Nat
  | 0 => none
  | fuel + 1 =>
    if bits a i 1 = 1 then some 0
    else (zeros a (i + 1) fuel).map (· + 1)

/-- `(rub i a)`: the length-prefixed atom at bit `i` of `a`, as the number
of bits it takes and the atom. -/
def rub (a i : Nat) : Option (Nat × Nat) :=
  -- `a` has no one bit at or above bit `a.log2 + 1`
  match zeros a i (a.log2 + 2) with
  | none => none
  | some 0 => some (1, 0)
  | some (c + 1) =>
    -- past the `c + 1` zeros and the one
    let d := i + (c + 1) + 1
    -- the length of the atom: a one above the `c` bits at `d`
    let e := 2 ^ c + bits a d c
    some ((c + 1) + (c + 1) + e, bits a (d + c) e)

/-- A table with one more entry. -/
def put (m : Nat → Option Noun) (key : Nat) (noun : Noun) : Nat → Option Noun :=
  fun k => if k = key then some noun else m k

/-- The noun of the jam `a` that starts at bit `b`, where `m` holds the nouns
decoded before it by the bits they start at: the number of bits it takes,
the noun, and `m` with the noun and its parts added.  `fuel` bounds the
depth of the noun. -/
def cueAt (a : Nat) : (fuel : Nat) → (b : Nat) → (m : Nat → Option Noun) →
    Option (Nat × Noun × (Nat → Option Noun))
  | 0, _, _ => none
  | fuel + 1, b, m =>
    if bits a b 1 = 0 then
      -- an atom
      match rub a (b + 1) with
      | none => none
      | some (p, q) => some (p + 1, A q, put m b (A q))
    else if bits a (b + 1) 1 = 0 then
      -- a cell: its head, then its tail
      match cueAt a fuel (b + 2) m with
      | none => none
      | some (pu, head, mu) =>
        match cueAt a fuel (b + 2 + pu) mu with
        | none => none
        | some (pv, tail, mv) =>
          some (2 + pu + pv, C head tail, put mv b (C head tail))
    else
      -- a reference to a noun decoded before
      match rub a (b + 2) with
      | none => none
      | some (p, q) =>
        match m q with
        | none => none
        | some noun => some (2 + p, noun, m)

/-- `(cue a)`.  A noun nested deeper than `a` has bits does not fit in `a`. -/
def cue (a : Nat) : Option Noun :=
  match cueAt a (a.log2 + 2) 0 (fun _ => none) with
  | none => none
  | some (_, noun, _) => some noun

end Nock
end Formalization
