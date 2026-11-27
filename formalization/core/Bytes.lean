module

public meta import Lean

/-!
`bytes% { b₀, b₁, b₂, … }` is the natural number whose bytes, lowest first,
are `b₀`, `b₁`, `b₂`, …:

    b₀ + 256 * b₁ + 256 ^ 2 * b₂ + …

It is how `core/Pill.lean` writes the pill, so that the text between the
braces is the text between the braces of `steel.c`.

A list of this many numerals is more than Lean elaborates, and one literal
of this size is more than it prints, so the term that `bytes%` makes is
`glue` of the list of the 1024-byte pieces of the number, each piece a
literal.  The pieces are computed when the term is read.
-/

@[expose] public section

namespace Formalization

/-- The atom whose bytes, lowest first, are the chunks in order, each chunk
1024 bytes wide. -/
def glue : List Nat → Nat
  | [] => 0
  | chunk :: rest => chunk + 2 ^ 8192 * glue rest

/-- The number whose bytes, lowest first, are `bs[lo]`, …, `bs[hi - 1]`. -/
meta def atomOfBytes (bs : Array Nat) (lo hi : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [lo:hi] do
    n := n + 256 ^ (i - lo) * bs[i]!
  return n

open Lean Elab Term in
/-- `bytes% { b₀, b₁, … }`: the number whose bytes, lowest first, are `b₀`,
`b₁`, …, as `glue` of its 1024-byte pieces. -/
elab "bytes% " "{" bs:num,*,? "}" : term => do
  let mut vals : Array Nat := #[]
  for b in bs.getElems do
    unless b.getNat < 256 do throwErrorAt b "bytes%: not a byte"
    vals := vals.push b.getNat
  let mut chunks : Array Expr := #[]
  for i in [0:vals.size:1024] do
    chunks := chunks.push (mkNatLit (atomOfBytes vals i (min (i + 1024) vals.size)))
  return mkApp (mkConst ``glue) (← Meta.mkListLit (mkConst ``Nat) chunks.toList)

end Formalization
