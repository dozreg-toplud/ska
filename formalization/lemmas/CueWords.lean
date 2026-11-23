import lemmas.Fuel

/-!
`cue` decodes a jammed noun.  The jam is given as its little-endian 32-bit
words, so a pill file of `4 * n` bytes is a list of `n` words.

The function is written for the kernel: it is structurally recursive on fuel,
it reads the words in order, and it forces every intermediate value at the
step that produces it (a lazy evaluator would otherwise pile up unevaluated
updates of the back-reference table).

Encoding, with the low bit first:

* `0` then a length-prefixed atom:          an atom
* `1 0` then two nouns:                     a cell
* `1 1` then a length-prefixed atom `p`:    the noun that started at bit `p`

A length-prefixed atom `a` of `b` bits is `c` zeros, a one, the low `c - 1`
bits of `b`, and the `b` bits of `a`, where `c` is the bit length of `b`.
Zero is the single bit `1`.
-/

namespace Formalization
namespace Nock

def wordBits : Nat := 32

/-- The unread part of the jam: `left` unread low bits in `cur`, then `more`. -/
structure Stream where
  cur : Nat
  left : Nat
  more : List Nat

def Stream.ofWords (words : List Nat) : Stream :=
  ⟨0, 0, words⟩

/-- Read one bit. -/
def Stream.bit : Stream → Option (Nat × Stream)
  | ⟨cur, left + 1, more⟩ => some (cur &&& 1, ⟨cur >>> 1, left, more⟩)
  | ⟨_, 0, word :: more⟩ => some (word &&& 1, ⟨word >>> 1, wordBits - 1, more⟩)
  | ⟨_, 0, []⟩ => none

/-- Read `n` bits as a number, low bit first. -/
def Stream.takeAux : (more : List Nat) → (n cur left : Nat) → Option (Nat × Stream)
  | more, n, cur, left =>
    match Nat.ble n left with
    | true => some (cur &&& (2 ^ n - 1), ⟨cur >>> n, left - n, more⟩)
    | false =>
      match more with
      | [] => none
      | word :: more' =>
        match Stream.takeAux more' (n - left) word wordBits with
        | none => none
        | some (high, rest) => some (cur ||| (high <<< left), rest)

def Stream.take (n : Nat) (s : Stream) : Option (Nat × Stream) :=
  Stream.takeAux s.more n s.cur s.left

/-- Count zero bits up to and including the first one bit. -/
def Stream.zeros : (fuel : Nat) → Stream → Option (Nat × Stream)
  | 0, _ => none
  | fuel + 1, s =>
    match s.bit with
    | none => none
    | some (0, s') =>
      match Stream.zeros fuel s' with
      | none => none
      | some (count, s'') => some (count + 1, s'')
    | some (_, s') => some (0, s')

/-- Read a length-prefixed atom: the atom and the number of bits it took. -/
def Stream.rub (s : Stream) : Option (Nat × Nat × Stream) :=
  match Stream.zeros 64 s with
  | none => none
  | some (0, s') => some (0, 1, s')
  | some (count + 1, s') =>
    match s'.take count with
    | none => none
    | some (low, s'') =>
      match s''.take (low ||| (1 <<< count)) with
      | none => none
      | some (atom, s''') =>
        some (atom, (count + 1) + (count + 1) + (low ||| (1 <<< count)), s''')

/-- Nouns by the bit position at which their encoding starts: a binary trie
on the bits of the position, low bit first. -/
inductive Refs where
  | leaf : Refs
  | node : Option Noun → Refs → Refs → Refs

/-- Evaluate a table before passing it on. -/
def Refs.force {α : Type} (refs : Refs) (next : Refs → α) : α :=
  match refs with
  | Refs.leaf => next Refs.leaf
  | Refs.node noun zero one => next (Refs.node noun zero one)

def Refs.get : Refs → Nat → Option Noun
  | Refs.leaf, _ => none
  | Refs.node noun zero one, key =>
    match key with
    | 0 => noun
    | _ =>
      match key &&& 1 with
      | 0 => zero.get (key >>> 1)
      | _ => one.get (key >>> 1)

/-- Positions are below `2 ^ fuel`. -/
def Refs.insert : (fuel : Nat) → Refs → Nat → Noun → Refs
  | 0, refs, _, _ => refs
  | fuel + 1, Refs.leaf, key, noun =>
    match key with
    | 0 => Refs.node (some noun) Refs.leaf Refs.leaf
    | _ =>
      match key &&& 1 with
      | 0 => (Refs.insert fuel Refs.leaf (key >>> 1) noun).force fun zero =>
          Refs.node none zero Refs.leaf
      | _ => (Refs.insert fuel Refs.leaf (key >>> 1) noun).force fun one =>
          Refs.node none Refs.leaf one
  | fuel + 1, Refs.node old zero one, key, noun =>
    match key with
    | 0 => Refs.node (some noun) zero one
    | _ =>
      match key &&& 1 with
      | 0 => (Refs.insert fuel zero (key >>> 1) noun).force fun zero' =>
          Refs.node old zero' one
      | _ => (Refs.insert fuel one (key >>> 1) noun).force fun one' =>
          Refs.node old zero one'

/-- Decode one noun that starts at bit `pos`: the noun, the position after
it, the rest of the stream and the table with the noun's parts added. -/
def cueAux : (fuel : Nat) → (pos : Nat) → Stream → Refs → Option (Noun × Nat × Stream × Refs)
  | 0, _, _, _ => none
  | fuel + 1, pos, s, refs =>
    match s.bit with
    | none => none
    | some (0, s') =>
      match s'.rub with
      | none => none
      | some (atom, used, s'') =>
        (refs.insert 64 pos (A atom)).force fun refs' =>
          some (A atom, pos + 1 + used, s'', refs')
    | some (_, s') =>
      match s'.bit with
      | none => none
      | some (0, s'') =>
        match cueAux fuel (pos + 2) s'' refs with
        | none => none
        | some (head, pos', s''', refs') =>
          match cueAux fuel pos' s''' refs' with
          | none => none
          | some (tail, pos'', s'''', refs'') =>
            (refs''.insert 64 pos (C head tail)).force fun refs''' =>
              some (C head tail, pos'', s'''', refs''')
      | some (_, s'') =>
        match s''.rub with
        | none => none
        | some (ref, used, s''') =>
          match refs.get ref with
          | none => none
          | some noun => some (noun, pos + 2 + used, s''', refs)

/-- The noun that a jam, given as 32-bit words, decodes to. -/
def cue (words : List Nat) : Option Noun :=
  match cueAux (wordBits * words.length + 1) 0 (Stream.ofWords words) Refs.leaf with
  | none => none
  | some (noun, _, _, _) => some noun

end Nock
end Formalization
