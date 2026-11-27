import lemmas.Glue.Inline
import lemmas.Glue.InlineData

/-!
# `inlinedM` against the real `+inlined`

`tools/hoon/inldump.hoon` runs 20 pokes in a row on one state (16 with an
unknown subject through the `%full` branch by hand, 4 real `%full` pokes) and
dumps `inl.cache` and the code table (`tools/hoon/inlcheck.py --lean` writes
`InlineData.lean`).  The cases: a small callee (inlined), one over
`inline-max` (kept), a chain of two inlinable callees, a callee whose own
inlining takes it over `inline-max` (inlined into its caller's entry, kept at
the root), a recursive callee (kept), a callee in an SCC of two (kept), a
formula part that is not `+safe-fol-fol`, a memoized call, a `%9` arm call,
calls under `%6` and in a cons, the same callee twice, a `%spot` hint around
the formula part, a callee calling a recursive one, a callee calling into an
SCC of two, and four real `%full` pokes.  `jets-hot` is `~`, so `hot` is
`false` everywhere.

Every one of the 29 entries of `inl.cache` is `inlinedM` of its bell on the
final table (old entries were computed on smaller tables, which the model
does not see: the table only grows).
-/

namespace Formalization
namespace SkaModel
namespace Glue

open Nock

/-- The noun of a nomm, decoded (as `Comp.nommOf` of `Ska/CompHintCheck.lean`). -/
def nommOfG : Nat → Noun → Option Nomm
  | 0, _ => Option.none
  | n + 1, Noun.cell (Noun.cell a b) q => do
      pure (Nomm.cons (← nommOfG n (Noun.cell a b)) (← nommOfG n q))
  | n + 1, Noun.cell (Noun.atom t) r =>
      match t, r with
      | 0, Noun.atom p => some (Nomm.n0 p)
      | 1, k => some (Nomm.n1 k)
      | 2, Noun.cell p (Noun.cell q info) => do
          let p ← nommOfG n p
          let q ← nommOfG n q
          let info ← (match info with
            | Noun.atom 0 => some Option.none
            | Noun.cell (Noun.atom 0) (Noun.cell b k) => do
                let b ← Bell.ofNoun? b
                let k ← (match k with
                  | Noun.atom 0 => some Option.none
                  | Noun.cell (Noun.atom 0) v => some (some v)
                  | _ => Option.none)
                some (some (b, k))
            | _ => Option.none)
          pure (Nomm.n2 p q info)
      | 3, p => do pure (Nomm.n3 (← nommOfG n p))
      | 4, p => do pure (Nomm.n4 (← nommOfG n p))
      | 5, Noun.cell p q => do pure (Nomm.n5 (← nommOfG n p) (← nommOfG n q))
      | 6, Noun.cell p (Noun.cell q r) => do
          pure (Nomm.n6 (← nommOfG n p) (← nommOfG n q) (← nommOfG n r))
      | 7, Noun.cell p q => do pure (Nomm.n7 (← nommOfG n p) (← nommOfG n q))
      | 10, Noun.cell (Noun.cell (Noun.atom a) v) q => do pure (Nomm.n10 a (← nommOfG n v) (← nommOfG n q))
      | 11, Noun.cell (Noun.atom tag) (Noun.cell q body) => do pure (Nomm.n11s tag (← nommOfG n q) body)
      | 11, Noun.cell (Noun.cell (Noun.atom tag) h) (Noun.cell q body) => do
          pure (Nomm.n11d tag (← nommOfG n h) (← nommOfG n q) body)
      | 12, Noun.cell p q => do pure (Nomm.n12 (← nommOfG n p) (← nommOfG n q))
      | t, Noun.cell p (Noun.cell b (Noun.cell q (Noun.cell body k))) =>
          if t = Tag.mean then do
            let p ← nommOfG n p
            let b ← Bell.ofNoun? b
            let q ← nommOfG n q
            let k ← (match k with
              | Noun.atom 0 => some Option.none
              | Noun.cell (Noun.atom 0) v => some (some v)
              | _ => Option.none)
            pure (Nomm.mean p b q body k)
          else Option.none
      | _, _ => Option.none
  | _ + 1, Noun.atom _ => Option.none

/-- The code table of the dump: bell, nomm, single, self. -/
def codL : List (Bell × Nomm × Bool × Bool) :=
  InlineData.cod.filterMap fun e => do
    let b ← Bell.ofNoun? e.1
    let n ← nommOfG 100000 e.2.1
    pure (b, n, e.2.2.1, e.2.2.2)

def codeD (b : Bell) : Option Nomm := (codL.find? fun e => decide (e.1 = b)).map (·.2.1)
def singleD (b : Bell) : Bool := ((codL.find? fun e => decide (e.1 = b)).map (·.2.2.1)).getD false
def callsD (c d : Bell) : Bool := decide (c = d) && ((codL.find? fun e => decide (e.1 = c)).map (·.2.2.2)).getD false
def hotD (_ : Bell) : Bool := false

/-- The entries of `inl.cache` where the model differs (by index). -/
def inlFailing : List Nat :=
  (List.range InlineData.inl.length).filter fun i =>
    match InlineData.inl[i]? with
    | some (bN, nN) =>
        !(((Bell.ofNoun? bN).bind (inlinedM codeD callsD hotD singleD 40)).map Nomm.toNoun == some nN)
    | none => true

/-- How many entries differ from the code's own nomm (calls were inlined). -/
def inlChanged : Nat :=
  (InlineData.inl.filter fun e =>
    match Bell.ofNoun? e.1 with
    | some b => !((codeD b).map Nomm.toNoun == some e.2)
    | none => false).length

#guard InlineData.inl.length == 29
#guard codL.length == 29
#guard inlFailing == []
#guard inlChanged == 11

end Glue
end SkaModel
end Formalization
