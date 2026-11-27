import lemmas.Ska.FolLoop

/-!
# `inlinedM`: a model of `+inlined`

`+inlined` (`desk/lib/nock-compilation.hoon`, lines 3304 to 3394) returns,
for a bell `b`, the nomm of `(~(got by code.long-ska) b)` copied case by case
(every constructor rebuilt from its copied children), except at a direct call
`[%2 p q [~ c k]]`: when the memo key `k` is `~`, `+safe-fol-fol` holds of
the call's ORIGINAL formula part `q.nomm`, `c` is not hot (its ring has a
driver in `jets-hot`), `+scc-of c` is the singleton `{c}` and `c` is not in
its own `calls`, the callee's own `+inlined` nomm `m` is computed (the
recursion `inlined-loop(b c)`), and the call becomes `[%7 p' m]` unless
`(nomm-size m)` exceeds `inline-max` (48).  `inline-off` is the constant `|`
(`inline_off_at`, `Compiler/CompInlined.lean`), so this model has no flag
for it.

The cache `inl.cache` is a memo of this function: a hit returns the stored
nomm (line 3313) and a miss stores the result (line 3319).  The model has no
cache: it is the function the cache must memoize (the pill half,
LEDGER 2.e, is `D.inl = inlinedM …` given that every entry of `inl.cache` is
`inlinedM` of its bell).  `sccs.cache`, which `+scc-of` reads and extends, is
read only through the test "the SCC of `c` is `{c}`", the parameter
`single`.

FUEL.  `inlinedM` recurses through callees.  A callee `c` it enters is
alone in its SCC of `calls` and does not call itself, so (when `calls`
contains every direct callee of a nomm of the table) the chain of entered
bells goes strictly down the condensation of `calls`: a fuel of one more
than the number of bells of `code` is enough.  The model returns `none` when
the fuel runs out, so every theorem about a result needs no measure.

CHECKED against the real compiler: `Glue/InlineCheck.lean` (`tools/hoon/inldump.hoon`,
20 pokes, the 29 entries of `inl.cache`, no difference).
-/

namespace Formalization
namespace SkaModel
namespace Glue

open Nock

/-- `+inline-max`. -/
def inlineMax : Nat := 48

/-- `+nomm-size` from the count `n` (the Hoon starts at `0`): it stops
counting once the count exceeds `inline-max`; each node adds one, then the
children are counted left to right. -/
def nommSize : Nat → Nomm → Nat
  | n, Nomm.cons p q => if inlineMax < n then n else nommSize (nommSize (n + 1) p) q
  | n, Nomm.n0 _ => if inlineMax < n then n else n + 1
  | n, Nomm.n1 _ => if inlineMax < n then n else n + 1
  | n, Nomm.n2 p q _ => if inlineMax < n then n else nommSize (nommSize (n + 1) p) q
  | n, Nomm.n3 p => if inlineMax < n then n else nommSize (n + 1) p
  | n, Nomm.n4 p => if inlineMax < n then n else nommSize (n + 1) p
  | n, Nomm.n5 p q => if inlineMax < n then n else nommSize (nommSize (n + 1) p) q
  | n, Nomm.n6 p q r => if inlineMax < n then n else nommSize (nommSize (nommSize (n + 1) p) q) r
  | n, Nomm.n7 p q => if inlineMax < n then n else nommSize (nommSize (n + 1) p) q
  | n, Nomm.n10 _ v q => if inlineMax < n then n else nommSize (nommSize (n + 1) v) q
  | n, Nomm.n11s _ q _ => if inlineMax < n then n else nommSize (n + 1) q
  | n, Nomm.n11d _ h q _ => if inlineMax < n then n else nommSize (nommSize (n + 1) h) q
  | n, Nomm.n12 p q => if inlineMax < n then n else nommSize (nommSize (n + 1) p) q
  | n, Nomm.mean p _ q _ _ => if inlineMax < n then n else nommSize (nommSize (n + 1) p) q

/-- The test of line 3339 to 3343 for the callee `c` with memo key `k` and
the original formula part `q`. -/
def inlOK (calls : Bell → Bell → Bool) (hot single : Bell → Bool) (c : Bell) (k : Option Noun)
    (q : Nomm) : Bool :=
  k.isNone && safeFolFol q && !hot c && single c && !calls c c

/-- The trap `|-` of `+inlined` over a nomm (lines 3323 to 3394), with `go`
the recursion `inlined-loop` at a callee. -/
def inlWalk (calls : Bell → Bell → Bool) (hot single : Bell → Bool) (go : Bell → Option Nomm) :
    Nomm → Option Nomm
  | Nomm.cons p q =>
      (inlWalk calls hot single go p).bind fun a =>
        (inlWalk calls hot single go q).bind fun d => some (Nomm.cons a d)
  | Nomm.n0 a => some (Nomm.n0 a)
  | Nomm.n1 k => some (Nomm.n1 k)
  | Nomm.n2 p q none =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.n2 p' q' none)
  | Nomm.n2 p q (some (c, k)) =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' =>
          if inlOK calls hot single c k q then
            (go c).bind fun m =>
              some (if inlineMax < nommSize 0 m then Nomm.n2 p' q' (some (c, k)) else Nomm.n7 p' m)
          else some (Nomm.n2 p' q' (some (c, k)))
  | Nomm.n3 p => (inlWalk calls hot single go p).bind fun p' => some (Nomm.n3 p')
  | Nomm.n4 p => (inlWalk calls hot single go p).bind fun p' => some (Nomm.n4 p')
  | Nomm.n5 p q =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.n5 p' q')
  | Nomm.n6 p q r =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' =>
          (inlWalk calls hot single go r).bind fun r' => some (Nomm.n6 p' q' r')
  | Nomm.n7 p q =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.n7 p' q')
  | Nomm.n10 a v q =>
      (inlWalk calls hot single go v).bind fun v' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.n10 a v' q')
  | Nomm.n11s t q body => (inlWalk calls hot single go q).bind fun q' => some (Nomm.n11s t q' body)
  | Nomm.n11d t h q body =>
      (inlWalk calls hot single go h).bind fun h' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.n11d t h' q' body)
  | Nomm.n12 p q =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.n12 p' q')
  | Nomm.mean p b q body k =>
      (inlWalk calls hot single go p).bind fun p' =>
        (inlWalk calls hot single go q).bind fun q' => some (Nomm.mean p' b q' body k)

/-- **The model of `+inlined`**: `code` is the nomm of `code.long-ska`,
`calls c d` says `d ∈ calls.long-ska c`, `hot c` that `c`'s ring has a driver
in `jets-hot`, `single c` that `+scc-of c` is `{c}`.  `none` when the fuel
runs out or a bell entered is not in `code` (where the Hoon's `+got:by`
crashes). -/
def inlinedM (code : Bell → Option Nomm) (calls : Bell → Bell → Bool) (hot single : Bell → Bool) :
    Nat → Bell → Option Nomm
  | 0, _ => none
  | f + 1, b => (code b).bind (inlWalk calls hot single (inlinedM code calls hot single f))

end Glue
end SkaModel
end Formalization
