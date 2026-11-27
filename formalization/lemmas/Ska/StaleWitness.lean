import core.Nock
import lemmas.Spec

/-!
# A member left stale by the first pass at a root (fixed)

**Fixed in the Hoon** (commit `fefb95d`): `+analyze` now runs
`=.  st  (cull id st)` once before the pass loop, so the members that the
root does not reach are dropped before the first pass, as they are after
every pass.  `Ana.analyzeStep` makes that cull (`Ana.cullPass`).  On the
fixed compiler the poke below leaves no stale `m2`, and the compiled `fR`
crashes on `x` as `+mink` does.  The formulas are kept as a regression test.
What follows describes the Hoon before the fix.

The pass loop of `+analyze` sweeps, in each pass, the members of the
component that the root reaches over the current callees (`+sweep`), and
`+cull` dropped the members it does not reach only after the member loop.  So
the first pass at a root does not run a member that was left on the stack by
a nested pass loop which exited early (`low < index`) and that the root does
not reach when the pass starts.  If a run in that pass reaches the member
again (a call that is an exact identity in the graph and in `order`) and the
pass is stable, `+cull` keeps the member and `+pop` finalizes it with its
entry from before the change of its callees: `+dirty` would have rerun it,
but it was never in the list of the pass.

The formulas below show it.  The subject is `[[0 [fR [fW fm2]]] [d6 d7]]`,
so `fR`, `fW`, `fm2` are at the axes `10`, `22`, `23`; the recursive calls
set `d6` or `d7` to `0`, which on the subject of the poke (`d6 = d7 = 0`)
keeps the subject sock.  The poke is `[&+[[0 [fR [fW fm2]]] [0 0]] fid]`.
With `S'` the subject sock after `[10 [6 1 0] 0 1]`, `R`, `W`, `m2` are the
identities `[S' fR]`, `[S' fW]`, `[S' fm2]`.

1. `id` runs and calls `R`.  `R`'s first run calls `W` (whose first run reads
   `R`'s empty entry and returns `fm2`), then `[S' fm2]`, that is `m2` (whose
   first run reads `R`'s empty entry and returns `fW`); its self-call reads
   its own empty entry, so the rest of `SIDE` is void.  `R` returns `fW` and is
   the root of `{R W m2}`.
2. The first pass at `R`: `W` reruns and now returns an unknown formula; `m2`
   reruns, reads `R`'s product `fW`, and still returns `fW`; `R` reruns, its
   call through `W`'s product is now indirect (so it no longer calls `m2`),
   and `SIDE` calls `id`, below `R`: the member loop exits, nothing is culled,
   `R`'s product is now unknown, and `m2` is dirty.
3. `id`'s run ends; it returns `fm2`.  The first pass at `id` sweeps
   `[W R id]`: `m2` is on the stack but `id` does not reach it.  `R` reruns;
   `SIDE` now gets `fm2` from `id` and calls `m2` (exact, in `order`), reads
   its stale product `fW`, and makes the call `[2 [0 15] [0 2]]` a direct call
   to `W`.  `R`'s entry does not change, `id` is not dirty, no function is
   new: the pass is stable, `+cull` keeps `m2`, `+pop` finalizes everything.
4. `m2` keeps the product `fW`, but on a subject with `d6 ≠ 0`, `d7 ≠ 0` it
   returns `[fW 42]` (it calls `R` with `d7 = 0`, which takes `SIDE`).  On
   `x = [[0 [fR [fW fm2]]] [1 1]]`, which fits `R`'s code requirement (it
   knows only `fR`, `fW`, `fm2`), `*[x fR]` crashes at `[2 [0 15] [0 2]]`
   (the formula `[fW 42]` has the atom `42` where a formula must be), while
   the nomm of `R` jumps to `W`'s code and returns `[fW 42]`.

This was found on the model of `Analysis.lean`, evaluated with association
lists for the treaps: the final graph has `m2` with product `&+fW` (map `22`),
`R` and `W` with an unknown product, `9` runs, `2` passes, nothing culled;
`minkF` of `fR` on `x` is a crash, `nommF` of `R`'s nomm with `codeOf` of the
final entries is `[fW 42]`.  A second poke `[&+x fR]` hits `R` in the memo.
-/

namespace Formalization
namespace SkaModel
namespace StaleWitness

open Nock

def q (k : Noun) : Noun := C (A 1) k
def ax (n : Nat) : Noun := C (A 0) (A n)
def call (s f : Noun) : Noun := C (A 2) (C s f)
def seven (a b : Noun) : Noun := C (A 7) (C a b)
def eight (a b : Noun) : Noun := C (A 8) (C a b)
def six (c a b : Noun) : Noun := C (A 6) (C c (C a b))
def edit (x : Nat) (v t : Noun) : Noun := C (A 10) (C (C (A x) v) t)

/-- `[10 [6 1 0] 0 1]` and `[10 [7 1 0] 0 1]`. -/
def e6 : Noun := edit 6 (q (A 0)) (ax 1)
def e7 : Noun := edit 7 (q (A 0)) (ax 1)

/-- `[6 [0 6] [0 23] 2 [10 [6 1 0] 0 1] 0 10]` -/
def fW : Noun := six (ax 6) (ax 23) (call e6 (ax 10))
/-- `[6 [0 7] [0 22] 2 [10 [7 1 0] 0 1] 0 10]` -/
def fm2 : Noun := six (ax 7) (ax 22) (call e7 (ax 10))
/-- `[8 [2 [10 [6 1 0] 0 1] 0 10] 1 fm2]` -/
def fid : Noun := eight (call e6 (ax 10)) (q fm2)
/-- `[2 [0 1] 2 [0 1] 0 22]` -/
def s1 : Noun := call (ax 1) (call (ax 1) (ax 22))
/-- `[8 [2 [10 [6 1 0] 0 1] 0 10] 8 [2 [0 3] 1 fid] 8 [2 [0 7] 0 2] 7 [2 [0 15] 0 2] [0 1] 1 42]` -/
def side : Noun :=
  eight (call e6 (ax 10))
    (eight (call (ax 3) (q fid))
      (eight (call (ax 7) (ax 2))
        (seven (call (ax 15) (ax 2)) (C (ax 1) (q (A 42))))))
/-- `[6 [0 6] s1 side]` -/
def fR : Noun := six (ax 6) s1 side

/-- The subject `[[0 [fR [fW fm2]]] [d6 d7]]`. -/
def subj (d6 d7 : Nat) : Noun := C (C (A 0) (C fR (C fW fm2))) (C (A d6) (A d7))

/-- The poke's subject and the subject of the disagreement. -/
def pokeSubject : Noun := subj 0 0
def badSubject : Noun := subj 1 1

end StaleWitness
end SkaModel
end Formalization
