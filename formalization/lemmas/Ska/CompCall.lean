import lemmas.Ska.CompLazyRun
import lemmas.Ska.FolLoop
import lemmas.Ska.Contract
import lemmas.Ska.CompUnproxy

/-!
# Calls in `+comp`: the case `%2` of `+run`

README Gaps 12.9 (eleventh session).  The design of the model of calls, the
first definitions, their check against the raw blocks of the real compiler,
and the run relation a call must meet.  Nothing here changes `Gen`, `runL`
or the arms of `CompModel.lean`, `CompLazyArms.lean`, `CompLazyRun.lean`.

## The Hoon (`desk/lib/nock-compilation.hoon`, 2026-11-24)

`+run` of `+comp` (line 3836) is `|=  [mono=? =nomm =goal region sup]`.  `mono`
is `&` only in `+compile-unary` (line 3414), the version of a function of its
whole subject; the n-ary versions (`+compile-scc-in`, lines 3505, 3525) run
with `mono` `|` on the nomm of `+inlined` (line 3298), which replaces a direct
call by `[%7 p callee-nomm]` when the formula-formula is `+safe-fol-fol`, the
callee has no memo key, no hot jet, is alone in its SCC, does not call itself,
and its inlined nomm has at most `inline-max` (48) nodes (lines 3327 to 3340).
`sup` is the head of the composition the nomm is the tail of, for `+made`.

The case `[%2 *]` (lines 3900 to 4051):

1. *Indirect call* (`info` is `~`, lines 3901 to 3923).  `+simple-next` of the
   goal; `+kerf` (line 5038): a block `%hop then` and `+kern` of the goal's
   lazy need from one fresh register `pro` (the product); two fresh registers
   `r-sub`, `r-fol`; a block `[%nok r-sub r-fol pro]` ending in `%hop out`;
   then `q` (the formula) for `%next` of `this r-fol` into that block,
   `+past` over `p`, `p` (the subject) for `%next` of `this r-sub`, and
   `+copy`.  Never a tail call.
2. *Direct call, dropped* (lines 3924 to 3935).  When the callee's code entry
   is `pure` (no crash, no hint but `%fast`, `%memo` and the safe ones,
   `+eval-finalized`, line 1959; a member of a recursive SCC starts and stays
   impure, line 1904) and the goal is `%next` of a need that asks nothing
   (`+none-equivalent`), no call: `q` (unless `+safe-fol-fol`) and `p` run for
   needs that ask nothing.
3. *Direct call* (lines 3936 to 4051).  `info` is `[b-callee key]`.
   `rin` is the callee's ring in `call.cole` (a jet).  `b-ned`, the callee's
   need (`need-ordered`): `this` for a persistent memo key (`[~ ^]`), else
   `+callee-need` (line 4593): a hot jet's need; for a callee outside the
   SCC, `+callee-compiled` (from `nary.cache`, or the callee's SCC compiled
   now with `+compile-scc-in`, which extends `cache`); for a member of the
   SCC, its shape in `map-local` or its `top` (what it may read).
   `sub-ned` is `b-ned` with fresh registers (`+need-ord-alloc-regs`, line
   6766, preorder, the whole of a `%both` first), `sub-v` its leaves
   (`+flatten-need`).  `b-sur`, what the callee reads first thing: `[%none ~]`
   for a hot jet, else `+callee-sure` (line 4588, `sure.cache`).
   `sof` (lines 3967 to 3974): no memo key, `+sound` of `(made p sup)` against
   `b-ned` fails (`+made`, line 5181: `[0 1]` stands for `sup`), and the
   need is soft (`+need-soft`, line 7675) or `p` or `q` is hinted.  The ops:
   `call-op` is `%cal b sub-v pro` (no ring), `%caf … ring` (a ring), `%cam`
   and `%csm` (memo keys), `%csl`, `%csf` (the subject version, one
   register); `jump-op` is `%jmp b sub-v`, `%jmf`, `%jsp`, `%jsf`.
   * Under `%done` with no memo key, a tail call: not `mono`, one block
     `[~ ~ (jump-op ~)]`; `mono`, a register `sub-pes` and two blocks, the
     optimistic `jmp` and the pessimistic `jsp sub-pes`, which
     `+mono-try-call` (line 7255) joins with the tests that the subject has
     the parts (`%clq`) before the optimistic one.  With `sof`, `+soft-new`
     records the block as a soft call of kind `%tail`.
   * Otherwise `+simple-next`, `+kerf` (`out`, `pro`), and, not `mono`, one
     block `[~ [(call-op ~ pro)]~ %hop ~ out]`, with `sof` recorded as a soft
     call of kind `%call`; `mono`, two call blocks (`pro-opt`, `pro-pes`) that
     hop with their product to a block `merge` that moves it to `pro`.
   * `nex-arg` is `%next` of `lazy-from-need sub-ned` into the call block;
     when the block is a soft call, `+soft-bond` (line 5206) emits three
     blocks `h`, `o`, `l` before it, tags `o` with the region and moves the
     soft call's record to `o`, and the need becomes a bond at `o`.
   * Then `q` (skipped when `+safe-fol-fol`, as when the analysis made it a
     constant `[1 battery]`), `+past` over `p`, `p` for `laz.nex-arg`, and
     `+copy`.
   The soft calls are finished after `+coerce-lazy` (`+soft-done`, line 5286,
   `+soft-emit`): the nouns that `+kern` and `+kern-need` asked to take apart
   in a soft block (`+soft-ask`) are fetched there, with tries that fall back
   to the subject version of the callee.

What `gen` holds that `Gen` lacks (`+$line-short`, line 2965): `cache`
(`nary`, `mono`, `sccs`, `inl`, `sure`), `soft` (the soft calls by block) and
`sofs` (the same for shapes).  `+kern` reads `soft` (`+soft-ask`), and so do
`+kern-need`'s callers (lines 5943, 5948, 6818) and `+soft-fork`.

## The raw blocks (`tools/hoon/calldump.hoon`, 2026-11-24)

`R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]` recurs on the tail of its
sample, so `+inlined` keeps every call of it.  Its bell is
`[[[& |] [R 0]] R]` and its need `[~ this]` (the sample whole, the battery
known).  The n-ary code, subject sock that knows nothing.  The registers of
the raw blocks are those of the model plus the number of arguments
(`+to-straight` puts the arguments first); hop-only blocks are chased away.

* `[2 [0 3] [0 2]]` (need `[this this]`, 2 arguments): `0w0 mov v1 v4, mov v0
  v5, hop 3`; `0w3 nok v4 v5 v3, hop 2`; `0w2 mov v3 v2, hop 1`; `0w1 don v2`.
* `[8 [1 R] [9 2 [0 1]]]` (need `this`): nomm `[7 [[1 R] [0 1]] [7 [0 1] [2
  [0 1] [1 R] [R-bell ~]]]]` (the formula became the constant `[1 R]`);
  `0w0 mov v0 v1, hop 1`; `0w1 jmp R-bell [v1]`, a tail call.
* `[4 [8 [1 R] [9 2 [0 1]]]]`: `0w0 mov v0 v3, hop 3`; `0w3 cal R-bell [v3]
  v4, hop 2`; `0w2 mov v4 v2, hop 1`; `0w1 inc v2 v1, don v1`.
* `[[8 [1 R] [9 2 [0 1]]] [0 1]]`: `0w5 cal R-bell [v4] v5, hop 4`; `0w4 mov
  v5 v2, hop 3`; `0w3 mov v0 v3, hop 2`; `0w2 con v2 v3 v1, hop 1`; `0w1 don
  v1`; `0w0 mov v0 v4, hop 5` (the call runs first, the tail after it).
* `[6 [3 [0 1]] [8 [1 R] [9 2 [0 1]]] [1 0]]`: `0w9 clq v3 7 1`; `0w7 mov v0
  v2, hop 2`; `0w2 jmp R-bell [v2]` (a tail call in a branch); `0w1 imm 0
  v1, don v1`.
* `[6 [8 [1 R] [9 2 [0 1]]] [1 0] [1 1]]` (the call for `%pick`): `0w7 cal
  R-bell [v3] v5, hop 6`; `0w6 mov v5 v4, hop 5`; `0w5 brn v4 2 1`; `0w2 imm
  0 v2, don v2`; `0w1 imm 1 v1, don v1`.
* `[7 [8 [1 R] [9 2 [0 1]]] [1 5]]`: the call is kept (`R` is impure, it has
  a `%6`): `0w3 cal R-bell [v2] v3, hop 1`, `v3` read by nothing.
* `R` itself (need `[~ this]`): `0w8 clq v3 6 7`; `0w6 mov v0 v4, cel v4, tal
  v4 v5, mov v5 v2, hop 2`; `0w2 jmp R-bell [v2]` (the recursive tail call);
  `0w7 mov v0 v1, hop 1`; `0w1 don v1`.
* The whole-subject versions of the same tops call with tries: `[8 [1 R] [9
  2 [0 1]]]` has `0w1 jmp R-bell [v1]` after `%clq` tests of the subject and
  `0w2 jsp R-bell v2` when a part is missing (`+mono-try-call`).

## The model

* `CallEnv`: what the `%2` case reads of the rest of the compiler as
  functions of the callee: its need (`+callee-need`), what it reads first
  (`+callee-sure`), `pure`, its ring, `hinted` of the code table, and `sof`.
  `+callee-need` may compile the callee's SCC and extend `cache`, but a
  callee's n-ary need, once compiled, does not change within a poke, so a
  function is exact for the runs of one function.  `+sound` and
  `+need-soft` are not modelled yet: `sof` is a parameter.
* `SoftCall`, `GenC`: the state with `soft` and `sofs` (for the soft calls,
  not used by the definitions below).
* `callL`: the case `%2` for `mono` `|`, no memo key, no ring and `sof` false,
  with the runs of `p` and `q` as parameters (as `sixNextL` takes them).  It
  is exact there: the call block is fresh, so it is no soft call and
  `+soft-bond` is not reached, and `+kern` meets no soft block.
  `none` for the cases not modelled.
* `checks`: `#guard` lines that run `callL` on the inner `%2` of the cases
  above and compare the blocks with the raw blocks (registers shifted).
* `CalleeNeeds`, `CallSem`, `RunOKC`: the run relation (stated, not proved).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-! ## What the case reads of the rest of the compiler -/

/-- **What the case `%2` reads of the rest of the compiler**, as functions
of the callee. -/
structure CallEnv where
  /-- `+callee-need` (a hot jet's need, `map-local` or `top` in the SCC, the
  n-ary cache or a compile of the callee's SCC outside it). -/
  need : Bell → Option NeedOrd
  /-- `+callee-sure`: `sure.cache`, `[%none ~]` when absent. -/
  sure : Bell → NeedOrd
  /-- `pure` of the callee's code entry. -/
  pure : Bell → Bool
  /-- The ring of the callee in `call.cole`, when it is a jet. -/
  ring : Bell → Option Noun
  /-- `+hinted` reads the code table through this. -/
  cod : Bell → Option Bool
  /-- `sof` of lines 3967 to 3974, on `made p sup`, `p`, `q`, the callee and
  `b-ned` (`+sound`, `+need-soft` and `+hinted` are not modelled yet). -/
  sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool

/-- `+$soft-call` (line 2999): the kind (`%call` 0, `%tail` 1, `%mean` 2),
the callee and its ring, its need with the call's registers, what it reads
first, the blocks `plain`, `head`, `last`, the product and the block after,
and the nouns to take apart with their needs. -/
structure SoftCall where
  kin : Nat
  b : Bell
  rin : Option Noun
  ned : Need
  sur : NeedOrd
  plain : Nat
  head : Nat
  last : Nat
  pro : Nat
  out : Nat
  req : List (Nat × Need)

/-- **The state of `+comp` with the soft calls**: `Gen` and `soft`, `sofs`.
`cache` is not state here: what the case reads of it is `CallEnv`. -/
structure GenC (Map : Type → Type) extends Gen Map where
  soft : Map SoftCall
  sofs : List Nat

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- `+made`: the formula that makes the product of `nom`, `sup` for `[0 1]`. -/
def made (nom : Nomm) (sup : Option Nomm) : Nomm :=
  match nom, sup with
  | Nomm.n0 1, some s => s
  | _, _ => nom

/-! ## The case `%2` -/

/-- **The case `%2` of `run`** for `mono` `|`, with the runs of the subject
`p` and of the formula `q` as parameters (`rp`, `rq`): the indirect call,
the dropped call, and the direct call with no memo key, no ring and `sof`
false (a tail call under `%done`, else a `%cal` into the block of `+kerf`).
`none` on the other direct calls (not modelled). -/
def callL (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CM Map (NextL S) :=
  match info with
  | Option.none => do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let rSub ← re
      let rFol ← re
      let o ← emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩
      let nexFol ← rq (CGoalL.next (ofSure (lazyReg rFol)) (jmp0 o)) region
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next (ofSure (lazyReg rSub)) nexFol.th) region
      copyL nexSub nexFol.laz
  | some (b, key) =>
      let drop : Option Jmp := match goal with
        | CGoalL.next laz th => if env.pure b && noneEquivalentL laz then some th else Option.none
        | _ => Option.none
      match drop with
      | some th => do
          let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
            else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
          let nexFol ← pastL env.cod nexFol p region
          let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
          copyL nexSub nexFol.laz
      | Option.none =>
          match key, env.ring b, env.need b with
          | Option.none, Option.none, some bNed =>
            if env.sof (made p sup) p q b bNed then fun _ => Option.none else do
            let subNed ← needOrdAllocRegs bNed
            let subV := flattenNeed subNed
            let callBlock ← (match goal with
              | CGoalL.done => emit ⟨[], [], Termin.jmp b subV⟩
              | g => do
                  let nex ← simpleNextL g
                  let (out, pro) ← kerf nex
                  emit ⟨[], [Pole.cal b subV pro], Termin.hop (jmp0 out)⟩ : CM Map Nat)
            let nexArg : NextL S := ⟨ofSure ⟨subNed, HoonSet.empty⟩, jmp0 callBlock⟩
            let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
              else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
            let nexFol ← pastL env.cod nexFol p region
            let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
            copyL nexSub nexFol.laz
          | _, _, _ => fun _ => Option.none

/-! ## Checks against the raw blocks

A map and a set that evaluate, and `callL` on the inner `%2` of the cases of
`tools/hoon/calldump.hoon`, from the state the enclosing nomms leave (the
`%4` of `[4 …]` has emitted its block `1` and taken registers `0`, `1`; the
`%6` of the `%pick` case its four blocks and registers `0`, `1`).  The
expected blocks are the raw blocks with the registers less the number of
arguments, before `+to-straight` chases the hop-only blocks. -/

/-- A map as a function with the list of its keys. -/
structure FM (ν : Type) where
  f : Nat → Option ν
  ks : List Nat
  ok : ∀ k, k ∈ ks ↔ (f k).isSome

instance : HoonMap FM where
  empty := ⟨fun _ => Option.none, [], fun k => by simp⟩
  get m k := m.f k
  put m k v := ⟨fun k' => if k' = k then some v else m.f k', k :: m.ks, fun k' => by
    by_cases e : k' = k
    · subst e; simp
    · simp [e, m.ok k']⟩
  del m k := ⟨fun k' => if k' = k then Option.none else m.f k', m.ks.filter (fun x => x ≠ k), fun k' => by
    by_cases e : k' = k
    · subst e; simp
    · simp [e, m.ok k']⟩
  toNoun _ _ := A 0
  get_empty _ := rfl
  get_put _ _ _ _ := rfl
  get_del _ _ _ := rfl
  toNoun_empty _ := rfl

instance : HoonMapKeys FM where
  keys m := m.ks
  mem_keys m k := m.ok k

/-- A set as a list. -/
structure LS where
  l : List Nat

instance : HoonSet LS where
  empty := ⟨[]⟩
  toList s := s.l
  put s x := ⟨x :: s.l⟩
  uni a b := ⟨a.l ++ b.l⟩
  isEmpty s := s.l.isEmpty
  small s := s.l.all (· = 1)
  toNoun _ := A 0
  mem_empty _ := by simp
  mem_put _ _ _ := by simp
  mem_uni _ _ _ := by simp
  isEmpty_iff _ := by simp
  small_iff _ := by simp
  toNoun_empty := rfl

/-- `R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]`. -/
def nounR : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 3)))
    (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 3) (C (A 0) (A 7))) (C (A 0) (A 1)))))) (C (A 0) (A 3))))

/-- The bell of `R` in the dumps: `[[[& |] [R 0]] R]`. -/
def bellR : Bell := ⟨Sock.mk (Cape.cell Cape.yes Cape.no) (C nounR (A 0)), nounR⟩

/-- The environment of the dumps: `R` needs `[~ this]`, is impure, no jet,
no soft call. -/
def envR : CallEnv :=
  ⟨fun b => if b = bellR then some (NeedOrd.pair NeedOrd.none NeedOrd.this) else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false,
   fun _ _ _ _ _ => false⟩

/-- The blocks `lo ..< hi` of a state. -/
def blocksIn (g : Gen FM) (lo hi : Nat) : List (Nat × Option Blob) :=
  (List.range (hi - lo)).map fun i => (lo + i, g.blocks.f (lo + i))

/-- A state with registers from `re` and labels from `bo`, the labels below
`bo` holding placeholders. -/
def genAt (re bo : Nat) : Gen FM :=
  ⟨re, bo, 0, false,
   ⟨fun k => if 1 ≤ k ∧ k < bo then some ⟨[], [], Termin.bom Option.none⟩ else Option.none,
    (List.range bo).filter (1 ≤ ·), fun k => by
      by_cases h : 1 ≤ k ∧ k < bo
      · simp [h, List.mem_filter, List.mem_range]
      · simp only [h, if_false, Option.isSome_none, List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro ⟨a, b⟩; exact absurd ⟨b, a⟩ h
        · intro e; cases e⟩,
   ⟨fun _ => Option.none, [], fun k => by simp⟩, ⟨fun _ => Option.none, [], fun k => by simp⟩⟩

/-- The runs of the parts: the existing `runL` (the parts here are `%0` and
`%1`). -/
def runP : Nomm → CGoalL LS → List Nat → CM FM (NextL LS) := fun nm goal region => runL nm goal region

/-- The inner `%2` of the direct cases: `[2 [0 1] [1 R] [R-bell ~]]`. -/
def callR : Nomm := Nomm.n2 (Nomm.n0 1) (Nomm.n1 nounR) (some (bellR, Option.none))

/-- `callL` on `n` for `goal` from `g`: the blocks `lo ..< hi` and the
result's sure need. -/
def callOut (n : Nomm) (goal : CGoalL LS) (g : Gen FM) (lo hi : Nat) : Option (List (Nat × Option Blob) × Need) :=
  match n with
  | Nomm.n2 p q info =>
      (callL envR (runP p) (runP q) p q info Option.none goal [] g).map fun (nex, g') =>
        (blocksIn g' lo hi, nex.laz.sure.ned)
  | _ => Option.none

/-- `[2 [0 3] [0 2]]` for `%done` from `gen0` shifted by the two arguments:
`don v2`, `mov v3 v2`, `nok v4 v5 v3` become `don 0`, `mov 1 0`, `nok 2 3 1`;
the subject needs `[this 3 this 2]`: the formula at axis 2, the subject at
axis 3 (the raw entry moves `v0` to `v5`, `v1` to `v4`). -/
def indOut : Option (List (Nat × Option Blob) × Need) :=
  callOut (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) CGoalL.done (genAt 0 1) 1 4

#guard indOut ==
  some ([(1, some ⟨[], [], Termin.don 0⟩), (2, some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩),
    (3, some ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩)],
    Need.pair (Need.this 3) (Need.this 2))

/-- The tail call of `[8 [1 R] [9 2 [0 1]]]`: `jmp R-bell [v1]` is
`jmp R-bell [0]`, and the core needs `[~ this 0]`. -/
def tailOut : Option (List (Nat × Option Blob) × Need) := callOut callR CGoalL.done (genAt 0 1) 1 2

#guard tailOut ==
  some ([(1, some ⟨[], [], Termin.jmp bellR [0]⟩)], Need.pair Need.none (Need.this 0))

/-- The call under `%next` of `[4 [8 [1 R] [9 2 [0 1]]]]`, after the block
`1` of the increment (`inc v2 v1, don v1`: registers `0` and `1`): `cal
R-bell [v3] v4, hop 2` and `mov v4 v2, hop 1` are `cal R-bell [2] 3` and
`mov 3 1`. -/
def nextOut : Option (List (Nat × Option Blob) × Need) :=
  callOut callR (CGoalL.next (ofSure (lazyReg 1)) (jmp0 1)) (genAt 2 2) 2 4

#guard nextOut ==
  some ([(2, some ⟨[], [Pole.mov 3 1], Termin.hop (jmp0 1)⟩),
    (3, some ⟨[], [Pole.cal bellR [2] 3], Termin.hop (jmp0 2)⟩)], Need.pair Need.none (Need.this 2))

/-- The call for `%pick` of `[6 [8 [1 R] [9 2 [0 1]]] [1 0] [1 1]]`, after the
branches (registers `0`, `1`) and the `%6`'s two hop blocks `3` and `4`:
`brn v4`, `mov v5 v4`, `cal R-bell [v3] v5` are `brn 3`, `mov 4 3`, `cal
R-bell [2] 4`. -/
def pickOut : Option (List (Nat × Option Blob) × Need) :=
  callOut callR (CGoalL.pick (jmp0 3) (jmp0 4)) (genAt 2 5) 5 8

#guard pickOut ==
  some ([(5, some ⟨[], [], Termin.brn 3 (jmp0 3) (jmp0 4)⟩),
    (6, some ⟨[], [Pole.mov 4 3], Termin.hop (jmp0 5)⟩),
    (7, some ⟨[], [Pole.cal bellR [2] 4], Termin.hop (jmp0 6)⟩)], Need.pair Need.none (Need.this 2))

/-! ## The run relation of a call (stated, not proved)

The relations of the fragment so far (`RunOKV`, `RunOKNV`) take the product
of a nomm from `pureEval` and keep the oracle's state: their `GoalSem` says
`goJ … st regs t je = goJ … st regs' t th`.  A call changes both: the callee
may crash or block with a trace, and the oracle's state moves (the needs it
answers with grow).  So the relation for nomms with calls takes `+mink`'s
tone from `nommF` and lets the state move, under the hypotheses of
`ContractFwd`. -/

section
variable {σ : Type}

/-- **The callees' needs the compiler used are those of the table** against
which the contract is stated: the arguments of `%cal b v` are the split of
the callee's subject by `N b false` (`argsFor`), which is what `OracleFwd`
asks of a call. -/
def CalleeNeeds (env : CallEnv) (N : Needs) : Prop :=
  ∀ b nd, env.need b = some nd → N b false = some nd

/-- **The registers of a callee's need hold its arguments** (to prove):
the need that `+need-ord-alloc-regs` makes of `nd`, held by the noun `s`,
reads in the order of `+flatten-need` the split of `s` by `nd`. -/
def AllocSplit (Map : Type → Type) [HoonMap Map] : Prop :=
  ∀ (nd : NeedOrd) (g g' : Gen Map) (sub : Need), needOrdAllocRegs nd g = some (sub, g') →
    ∀ (regs : Map (Option Noun)) (s : Noun), HoldsN sub regs s →
      (flattenNeed sub).mapM (fun r => SkaModel.read r regs) = SkaModel.split nd s

/-- **What the call block does** (to prove from `execBlob` and `execPole`):
the oracle answers the call of `b` on the arguments' values with the
caller's trace; a product goes to `pro` and the code hops to `out`; any
other tone, a crash or a block, is the function's, at the state reached. -/
def CallBlockSem (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) : Prop :=
  ∀ (o out pro : Nat) (b : Bell) (subV : List Nat), HoonMap.get c.blocks o =
      some ⟨[], [Pole.cal b subV pro], Termin.hop (jmp0 out)⟩ →
    ∀ (st : σ) (regs : Map (Option Noun)) (t : Trace) (vs : List Noun), subV.mapM (fun r => SkaModel.read r regs) = some vs →
      goJ lib O c gul st regs t (jmp0 o) = (O.call st b false vs t gul).bind fun (ton, st') =>
        match ton with
        | Tone.zero p => goJ lib O c gul st' (store pro p regs) t (jmp0 out)
        | ton => some (ton, st')

/-- The code from `je` returns a tone that stands for `r`, at a state where
`Inv` holds and whose needs include those of `st`. -/
def ReturnsC (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (Inv : σ → Prop)
    (ν : σ → Needs) (st : σ) (regs : Map (Option Noun)) (t : Trace) (je : Jmp) (r : Tone) : Prop :=
  ∃ ton st', Inv st' ∧ ν st ≤ ν st' ∧ goJ lib O c gul st regs t je = some (ton, st') ∧ ToneRel lib (ν st') ton r

/-- The code from `je` goes on as the code from `j` with the registers
`regs'` (the ones of `K` as in `regs`), at a state where `Inv` holds and
whose needs include those of `st`. -/
def GoesC (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (Inv : σ → Prop)
    (ν : σ → Needs) (K : Nat → Prop) (st : σ) (regs : Map (Option Noun)) (t : Trace) (je j : Jmp)
    (P : Map (Option Noun) → Prop) : Prop :=
  ∃ st' regs', Inv st' ∧ ν st ≤ ν st' ∧ P regs' ∧ (∀ x, K x → SkaModel.read x regs' = SkaModel.read x regs) ∧
    goJ lib O c gul st regs t je = goJ lib O c gul st' regs' t j

/-- **What entering `je` does for the goal when the code may call**, for
`+mink`'s tone `r` on the nomm (`GoalSem` with the oracle's state moving).
A product goes on to the goal's jump holding the goal's need (`%next`, a
crash when it does not fit), picks the branch (`%pick`, a crash on another
atom or a cell), or is returned (`%done`); a crash or a block of `+mink` is
returned, standing for `r`. -/
def GoalSemC (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (Inv : σ → Prop)
    (ν : σ → Needs) (K : Nat → Prop) (st : σ) (regs : Map (Option Noun)) (t : Trace) (je : Jmp) :
    CGoal S → Tone → Prop
  | CGoal.done, r => ReturnsC lib O c gul Inv ν st regs t je r
  | CGoal.next laz th, Tone.zero p =>
      (FitsS laz p → GoesC lib O c gul Inv ν K st regs t je th (fun regs' => HoldsN laz.ned regs' p)) ∧
      (¬ FitsS laz p → ReturnsC lib O c gul Inv ν st regs t je (Tone.two t))
  | CGoal.pick z o, Tone.zero p =>
      (p = A 0 → GoesC lib O c gul Inv ν K st regs t je z (fun _ => True)) ∧
      (p = A 1 → GoesC lib O c gul Inv ν K st regs t je o (fun _ => True)) ∧
      (p ≠ A 0 → p ≠ A 1 → ReturnsC lib O c gul Inv ν st regs t je (Tone.two t))
  | _, r => ReturnsC lib O c gul Inv ν st regs t je r

/-- **The run relation of a nomm with calls** (the forward half, the `sem`
of `RunOKV` and `RunOKNV` for code that calls).  For every oracle that
answers below `n` fuel as `+mink` does, keeps `Inv` and whose needs include
`N`, where the compiler used the needs of `N` (`CalleeNeeds`): when `nommF`
returns `r` on the subject `s` from `+mink`'s trace `tm`, the code entered at
the run's jump, with registers where the run's need holds `s`, a trace `ti`
that stands for `tm` and the blocks of the run agreeing with `c` at every
state (the lazy blocks run after calls), meets `GoalSemC`.  The trace passed
to a call is `ti` as the enclosing hints left it, which is where the frames
come in: `FrameRel` must hold of it at the call's state, so it must be
monotone in the needs. -/
def SemC (lib : Lib) (env : CallEnv) (N : Needs) (code : Bell → Option Nomm) (nm : Nomm) (goal : CGoal S)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  CalleeNeeds env N →
  ∀ (c : Straight Map) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat) (gul : Noun)
    (ti tm : Trace) (s s0 : Noun) (r : Tone) (cf : Map (Nat × List Nat)) (ned : Need),
    (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    nommF lib gul code n tm s nm = some r →
    (∀ st, AgreeU lib O c gul st ti cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ st, Inv st → Forall2 (FrameRel lib (ν st)) ti tm →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemC lib O c gul Inv ν (fun x => x < g0.re ∨ NMem ned x) st regs ti nex.th goal r

end

end Comp
end SkaModel
end Formalization
