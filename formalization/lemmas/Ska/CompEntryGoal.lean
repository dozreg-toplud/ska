import lemmas.Ska.CompFragX

/-!
# The open case: runs for a goal `%next` whose need has forks (statements)

Nothing here is proved.  These are the statements that the last piece of
the pure fragment needs: a `%6` (or any nomm) that runs for a goal `%next
laz th` whose lazy need `laz` has entries, as `p` of `[7 p q]` when `q`
ends in a `%6` (`[7 [6 [0 2] [1 1] [1 2]] [6 [0 2] [0 3] [0 1]]]`), and as a
branch of the case `sixNextFork`.

## (a) `RunOKE`: the relation for a goal with entries

A run for such a goal does two things that a run for a fork-free goal does
not.  It puts ops in front of the old bodies of the goal's lazy blocks
(`+collapse-lazy-atom`, `+kern`, `+fork` reach into them through `walkLazy`),
and those ops read registers that the run writes, directly in the block that
the goal's jump enters and through a proxy elsewhere.  So the filling of the
goal's entries can only be stated relative to the registers at the time the
code of the run reaches `th`: the code between `th` and an entry block is
the code of the goal's continuation, which writes only registers allocated
before the run (and never the input registers), so at the entry block the
registers agree with those at `th` on the registers the run allocated.

`EntryFill`: for every entry `e` of `laz`, the run put ops `Arun` in front of
the old body of the block `e.1` (`g1` holds `⟨[], Arun ++ body, fin⟩` where
`g0` held `⟨[], body, fin⟩`), and for every `R` that agrees with the
registers `regs'` at `th` on the registers in `[g0.re, g1.re)` and holds the
input need `ned` for `s0`, the ops `Arun` fill `e`'s need for the product
`p` (and crash when `p` has not its shape), keeping the input registers and
the registers allocated before the run outside `e`'s need.  `GoalSemE` is
`GoalSem` of the sure part with `EntryFill` at the `regs'` it gives, and
`RunOKE` is `RunOKN` with it.  For a goal without entries (`ofSure`),
`EntryFill` holds trivially and `RunOKE` is `RunOKN` (`entryFill_ofSure`).

## (b) The threading of `+sect` and the proxies

The invariant in the author's words: a register passed `~` is defined, just
poisoned; it may be moved through joins; every real read of it is guarded by
the threaded conditionals.  In terms of `cond` (proxy `k ↦ (d, tag)`: the
register `k` stands for `d` in the blocks of the region `tag`):

1. `ProxyHeld cond val regs`: at a block of the region `tag` reached on a
   path where the proxy's definition was made (`val d = some v`), `k` holds
   `v` or is poisoned.  A move or a hop argument from `k` keeps this, and a
   join parameter that `+sect` threads for `k` is passed `d` by the branch
   that made the proxy and `~` by the other.
2. `GuardedReads`: every op of a block of the region `tag` that really reads
   `k` (not a `%mov`, not a hop argument) lies after a `%brn` or `%brz` on
   the test register of the `%6` whose branch made the proxy, on the side of
   that branch, so on every path that reaches it `k` holds `v`.

The first is a property of the registers at a block, stated below.  The
second is a property of the paths of the program, which needs a path
semantics of `execBlob` that the formalization does not have yet.  On the
real compiler it holds on all 162 threading test formulas of
`tools/hoon/thread-*.hoon`, before and after `+optimize`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The filling of the goal's entries, relative to the registers `regs'`
at the time the code reaches the goal's jump.** -/
def EntryFill (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 p : Noun) (regs' : Map (Option Noun)) : Prop :=
  ∀ e ∈ entries laz, ∃ (body : List Pole) (fin : Termin) (Arun : List Pole),
    HoonMap.get g0.blocks e.1 = some ⟨[], body, fin⟩ ∧ HoonMap.get g1.blocks e.1 = some ⟨[], Arun ++ body, fin⟩ ∧
    ∀ R : Map (Option Noun), (∀ r, g0.re ≤ r → r < g1.re → SkaModel.read r R = SkaModel.read r regs') →
      HoldsN ned R s0 →
      (FitsS e.2.sure p → ∃ R', Runs lib O c gul st t Arun R R' ∧ HoldsS e.2.sure R' p ∧
        ∀ x, (NMem ned x ∨ x < g0.re) → ¬ NMem e.2.sure.ned x → SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ FitsS e.2.sure p → Crashes lib O c gul st t Arun R)

/-- **`GoalSem` for a goal `%next laz th` with entries**: the sure part as
`GoalSem` says, and the entries filled relative to the registers at `th`. -/
def GoalSemE (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (K : Nat → Prop)
    (ned : Need) (g0 g1 : Gen Map) (s0 : Noun) (regs : Map (Option Noun)) (t : Trace) (je : Jmp)
    (laz : Lazy S) (th : Jmp) : Option Noun → Prop
  | none => goJ lib O c gul st regs t je = some (Tone.two t, st)
  | some p =>
    (FitsS laz.sure p → ∃ regs', HoldsN laz.sure.ned regs' p ∧
      (∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      goJ lib O c gul st regs t je = goJ lib O c gul st regs' t th ∧
      EntryFill lib O c gul st t ned g0 g1 laz s0 p regs') ∧
    (¬ FitsS laz.sure p → goJ lib O c gul st regs t je = some (Tone.two t, st))

/-- **The relation for one run for a goal `%next laz th` whose need may have
entries** (the statement of the open case).  `RunOKN` with `GoalSemE`; the
entries of the result and those of the goal share no label (the goal's
were allocated before the run). -/
structure RunOKE (lib : Lib) (nm : Nomm) (laz : Lazy S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem laz.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ ¬ FitsS laz.sure p
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemE lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem laz.sure.ned r) ned g0 g1 s0 regs t
      nex.th laz th (pureEval nm s)

/-- A goal without entries asks nothing of them. -/
theorem entryFill_ofSure (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (g0 g1 : Gen Map) (sur : Sure S) (s0 p : Noun) (regs' : Map (Option Noun)) :
    EntryFill lib O c gul st t ned g0 g1 (ofSure sur) s0 p regs' := by
  intro e he; rw [entries_ofSure] at he; exact absurd he List.not_mem_nil

/-- **(b), the part on registers**: at a block of a proxy's region reached
where the proxy's definition `d` was made with the value `val d`, the proxy
register holds that value or is poisoned (passed `~` by the other branch of
a join and only moved since). -/
def ProxyHeld (cond : Map (Nat × List Nat)) (val : Nat → Option Noun) (regs : Map (Option Noun)) : Prop :=
  ∀ k d tag, HoonMap.get cond k = some (d, tag) → ∀ v, val d = some v →
    HoonMap.get regs k = some (some v) ∨ HoonMap.get regs k = some Option.none

end Comp
end SkaModel
end Formalization
