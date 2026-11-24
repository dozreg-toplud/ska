import lemmas.Ska.CompFragX

/-!
# The open case: runs for a goal `%next` whose need has entries

The statements that the last piece of the pure fragment needs: a nomm `p`
that runs for a goal `%next laz th` whose lazy need `laz` has entries, as `p`
of `[7 p q]` when `q` has a `%6` (`[7 [6 [0 2] [1 1] [1 2]] [6 [0 2] [0 3] [0 1]]]`),
and as a branch of the case `sixNextFork`.

## (a) `RunOKE`: the relation for a goal with entries

The arms that meet a goal with entries keep the goal's labels.  `+from`
(`%0`) moves the need of each entry under the axis and puts no op.
`+split` (cons) and `+into` (`%10`) split the need of each entry at its own
label and put `%con` ops in front of the old body, which read the halves.
`+mede` (`%1`), `+collapse-lazy-atom` (`%3`, `%4`, `%5`), `+kern` and `+fork`
consume the entries and put ops in front of their bodies; all but `+mede`
read a register of the run there, through a proxy.  So `RunOKE` pairs each
entry `(o, L)` of the goal with the ops `F` the run put in front of block `o`
and with the entry of the result at `o`, if any: that entry's need, filled
by the final pass and followed by `F`, fills `L` for the product
(`FrontSem`); with no entry there, `F` alone fills `L`.  The other entries
of the result are new, from a `%6` in `p`, as in `RunOKG`.
`CompEntryRun.lean` proves it for `%0` and composes it with `RunOKG` of `q`
for `[7 p q]`.

The earlier statement (`EntryFill`, `GoalSemE`) put every entry of the
result at a new label and so fitted none of these arms.

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

/-- **What the ops `F` put in front of a goal entry's block do**: whatever
fills the result's need `L'` at that label for the subject `s` of the run,
followed by `F`, fills the goal entry's need `L` for the product `v` of the
nomm.  `lo` bounds the registers the fill keeps at the result (the end of the
run), `lo0` at the goal (the start of the run).  For an entry of the goal that
the run consumes (no entry of the result at its label), `L'` is the bunt and
the final pass puts nothing there, so `F` alone fills `L` (`A = []`). -/
def FrontSem (lo0 lo : Nat) (nm : Nomm) (L' : Sure S) (F : List Pole) (L : Sure S) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace) (ned : Need)
    (A : List Pole) (s0 s v : Noun), (∀ r, NMem ned r → lo ≤ r) → pureEval nm s = some v →
    FillSem (Map := Map) lib O c gul st t ned lo L' A s0 s → FillSem lib O c gul st t ned lo0 L (A ++ F) s0 v

/-- **The relation for one run of `runL` for a goal `%next laz th` whose
need may have entries.**  It replaces the earlier statement, which put every
entry of the result at a new label.  The entries of the goal keep their
labels: each gets ops `F` in front of its old body (`front`), and either the
result has an entry at the same label whose need, filled and followed by
`F`, fills the goal entry's need, or the run consumed it and `F` alone fills
it (`FrontSem`).  Every other entry of the result is new, as in `RunOKG`
(`labs`).  The blocks below `g0.bo` other than the goal's entries are kept
(`keep`); `GrowU` keeps only terminators and parameters, so it holds through
`F`.  `cnd`: the run makes no proxy. -/
structure RunOKE (lib : Lib) (nm : Nomm) (laz : Lazy S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  re : g0.re ≤ g1.re
  bo : g0.bo ≤ g1.bo
  drop : g1.drop = g0.drop
  keep : ∀ o, o < g0.bo → o ∉ (entries laz).map Prod.fst → HoonMap.get g1.blocks o = HoonMap.get g0.blocks o
  grow : GrowU g0 g1
  cnd : g1.cond = g0.cond
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  thle : th.there ≤ nex.th.there
  ent : Fresh g1 nex.th ∨ nex.th = th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem laz.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r →
    (∃ e0 ∈ entries laz, NMem e0.2.sure.ned r) ∨ (g0.re ≤ r ∧ r < g1.re)
  labs : ∀ e ∈ entries nex.laz, e.1 ∈ (entries laz).map Prod.fst ∨
    (g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧ ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩)
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ (entries laz).length + 2 * sixCount nm
  front : ∀ e ∈ entries laz, ∃ F : List Pole,
    (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
    ((∃ L', (e.1, L') ∈ entries nex.laz ∧ FrontSem (Map := Map) g0.re g1.re nm L'.sure F e.2.sure) ∨
     (e.1 ∉ (entries nex.laz).map Prod.fst ∧ FrontSem (Map := Map) g0.re g1.re nm Sure.bunt F e.2.sure))
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ ¬ FitsS laz.sure p
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem laz.sure.ned r) regs t nex.th
      (CGoal.next laz.sure th) (pureEval nm s)

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
