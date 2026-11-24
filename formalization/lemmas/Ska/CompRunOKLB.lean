import lemmas.Ska.CompHypOfNC

/-!
# One relation for runs under any lazy goal, with bodies at the entries: `RunOKLB`

README Gaps 12.23.  `RunOKLC` (`CompRunOKLC.lean`) is false for three
kinds of runs that real code produces (`tools/hoon/calldump4.hoon`, header of
`CompNC.lean`): a result entry's block may hold ops (`+split`'s `con`,
`+copy`'s moves, `+into`'s ops), and `+collapse-lazy-atom` reads the goal's
own sure register in the lazy blocks.  `RunOKLB` is `RunOKLC` with

* (a) **bodies at the result entries**: `labs` asks a result entry's block
  to be `⟨[], B, hop th⟩` for some `B` (not `B = []`), a new entry's label
  below the end `g1.bo` (not below the jump: the jump's place is a fact of
  `LOKB`, `CompSimBodyLift.lean`), and the `sem`
  clauses assume `AgreeLB` in place of `AgreeL`: at a result entry the run
  made, the program's block is `A ++ B` unproxied, `A` filling the entry's
  need, `B` the block's body in the run's final state;
* (b') **fronts that read the goal's sure registers**: with the flag `x`,
  the ops a run put in front of a goal entry's block may read the registers
  of the goal's sure need, which hold the product at the run's jump
  (`FrontLB`, the input `pair (pair ned d) E` holding `[[s0 w] v]` with `E`
  the goal's sure need when `x` and `none` otherwise).

## Why (b') and not the relaxed input need of `CollRunU`

The last session proposed for finding 3 the relaxed input need of
`CollRunU` (`InR`, `KeepI`): the `sem` of `q` in `[7 p q]` accepts input
registers of its own result's sure need and keeps them.  That is a
STRENGTHENING of `sem` (a weaker hypothesis on `ned`): no relation proved so
far has it for a nomm that calls, it does not follow from the strict `sem`
(the fills `AgreeL` describes read the extra registers, so the strict `sem`
cannot be instantiated with the strict part of `ned`), and `RunOKLC` would
not lift to it.  It needs the fact that a run's code keeps its own sure
registers (fact (i) of README Gaps 12.2 for runs that call, with a frame
argument), a new induction over every composition.

(b') puts the reading of the goal's register on the producer's side, where
it costs nothing: `RunOKLC` lifts with `x = false`, the leaves
`+collapse-lazy-atom` (`[3 p]`, `[4 p]`, `[5 p q]`) meet it with `x = true`
under every lazy goal, and the cons and `%10` absorb a part's `x`: `+split`
and `+into` allocate the halves' registers in the parent's run, the tail's
code keeps the head's goal registers (they are below the tail's start and
not its goal's), so the parent's witness contains them.  Only `[7 p q]`
with `x = true` for `p` and entries in `q`'s result needs more: `q` must keep
its own sure registers until its result entries' blocks, which is (b).

## The checks against the raw blocks

Registers `vN` and labels `N` of the model (`runLC envR none nm` from
`gen0`; the Hoon dump of `tools/hoon/calldump4.hoon` numbers registers one
higher and the same labels).  Each case is `[7 p q]`: `q` runs under
`%done` from `gen0` (state `g1`, result `L`, jump `j`), then `p` under
`%next L j` from `g1` (state `g2`); the fields are those of `p`'s run.

1. `%bc1` `[7 [[0 2] [0 3]] [[2 [0 2] [0 6]] [0 1]]]`.  `L = ⟨[v4 [v5 ~]],
   bond (3, v2)⟩`, `j = 7`, `g1.blocks 3 = ⟨[], [], hop 2⟩`.  `p`'s result
   `⟨[v4 [v5 ~]], bond (3, [v6 v7])⟩` and `g2.blocks 3 = ⟨[], [con v6 v7 v2],
   hop 2⟩`.  `labs`: the entry `3` is a goal label, its block is `⟨[], B, hop
   2⟩` with `B = [con v6 v7 v2]` (the old `labs`, `B = []`, fails).
   `front` at the goal entry `(3, v2)`: `F = [con v6 v7 v2]` in front of the
   empty body, the result entry `(3, [v6 v7])`; after any `A` that fills
   `[v6 v7]` for `p`'s subject `s` (`v6 = s/2`, `v7 = s/3`), `F` fills `v2`
   with `[s/2 s/3]`, the product: `FrontLB` with no witness (`d = none`) and
   `x = false`.  The final pass fills `[v6 v7]` from the input and keeps `B`:
   Hoon `3: mov v0 vg, cel vg, hed vg vi, mov vi v7, tal vg vh, mov vh v8,
   con v7 v8 v3, hop 2`, `A ++ B` as `AgreeLB` says.
2. `%bc2` `[7 [[0 1] [0 1]] [[2 [0 2] [0 6]] [[0 2] [0 3]]]]`.  `L =
   ⟨[v6 [v7 ~]], bond (5, [v3 v4])⟩` (`+split` of `q`'s tail put `con v3 v4
   v2` at `q`'s own split block `3`), `g1.blocks 5 = ⟨[], [], hop 4⟩`.  `p`'s
   result `⟨(both v8 v7 ~), bond (5, v3)⟩`, `g2.blocks 5 = ⟨[], [mov v3 v4],
   hop 4⟩` (`+copy` merging the halves `v3`, `v4` at `5`), `g2.blocks 11 =
   ⟨[], [mov v8 v6], hop 10⟩` (the copy block).  `labs`: body `[mov v3 v4]`.
   `front` at `(5, [v3 v4])`: `F = [mov v3 v4]`, `L' = v3`: after `A` fills
   `v3 := s`, `F` gives `v4 := s`, and `[v3 v4]` holds the product `[s s]`.
   Hoon `5: mov v0 v4, mov v4 v5, hop 3`: `A = [mov v0 v4]`, `B = [mov v4 v5]`.
3. `%s4t` `[7 [4 [0 3]] [[2 [0 1] [0 1]] [0 1]]]`.  `L = ⟨v4, bond (3, v2)⟩`,
   `j = 7`.  `p`'s `+collapse-lazy-atom` takes the goal's register `v4`:
   `g2.blocks 8 = ⟨[], [inc v7 v4], hop 7⟩`, `g2.blocks 3 = ⟨[], [mov v6 v2],
   hop 2⟩` with `v6` a proxy of `v4` (`cond` key `6`), result `⟨[~ v7]⟩`, no
   entries.  `front` at `(3, v2)`: `F = [mov v6 v2]`, unproxied `mov v4 v2`,
   no result entry at `3` (`L' = bunt`): `F` fills `v2` with the product from
   `E = this v4` holding it, so `FrontLB` holds with `x = true` and fails with
   `x = false` (`v4` is in neither `ned` nor `d`); `dreg` holds (`d = none`).
   The composition `[7 p q]` then needs `q`'s code (`6: mov v4 v5`, `5: nok
   v4 v5 v3`, `4: mov v3 v1`) to keep its own sure register `v4` until the
   bond block `3`, which no relation states (b): open.
4. `%s10` `[7 [10 [2 [0 3]] [0 1]] [[2 [0 2] [0 6]] [0 1]]]`.  `L` as in 1.
   `+into` puts `con v6 v7 v2` at `3`, the donor `[0 3]` keeps `(3, [~ v6])`,
   the recipient `[0 1]` keeps `(3, [~ v7])`, `+copy` merges them into `(3,
   [~ v7])` with `mov v7 v6`: `g2.blocks 3 = ⟨[], [mov v7 v6, con v6 v7 v2],
   hop 2⟩`, result `⟨[~ (both v8 v5 ~)], bond (3, [~ v7])⟩`.  `labs`: body.
   `front`: `F = [mov v7 v6, con v6 v7 v2]`, `L' = [~ v7]`: `v7 := s/3`, then
   `v6 := s/3`, `v2 := [s/3 s/3]`, the product of `[10 [2 [0 3]] [0 1]]`.
5. `%lim` `[7 [[0 3] [0 1]] [[2 [0 2] [0 6]] [0 3]]]` (`[8 [0 3] ..]`), old
   relation.  `L = ⟨[v4 [v5 ~]], bond (3, [~ v2])⟩`; the bond need is a pair,
   `+split` puts nothing, the head `[0 3]` drops its empty half, the tail
   `[0 1]` keeps `(3, v2)`: result `⟨[v5 v4], bond (3, v2)⟩`, `g2.blocks 3 =
   ⟨[], [], hop 2⟩`: `labs` with `B = []`, `front` with `F = []`, `L' = v2`
   (`v2 := s`, and `[~ v2]` holds the product `[s/3 s]`).
6. `%s7g` `[7 [2 [0 3] [0 2]] [[2 [0 3] [0 2]] [0 1]]]`, old relation.  `L =
   ⟨[v5 v4], bond (3, v2)⟩`; `p`'s `+kerf` puts `mov v10 v2` at `3` (`v10` a
   proxy of `+kern`'s register `v6`, allocated in `p`'s run, `re` 6 to 13),
   no result entry: `d = this v6` (`dreg`), `x = false`.
7. `%cc2` `[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` under `%done`, old relation:
   the head runs under the bond goal `⟨bunt, bond (3, v1)⟩` and `+kern` puts
   `mov v7 v1` at `3` (`v7` a proxy of the fresh `v6`); the cons's result
   `⟨[v9 v8], bond (7, [v5 v4])⟩` has `g.blocks 7 = ⟨[], [], hop 6⟩`.  (So
   does `%h4c`: `+collapse-lazy-atom` under the bond goal, whose sure part
   asks nothing, takes a fresh register, `8: inc v8 v6`, `3: mov v7 v1`.)

## Contents

* `AgreeLB`, `gsE`, `FrontLB`, `SemLB`, `SemLBB`, `RunOKLB`.
* `AgreeLB.toL`, `AgreeL.toB`: with empty bodies the two agree.
* `frontLB_of_frontLC`, `FrontLB.up`: the lift and the weakening of `x`.
* `RunOKLC.toB` (`x = false`), `RunOKLB.up` (`x = false` to `x = true`),
  `RunOKLB.toLC` (empty bodies and `x = false` back), `RunOKLB.wrap`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- **`AgreeL` with bodies**: at a result entry the run made, the program's
block is a fill `A` of the entry's need followed by the block's body `B` in
the run's final state, unproxied. -/
def AgreeLB (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (cond : Map (Nat × List Nat)) (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cond)) ∧
  ∀ e ∈ entries laz, g0.bo ≤ e.1 → ∃ A B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A ++ B.map (renPole (unproxy cond)), Termin.hop (renJmp (unproxy cond) th)⟩ ∧
    FillSem lib O c gul st t ned g1.re e.2.sure A s0 s

/-- The goal's sure registers that the fronts may read: those of `L`'s sure
need when `x`, none otherwise. -/
def gsE (x : Bool) (L : Lazy S) : Need := if x then L.sure.ned else Need.none

/-- **What the ops `F` a run put in front of a goal entry's block do**, with
the goal's sure registers `E`: after any ops `A` that fill the result's need
`L'` at that label, they fill the goal entry's need `L` for the product `v`
from `ned`, the witness `d` holding `w` and `E` holding `v`. -/
def FrontLB (Q : Wit) (E : Need) (lo0 lo : Nat) (L' : Sure S) (F : List Pole) (L : Sure S) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace) (ned : Need)
    (A : List Pole) (s0 s v : Noun) (d : Need) (w : Noun), (∀ r, NMem ned r → lo ≤ r) → Q s v d w →
    FillSem (Map := Map) lib O c gul st t ned lo L' A s0 s →
    FillSem lib O c gul st t (Need.pair (Need.pair ned d) E) lo0 L (A ++ F) (C (C s0 w) v) v

/-- **The forward `sem` of `RunOKLB`** (`SemLC` with `AgreeLB`). -/
def SemLB (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
      L.sure th (Q s) r

/-- **The backward `sem` of `RunOKLB`** (`SemLCB` with `AgreeLB`). -/
def SemLBB (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm
        nex.th L.sure th (Q s) r

/-- **The relation of one run that may call, under `%next L th` for any
lazy need `L`, with bodies at the entries**: `RunOKLC` with `labs` allowing
a body `B` at every result entry, `front` through `FrontLB` (the fronts may
read the goal's sure registers when `x`), and the `sem` clauses assuming
`AgreeLB`. -/
structure RunOKLB (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (x : Bool)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  re : g0.re ≤ g1.re
  bo : g0.bo ≤ g1.bo
  drop : g1.drop = g0.drop
  keep : ∀ o, o < g0.bo → o ∉ (entries L).map Prod.fst → HoonMap.get g1.blocks o = HoonMap.get g0.blocks o
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 (CGoal.next L.sure th) nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r →
    (∃ e0 ∈ entries L, NMem e0.2.sure.ned r) ∨ NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  labs : ∀ e ∈ entries nex.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < g1.bo)) ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  dreg : ∀ s v d w r, Q s v d w → NMem d r → g0.re ≤ r ∧ r < g1.re
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f (CGoal.next L.sure th) s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  front : ∀ e ∈ entries L, ∃ F : List Pole,
    (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
    ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ((∃ L', (e.1, L') ∈ entries nex.laz ∧
        FrontLB (Map := Map) Q (gsE x L) g0.re g1.re L'.sure (F.map (renPole (unproxy cf))) e.2.sure) ∨
     (e.1 ∉ (entries nex.laz).map Prod.fst ∧
        FrontLB (Map := Map) Q (gsE x L) g0.re g1.re Sure.bunt (F.map (renPole (unproxy cf))) e.2.sure))
  sem : SemLB lib P f L th Q g0 g1 nex
  semB : SemLBB lib P f L th Q g0 g1 nex

/-! ## Bodies and the old relation -/

section Agree
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
  {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}

/-- **`AgreeLB` gives `AgreeL` where the made entries' blocks are empty.** -/
theorem AgreeLB.toL (h : AgreeLB lib O c gul st t cond ned g0 g1 laz s0 s)
    (hl : ∀ e ∈ entries laz, g0.bo ≤ e.1 → ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩) :
    AgreeL lib O c gul st t cond ned g0 g1 laz s0 s := by
  refine ⟨h.1, fun e he l => ?_⟩
  obtain ⟨A, B, th, h1, h2, h3⟩ := h.2 e he l
  obtain ⟨th', h1'⟩ := hl e he l
  rw [h1'] at h1
  simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact ⟨A, th', h1', by simpa using h2, h3⟩

/-- **`AgreeL` is `AgreeLB` with empty bodies.** -/
theorem AgreeL.toB (h : AgreeL lib O c gul st t cond ned g0 g1 laz s0 s) :
    AgreeLB lib O c gul st t cond ned g0 g1 laz s0 s := by
  refine ⟨h.1, fun e he l => ?_⟩
  obtain ⟨A, th, h1, h2, h3⟩ := h.2 e he l
  exact ⟨A, [], th, h1, by simpa using h2, h3⟩

end Agree

/-- **A front of `RunOKLC` is a front of `RunOKLB`** for any `E` below
`lo0`. -/
theorem frontLB_of_frontLC {Q : Wit} {E : Need} {lo0 lo : Nat} {L' : Sure S} {F : List Pole} {L : Sure S}
    (hE : ∀ r, NMem E r → r < lo0) (h : FrontLC (Map := Map) Q lo0 lo L' F L) :
    FrontLB (Map := Map) Q E lo0 lo L' F L := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hf
  exact (h lib σ O c gul st t ned A s0 s v d w hn hq hf).pair E hE v

/-- **A front with no goal register read is a front with any.** -/
theorem FrontLB.up {Q : Wit} {E : Need} {lo0 lo : Nat} {L' : Sure S} {F : List Pole} {L : Sure S}
    (hE : ∀ r, NMem E r → r < lo0) (h : FrontLB (Map := Map) Q Need.none lo0 lo L' F L) :
    FrontLB (Map := Map) Q E lo0 lo L' F L := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hf R hR
  have H := h lib σ O c gul st t ned A s0 s v d w hn hq hf R ⟨hR.1, trivial⟩
  refine ⟨fun fit => ?_, H.2⟩
  obtain ⟨R', r, hh, k⟩ := H.1 fit
  refine ⟨R', r, hh, fun z hz hnz => k z ?_ hnz⟩
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inl hz)
  · exact Or.inr (hE z hz)
  · exact Or.inr hz

/-- **A front with `E = none` is a front of `RunOKLC`.** -/
theorem FrontLB.toLC {Q : Wit} {lo0 lo : Nat} {L' : Sure S} {F : List Pole} {L : Sure S}
    (h : FrontLB (Map := Map) Q Need.none lo0 lo L' F L) : FrontLC (Map := Map) Q lo0 lo L' F L := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hf R hR
  have H := h lib σ O c gul st t ned A s0 s v d w hn hq hf R ⟨hR, trivial⟩
  refine ⟨fun fit => ?_, H.2⟩
  obtain ⟨R', r, hh, k⟩ := H.1 fit
  refine ⟨R', r, hh, fun z hz hnz => k z ?_ hnz⟩
  rcases hz with hz | hz
  · exact Or.inl (Or.inl hz)
  · exact Or.inr hz

theorem gsE_false (L : Lazy S) : gsE false L = Need.none := rfl

theorem gsE_true (L : Lazy S) : gsE true L = L.sure.ned := rfl

/-- The goal's sure registers read by the fronts lie below the run's start
when the goal's do. -/
theorem gsE_lt {x : Bool} {L : Lazy S} {lo : Nat} (h : ∀ r, NMem L.sure.ned r → r < lo) :
    ∀ r, NMem (gsE x L) r → r < lo := by
  cases x
  · intro r hr; exact hr.elim
  · exact h

/-! ## The lift from `RunOKLC` -/

/-- **`RunOKLC` gives `RunOKLB` with `x = false`**: the made entries'
blocks are empty, so `AgreeLB` gives `AgreeL`, and a front of `RunOKLC` is
one of `RunOKLB` with no goal register. -/
theorem RunOKLC.toB {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKLC (Map := Map) lib P f L th Q g0 g1 nex) :
    RunOKLB (Map := Map) lib P f L th Q false g0 g1 nex := by
  have hl : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 → ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ :=
    fun e he _ => (R.labs e he).2
  refine ⟨R.re, R.bo, R.drop, R.keep, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs,
    fun e he => ⟨(R.labs e he).1.imp_right (fun h => ⟨h.1, by have := R.hi; omega⟩), [], (R.labs e he).2⟩, R.nodup,
    R.dreg, R.nec, R.ncond, R.econd,
    fun e he => ?_, ?_, ?_⟩
  · obtain ⟨F, hb, hf⟩ := R.front e he
    exact ⟨F, hb, fun cf hcf => (hf cf hcf).imp
      (fun ⟨L', hm, fl⟩ => ⟨L', hm, frontLB_of_frontLC (fun r hr => hr.elim) fl⟩)
      (fun ⟨hn, fl⟩ => ⟨hn, frontLB_of_frontLC (fun r hr => hr.elim) fl⟩)⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm (fun st' => (ag st').toL hl) hned
      regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs (fun st' => (ag st').toL hl) hned regs
      hh hn res hres

/-- **The weakening of `x`**, when the goal's sure registers lie below the
run's start. -/
theorem RunOKLB.up {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKLB (Map := Map) lib P f L th Q false g0 g1 nex)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re) (x : Bool) : RunOKLB (Map := Map) lib P f L th Q x g0 g1 nex := by
  refine ⟨R.re, R.bo, R.drop, R.keep, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    R.dreg, R.nec, R.ncond, R.econd, fun e he => ?_, R.sem, R.semB⟩
  obtain ⟨F, hb, hf⟩ := R.front e he
  exact ⟨F, hb, fun cf hcf => (hf cf hcf).imp
    (fun ⟨L', hm, fl⟩ => ⟨L', hm, fl.up (gsE_lt hL)⟩) (fun ⟨hn, fl⟩ => ⟨hn, fl.up (gsE_lt hL)⟩)⟩

/-- **`RunOKLB` with `x = false` and empty bodies is `RunOKLC`.** -/
theorem RunOKLB.toLC {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKLB (Map := Map) lib P f L th Q false g0 g1 nex)
    (he : ∀ e ∈ entries nex.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < nex.th.there)) ∧
      ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩) :
    RunOKLC (Map := Map) lib P f L th Q g0 g1 nex := by
  have hl : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 → ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ :=
    fun e h _ => (he e h).2
  refine ⟨R.re, R.bo, R.drop, R.keep, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs,
    he, R.nodup, R.dreg, R.nec, R.ncond, R.econd, fun e h => ?_, ?_, ?_⟩
  · obtain ⟨F, hb, hf⟩ := R.front e h
    exact ⟨F, hb, fun cf hcf => (hf cf hcf).imp
      (fun ⟨L', hm, fl⟩ => ⟨L', hm, FrontLB.toLC fl⟩) (fun ⟨hn, fl⟩ => ⟨hn, FrontLB.toLC fl⟩)⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm (fun st' => (ag st').toB) hned
      regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs (fun st' => (ag st').toB) hned regs
      hh hn res hres

/-- **Through `WrapRel`** (the memo hint, the folded `%6`). -/
theorem RunOKLB.wrap {lib : Lib} {P : Noun → Prop} {f f' : Noun} (W : WrapRel lib P f f') {L : Lazy S} {th : Jmp}
    {Q : Wit} {x : Bool} {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKLB (Map := Map) lib P f L th Q x g0 g1 nex) :
    RunOKLB lib P f' L th Q x g0 g1 nex := by
  refine ⟨R.re, R.bo, R.drop, R.keep, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    R.dreg, fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, R.ncond, R.econd, R.front, ?_, ?_⟩
  · obtain ⟨n', _, hm'⟩ := W.fwd hs hm
    exact (R.nec s hs hf).1 gul n' tm r hm'
  · obtain ⟨r, hm, hb⟩ := (R.nec s hs hf).2 gul tm
    exact ⟨r, W.bwd hs hm, hb⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hle, hm'⟩ := W.fwd hs hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hle) st t tm s0 s r hI htr hs hm' ag hned
      regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact ⟨r, W.bwd hs hm, G⟩

end Comp
end SkaModel
end Formalization
