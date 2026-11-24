import lemmas.Ska.CompCollapseRun
import lemmas.Ska.CompFragU
import lemmas.Ska.CompConsCall

/-!
# One run relation for a goal `%next L th` with entries: `RunOKL`

README Gaps 12.18.  Every run relation of the `+comp` proof before this file
speaks of goals `%next (ofSure sur) th`.  The compiler runs parts under goals
whose lazy need has entries: behind a call (`+past` parks the head's need in
a bond), in `[7 p q]` with a `%6` in `q` (the result need of `q` has forks),
and a `%6` under such a goal.  `RunOKL` is the relation for a call-free part
under `%next L th` for any `L`.

## The raw blocks

`tools/hoon/lazydump.hoon` (whole-subject version, subject unknown, before
`+optimize`; registers `0vN` are written `vN`, labels `0wN` as `N`).

`[[0 1] [2 [0 3] [0 2]]]` (`%bnd`): `0: v0 -> cel, hed v9 -> v6, tal v8 -> v5,
hop 5`; `5: nok v5 v6 -> v4, hop 4`; `4: mov v4 v3, hop 3`; `3: mov v0 v2, hop 2`;
`2: con v2 v3 -> v1, hop 1`; `1: don v1`.  Block `2` is the block of
`+split`, `3` the block of `+past` (the bond: the head's need `this v2`
parked behind the call), `4` the copy of the call's product into the tail
register, `5` the call.  The head `[0 1]` puts nothing at `3` (it keeps the
bond entry at the same label, `+from` at axis `1`), and the final pass fills
`v2` there from the input register `v0`.

`[[0 2] [2 [0 3] [0 2]]]` (`%bnh`): the same, with `3: mov v0 vb, cel vb,
hed vb vd, mov vd v2, hop 2`: the head `[0 2]` keeps the bond entry with the
need moved under axis `2` (`fromL 2`), which the final pass fills from `v0`.

`[[4 [0 3]] [2 [0 3] [0 2]]]` (`%bnc`, a head that computes under a bond
goal): `0: v0 -> cel, hed -> v6, tal -> v9, hop 8`; `8: mov v9 v5, hop 7`
(the copy of the two parts' needs at the subject's tail); `7: inc v9 -> v7,
hop 5` (the head's code); `5: nok v5 v6 -> v4, hop 4` (the call);
`4: mov v4 v3, hop 3`; `3: mov v7 v2, hop 2` (the bond block: the head's
`+collapse-lazy-atom` put `mov p v2` with `p` a proxy for `v7`, which
`+to-straight` unproxied); `2: con`; `1: don`.  So the bond block reads `v7`,
which the head's code wrote BEFORE the call: the lazy block of an entry
reads a register the run computed, and every code between the run's end and
the lazy block (here the call) must keep it.  `v7` is allocated in the
head's run, after the tail's (the tail is compiled first), so it lies above
the tail's end.

`[7 [0 3] [6 [0 1] [0 2] [1 0]]]` (`%fk1`, forks): `5: brn v3 -> 3 | 4` (the
test `[0 1]` for `%pick`, its need `this v3`), `3` and `4` the branch blocks
of the `%6` (the fork entries of `q`'s result need) with the fill ops of the
final pass (`3: v0 -> tal -> cel, hed -> v2, hop 2`: the yes branch `[0 2]`
of the subject's tail), `2: don v2`, `1: imm 0 v1, don v1`; `0: v0 -> tal ->
v3, hop 5`.  `p = [0 3]` keeps the two fork entries at their labels with the
needs moved under axis `3`, and puts nothing there.

`[7 [[0 2] [0 3]] [6 [0 2] [0 3] [1 0]]]` (`%fk2`, a cons at fork entries):
`3: v0 -> cel, tal va -> v2, hop 2`.  The entry `3` of `q`'s result asks
`pair none (this v2)`, a `pair`, so `+split` puts no `con` at `3`, the
tail `[0 3]` keeps the half `this v2` at label `3`, the head drops its empty
half, and the final pass fills `v2` from `v0` at `3`.  (A `both` or `this`
entry need would make `+split` put `con h t r` at `3`, and the halves would
stay at `3` behind it: a result entry whose block is not empty.)

`[7 [6 [0 2] [1 0] [1 1]] [6 [0 1] [1 5] [1 6]]]` (`%fk3`, a `%6` under a
goal with forks): the forks of `q`'s result ask nothing (`[1 5]`, `[1 6]`
under `%done`), so the outer `%6` takes `sixNextSimple` (`+fork-sure` of
`this v3`): `7: hop 9 (v4)`, `8: hop 9 (v5)`, `9 (par v3): hop 5`,
`10: imm 1 v5, hop 9 (v5)`, `11: imm 0 v4, hop 9 (v4)`, `14: brn v6 -> 11 | 10`,
`0: v0 -> hed -> v6, hop 14`.  The fork path (`sixNextFork`) needs fork
entries that ask something.

## The relation

A run under `%next L th` returns, besides the sure part of `L` at `th`, a
need `D s` holding a noun `W s` (both functions of the subject `s` of the
run): the registers the run computed and that the ops it put in front of the
goal's lazy blocks read.  For `[4 p]` under a bond goal, `D s = this d` and
`W s` is the product.  Every entry of `L` is served (`front`): the ops `F`
the run put in front of the entry's block, after any ops `A` that fill the
result's entry at that label for the subject (`A = []` when the run consumed
the entry), fill the goal entry's need for the product from the input
registers `ned` holding `s0` AND `D s` holding `W s` (`FrontL`).  The parent
keeps `D s` until the lazy block by passing `pair ned (D s)` as the input
need of the code that runs between (the `sem` of each relation keeps its
input registers).

* `FrontL`, `GoalSemD`, `AgreeL` (`AgreeU` at the result entries the run
  made: those it kept from its goal lie in the parent's blocks), `SemL`,
  `RunOKL`.
* `RunOKL.toNV`, `RunOKNV.toL`: for a goal with no entries, `RunOKL` with
  `D = none` is `RunOKNV`.
* `runOKL_n0`: `[0 axe]` (`+from`, every entry kept at its label).
* `runOKL_n4`: `[4 p]` (`+collapse-lazy-atom`, every entry consumed, with
  `D s = this d`), from `CollRunU`; `runOKL_n4_none` from the run of
  `collRun_n4` under a goal whose sure part asks nothing (a bond goal).
* `runOKL_seven`: `[7 p q]` composes (`sevenD`, `sevenW`, `frontL_seven`).
* `fillSem_bunt_append`, `FillSem.assoc`, `FillSem.bunt_subj`.

Where it stops.  (1) `labs` asks every result entry's block to be empty,
which `+split` breaks: a cons at a goal entry whose need is `this r` or
`both r ..` puts `con h t r` at the entry's block and keeps both halves at
that label, so the block of a result entry holds the `con` (and the ops of
the other half).  The weakest change: `AgreeL` with a body, `g1` holding
`⟨[], B, hop th⟩` at the entry and the program `A ++ B` unproxied, `A`
filling the entry, and `front` about the prefix the run put before the
parent's body, as now.  (2) The `sem` is strict (input registers from the
run's end on), as `SemNV` is, so `D s` must be allocated in the run: when
the goal's sure part is one register `d` that `+collapse-lazy-atom` reads in
the lazy blocks (`[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]`, `%h` of
`proxy-dump.hoon`), the later code must keep its own result register `d`,
which only the relaxed form (`InR`, `KeepI`, as in `CollRunU`) says.
(3) Under `+fork` (`sixNextFork`) a branch's ops in a kid of a lazy block
read that branch's registers only on its path.  `D` is a function of the
subject so that the `%6` can take the `D s` of the branch its test takes;
that case is not proved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- **What the ops `F` a run put in front of a goal entry's block do**, for
the run's `D` and `W`: after any ops `A` that fill the result's need `L'` at
that label for the subject `s` from the input need `ned` holding `s0`, they
fill the goal entry's need `L` for the product `v` from `ned` and `D s`
holding `W s`. -/
def FrontL (D : Noun → Need) (W : Noun → Noun) (lo0 lo : Nat) (nm : Nomm) (L' : Sure S) (F : List Pole)
    (L : Sure S) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace) (ned : Need)
    (A : List Pole) (s0 s v : Noun), (∀ r, NMem ned r → lo ≤ r) → pureEval nm s = some v →
    FillSem (Map := Map) lib O c gul st t ned lo L' A s0 s →
    FillSem lib O c gul st t (Need.pair ned (D s)) lo0 L (A ++ F) (C s0 (W s)) v

section Exec
variable (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ)

/-- **`GoalSem` of `%next sur th` with the run's `D` holding `w` at `th`.** -/
def GoalSemD (K : Nat → Prop) (regs : Map (Option Noun)) (t : Trace) (je : Jmp) (sur : Sure S) (th : Jmp)
    (D : Need) (w : Noun) : Option Noun → Prop
  | some p =>
      (FitsS sur p → ∃ regs', HoldsN sur.ned regs' p ∧ HoldsN D regs' w ∧
        (∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs) ∧
        goJ lib O c gul st regs t je = goJ lib O c gul st regs' t th) ∧
      (¬ FitsS sur p → goJ lib O c gul st regs t je = some (Tone.two t, st))
  | none => goJ lib O c gul st regs t je = some (Tone.two t, st)

theorem goalSemD_toGoalSem {K : Nat → Prop} {regs : Map (Option Noun)} {t : Trace} {je : Jmp} {sur : Sure S}
    {th : Jmp} {D : Need} {w : Noun} :
    ∀ {v : Option Noun}, GoalSemD lib O c gul st K regs t je sur th D w v →
      GoalSem lib O c gul st K regs t je (CGoal.next sur th) v
  | some _, h => ⟨fun f => by obtain ⟨R, h1, _, h3, h4⟩ := h.1 f; exact ⟨R, h1, h3, h4⟩, h.2⟩
  | none, h => h

theorem goalSem_toGoalSemD {K : Nat → Prop} {regs : Map (Option Noun)} {t : Trace} {je : Jmp} {sur : Sure S}
    {th : Jmp} {w : Noun} :
    ∀ {v : Option Noun}, GoalSem lib O c gul st K regs t je (CGoal.next sur th) v →
      GoalSemD lib O c gul st K regs t je sur th Need.none w v
  | some _, h => ⟨fun f => by obtain ⟨R, h1, h3, h4⟩ := h.1 f; exact ⟨R, h1, trivial, h3, h4⟩, h.2⟩
  | none, h => h

end Exec

/-- **`AgreeU` for the result entries the run made** (labels from `g0.bo`
on): the result entries that the run kept from its goal lie in the parent's
blocks, which the run's code does not reach, and the parent may have put ops
there (`+split`'s `con`, the ops of a later part). -/
def AgreeL (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (cond : Map (Nat × List Nat)) (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cond)) ∧
  ∀ e ∈ entries laz, g0.bo ≤ e.1 → ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A, Termin.hop (renJmp (unproxy cond) th)⟩ ∧
    FillSem lib O c gul st t ned g1.re e.2.sure A s0 s

theorem AgreeU.toL {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeU lib O c gul st t cond ned g0 g1 laz s0 s) : AgreeL lib O c gul st t cond ned g0 g1 laz s0 s :=
  ⟨h.1, fun e he _ => h.2 e he⟩

theorem AgreeL.toU {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeL lib O c gul st t cond ned g0 g1 laz s0 s) (hl : ∀ e ∈ entries laz, g0.bo ≤ e.1) :
    AgreeU lib O c gul st t cond ned g0 g1 laz s0 s :=
  ⟨h.1, fun e he => h.2 e he (hl e he)⟩

/-- **The `sem` of `RunOKL`**: `SemNV` with `AgreeL`, the goal's sure part
and `D s` holding `W s` at `th`. -/
def SemL (lib : Lib) (nm : Nomm) (L : Lazy S) (th : Jmp) (D : Noun → Need) (W : Noun → Noun) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeL lib O c gul st t cf ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemD lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem L.sure.ned r) regs t nex.th L.sure th
      (D s) (W s) (pureEval nm s)

/-- **The relation for one call-free run under `%next L th`, for any lazy
need `L`.**  The structural fields of `RunOKE` with `CondFresh` in place of
an unchanged `cond` and every result entry's block empty (`labs`: at a goal
entry's label, which the run left empty, or new); `D` and `W` (`dreg`: the
registers of `D s` are allocated in the run); `front`: every goal entry got
ops `F` in front of its block, which, unproxied by any later `cond`, meet
`FrontL`; `sem`: `SemL`. -/
structure RunOKL (lib : Lib) (nm : Nomm) (L : Lazy S) (th : Jmp) (D : Noun → Need) (W : Noun → Noun)
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
    (∃ e0 ∈ entries L, NMem e0.2.sure.ned r) ∨ (g0.re ≤ r ∧ r < g1.re)
  labs : ∀ e ∈ entries nex.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < nex.th.there)) ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ (entries L).length + 2 * sixCount nm
  dreg : ∀ s r, NMem (D s) r → g0.re ≤ r ∧ r < g1.re
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ ¬ FitsS L.sure p
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  front : ∀ e ∈ entries L, ∃ F : List Pole,
    (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
    ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ((∃ L', (e.1, L') ∈ entries nex.laz ∧
        FrontL (Map := Map) D W g0.re g1.re nm L'.sure (F.map (renPole (unproxy cf))) e.2.sure) ∨
     (e.1 ∉ (entries nex.laz).map Prod.fst ∧
        FrontL (Map := Map) D W g0.re g1.re nm Sure.bunt (F.map (renPole (unproxy cf))) e.2.sure))
  sem : SemL lib nm L th D W g0 g1 nex

/-! ## Goals without entries -/

/-- **`RunOKL` under a goal without entries gives `RunOKNV`** (forget `D`). -/
theorem RunOKL.toNV {lib : Lib} {nm : Nomm} {sur : Sure S} {th : Jmp} {D : Noun → Need} {W : Noun → Noun}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKL (Map := Map) lib nm (ofSure sur) th D W g0 g1 nex) :
    RunOKNV lib nm sur th g0 g1 nex := by
  have e0 : entries (ofSure sur) = [] := entries_ofSure sur
  refine ⟨⟨R.re, R.bo, R.drop, fun o ho => R.keep o ho (by rw [e0]; simp)⟩, R.grow, R.cfr, R.lo, R.hi, R.ent,
    R.regs, R.dist, fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩, fun e he => ?_, R.nodup, ?_, R.nec,
    R.ncond, R.econd, ?_⟩
  · rcases (R.eregs e he).2 r hr with ⟨e0', h0, _⟩ | h
    · rw [e0] at h0; cases h0
    · exact h
  · obtain ⟨h1 | h1, th', hb⟩ := R.labs e he
    · rw [e0] at h1; cases h1
    · exact ⟨h1.1, h1.2, th', hb⟩
  · have := R.size; rw [e0] at this; simpa using this
  · intro cf hcf c ned σ O st t gul s0 s ag hn regs hh h0
    exact goalSemD_toGoalSem lib O c gul st (R.sem cf hcf c ned σ O st t gul s0 s ag.toL hn regs hh h0)

/-- **`RunOKNV` is `RunOKL` under a goal without entries, with `D = none`.** -/
theorem RunOKNV.toL {lib : Lib} {nm : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKNV (Map := Map) lib nm sur th g0 g1 nex) (W : Noun → Noun) :
    RunOKL lib nm (ofSure sur) th (fun _ => Need.none) W g0 g1 nex := by
  have e0 : entries (ofSure sur) = [] := entries_ofSure sur
  refine ⟨R.ext.1, R.ext.2.1, R.ext.2.2.1, fun o ho _ => R.ext.2.2.2 o ho, R.grow, R.cfr, R.lo, R.hi, R.ent,
    R.regs, R.dist, fun e he => ⟨(R.eregs e he).1, fun r hr => Or.inr ((R.eregs e he).2 r hr)⟩,
    fun e he => ⟨Or.inr ⟨(R.labs e he).1, (R.labs e he).2.1⟩, (R.labs e he).2.2⟩, R.nodup,
    by rw [e0]; simpa using R.size, fun _ _ hr => hr.elim, R.nec, R.ncond, R.econd,
    fun e he => (by rw [e0] at he; cases he), ?_⟩
  intro cf hcf c ned σ O st t gul s0 s ag hn regs hh h0
  exact goalSem_toGoalSemD lib O c gul st
    (R.sem cf hcf c ned σ O st t gul s0 s (ag.toU fun e he => (R.labs e he).1) hn regs hh h0)

/-! ## Fills -/

/-- **A fill of the bunt followed by ops that fill from `pair ned D`**: the
bunt's fill keeps `ned` and every register below `lo`, where `D` lies. -/
theorem fillSem_bunt_append {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {ned D : Need} {lo lo0 : Nat} {M : Sure S} {A F : List Pole} {s0 s w v : Noun}
    (hA : FillSem (Map := Map) lib O c gul st t ned lo (Sure.bunt : Sure S) A s0 s)
    (hD : ∀ x, NMem D x → x < lo) (hl : lo0 ≤ lo)
    (hF : FillSem lib O c gul st t (Need.pair ned D) lo0 M F (C s0 w) v) :
    FillSem lib O c gul st t (Need.pair ned D) lo0 M (A ++ F) (C s0 w) v := by
  intro R hR
  have hR0 : HoldsN ned R s0 := hR.1
  obtain ⟨R1, r1, _, k1⟩ := (hA R hR0).1 (fitsS_bunt s)
  have k1' : ∀ x, (NMem ned x ∨ x < lo) → SkaModel.read x R1 = SkaModel.read x R := fun x hx =>
    k1 x hx (fun hm => by simp [Sure.bunt, NMem] at hm)
  have hR1 : HoldsN (Need.pair ned D) R1 (C s0 w) :=
    ⟨HoldsN.agree ned (fun x hx => k1' x (Or.inl hx)) hR.1,
     HoldsN.agree D (fun x hx => k1' x (Or.inr (hD x hx))) hR.2⟩
  refine ⟨fun f => ?_, fun nf => Crashes.append_right r1 ((hF R1 hR1).2 nf)⟩
  obtain ⟨R2, r2, hh, k2⟩ := (hF R1 hR1).1 f
  refine ⟨R2, Runs.append r1 r2, hh, fun x hx hn => (k2 x hx hn).trans (k1' x ?_)⟩
  rcases hx with (hx | hx) | hx
  · exact Or.inl hx
  · exact Or.inr (hD x hx)
  · exact Or.inr (Nat.lt_of_lt_of_le hx hl)

/-! ## `[0 axe]` -/

/-- **`[0 axe]` under `%next L th`** (`+from`, no op): every entry stays at
its label with its need moved under the axis, `D = none`.  The goal
entries' blocks are empty and their registers, like the sure part's, are no
keys of `cond`. -/
theorem runOKL_n0 (lib : Lib) {axe : Nat} {L L' : Lazy S} {th : Jmp} {g : Gen Map}
    (hf : fromL axe L = some L') (h1 : 1 ≤ th.there) (h2 : th.there < g.bo) (hd : Distinct L.sure.ned)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned) (hnd : ((entries L).map Prod.fst).Nodup)
    (hemp : ∀ e ∈ entries L, ∃ th', HoonMap.get g.blocks e.1 = some ⟨[], [], Termin.hop th'⟩)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g.cond r = Option.none) (W : Noun → Noun) :
    RunOKL (Map := Map) lib (Nomm.n0 axe) L th (fun _ => Need.none) W g g ⟨L', th⟩ := by
  have E := runOKE_n0 (Map := Map) lib hf h1 h2 hd hed hnd
  have EF := fromL_ent axe _ _ hf
  have hs := fromL_sure hf
  obtain ⟨_, hhold, _, _⟩ := fromSure_spec (Map := Map) hs
  refine ⟨E.re, E.bo, E.drop, E.keep, E.grow, CondFresh.refl g, E.lo, E.hi, Or.inr rfl, E.regs, E.dist,
    E.eregs, fun e he => ?_, E.nodup, E.size, fun _ _ hr => hr.elim, E.nec, fun r hr => ?_, fun e he r hr => ?_,
    fun e he => ?_, ?_⟩
  · rcases E.labs e he with h | h
    · obtain ⟨e0, he0, h0⟩ := List.mem_map.mp h
      obtain ⟨th', hb⟩ := hemp e0 he0
      exact ⟨Or.inl h, th', by rw [← h0]; exact hb⟩
    · have a : g.bo ≤ e.1 := h.1
      have b : e.1 < th.there := h.2.1
      omega
  · rcases E.regs r hr with h | h
    · exact hnc r h
    · omega
  · rcases (E.eregs e he).2 r hr with ⟨e0, he0, h⟩ | h
    · exact hec e0 he0 r h
    · omega
  · obtain ⟨l', hl', hm'⟩ := EF.mem_left he
    refine ⟨[], fun B fin hb => by simpa using hb, fun cf _ => Or.inl ⟨l', hm', ?_⟩⟩
    intro lib σ O c gul st t ned A s0 s v _ hev hfill
    simp only [pureEval] at hev
    simp only [List.map_nil, List.append_nil]
    exact (fillSem_from (fromL_sure hl') hev hfill).pair Need.none (fun _ h => h.elim) (W s)
  · intro cf _ c ned σ O st t gul s0 s _ _ regs hh _
    obtain ⟨s', hs1, hh'⟩ := hhold regs s hh
    show GoalSemD lib O c gul st _ regs t th L.sure th Need.none (W s) (pureEval (Nomm.n0 axe) s)
    simp only [pureEval, hs1]
    exact ⟨fun _ => ⟨regs, hh'.1, trivial, fun _ _ => rfl, rfl⟩, fun nf => absurd (fitsS_of_holdsS hh') nf⟩

/-! ## `[4 p]` -/

/-- **`[4 p]` under `%next L th` from `CollRunU`**, when the register `d`
the increment writes is allocated in the run (the goal's sure part is not
one register, as under a bond goal, whose sure part is the bunt): every
entry is consumed by ops that read `d`, so `D s = this d` and `W s` is the
product.  The goal entries' registers are allocated before the run and no
keys of `cond`. -/
theorem runOKL_n4 {lib : Lib} {p : Nomm} {L : Lazy S} {th : Jmp} {d : Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (CR : CollRunU (Map := Map) lib (Nomm.n4 p) L th d g0 g1 nex) (hdf : g0.re ≤ d)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hec : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) :
    RunOKL lib (Nomm.n4 p) L th (fun _ => Need.this d) (fun s => (pureEval (Nomm.n4 p) s).getD (A 0)) g0 g1
      nex := by
  have Cre := CR.re
  have Cdl := CR.dlt
  refine ⟨CR.re, CR.bo, CR.drop, CR.keep, CR.grow, CR.pfor.1, CR.lo, CR.hi, Or.inl CR.ent,
    fun r hr => Or.inr (CR.regs r hr), CR.dist, fun e he => ⟨(CR.eregs e he).1, fun r hr => Or.inr ((CR.eregs e he).2 r hr)⟩,
    fun e he => ⟨Or.inr ⟨(CR.labs e he).1, (CR.labs e he).2.1⟩, (CR.labs e he).2.2⟩, CR.nodup,
    by have := CR.size; omega, fun _ r hr => by
      have hr' : r = d := hr
      subst hr'; exact ⟨hdf, CR.dlt⟩,
    fun s hs => Or.inl (CR.nec s hs), CR.ncond, CR.econd, fun e he => ?_, ?_⟩
  · obtain ⟨F, hF, hP⟩ := CR.front e he
    refine ⟨F, hF, fun cf hcf => Or.inr ⟨fun hm => ?_, ?_⟩⟩
    · obtain ⟨e', he', e1⟩ := List.mem_map.mp hm
      have := (CR.labs e' he').1; have := hlab e he; omega
    intro lib σ O c gul st t ned A0 s0 s v _ hev hfill
    obtain ⟨m, rfl⟩ : ∃ m, v = A m := by
      rw [pureEval_n4] at hev
      cases ep : pureEval p s with
      | none => rw [ep] at hev; cases hev
      | some x =>
        rw [ep] at hev
        cases x with
        | atom n => simp [incF] at hev; exact ⟨n + 1, hev.symm⟩
        | cell _ _ => simp [incF] at hev
    simp only [hev, Option.getD_some]
    refine fillSem_bunt_append hfill (fun x hx => by have hx' : x = d := hx; subst hx'; exact CR.dlt) CR.re ?_
    exact collP_fillSem hP ((hcf d Cdl).trans CR.dkey)
      (fun x hx => by
        have hx1 := hec e he x hx
        rw [hcf x (by omega), ProxyFor.get_lt CR.pfor hx1.1]; exact hx1.2)
      (fun k hk => hcf k hk) lib O c gul st t ned g0.re s0 m
  · intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    have inR : ∀ r, NMem ned r → InR (CGoal.next L.sure th) g0 g1 nex.laz.sure.ned r := fun r hr =>
      Or.inl (hned r hr)
    have ag' := ag.toU fun e he => (CR.labs e he).1
    have Sp := CR.sem cf hcf c ned σ O st t gul s0 s ag' inR regs hh hn
    have kk : ∀ r, ((r < g0.re ∨ NMem ned r) ∧ ¬ NMem L.sure.ned r) → KeepI (CGoal.next L.sure th) g0 ned r := by
      rintro r ⟨h | h, hn'⟩
      · exact Or.inl ⟨h, hn'⟩
      · exact Or.inr h
    show GoalSemD lib O c gul st _ regs t nex.th L.sure th (Need.this d) ((pureEval (Nomm.n4 p) s).getD (A 0))
      (pureEval (Nomm.n4 p) s)
    cases ev : pureEval (Nomm.n4 p) s with
    | none => rw [ev] at Sp; exact Sp
    | some v =>
      rw [ev] at Sp
      obtain ⟨m, rfl⟩ : ∃ m, v = A m := by
        rw [pureEval_n4] at ev
        cases ep : pureEval p s with
        | none => rw [ep] at ev; cases ev
        | some x =>
          rw [ep] at ev
          cases x with
          | atom n => simp [incF] at ev; exact ⟨n + 1, ev.symm⟩
          | cell _ _ => simp [incF] at ev
      simp only [Option.getD_some]
      refine ⟨fun fit => ?_, fun nf => Sp.2 nf⟩
      have hfa : ∀ v, FitsS L.sure (A v) := CR.dich.elim id (fun hn' => absurd fit (hn' m))
      have T := CR.semT hfa cf hcf c ned σ O st t gul s0 s ag' inR regs hh hn
      rw [ev] at T
      obtain ⟨R, hR, kR, eR⟩ := T.1 ⟨trivial, looks_empty _⟩
      have hR' : SkaModel.read d R = some (A m) := hR
      exact ⟨R, (CR.dhold hfa R m hR').1, hR', fun r hr => kR r (kk r hr), eR⟩

/-- **`[4 p]` from its run under a goal whose sure part asks nothing** (a
bond goal behind a call: `mk bunt [] [(o, ..)]`): the register the increment
writes is fresh, so `runOKL_n4` applies to the run of `collRun_n4`.  For
example the head `[4 [0 3]]` of `[[4 [0 3]] [2 [0 3] [0 2]]]`, whose bond
block reads `v7` (see the header). -/
theorem runOKL_n4_none (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n4 p) (CGoalL.next L th) region g0 = some (nex, g1))
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hsn : L.sure.ned = Need.none)
    (hcb : CondBelow g0) (hnd : (th.there :: (entries L).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hen : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) :
    ∃ d, RunOKL lib (Nomm.n4 p) L th (fun _ => Need.this d) (fun s => (pureEval (Nomm.n4 p) s).getD (A 0)) g0 g1
      nex := by
  have nn : ∀ x, ¬ NMem L.sure.ned x := fun x hx => by rw [hsn] at hx; exact hx
  obtain ⟨d, CR⟩ := collRun_n4 lib hp sp kp ap h hcount b0 d0 hu hcl0 h1 h2 (fun x hx => absurd hx (nn x))
    (fun x hx => absurd hx (nn x)) hcb hnd hlab (fun e he x hx => (hen e he x hx).1)
  have hdf : g0.re ≤ d := CR.dreg.elim (fun hx => absurd hx (nn d)) id
  exact ⟨d, runOKL_n4 CR hdf (fun e he => (hlab e he).1) hen⟩

/-! ## `[7 p q]`: the relation composes -/

/-- Two members of a list with distinct keys and the same key are equal. -/
theorem mem_key_eq {α β : Type} {l : List (α × β)} (h : (l.map Prod.fst).Nodup) {a b : α × β} (ha : a ∈ l)
    (hb : b ∈ l) (e : a.1 = b.1) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨b, hb', e.symm⟩) h.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (List.mem_map.mpr ⟨a, ha', e⟩) h.1
      · exact ih h.2 ha' hb'

/-- Reassociate the input need of a fill. -/
theorem FillSem.assoc {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {ned D1 D2 : Need} {lo : Nat} {M : Sure S} {A0 : List Pole} {s0 w1 w2 v : Noun}
    (h : FillSem (Map := Map) lib O c gul st t (Need.pair (Need.pair ned D1) D2) lo M A0 (C (C s0 w1) w2) v) :
    FillSem lib O c gul st t (Need.pair ned (Need.pair D1 D2)) lo M A0 (C s0 (C w1 w2)) v := by
  intro R hR
  have hR' : HoldsN ned R s0 ∧ HoldsN D1 R w1 ∧ HoldsN D2 R w2 := hR
  obtain ⟨F1, F2⟩ := h R ⟨⟨hR'.1, hR'.2.1⟩, hR'.2.2⟩
  refine ⟨fun f => ?_, F2⟩
  obtain ⟨R', r, hh, k⟩ := F1 f
  refine ⟨R', r, hh, fun x hx hn => k x ?_ hn⟩
  rcases hx with (hx | hx | hx) | hx
  · exact Or.inl (Or.inl (Or.inl hx))
  · exact Or.inl (Or.inl (Or.inr hx))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

/-- A fill of the bunt does not look at the subject. -/
theorem FillSem.bunt_subj {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {ned : Need} {lo : Nat} {A0 : List Pole} {s0 s s' : Noun}
    (h : FillSem (Map := Map) lib O c gul st t ned lo (Sure.bunt : Sure S) A0 s0 s) :
    FillSem lib O c gul st t ned lo (Sure.bunt : Sure S) A0 s0 s' := fun R hR =>
  ⟨fun _ => by
    obtain ⟨R', r, _, k⟩ := (h R hR).1 (fitsS_bunt s)
    exact ⟨R', r, holdsS_bunt R' s', k⟩, fun nf => absurd (fitsS_bunt s') nf⟩

/-- The `D` and `W` of `[7 p q]`: `p`'s, and `q`'s at `p`'s product. -/
def sevenD (p : Nomm) (Dp Dq : Noun → Need) (s : Noun) : Need :=
  Need.pair (Dp s) (Dq ((pureEval p s).getD (A 0)))

def sevenW (p : Nomm) (Wp Wq : Noun → Noun) (s : Noun) : Noun :=
  C (Wp s) (Wq ((pureEval p s).getD (A 0)))

/-- **The fronts compose**: `p`'s ops in front of `q`'s at an entry that `q`
kept for `p`. -/
theorem frontL_seven {p q : Nomm} {Dp Dq : Noun → Need} {Wp Wq : Noun → Noun} {lo0 lo1 lo2 : Nat}
    {Lp Lq M : Sure S} {Fp Fq : List Pole} (hdp : ∀ s r, NMem (Dp s) r → lo1 ≤ r) (h12 : lo1 ≤ lo2)
    (FP : FrontL (Map := Map) Dp Wp lo1 lo2 p Lp Fp Lq) (FQ : FrontL (Map := Map) Dq Wq lo0 lo1 q Lq Fq M) :
    FrontL (Map := Map) (sevenD p Dp Dq) (sevenW p Wp Wq) lo0 lo2 (Nomm.n7 p q) Lp (Fp ++ Fq) M := by
  intro lib σ O c gul st t ned A0 s0 s v hned hev hfill
  have p7 : pureEval (Nomm.n7 p q) s = (pureEval p s).bind (pureEval q) := rfl
  rw [p7] at hev
  cases ev : pureEval p s with
  | none => rw [ev] at hev; cases hev
  | some vp =>
    rw [ev] at hev
    have h1 := FP lib σ O c gul st t ned A0 s0 s vp hned ev hfill
    have h2 := FQ lib σ O c gul st t (Need.pair ned (Dp s)) (A0 ++ Fp) (C s0 (Wp s)) vp v
      (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => hdp s r h)) hev h1
    simp only [sevenD, sevenW, ev, Option.getD_some, ← List.append_assoc]
    exact h2.assoc

/-- **A front of `q` at an entry that `p` does not see.** -/
theorem frontL_seven_bunt {p q : Nomm} {Dp Dq : Noun → Need} {Wp Wq : Noun → Noun} {lo0 lo1 lo2 : Nat}
    {M : Sure S} {Fq : List Pole} (hdp : ∀ s r, NMem (Dp s) r → lo1 ≤ r ∧ r < lo2) (h12 : lo1 ≤ lo2)
    (FQ : FrontL (Map := Map) Dq Wq lo0 lo1 q Sure.bunt Fq M) :
    FrontL (Map := Map) (sevenD p Dp Dq) (sevenW p Wp Wq) lo0 lo2 (Nomm.n7 p q) Sure.bunt Fq M := by
  intro lib σ O c gul st t ned A0 s0 s v hned hev hfill
  have p7 : pureEval (Nomm.n7 p q) s = (pureEval p s).bind (pureEval q) := rfl
  rw [p7] at hev
  cases ev : pureEval p s with
  | none => rw [ev] at hev; cases hev
  | some vp =>
    rw [ev] at hev
    have h1 : FillSem lib O c gul st t (Need.pair ned (Dp s)) lo1 (Sure.bunt : Sure S) A0 (C s0 (Wp s)) vp :=
      ((hfill.pair (Dp s) (fun r hr => (hdp s r hr).2) (Wp s)).mono h12).bunt_subj
    have h2 := FQ lib σ O c gul st t (Need.pair ned (Dp s)) A0 (C s0 (Wp s)) vp v
      (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => (hdp s r h).1)) hev h1
    simp only [sevenD, sevenW, ev, Option.getD_some]
    exact h2.assoc

/-- **`[7 p q]` under `%next L th`**: `RunOKL` of `q` under the goal and of
`p` under the goal `q`'s run returns give `RunOKL` of the whole, with `p`'s
`D` and `q`'s at `p`'s product.  At run time `p`'s code runs, then `q`'s with
the input need `pair ned (Dp s)`, which keeps `Dp s` for the lazy blocks
that `p` put ops at.  `hle`: `p`'s jump is at or after `q`'s; the goal's
sure part and entries were allocated before the run. -/
theorem runOKL_seven {lib : Lib} {p q : Nomm} {L : Lazy S} {th : Jmp} {Dp Dq : Noun → Need}
    {Wp Wq : Noun → Noun} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKL (Map := Map) lib q L th Dq Wq g0 g1 nx) (Rp : RunOKL (Map := Map) lib p nx.laz nx.th Dp Wp g1 g2 nex)
    (hle : nx.th.there ≤ nex.th.there) (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo) :
    RunOKL lib (Nomm.n7 p q) L th (sevenD p Dp Dq) (sevenW p Wp Wq) g0 g2 nex := by
  have q1 := Rq.re
  have q2 := Rq.bo
  have p1 := Rp.re
  have p2 := Rp.bo
  have qhi := Rq.hi
  have p7 : ∀ s, pureEval (Nomm.n7 p q) s = (pureEval p s).bind (pureEval q) := fun _ => rfl
  -- the labels of `q`'s result
  have qlab : ∀ o, o ∈ (entries nx.laz).map Prod.fst → o ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ o ∧ o < g1.bo) :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Rq.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, by omega⟩
  have plab : ∀ o, o ∈ (entries nex.laz).map Prod.fst → o ∈ (entries nx.laz).map Prod.fst ∨ g1.bo ≤ o :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Rp.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
  have nxL : ∀ r, NMem nx.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases Rq.regs r hr with h | h
    · have := hL r h; omega
    · exact h.2
  refine ⟨by omega, by omega, Rp.drop.trans Rq.drop, fun o ho hn => ?_, Rq.grow.trans Rp.grow, Rq.cfr.trans Rp.cfr,
    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ⟨(Rp.eregs e he).1, fun r hr => ?_⟩, fun e he => ?_,
    Rp.nodup, ?_, fun s r hr => ?_, fun s hs => ?_, Rp.ncond, Rp.econd, fun e he => ?_, ?_⟩
  · -- keep
    have hn' : o ∉ (entries nx.laz).map Prod.fst := fun hm => by
      rcases qlab o hm with h | h
      · exact hn h
      · omega
    exact (Rp.keep o (by omega) hn').trans (Rq.keep o ho hn)
  · -- ent
    rcases Rp.ent with f | e
    · exact Or.inl f
    · have e' : nex.th = nx.th := e
      rw [e']
      rcases Rq.ent with f | e2
      · exact Or.inl (f.growU Rq.hi Rp.grow)
      · exact Or.inr e2
  · -- regs
    rcases Rp.regs r hr with h | h
    · rcases Rq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · -- eregs
    rcases (Rp.eregs e he).2 r hr with ⟨e0, he0, h0⟩ | h
    · rcases (Rq.eregs e0 he0).2 r h0 with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · -- labs
    obtain ⟨h, blk⟩ := Rp.labs e he
    refine ⟨?_, blk⟩
    rcases h with h | h
    · rcases qlab e.1 h with h' | h'
      · exact Or.inl h'
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
        have := (Rq.labs e0 he0).1
        rcases this with h'' | h''
        · exact Or.inl (by rw [← e1]; exact h'')
        · exact Or.inr ⟨h'.1, by rw [← e1]; omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · -- size
    have := Rp.size
    have := Rq.size
    simp only [sixCount]
    omega
  · -- dreg
    rcases hr with h | h
    · have := Rp.dreg s r h; exact ⟨by omega, this.2⟩
    · have := Rq.dreg _ r h; exact ⟨this.1, by omega⟩
  · -- nec
    rcases Rp.nec s hs with h | ⟨vp, hv, nf⟩
    · exact Or.inl (by rw [p7, h]; rfl)
    · rcases Rq.nec vp nf with h' | ⟨w, hw, nf'⟩
      · exact Or.inl (by rw [p7, hv]; exact h')
      · exact Or.inr ⟨w, by rw [p7, hv]; exact hw, nf'⟩
  · -- front
    obtain ⟨Fq, hFq, Sq⟩ := Rq.front e he
    have hdp : ∀ s r, NMem (Dp s) r → g1.re ≤ r ∧ r < g2.re := Rp.dreg
    by_cases hk : e.1 ∈ (entries nx.laz).map Prod.fst
    · obtain ⟨e', he', he1⟩ := List.mem_map.mp hk
      obtain ⟨Fp, hFp, Sp⟩ := Rp.front e' he'
      refine ⟨Fp ++ Fq, fun B fin hb => ?_, fun cf hcf => ?_⟩
      · have h1 := hFq B fin hb
        rw [← he1] at h1
        have h2 := hFp _ fin h1
        rw [he1, ← List.append_assoc] at h2
        exact h2
      · have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
          (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
        obtain ⟨Lq, hLq, FQ⟩ : ∃ L', (e.1, L') ∈ entries nx.laz ∧
            FrontL (Map := Map) Dq Wq g0.re g1.re q L'.sure (Fq.map (renPole (unproxy cf))) e.2.sure :=
          (Sq cf hcf1).elim id (fun h => absurd hk h.1)
        have ee : e' = (e.1, Lq) := mem_key_eq Rq.nodup he' hLq he1
        subst ee
        simp only [List.map_append]
        rcases Sp cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
        · exact Or.inl ⟨L', hL', frontL_seven (fun s r hr => (hdp s r hr).1) p1 FP FQ⟩
        · exact Or.inr ⟨hn2, frontL_seven (fun s r hr => (hdp s r hr).1) p1 FP FQ⟩
    · refine ⟨Fq, fun B fin hb => ?_, fun cf hcf => ?_⟩
      · rw [Rp.keep e.1 (by have := hlab e he; omega) hk]; exact hFq B fin hb
      · have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
          (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
        rcases Sq cf hcf1 with ⟨L', hL', _⟩ | ⟨_, FQ⟩
        · exact absurd (List.mem_map.mpr ⟨_, hL', rfl⟩) hk
        · refine Or.inr ⟨fun hm => ?_, frontL_seven_bunt hdp p1 FQ⟩
          rcases plab e.1 hm with h | h
          · exact hk h
          · have := hlab e he; omega
  · -- sem
    intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    have agP : AgreeL lib O c gul st t cf ned g1 g2 nex.laz s0 s :=
      ⟨fun o l u hnl => ag.1 o (by omega) u hnl, fun e he l => ag.2 e he (by omega)⟩
    have Sp := Rp.sem cf hcf c ned σ O st t gul s0 s agP hned regs hh hn
    show GoalSemD lib O c gul st _ regs t nex.th L.sure th (sevenD p Dp Dq s) (sevenW p Wp Wq s)
      (pureEval (Nomm.n7 p q) s)
    rw [p7]
    simp only [sevenD, sevenW]
    cases ev : pureEval p s with
    | none => rw [ev] at Sp; exact Sp
    | some vp =>
      rw [ev] at Sp
      simp only [Option.bind_some, Option.getD_some]
      by_cases fit : FitsS nx.laz.sure vp
      · obtain ⟨R1, h1, hD1, k1, e1⟩ := Sp.1 fit
        have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
          have := nxL x hm; have := hned x hx; omega⟩) hn
        have agQ : AgreeL lib O c gul st t cf (Need.pair ned (Dp s)) g0 g1 nx.laz (C s0 (Wp s)) vp := by
          refine ⟨fun o l u hnl => ?_, fun e he l => ?_⟩
          · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
              rcases plab o hm with h | h
              · exact hnl h
              · omega
            rw [ag.1 o l (by omega) hn2, Rp.keep o u hnl]
          · obtain ⟨_, th', hb1⟩ := Rq.labs e he
            have hlt : e.1 < g1.bo := by
              rcases (Rq.labs e he).1 with h | h
              · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h; have := hlab e0 he0; omega
              · omega
            obtain ⟨Fp, hFp, Sp'⟩ := Rp.front e he
            have hb2 := hFp [] (Termin.hop th') hb1
            rw [List.append_nil] at hb2
            rcases Sp' cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
            · obtain ⟨A0, th'', hb3, hc3, hf3⟩ := ag.2 (e.1, L') hL' l
              rw [hb2] at hb3
              simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
              obtain ⟨rfl, rfl⟩ := hb3
              refine ⟨A0 ++ ([] : List Pole).map (renPole (unproxy cf)), th', hb1, by simpa using hc3, ?_⟩
              exact (FP lib σ O c gul st t ned A0 s0 s vp hned ev hf3).mono (Nat.le_refl _)
            · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), th', hb1, ?_, ?_⟩
              · rw [ag.1 e.1 l (by omega) hn2, hb2]
                simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, List.nil_append]
              · exact FP lib σ O c gul st t ned [] s0 s vp hned ev fillSem_bunt_nil
        have Sq := Rq.sem cf hcf1 c (Need.pair ned (Dp s)) σ O st t gul (C s0 (Wp s)) vp agQ
          (fun r hr => hr.elim (fun h => by have := hned r h; omega) (fun h => (Rp.dreg s r h).1)) R1
          ⟨h1, fit.2⟩ ⟨hn1, hD1⟩
        cases eq : pureEval q vp with
        | none => rw [eq] at Sq; exact e1.trans Sq
        | some v =>
          rw [eq] at Sq
          refine ⟨fun f => ?_, fun nf => e1.trans (Sq.2 nf)⟩
          obtain ⟨R2, h2, hD2, k2, e2⟩ := Sq.1 f
          refine ⟨R2, h2, ⟨HoldsN.agree (Dp s) (fun x hx => k2 x ⟨Or.inr (Or.inr hx), fun hm => by
            have := hL x hm; have := (Rp.dreg s x hx).1; omega⟩) hD1, hD2⟩, fun r hr => ?_, e1.trans e2⟩
          rw [k2 r ⟨hr.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hr.2⟩]
          refine k1 r ⟨hr.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hm => ?_⟩
          rcases Rq.regs r hm with h | h
          · exact hr.2 h
          · rcases hr.1 with h' | h'
            · omega
            · have := hned r h'; omega
      · rcases Rq.nec vp fit with h | ⟨w, hw, nf⟩
        · rw [h]; exact Sp.2 fit
        · rw [hw]; exact ⟨fun f => absurd f nf, fun _ => Sp.2 fit⟩

end Comp
end SkaModel
end Formalization
