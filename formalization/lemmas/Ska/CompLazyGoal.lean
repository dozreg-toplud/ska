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

* `FrontL`, `GoalSemD`, `SemL`, `RunOKL`.
* `RunOKL.toNV`, `RunOKNV.toL`: for a goal with no entries, `RunOKL` with
  `D = none` is `RunOKNV`.
* `runOKL_n0`: `[0 axe]` (`+from`, every entry kept at its label).
* `runOKL_n4`: `[4 p]` (`+collapse-lazy-atom`, every entry consumed, with
  `D s = this d`), from `CollRunU`.
* `fillSem_bunt_append`: a fill of the bunt followed by ops that fill from
  `pair ned D`.
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

/-- **The `sem` of `RunOKL`**: `SemNV` with the goal's sure part and `D s`
holding `W s` at `th`. -/
def SemL (lib : Lib) (nm : Nomm) (L : Lazy S) (th : Jmp) (D : Noun → Need) (W : Noun → Noun) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
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
    exact goalSemD_toGoalSem lib O c gul st (R.sem cf hcf c ned σ O st t gul s0 s ag hn regs hh h0)

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
  exact goalSem_toGoalSemD lib O c gul st (R.sem cf hcf c ned σ O st t gul s0 s ag hn regs hh h0)

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
    have Sp := CR.sem cf hcf c ned σ O st t gul s0 s ag inR regs hh hn
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
      have T := CR.semT hfa cf hcf c ned σ O st t gul s0 s ag inR regs hh hn
      rw [ev] at T
      obtain ⟨R, hR, kR, eR⟩ := T.1 ⟨trivial, looks_empty _⟩
      have hR' : SkaModel.read d R = some (A m) := hR
      exact ⟨R, (CR.dhold hfa R m hR').1, hR', fun r hr => kR r (kk r hr), eR⟩

end Comp
end SkaModel
end Formalization
