import lemmas.Ska.CompConsT

/-!
# One relation for runs that call, under any lazy goal: `RunOKLC`

README Gaps 12.20.  `RunOKL` (`CompLazyGoal.lean`) is the relation of a
call-free run under a goal `%next L th` with entries; `RunOKGC`
(`CompUOKC.lean`) is the relation of a run that may call, under a goal
without entries.  `RunOKLC` is both at once.

## The raw blocks

`tools/hoon/calldump2.hoon` (whole-subject version, subject unknown, before
`+optimize`; `vN` registers, `N` labels), checked against `finishLUC` by the
`#guard`s below.

`[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` (`%cc2`, calls in both halves, subject
`[[4 0 1] 5]`, product `[6 6]`): `0: v0 -> cel, hed -> va, tal -> v9,
hop 9`; `9: nok v9 va -> v7, hop 7` (the head's call, its `+kerf` block a
bare hop under the bond goal, chased); `7: v0 -> cel, hed -> v6, tal -> v5,
hop 5` (the `+past` of the tail's need behind the head's call, filled from
the subject by the final pass); `5: nok v5 v6 -> v4, hop 4` (the tail's
call); `4: mov v4 v3, hop 3`; `3: mov v7 v2, hop 2` (the bond block of the
head's need behind the tail's call: the head's `+kern` put `mov v7 v2`
there, `v7` the head call's product, kept across the tail's call); `2: con
v2 v3 -> v1`; `1: don v1`.  So the head is the indirect call under the bond
goal `mk bunt [] [(3, this v2)]`, its `D` is `this v7` (`+kern`'s register)
and its `W` the call's product, a value of the oracle: `W` is no function of
the subject, and the relation takes a witness relation `Q s v d w` in place
of `D`, `W`.

`[7 [2 [0 3] [0 2]] [4 [0 1]]]` (`%s7a`, product `7`): `0: v0 -> v5, v4,
hop 3`; `3: nok v4 v5 -> v3, hop 2`; `2: mov v3 v2, hop 1`; `1: inc v2 v1,
don v1`.  The call runs under `q`'s result goal `%next (this v2)`, no entries.

`[7 [[0 1] [0 1]] [2 [0 3] [0 2]]]` (`%s7b`, subject `[0 1]`, product
`[0 1]`): `0: mov v0 v4, hop 6`; `6: mov v4 v3, hop 3` (the copy of the
cons's halves, both the subject); `3: nok v3 v4 -> v2, hop 2`; `2`, `1`.

`[[7 [0 3] [4 [0 1]]] [2 [0 3] [0 2]]]` (`%s7c`, product `[6 6]`): `0: v0
-> v6, v9, hop 8`; `8: mov v9 v5, hop 7`; `7: inc v9 v7, hop 5` (the head:
`[4 [0 1]]` consumes the bond entry, `D = this v7`, then `[0 3]` under a
goal without entries); `5: nok v5 v6 -> v4`; `4: mov v4 v3`; `3: mov v7 v2`
(bond); `2: con`; `1: don`.

`[[4 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]` (`%h4c`) and `[[7 [2 [0 3] [0 2]]
[4 [0 1]]] [2 [0 3] [0 2]]]` (`%h7c`, the same nomm after the analysis
folds nothing; identical blocks): `10: nok v11 v12 -> v10`; `9: mov v10 v9`;
`8: inc v9 v7` (the head's increment after its call); `7: v0 -> v6, v5`
(past of the tail behind the head); `5: nok v5 v6 -> v4`; `4`; `3: mov v7
v2` (bond, `v7` written before the tail's call); `2: con`.

`[2 [2 [0 3] [0 2]] [0 2]]` (`%isc`, an indirect call whose subject part
calls, product `7`): `6: nok v6 v7 -> v5`; `5: mov v5 v3`; `4: v0 -> cel,
hed -> v4, hop 3` (past of the formula part `[0 2]` behind the subject part's
call); `3: nok v3 v4 -> v2`.  `[2 [0 3] [2 [0 1] [0 2]]]` (`%ifc`, subject
`[[0 3] [0 1]]`, product `[0 1]`): `0: v0 -> v8, hed -> v7, tal -> v3,
hop 6`; `6: mov v8 v6` (copy); `5: nok v6 v7 -> v5` (the formula part's
call); `4: mov v5 v4`; `3: nok v3 v4 -> v2` (`v3`, the subject part's
register, kept across the formula part's call).

`[[0 1] [[2 [0 3] [0 2]] [0 1]]]` (`%cct`): `0: v0 -> v8, v7, hop 7`;
`7: nok v7 v8 -> v6`; `6: mov v6 v4`; `5: mov v0 v5` (past of the inner
tail behind the call); `4: con v4 v5 -> v3`; `3: mov v0 v2` (bond of the
outer head `[0 1]` behind the inner cons, kept by `[0 1]` and filled by the
final pass); `2: con`; `1: don`.

`[7 [[2 [0 3] [0 2]] [0 1]] [2 [0 3] [0 2]]]` (`%s7d`) and `[7 [[2 [0 3]
[0 2]] [0 3]] [[0 2] [0 3]]]` (`%s7e`): `q` runs under `%done`, then the cons
whose head calls under `q`'s result goal, a `pair` of registers, so
`+split` puts no `con` and the tail's `+past` block (`6: mov v0 v3`,
`5: v0 -> cel, tal -> v3`) fills the tail's half from the subject.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-! ## The raw blocks -/

-- `%cc2`
#guard monoOutC envR (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 11 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 11, Pole.cel 11, Pole.hed 11 13, Pole.mov 13 10, Pole.tal 11 12, Pole.mov 12 9] (hp 9)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.mov 0 15, Pole.cel 15, Pole.hed 15 17, Pole.mov 17 6, Pole.tal 15 16, Pole.mov 16 5] (hp 5)),
    (8, none),
    (9, bk [Pole.nok 9 10 7] (hp 7)),
    (10, none)])

-- `%s7a`
#guard monoOutC envR (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) 5 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6, Pole.cel 6, Pole.hed 6 8, Pole.mov 8 5, Pole.tal 6 7, Pole.mov 7 4] (hp 3)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 3 2] (hp 1)),
    (3, bk [Pole.nok 4 5 3] (hp 2)),
    (4, none)])

-- `%s7b`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 4] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, none),
    (5, none),
    (6, bk [Pole.mov 4 3] (hp 3)),
    (7, none)])

-- `%s7c`
#guard monoOutC envR (Nomm.cons (Nomm.n7 (Nomm.n0 3) (Nomm.n4 (Nomm.n0 1))) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 10, Pole.cel 10, Pole.hed 10 12, Pole.mov 12 6, Pole.tal 10 11, Pole.mov 11 9] (hp 8)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.inc 9 7] (hp 5)),
    (8, bk [Pole.mov 9 5] (hp 7)),
    (9, none)])

-- `%h4c`
#guard monoOutC envR (Nomm.cons (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 12 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13, Pole.cel 13, Pole.hed 13 15, Pole.mov 15 12, Pole.tal 13 14, Pole.mov 14 11] (hp 10)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.mov 0 17, Pole.cel 17, Pole.hed 17 19, Pole.mov 19 6, Pole.tal 17 18, Pole.mov 18 5] (hp 5)),
    (8, bk [Pole.inc 9 7] (hp 7)),
    (9, bk [Pole.mov 10 9] (hp 8)),
    (10, bk [Pole.nok 11 12 10] (hp 9)),
    (11, none)])

-- `%h7c`
#guard monoOutC envR (Nomm.cons (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 12 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13, Pole.cel 13, Pole.hed 13 15, Pole.mov 15 12, Pole.tal 13 14, Pole.mov 14 11] (hp 10)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.mov 0 17, Pole.cel 17, Pole.hed 17 19, Pole.mov 19 6, Pole.tal 17 18, Pole.mov 18 5] (hp 5)),
    (8, bk [Pole.inc 9 7] (hp 7)),
    (9, bk [Pole.mov 10 9] (hp 8)),
    (10, bk [Pole.nok 11 12 10] (hp 9)),
    (11, none)])

-- `%cct`
#guard monoOutC envR (Nomm.cons (Nomm.n0 1) (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))) 9 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 9, Pole.cel 9, Pole.hed 9 11, Pole.mov 11 8, Pole.tal 9 10, Pole.mov 10 7] (hp 7)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 0 2] (hp 2)),
    (4, bk [Pole.con 4 5 3] (hp 3)),
    (5, bk [Pole.mov 0 5] (hp 4)),
    (6, bk [Pole.mov 6 4] (hp 5)),
    (7, bk [Pole.nok 7 8 6] (hp 6)),
    (8, none)])

-- `%isc`
#guard monoOutC envR (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 8, Pole.cel 8, Pole.hed 8 10, Pole.mov 10 7, Pole.tal 8 9, Pole.mov 9 6] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, bk [Pole.mov 0 12, Pole.cel 12, Pole.hed 12 14, Pole.mov 14 4] (hp 3)),
    (5, bk [Pole.mov 5 3] (hp 4)),
    (6, bk [Pole.nok 6 7 5] (hp 5)),
    (7, none)])

-- `%ifc`
#guard monoOutC envR (Nomm.n2 (Nomm.n0 3) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none) Option.none) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 8, Pole.cel 8, Pole.hed 8 10, Pole.mov 10 7, Pole.tal 8 9, Pole.mov 9 3] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, bk [Pole.mov 5 4] (hp 3)),
    (5, bk [Pole.nok 6 7 5] (hp 4)),
    (6, bk [Pole.mov 8 6] (hp 5)),
    (7, none)])

-- `%s7d`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 8, Pole.cel 8, Pole.hed 8 10, Pole.mov 10 7, Pole.tal 8 9, Pole.mov 9 6] (hp 8)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, none),
    (5, none),
    (6, bk [Pole.mov 0 3] (hp 3)),
    (7, bk [Pole.mov 5 4] (hp 6)),
    (8, bk [Pole.nok 6 7 5] (hp 7)),
    (9, none)])

-- `%s7e`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3)) (Nomm.cons (Nomm.n0 2) (Nomm.n0 3))) 9 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 7, Pole.cel 7, Pole.hed 7 9, Pole.mov 9 6, Pole.tal 7 8, Pole.mov 8 5] (hp 7)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, none),
    (4, none),
    (5, bk [Pole.mov 0 11, Pole.cel 11, Pole.tal 11 12, Pole.mov 12 3] (hp 2)),
    (6, bk [Pole.mov 4 2] (hp 5)),
    (7, bk [Pole.nok 5 6 4] (hp 6)),
    (8, none)])


variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- **A witness relation of a run**: for the subject `s` and the product `v`,
the registers `d` that the run computed for the ops it put in front of its
goal's lazy blocks, holding `w`.  For a call-free run `d = D s` and
`w = W s` (`pureWit`); for a call `d` is the register of `+kern` and `w` the
product, which the oracle gives. -/
abbrev Wit := Noun → Noun → Need → Noun → Prop

/-- The witness relation of `RunOKL`. -/
def pureWit (nm : Nomm) (D : Noun → Need) (W : Noun → Noun) : Wit :=
  fun s v d w => pureEval nm s = some v ∧ d = D s ∧ w = W s

/-- The witness relation of a run that put no ops in front of lazy blocks. -/
def noWit : Wit := fun _ _ d _ => d = Need.none

/-- **What the ops `F` a run put in front of a goal entry's block do**
(`FrontL` with a witness relation): after any ops `A` that fill the result's
need `L'` at that label for the subject `s`, they fill the goal entry's need
`L` for the product `v` from `ned` and `d` holding `w`, for every `d`, `w`
that the run's witness relation gives at `s` and `v`. -/
def FrontLC (Q : Wit) (lo0 lo : Nat) (L' : Sure S) (F : List Pole) (L : Sure S) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace) (ned : Need)
    (A : List Pole) (s0 s v : Noun) (d : Need) (w : Noun), (∀ r, NMem ned r → lo ≤ r) → Q s v d w →
    FillSem (Map := Map) lib O c gul st t ned lo L' A s0 s →
    FillSem lib O c gul st t (Need.pair ned d) lo0 L (A ++ F) (C s0 w) v

theorem frontLC_of_frontL {D : Noun → Need} {W : Noun → Noun} {lo0 lo : Nat} {nm : Nomm} {L' : Sure S}
    {F : List Pole} {L : Sure S} (h : FrontL (Map := Map) D W lo0 lo nm L' F L) :
    FrontLC (Map := Map) (pureWit nm D W) lo0 lo L' F L := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hf
  obtain ⟨hv, rfl, rfl⟩ := hq
  exact h lib σ O c gul st t ned A s0 s v hn hv hf

section Exec
variable (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (Inv : σ → Prop) (ν : σ → Needs)

/-- **`GoalSemCM` of `%next sur th` with a witness at `th`**: a product that
fits goes on to `th` at a state where `Inv` holds and whose needs include
those of `st`, with registers where `sur` holds it and some `d` holds `w`,
`Q p d w`, and the registers of `K` kept. -/
def GoalSemCMD (K : Nat → Prop) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (je : Jmp) (sur : Sure S)
    (th : Jmp) (Q : Noun → Need → Noun → Prop) : Tone → Prop
  | Tone.zero p =>
      (FitsS sur p → ∃ st' regs' d w, Inv st' ∧ ν st ≤ ν st' ∧ Q p d w ∧ HoldsN sur.ned regs' p ∧
        HoldsN d regs' w ∧ (∀ x, K x → SkaModel.read x regs' = SkaModel.read x regs) ∧
        goJ lib O c gul st regs t je = goJ lib O c gul st' regs' t th) ∧
      (¬ FitsS sur p → ReturnsC lib O c gul Inv ν st regs t je (Tone.two tm))
  | r => ReturnsC lib O c gul Inv ν st regs t je r

variable {lib O c gul Inv ν}

theorem goalSemCMD_toCM {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} :
    ∀ {r : Tone}, GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) r
  | Tone.zero _, h => ⟨fun f => by
      obtain ⟨st', R, d, w, hI, hle, _, h1, _, h3, h4⟩ := h.1 f
      exact ⟨st', R, hI, hle, h1, h3, h4⟩, h.2⟩
  | Tone.one _, h => h
  | Tone.two _, h => h

theorem goalSemCM_toCMD {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} (hQ : ∀ p, ∃ w, Q p Need.none w) :
    ∀ {r : Tone}, GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) r →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r
  | Tone.zero p, h => ⟨fun f => by
      obtain ⟨st', R, hI, hle, h1, h3, h4⟩ := h.1 f
      obtain ⟨w, hw⟩ := hQ p
      exact ⟨st', R, Need.none, w, hI, hle, hw, h1, trivial, h3, h4⟩, h.2⟩
  | Tone.one _, h => h
  | Tone.two _, h => h

/-- **A pure part's `GoalSemD` lifts to `GoalSemCMD`** at `+mink`'s tone
`toneOf tm v`, at the same state. -/
theorem goalSemCMD_of_goalSemD {K : Nat → Prop} {st : σ} (hI : Inv st) {regs : Map (Option Noun)}
    {ti tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) ti tm) {je : Jmp} {sur : Sure S} {th : Jmp} {D : Need}
    {w : Noun} {Q : Noun → Need → Noun → Prop} :
    ∀ {v : Option Noun}, (∀ p, v = some p → Q p D w) → GoalSemD lib O c gul st K regs ti je sur th D w v →
      GoalSemCMD lib O c gul Inv ν K st regs ti tm je sur th Q (toneOf tm v)
  | some p, hQ, h => ⟨fun f => by
      obtain ⟨R, h1, h2, h3, h4⟩ := h.1 f
      exact ⟨st, R, D, w, hI, Needs.le_refl _, hQ p rfl, h1, h2, h3, h4⟩,
      fun nf => ⟨Tone.two ti, st, hI, Needs.le_refl _, h.2 nf, ToneRel.two htr⟩⟩
  | none, _, h => ⟨Tone.two ti, st, hI, Needs.le_refl _, h, ToneRel.two htr⟩

/-- **`GoalSemCMD` moves back over a step** of the code. -/
theorem goalSemCMD_step {K : Nat → Prop} {st st' : σ} {regs regs' : Map (Option Noun)} {t tm : Trace}
    {je je' : Jmp} {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} (hν : ν st ≤ ν st')
    (hk : ∀ x, K x → SkaModel.read x regs' = SkaModel.read x regs)
    (e : goJ lib O c gul st regs t je = goJ lib O c gul st' regs' t je') :
    ∀ {r : Tone}, GoalSemCMD lib O c gul Inv ν K st' regs' t tm je' sur th Q r →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r
  | Tone.zero _, H => ⟨fun hf => by
      obtain ⟨st'', R, d, w, hI, hle, hq, h1, h2, h3, h4⟩ := H.1 hf
      exact ⟨st'', R, d, w, hI, Needs.le_trans hν hle, hq, h1, h2, fun x hx => (h3 x hx).trans (hk x hx),
        e.trans h4⟩, fun hf => returnsC_step hν e (H.2 hf)⟩
  | Tone.one _, H => returnsC_step hν e H
  | Tone.two _, H => returnsC_step hν e H

theorem goalSemCMD_ret {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} :
    ∀ {r : Tone}, (∀ p, r ≠ Tone.zero p) → ReturnsC lib O c gul Inv ν st regs t je r →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r
  | Tone.zero p, hn, _ => absurd rfl (hn p)
  | Tone.one _, _, H => H
  | Tone.two _, _, H => H

theorem returnsC_of_goalSemCMD {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} :
    ∀ {r : Tone}, (∀ p, r ≠ Tone.zero p) → GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r →
      ReturnsC lib O c gul Inv ν st regs t je r
  | Tone.zero p, hn, _ => absurd rfl (hn p)
  | Tone.one _, _, H => H
  | Tone.two _, _, H => H

theorem GoalSemCMD.mono {K K' : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q Q' : Noun → Need → Noun → Prop} (hK : ∀ x, K' x → K x)
    (hQ : ∀ p d w, Q p d w → Q' p d w) :
    ∀ {r : Tone}, GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r →
      GoalSemCMD lib O c gul Inv ν K' st regs t tm je sur th Q' r
  | Tone.zero _, H => ⟨fun hf => by
      obtain ⟨st'', R, d, w, hI, hle, hq, h1, h2, h3, h4⟩ := H.1 hf
      exact ⟨st'', R, d, w, hI, hle, hQ _ _ _ hq, h1, h2, fun x hx => h3 x (hK x hx), h4⟩, H.2⟩
  | Tone.one _, H => H
  | Tone.two _, H => H

end Exec

/-- **The forward `sem` of `RunOKLC`**: `SemGC` with `AgreeL` at every
state and `GoalSemCMD` of the goal's sure part at `th` with the run's
witness relation at the subject. -/
def SemLC (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ st' : σ, AgreeL lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
      L.sure th (Q s) r

/-- **The backward `sem` of `RunOKLC`** (`SemGCB` with `AgreeL` and
`GoalSemCMD`). -/
def SemLCB (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ st' : σ, AgreeL lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm
        nex.th L.sure th (Q s) r

/-- **The relation of one run that may call, under `%next L th` for any
lazy need `L`**: the structural fields of `RunOKL` (without `size`, as
`RunOKGC` dropped it) with the entries' registers allowed to be the goal's
(as in `RunOKGC`), `dreg` and `front` for the witness relation `Q`, the
semantic `nec` of `RunOKGC`, and both `sem` clauses with `AgreeL` and
`GoalSemCMD`.  `RunOKL.toLC`, `RunOKGC.toLC` and `RunOKLC.toGC` are the
specializations. -/
structure RunOKLC (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop where
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
  labs : ∀ e ∈ entries nex.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < nex.th.there)) ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  dreg : ∀ s v d w r, Q s v d w → NMem d r → g0.re ≤ r ∧ r < g1.re
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f (CGoal.next L.sure th) s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  front : ∀ e ∈ entries L, ∃ F : List Pole,
    (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
    ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ((∃ L', (e.1, L') ∈ entries nex.laz ∧
        FrontLC (Map := Map) Q g0.re g1.re L'.sure (F.map (renPole (unproxy cf))) e.2.sure) ∨
     (e.1 ∉ (entries nex.laz).map Prod.fst ∧
        FrontLC (Map := Map) Q g0.re g1.re Sure.bunt (F.map (renPole (unproxy cf))) e.2.sure))
  sem : SemLC lib P f L th Q g0 g1 nex
  semB : SemLCB lib P f L th Q g0 g1 nex

/-! ## The specializations -/

/-- **A call-free run**: `RunOKL` with `+mink` on `f` the pure value gives
`RunOKLC` with the witness relation `pureWit` (the state stays). -/
theorem RunOKL.toLC {lib : Lib} {P : Noun → Prop} {f : Noun} {nm : Nomm} (M : MinkEq lib P f nm) {L : Lazy S}
    {th : Jmp} {D : Noun → Need} {W : Noun → Noun} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKL (Map := Map) lib nm L th D W g0 g1 nex) : RunOKLC lib P f L th (pureWit nm D W) g0 g1 nex := by
  refine ⟨R.re, R.bo, R.drop, R.keep, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ((R.eregs e he).2 r hr).imp_right Or.inr⟩, R.labs, R.nodup,
    fun s v d w r hq hr => ?_, fun s hs hf => necC_of_pure M hs (R.nec s hf), R.ncond, R.econd,
    fun e he => ?_, ?_, ?_⟩
  · obtain ⟨_, rfl, _⟩ := hq
    exact R.dreg s r hr
  · obtain ⟨F, hb, hf⟩ := R.front e he
    exact ⟨F, hb, fun cf hcf => (hf cf hcf).imp (fun ⟨L', hm, fl⟩ => ⟨L', hm, frontLC_of_frontL fl⟩)
      (fun ⟨hn, fl⟩ => ⟨hn, frontLC_of_frontL fl⟩)⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    rw [(M s hs gul tm r).mp ⟨n, hm⟩]
    exact goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩)
      (R.sem cf hcf c ned σ O st t gul s0 s (ag st) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact ⟨_, (M s hs gul tm _).mpr rfl, goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩)
      (R.sem cf hcf c ned σ O st t gul s0 s (ag st) hned regs hh hn)⟩

/-- **A goal without entries**: `RunOKGC` under `%next sur th` gives
`RunOKLC` under `ofSure sur` with the witness relation `noWit`. -/
theorem RunOKGC.toLC {lib : Lib} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKGC (Map := Map) lib P f (CGoal.next sur th) g0 g1 nex) :
    RunOKLC lib P f (ofSure sur) th noWit g0 g1 nex := by
  have e0 : entries (ofSure sur) = [] := entries_ofSure sur
  refine ⟨R.ext.1, R.ext.2.1, R.ext.2.2.1, fun o ho _ => R.ext.2.2.2 o ho, R.grow, R.cfr, R.lo, R.hi, R.ent,
    R.regs, R.dist, fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ⟨Or.inr ⟨(R.labs e he).1, (R.labs e he).2.1⟩, (R.labs e he).2.2⟩, R.nodup,
    fun s v d w r hq hr => ?_, R.nec, R.ncond, R.econd, fun e he => absurd he (by rw [e0]; simp), ?_, ?_⟩
  · obtain ⟨h1 | h1, h2⟩ := (R.eregs e he).2 r hr
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · simp only [noWit] at hq; subst hq; exact hr.elim
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact goalSemCM_toCMD (fun _ => ⟨A 0, rfl⟩) (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs
      hm (fun st' => (ag st').toU fun e he => (R.labs e he).1) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (fun st' => (ag st').toU fun e he => (R.labs e he).1) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_toCMD (fun _ => ⟨A 0, rfl⟩) G⟩

/-- **A goal without entries, back**: `RunOKLC` under `ofSure sur` gives
`RunOKGC` under `%next sur th` when the registers of `sur` were allocated
before the run. -/
theorem RunOKLC.toGC {lib : Lib} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th : Jmp} {Q : Wit}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKLC (Map := Map) lib P f (ofSure sur) th Q g0 g1 nex)
    (hlt : ∀ r, NMem sur.ned r → r < g0.re) : RunOKGC lib P f (CGoal.next sur th) g0 g1 nex := by
  have e0 : entries (ofSure sur) = [] := entries_ofSure sur
  refine ⟨⟨R.re, R.bo, R.drop, fun o ho => R.keep o ho (by rw [e0]; simp)⟩, R.grow, R.cfr, R.lo, R.hi, R.ent,
    R.regs, R.dist, fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩, fun e he => ?_, R.nodup, R.nec, R.ncond,
    R.econd, ?_, ?_⟩
  · rcases (R.eregs e he).2 r hr with ⟨e0', h0, _⟩ | h | h
    · rw [e0] at h0; cases h0
    · have := hlt r h; have := R.re; exact ⟨Or.inl h, by omega⟩
    · exact ⟨Or.inr h.1, h.2⟩
  · obtain ⟨h1 | h1, th', hb⟩ := R.labs e he
    · rw [e0] at h1; cases h1
    · exact ⟨h1.1, h1.2, th', hb⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact goalSemCMD_toCM (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm
      (fun st' => (ag st').toL) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (fun st' => (ag st').toL) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCMD_toCM G⟩

end Comp
end SkaModel
end Formalization
