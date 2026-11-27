import lemmas.Ska.CompCallStep
import lemmas.Ska.CompWhole

/-!
# Direct calls: the map, the checks, the steps

README Gaps 18 (track J, 2026-11-27).  The first file of the direct call
`[2 p q]` whose callee `b` is known (`info = some (b, key)`).

## How the model compiles a direct call

`callL` (`CompCall.lean`), the case `%2` of `runLC`, for `mono` `|`, no memo
key, no ring, `sof` false, `env.need b = some bNed` (the callee's n-ary
need, `+callee-need`): `+need-ord-alloc-regs` of `bNed` (fresh registers
`sub`, the arguments `flattenNeed sub`); under `%done` the block `[jmp b
subV]`, otherwise `+simple-next`, `+kerf` (`out`, `pro`) and the block `[cal
b subV pro]`, `hop out`; then `q` for a need that asks nothing (skipped when
`safeFolFol q`, as for the literal `[1 fol]` the analysis leaves), `+past`
over `p`, `p` for `%next (ofSure sub) callBlock`, `+copy`.  A pure callee
whose product nothing needs is not called.

## The finding: the whole-subject version is not modelled on direct calls

`finishLUC` (the model of `+compile-unary`, what `%full` runs) runs `runLC`,
which has no `mono`.  The Hoon runs `+run` with `mono` `&` there, and the
case `%2` then calls through `+mono-try-call`: the subject of the callee is
taken whole into one register `sub-pes`, tested and split by `%clq`, `%hed`,
`%tal` along `bNed`, then the optimistic `%jmp`/`%cal` on the parts, and the
pessimistic `%jsp`/`%csl` on the whole when a part is missing; under `%next`
the two call blocks hop with an argument to a merge block with a parameter.
`tools/hoon/directdump.hoon` (case `%dt`, `[8 [1 R] [9 2 [0 1]]]`, the
whole-subject version): `0w0 mov v0 v6, hop 8`; `0w8 imm R v5, hop 7`; `0w7
con v5 v6 v2, hop 5`; `0w5 clq v2 4 2`; `0w4 hed v2 v4, tal v2 v3, hop 3`;
`0w3 mov v3 v1, hop 1`; `0w1 jmp R-bell [v1]`; `0w2 jsp R-bell v2`.  The
model gives the two blocks of the n-ary version (`dt_model` below): `0 mov 0
1, hop 1`; `1 jmp R-bell [1]`.  So every theorem about `finishLUC` of a
nomm with a direct call speaks of code the Hoon does not produce; the runs
of `runLC` with a direct call are exact for the n-ary version
(`+compile-scc-in`, `mono` `|`), whose top is `finishLFC`.

## What the interpreter does

`goJ_cal` and `goJ_jmp` (`CompCallSem.lean`): the oracle's `call st b false
vs t gul` on the values of `subV`; `%jsp`/`%csl` call `call st b true [v]`.
The contract (`ContractFwd`, `ContractBwd`) is stated against any oracle
that answers as `+mink` does (`OracleFwd`, `OracleBwd`) where the needs of
the states include `N`; so a compositional theorem needs no hypothesis that
the callee's CODE meets `BellContract` (that is what makes the
interpreter's own oracle meet `OracleFwd`, `Theorems.lean`), only:

* `N b false = some bNed` (`CalleeNeeds`): the values passed are
  `argsFor (ν st) b false` of the callee's subject (`argsFor_of_alloc`);
  for the whole-subject version also `N b true ≠ none` (the call by
  subject, `argsFor _ b true s = some [s]`);
* the facts of `Annot.direct`: the products of `p` fit `b.less`, the
  product of `q` is `b.fol`;
* for the n-ary version, `CalleeNec` below: on a subject that fits `b.less`
  and does not split by `bNed`, `+mink` on `b.fol` crashes at once with the
  trace as it is (the caller's code crashes in `p`'s split, before the
  call).  The Hoon ensures it through `sof` (`+sound`, `+need-soft` against
  `+callee-sure`, `+hinted`), which the model leaves as the parameter
  `env.sof`.  The whole-subject version needs no such fact: its pessimistic
  call takes the whole subject.

## Contents

* `dt_model`: the `#guard` of the finding.
* `dt_run`: the interpreter model runs the model's code of `%dt` against an
  oracle that runs `+mink` on the callee, and agrees with `+mink` on the
  formula on four subjects.
* `callStep_bwd`, `tailStep_bwd`: the call blocks, backward.
* `needOrdAllocRegs_clean`: the registers of a callee's need are `Clean`.
* `fits_of_split`, `split_of_holds`: they hold the callee's subject exactly
  where it splits by the callee's need.
* `runLC_n2_direct`: the run of a direct call, step by step.
* `CalleeNec`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-! ## The finding, checked -/

/-- The nomm of `%dt`, `[8 [1 R] [9 2 [0 1]]]`:
`[7 [[1 R] [0 1]] [7 [0 1] [2 [0 1] [1 R] [R-bell ~]]]]`. -/
def dtNomm : Nomm :=
  Nomm.n7 (Nomm.cons (Nomm.n1 nounR) (Nomm.n0 1)) (Nomm.n7 (Nomm.n0 1) callR)

/-- The formula of `%dt`. -/
def dtFol : Noun :=
  C (A 8) (C (C (A 1) nounR) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

def blocksOf (c : Straight FM) (k : Nat) : List (Nat × Option Blob) :=
  (List.range k).map fun i => (i, c.blocks.f i)

/- `dt_model`: **the model's whole-subject code of `%dt` is the n-ary
call**, two blocks, no `%clq`, no `%jsp` (the Hoon's has eight, header). -/
#guard ((finishLUC (S := LS) envR dtNomm).map fun c => (c.need, c.nargs, blocksOf c 4)) ==
  some (NeedOrd.this, 1, [(0, some ⟨[], [Pole.mov 0 1], Termin.hop (jmp0 1)⟩),
    (1, some ⟨[], [], Termin.jmp bellR [1]⟩), (2, Option.none), (3, Option.none)])

/-! ## The model's code run by the interpreter model -/

/-- A library for formulas without hints and scries. -/
def libT : Lib := ⟨fun _ _ => Option.none, fun _ => Option.none, fun _ _ => Option.none, fun _ => A 0⟩

/-- An oracle that answers a call of `R-bell` by `+mink` on `[R v]` (the
need `[~ this]` passes the sample `v`), and an indirect call by `+mink`. -/
def oracleR : Oracle Unit :=
  ⟨fun st b m vals t gul => if b = bellR ∧ m = false then
      (match vals with
       | [v] => (minkF libT gul 500 t (C nounR v) nounR).map fun r => (r, st)
       | _ => Option.none)
    else Option.none,
   fun st u f gul => (minkF libT gul 500 [] u f).map fun r => (r, st)⟩

/-- The interpreter model on the model's code of `%dt`, against `+mink` on
the formula. -/
def dtRun (s : Noun) : Bool :=
  match (finishLUC (S := LS) envR dtNomm : Option (Straight FM)) with
  | some c => (execEntry libT oracleR () c [s] [] (A 0)).map Prod.fst == minkF libT (A 0) 500 [] s dtFol
  | Option.none => false

#guard dtRun (C (A 1) (C (A 2) (A 3)))
#guard dtRun (A 7)
#guard dtRun (C (C (A 1) (A 2)) (C (A 3) (C (A 4) (A 5))))
#guard dtRun (C (A 0) (A 0))
#guard minkF libT (A 0) 500 [] (C (A 1) (C (A 2) (A 3))) dtFol == some (Tone.zero (A 3))

/-! ## The call blocks, backward -/

variable {Map : Type → Type} [HoonMap Map]

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {gul : Noun}
  {c : Straight Map}

/-- **The tail call, backward**: if the code from the block `[jmp b subV]`
returns, `+mink` on the callee's formula returns a tone that the answer
stands for. -/
theorem tailStep_bwd (hS : OracleSteps Inv ν O) (hB : OracleBwd lib Inv ν O)
    {o : Nat} {b : Bell} {N : Needs} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (halloc : needOrdAllocRegs nd g = some (sub, g'))
    (hb : HoonMap.get c.blocks o = some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {res : Tone × σ}
    (hres : goJ lib O c gul st regs ti (jmp0 o) = some res) :
    ∃ r, Mink lib gul tm s' b.fol r ∧ ReturnsC lib O c gul Inv ν st regs ti (jmp0 o) r := by
  obtain ⟨vs, hvs⟩ := holds_mapM sub regs s' hs
  have hargs : argsFor (ν st) b false s' = some vs := by
    rw [← argsFor_of_alloc (hNle b false nd hN) halloc hs, hvs]
  have J := goJ_jmp (lib := lib) (O := O) (gul := gul) hb st regs ti hvs
  rw [J] at hres
  obtain ⟨ton, st'⟩ := res
  obtain ⟨r, hm, hrel⟩ := hB.call st b false vs ti gul ton st' hI hres s' tm hfit hargs htr
  obtain ⟨hI', hle⟩ := hS.call st b false vs ti gul ton st' hI hres
  exact ⟨r, hm, ton, st', hI', hle, by rw [J, hres], hrel⟩

/-- **The call under `%next` or `%pick`, backward**: if the code from the
block `[cal b subV pro]` returns, the oracle answered with a tone that
stands for a tone of `+mink` on the callee's formula, and the code goes on
at `out` with the product in `pro` or returns that tone. -/
theorem callStep_bwd (hS : OracleSteps Inv ν O) (hB : OracleBwd lib Inv ν O)
    {o out pro : Nat} {b : Bell} {N : Needs} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (halloc : needOrdAllocRegs nd g = some (sub, g'))
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {res : Tone × σ}
    (hres : goJ lib O c gul st regs ti (jmp0 o) = some res) :
    ∃ r ton st', Mink lib gul tm s' b.fol r ∧ Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r ∧
      goJ lib O c gul st regs ti (jmp0 o) =
        (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p regs) ti (jmp0 out)
         | ton => some (ton, st')) := by
  obtain ⟨vs, hvs⟩ := holds_mapM sub regs s' hs
  have hargs : argsFor (ν st) b false s' = some vs := by
    rw [← argsFor_of_alloc (hNle b false nd hN) halloc hs, hvs]
  have J := goJ_cal (lib := lib) (O := O) (gul := gul) hb st regs ti hvs
  rw [J] at hres
  obtain ⟨⟨ton, st'⟩, hc, -⟩ := Option.bind_eq_some_iff.mp hres
  obtain ⟨r, hm, hrel⟩ := hB.call st b false vs ti gul ton st' hI hc s' tm hfit hargs htr
  obtain ⟨hI', hle⟩ := hS.call st b false vs ti gul ton st' hI hc
  refine ⟨r, ton, st', hm, hI', hle, hrel, ?_⟩
  rw [J, hc, Option.bind_some]
  cases ton <;> rfl

end

/-! ## The registers of a callee's need -/

/-- **`+need-ord-alloc-regs` makes a clean need**: it crashes on a cell of
two empty halves. -/
theorem needOrdAllocRegs_clean : ∀ (nd : NeedOrd) (g g' : Gen Map) (sub : Need),
    needOrdAllocRegs nd g = some (sub, g') → Clean sub
  | NeedOrd.none, g, g', sub, h => by
    simp only [needOrdAllocRegs, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | NeedOrd.this, g, g', sub, h => by
    simp only [needOrdAllocRegs, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | NeedOrd.pair p q, g, g', sub, h => by
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    split at h
    · cases h
    · rename_i hne
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hne, needOrdAllocRegs_clean p _ _ _ h1, needOrdAllocRegs_clean q _ _ _ h2⟩
  | NeedOrd.both p q, g, g', sub, h => by
    obtain ⟨r0, g0', h0, h⟩ := bind_some h
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨needOrdAllocRegs_clean p _ _ _ h1, needOrdAllocRegs_clean q _ _ _ h2⟩

/-- **A subject that splits by the callee's need fits the registers
allocated for it**, and conversely (`split_of_holds`): the code's split of
`p`'s product fails exactly where `split` does, where `CalleeNec` applies. -/
theorem fits_of_split : ∀ (nd : NeedOrd) (g g' : Gen Map) (sub : Need), needOrdAllocRegs nd g = some (sub, g') →
    ∀ (s : Noun) (vs : List Noun), SkaModel.split nd s = some vs → Fits sub s
  | NeedOrd.none, g, g', sub, h, s, vs, _ => by
    simp only [needOrdAllocRegs, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | NeedOrd.this, g, g', sub, h, s, vs, _ => by
    simp only [needOrdAllocRegs, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  | NeedOrd.pair p q, g, g', sub, h, s, vs, hs => by
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases s with
      | atom _ => simp [SkaModel.split] at hs
      | cell sh st =>
        simp only [SkaModel.split] at hs
        obtain ⟨a, ha, hs⟩ := Option.bind_eq_some_iff.mp hs
        obtain ⟨b', hb, -⟩ := Option.bind_eq_some_iff.mp hs
        exact ⟨fits_of_split p _ _ _ h1 sh a ha, fits_of_split q _ _ _ h2 st b' hb⟩
  | NeedOrd.both p q, g, g', sub, h, s, vs, hs => by
    obtain ⟨r0, g0', h0, h⟩ := bind_some h
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases s with
      | atom _ => simp [SkaModel.split] at hs
      | cell sh st =>
        simp only [SkaModel.split] at hs
        obtain ⟨a, ha, hs⟩ := Option.bind_eq_some_iff.mp hs
        obtain ⟨b', hb, -⟩ := Option.bind_eq_some_iff.mp hs
        exact ⟨fits_of_split p _ _ _ h1 sh a ha, fits_of_split q _ _ _ h2 st b' hb⟩

/-- **The registers of a callee's need hold its subject only where it
splits**: if they hold `s`, `split` succeeds (`allocSplit`, `holds_mapM`). -/
theorem split_of_holds {nd : NeedOrd} {g g' : Gen Map} {sub : Need} (h : needOrdAllocRegs nd g = some (sub, g'))
    {regs : Map (Option Noun)} {s : Noun} (hs : HoldsN sub regs s) : ∃ vs, SkaModel.split nd s = some vs := by
  obtain ⟨vs, hvs⟩ := holds_mapM sub regs s hs
  exact ⟨vs, by rw [← allocSplit_go nd g g' sub h regs s hs, hvs]⟩

/-! ## The run of a direct call -/

variable {S : Type} [HoonSet S] [HoonMapKeys Map]

/-- **The run of a direct call under a goal other than `%done`, step by
step** (no memo key, no ring, `sof` false, the formula part skipped by
`safeFolFol`, the callee impure): `+need-ord-alloc-regs`, `+simple-next`,
`+kerf`, the block `[cal b subV pro]`, `+past` of the empty need over `p`,
`p` for the callee's need into the call block, `+copy`. -/
theorem runLC_n2_direct {env : CallEnv} {sup : Option Nomm} {p q : Nomm} {b : Bell} {bNed : NeedOrd}
    {goal : CGoalL S} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hpure : env.pure b = false) (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : env.sof (made p sup) p q b bNed = false) (hsafe : safeFolFol q = true)
    (hgoal : goal ≠ CGoalL.done)
    (h : runLC env sup (Nomm.n2 p q (some (b, Option.none))) goal region g0 = some (nex, g')) :
    ∃ (sub : Need) (gA : Gen Map) (nex0 : NextL S) (g1 : Gen Map) (out pro : Nat) (g2 : Gen Map) (o : Nat)
      (g3 : Gen Map) (nexF' : NextL S) (g4 : Gen Map) (nexS : NextL S) (g5 : Gen Map),
      needOrdAllocRegs bNed g0 = some (sub, gA) ∧ simpleNextL goal gA = some (nex0, g1) ∧
      kerf nex0 g1 = some ((out, pro), g2) ∧
      emit ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩ g2 = some (o, g3) ∧
      pastL env.cod ⟨ofSure Sure.bunt, jmp0 o⟩ p region g3 = some (nexF', g4) ∧
      runLC env sup p (CGoalL.next (ofSure ⟨sub, HoonSet.empty⟩) nexF'.th) region g4 = some (nexS, g5) ∧
      copyL nexS nexF'.laz g5 = some (nex, g') := by
  cases goal with
  | done => exact absurd rfl hgoal
  | pick z o' =>
    simp only [runLC, callL, hring, hned, hsof, Bool.false_eq_true, if_false, hsafe, if_true] at h
    obtain ⟨sub, gA, ha, h⟩ := bind_some h
    obtain ⟨o, g3, hc, h⟩ := bind_some h
    obtain ⟨nex0, g1, h1, hc⟩ := bind_some hc
    obtain ⟨⟨out, pro⟩, g2, h2, hc⟩ := bind_some hc
    obtain ⟨nexF0, gX, h0, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨nexF', g4, h4, h⟩ := bind_some h
    obtain ⟨nexS, g5, h5, h⟩ := bind_some h
    exact ⟨sub, gA, nex0, g1, out, pro, g2, o, g3, nexF', g4, nexS, g5, ha, h1, h2, hc, h4, h5, h⟩
  | next laz th =>
    simp only [runLC, callL, hpure, Bool.false_and, Bool.false_eq_true, if_false, hring, hned, hsof, hsafe,
      if_true] at h
    obtain ⟨sub, gA, ha, h⟩ := bind_some h
    obtain ⟨o, g3, hc, h⟩ := bind_some h
    obtain ⟨nex0, g1, h1, hc⟩ := bind_some hc
    obtain ⟨⟨out, pro⟩, g2, h2, hc⟩ := bind_some hc
    obtain ⟨nexF0, gX, h0, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨nexF', g4, h4, h⟩ := bind_some h
    obtain ⟨nexS, g5, h5, h⟩ := bind_some h
    exact ⟨sub, gA, nex0, g1, out, pro, g2, o, g3, nexF', g4, nexS, g5, ha, h1, h2, hc, h4, h5, h⟩

/-! ## What the callee must do where its need is not met -/

/-- **The necessity of the callee's need** (what the n-ary version needs of
the callee, and the Hoon ensures through `sof`): on the subjects of `Y`
(the products of the subject part) that do not split by `bNed`, `+mink` on
the callee's formula crashes at once, with the trace as it is. -/
def CalleeNec (lib : Lib) (Y : Noun → Prop) (b : Bell) (bNed : NeedOrd) : Prop :=
  ∀ y, Y y → SkaModel.split bNed y = Option.none → ∀ gul tm, Mink lib gul tm y b.fol (Tone.two tm)

end Comp
end SkaModel
end Formalization
