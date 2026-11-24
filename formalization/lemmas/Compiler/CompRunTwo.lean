import lemmas.Compiler.CompRunAll
import lemmas.Ska.CompRunLCEq
import lemmas.Compiler.CompKerfLink
import lemmas.Ska.CompIndirectOut

/-!
# The case `%2` of `+run`: the indirect call

## The Hoon (`desk/lib/nock-compilation.hoon`, lines 3900 to 3924)

The case `[%2 *]` of `+run` first tests `?~  info.nomm` (the `info` of the
nomm `[%2 p q info]` at axis `58` of the `$` arm's subject is at `471`).  On
`~` (the indirect call, the branch linked here), in this order:

1. `=^  nex  gen  simple-next`: the goal itself under `%next laz th`; under
   `%done` a fresh register `r` and a block `[~ ~ %don r]`; under `%pick z
   o` a fresh `r` and `[~ ~ %brn r z o]`; the need is `[[%this r] ~] ~ ~]`.
2. `=^  [out pro]  gen  (kerf nex)`: `+kerf` emits `[~ ~ %hop then.nex]` as
   block `out` and runs `+kern` there on `laz.nex`: a fresh register `pro`
   (the call's product), and the ops of `+kern-need` that take `pro` apart
   into the registers of the need, added to `out`.  Under `%done` and
   `%pick` the need is `[%this r]` and `+kern-need` is one `%mov`.
3. `=^  r-sub  gen  re`, `=^  r-fol  gen  re`: two fresh registers.
4. `=^  o  gen  (emit ~ [%nok r-sub r-fol pro]~ %hop ~ out)`: the call block.
   It is never a tail call (`%nok` and `%hop`, not a jump).
5. `$(nomm q.nomm, goal [%next (lazy-from-need this+r-fol) ~ o])`: the
   formula for the goal "the whole product in `r-fol`, then block `o`".
6. `(past nex-fol p.nomm region)`: `+past` over the subject's nomm `p`.
7. `$(nomm p.nomm, goal [%next (lazy-from-need this+r-sub) then.nex-fol])`:
   the subject for "the whole product in `r-sub`", then the formula's code.
8. `(copy nex-sub laz.nex-fol)`.

The goal of each part: `q` runs for `[%next [[%this r-fol] ~] ~ ~] ~ o]`,
`p` for `[%next [[%this r-sub] ~] ~ ~] then.nex-fol]`; both are fork-free
(`CGoal.toL (CGoal.next (lazyReg r) j)`), whatever the goal of the call.
The goal of the call itself reaches only `+simple-next` and `+kerf`.

The model is `callL` of `Ska/CompCall.lean` with `info = none`, the case
`%2` of `runLC env sup` (`Ska/CompRunLC.lean`); `runL` is `none` on `%2`,
so the link is stated against `runLC` (`CompRunAtR`, `CompRunAtC` below).
The two agree step by step: `simpleNextL`, `kerf`, `re`, `re`, `emit` of
`⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩`, the run of `q` for
`CGoalL.next (ofSure (lazyReg rFol)) (jmp0 o)`, `pastL env.cod`, the run of
`p`, `copyL` (`cr2_model`).  No departure.

What the indirect branch reads of the state that the pure cases never read:
* `soft`, through `+kern` (the test `(~(has by soft.gen) o-laz)`, then
  `+soft-ask`): only at the block `out` it has just emitted, which is no key
  of `soft` when `soft` is empty (`GenRest.NoSoft`, as in `CompRunAt`).
* `code.long-ska` (axis `52` of the context), through `+hinted` in `+past`:
  `+hinted` reads it only at a `%2` with a callee, and the link takes `p`
  pure, where `+hinted` is `|` and `+past` returns its argument.
* `cond`: `+kern` writes it only through `+proxy`, at a lazy block other
  than `out`; a fork-free need has none, so `cond` is unchanged.
* Nothing else: not `mono` nor `sup` (read only by the direct branch),
  not `jets`, `cache`, `calls`, `sofs`, `map-local`, `top`, `scc`.

The direct branch (`info` not `~`: `+callee-need`, `+callee-sure`,
`call.cole` of `jets`, `jets-hot`, `cache` through `+callee-compiled`,
`+sound` of `+made` with `sup`, `+need-soft`, `+soft-new`,
`+mono-try-call` with `mono`, `+soft-bond` reading `soft`) is not linked;
its Nock stays `cr2Dir`, read from the pill.

## Where bonds come from

`+past` parks a need that asks something behind a `%hop` block, as a bond,
when its nomm is hinted, and every nomm with an indirect call is hinted
(`hinted` is `&` on `[%2 p q ~]`).  So a cons, `%5`, `%10` or `%2` whose
part that runs first in Nock order calls returns a lazy need with a bond,
and the head of a cons whose tail calls runs for a goal with a bond.  The
links of `+from`, `+mede`, `+collapse-lazy-atom`, `+split`, `+into`,
`+copy` and `+kern` are on fork-free needs (`[sure ~ ~]`) only, so the
fragment of `CompRunCall.lean` is the one where no bond arises: the parts
that run first are pure (`indOk`).

## What is here

* `CompRunAtR R`: `CompRunAt` against any model `R` of `run`
  (`CompRunAt` is `CompRunAtR runL`, `cra_runL`); `CompRunAtC env`: against
  `runLC env msup` for every `msup` (the Hoon's `sup` noun is quantified as
  before); from `CompRunAt` on a pure nomm (`crc_of_pure`, by `runLC_eq`).
* `CrOut`, `CrRes`: what a run returns (fork-free, its need below the
  counter, made of the goal's registers and fresh ones, distinct, no look
  at `0`), and the copy facts `crf_copy_ok`, `crf_copy_out`.
* The Nock of the case (`tools/gen/runtwo.py`): `cr2_eq`, the dispatch
  `cr_disp_n2`, the test `cr2_ind`.
* `cr2_tail`: from the call block on, and `comp_run_n2`: **the case `%2`
  for an indirect call, on every fork-free goal, `p` pure** (with no `%6`),
  given the link of `q` and its result's shape for the goals of the parts.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## The predicates -/

/-- **`CompRunAt` against a model `R` of `run`**: the `$` arm of `+run` on
the noun of a nomm and a goal is `R`, for every `mono`, `sup` and rest of
the state with an empty `soft`. -/
def CompRunAtR (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (ctx : Noun)
    (n : Nomm) (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  ∀ (x : GenRest) (mono sup : Noun), x.NoSoft →
    nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
      = (R n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

theorem cra_runL {n : Nomm} {goal : CGoalL CSet} {region : List Nat} {g : Gen (TreapMap mugF)} :
    CompRunAtR runL ctx n goal region g ↔ CompRunAt ctx n goal region g := Iff.rfl

/-- **The run link with calls**: against `runLC env msup`, for every `msup`
(the model's `sup`; the Hoon's `sup` noun is quantified in `CompRunAtR`). -/
def CompRunAtC (env : CallEnv) (ctx : Noun) (n : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) : Prop :=
  ∀ msup : Option Nomm, CompRunAtR (runLC env msup) ctx n goal region g

/-- On a pure nomm `runLC` is `runL`, so `CompRunAt` gives `CompRunAtC`. -/
theorem crc_of_pure (env : CallEnv) {n : Nomm} (hn : n.pure = true) {goal : CGoalL CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)} (h : CompRunAt ctx n goal region g) :
    CompRunAtC env ctx n goal region g := by
  intro msup x mono sup hx
  rw [h x mono sup hx, runLC_eq env n (Nomm.noCall_of_pure n hn)]

/-! ## What a run returns -/

/-- **What a run returns from a goal with the invariant**: the counter
grows, the mode stays, the result is below the new counter, its need is made
of fresh registers and those of the goal's need, has no register twice, and
looks at no axis `0`. -/
def CrOut (g : Gen (TreapMap mugF)) (gl : CGoal CSet) (g' : Gen (TreapMap mugF)) (nex : Next CSet) : Prop :=
  g.re ≤ g'.re ∧ g'.drop = false ∧ NextIn g'.re nex ∧ (∀ y, NMem nex.laz.ned y → g.re ≤ y ∨ GMem gl y) ∧
    Distinct nex.laz.ned ∧ CrLok nex.laz

/-- The same of a `NextL`, which is fork-free. -/
def CrRes (g : Gen (TreapMap mugF)) (gl : CGoal CSet) (g' : Gen (TreapMap mugF)) (nex : NextL CSet) : Prop :=
  ∃ n : Next CSet, nex = Next.toL n ∧ CrOut g gl g' n

/-- A pure run meets `CrOut` (`cri_run`, `cra_run_lok`). -/
theorem cro_run {n : Nomm} (hn : n.pure = true) (h6 : noSix n = true) {gl : CGoal CSet}
    {g g' : Gen (TreapMap mugF)} {nex : Next CSet} (hi : CrInv g gl) (h : run n gl g = some (nex, g')) :
    CrOut g gl g' nex := by
  obtain ⟨l, d, ni, s, D⟩ := cri_run hi h
  exact ⟨l, d, ni, s, D, cra_run_lok n hn h6 gl g g' nex h hi.1⟩

/-- A pure `runLC` from a fork-free goal meets `CrRes`. -/
theorem crr_pure (env : CallEnv) (msup : Option Nomm) {n : Nomm} (hn : n.pure = true) (h6 : noSix n = true)
    {gl : CGoal CSet} (region : List Nat) {g g' : Gen (TreapMap mugF)} {nex : NextL CSet} (hi : CrInv g gl)
    (h : runLC env msup n (CGoal.toL gl) region g = some (nex, g')) : CrRes g gl g' nex := by
  rw [runLC_eq env n (Nomm.noCall_of_pure n hn), runL_toL n hn h6] at h
  cases e : run (S := CSet) (Map := TreapMap mugF) n gl g with
  | none => rw [map_apply, e] at h; cases h
  | some r =>
    obtain ⟨n', g''⟩ := r
    rw [map_apply, e] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨n', rfl, cro_run hn h6 hi e⟩

/-- The goal `nex.goal` of a result with `CrOut` meets the invariant. -/
theorem cro_goal {g : Gen (TreapMap mugF)} {gl : CGoal CSet} {g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : CrOut g gl g' nex) : CrInv g' nex.goal :=
  ⟨h.2.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.2.1⟩

/-! ## The `+copy` of two runs -/

/-- **The side condition of `+copy` from the runs' results**: `q` ran first
for `ts`, `p` second for `hs` (apart from `ts` and below the counter). -/
theorem crf_copy_ok {hs ts : Sure CSet} {j : Jmp} {g2 g3 g4 : Gen (TreapMap mugF)} {nex2 nex1 : Next CSet}
    (nh : NB g2.re hs.ned) (ap : ∀ x, NMem hs.ned x → ¬ NMem ts.ned x)
    (O3 : CrOut g2 (CGoal.next ts j) g3 nex2) (O4 : CrOut g3 (CGoal.next hs nex2.th) g4 nex1) :
    CrCopyOk g4 nex1 nex2.laz := by
  obtain ⟨l3, -, n3, s3, -⟩ := O3
  obtain ⟨l4, -, n4, s4, -⟩ := O4
  refine ⟨cri_lt_of_nb _ n4.1, cri_lt_of_nb _ (n3.1.mono l4), cri_meet_apart _ _ fun x e1 e2 => ?_⟩
  have x3 := n3.1 x e2
  rcases s4 x e1 with e | e
  · omega
  · have x2 := nh x e
    rcases s3 x e2 with e' | e'
    · omega
    · exact ap x e e'

/-- **What the `+copy` of two runs returns**: below the new counter, made of
fresh registers and those of the two goals' needs, distinct, no look at
`0`. -/
theorem crf_copy_out {hs ts : Sure CSet} {j : Jmp} {g2 g3 g4 g5 : Gen (TreapMap mugF)} {nex2 nex1 nex : Next CSet}
    (nh : NB g2.re hs.ned) (ap : ∀ x, NMem hs.ned x → ¬ NMem ts.ned x)
    (O3 : CrOut g2 (CGoal.next ts j) g3 nex2) (O4 : CrOut g3 (CGoal.next hs nex2.th) g4 nex1)
    (h5 : copy nex1 nex2.laz g4 = some (nex, g5)) :
    g2.re ≤ g5.re ∧ g5.drop = false ∧ NextIn g5.re nex ∧
      (∀ y, NMem nex.laz.ned y → g2.re ≤ y ∨ NMem hs.ned y ∨ NMem ts.ned y) ∧
      Distinct nex.laz.ned ∧ CrLok nex.laz := by
  obtain ⟨l3, d3, n3, s3, D3, L3⟩ := O3
  obtain ⟨l4, d4, n4, s4, D4, L4⟩ := O4
  obtain ⟨k5, ni5⟩ := keeps_copy d4 n4 (n3.1.mono l4) h5
  have lok := cra_copy_lok h5 L4 L3
  have a12 : ∀ y, NMem nex1.laz.ned y → ¬ NMem nex2.laz.ned y := fun y e1 e2 => by
    have := n3.1 y e2
    rcases s4 y e1 with e | e
    · omega
    · rcases s3 y e2 with e' | e'
      · have := nh y e; omega
      · exact ap y e e'
  have dpair : Distinct (Need.pair nex1.laz.ned nex2.laz.ned) := ⟨D4, D3, a12⟩
  simp only [copy] at h5
  obtain ⟨o, g6, h6, h5⟩ := bind_some h5
  obtain ⟨k6, q6⟩ := keeps_emit d4 (blobIn_fin (f := Termin.hop nex1.th) n4.2) h6
  obtain ⟨laz, g7, h7, h5⟩ := bind_some h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  simp only [copyLazy] at h7
  obtain ⟨⟨n1, o1⟩, g8, h8, h7⟩ := bind_some h7
  obtain ⟨u, g9, h9, h7⟩ := bind_some h7
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h7
  obtain ⟨rfl, rfl⟩ := h7
  have nb1 : NB g6.re nex1.laz.ned := by rw [q6]; exact n4.1
  have nb2 : NB g6.re nex2.laz.ned := by rw [q6]; exact n3.1.mono l4
  have dres := copyNeed_dist _ _ _ _ _ _ h8 dpair nb1 nb2
  obtain ⟨_, _, c8⟩ := copyNeed_spec _ _ _ _ _ _ h8
  have m8 := c8.mem
  have l6 := k6.le
  refine ⟨by have := k5.le; omega, k5.dropF d4, ni5, fun y hy => ?_, dres, lok⟩
  simp only at hy m8
  rcases m8 y hy with (e | e) | e
  · rcases s4 y e with e' | e'
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl e')
  · rcases s3 y e with e' | e'
    · exact Or.inl e'
    · exact Or.inr (Or.inr e')
  · exact Or.inl (by omega)

/-! ## The Nock of the case (`tools/gen/runtwo.py`)

`cr2Head` is `[6 [5 [1 0] [0 471]] cr2Ind cr2Dir]`: the test `?~  info.nomm`,
the indirect call `cr2Ind` and the direct call `cr2Dir` (read from the
pill).  `cr2Ind` pushes the `next` of `+simple-next` and goes on with
`cr2Kf`: `+kerf` (arm `0xabb4` of the door's core, door arm `27572`), the two
`+re`, `+emit` of the call block, then `cr2Tail`: the run of `q` (`$` of the
`|^` core with `nomm` and `goal` edited), `cr2T2`: `+past` (door arm `7166`),
`cr2T3`: the run of `p` and `+copy` (door arm `220590`). -/

def cr2T3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 62)))))) (C (A 0) (A 2)))))))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 0x7fea))) (C (A 0) (A 255)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))))))))))))

def cr2T2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 0x7fea)) (C (A 0) (A 0x7fee))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr2T3))))))))

def cr2Tail : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6)))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 0x3fd6))) (C (A 0) (A 63)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr2T2))))))))

def cr2Kf : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabb4) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 63)))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6b6f6e)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 29))))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 60))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr2Tail))))))))))))))))))))))))))))))))

def cr2Ind : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr2Kf))))))))

def cr2Dir : Noun := (slot? 68709908471 comp.door).getD (A 0)

def cr2Head : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 471)))) (C cr2Ind cr2Dir))

theorem cr2_eq : crK2 = cr2Head := by kernel_rfl

theorem cr_disp_n2 (t mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 2) t) goal region sup D) crDol
      = nock (crSubj mono (C (A 2) t) goal region sup D) crK2 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- The noun of an indirect call. -/
theorem cr2_noun (p q : Nomm) : (Nomm.n2 p q Option.none).toNoun = C (A 2) (C p.toNoun (C q.toNoun (A 0))) := rfl

/-- The test `?~  info.nomm` sends an indirect call to `cr2Ind`. -/
theorem cr2_ind (P Q mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 2) (C P (C Q (A 0)))) goal region sup D) crK2
      = nock (crSubj mono (C (A 2) (C P (C Q (A 0)))) goal region sup D) cr2Ind := by
  rw [cr2_eq]
  unfold cr2Head
  simp [nock_exec, crSubj]

/-! ## From the call block on -/

/-- The run of `p` in `runLC` on a pure `p` with no `%6` is `run`. -/
theorem cr2_run_pure (env : CallEnv) (msup : Option Nomm) {p : Nomm} (hpp : p.pure = true) (hp6 : noSix p = true)
    (gl : CGoal CSet) (region : List Nat) :
    (runLC env msup p (CGoal.toL gl) region : CM (TreapMap mugF) (NextL CSet)) = Next.toL <$> run p gl := by
  rw [runLC_eq env p (Nomm.noCall_of_pure p hpp), runL_toL p hpp hp6]

/-- **The tail of the indirect call**: the run of `q` into the call block
`o`, `+past` (the identity on a pure `p`), the run of `p` with the `then`
of `q`, and `+copy`, given the link of `q` for its goal and the shape of its
result, the link of `p`, and the side condition of `+copy` on the states the
model reaches. -/
theorem cr2_tail (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpp : p.pure = true) (hp6 : noSix p = true)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup nexN : Noun) (out pro rSub rFol o : Nat)
    (g1 : Gen (TreapMap mugF))
    (hq : CompRunAtR (runLC env msup) ctx q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region g1)
    (hqF : ∀ nex g2, runLC env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region g1 = some (nex, g2) →
      ∃ n : Next CSet, nex = Next.toL n)
    (hp : ∀ (nexF : Next CSet) g2,
      runLC env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region g1 = some (Next.toL nexF, g2) →
      CompRunAt ctx p (CGoal.toL (CGoal.next (lazyReg rSub) nexF.th)) region g2)
    (hcp : ∀ (nexF : Next CSet) g2 nexS g3,
      runLC env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region g1 = some (Next.toL nexF, g2) →
      run p (CGoal.next (lazyReg rSub) nexF.th) g2 = some (nexS, g3) → CrCopyOk g3 nexS nexF.laz) :
    nock (C (A o) (C (A rFol) (C (A rSub) (C (C (A out) (A pro)) (C nexN
      (crSubj mono (Nomm.n2 p q Option.none).toNoun goalN (listNoun A region) sup (compCore g1 x ctx))))))) cr2Tail
      = ((do
          let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region
          let nexF ← pastL env.cod nexF p region
          let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg rSub) nexF.th)) region
          copyL nexS nexF.laz : CM (TreapMap mugF) (NextL CSet)) g1).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, hl, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  have hq1 := hq x mono sup hx
  rw [cr_goal_reg] at hq1
  simp only [crSubj, compCore] at hq1
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases eq : runLC (S := CSet) (Map := TreapMap mugF) env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o)))
      region g1 with
  | none =>
    rw [eq] at hq1
    generalize comp.door = Dr at hq1 hD1 hD2 ⊢
    nock_open cr2Tail
    simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
      StateT.bind, eq]
  | some r =>
    obtain ⟨nexL, g2⟩ := r
    obtain ⟨nexF, rfl⟩ := hqF _ _ eq
    rw [eq] at hq1
    simp only [Option.map_some, cr_next_noun] at hq1
    have hpa := cr_past_pure h7 hcode x g2 nexF p hpp region
    have hp1 := cr_at_run hpp hp6 (hp nexF g2 eq) x mono sup hx
    rw [cr_goal_reg'] at hp1
    simp only [crSubj, compCore] at hp1
    have hpm := cr2_run_pure env msup hpp hp6 (CGoal.next (lazyReg rSub) nexF.th) region
    have hps : (pastL env.cod (Next.toL nexF) p region : CM (TreapMap mugF) (NextL CSet)) = pure (Next.toL nexF) :=
      pastL_pure env.cod _ hpp region
    cases eq2 : run (S := CSet) (Map := TreapMap mugF) p (CGoal.next (lazyReg rSub) nexF.th) g2 with
    | none =>
      rw [eq2] at hp1
      generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 ⊢
      unfold cr2Tail cr2T2 cr2T3
      simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
        StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, eq, hps, hpm, pure, StateT.pure, map_apply]
    | some r' =>
      obtain ⟨nexS, g3⟩ := r'
      rw [eq2] at hp1
      simp only [Option.map_some, cr_next_noun'] at hp1
      obtain ⟨hlt, hrt, hm⟩ := hcp nexF g2 nexS g3 eq eq2
      have hcpy := comp_copy (x := x) hc hl g3 nexS nexF.laz hlt hrt hm
      simp only [compCore, cr_next_noun'] at hcpy
      have hcm := copyL_toL (Map := TreapMap mugF) nexS nexF.laz
      generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 hcpy ⊢
      unfold cr2Tail cr2T2 cr2T3
      simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
        StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, hD2, cr_cp_arm, hcpy, eq, cr_next_noun', hps,
        hpm, pure, StateT.pure, hcm, cr_next_noun, map_apply, Function.comp_def]

/-! ## From `+kerf` on, and the whole case -/

theorem next_toL_inj {a b : Next CSet} (h : Next.toL a = Next.toL b) : a = b := by
  obtain ⟨la, ta⟩ := a
  obtain ⟨lb, tb⟩ := b
  simp only [Next.toL, NextL.mk.injEq, Lazy.ofSure, Lazy.mk.injEq] at h
  obtain ⟨⟨rfl, -, -⟩, rfl⟩ := h
  rfl

theorem crr_out {g : Gen (TreapMap mugF)} {gl : CGoal CSet} {g' : Gen (TreapMap mugF)} {n : Next CSet}
    (h : CrRes g gl g' (Next.toL n)) : CrOut g gl g' n := by
  obtain ⟨n', e, o⟩ := h
  rw [next_toL_inj e]; exact o

/-- The call block `[~ [%nok s f p]~ %hop ~ t]`. -/
theorem cr_blob_nok_hop (s f d t : Nat) : Blob.toNoun ⟨[], [Pole.nok s f d], Termin.hop (jmp0 t)⟩
    = C (A 0) (C (C (C (A 0x6b6f6e) (C (A s) (C (A f) (A d)))) (A 0)) (C (A 0x706f68) (C (A 0) (A t)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.nok, Jmp.toNoun, jmp0]

/-- The model of the indirect call, from `+kerf` on. -/
noncomputable def cr2KfM (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (region : List Nat) (nex : NextL CSet) :
    CM (TreapMap mugF) (NextL CSet) := do
  let (out, pro) ← kerf nex
  let rSub ← re
  let rFol ← re
  let o ← emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩
  let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region
  let nexF ← pastL env.cod nexF p region
  let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg rSub) nexF.th)) region
  copyL nexS nexF.laz

/-- **The model of the indirect call** (`callL` with `info = none`):
`+simple-next`, then `cr2KfM`. -/
theorem cr2_model (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet) (region : List Nat) :
    (runLC env msup (Nomm.n2 p q Option.none) goal region : CM (TreapMap mugF) (NextL CSet)) =
      simpleNextL goal >>= cr2KfM env msup p q region := rfl

/-- The hypotheses on the parts, as the case takes them: the link of `q`
and the shape of its result on every goal with the invariant, and the link
of `p` on every such goal. -/
structure Cr2Parts (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (region : List Nat) : Prop where
  runQ : ∀ s th g1, CrInv g1 (CGoal.next s th) → CompRunAtR (runLC env msup) ctx q (CGoal.toL (CGoal.next s th)) region g1
  resQ : ∀ s th g1 nex g2, CrInv g1 (CGoal.next s th) →
    runLC env msup q (CGoal.toL (CGoal.next s th)) region g1 = some (nex, g2) → CrRes g1 (CGoal.next s th) g2 nex
  runP : ∀ s th g1, CrInv g1 (CGoal.next s th) → CompRunAt ctx p (CGoal.toL (CGoal.next s th)) region g1

/-- **From `+kerf` on**: `+kerf` of a fork-free `next`, the two registers,
the call block and the tail. -/
theorem cr2_kf (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpp : p.pure = true) (hp6 : noSix p = true)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun) (nex0 : Next CSet)
    (g1 : Gen (TreapMap mugF)) (hd : g1.drop = false) (hlok : CrLok nex0.laz)
    (P : Cr2Parts env msup ctx p q region) :
    nock (C (C (A 0x7478656e) (C (lazyNoun nex0.laz) nex0.th.toNoun))
      (crSubj mono (Nomm.n2 p q Option.none).toNoun goalN (listNoun A region) sup (compCore g1 x ctx))) cr2Kf
      = (cr2KfM env msup p q region (Next.toL nex0) g1).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  have hk := comp_kerf hc hl hm x g1 nex0 (hx g1.bo) hlok
  have hD1 := comp_kerf_at
  have hD2 := comp_re_at
  have hD3 := comp_emit_at
  simp only [compCore] at hk ⊢
  cases ek : kerf (Next.toL nex0) g1 with
  | none =>
    rw [ek] at hk
    generalize comp.door = Dr at hk hD1 hD2 hD3 ⊢
    nock_open cr2Kf
    simp [nock_exec, crSubj, hD1, comp_kerf_arm, hk, cr2KfM, bind, StateT.bind, ek]
  | some r =>
    obtain ⟨⟨out, pro⟩, g2⟩ := r
    rw [ek] at hk
    simp only [Option.map_some] at hk
    have K := kerf_ofSure (S := CSet) (Map := TreapMap mugF) ek hd
    obtain ⟨-, epro, -, ed2, -, -, l2, -⟩ := K
    have d2 : g2.drop = false := ed2.trans hd
    have hre0 := comp_re' ctx x g2
    have hre1 := comp_re' ctx x { g2 with re := g2.re + 1 }
    have he := cf_emit (x := x) hc { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }
      ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
    rw [cr_blob_nok_hop] at he
    generalize hg5 : cfEmitG ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
      { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = g5 at he
    have r5 : g5.re = g2.re + 1 + 1 := by rw [← hg5, cf_emitG_re]
    have d5 : g5.drop = false := by rw [← hg5, cf_emitG_drop]; exact d2
    have o5 : ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } : Gen (TreapMap mugF)).bo = g2.bo := rfl
    have iq : CrInv g5 (CGoal.next (lazyReg (g2.re + 1)) (jmp0 g2.bo)) := cri_reg g2.bo (by omega) d5
    have hip : ∀ (nexF : Next CSet) g6,
        runLC env msup q (CGoal.toL (CGoal.next (lazyReg (g2.re + 1)) (jmp0 g2.bo))) region g5 = some (Next.toL nexF, g6) →
        CrOut g5 (CGoal.next (lazyReg (g2.re + 1)) (jmp0 g2.bo)) g6 nexF ∧
          CrInv g6 (CGoal.next (lazyReg g2.re) nexF.th) := by
      intro nexF g6 e
      have O := crr_out (P.resQ _ _ _ _ _ iq e)
      refine ⟨O, cra_lok_reg _, O.2.1, ⟨nb_this (by have := O.1; omega), O.2.2.1.2⟩, by simp [GDist, lazyReg, Distinct]⟩
    have ht := cr2_tail h7 hcode env msup p q hpp hp6 region x hx mono goalN sup
      (C (A 0x7478656e) (C (lazyNoun nex0.laz) nex0.th.toNoun)) out pro g2.re (g2.re + 1) g2.bo g5 (P.runQ _ _ _ iq)
      (fun nex g6 e => let ⟨n, e', _⟩ := P.resQ _ _ _ _ _ iq e; ⟨n, e'⟩)
      (fun nexF g6 e => P.runP _ _ _ (hip nexF g6 e).2)
      (fun nexF g6 nexS g7 e e2 => crf_copy_ok (nb_this (by omega))
        (fun y e1 e2' => by simp only [lazyReg, NMem] at e1 e2'; omega) (hip nexF g6 e).1
        (cro_run hpp hp6 (hip nexF g6 e).2 e2))
    simp only [crSubj, compCore] at ht hre0 hre1
    generalize comp.door = Dr at hk hD1 hD2 hD3 hre0 hre1 he ht ⊢
    nock_open cr2Kf
    simp [nock_exec, crSubj, hD1, comp_kerf_arm, hk, hD2, hre0, hre1, hD3, comp_emit_arm, he, ht, cr2KfM, bind,
      StateT.bind, ek, re, cf_emit_g, hg5]

/-- **The case `%2` of `+run` for an indirect call** (`info` `~`), on every
fork-free goal with the invariant, for `p` pure with no `%6`: `+simple-next`,
`+kerf`, two registers, the block `[%nok r-sub r-fol pro]` hopping to
`out`, `q` for the whole formula in `r-fol`, `+past` (the identity on `p`),
`p` for the whole subject in `r-sub`, and `+copy`.  Against `runLC env
msup`, given the links of the parts on the goals with the invariant and the
shape of `q`'s results (`Cr2Parts`). -/
theorem comp_run_n2 (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpp : p.pure = true) (hp6 : noSix p = true)
    (gl : CGoal CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : CrInv g gl)
    (P : Cr2Parts env msup ctx p q region) :
    CompRunAtR (runLC env msup) ctx (Nomm.n2 p q Option.none) (CGoal.toL gl) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  intro x mono sup hx
  rw [cr2_model, cr2_noun, cr_disp_n2, cr2_ind]
  have hsn := comp_simple_next hc x g (CGoal.toL gl) mono (C (A 2) (C p.toNoun (C q.toNoun (A 0))))
    (listNoun A region) sup
  rw [simpleNextL_toL, map_apply] at hsn
  rw [simpleNextL_toL, bind_apply, map_apply]
  cases e : simpleNext (S := CSet) (Map := TreapMap mugF) gl g with
  | none =>
    rw [e] at hsn
    simp only [Option.map_none] at hsn
    simp only [crSubj, compCore] at hsn ⊢
    generalize comp.door = Dr at hsn ⊢
    nock_open cr2Ind
    simp [nock_exec, crSubj, hsn, cr_bat_sn]
  | some r =>
    obtain ⟨nex0, g1⟩ := r
    rw [e] at hsn
    simp only [Option.map_some, cr_next_noun] at hsn
    obtain ⟨d1, -, -⟩ := cri_simple_next hinv e
    have hk := cr2_kf h7 hcode env msup p q hpp hp6 region x hx mono (CGoal.toL gl).toNoun sup nex0 g1 d1
      (cr_sn_lok gl hinv.1 g nex0 g1 e) P
    rw [cr2_noun] at hk
    simp only [crSubj, compCore] at hsn hk ⊢
    generalize comp.door = Dr at hsn hk ⊢
    nock_open cr2Ind
    simp [nock_exec, crSubj, hsn, cr_bat_sn, hk]

end Compiler
end Formalization
