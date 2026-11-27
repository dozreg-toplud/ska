import lemmas.Ska.CompCall

/-!
# The whole-subject version of a direct call: `+mono-try-call`

README Gaps 18 (track J, 2026-11-27).  The case `%2` of `+run` with `mono`
`&`, which `+compile-unary` runs (the version of a function of its whole
subject, what `%full` runs).  `callL` (`CompCall.lean`) is the case for
`mono` `|`; nothing here changes it.

## The Hoon (`desk/lib/nock-compilation.hoon`)

The direct call `[2 p q]` with `info = [b key]`, past the drop test (lines
3924 to 3942), no memo key, no ring: `b-ned` from `+callee-need`, `sub-ned`
its registers (`+need-ord-alloc-regs`), `sub-v` their list.  With `mono`
`&` the soft-call machinery is never entered: `sof` is computed but read only
by the `?.  mono` branches (`+soft-new`), and the call block that
`+mono-try-call` returns is fresh, so `(~(has by soft.gen) call-block)` is
false and `+soft-bond` is not reached.  So no `sof` condition here.

* Under `%done` (lines 4002 to 4011): a register `sub-pes`, the block `opt`
  `[~ ~ [%jmp b sub-v]]`, the block `pes` `[~ ~ [%jsp b sub-pes]]`.
* Otherwise (lines 4012 to 4031): `+simple-next`, `+kerf` (`out`, `pro`),
  registers `merged`, `sub-pes`, the block `merge` `[~[merged] [%mov merged
  pro]~ %hop ~ out]`, registers `pro-opt`, `pro-pes`, the block `opt`
  `[~ [%cal b sub-v pro-opt]~ %hop ~[`pro-opt] merge]` and the block `pes`
  `[~ [%csl b sub-pes pro-pes]~ %hop ~[`pro-pes] merge]`.
* Then (line 4038) `(mono-try-call sub-ned [opt sub-pes pes])` gives the
  call block, and the need of the call becomes `this+sub-pes`: the subject
  of the callee is taken whole.
* The rest as for `mono` `|`: `q` for a need that asks nothing (skipped by
  `+safe-fol-fol`), `+past` over `p`, `p` for `%next (this sub-pes)
  call-block`, `+copy`.

`+mono-try-call` (line 7267) walks `sub-ned` from the register `r = sub-pes`
with the success block `o = opt` and the failure block `fail = pes`:
`%none` gives `o`; `%this` a block `[%mov r r.ned]`, `%hop o` (asserting
`r ≠ r.ned`); a cell `[h t]` two fresh registers `r-t`, `r-h` (in that
order), the tail's walk from `r-t` into `o`, the head's from `r-h` into the
tail's block, a block `[%hed r r-h] [%tal r r-t]`, `%hop` into the head's
block, and a block `[%clq r split fail]`; `%both` the same with `[%mov r
r.ned]` after the split ops.

## Contents

* `monoTryLoop`, `monoTryCall`: `+mono-try-call`.
* `callDM`: the direct call with `mono` `&` (drop test, then the two call
  blocks and `+mono-try-call`), for no memo key and no ring.
* `callLM env mono`: the case `%2` with `mono`: `callDM` for a direct call
  when `mono`, `callL` otherwise.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The loop of `+mono-try-call`**: the need `ned` of the callee with its
registers, the register `r` that holds the noun to take apart, the block `o`
to go to once it is taken apart; `fail` is the pessimistic call block. -/
def monoTryLoop (fail : Nat) : Need → Nat → Nat → CM Map Nat
  | Need.none, _, o => pure o
  | Need.this rn, r, o =>
      if r = rn then crashM else emit ⟨[], [Pole.mov r rn], Termin.hop (jmp0 o)⟩
  | Need.pair h t, r, o => do
      let rt ← re
      let rh ← re
      let ot ← monoTryLoop fail t rt o
      let oh ← monoTryLoop fail h rh ot
      let os ← emit ⟨[], [Pole.hed r rh, Pole.tal r rt], Termin.hop (jmp0 oh)⟩
      emit ⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩
  | Need.both rn h t, r, o => do
      let rt ← re
      let rh ← re
      let ot ← monoTryLoop fail t rt o
      let oh ← monoTryLoop fail h rh ot
      if r = rn then crashM else do
      let os ← emit ⟨[], [Pole.hed r rh, Pole.tal r rt, Pole.mov r rn], Termin.hop (jmp0 oh)⟩
      emit ⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩

/-- **`+mono-try-call`** of `[ned opt [sub pes]]`. -/
def monoTryCall (ned : Need) (opt sub pes : Nat) : CM Map Nat :=
  monoTryLoop pes ned sub opt

/-- **The call blocks with `mono` `&`** (lines 4002 to 4038): the register
`sub-pes` and the block that `+mono-try-call` returns. -/
def monoBlocks (b : Bell) (subNed : Need) (goal : CGoalL S) : CM Map (Nat × Nat) :=
  let subV := flattenNeed subNed
  match goal with
  | CGoalL.done => do
      let subPes ← re
      let opt ← emit ⟨[], [], Termin.jmp b subV⟩
      let pes ← emit ⟨[], [], Termin.jsp b subPes⟩
      let o ← monoTryCall subNed opt subPes pes
      pure (subPes, o)
  | g => do
      let nex ← simpleNextL g
      let (out, pro) ← kerf nex
      let merged ← re
      let subPes ← re
      let merge ← emit ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩
      let proOpt ← re
      let proPes ← re
      let opt ← emit ⟨[], [Pole.cal b subV proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
      let pes ← emit ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], merge⟩⟩
      let o ← monoTryCall subNed opt subPes pes
      pure (subPes, o)

/-- **The direct call with `mono` `&`**, with the runs of the subject `p`
and the formula `q` as parameters: the drop of `callL`, else, for no memo
key and no ring, `monoBlocks` and the rest as in `callL` with the need
`this sub-pes`.  `none` on the cases not modelled (a memo key, a ring, no
need). -/
def callDM (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (b : Bell) (key : Option Noun) (goal : CGoalL S) (region : List Nat) : CM Map (NextL S) :=
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
      | Option.none, Option.none, some bNed => do
        let subNed ← needOrdAllocRegs bNed
        let (subPes, callBlock) ← monoBlocks b subNed goal
        let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
        copyL nexSub nexFol.laz
      | _, _, _ => fun _ => Option.none

/-- **The case `%2` of `run` with `mono`**: a direct call with `mono` `&`
is `callDM`; everything else (`mono` `|`, an indirect call) is `callL`. -/
def callLM (env : CallEnv) (mono : Bool) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CM Map (NextL S) :=
  match mono, info with
  | true, some (b, key) => callDM env rp rq p q b key goal region
  | _, _ => callL env rp rq p q info sup goal region

theorem callLM_false (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    (callLM env false rp rq p q info sup goal region : CM Map (NextL S)) = callL env rp rq p q info sup goal region :=
  rfl

theorem callLM_none (env : CallEnv) (mono : Bool) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    (callLM env mono rp rq p q Option.none sup goal region : CM Map (NextL S)) =
      callL env rp rq p q Option.none sup goal region := by
  cases mono <;> rfl

end Comp
end SkaModel
end Formalization
