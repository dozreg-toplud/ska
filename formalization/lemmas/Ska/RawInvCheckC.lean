import lemmas.Ska.RawInvCheckX
import lemmas.Ska.CompRunLCEq

/-!
# Raw `+comp` output with indirect calls: the input of `+optimize`'s totality

README Gaps 14 (b), track D.  On the 120 nomms of `enumC` (an indirect call
`[2 p [0 2]]` alone, under a cons, and in a branch of a `%6`, for 40 nomms
`p` of `enum6`), run through `runLC envR`:
* the raw blocks of the top run meet `Closed`, `ArityOK` and `TwoNA`
  (`stB`), the facts of `RunAT`;
* the output of both final passes (`finishLUC`, `finishLFC`) meets the
  facts of `StInv` that `stIn_finishLFX_of` gives on `FragX` (`okSt`:
  `Closed`, `ArityOK`, `TwoNA` and the block `0`) and `ReadsIn nargs` over
  the reachable blocks (`okReads`).
Not vacuous: 60 of the raw runs and 60 of the n-ary outputs have a jump
with arguments (`argsB`).
So the statements of `RawInvStX.lean` and `RawInvATX.lean` are candidates
for indirect calls too; what blocks their proofs is the induction on
`runLC` (README Gaps 14 (b)).
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- The top run with indirect calls. -/
def runC (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  runLC envR Option.none nm (CGoalL.done : CGoalL LS) [] (gen0 : Comp.Gen FM)

/-- The n-ary final pass with indirect calls. -/
def naryC (nm : Nomm) : Option (Straight FM) :=
  finishLFC (S := LS) (Map := FM) envR nm NeedOrd.this Cape.no (fun ned => (ned, []))

#guard enumC.length == 120 && (enumC.filter fun nm => (runC nm).isSome).length == 120
#guard (enumC.filter fun nm => (finishLUC (S := LS) (Map := FM) envR nm).isSome).length == 120
#guard (enumC.filter fun nm => (naryC nm).isSome).length == 120
#guard enumC.all fun nm => match runC nm with | some (_, g) => stB g.blocks | none => true
#guard enumC.all fun nm => okSt (finishLUC (S := LS) (Map := FM) envR nm) && okSt (naryC nm)
#guard enumC.all fun nm => okReads (finishLUC (S := LS) (Map := FM) envR nm) && okReads (naryC nm)
/-- Not vacuous: 60 raw runs and 60 n-ary outputs have a jump with arguments. -/
def argsB (m : FM Blob) : Bool := (blocksOf m).any fun (_, b) => (getJmps b.fin).any fun j => !j.args.isEmpty

#guard (enumC.filter fun nm => match runC nm with | some (_, g) => argsB g.blocks | none => false).length == 60
#guard (enumC.filter fun nm => match naryC nm with | some c => argsB c.blocks | none => false).length == 60

end Raw
end SkaModel
end Formalization
