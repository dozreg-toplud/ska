import lemmas.Ska.CompNaryTopEx

/-!
# The n-ary `%cal` form, checked before it is proved

README Gaps 18.15 (c).  `runLC_cal` and `callN_run` (`CompNaryTopCal.lean`)
state the shape of the code `callL` emits for a direct call `[2 p q b]`
under a goal `%next L th` in the n-ary code (`mono` `|`): from the state
`g0`, the callee's registers `sub` (`+need-ord-alloc-regs` of the need
read), `+kerf` of `[L th]` from the state after them (`out`, `pro`), the
block `[cal b sub pro] hop out` at the next label, `p` under `%next (ofSure
sub) (jmp0 that block)`, and `+copy` into the need that asks nothing.  Both
facts are checked here first:

* `calReplay`: that replay of the steps gives exactly what `runLC` gives on
  the whole nomm (registers, labels, every block, the result), for direct
  calls with `p` a `%0`, a cons, a cons holding a direct call, and the
  callee `R` or `R2`, under the goals a `%4`, a cons head, a `%7` and an
  indirect call's operands hand down (a single register, a pair of
  registers, the empty need, a register with labels below), from states
  with registers and labels below.
* `calAll`: the n-ary code (`finishLFC`) of nomms with a direct call in the
  `%cal` form (under `%7` as `p`, as the subject and as the formula of an
  indirect call, under `%3`, `%5`, in a cons, a direct call in the `p` of a
  direct call, under `%4`) agrees with `+mink`, run by the interpreter model
  on the table of `R` and `R2`'s real entries, entered with the split of the
  subject, under the six needs and four capes of `CompNaryTopEx.lean`: 13
  nomms, 176 codes, 528 runs, 456 of them products, no disagreement.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The steps of `runLC_cal`, replayed, against `runLC` on the whole nomm:
the same registers, labels, blocks below the final label and result. -/
def calReplay (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : Bool :=
  match nm with
  | Nomm.n2 p q (some (b, Option.none)) =>
    match envD.need b with
    | some bNed =>
      match (needOrdAllocRegs bNed g0 : Option (Need × Gen FM)) with
      | some (sub, gA) =>
        match (kerf (S := LS) ⟨L, th⟩ gA) with
        | some ((out, pro), g2) =>
          let g3 := g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩
          let rep := (runLC (S := LS) envD Option.none p (CGoalL.next (ofSure ⟨sub, HoonSet.empty⟩) (jmp0 g2.bo)) [] g3).bind
            fun (nexS, g5) => copyL nexS (ofSure Sure.bunt) g5
          match rep, runLC (S := LS) (Map := FM) envD Option.none nm (CGoalL.next L th) [] g0 with
          | some (n1, h1), some (n2, h2) =>
            safeFolFol q && h1.re == h2.re && h1.bo == h2.bo && n1.th == n2.th &&
              flattenNeed n1.laz.sure.ned == flattenNeed n2.laz.sure.ned &&
              (entries n1.laz).length == (entries n2.laz).length &&
              (List.range h1.bo).all fun k => h1.blocks.f k == h2.blocks.f k
          | _, _ => false
        | Option.none => false
      | Option.none => false
    | Option.none => false
  | _ => false

/-- The direct calls replayed. -/
def calNomms : List Nomm :=
  [callR, callR3, callR2,
   Nomm.n2 (Nomm.cons (Nomm.n1 nounR) callR) (Nomm.n1 nounR) (some (bellR, Option.none)),
   Nomm.n2 (Nomm.cons (Nomm.n1 nounR2) (Nomm.cons (Nomm.n0 3) (Nomm.n0 2))) (Nomm.n1 nounR2)
     (some (bellR2, Option.none))]

/-- The goals and states: what `%4` under `%done` hands down (one register,
block `1`), a cons head (two registers), the need that asks nothing, a
register with more labels and registers below. -/
def calGoals : List (Lazy LS × Jmp × Gen FM) :=
  [(ofSure (lazyReg 0), jmp0 1, genAt 1 2),
   (ofSure ⟨Need.pair (Need.this 0) (Need.this 1), HoonSet.empty⟩, jmp0 1, genAt 2 2),
   (ofSure Sure.bunt, jmp0 3, genAt 5 4),
   (ofSure (lazyReg 4), jmp0 2, genAt 7 6),
   (ofSure ⟨Need.pair Need.none (Need.this 2), HoonSet.empty⟩, jmp0 1, genAt 3 3)]

#guard calNomms.all fun nm => calGoals.all fun (L, th, g0) => calReplay nm L th g0
#guard (calNomms.length, calGoals.length) = (5, 5)

/-- `[[1 R] [2 [0 1] [1 R] R-bell]]` as the `p` of a direct call of `R`. -/
def callRR : Nomm := Nomm.n2 (Nomm.cons (Nomm.n1 nounR) callR) (Nomm.n1 nounR) (some (bellR, Option.none))
def callRRF : Noun := n3 (A 2) (C (quote nounR) callRF) (quote nounR)

/-- The cases: the `%cal` form below a `%7`, an indirect call, `%3`, `%5`,
a cons, `%4`, and in the `p` of a direct call. -/
def calCases : List (Nomm × Noun × List Noun) :=
  let lst : Noun := C (A 1) (C (A 2) (C (A 3) (A 4)))
  let sAny : List Noun := [A 7, C (A 1) (A 2), C (A 0) lst, C (C (A 1) (A 2)) (C (A 3) (A 4))]
  let sR : List Noun := [C nounR (A 7), C nounR lst, C nounR (C (A 0) (C (A 0) (A 0)))]
  let sR2 : List Noun := [C nounR2 (C lst (slot 2)), C nounR2 (C (A 3) (slot 1)), C nounR2 (C lst (A 9)),
    C nounR2 (C (C (A 1) (A 2)) (n2 (A 4) (slot 3)))]
  [ (Nomm.n7 callR (Nomm.n0 1), n3 (A 7) callRF (slot 1), sR),
    (Nomm.n7 callR3 (Nomm.n4 (Nomm.n0 1)), n3 (A 7) callR3F (n2 (A 4) (slot 1)), sAny),
    (Nomm.n2 callR (Nomm.n1 (slot 1)) Option.none, n3 (A 2) callRF (quote (slot 1)), sR),
    (Nomm.n2 (Nomm.n0 1) callR2 Option.none, n3 (A 2) (slot 1) callR2F, sR2),
    (Nomm.n2 callR3 callR2 Option.none, n3 (A 2) callR3F callR2F, sR2),
    (Nomm.n3 callR3, n2 (A 3) callR3F, sAny),
    (Nomm.n5 callR (Nomm.n0 3), n3 (A 5) callRF (slot 3), sR),
    (Nomm.cons (Nomm.n4 callR3) callR, C (n2 (A 4) callR3F) callRF, sR),
    (Nomm.cons callR3 (Nomm.n4 callR3), C callR3F (n2 (A 4) callR3F), sAny),
    (callRR, callRRF, sR),
    (Nomm.n4 callRR, n2 (A 4) callRRF, sR),
    (Nomm.cons callRR (Nomm.n0 2), C callRRF (slot 2), sR),
    (Nomm.n7 (Nomm.cons (Nomm.n1 nounR2) (Nomm.cons callR3 (Nomm.n0 1))) (Nomm.n4 callR2),
      n3 (A 7) (C (quote nounR2) (C callR3F (slot 1))) (n2 (A 4) callR2F), sAny) ]

/-- Every (case, need, cape) that compiles: its index, the subjects checked,
whether all agree with `+mink`. -/
def calAll : List ((Nat × Nat × Nat) × Nat × Bool) :=
  (calCases.zipIdx).flatMap fun ((nm, f, ss), i) =>
    (naryOrds.zipIdx).flatMap fun (ord, j) =>
      (naryCapes.zipIdx).filterMap fun (cp, k) =>
        (naryOK nm f ord cp ss).map fun (n, ok) => ((i, j, k), n, ok)

-- every code that compiles agrees with `+mink`
#guard calAll.all fun (_, _, ok) => ok
-- how many compile, how many runs, how many nomms compile at all, how many answers are products
#guard calAll.length = 176
#guard (calAll.map fun (_, n, _) => n).sum = 528
#guard (calCases.zipIdx.filter fun (_, i) => calAll.any fun ((i', _, _), _) => i' = i).length = 13
#guard ((calCases.flatMap fun (nm, _, ss) => naryOrds.flatMap fun o => naryCapes.map fun cp =>
  naryZeros nm o cp ss)).sum = 456


end Comp
end SkaModel
end Formalization
