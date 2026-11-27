import lemmas.Ska.CompDirectMCloseEx
import lemmas.Ska.CompUnproxyFill

/-!
# The n-ary top with calls, checked before it is proved

README Gaps 18.15 (a).  `finishTopF_genB` (`CompNaryTop.lean`) states that
the n-ary code `finishLFC` (`+need-ord-alloc-regs`, `+coerce-lazy`,
`+to-straight` with proxies) of a nomm whose run under `%done` meets
`RunOKGB` does what the run's relation says, entered with the split of the
subject by the code's need, on every subject with the axes of the cape.  Two
facts carry it, and both are checked here on the real model:

* `naryOK`: the code, run by the interpreter model on the table of `R-bell`
  and `R2-bell` (`tableRR2`: their real n-ary and whole-subject entries, so a
  direct call runs the callee's compiled code, and an indirect call runs
  `+mink` with the level's fuel), entered with `split c.need s`, agrees with
  `+mink` on the nomm's formula.
* `naryRegs`: the ops `+coerce-lazy` puts in front of the entry block and of
  every lazy entry name only registers of the final need, of the need taken
  there, or registers from the state `+coerce-lazy` starts at
  (`coerceLazyL_regs`), and no key of the final `cond`, so `unproxy` leaves
  them alone; the entry block is no lazy entry (`DoneOK.nent`); and the code
  of the entry block is those ops in front of the run's block.

The cases: 35 nomms (indirect calls under a cons, `%7`, `%4`, `%3`, `%5`;
direct calls of `R` and `R2` as a tail call, under `%4`, in a cons, after a
`%7`, with a `p` that is not `[0 1]`; `R` and `R2` themselves; six of them make proxies, 17 have lazy entries), each under
the needs `this`, `[this this]`, `[~ this]`, `[this ~]`, `[[this this] this]`
and the capes `|`, `[| |]`, `[& |]`, `[| &]`, on subjects that have the cape's
axes.  Every code that compiles (348) is checked on every subject it splits
(1163 runs, 998 of them products).  No disagreement.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The nomm of `R2`: `[6 [3 [0 6]] [7 [10 [6 [0 13]] [0 1]] [2 [0 1] [1 R2] [R2-bell ~]]] [0 7]]`. -/
def nommR2 : Nomm :=
  Nomm.n6 (Nomm.n3 (Nomm.n0 6)) (Nomm.n7 (Nomm.n10 6 (Nomm.n0 13) (Nomm.n0 1)) callR2) (Nomm.n0 7)

/-- The n-ary entry of `R2-bell`. -/
def r2N : Option (Straight FM) :=
  finishLFC (S := LS) envD nommR2 (NeedOrd.pair NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.this))
    (Cape.cell Cape.yes Cape.no) (fun ned => (ned, []))

/-- The whole-subject entry of `R2-bell`. -/
def r2W : Option (Straight FM) := finishLUCM (S := LS) envD nommR2

/-- The table of `R-bell` and `R2-bell`, their real entries. -/
def tableRR2 : Table FM := fun b m =>
  if b = bellR then (if m then rW else rN) else if b = bellR2 then (if m then r2W else r2N) else Option.none

#guard r2N.map (·.need) == envD.need bellR2
#guard r2W.isSome

/-- The n-ary code of `nm` for `ord` and `less`. -/
def naryCode (nm : Nomm) (ord : NeedOrd) (less : Cape) : Option (Straight FM) :=
  finishLFC (S := LS) envD nm ord less (fun ned => (ned, []))

/-- Whether a subject has the axes of the cape (`CapeAxes`). -/
def capeOK : Cape → Noun → Bool
  | Cape.cell h t, Noun.cell a b => capeOK h a && capeOK t b
  | Cape.cell _ _, Noun.atom _ => false
  | _, _ => true

/-- **The n-ary code agrees with `+mink`** on every subject that has the
cape's axes and splits by the code's need; `none` when it does not compile,
else the number of subjects checked and whether all agree. -/
def naryOK (nm : Nomm) (f : Noun) (ord : NeedOrd) (less : Cape) (ss : List Noun) : Option (Nat × Bool) :=
  (naryCode nm ord less).map fun c =>
    ss.foldl (fun (acc : Nat × Bool) s =>
      if capeOK less s then
        match SkaModel.split c.need s with
        | some args =>
          (acc.1 + 1, acc.2 && (execEntry libT (tableOracle libT tableRR2 12) () c args [] (A 0)).map Prod.fst ==
            minkF libT (A 0) 800 [] s f)
        | Option.none => acc
      else acc) (0, true)

/-- **The registers of the coerced ops**, replayed step by step as
`finishLFC` runs: at the entry block and at every lazy entry, the block after
`+coerce-lazy` is ops `A` in front of the run's block, every register of `A`
is in the final need, in the need taken there, or at least the `re` that
`+coerce-lazy` starts from, and no key of the final `cond`; the entry block
is no lazy entry. -/
def naryRegs (nm : Nomm) (ord : NeedOrd) (less : Cape) : Bool :=
  match (runLC (S := LS) (Map := FM) envD Option.none nm (CGoalL.done : CGoalL LS) [] gen0) with
  | some (nex, g1) =>
    match (needOrdAllocRegs ord g1 : Option (Need × Gen FM)) with
    | some (nedF, g2) =>
      match (coerceLazyL nedF less nex.th.there nex.laz g2 : Option (Unit × Gen FM)) with
      | some (_, g3) =>
        !(((entries nex.laz).map Prod.fst).contains nex.th.there) &&
        ((nex.th.there, nex.laz) :: entries nex.laz).all fun e =>
          match g1.blocks.f e.1, g3.blocks.f e.1 with
          | some b1, some b3 =>
            let k := b3.body.length - b1.body.length
            b3.par == b1.par && b3.fin == b1.fin && b3.body.drop k == b1.body &&
            (b3.body.take k).all fun p => (poleRegs p).all fun x =>
              (g3.cond.f x).isNone &&
                ((flattenNeed nedF).contains x || (flattenNeed e.2.sure.ned).contains x || decide (g2.re ≤ x))
          | _, _ => false
      | Option.none => false
    | Option.none => false
  | Option.none => false

/-- Whether the run of `nm` makes a proxy (a key of `cond`) and whether its
result has lazy entries: the two things the register clause is about. -/
def naryShape (nm : Nomm) : Bool × Bool :=
  match (runLC (S := LS) (Map := FM) envD Option.none nm (CGoalL.done : CGoalL LS) [] gen0) with
  | some (nex, g1) => (!g1.cond.ks.isEmpty, !(entries nex.laz).isEmpty)
  | Option.none => (false, false)

/-- The answers of the code that are products, over the subjects checked. -/
def naryZeros (nm : Nomm) (ord : NeedOrd) (less : Cape) (ss : List Noun) : Nat :=
  match naryCode nm ord less with
  | some c => (ss.filter fun s => capeOK less s && match SkaModel.split c.need s with
      | some args => match execEntry libT (tableOracle libT tableRR2 12) () c args [] (A 0) with
        | some (Tone.zero _, _) => true
        | _ => false
      | Option.none => false).length
  | Option.none => 0

/-- `[2 [0 2] [0 3]]`. -/
def ind23 : Nomm := Nomm.n2 (Nomm.n0 2) (Nomm.n0 3) Option.none
def ind23F : Noun := n3 (A 2) (slot 2) (slot 3)

/-- `[2 [0 1] [1 R] R-bell]` with `p = [[1 R] [0 3]]`: `R` on `[R s/3]`. -/
def callR3 : Nomm := Nomm.n2 (Nomm.cons (Nomm.n1 nounR) (Nomm.n0 3)) (Nomm.n1 nounR) (some (bellR, Option.none))
def callR3F : Noun := n3 (A 2) (C (quote nounR) (slot 3)) (quote nounR)

/-- `R`'s call itself, on its subject. -/
def callRF : Noun := n3 (A 2) (slot 1) (quote nounR)
def callR2F : Noun := n3 (A 2) (slot 1) (quote nounR2)

/-- The formula of `nommR`, as the nomm reads it. -/
def nommRF : Noun := C (A 6) (C (n2 (A 3) (slot 3)) (C (n3 (A 7) (n3 (A 10) (C (A 3) (slot 7)) (slot 1)) callRF) (slot 3)))
def nommR2F : Noun :=
  C (A 6) (C (n2 (A 3) (slot 6)) (C (n3 (A 7) (n3 (A 10) (C (A 6) (slot 13)) (slot 1)) callR2F) (slot 7)))

/-- The formula of `etNomm`. -/
def etFolD : Noun := n3 (A 7) (C (quote nounR2) (slot 1)) (n3 (A 7) (slot 1) callR2F)

/-- The cases: nomm, formula, subjects. -/
def naryCases : List (Nomm × Noun × List Noun) :=
  let sInd : List Noun := [C (C (A 5) (A 6)) (C (A 0) (A 1)), C (C (A 5) (A 6)) (C (A 0) (A 2)),
    C (C (A 5) (A 6)) (C (A 4) (C (A 0) (A 3))), C (A 5) (C (A 0) (A 1)), C (C (A 5) (A 6)) (A 9)]
  let lst : Noun := C (A 1) (C (A 2) (C (A 3) (A 4)))
  let sAny : List Noun := [A 7, C (A 1) (A 2), C (A 0) lst, C (C (A 1) (A 2)) (C (A 3) (A 4))]
  let sR : List Noun := [C nounR (A 7), C nounR lst, C nounR (C (A 0) (C (A 0) (A 0)))]
  let sR2 : List Noun := [C nounR2 (C lst (A 9)), C nounR2 (C (A 3) (A 9)), C nounR2 (A 3),
    C nounR2 (C (C (A 1) (C (A 2) (A 3))) (C (A 8) (A 9)))]
  [ (ind23, ind23F, sInd),
    (Nomm.cons ind23 (Nomm.n0 2), C ind23F (slot 2), sInd),
    (Nomm.cons (Nomm.n0 3) ind23, C (slot 3) ind23F, sInd),
    (Nomm.n4 ind23, n2 (A 4) ind23F, sInd),
    (Nomm.n3 ind23, n2 (A 3) ind23F, sInd),
    (Nomm.n5 ind23 (Nomm.n0 2), n3 (A 5) ind23F (slot 2), sInd),
    (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)) ind23, n3 (A 7) (C (slot 3) (slot 2)) ind23F,
      [C (C (A 0) (A 1)) (C (A 5) (A 6)), C (C (A 4) (C (A 0) (A 3))) (A 8), A 3]),
    (Nomm.n2 (Nomm.n0 2) (Nomm.n1 (slot 3)) Option.none, n3 (A 2) (slot 2) (quote (slot 3)), sInd),
    (Nomm.n2 ind23 (Nomm.n0 3) Option.none, n3 (A 2) ind23F (slot 3),
      [C (C (C (A 5) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 3)), C (A 0) (A 1)]),
    (Nomm.n4 (Nomm.n4 ind23), n2 (A 4) (n2 (A 4) ind23F), sInd),
    (Nomm.cons ind23 ind23, C ind23F ind23F, sInd),
    (dtNomm, dtFolD, sAny),
    (Nomm.n4 dtNomm, n2 (A 4) dtFolD, [C (A 0) (C (A 0) (A 0)), A 3, C (A 1) (A 2)]),
    (Nomm.cons dtNomm (Nomm.n0 1), C dtFolD (slot 1), sAny),
    (Nomm.cons (Nomm.n0 1) dtNomm, C (slot 1) dtFolD, sAny),
    (Nomm.n7 (Nomm.n0 3) dtNomm, n3 (A 7) (slot 3) dtFolD, sAny),
    (Nomm.n3 dtNomm, n2 (A 3) dtFolD, sAny),
    (Nomm.n5 dtNomm (Nomm.n0 3), n3 (A 5) dtFolD (slot 3), sAny),
    (callR, callRF, sR),
    (Nomm.n4 callR, n2 (A 4) callRF, [C nounR (C (A 0) (A 0)), C nounR (A 0)]),
    (Nomm.cons callR (Nomm.n0 3), C callRF (slot 3), sR),
    (callR3, callR3F, sAny),
    (Nomm.n4 callR3, n2 (A 4) callR3F, [C (A 0) (C (A 0) (A 0)), C (A 1) (A 2)]),
    (nommR, nommRF, sR),
    (Nomm.n4 nommR, n2 (A 4) nommRF, sR),
    (etNomm, etFolD, [C (C (A 1) (A 2)) (A 3), A 7, C (A 7) (A 3), C (C (A 1) (C (A 2) (A 0))) (A 5)]),
    (Nomm.n4 etNomm, n2 (A 4) etFolD, [C (C (A 1) (A 2)) (A 3), C (A 7) (A 3)]),
    (nommR2, nommR2F, sR2),
    (callR2, callR2F, sR2),
    (Nomm.cons dtNomm etNomm, C dtFolD etFolD, [C (C (A 1) (A 2)) (A 3), C (A 7) (A 3)]),
    (Nomm.n2 (Nomm.n0 2) (Nomm.n1 dtFolD) Option.none, n3 (A 2) (slot 2) (quote dtFolD),
      [C (C (A 0) (A 1)) (A 0), C (A 5) (A 6)]),
    (Nomm.cons (Nomm.n4 ind23) ind23, C (n2 (A 4) ind23F) ind23F, sInd),
    (Nomm.cons ind23 (Nomm.cons ind23 (Nomm.n0 1)), C ind23F (C ind23F (slot 1)), sInd),
    (Nomm.cons dtNomm dtNomm, C dtFolD dtFolD, sAny),
    (Nomm.cons callR callR, C callRF callRF, sR) ]

def naryOrds : List NeedOrd :=
  [NeedOrd.this, NeedOrd.pair NeedOrd.this NeedOrd.this, NeedOrd.pair NeedOrd.none NeedOrd.this,
   NeedOrd.pair NeedOrd.this NeedOrd.none,
   NeedOrd.pair (NeedOrd.pair NeedOrd.this NeedOrd.this) NeedOrd.this,
   NeedOrd.pair NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.this)]

def naryCapes : List Cape :=
  [Cape.no, Cape.cell Cape.no Cape.no, Cape.cell Cape.yes Cape.no, Cape.cell Cape.no Cape.yes]

/-- Every (case, need, cape) that compiles: its index, the subjects checked,
whether all agree with `+mink`, and whether the registers are as stated. -/
def naryAll : List ((Nat × Nat × Nat) × Nat × Bool × Bool) :=
  (naryCases.zipIdx).flatMap fun ((nm, f, ss), i) =>
    (naryOrds.zipIdx).flatMap fun (ord, j) =>
      (naryCapes.zipIdx).filterMap fun (cp, k) =>
        (naryOK nm f ord cp ss).map fun (n, ok) => ((i, j, k), n, ok, naryRegs nm ord cp)

-- every code that compiles agrees with `+mink`, and its coerced ops are where `coerceLazyL_regs` says
#guard naryAll.all fun (_, _, ok, rg) => ok && rg
-- how many compile, how many runs were checked, how many nomms compile at all
#guard naryAll.length = 348
#guard (naryAll.map fun (_, n, _, _) => n).sum = 1163
#guard (naryCases.zipIdx.filter fun (_, i) => naryAll.any fun ((i', _, _), _) => i' = i).length = 35
-- of the answers, 998 are products; six runs make proxies, with direct calls among them;
-- 17 have lazy entries
#guard ((naryCases.flatMap fun (nm, _, ss) => naryOrds.flatMap fun o => naryCapes.map fun cp =>
  naryZeros nm o cp ss)).sum = 998
#guard (naryCases.filter fun (nm, _, _) => (naryShape nm).1).length = 6
#guard (naryCases.filter fun (nm, _, _) => (naryShape nm).2).length = 17

end Comp
end SkaModel
end Formalization
