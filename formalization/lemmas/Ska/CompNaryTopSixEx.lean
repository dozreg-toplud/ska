import lemmas.Ska.CompNaryTopRecEx

/-!
# `[6 c a b]` with direct calls: the guards (checked before the proofs)

README Gaps 18.16, step 1.  The whole-subject code (`finishLUCM`) and the
n-ary code (`finishLFC`, under the six needs and four capes of
`CompNaryTopEx.lean`, entered with the split) of nomms `[6 c a b]` with a
direct call of `R` in a branch (a tail call, a tail call behind `%7`, a call
under `%4` or in a cons), in both branches, in the test's operand (`%3`,
`%5`), nested in a branch, under a `%7`, and `R` itself, run by the
interpreter model on the table of `R`'s and `R2`'s real entries
(`tableRR2`), agree with `+mink` on every subject.

* `sixCases`, `sixWhole`, `sixAll`: 22 nomms; every whole-subject code
  compiles and agrees on its subjects (126 runs), and so does every n-ary
  code that compiles (200 codes, 956 runs, 936 of them products).
* `nommLW`, the terminating walker of step 5: `[6 [3 [0 3]] [2 [[0 2] [0 7]]
  [0 2]] [0 3]]` on `[L x]` calls itself on `[L x.tail]` while `x` is a cell
  and returns the atom that ends `x`.  Both its entries, on the table of
  themselves, return that atom (a product) as `+mink` does.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `[3 [0 2]]` and `[3 [0 3]]` as tests. -/
def t2 : Nomm := Nomm.n3 (Nomm.n0 2)
def t2F : Noun := n2 (A 3) (slot 2)
def t3 : Nomm := Nomm.n3 (Nomm.n0 3)
def t3F : Noun := n2 (A 3) (slot 3)

/-- `[7 [[1 R] [0 3]] [2 [0 1] [1 R] R-bell]]`: `R` on `[R s/3]` behind a `%7`. -/
def callR7 : Nomm := Nomm.n7 (Nomm.cons (Nomm.n1 nounR) (Nomm.n0 3)) callR
def callR7F : Noun := n3 (A 7) (C (quote nounR) (slot 3)) callRF

/-- The cases `(nm, its formula, subjects)`. -/
def sixCases : List (Nomm × Noun × List Noun) :=
  let lst : Noun := C (A 1) (C (A 2) (C (A 3) (A 4)))
  let sAny : List Noun := [A 7, C (A 1) (A 2), C (C (A 1) (A 2)) lst, C (C (A 1) (A 2)) (C (A 3) (A 4)),
    C (A 0) lst, C (C (A 0) (A 0)) (A 9)]
  let sR : List Noun := [C nounR (A 7), C nounR lst, C nounR (C (A 0) (C (A 0) (A 0)))]
  let s6 := fun (c a b : Noun) => n4 (A 6) c a b
  [ -- a tail call in the yes branch, the no branch, both
    (Nomm.n6 t2 callR3 (Nomm.n0 3), s6 t2F callR3F (slot 3), sAny),
    (Nomm.n6 t2 (Nomm.n0 3) callR3, s6 t2F (slot 3) callR3F, sAny),
    (Nomm.n6 t2 callR3 callR3, s6 t2F callR3F callR3F, sAny),
    -- a tail call behind `%7` (the form of `R`'s own yes branch)
    (Nomm.n6 t2 callR7 (Nomm.n0 3), s6 t2F callR7F (slot 3), sAny),
    (Nomm.n6 t3 (Nomm.n0 2) callR7, s6 t3F (slot 2) callR7F, sAny),
    -- non-tail calls: under `%4`, in a cons, under `%3`
    (Nomm.n6 t2 (Nomm.n4 callR3) (Nomm.n0 2), s6 t2F (n2 (A 4) callR3F) (slot 2), sAny),
    (Nomm.n6 t2 (Nomm.n0 2) (Nomm.n4 callR3), s6 t2F (slot 2) (n2 (A 4) callR3F), sAny),
    (Nomm.n6 t2 (Nomm.cons callR3 (Nomm.n0 2)) (Nomm.n0 3), s6 t2F (C callR3F (slot 2)) (slot 3), sAny),
    (Nomm.n6 t3 (Nomm.n3 callR3) (Nomm.cons (Nomm.n0 2) callR7), s6 t3F (n2 (A 3) callR3F) (C (slot 2) callR7F), sAny),
    (Nomm.n6 t2 (Nomm.n7 (Nomm.cons (Nomm.n1 nounR) (Nomm.n0 3)) (Nomm.n4 callR)) (Nomm.n0 2),
      s6 t2F (n3 (A 7) (C (quote nounR) (slot 3)) (n2 (A 4) callRF)) (slot 2), sAny),
    -- mixed: a tail call and a non-tail one
    (Nomm.n6 t3 callR3 (Nomm.n4 callR3), s6 t3F callR3F (n2 (A 4) callR3F), sAny),
    (Nomm.n6 t2 (Nomm.n4 (Nomm.n4 callR3)) callR7, s6 t2F (n2 (A 4) (n2 (A 4) callR3F)) callR7F, sAny),
    -- the direct call in the test's operand
    (Nomm.n6 (Nomm.n3 callR3) (Nomm.n0 2) (Nomm.n0 3), s6 (n2 (A 3) callR3F) (slot 2) (slot 3), sAny),
    (Nomm.n6 (Nomm.n5 callR3 (Nomm.n1 (A 4))) (Nomm.n0 2) (Nomm.n0 3),
      s6 (n3 (A 5) callR3F (quote (A 4))) (slot 2) (slot 3), sAny),
    (Nomm.n6 (Nomm.n3 callR3) callR3 (Nomm.n4 callR7), s6 (n2 (A 3) callR3F) callR3F (n2 (A 4) callR7F), sAny),
    -- nested in a branch
    (Nomm.n6 t2 (Nomm.n6 t3 callR3 (Nomm.n0 2)) (Nomm.n0 3), s6 t2F (s6 t3F callR3F (slot 2)) (slot 3), sAny),
    (Nomm.n6 t2 (Nomm.n0 3) (Nomm.n6 t3 (Nomm.n0 2) callR7), s6 t2F (slot 3) (s6 t3F (slot 2) callR7F), sAny),
    (Nomm.n6 t2 (Nomm.n6 (Nomm.n3 callR3) callR3 (Nomm.n0 2)) (Nomm.n4 callR3),
      s6 t2F (s6 (n2 (A 3) callR3F) callR3F (slot 2)) (n2 (A 4) callR3F), sAny),
    -- a `%6` as the test, and a `%6` under `%7`
    (Nomm.n6 (Nomm.n6 t2 (Nomm.n1 (A 0)) (Nomm.n1 (A 1))) callR3 (Nomm.n0 3),
      s6 (s6 t2F (quote (A 0)) (quote (A 1))) callR3F (slot 3), sAny),
    (Nomm.n7 (Nomm.n0 1) (Nomm.n6 t2 callR3 (Nomm.n0 3)), n3 (A 7) (slot 1) (s6 t2F callR3F (slot 3)), sAny),
    -- `R` itself and `R2` itself, on their subjects
    (nommR, nounR, sR),
    (Nomm.n6 t3 callR (Nomm.n0 2), s6 t3F callRF (slot 2), sR) ]

/-- The whole-subject code of `nm` on the table of `R` and `R2` (12 levels),
against `+mink`: `none` when it does not compile, else whether every subject
agrees. -/
def sixWholeOK (nm : Nomm) (f : Noun) (ss : List Noun) : Option Bool :=
  (finishLUCM (S := LS) (Map := FM) envD nm).map fun c =>
    ss.all fun s => (execEntry libT (tableOracle libT tableRR2 12) () c [s] [] (A 0)).map Prod.fst ==
      minkF libT (A 0) 800 [] s f

def sixWhole : List (Option Bool) := sixCases.map fun (nm, f, ss) => sixWholeOK nm f ss

/-- Every (case, need, cape) whose n-ary code compiles. -/
def sixAll : List ((Nat × Nat × Nat) × Nat × Bool) :=
  (sixCases.zipIdx).flatMap fun ((nm, f, ss), i) =>
    (naryOrds.zipIdx).flatMap fun (ord, j) =>
      (naryCapes.zipIdx).filterMap fun (cp, k) =>
        (naryOK nm f ord cp ss).map fun (n, ok) => ((i, j, k), n, ok)

-- every whole-subject code compiles and agrees with `+mink`
#guard sixCases.length = 22
#guard sixWhole.all (· == some true)
-- every n-ary code that compiles agrees with `+mink`; how many compile, how many runs
#guard sixAll.all fun (_, _, ok) => ok
#guard sixAll.length = 200
#guard (sixAll.map fun (_, n, _) => n).sum = 956
-- every case has a code that compiles for some need and cape
#guard (sixCases.zipIdx.filter fun (_, i) => sixAll.any fun ((i', _, _), _) => i' = i).length = 22
-- the products among the runs (the rest crash where `+mink` does)
#guard ((sixCases.flatMap fun (nm, _, ss) => naryOrds.flatMap fun o => naryCapes.map fun cp =>
  naryZeros nm o cp ss)).sum = 936

/-! ## The terminating walker `L` (step 5) -/

/-- `L = [6 [3 [0 3]] [2 [[0 2] [0 7]] [0 2]] [0 3]]`. -/
def nounLW : Noun := n4 (A 6) (n2 (A 3) (slot 3)) (n3 (A 2) (C (slot 2) (slot 7)) (slot 2)) (slot 3)
def bellLW : Bell := ⟨walkSock nounLW, nounLW⟩

/-- `L` needs `[~ this]`, is impure, no jet, hinted, no soft call. -/
def envLW : CallEnv :=
  ⟨fun b => if b = bellLW then some walkNeed else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false, fun _ _ _ _ _ => false⟩

/-- Its nomm: the test `[3 [0 3]]`, the self call on `[L x.tail]`, `[0 3]`. -/
def nommLW : Nomm :=
  Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n2 (Nomm.cons (Nomm.n0 2) (Nomm.n0 7)) (Nomm.n0 2) (some (bellLW, Option.none)))
    (Nomm.n0 3)

def naryLW : Option (Straight FM) := finishLFC (S := LS) envLW nommLW walkNeed capeW (fun ned => (ned, []))
def wholeLW : Option (Straight FM) := finishLUCM (S := LS) envLW nommLW
def tableLWg : Table FM := fun b m => if b = bellLW then (if m then wholeLW else naryLW) else Option.none

#guard (naryLW.map (·.need)) == some walkNeed && wholeLW.isSome
#guard envLW.need bellLW == some walkNeed

/-- The atom that ends `x`. -/
def lastAtom : Noun → Noun
  | Noun.atom n => Noun.atom n
  | Noun.cell _ t => lastAtom t

/-- On `[L x]`: `+mink` returns the atom ending `x`, and both entries (the
n-ary one entered with the split) answer the same with `k` levels. -/
def walkRunLW (k : Nat) : Bool :=
  walkXs.all fun x =>
    let s := C nounLW x
    let mk := minkF libT (A 0) 800 [] s nounLW
    mk == some (Tone.zero (lastAtom x)) &&
    (match tableLWg bellLW false, tableLWg bellLW true with
     | some cN, some cW =>
       (match SkaModel.split cN.need s with
        | some args => (execEntry libT (tableOracle libT tableLWg k) () cN args [] (A 0)).map Prod.fst == mk
        | Option.none => false) &&
       (execEntry libT (tableOracle libT tableLWg k) () cW [s] [] (A 0)).map Prod.fst == mk
     | _, _ => false)

#guard walkRunLW 12
-- too few levels: no answer on the longest list (six calls)
#guard match tableLWg bellLW true with
  | some cW => (execEntry libT (tableOracle libT tableLWg 3) () cW [C nounLW (walkXs.getD 4 (A 0))] [] (A 0)).isNone
  | Option.none => false

end Comp
end SkaModel
end Formalization
