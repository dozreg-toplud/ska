import lemmas.Ska.SccLoopSoftTry
import lemmas.Ska.SccLoopSoft2Check
import lemmas.Ska.SccLoopSoftFinCheck

/-! # `finishLFCS2` against the real compiler (README Gaps 21.20)

On the 65 `%done` compiles of the corpus and the 24 of `SccLoopMedeData.lean`: the soft map after
`+coerce-lazy` (`csoft`) and the straight of `(finish ~)` (`zneed`, `znargs`, every block). -/

namespace Formalization.SkaModel.SccLoop.SoftTryCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData
open Formalization.SkaModel.SccLoop.RealCheck Formalization.SkaModel.SccLoop.SoftCheck
open Formalization.SkaModel.SccLoop.SoftFinCheck

/-- The run and `+coerce-lazy` of `finishLFCS2`: the soft map after it. -/
def coerceSoft2 (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (ord : NeedOrd)
    (less : Cape) : Option (FM SoftCall) :=
  (runLCS2 (S := LS) (Map := FM) env snd Option.none nm CGoalL.done [] (GenSf.ofGen gen0)).bind
    fun (nex, g1) =>
    (needOrdAllocRegs ord g1.g).bind fun (nedFinal, g2) =>
      (coerceLazyLS nedFinal less nex.th.there nex.laz ⟨g2, g1.soft⟩).map fun (_, g3) => g3.soft

def finOf2 (r : DoneRec) (d : Dec) : Option (Straight FM) :=
  finishLFCS2 (S := LS) (Map := FM) (sofOf r (envOf d.mem d.out)) (fun _ _ => true) tapFM d.nm d.ord
    d.cape (fun ned => bakeNeed ned (Sock.mk d.cape d.data))

/-- `0` agrees; `1` decode, `2` `finishLFCS2` fails, `3` need, `4` `n-args`, `5` blocks. -/
def finOk2 (r : DoneRec) : Nat :=
  match decode r with
  | none => 1
  | some d =>
    match finOf2 r d with
    | none => 2
    | some st => if st.need.toNoun != nounOfStr r.zneed then 3 else if st.nargs != r.znargs then 4 else
        if blockList st.blocks != blockDump r then 5 else 0

def csoftOk2 (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    match coerceSoft2 (sofOf r (envOf d.mem d.out)) (fun _ _ => true) d.nm d.ord d.cape with
    | none => false
    | some sm => softList sm == (r.csoft.map nounOfStr).mergeSort fun a b =>
        (match a with | Noun.cell (Noun.atom o) _ => o | _ => 0) ≤
        (match b with | Noun.cell (Noun.atom o) _ => o | _ => 0)

/-- Per soft call after `+coerce-lazy`: the number of tries and `+soft-free` (`2` none, `1` `&`, `0` `|`). -/
def tryInfo (r : DoneRec) : List (Nat × Nat) :=
  match decode r with
  | none => []
  | some d =>
    let env := sofOf r (envOf d.mem d.out)
    match (runLCS2 (S := LS) (Map := FM) env (fun _ _ => true) Option.none d.nm CGoalL.done [] (GenSf.ofGen gen0)) with
    | none => []
    | some (nex, g1) =>
      match needOrdAllocRegs d.ord g1.g with
      | none => []
      | some (nedFinal, g2) =>
        match coerceLazyLS nedFinal d.cape nex.th.there nex.laz ⟨g2, g1.soft⟩ with
        | none => []
        | some (_, g3) => (tapFM g3.soft).map fun (o, s) =>
          match softCutsM (Map := FM) (softAxes s.ned 1 []) s.sur s.b.less s.req ([], []) g3.g with
          | none => (99, 99)
          | some ((_, tops), g4) =>
            let tries := softTriesP tops
            (tries.length, match softFreeF g4.blocks s.last ((tries.map fun (_, _, n) => flattenNeed n).flatten) 100000 [o] [] with
              | none => 2 | some true => 1 | some false => 0)

-- The corpus: no try anywhere; `finishLFCS2` gives every straight and every `csoft`.
#guard RealData.recs.all fun r => (tryInfo r).all (·.1 == 0)
#guard RealData.recs.all fun r => finOk2 r == 0
#guard RealData.recs.all csoftOk2
-- The 24 extra compiles: one try in each of the 7 whose run records a `req` (the try path of
-- `+soft-emit`, with `+soft-free` `&`), none elsewhere; the flag path (`+soft-free` `|`) is not
-- reached.  `finishLFCS2` gives all 23 straights and soft maps but the first `w15` (`%11`).
#guard (MedeData.recs.map tryInfo) = [[(1, 1)], [(0, 1)], [(0, 1)], [], [(0, 1)], [(0, 1)], [], [(1, 1)],
  [(0, 1)], [(1, 1)], [], [(0, 1)], [(1, 1)], [(0, 1)], [(0, 1)], [(1, 1)], [(0, 1)], [(0, 1)], [(1, 1)],
  [(0, 1)], [(0, 1)], [(1, 1)], [(0, 1)], [(0, 1)]]
#guard MedeData.recs.zipIdx.all fun (r, i) => finOk2 r == (if i = 3 then 2 else 0)
#guard MedeData.recs.zipIdx.all fun (r, i) => csoftOk2 r == (i != 3)
-- the old `finishLFCS` (no ask, no try) fails on the 7 try compiles
#guard MedeData.recs.zipIdx.all fun (r, i) => (i == 3 || (tryInfo r).any (·.1 > 0)) == !(finOk r)

end Formalization.SkaModel.SccLoop.SoftTryCheck
