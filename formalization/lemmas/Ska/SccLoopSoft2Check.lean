import lemmas.Ska.SccLoopSoft2
import lemmas.Ska.SccLoopSoftCheck
import lemmas.Ska.SccLoopMedeData

/-! # `runLCS2` against the real compiler (README Gaps 21.20)

`memDoneLSS2` is `memDoneLSS` of `SccLoopSoftCheck.lean` with `runLCS2`.  Checked on the 65
`%done` compiles of `SccLoopRealData.lean` and the 24 of the 8 extra cases
(`SccLoopMedeData.lean`, `tools/hoon/sccreal.py OUT --extra`): the run's `laz` and `o`, `ord`,
`ned-final`, `need-new`, `sur` and the soft map after the run with its `req`. -/

namespace Formalization.SkaModel.SccLoop.Soft2Check

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData
open Formalization.SkaModel.SccLoop.RealCheck Formalization.SkaModel.SccLoop.SoftCheck

/-- `memDoneLSS` with `runLCS2`. -/
def memDoneLSS2 (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (cape : Cape) (data : Noun)
    (fuel : Nat) : Option (NextL LS × NeedOrd × Need × Out NeedOrd × FM SoftCall) :=
  (runLCS2 (S := LS) (Map := FM) env snd Option.none nm CGoalL.done [] (GenSf.ofGen gen0)).bind
    fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (shapeCol fuel nex.laz cape).bind fun ord =>
      (needOrdAllocRegs ord g1.g).bind fun (nedF, _) =>
        (sureOfS (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape).map fun sur =>
          (nex, ord, nedF, ⟨needToOrd (bakeNeed nedF (Sock.mk cape data)).1, sur⟩, g1.soft)

/-- The whole `%done` compile on `runLCS2`, as `runOkS`; `0` where it agrees, else the first
field that differs (`1` decode, `2` run fails, `3` laz, `4` o, `5` ord, `6` ned-final, `7`
need-new / sur, `8` soft map). -/
def runOkS2 (snd : Nomm → NeedOrd → Bool) (r : DoneRec) : Nat :=
  match decode r with
  | none => 1
  | some d =>
    match memDoneLSS2 (sofOf r (envOf d.mem d.out)) snd d.nm d.cape d.data 64 with
    | none => 2
    | some (nex, ord, nedF, o, sm) =>
      if lazyN nex.laz != lazyN d.laz then 3 else if nex.th.there != r.o then 4 else
      if ord != d.ord then 5 else if nedF != d.nedF then 6 else
      if !(o.nn == d.nn && o.sur == d.sur) then 7 else if softList sm != softDump r then 8 else 0

-- `runLCS2` on all 65 of the corpus, with `snd` all `&` and all `|`.
#guard RealData.recs.all fun r => runOkS2 (fun _ _ => true) r == 0
#guard RealData.recs.all fun r => runOkS2 (fun _ _ => false) r == 0
-- The 8 extra cases give 24 `%done` compiles; `runLCS2` gives all of them but one: the first
-- of `w15`, whose nomm has the static hint `~>(%xx 5)` (`%11`, not in `runLC`: the run fails).
#guard MedeData.recs.length = 24
#guard (MedeData.recs.map (·.cs)).eraseDups = ["w14", "w15", "w17", "w18", "w19", "w20", "w21", "w22"]
#guard MedeData.recs.zipIdx.all fun (r, i) =>
  runOkS2 (fun _ _ => true) r == (if i = 3 then 2 else 0) &&
  runOkS2 (fun _ _ => false) r == (if i = 3 then 2 else 0)
#guard (MedeData.recs[3]?.map fun r => r.cs == "w15" && (r.nomm.splitOn "[11 [30840 ").length > 1) == some true
-- The soft compiles whose run records a `req` (the first `%done` compile of each case's soft
-- member): 8, one per case; `runLCS` fails on exactly these (on 7 by the soft map, the `w15`
-- one by the hint), so `runLCS2` is the fix and the guards see it.
def hasReq (r : DoneRec) : Bool :=
  r.soft.any fun s => match nounOfStr s with
    | Noun.cell _ c =>
      let rec last : Nat → Noun → Noun
        | 0, n => n
        | k + 1, Noun.cell _ t => last k t
        | _ + 1, n => n
      last 11 c != A 0
    | _ => false
#guard (MedeData.recs.zipIdx.filter fun (r, _) => hasReq r).map (·.2) = [0, 3, 7, 9, 12, 15, 18, 21]
#guard MedeData.recs.zipIdx.all fun (r, i) => runOkS (fun _ _ => true) r == !(hasReq r)
#guard RealData.recs.all fun r => !(hasReq r)

end Formalization.SkaModel.SccLoop.Soft2Check
