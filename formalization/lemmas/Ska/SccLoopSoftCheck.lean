import lemmas.Ska.SccLoopSoft
import lemmas.Ska.SccLoopRealCheck

/-! # `memDoneMS` against the real compiler, soft calls included (README Gaps 21.15)

The 65 `%done` compiles of `SccLoopRealData.lean` (`tools/hoon/sccreal.py`), now with the soft
map after the run (`soft`, each entry `[o soft-call]`).  `memDoneLSS` is the body of
`memDoneMS` over `LS`, `FM`.  The environment is `envOf` of `SccLoopRealCheck.lean` with `sof`
true exactly at the callees of the dumped soft entries (`sofOf`: `+sound`, `+need-soft` and
`+hinted` are not modelled, so `sof` stays a parameter read from the dump).  Checked:

* `runOkS`: on all 65, `runLCS` gives the dumped `laz` and `o`, the chain after it the dumped
  `ord`, `ned-final`, `need-new` and `sur`, and the final `soft.gen` of the model is the dumped
  soft map (as nouns, sorted by block);
* the same with `snd` (`+sound`, read by `+soft-fork` only) all `&` and all `|`: the corpus does
  not depend on it;
* on the 59 compiles without a soft call, `runLCS` from an empty map ends with an empty map. -/

namespace Formalization.SkaModel.SccLoop.SoftCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData
open Formalization.SkaModel.SccLoop.RealCheck

/-- A `soft-call` as the noun the dump prints (`aux` is `~`: no `%mean` here). -/
def softNoun (o : Nat) (c : SoftCall) : Noun :=
  C (A o) (C (A (if c.kin = 1 then 1818845556 else if c.kin = 0 then 1819042147 else 1851876717))
    (C c.b.toNoun (C (match c.rin with | none => A 0 | some r => C (A 0) r) (C c.ned.toNoun
      (C c.sur.toNoun (C (A c.plain) (C (A c.head) (C (A c.last) (C (A c.pro) (C (A c.out) (C (A 0)
        (c.req.foldr (fun (s, n) acc => C (C (A s) n.toNoun) acc) (A 0)))))))))))))

/-- The entries of a soft map, sorted by block. -/
def softList (m : FM SoftCall) : List Noun :=
  ((m.ks.eraseDups.mergeSort).filterMap fun k => (m.f k).map (softNoun k))

/-- The dumped soft map, sorted by block. -/
def softDump (r : DoneRec) : List Noun :=
  let ns := r.soft.map nounOfStr
  let key : Noun → Nat := fun n => match n with | Noun.cell (Noun.atom o) _ => o | _ => 0
  ns.mergeSort fun a b => key a ≤ key b

/-- The callees of the dumped soft entries. -/
def softBells (r : DoneRec) : List Noun :=
  r.soft.filterMap fun s => match nounOfStr s with
    | Noun.cell _ (Noun.cell _ (Noun.cell b _)) => some b
    | _ => none

/-- `sof` from the dump: true at the callees of the soft entries. -/
def sofOf (r : DoneRec) (e : CallEnv) : CallEnv :=
  { e with sof := fun _ _ _ b _ => (softBells r).contains b.toNoun }

/-- `memDoneMS` over `LS`, `FM`, with `sureOfS`, returning the run, `ned-final` and the soft map. -/
def memDoneLSS (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (cape : Cape) (data : Noun)
    (fuel : Nat) : Option (NextL LS × NeedOrd × Need × Out NeedOrd × FM SoftCall) :=
  (runLCS (S := LS) (Map := FM) env snd Option.none nm CGoalL.done [] (GenSf.ofGen gen0)).bind
    fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (shapeCol fuel nex.laz cape).bind fun ord =>
      (needOrdAllocRegs ord g1.g).bind fun (nedF, _) =>
        (sureOfS (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape).map fun sur =>
          (nex, ord, nedF, ⟨needToOrd (bakeNeed nedF (Sock.mk cape data)).1, sur⟩, g1.soft)

/-- **The whole `%done` compile with soft calls.** -/
def runOkS (snd : Nomm → NeedOrd → Bool) (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    match memDoneLSS (sofOf r (envOf d.mem d.out)) snd d.nm d.cape d.data 64 with
    | none => false
    | some (nex, ord, nedF, o, sm) =>
      lazyN nex.laz == lazyN d.laz && nex.th.there == r.o && ord == d.ord && nedF == d.nedF &&
        o.nn == d.nn && o.sur == d.sur && softList sm == softDump r

#guard (recs.filter (! ·.nosoft)).length = 6
#guard recs.all fun r => r.nosoft == r.soft.isEmpty
-- every soft compile has one soft call, a tail call
#guard (recs.filter (! ·.nosoft)).all fun r => r.soft.length == 1
-- The whole `memDoneMS` on all 65, with the soft map.
#guard recs.all (runOkS fun _ _ => true)
#guard recs.all (runOkS fun _ _ => false)

end Formalization.SkaModel.SccLoop.SoftCheck
