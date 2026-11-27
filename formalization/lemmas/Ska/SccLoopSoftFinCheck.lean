import lemmas.Ska.SccLoopSoftFin
import lemmas.Ska.SccLoopSoftCheck

/-! # `finish` with soft calls against the real compiler (README Gaps 21.16)

The 65 `%done` compiles of `SccLoopRealData.lean` (`tools/hoon/sccreal.py`), now with the soft
map after `+coerce-lazy` inside `finish` (`csoft`) and the straight `(finish ~)` returns
(`zneed`, `znargs`, `zblocks`: its need, argument count and `~(tap by blocks)`).  Checked over
`LS`, `FM`, with the environment of `SccLoopSoftCheck.lean` (`sofOf`, `envOf`) and the bake
`bakeNeed · [cape data]`:

* `finOk`: on all 65 compiles `finishLFCS` returns the dumped straight: the need, the argument
  count and every block (as nouns, sorted by label), the 6 soft compiles included;
* `csoftOk`: on all 65 the soft map after the model's `+coerce-lazy` is the dumped one (the 6
  soft compiles have 3 requirements each, all `%this` or `%none`, so `+soft-emit` makes no try);
* on the 59 compiles without a soft call `finishLFCS` is `finishLFC`. -/

namespace Formalization.SkaModel.SccLoop.SoftFinCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData
open Formalization.SkaModel.SccLoop.RealCheck Formalization.SkaModel.SccLoop.SoftCheck

/-- `~(tap by m)` of an `FM` (its keys, deduplicated; the corpus's soft maps have one entry). -/
def tapFM {ν : Type} (m : FM ν) : List (Nat × ν) :=
  m.ks.eraseDups.filterMap fun k => (m.f k).map fun v => (k, v)

/-- The blocks of a straight, `[o blob]`, sorted by label. -/
def blockList (m : FM Blob) : List Noun :=
  (m.ks.eraseDups.mergeSort).filterMap fun k => (m.f k).map fun b => C (A k) b.toNoun

/-- The dumped blocks, sorted by label. -/
def blockDump (r : DoneRec) : List Noun :=
  let key : Noun → Nat := fun n => match n with | Noun.cell (Noun.atom o) _ => o | _ => 0
  (r.zblocks.map nounOfStr).mergeSort fun a b => key a ≤ key b

/-- The run and `+coerce-lazy` of `finishLFCS`, returning the soft map after it. -/
def coerceSoft (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (ord : NeedOrd)
    (less : Cape) : Option (FM SoftCall) :=
  (runLCS (S := LS) (Map := FM) env snd Option.none nm CGoalL.done [] (GenSf.ofGen gen0)).bind
    fun (nex, g1) =>
    (needOrdAllocRegs ord g1.g).bind fun (nedFinal, g2) =>
      (coerceLazyLS nedFinal less nex.th.there nex.laz ⟨g2, g1.soft⟩).map fun (_, g3) => g3.soft

def finOf (r : DoneRec) (d : Dec) : Option (Straight FM) :=
  finishLFCS (S := LS) (Map := FM) (sofOf r (envOf d.mem d.out)) (fun _ _ => true) tapFM d.nm d.ord
    d.cape (fun ned => bakeNeed ned (Sock.mk d.cape d.data))

/-- **The straight of `(finish ~)`**: need, argument count and blocks. -/
def finOk (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    match finOf r d with
    | none => false
    | some st => st.need.toNoun == nounOfStr r.zneed && st.nargs == r.znargs &&
        blockList st.blocks == blockDump r

/-- The soft map after `+coerce-lazy`. -/
def csoftOk (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    match coerceSoft (sofOf r (envOf d.mem d.out)) (fun _ _ => true) d.nm d.ord d.cape with
    | none => false
    | some sm => softList sm == (r.csoft.map nounOfStr).mergeSort fun a b =>
        (match a with | Noun.cell (Noun.atom o) _ => o | _ => 0) ≤
        (match b with | Noun.cell (Noun.atom o) _ => o | _ => 0)

/-- Without a soft call, `finishLFCS` is `finishLFC`. -/
def sameOk (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    match finOf r d, finishLFC (S := LS) (Map := FM) (sofOf r (envOf d.mem d.out)) d.nm d.ord d.cape
        (fun ned => bakeNeed ned (Sock.mk d.cape d.data)) with
    | some a, some b => a.need == b.need && a.nargs == b.nargs && blockList a.blocks == blockList b.blocks
    | _, _ => false

-- every soft compile has 3 requirements after `+coerce-lazy`, all `%this` or `%none`
#guard (recs.filter (! ·.nosoft)).all fun r => r.csoft.length == 1
#guard recs.all csoftOk
#guard recs.all finOk
#guard (recs.filter (·.nosoft)).all sameOk

end Formalization.SkaModel.SccLoop.SoftFinCheck
