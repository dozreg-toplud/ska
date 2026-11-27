import lemmas.Ska.SccLoopSoftShape
import lemmas.Ska.SccLoopSoftCheck
import lemmas.Ska.SccLoopShapeCheck

/-! # `cfgRealSS` against the real compiler: one configuration per SCC (README Gaps 21.19)

The 65 `%done` compiles (`SccLoopRealData.lean`) and the 109 sweep compiles
(`SccLoopShapeData.lean`) of the corpus, grouped by SCC (the case and the members' bells).  For
each SCC ONE configuration is built from all its dumps (`cfgOf`): the members, per member its
nomm, `less.b` and fuel `64` (`infoOf`, the same in every dump of the member: `infoOk`), the
outside callees (`envOut` of the union of the dumps' outside callees, which agree:
`outOk`), `sof` true at the callees of the SCC's dumped soft calls, and the `ShapeX` of the case.
Then every compile of the SCC, `%done` or sweep, is the compile of that configuration at the
dumped views (`compRealSL`, the body of `compRealS` with `laze := lazeRealG`, over `LS`, `FM`):

* `infoOk`, `outOk`: the configuration is well defined (47 SCCs, 9 compiles in SCCs with a soft
  call);
* `compOk`: on all 174, `compRealSL` gives the dumped `Out` (`need-new` and `sur` on `%done`,
  `shape` and `sur` on the sweeps), with `snd` all `&` and all `|`;
* `compOkNS`: with `sof` false the compile differs on 5 of the 6 soft `%done` compiles, and only
  there (the guards see the soft calls). -/

namespace Formalization.SkaModel.SccLoop.SoftShapeCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop
open Formalization.SkaModel.SccLoop.RealCheck

/-- One compile of the corpus, `%done` or a sweep: the case, the bell's mug, the mode, `less.b`,
the nomm, the views, the outside callees, the soft callees, and the dumped `Out`. -/
structure Any where
  cs : String
  b : Nat
  mode : Mode
  less : String
  nomm : String
  mem : List String
  out : List String
  soft : List Noun
  nn : String
  sur : String

def ofDone (r : RealData.DoneRec) : Any :=
  ⟨r.cs, r.b, Mode.done, r.less, r.nomm, r.mem, r.out, SoftCheck.softBells r, r.nn, r.sur⟩

def ofShape (r : ShapeData.ShapeRec) : Any :=
  ⟨r.cs, r.b, if r.must then Mode.must else Mode.may, r.less, r.nomm, r.mem, r.out, [], r.shape, r.sur⟩

def all : List Any := RealData.recs.map ofDone ++ ShapeData.recs.map ofShape

def ents (l : List String) : List Ent := l.filterMap entOf

/-- Two compiles of one SCC: one case, the same members (as sets). -/
def sameScc (a a' : Any) : Bool :=
  a.cs == a'.cs && (ents a.mem).all (fun e => (ents a'.mem).any (·.bell == e.bell)) &&
    (ents a'.mem).all (fun e => (ents a.mem).any (·.bell == e.bell))

/-- The compiles of the SCC of `a`. -/
def sccOf (a : Any) : List Any := all.filter (sameScc a)

/-- The bell of a compile: the member whose dumps have its mug (`ofShape` dumps the bell). -/
def bellOf (a : Any) : Option Noun :=
  match (ShapeData.recs.find? fun r => r.cs == a.cs && r.b == a.b) with
  | some r => some (nounOfStr r.bell)
  | none => match ents a.mem with
    | [e] => some e.bell
    | _ => none

def decInfo (a : Any) : Option MemInfo :=
  match nounOfStr a.less with
  | Noun.cell c d => (nommOf (nounOfStr a.nomm)).map fun nm => ⟨nm, capeOf c, d, 64⟩
  | _ => none

/-- The configuration of the SCC of `a`. -/
structure SccCfg where
  scc : List Noun
  info : Noun → MemInfo
  env : CallEnv
  xs : ShapeX

def bunt : MemInfo := ⟨Nomm.n0 0, Cape.no, A 0, 0⟩

def cfgOf (a : Any) : SccCfg :=
  let cs := sccOf a
  let mem := ents a.mem
  let out := cs.foldl (fun acc a' => acc ++ ents a'.out) []
  let soft := cs.foldl (fun acc a' => acc ++ a'.soft) []
  let e := envOut mem out
  ⟨mem.map (·.bell),
   fun k => ((cs.find? fun a' => bellOf a' == some k).bind decInfo).getD bunt,
   { e with sof := fun _ _ _ b _ => soft.contains b.toNoun },
   ShapeCheck.shapeXOf a.cs mem out⟩

/-- **`compRealS` with `laze := lazeRealG`, over `LS`, `FM`** (the `Option` kept). -/
def compRealSL (c : SccCfg) (snd : Nomm → NeedOrd → Bool) (b : Noun) (mode : Mode) (vn vs : Noun → NeedOrd) :
    Option (Out NeedOrd) :=
  let e := envView c.env c.scc vn vs
  let m := c.info b
  match mode with
  | Mode.done => (SoftCheck.memDoneLSS e snd m.nm m.cape m.data m.fuel).map (·.2.2.2.1)
  | _ => (lazeRealG (S := LS) c.xs mode e m).map fun p => ⟨bakeNeedOrd p.1 (Sock.mk m.cape m.data), p.2⟩

/-- The info of every member is the same in every dump of it. -/
def infoOk (a : Any) : Bool :=
  match bellOf a, decInfo a with
  | some k, some m => let i := (cfgOf a).info k
      i.nm.toNoun == m.nm.toNoun && i.cape == m.cape && i.data == m.data
  | _, _ => false

/-- The outside callees of every dump of the SCC agree on each callee. -/
def outOk (a : Any) : Bool :=
  let es := (sccOf a).foldl (fun acc a' => acc ++ ents a'.out) []
  es.all fun e => es.all fun e' => e.bell != e'.bell || (e.need == e'.need && e.sure == e'.sure && e.pure == e'.pure && e.jet == e'.jet)

/-- **The compile of the SCC's configuration at the dumped views is the dumped `Out`.** -/
def compOk (snd : Nomm → NeedOrd → Bool) (a : Any) : Bool :=
  let mem := ents a.mem
  match bellOf a, ordOf (nounOfStr a.nn), ordOf (nounOfStr a.sur) with
  | some k, some nn, some sur =>
    compRealSL (cfgOf a) snd k a.mode (fun k => ((look mem k).map (·.need)).getD NeedOrd.none)
      (fun k => ((look mem k).map (·.sure)).getD NeedOrd.none) == some ⟨nn, sur⟩
  | _, _, _ => false

/-- `compOk` with `sof` false at every call (the configuration without soft calls). -/
def compOkNS (a : Any) : Bool :=
  let mem := ents a.mem
  let c := cfgOf a
  match bellOf a, ordOf (nounOfStr a.nn), ordOf (nounOfStr a.sur) with
  | some k, some nn, some sur =>
    compRealSL { c with env := { c.env with sof := fun _ _ _ _ _ => false } } (fun _ _ => true) k a.mode
      (fun k => ((look mem k).map (·.need)).getD NeedOrd.none)
      (fun k => ((look mem k).map (·.sure)).getD NeedOrd.none) == some ⟨nn, sur⟩
  | _, _, _ => false

/-- The number of SCCs (case, members) of the corpus. -/
def nScc : Nat :=
  (all.foldl (fun acc a => if acc.any (sameScc a) then acc else acc ++ [a]) []).length

#guard all.length = 174
#guard all.all fun a => (bellOf a).isSome
#guard all.all infoOk
#guard all.all outOk
#guard all.all (compOk fun _ _ => true)
#guard all.all (compOk fun _ _ => false)
-- the SCCs of the corpus: their number, and the compiles of the SCCs with a soft call
#guard nScc = 47
#guard (all.filter fun a => (sccOf a).any (·.soft != [])).length = 9
-- `sof` matters: with `sof` false at every call, 5 of the 6 soft `%done` compiles give another
-- `Out` (the sixth, a `fld` member, the same `Out`: only its soft map differs), and nothing else
#guard (all.filter fun a => !compOkNS a).length = 5
#guard (all.filter fun a => !compOkNS a).all fun a => a.mode == Mode.done && a.soft != []

end Formalization.SkaModel.SccLoop.SoftShapeCheck
