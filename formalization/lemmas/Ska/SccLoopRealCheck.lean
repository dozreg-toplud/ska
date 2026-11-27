import lemmas.Ska.SccLoopReal
import lemmas.Ska.SccLoopRealData
import lemmas.Ska.CompCall

/-! # The `%done` compile of a real member against the real compiler (README Gaps 21.14)

The dumps of `SccLoopRealData.lean` (`tools/hoon/sccreal.py`: every `%done` compile of
`member` on the 18 formulas of `tools/hoon/sccloop.py`, lone bells included): per compile the
nomm, `laz`, the `ord` of `+shape-collapse`, `ned-final`, `need-new`, the raw `sur`, `o`, the
views of the members, the outside callees' needs, `sure.cache`, `pure`, and the entry found
with `need-pessimized`.  Checked, over the computable instances `LS`, `FM` (`memDoneLS` is the
body of `memDoneM` with `sureOfS` for `sureOf`):

* `postOk` (the chain after the run, from the dumped `laz`): `shapeCol` gives the dumped `ord`,
  `needOrdAllocRegs` of it from the dumped first register gives the dumped `ned-final`,
  `bakeNeed` under `less.b` gives `need-new`, `sureOfS` of the sure part of `laz` the raw `sur`,
  and the entry's need is `msgOrd need-new prev cape` (`need-new` without an entry);
* `runOk` (the whole of `memDoneM`): `runLC env ~` of the decoded nomm on `[%done ~]`, with `env`
  the `envView` of the dumped outside environment at the members' views, gives the dumped
  `laz` (sets compared as sets) and `o`, then the chain gives the dumped `ord`, `ned-final`,
  `need-new` and `sur`. -/

namespace Formalization.SkaModel.SccLoop.RealCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData

/-! ## Reading the dumps -/

/-- One character of the compact noun syntax, on a stack of open cells and a pending atom. -/
def step (st : List (List Noun) × Option Nat) (c : Char) : List (List Noun) × Option Nat :=
  let flush : List (List Noun) := match st.2, st.1 with
    | some n, top :: rest => (A n :: top) :: rest
    | _, s => s
  if c.isDigit then (st.1, some ((st.2.getD 0) * 10 + (c.toNat - '0'.toNat)))
  else if c = '[' then ([] :: flush, none)
  else if c = ']' then
    match flush with
    | [t, h] :: up :: rest => ((C h t :: up) :: rest, none)
    | s => (s, none)
  else (flush, none)

/-- A noun from its compact syntax (atoms in decimal, cells `[h t]`). -/
def nounOfStr (s : String) : Noun :=
  match s.foldl step ([[]], none) with
  | ([x] :: _, none) => x
  | (_, some n) => A n
  | _ => A 0xbad

def capeOf : Noun → Cape
  | Noun.atom 0 => Cape.yes
  | Noun.atom _ => Cape.no
  | Noun.cell h t => Cape.cell (capeOf h) (capeOf t)

def ordOf : Noun → Option NeedOrd
  | Noun.cell (Noun.atom t) (Noun.atom _) =>
    if t = Tag.this then some NeedOrd.this else if t = Tag.none then some NeedOrd.none else none
  | Noun.cell (Noun.atom t) (Noun.cell h tl) =>
    if t = Tag.both then (ordOf h).bind fun a => (ordOf tl).map fun b => NeedOrd.both a b else none
  | Noun.cell p q => (ordOf p).bind fun a => (ordOf q).map fun b => NeedOrd.pair a b
  | Noun.atom _ => none

def needOf : Noun → Option Need
  | Noun.cell (Noun.atom t) (Noun.atom r) =>
    if t = Tag.this then some (Need.this r) else if t = Tag.none then some Need.none else none
  | Noun.cell (Noun.atom t) (Noun.cell (Noun.atom r) (Noun.cell h tl)) =>
    if t = Tag.both then (needOf h).bind fun a => (needOf tl).map fun b => Need.both r a b else none
  | Noun.cell p q => (needOf p).bind fun a => (needOf q).map fun b => Need.pair a b
  | Noun.atom _ => none

/-- The atoms of a treap set, in the order of `+rep:in` (node, left, right). -/
def setList : Noun → List Nat
  | Noun.cell (Noun.atom n) (Noun.cell l r) => n :: (setList l ++ setList r)
  | _ => []

def lsOf (n : Noun) : LS := ⟨setList n⟩

mutual
def lazyOf : Noun → Option (Lazy LS)
  | Noun.cell (Noun.cell ned lok) (Noun.cell fk bd) =>
    (needOf ned).bind fun nd => (forksOf fk).bind fun f => (bondsOf bd).map fun b =>
      Lazy.mk ⟨nd, lsOf lok⟩ f b
  | _ => none
def forksOf : Noun → Option (List ((Nat × Lazy LS) × (Nat × Lazy LS)))
  | Noun.atom 0 => some []
  | Noun.cell (Noun.cell (Noun.cell (Noun.atom oy) ly) (Noun.cell (Noun.atom on) ln)) rest =>
    (lazyOf ly).bind fun a => (lazyOf ln).bind fun b => (forksOf rest).map fun r => ((oy, a), (on, b)) :: r
  | _ => none
def bondsOf : Noun → Option (List (Nat × Lazy LS))
  | Noun.atom 0 => some []
  | Noun.cell (Noun.cell (Noun.atom o) l) rest =>
    (lazyOf l).bind fun a => (bondsOf rest).map fun r => (o, a) :: r
  | _ => none
end

/-- Sorted without duplicates: a set compared as a set. -/
def norm (l : List Nat) : List Nat := (l.eraseDups).mergeSort

/-- `laz` with its sets as sorted lists: the noun compared. -/
def lazyN : Lazy LS → Noun
  | Lazy.mk s f b => C (C s.ned.toNoun (listNat (norm s.lok.l)))
      (C (forksN f) (bondsN b))
where
  listNat : List Nat → Noun
    | [] => A 0
    | x :: r => C (A x) (listNat r)
  forksN : List ((Nat × Lazy LS) × (Nat × Lazy LS)) → Noun
    | [] => A 0
    | ((oy, ly), (on, ln)) :: rest => C (C (C (A oy) (lazyN ly)) (C (A on) (lazyN ln))) (forksN rest)
  bondsN : List (Nat × Lazy LS) → Noun
    | [] => A 0
    | (o, l) :: rest => C (C (A o) (lazyN l)) (bondsN rest)

def bellOf (n : Noun) : Option Bell := Bell.ofNoun? n

def nommOf : Noun → Option Nomm
  | Noun.cell (Noun.cell a b) q => (nommOf (Noun.cell a b)).bind fun x => (nommOf q).map fun y => Nomm.cons x y
  | Noun.cell (Noun.atom 0) (Noun.atom p) => some (Nomm.n0 p)
  | Noun.cell (Noun.atom 1) x => some (Nomm.n1 x)
  | Noun.cell (Noun.atom 2) (Noun.cell p (Noun.cell q (Noun.atom 0))) =>
    (nommOf p).bind fun x => (nommOf q).map fun y => Nomm.n2 x y none
  | Noun.cell (Noun.atom 2) (Noun.cell p (Noun.cell q (Noun.cell (Noun.atom 0) (Noun.cell b k)))) =>
    (nommOf p).bind fun x => (nommOf q).bind fun y => (bellOf b).bind fun bl =>
      match k with
      | Noun.atom 0 => some (Nomm.n2 x y (some (bl, none)))
      | Noun.cell (Noun.atom 0) v => some (Nomm.n2 x y (some (bl, some v)))
      | _ => none
  | Noun.cell (Noun.atom 3) p => (nommOf p).map Nomm.n3
  | Noun.cell (Noun.atom 4) p => (nommOf p).map Nomm.n4
  | Noun.cell (Noun.atom 5) (Noun.cell p q) => (nommOf p).bind fun x => (nommOf q).map fun y => Nomm.n5 x y
  | Noun.cell (Noun.atom 6) (Noun.cell p (Noun.cell q r)) =>
    (nommOf p).bind fun x => (nommOf q).bind fun y => (nommOf r).map fun z => Nomm.n6 x y z
  | Noun.cell (Noun.atom 7) (Noun.cell p q) => (nommOf p).bind fun x => (nommOf q).map fun y => Nomm.n7 x y
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a) v) q) =>
    (nommOf v).bind fun x => (nommOf q).map fun y => Nomm.n10 a x y
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag) (Noun.cell q body)) =>
    (nommOf q).map fun y => Nomm.n11s tag y body
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) h) (Noun.cell q body)) =>
    (nommOf h).bind fun x => (nommOf q).map fun y => Nomm.n11d tag x y body
  | Noun.cell (Noun.atom 12) (Noun.cell p q) => (nommOf p).bind fun x => (nommOf q).map fun y => Nomm.n12 x y
  | _ => none

/-- An entry `[bell need sure pure jet]` of the views or of the outside callees. -/
structure Ent where
  bell : Noun
  need : NeedOrd
  sure : NeedOrd
  pure : Bool
  jet : Bool

def entOf (s : String) : Option Ent :=
  match nounOfStr s with
  | Noun.cell b (Noun.cell n (Noun.cell su (Noun.cell (Noun.atom p) (Noun.atom j)))) =>
    (ordOf n).bind fun nd => (ordOf su).map fun sd => ⟨b, nd, sd, p == 0, j == 0⟩
  | _ => none

def look (es : List Ent) (k : Noun) : Option Ent := es.find? fun e => e.bell == k

/-- The environment outside the SCC, from the dumps: the outside callees' needs and
`sure.cache`, `pure` and the jets of every callee, `+hinted`'s code table, and no soft call. -/
def envOut (mem out : List Ent) : CallEnv :=
  ⟨fun b => (look out b.toNoun).map (·.need),
   fun b => ((look out b.toNoun).map (·.sure)).getD NeedOrd.none,
   fun b => ((look (mem ++ out) b.toNoun).map (·.pure)).getD false,
   fun b => if ((look (mem ++ out) b.toNoun).map (·.jet)).getD false then some (A 0) else none,
   fun b => (look (mem ++ out) b.toNoun).map (·.pure),
   fun _ _ _ _ _ => false⟩

/-- The `envView` of a compile: `envOut` outside, the views of the members at the members. -/
def envOf (mem out : List Ent) : CallEnv :=
  envView (envOut mem out) (mem.map (·.bell))
    (fun k => ((look mem k).map (·.need)).getD NeedOrd.none)
    (fun k => ((look mem k).map (·.sure)).getD NeedOrd.none)

/-- `memDoneM` over `LS`, `FM`, with `sureOfS`, returning the run and `ned-final` too. -/
def memDoneLS (env : CallEnv) (nm : Nomm) (cape : Cape) (data : Noun) (fuel : Nat) :
    Option (NextL LS × NeedOrd × Need × Out NeedOrd) :=
  (runLC (S := LS) (Map := FM) env Option.none nm CGoalL.done [] gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (shapeCol fuel nex.laz cape).bind fun ord =>
      (needOrdAllocRegs ord g1).bind fun (nedF, _) =>
        (sureOfS (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape).map fun sur =>
          (nex, ord, nedF, ⟨needToOrd (bakeNeed nedF (Sock.mk cape data)).1, sur⟩)

/-- The least register of a need (`ned-final` is allocated from it). -/
def minReg : Need → Option Nat
  | Need.none => none
  | Need.this r => some r
  | Need.pair p q => match minReg p, minReg q with
    | some a, some b => some (min a b) | some a, none => some a | none, b => b
  | Need.both r p q => match minReg p, minReg q with
    | some a, some b => some (min r (min a b)) | some a, none => some (min r a) | none, some b => some (min r b)
    | none, none => some r

structure Dec where
  cape : Cape
  data : Noun
  nm : Nomm
  laz : Lazy LS
  ord : NeedOrd
  nedF : Need
  nn : NeedOrd
  sur : NeedOrd
  mem : List Ent
  out : List Ent
  prev : Option NeedOrd
  np : NeedOrd

def decode (r : DoneRec) : Option Dec :=
  match nounOfStr r.less, nounOfStr r.prev with
  | Noun.cell c d, pv =>
    (nommOf (nounOfStr r.nomm)).bind fun nm =>
    (lazyOf (nounOfStr r.laz)).bind fun laz =>
    (ordOf (nounOfStr r.ord)).bind fun ord =>
    (needOf (nounOfStr r.nedf)).bind fun nedF =>
    (ordOf (nounOfStr r.nn)).bind fun nn =>
    (ordOf (nounOfStr r.sur)).bind fun sur =>
    (r.mem.mapM entOf).bind fun mem =>
    (r.out.mapM entOf).bind fun out =>
    (ordOf (nounOfStr r.np)).bind fun np =>
    let prev := match pv with
      | Noun.cell (Noun.atom 0) p => ordOf p
      | _ => none
    if (pv != A 0) && prev.isNone then none else
    some ⟨capeOf c, d, nm, laz, ord, nedF, nn, sur, mem, out, prev, np⟩
  | _, _ => none

/-- The decoders invert the nouns of the nomm and of `laz` (so the checks read the dumps). -/
def decOk (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d => d.nm.toNoun == nounOfStr r.nomm &&
      d.ord.toNoun == nounOfStr r.ord && d.nedF.toNoun == nounOfStr r.nedf

/-- **The chain after the run**, from the dumped `laz` and `ned-final`. -/
def postOk (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    shapeCol 64 d.laz d.cape == some d.ord &&
    ((minReg d.nedF).map fun r0 =>
      ((needOrdAllocRegs (Map := FM) d.ord ⟨r0, 1, 0, false, HoonMap.empty, HoonMap.empty, HoonMap.empty⟩).map
        (·.1)) == some d.nedF).getD (d.ord == NeedOrd.none) &&
    needToOrd d.nedF == d.ord &&
    needToOrd (bakeNeed d.nedF (Sock.mk d.cape d.data)).1 == d.nn &&
    sureOfS (needToOrd d.laz.sure.ned) d.laz.sure.lok d.cape == some d.sur &&
    (match d.prev with
      | none => d.np == d.nn
      | some p => msgOrd d.nn p d.cape == d.np)

/-- **The whole `%done` compile**: `runLC` with `envView` gives the dumped `laz` and `o`, and
the chain the dumped `ord`, `ned-final`, `need-new` and `sur`. -/
def runOk (r : DoneRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    match memDoneLS (envOf d.mem d.out) d.nm d.cape d.data 64 with
    | none => false
    | some (nex, ord, nedF, o) =>
      lazyN nex.laz == lazyN d.laz && nex.th.there == r.o && ord == d.ord && nedF == d.nedF &&
        o.nn == d.nn && o.sur == d.sur

/-- What the run of the model gives on a compile (for the report of a difference). -/
def runOut (r : DoneRec) : Option (Noun × Nat × NeedOrd × NeedOrd) :=
  (decode r).bind fun d => (memDoneLS (envOf d.mem d.out) d.nm d.cape d.data 64).map fun (nex, ord, _, o) =>
    (lazyN nex.laz, nex.th.there, ord, o.nn)

/-! ## The checks

65 `%done` compiles: 37 of lone bells (the loop is skipped or the SCC is one bell), 28 of
members of SCCs of two to four bells; 41 find an entry `prev` (every compile after the sweeps),
and on none of them is `need-pessimized` other than `need-new` (so `finish` always gets `~`
here: the `+coerce-soft` branch is not taken by the corpus); 6 make a soft call (`soft.gen` not
empty after the run: `%swap` twice, `%fld` three times, `%rot3` once). -/

#guard recs.length = 65
#guard recs.all decOk
-- The chain after the run, on every compile.
#guard recs.all postOk
-- On an entry, `need-pessimized` is `need-new` on every `%done` compile.
#guard recs.all fun r => match decode r with | some d => d.np == d.nn | none => false
-- The whole `memDoneM` (`runLC` with `envView`, then the chain), on the 59 compiles with no soft call.
#guard (recs.filter (·.nosoft)).length = 59
#guard (recs.filter (·.nosoft)).all runOk
-- Of them, 28 are members of SCCs of two bells or more, each with an entry.
#guard ((recs.filter (·.nosoft)).filter fun r => r.mem.length > 1 &&
    match decode r with | some d => d.prev.isSome | none => false).length = 28
-- The 6 soft compiles: with `sof` true at every call the model returns nothing (the soft call is
-- not modelled), and with `sof` false it differs from the compiler.
#guard (recs.filter (! ·.nosoft)).all fun r => (decode r).any fun d =>
    let e := envOf d.mem d.out
    (memDoneLS { e with sof := fun _ _ _ _ _ => true } d.nm d.cape d.data 64).isNone && !runOk r
-- The views matter: with every member read as `this` (need and sure), the 28 members' runs differ.
#guard ((recs.filter fun r => r.nosoft && r.mem.length > 1).filter fun r => (decode r).any fun d =>
    let mem := d.mem.map fun e => { e with need := NeedOrd.this, sure := NeedOrd.this }
    match memDoneLS (envOf mem d.out) d.nm d.cape d.data 64 with
    | none => true
    | some (nex, _, _, o) => !(lazyN nex.laz == lazyN d.laz && o.nn == d.nn && o.sur == d.sur)).length = 28

end Formalization.SkaModel.SccLoop.RealCheck
