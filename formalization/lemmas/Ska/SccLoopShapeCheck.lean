import lemmas.Ska.SccLoopShape
import lemmas.Ska.SccLoopShapeData
import lemmas.Ska.SccLoopRealCheck

/-! # The sweeps' compile of a real member against the real compiler (README Gaps 21.18)

The dumps of `SccLoopShapeData.lean` (`tools/hoon/sccreal.py OUT --shape-lib`: every `%must` and
`%may` compile of `member` on the 18 formulas of `tools/hoon/sccloop.py`): per compile the nomm,
the `laze` of `+run-shape`, `collapsed`, `shape`, the raw `sur`, `id-gen` and `sofs` after the run,
the views and the outside callees, the code table the compiles reach, and at the product `keep`,
`was`, the `sur` put, `moved`, the entry, the need put `np` and `chg`.  Checked over the
computable set `LS`, with the call environment `envOf` of the `%done` check
(`SccLoopRealCheck.lean`: `envView` of the outside callees at the members' views) and the
`ShapeX` of the dumps (`jet` as `+run-shape` reads it, `cod` the code table's nomms):

* `runOk`: `runShape` of the model (`lazeRealG`'s run) gives the dumped `laze`, `id-gen`, `sofs`;
* `colOk`: `collapseOf` (fuel `64`) on it gives `collapsed`, `bakeNeedOrd` gives `shape`,
  `sureOfS` gives `sur`: so `lazeRealG` gives `(collapsed, sur)`;
* `prodOk`: the model's `member` logic (`Ska/SccLoop.lean`) on the compile's `Out` gives the dumped
  `sur` put, `moved`, `np` and `chg` (`top` the view of the members, `prev` the entry). -/

namespace Formalization.SkaModel.SccLoop.ShapeCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop
open Formalization.SkaModel.SccLoop.RealCheck Formalization.SkaModel.SccLoop.ShapeData

/-- A `laze` with its sets sorted, as the dumps print it. -/
def lazeNL : Laze LS → Noun
  | Laze.mk s f b => C (C s.ned.toNoun (listNat (norm s.lok.l))) (C (forksN f) (bondsN b))
where
  listNat : List Nat → Noun
    | [] => A 0
    | x :: r => C (A x) (listNat r)
  forksN : List ((Nat × Laze LS) × (Nat × Laze LS)) → Noun
    | [] => A 0
    | ((oy, ly), (on, ln)) :: rest => C (C (C (A oy) (lazeNL ly)) (C (A on) (lazeNL ln))) (forksN rest)
  bondsN : List (Nat × Laze LS) → Noun
    | [] => A 0
    | (o, l) :: rest => C (C (A o) (lazeNL l)) (bondsN rest)

/-- The code table of a case: `[bell nomm pure]`. -/
def codeOf (cs : String) : List (Noun × Noun) :=
  (((codes.find? (·.1 == cs)).map (·.2)).getD []).filterMap fun s =>
    match nounOfStr s with
    | Noun.cell k (Noun.cell n _) => some (k, n)
    | _ => none

/-- The `ShapeX` of a compile: `jet` from the views and the outside callees, `cod` the code table. -/
def shapeXOf (cs : String) (mem out : List Ent) : ShapeX :=
  ⟨fun b => ((look (mem ++ out) b.toNoun).map (·.jet)).getD false,
   fun b => ((codeOf cs).find? (·.1 == b.toNoun)).bind fun p => nommOf p.2⟩

/-- A decoded sweep compile. -/
structure Dec where
  mode : Mode
  cape : Cape
  data : Noun
  nm : Nomm
  col : NeedOrd
  shape : NeedOrd
  sur : NeedOrd
  mem : List Ent
  out : List Ent
  was : Option NeedOrd
  fsur : NeedOrd
  prev : Option NeedOrd
  np : NeedOrd

def unitOrd (n : Noun) : Option (Option NeedOrd) :=
  match n with
  | Noun.cell (Noun.atom 0) p => (ordOf p).map some
  | Noun.atom 0 => some none
  | _ => none

def decode (r : ShapeRec) : Option Dec :=
  match nounOfStr r.less with
  | Noun.cell c d =>
    (nommOf (nounOfStr r.nomm)).bind fun nm =>
    (ordOf (nounOfStr r.col)).bind fun col =>
    (ordOf (nounOfStr r.shape)).bind fun sh =>
    (ordOf (nounOfStr r.sur)).bind fun sur =>
    (r.mem.mapM entOf).bind fun mem =>
    (r.out.mapM entOf).bind fun out =>
    (unitOrd (nounOfStr r.was)).bind fun was =>
    (ordOf (nounOfStr r.fsur)).bind fun fsur =>
    (unitOrd (nounOfStr r.prev)).bind fun prev =>
    (ordOf (nounOfStr r.np)).map fun np =>
    ⟨if r.must then Mode.must else Mode.may, capeOf c, d, nm, col, sh, sur, mem, out, was, fsur, prev, np⟩
  | _ => none

/-- The model's run of `+run-shape` on a compile. -/
def runOf (r : ShapeRec) (d : Dec) : Option (Laze LS × RSt LS) :=
  runShape (S := LS) (shapeEnvOf (shapeXOf r.cs d.mem d.out) (envOf d.mem d.out)) Option.none d.nm GoalS.done rsSt0

/-- **The run**: the dumped `laze`, `id-gen` and `sofs`. -/
def runOk (r : ShapeRec) : Bool :=
  match decode r with
  | none => false
  | some d => match runOf r d with
    | none => false
    | some (l, st) => lazeNL l == nounOfStr r.l && st.idg == r.idg && norm st.sofs.l == r.sofs

/-- **`lazeRealG` on the compile**: `(collapsed, sur)`, and `shape` its `+bake-need-ord`. -/
def colOk (r : ShapeRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    lazeRealG (S := LS) (shapeXOf r.cs d.mem d.out) d.mode (envOf d.mem d.out) ⟨d.nm, d.cape, d.data, 64⟩
        == some (d.col, d.sur) &&
      bakeNeedOrd d.col (Sock.mk d.cape d.data) == d.shape

/-- **The product as the model's `member` computes it** from `Out = ⟨shape, sur⟩`: the `sur` put,
`moved`, `np` and `chg` (`top` the view of `b` when it has no entry). -/
def prodOk (r : ShapeRec) : Bool :=
  match decode r with
  | none => false
  | some d =>
    let o : Out NeedOrd := ⟨d.shape, d.sur⟩
    let sur := if r.keep then d.was.getD o.sur else o.sur
    let moved := sur != d.was.getD NeedOrd.none
    -- `top` at `b`: the view of `b` when it has no entry (`viewN`), and `was` its view of `sure`
    let vb := look d.mem (nounOfStr r.bell)
    let topB := (vb.map (·.need)).getD NeedOrd.none
    let res : Bool × NeedOrd := match d.prev with
      | none => (moved || o.nn != NeedOrd.none || topB != NeedOrd.none, o.nn)
      | some prev => (moved || msgOrd o.nn prev d.cape != prev, msgOrd o.nn prev d.cape)
    sur == d.fsur && moved == r.moved && res.2 == d.np && res.1 == r.chg &&
      (vb.map (·.sure)) == some (d.was.getD NeedOrd.none)

#guard recs.length = 109
#guard (recs.filter (·.must)).length = 68
#guard recs.all fun r => (decode r).isSome
#guard recs.all runOk
#guard recs.all colOk
#guard recs.all prodOk

/-! The corpus: 27 compiles with an entry; `need-pessimized` is `need-new` (`shape`) on every
sweep compile; 30 compiles mark a soft call in `sofs` (the soft branch of a direct call, checked
by `runOk`); `keep` is never set; 70 compiles are of members of SCCs of more than one bell. -/
#guard (recs.filter fun r => (decode r).any (·.prev.isSome)).length = 27
#guard recs.all fun r => (decode r).any fun d => d.np == d.shape
#guard (recs.filter (·.sofs != [])).length = 30
#guard recs.all (! ·.keep)
#guard (recs.filter (·.mem.length > 1)).length = 70

end Formalization.SkaModel.SccLoop.ShapeCheck
