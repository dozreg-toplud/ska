import lemmas.Ska.SccLoopSoftFinCheck

/-! # The hypotheses of `se_emit` on the corpus (README Gaps 21.17)

On the 65 `%done` compiles of `SccLoopRealData.lean`, with the FM model of
`SccLoopSoftFinCheck.lean` (the run, `needOrdAllocRegs` and the model's `+coerce-lazy` inside
`finish`), the state `stOf r` after `+coerce-lazy` satisfies what `se_emit` (and the path of
`softEmitT` that does not return `none`) asks:

* `reqOk`: every soft call has requirements whose needs are all `%none` or `%this` (`reqTNB`,
  which implies the predicate `ReqTN` of `se_emit`: `reqTNB_spec`);
* `headOk`: the head block of each soft call exists and is `[~ ~ %hop ~ *]` (the success path of
  the `?>` of `+soft-emit`);
* `cutsOk`: `softCuts (softAxes s.ned 1 []) s.req ([], [])` is `some` and its `tops` give no
  tries;
* `emitOk`: `softDone tapFM` on the state succeeds;
* the counts: exactly 6 compiles have a soft call (the ones with `nosoft` false), one call each,
  with 3 requirements. -/

namespace Formalization.SkaModel.SccLoop.SoftReqCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData
open Formalization.SkaModel.SccLoop.RealCheck Formalization.SkaModel.SccLoop.SoftCheck
open Formalization.SkaModel.SccLoop.SoftFinCheck

/-- Every requirement's need is `%none` or `%this`. -/
def reqTNB (req : List (Nat × Need)) : Bool :=
  req.all fun p => match p.2 with
    | Need.none => true
    | Need.this _ => true
    | _ => false

theorem reqTNB_spec (req : List (Nat × Need)) (h : reqTNB req = true) :
    ∀ p ∈ req, p.2 = Need.none ∨ ∃ r, p.2 = Need.this r := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  obtain ⟨src, n⟩ := p
  cases n with
  | none => exact Or.inl rfl
  | this r => exact Or.inr ⟨r, rfl⟩
  | pair a b => simp at this
  | both r a b => simp at this

/-- The head block exists and is `[~ ~ %hop ~ *]`. -/
def headOkB (blocks : FM Blob) (o : Nat) : Bool :=
  match HoonMap.get blocks o with
  | some hd => hd.par.isEmpty && hd.body.isEmpty &&
      (match hd.fin with
       | Termin.hop t => t.args.isEmpty
       | _ => false)
  | Option.none => false

/-- `softCuts` succeeds and makes no try. -/
def cutsOkB (s : SoftCall) : Bool :=
  match softCuts (softAxes s.ned 1 []) s.req ([], []) with
  | some c => (softTries c.2).isEmpty
  | Option.none => false

/-- The run and `+coerce-lazy` of `finishLFCS`, returning the state after it. -/
def coerceSt (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (ord : NeedOrd)
    (less : Cape) : Option (GenSf FM) :=
  (runLCS (S := LS) (Map := FM) env snd Option.none nm CGoalL.done [] (GenSf.ofGen gen0)).bind
    fun (nex, g1) =>
    (needOrdAllocRegs ord g1.g).bind fun (nedFinal, g2) =>
      (coerceLazyLS nedFinal less nex.th.there nex.laz ⟨g2, g1.soft⟩).map fun (_, g3) => g3

/-- The state after `+coerce-lazy` on a compile. -/
def stOf (r : DoneRec) : Option (GenSf FM) :=
  match decode r with
  | Option.none => Option.none
  | some d => coerceSt (sofOf r (envOf d.mem d.out)) (fun _ _ => true) d.nm d.ord d.cape

def reqOk (r : DoneRec) : Bool :=
  match stOf r with
  | Option.none => false
  | some st => (tapFM st.soft).all fun p => reqTNB p.2.req

def headOk (r : DoneRec) : Bool :=
  match stOf r with
  | Option.none => false
  | some st => (tapFM st.soft).all fun p => headOkB st.g.blocks p.2.head

def cutsOk (r : DoneRec) : Bool :=
  match stOf r with
  | Option.none => false
  | some st => (tapFM st.soft).all fun p => cutsOkB p.2

def emitOk (r : DoneRec) : Bool :=
  match stOf r with
  | Option.none => false
  | some st => (softDone tapFM st).isSome

/-- The number of soft calls after `+coerce-lazy`. -/
def nSoft (r : DoneRec) : Nat :=
  match stOf r with
  | Option.none => 0
  | some st => (tapFM st.soft).length

/-- The number of requirements, over all soft calls. -/
def nReq (r : DoneRec) : Nat :=
  match stOf r with
  | Option.none => 0
  | some st => ((tapFM st.soft).map fun p => p.2.req.length).sum

#guard recs.length == 65
#guard recs.all reqOk
#guard recs.all headOk
#guard recs.all cutsOk
#guard recs.all emitOk
-- exactly the 6 compiles with a soft call have a non-empty soft map, one call, 3 requirements
#guard recs.all fun r => (nSoft r != 0) == !r.nosoft
#guard (recs.filter fun r => nSoft r != 0).length == 6
#guard (recs.filter fun r => nSoft r != 0).all fun r => nSoft r == 1 && nReq r == 3

end Formalization.SkaModel.SccLoop.SoftReqCheck
