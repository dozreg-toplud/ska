import lemmas.Ska.SccLoop
import lemmas.Ska.ShapeCol
import lemmas.Ska.BakeNeed

/-! # The member compile of a real SCC: `compReal` (README Gaps 21.14)

The parameter `Cfg.comp b mode vn vs` of the loop model (`Ska/SccLoop.lean`) for a real
member, made of the models of the arms `member` runs (lines 3508 to 3539 of
`desk/lib/nock-compilation.hoon`, the branch `!@  dedicated-shape-pass` takes, since the
wing is defined at line 2822).

* `%done` (`memDoneM`): `+run` of the member's nomm on `[%done ~]` with `mono` `|` (`runLC env
  ~`, `env` reading the views `vn`, `vs` at the members, `envView`), `nex.th.args` empty (the
  `?>` of `+collapse-shape`), `+shape-collapse` (`shapeCol` at a fuel where it returns: the pill
  gives the same `ord` at every such fuel, `sc_gate`), `+need-ord-alloc-regs`, `+bake-need` with
  `less.b` (`bakeNeed`), `need-new` the `+need-to-ordered` of `ned.bak`, and `sur` the `+sure-of`
  of the sure part of `laz`.
* `%may`, `%must` (`sweepM`): `+run-shape` of the nomm, `+laze-collapse` (`%must`) or
  `+laze-may` (`%may`), then `+bake-need-ord` with `less.b`, and `sur` the `+sure-of` of `sure.l`.
  `+run-shape` (3284 cells), `+laze-collapse` and `+laze-may` have no model: the part up to
  `collapsed` and `sur` is the parameter `RealCfg.laze`, and `bakeNeedOrd` is applied to it.

A compile that crashes in the pill is `none` here; the loop model needs a total `Out`, so
`compReal` reads `none` as `[%none ~]` twice, and the link asks that the model returns
(`DoneRet`). -/

namespace Formalization.SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- What the compile of a member reads of the member itself: its nomm (the product of
`+inlined`), the cape and data of `less.b`, and a fuel at which `+shape-collapse` returns. -/
structure MemInfo where
  nm : Nomm
  cape : Cape
  data : Noun
  fuel : Nat

/-- The call environment of a member compile: at a callee in the SCC (its bell's noun in
`scc`), `+callee-need` gives the view `vn` and `+callee-sure` the view `vs`; elsewhere `e`. -/
def envView (e : CallEnv) (scc : List Noun) (vn vs : Noun → NeedOrd) : CallEnv :=
  { e with need := fun k => if k.toNoun ∈ scc then some (vn k.toNoun) else e.need k,
           sure := fun k => if k.toNoun ∈ scc then vs k.toNoun else e.sure k }

/-- **The `%done` compile of a member** (lines 3530 to 3539): `need-new` and the raw `sur`. -/
noncomputable def memDoneM (env : CallEnv) (m : MemInfo) : Option (Out NeedOrd) :=
  (runLC (S := CSet) (Map := TreapMap mugF) env Option.none m.nm CGoalL.done [] gen0).bind
    fun (nex, g1) =>
      if nex.th.args ≠ [] then Option.none else
      (shapeCol m.fuel nex.laz m.cape).bind fun ord =>
        (needOrdAllocRegs ord g1).bind fun (nedF, _) =>
          (sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok m.cape).map fun sur =>
            ⟨needToOrd (bakeNeed nedF (Sock.mk m.cape m.data)).1, sur⟩

/-- The data of a real SCC for the model: per member its `MemInfo`, the call environment
outside the SCC, and the unmodelled part of the sweeps' compile: `laze mode env m` is
`(collapsed, sur)` of lines 3520 to 3529 (`+run-shape`, then `+laze-collapse` on `%must` or
`+laze-may` on `%may`, and `+sure-of` of `sure.l`). -/
structure RealCfg where
  scc : List Noun
  info : Noun → MemInfo
  env : CallEnv
  laze : Mode → CallEnv → MemInfo → Option (NeedOrd × NeedOrd)

/-- The sweeps' compile (`%may`, `%must`): `shape` is `+bake-need-ord` of `collapsed`. -/
def sweepM (r : RealCfg) (mode : Mode) (env : CallEnv) (m : MemInfo) : Option (Out NeedOrd) :=
  (r.laze mode env m).map fun p => ⟨bakeNeedOrd p.1 (Sock.mk m.cape m.data), p.2⟩

/-- **The member compile of a real SCC**, the instance of `Cfg.comp`. -/
noncomputable def compReal (r : RealCfg) (b : Noun) (mode : Mode) (vn vs : Noun → NeedOrd) :
    Out NeedOrd :=
  let env := envView r.env r.scc vn vs
  let o := match mode with
    | Mode.done => memDoneM env (r.info b)
    | _ => sweepM r mode env (r.info b)
  o.getD ⟨NeedOrd.none, NeedOrd.none⟩

/-- **The model of a real SCC**: `Cfg` with `comp = compReal r` and `msg` the `msgOrd` of the
member's cape. -/
noncomputable def cfgReal (r : RealCfg) (order : List Noun) (kids : Noun → List Noun) :
    Cfg Noun NeedOrd :=
  ⟨r.scc, order, kids, NeedOrd.none, fun b a p => msgOrd a p (r.info b).cape, compReal r⟩

/-- The `%done` compile returns on every view: what the link asks of the model. -/
def DoneRet (r : RealCfg) : Prop :=
  ∀ b ∈ r.scc, ∀ vn vs, (memDoneM (envView r.env r.scc vn vs) (r.info b)).isSome

theorem compReal_done (r : RealCfg) (b : Noun) (vn vs : Noun → NeedOrd) (o : Out NeedOrd)
    (h : memDoneM (envView r.env r.scc vn vs) (r.info b) = some o) :
    compReal r b Mode.done vn vs = o := by
  simp [compReal, h]

end Formalization.SkaModel.SccLoop
