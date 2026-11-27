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

namespace Formalization.SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- `+rewrite-input` gives the `+need-to-ordered` of the need it renumbers. -/
theorem rewriteInputGo_need {Map : Type → Type} [HoonMap Map] (rr : Nat → RM Map Nat) :
    ∀ (ned : Need) (st st' : Nat × Map Nat) (x : NeedOrd),
      rewriteInputGo rr ned st = some (x, st') → x = needToOrd ned
  | Need.none, st, st', x, h => by
    simp only [rewriteInputGo, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | Need.this r, st, st', x, h => by
    simp only [rewriteInputGo, bind, StateT.bind, pure, StateT.pure] at h
    cases e : rr r st with
    | none => rw [e] at h; cases h
    | some p => rw [e] at h; simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | Need.pair p q, st, st', x, h => by
    simp only [rewriteInputGo, bind, StateT.bind, pure, StateT.pure] at h
    cases e1 : rewriteInputGo rr p st with
    | none => rw [e1] at h; cases h
    | some a =>
      rw [e1] at h
      simp only [Option.bind_some] at h
      cases e2 : rewriteInputGo rr q a.2 with
      | none => rw [e2] at h; cases h
      | some b =>
        rw [e2] at h
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, rewriteInputGo_need rr p st a.2 a.1 (by rw [e1]),
          rewriteInputGo_need rr q a.2 b.2 b.1 (by rw [e2])]; rfl
  | Need.both r p q, st, st', x, h => by
    simp only [rewriteInputGo, bind, StateT.bind, pure, StateT.pure] at h
    cases e0 : rr r st with
    | none => rw [e0] at h; cases h
    | some c =>
      rw [e0] at h
      simp only [Option.bind_some] at h
      cases e1 : rewriteInputGo rr p c.2 with
      | none => rw [e1] at h; cases h
      | some a =>
        rw [e1] at h
        simp only [Option.bind_some] at h
        cases e2 : rewriteInputGo rr q a.2 with
        | none => rw [e2] at h; cases h
        | some b =>
          rw [e2] at h
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, rewriteInputGo_need rr p c.2 a.2 a.1 (by rw [e1]),
            rewriteInputGo_need rr q a.2 b.2 b.1 (by rw [e2])]; rfl

/-- **The straight of `+to-straight` has the need it was given**, ordered. -/
theorem toStraightF_need {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] (cond : Map (Nat × List Nat))
    (blocks : Map Blob) (ned : Need) (o : Nat) (s : Straight Map) (h : toStraightF cond blocks ned o = some s) :
    s.need = needToOrd ned := by
  unfold toStraightF at h
  simp only at h
  cases e0 : HoonMap.get blocks o with
  | none => rw [e0] at h; cases h
  | some start =>
    rw [e0, Option.bind_some] at h
    generalize rer cond (hasProxies cond) _ (renReg _ _) = rr at h
    cases e1 : rewriteInput rr ned (0, HoonMap.empty) with
    | none => rw [e1] at h; cases h
    | some r =>
      obtain ⟨input, st⟩ := r
      rw [e1, Option.bind_some] at h
      have hin : input = needToOrd ned := by
        unfold rewriteInput at e1
        simp only [if_true] at e1
        exact rewriteInputGo_need rr ned _ st input e1
      split at h <;>
      · obtain ⟨new, -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact hin

/-- **The straight of the final pass has the need `need-new`**: the `+need-to-ordered` of the
residual of the bake. -/
theorem finishLFC_need (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) (nex : NextL CSet) (g1 : SkaModel.Comp.Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : SkaModel.Comp.Gen (TreapMap mugF)) = some (nex, g1))
    (nedF : Need) (g2 : SkaModel.Comp.Gen (TreapMap mugF)) (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (s : Straight (TreapMap mugF))
    (h : finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less bake = some s) :
    s.need = needToOrd (bake nedF).1 := by
  unfold finishLFC at h
  simp only [hrunL, Option.bind_some] at h
  by_cases ha : nex.th.args ≠ []
  · simp [ha] at h
  · simp only [ha, if_false, hnoar, Option.bind_some] at h
    cases e1 : coerceLazyL nedF less nex.th.there nex.laz g2 with
    | none => rw [e1] at h; cases h
    | some r1 =>
      rw [e1, Option.bind_some] at h
      cases e2 : addOps nex.th.there ((bake nedF).2.map fun (r, v) => Pole.imm v r) r1.2 with
      | none => rw [e2] at h; cases h
      | some r2 =>
        rw [e2, Option.bind_some] at h
        exact toStraightF_need _ _ _ _ s h

end Formalization.SkaModel.SccLoop
