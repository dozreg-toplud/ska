import lemmas.Ska.SccLoopSoftShape
import lemmas.Ska.SccLoopSoft2

/-! # The real SCC with soft members on the fixed run (README Gaps 21.20)

`memDoneMS2` is `memDoneMS` with `runLCS2` (`+crash-need` asking at a soft block), and
`cfgRealSS2` is `cfgRealSS` with it.  Where the two runs agree (`RunAgree`: on every member and
every view the `%done` run of `runLCS2` is that of `runLCS`), the configurations are equal
(`cfgRealSS2_eq`), so every theorem on `cfgRealSS` (the loop theorem `csi_gate_ranked_soft`,
`ranked_SS`, `cfgRealSS_member_sweep`) holds for `cfgRealSS2` by rewriting.  On `%may` /
`%must` they are equal always (`cfgRealSS2_comp_sweep`). -/

namespace Formalization.SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- **The `%done` compile with soft calls, fixed**: `memDoneMS` with `runLCS2`. -/
noncomputable def memDoneMS2 (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (m : MemInfo) :
    Option (Out NeedOrd) :=
  (runLCS2 (S := CSet) (Map := TreapMap mugF) env snd Option.none m.nm CGoalL.done [] (GenSf.ofGen gen0)).bind
    fun (nex, g1) =>
      if nex.th.args ≠ [] then Option.none else
      (shapeCol m.fuel nex.laz m.cape).bind fun ord =>
        (needOrdAllocRegs ord g1.g).bind fun (nedF, _) =>
          (sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok m.cape).map fun sur =>
            ⟨needToOrd (bakeNeed nedF (Sock.mk m.cape m.data)).1, sur⟩

noncomputable def compRealS2 (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (b : Noun) (mode : Mode)
    (vn vs : Noun → NeedOrd) : Out NeedOrd :=
  let env := envView r.env r.scc vn vs
  let o := match mode with
    | Mode.done => memDoneMS2 env snd (r.info b)
    | _ => sweepM r mode env (r.info b)
  o.getD ⟨NeedOrd.none, NeedOrd.none⟩

noncomputable def cfgRealS2 (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) : Cfg Noun NeedOrd :=
  ⟨r.scc, order, kids, NeedOrd.none, fun b a p => msgOrd a p (r.info b).cape, compRealS2 r snd⟩

/-- **The model of a real SCC with soft members, `+crash-need` asking.** -/
noncomputable def cfgRealSS2 (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) : Cfg Noun NeedOrd :=
  cfgRealS2 { r with laze := lazeReal x } snd order kids

/-- The two `%done` runs agree on every member and view. -/
def RunAgree (r : RealCfg) (snd : Nomm → NeedOrd → Bool) : Prop :=
  ∀ b vn vs, runLCS2 (S := CSet) (Map := TreapMap mugF) (envView r.env r.scc vn vs) snd Option.none (r.info b).nm
      CGoalL.done [] (GenSf.ofGen gen0)
    = runLCS (envView r.env r.scc vn vs) snd Option.none (r.info b).nm CGoalL.done [] (GenSf.ofGen gen0)

theorem memDoneMS2_eq (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (m : MemInfo)
    (h : runLCS2 (S := CSet) (Map := TreapMap mugF) env snd Option.none m.nm CGoalL.done [] (GenSf.ofGen gen0)
      = runLCS env snd Option.none m.nm CGoalL.done [] (GenSf.ofGen gen0)) :
    memDoneMS2 env snd m = memDoneMS env snd m := by
  unfold memDoneMS2 memDoneMS
  rw [h]

/-- **Where the runs agree, `cfgRealSS2` is `cfgRealSS`.** -/
theorem cfgRealSS2_eq (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (h : RunAgree r snd) :
    cfgRealSS2 r x snd order kids = cfgRealSS r x snd order kids := by
  unfold cfgRealSS2 cfgRealSS cfgRealS2 cfgRealS
  congr 1
  funext b mode vn vs
  cases mode with
  | done => simp only [compRealS2, compRealS]; rw [memDoneMS2_eq _ _ _ (h b vn vs)]
  | must => rfl
  | may => rfl

/-- On `%may` / `%must` the compile of `cfgRealSS2` is that of `cfgRealSS` (always). -/
theorem cfgRealSS2_comp_sweep (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (b : Noun) (mode : Mode) (hm : mode ≠ Mode.done) (vn vs : Noun → NeedOrd) :
    (cfgRealSS2 r x snd order kids).comp b mode vn vs = (cfgRealSS r x snd order kids).comp b mode vn vs := by
  cases mode with
  | done => exact absurd rfl hm
  | must => rfl
  | may => rfl

/-- On `%done` the compile of `cfgRealSS2` is `memDoneMS2`. -/
theorem cfgRealSS2_comp_done (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (b : Noun) (vn vs : Noun → NeedOrd) :
    (cfgRealSS2 r x snd order kids).comp b Mode.done vn vs
      = (memDoneMS2 (envView r.env r.scc vn vs) snd (r.info b)).getD ⟨NeedOrd.none, NeedOrd.none⟩ := rfl

end Formalization.SkaModel.SccLoop
