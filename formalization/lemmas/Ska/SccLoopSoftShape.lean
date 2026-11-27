import lemmas.Ska.SccLoopShape
import lemmas.Ska.SccLoopSoft
import lemmas.Ska.SccLoopTotal

/-! # One model of a real SCC: soft `%done` compiles and the sweeps of `+run-shape` (README Gaps 21.19)

`cfgRealS r snd` (`Ska/SccLoopSoft.lean`) is the model whose `%done` compile is `memDoneMS`
(`runLCS env snd ~`, soft calls included); its sweeps are `sweepM r`, i.e. `r.laze`.
`cfgRealShape r x` (`Ska/SccLoopShape.lean`) instantiates `r.laze` with track A's `+run-shape`
(`lazeReal x`) but keeps the `%done` compile of `cfgReal` (`memDoneM`, no soft call).

* **`cfgRealSS r x snd`**: `cfgRealS` with `laze := lazeReal x`: both at once.
* `member_cfg_congr`: `member` reads the configuration only through `none`, `msg` and the compile of
  the one mode it runs; so `cfgRealSS_member_sweep`: on `%may` / `%must` the members of `cfgRealSS`
  and of `cfgRealShape` are the same (the `%done` compile is never read there), and
  `ranked_SS`: a `Ranked` for `cfgRealShape` is one for `cfgRealSS` (`Ranked` reads `%must` only). -/

namespace Formalization.SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- **The model of a real SCC with soft members and the sweeps modelled**. -/
noncomputable def cfgRealSS (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) : Cfg Noun NeedOrd :=
  cfgRealS { r with laze := lazeReal x } snd order kids

/-- `member` depends on the configuration only through `none`, `msg` and the compile of its mode. -/
theorem member_cfg_congr {B N : Type} [DecidableEq B] [DecidableEq N] (c1 c2 : Cfg B N) (top : B → N) (b : B) (mode : Mode)
    (keep : Bool) (st : St B N) (hn : c1.none = c2.none) (hmsg : c1.msg = c2.msg)
    (hc : ∀ vn vs, c1.comp b mode vn vs = c2.comp b mode vn vs) :
    member c1 top b mode keep st = member c2 top b mode keep st := by
  have hv : viewS c1 st = viewS c2 st := by funext k; simp only [viewS, hn]
  simp only [member, hv, hn, hmsg, hc]

/-- On `%may` / `%must`, the compile of `cfgRealSS` is that of `cfgRealShape`. -/
theorem cfgRealSS_comp_sweep (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (b : Noun) (mode : Mode) (hm : mode ≠ Mode.done) (vn vs : Noun → NeedOrd) :
    (cfgRealSS r x snd order kids).comp b mode vn vs = (cfgRealShape r x order kids).comp b mode vn vs := by
  cases mode with
  | done => exact absurd rfl hm
  | must => rfl
  | may => rfl

/-- **On `%may` / `%must`, `member` of `cfgRealSS` is `member` of `cfgRealShape`.** -/
theorem cfgRealSS_member_sweep (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (top : Noun → NeedOrd) (b : Noun) (mode : Mode) (hm : mode ≠ Mode.done)
    (keep : Bool) (st : St Noun NeedOrd) :
    member (cfgRealSS r x snd order kids) top b mode keep st
      = member (cfgRealShape r x order kids) top b mode keep st :=
  member_cfg_congr _ _ top b mode keep st rfl rfl (cfgRealSS_comp_sweep r x snd order kids b mode hm)

/-- On `%done`, the compile of `cfgRealSS` is `memDoneMS` (the soft `%done` compile). -/
theorem cfgRealSS_comp_done (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (b : Noun) (vn vs : Noun → NeedOrd) :
    (cfgRealSS r x snd order kids).comp b Mode.done vn vs
      = (memDoneMS (envView r.env r.scc vn vs) snd (r.info b)).getD ⟨NeedOrd.none, NeedOrd.none⟩ := rfl

/-- **`Ranked` carries over**: it reads the `%must` compile only. -/
def ranked_SS (r : RealCfg) (x : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (rk : Ranked (cfgRealShape r x order kids)) :
    Ranked (cfgRealSS r x snd order kids) :=
  ⟨rk.rk, rk.H, rk.le_H, fun b vn vs h => by
    rw [cfgRealSS_comp_sweep r x snd order kids b Mode.must (by decide)] at h ⊢
    exact rk.up b vn vs h⟩

end Formalization.SkaModel.SccLoop
