import lemmas.Compiler.CompSccLoopSoftFinGate
import lemmas.Compiler.CompSccLoopSoftCoerce

/-! # The gate `finish` with soft calls, `+coerce-lazy` linked (README Gaps 21.17)

`fin_gate_ts_BS`, `fin_gate_finishLFCS_B` (`CompSccLoopSoftFinGate.lean`) with their hypothesis
`hcz` (the pill's `+coerce-lazy` with `+soft-ask`) discharged by `comp_coerce_lazy_allS`
(`CompSccLoopSoftCoerce.lean`).  What is left as a hypothesis is `hreq`: every soft call
in the model's soft map after `+coerce-lazy` has requirements `%none` / `%this` (checked on
the FM model of the 65 compiles in `Ska/SccLoopSoftReqCheck.lean`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- **`finish` after the run, with soft calls**: the tail `finTailS` of `finishLFCS`. -/
theorem fin_gate_ts_BSC (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun}
    (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (sf : TreapMap mugF SoftCall) (hx : x.soft = softMapNoun sf)
    (hQ : Q g.cond) (nedF : Need) (know : Sock)
    (hrun : isRun (flattenNeed (bakeNeed nedF know).1) ((flattenNeed (bakeNeed nedF know).1).headD 0) 0 = true)
    (o : Nat) (laz : Lazy CSet)
    (hreq : ∀ u st, coerceLazyLS nedF less o laz ⟨g, sf⟩ = some (u, st) →
      ∀ p ∈ TreapMap.tap st.soft, ReqTN p.2.req) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) o SUR (genNoun g x) REST))) finBody
      = (finTailS TreapMap.tap nedF less o laz (fun n => bakeNeed n know) ⟨g, sf⟩).map Straight.toNoun :=
  fin_gate_ts_BS Q hT h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g x sf hx hQ nedF know hrun o laz
    (comp_coerce_lazy_allS h7 x sf hx nedF o laz less g) hreq

/-- **`finish` with soft calls**: from the run `runLCS`, the gate is `finishLFCS`. -/
theorem fin_gate_finishLFCS_BC (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun}
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 : GenSf (TreapMap mugF))
    (g2 : Gen (TreapMap mugF)) (nedF : Need) (know : Sock) (hx : x.soft = softMapNoun g1.soft)
    (hrunL : runLCS env snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0) = some (nex, g1))
    (hargs : nex.th.args = [])
    (hQ : Q g1.g.cond)
    (hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF know).1) ((flattenNeed (bakeNeed nedF know).1).headD 0) 0 = true)
    (hreq : ∀ u st, coerceLazyLS nedF less nex.th.there nex.laz ⟨g2, g1.soft⟩ = some (u, st) →
      ∀ p ∈ TreapMap.tap st.soft, ReqTN p.2.req) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) nex.th.there SUR (genNoun g2 x) REST))) finBody
      = (finishLFCS (S := CSet) (Map := TreapMap mugF) env snd TreapMap.tap nm ord less
          (fun n => bakeNeed n know)).map Straight.toNoun :=
  fin_gate_finishLFCS_B Q hT env snd h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 x nm ord nex g1 g2
    nedF know hx hrunL hargs hQ hnoar hrun (comp_coerce_lazy_allS h7 x g1.soft hx nedF nex.th.there nex.laz less g2)
    hreq

end Compiler
end Formalization
