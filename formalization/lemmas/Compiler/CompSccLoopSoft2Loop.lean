import lemmas.Compiler.CompSccLoopSweepA
import lemmas.Compiler.CompSccLoopSoftLoop
import lemmas.Ska.SccLoopSoft2Shape
import lemmas.Compiler.CompSccLoopSoftMemDone2

/-! # The loop for a real SCC on the fixed soft model, the sweeps from track A (README Gaps 21.21)

`csi_gate_ranked_soft` (`CompSccLoopSoftLoop.lean`) for the fixed model `cfgRealSS2`
(`Ska/SccLoopSoft2Shape.lean`: `+crash-need` asking at a soft block, in `%1` and in `%3` / `%4` /
`%5`) where its `%done` runs agree with the old model (`RunAgree`, `cfgRealSS2_eq`), with the
`%may` / `%must` calls no longer taking `MemSweepCall` (whose pill hypothesis was `MemShapeBranch`)
but `SweepLeft` (`CompSccLoopSweepA.lean`: `memSweepCall_of_A`, through track A's
`memShape_branchA6`).

**`csi_gate_ranked_soft2`**: the loop theorem; per sweep call `SweepLeft`, per `%done` call
`MemDoneCallS`, and the loop-level facts `hrs`, `hPS`, `hre`, `hset`, `hcn`.

**`csi_gate_ranked_soft2F`**: the same for `cfgRealSS2` WITHOUT `RunAgree` (members whose runs
differ from the old model, the try path included): the `%done` gate is `memGate_done_KS2`
(`CompSccLoopSoftMemDone2.lean`: `MemDoneCallS2`, the run `CompRunAtXTS (runLCS2 ..)` and the
pill's `finish` `FinGateS2` in place of `hreq`), the sweep gates carried over from
`cfgRealShape` by `cfgRealSS2_member_sweep`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedVariables false

/-- **The loop's gate for a real SCC on the fixed soft model** (`cfgRealSS2`, under `RunAgree`):
the sweeps' calls from `SweepLeft` (track A's branch, the loop's own facts), the `%done` calls from
`MemDoneCallS`. -/
theorem csi_gate_ranked_soft2 (r : RealCfg) (xs : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (hag : RunAgree r snd)
    (rk : Ranked (cfgRealSS2 r xs snd order kids)) (nout : Noun → NeedOrd)
    (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P : Noun → Prop) (x : GenRest)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf (cfgRealSS2 r xs snd order kids) SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
    (hbell : ∀ k ∈ tapList SCC, ∃ b' : Bell, b'.toNoun = k)
    (hS : ∀ b ∈ r.scc, b ∈ tapList SCC)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (hrs : r.scc = tapList SCC) (hPS : ∀ k ∈ tapList SCC, ¬ P k) (hre : r.env = env)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc))) (hcn : CodeNomms xs.cod CODE)
    (hleftMay : ∀ (st : St Noun NeedOrd) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      SweepLeft r xs order kids inl P Mode.may (fun _ => NeedOrd.none) (A 0) st SCC CODE (C JETS CALLS) JH b ML CACHE)
    (hcallDone : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopR r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemDoneCallS { r with laze := lazeReal xs } snd order kids (fun _ => []) nout env (RK SC0 inl) P SCC x st keep
        (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR)
        b ML CACHE)
    (st0 : St Noun NeedOrd)
    (hleftMust : ∀ TOP, TopN (maySweep (cfgRealSS2 r xs snd order kids) st0).ml TOP →
      ∀ (st : St Noun NeedOrd) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      SweepLeft r xs order kids inl P Mode.must
        (topOf (cfgRealSS2 r xs snd order kids) (maySweep (cfgRealSS2 r xs snd order kids) st0)) TOP st
        SCC CODE (C JETS CALLS) JH b ML CACHE)
    (hQ : ∀ CA, QK env (RK SC0 inl) P SCC x CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds r.scc st0.sure (C NARY CR))
    (hq0 : QK env (RK SC0 inl) P SCC x (C NARY CR)) :
    ∃ s, compileSccIn (cfgRealSS2 r xs snd order kids) false
        (4 * (cfgRealSS2 r xs snd order kids).scc.length + (cfgRealSS2 r xs snd order kids).order.length * (rk.H + 1) + 2)
        st0 = some s ∧
      (∀ b ∈ (cfgRealSS2 r xs snd order kids).scc, (s.ml b).isSome) ∧
      (∀ k, k ∉ (cfgRealSS2 r xs snd order kids).scc → s.ml k = none) ∧
      ∃ M NR REST NARYU, LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) s.ml s.sure M (C NR REST) ∧
        IsMap mugF NR ∧ IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
        nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
          = some (C M (C NARYU REST)) ∧
        ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun ∧
          ∀ b : Bell, (m.1 b).map Straight.need = s.ml b.toNoun := by
  have e := cfgRealSS2_eq r xs snd order kids hag
  revert rk hcfg hleftMust
  rw [e]
  intro rk hcfg hleftMust
  exact csi_gate_ranked_soft r xs snd order kids rk (fun _ => []) nout env SC0 inl P x SCC CODE JETS CALLS JH NARY CR
    hsam hmiss hnd hcfg hbell hS hxS
    (fun st keep b ML CACHE hb hR =>
      memSweepCall_of_A (Or.inr rfl) hrs hPS hre hset hcn topH_nil hR (hleftMay st b ML CACHE hb hR))
    hcallDone st0
    (fun TOP hT st keep b ML CACHE hb hR =>
      memSweepCall_of_A (Or.inl rfl) hrs hPS hre hset hcn (topH_of_topN hT) hR (hleftMust TOP hT st b ML CACHE hb hR))
    hQ hml0 hsu0 hq0

/-- On `%may` / `%must`, `member` of `cfgRealSS2` is that of `cfgRealShape`. -/
theorem cfgRealSS2_member_sweep (r : RealCfg) (xs : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (top : Noun → NeedOrd) (b : Noun) (mode : Mode) (hm : mode ≠ Mode.done)
    (keep : Bool) (st : St Noun NeedOrd) :
    member (cfgRealSS2 r xs snd order kids) top b mode keep st
      = member (cfgRealShape r xs order kids) top b mode keep st :=
  member_cfg_congr _ _ top b mode keep st rfl rfl fun vn vs =>
    (cfgRealSS2_comp_sweep r xs snd order kids b mode hm vn vs).trans
      (cfgRealSS_comp_sweep r xs snd order kids b mode hm vn vs)

/-- **The loop's gate for a real SCC on the fixed soft model, no `RunAgree`**: the sweeps' calls
from `SweepLeft` (track A's branch), the `%done` calls from `MemDoneCallS2` (`runLCS2`,
`finishLFCS2`, the pill's `finish` with tries `FinGateS2`). -/
theorem csi_gate_ranked_soft2F (r : RealCfg) (xs : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun)
    (rk : Ranked (cfgRealSS2 r xs snd order kids)) (nout : Noun → NeedOrd)
    (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P : Noun → Prop) (x : GenRest)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf (cfgRealSS2 r xs snd order kids) SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
    (hbell : ∀ k ∈ tapList SCC, ∃ b' : Bell, b'.toNoun = k)
    (hS : ∀ b ∈ r.scc, b ∈ tapList SCC)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (hrs : r.scc = tapList SCC) (hPS : ∀ k ∈ tapList SCC, ¬ P k) (hre : r.env = env)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc))) (hcn : CodeNomms xs.cod CODE)
    (hleftMay : ∀ (st : St Noun NeedOrd) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      SweepLeft r xs order kids inl P Mode.may (fun _ => NeedOrd.none) (A 0) st SCC CODE (C JETS CALLS) JH b ML CACHE)
    (hcallDone : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopR r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemDoneCallS2 { r with laze := lazeReal xs } snd order kids (fun _ => []) nout env (RK SC0 inl) P SCC x st keep
        (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR)
        b ML CACHE)
    (st0 : St Noun NeedOrd)
    (hleftMust : ∀ TOP, TopN (maySweep (cfgRealSS2 r xs snd order kids) st0).ml TOP →
      ∀ (st : St Noun NeedOrd) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      SweepLeft r xs order kids inl P Mode.must
        (topOf (cfgRealSS2 r xs snd order kids) (maySweep (cfgRealSS2 r xs snd order kids) st0)) TOP st
        SCC CODE (C JETS CALLS) JH b ML CACHE)
    (hQ : ∀ CA, QK env (RK SC0 inl) P SCC x CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds r.scc st0.sure (C NARY CR))
    (hq0 : QK env (RK SC0 inl) P SCC x (C NARY CR)) :
    ∃ s, compileSccIn (cfgRealSS2 r xs snd order kids) false
        (4 * (cfgRealSS2 r xs snd order kids).scc.length + (cfgRealSS2 r xs snd order kids).order.length * (rk.H + 1) + 2)
        st0 = some s ∧
      (∀ b ∈ (cfgRealSS2 r xs snd order kids).scc, (s.ml b).isSome) ∧
      (∀ k, k ∉ (cfgRealSS2 r xs snd order kids).scc → s.ml k = none) ∧
      ∃ M NR REST NARYU, LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) s.ml s.sure M (C NR REST) ∧
        IsMap mugF NR ∧ IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
        nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
          = some (C M (C NARYU REST)) ∧
        ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun ∧
          ∀ b : Bell, (m.1 b).map Straight.need = s.ml b.toNoun := by
  have hmay := memGate_congr (cfgRealShape r xs order kids) (cfgRealSS2 r xs snd order kids) _ _ _ _ Mode.may _
    (fun _ h => h) (fun b keep st _ => cfgRealSS2_member_sweep r xs snd order kids _ b Mode.may (by decide) keep st)
    (memGate_may_K r xs order kids (fun _ => []) nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS
      (fun st keep b ML CACHE hb hR =>
        memSweepCall_of_A (Or.inr rfl) hrs hPS hre hset hcn topH_nil hR (hleftMay st b ML CACHE hb hR)))
  have hdone := memGate_done_KS2 { r with laze := lazeReal xs } snd order kids (fun _ => []) nout env SC0 inl P SCC
    CODE JETS CALLS JH x NARY CR hS hxS hcallDone
  have hmust : ∀ TOP, TopN (maySweep (cfgRealSS2 r xs snd order kids) st0).ml TOP →
      MemGate (cfgRealSS2 r xs snd order kids) (LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x))
        (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
        (topOf (cfgRealSS2 r xs snd order kids) (maySweep (cfgRealSS2 r xs snd order kids) st0)) TOP Mode.must
        (A 0x7473756d) := fun TOP hT =>
    memGate_congr (cfgRealShape r xs order kids) (cfgRealSS2 r xs snd order kids) _ _ _ _ Mode.must _
      (fun _ h => h) (fun b keep st _ => cfgRealSS2_member_sweep r xs snd order kids _ b Mode.must (by decide) keep st)
      (memGate_must_K r xs order kids (fun _ => []) nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS
        (maySweep (cfgRealSS2 r xs snd order kids) st0) TOP hT
        (fun st keep b ML CACHE hb hR =>
          memSweepCall_of_A (Or.inl rfl) hrs hPS hre hset hcn (topH_of_topN hT) hR (hleftMust TOP hT st b ML CACHE hb hR)))
  exact csi_gate_ranked_dec (cfgRealSS2 r xs snd order kids) rk r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x)
    SCC CODE JETS CALLS JH NARY CR hsam hmiss hnd hcfg hbell hmay hdone st0 hmust hQ hml0 hsu0 hq0

end Compiler
end Formalization
