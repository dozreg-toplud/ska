import lemmas.Compiler.CompSccLoopSweepA
import lemmas.Compiler.CompSccLoopSoftLoop
import lemmas.Ska.SccLoopSoft2Shape

/-! # The loop for a real SCC on the fixed soft model, the sweeps from track A (README Gaps 21.21)

`csi_gate_ranked_soft` (`CompSccLoopSoftLoop.lean`) for the fixed model `cfgRealSS2`
(`Ska/SccLoopSoft2Shape.lean`: `+crash-need` asking at a soft block, in `%1` and in `%3` / `%4` /
`%5`) where its `%done` runs agree with the old model (`RunAgree`, `cfgRealSS2_eq`), with the
`%may` / `%must` calls no longer taking `MemSweepCall` (whose pill hypothesis was `MemShapeBranch`)
but `SweepLeft` (`CompSccLoopSweepA.lean`: `memSweepCall_of_A`, through track A's
`memShape_branchA6`).

**`csi_gate_ranked_soft2`**: the loop theorem; per sweep call `SweepLeft`, per `%done` call
`MemDoneCallS`, and the loop-level facts `hrs`, `hPS`, `hre`, `hset`, `hcn`. -/

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

end Compiler
end Formalization
