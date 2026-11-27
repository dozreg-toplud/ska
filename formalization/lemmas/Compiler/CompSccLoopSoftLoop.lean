import lemmas.Compiler.CompSccLoopShapeLoop
import lemmas.Compiler.CompSccLoopSoftMemDone
import lemmas.Ska.SccLoopSoftShape

/-! # The loop of `+compile-scc-in` for a real SCC with soft members (README Gaps 21.19)

`csi_gate_ranked_dec` (`CompSccLoopStrDec.lean`) for `c := cfgRealSS r xs snd order kids`
(`Ska/SccLoopSoftShape.lean`: the `%done` compile `memDoneMS`, soft calls included, the sweeps
track A's `+run-shape`): the `%may` and `%must` gates are `memGate_may_K` / `memGate_must_K` of
`cfgRealShape`, carried over by `memGate_congr` (on those modes `member` of the two
configurations is the same, `cfgRealSS_member_sweep`), and the `%done` gate is
`memGate_done_KS` (`MemDoneCallS`, the soft `%done` call: the run in the `CompRunAtXTS` shape and
`hreq`) for the `RealCfg` with `laze := lazeReal xs`, which is `cfgRealSS` by definition. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

/-- **`MemGate` carries over** to a configuration with the same members and the same `member`
on the mode of the gate. -/
theorem memGate_congr {N : Type} [DecidableEq N] (c1 c2 : Cfg Noun N)
    (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop) (ctx : Noun) (top : Noun → N) (TOP : Noun)
    (mode : Mode) (MODE : Noun) (hscc : ∀ b ∈ c2.scc, b ∈ c1.scc)
    (hm : ∀ b keep st, b ∈ c2.scc → member c2 top b mode keep st = member c1 top b mode keep st)
    (h : MemGate c1 R ctx top TOP mode MODE) : MemGate c2 R ctx top TOP mode MODE := by
  intro st keep b ML CA hb hR
  rw [hm b keep st hb]
  exact h st keep b ML CA (hscc b hb) hR

/-- **The loop's gate for a real SCC with soft members**: every member gate discharged up to its
calls, `MemSweepCall` on `%may` / `%must`, `MemDoneCallS` on `%done` (soft or not). -/
theorem csi_gate_ranked_soft (r : RealCfg) (xs : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun)
    (rk : Ranked (cfgRealSS r xs snd order kids)) (outC : Noun → List Noun) (nout : Noun → NeedOrd)
    (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P : Noun → Prop) (x : GenRest)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf (cfgRealSS r xs snd order kids) SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
    (hbell : ∀ k ∈ tapList SCC, ∃ b' : Bell, b'.toNoun = k)
    (hS : ∀ b ∈ r.scc, b ∈ tapList SCC)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (hcallMay : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc outC nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemSweepCall r xs order kids outC nout env (RK SC0 inl) P SCC x Mode.may (fun _ => NeedOrd.none) (A 0) st keep
        (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR)
        b ML CACHE)
    (hcallDone : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopR r.scc outC nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemDoneCallS { r with laze := lazeReal xs } snd order kids outC nout env (RK SC0 inl) P SCC x st keep (A 1)
        (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR) b ML
        CACHE)
    (st0 : St Noun NeedOrd)
    (hcallMust : ∀ TOP, TopN (maySweep (cfgRealSS r xs snd order kids) st0).ml TOP →
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc outC nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemSweepCall r xs order kids outC nout env (RK SC0 inl) P SCC x Mode.must
        (topOf (cfgRealSS r xs snd order kids) (maySweep (cfgRealSS r xs snd order kids) st0)) TOP st keep
        (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR)
        b ML CACHE)
    (hQ : ∀ CA, QK env (RK SC0 inl) P SCC x CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds r.scc st0.sure (C NARY CR))
    (hq0 : QK env (RK SC0 inl) P SCC x (C NARY CR)) :
    ∃ s, compileSccIn (cfgRealSS r xs snd order kids) false
        (4 * (cfgRealSS r xs snd order kids).scc.length + (cfgRealSS r xs snd order kids).order.length * (rk.H + 1) + 2)
        st0 = some s ∧
      (∀ b ∈ (cfgRealSS r xs snd order kids).scc, (s.ml b).isSome) ∧
      (∀ k, k ∉ (cfgRealSS r xs snd order kids).scc → s.ml k = none) ∧
      ∃ M NR REST NARYU, LoopRS r.scc outC nout (QK env (RK SC0 inl) P SCC x) s.ml s.sure M (C NR REST) ∧
        IsMap mugF NR ∧ IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
        nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
          = some (C M (C NARYU REST)) ∧
        ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun ∧
          ∀ b : Bell, (m.1 b).map Straight.need = s.ml b.toNoun := by
  have hmay := memGate_congr (cfgRealShape r xs order kids) (cfgRealSS r xs snd order kids) _ _ _ _ Mode.may _
    (fun _ h => h) (fun b keep st _ => cfgRealSS_member_sweep r xs snd order kids _ b Mode.may (by decide) keep st)
    (memGate_may_K r xs order kids outC nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS hcallMay)
  have hdone := memGate_done_KS { r with laze := lazeReal xs } snd order kids outC nout env SC0 inl P SCC CODE JETS
    CALLS JH x NARY CR hS hxS hcallDone
  have hmust : ∀ TOP, TopN (maySweep (cfgRealSS r xs snd order kids) st0).ml TOP →
      MemGate (cfgRealSS r xs snd order kids) (LoopRS r.scc outC nout (QK env (RK SC0 inl) P SCC x))
        (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
        (topOf (cfgRealSS r xs snd order kids) (maySweep (cfgRealSS r xs snd order kids) st0)) TOP Mode.must
        (A 0x7473756d) := fun TOP hT =>
    memGate_congr (cfgRealShape r xs order kids) (cfgRealSS r xs snd order kids) _ _ _ _ Mode.must _
      (fun _ h => h) (fun b keep st _ => cfgRealSS_member_sweep r xs snd order kids _ b Mode.must (by decide) keep st)
      (memGate_must_K r xs order kids outC nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS
        (maySweep (cfgRealSS r xs snd order kids) st0) TOP hT (hcallMust TOP hT))
  exact csi_gate_ranked_dec (cfgRealSS r xs snd order kids) rk r.scc outC nout (QK env (RK SC0 inl) P SCC x)
    SCC CODE JETS CALLS JH NARY CR hsam hmiss hnd hcfg hbell hmay hdone st0 hmust hQ hml0 hsu0 hq0

end Compiler
end Formalization
