import lemmas.Compiler.CompSccLoopSweepStep
import lemmas.Compiler.CompSccLoopStrDec

/-! # The loop of `+compile-scc-in` with its three member gates discharged (README Gaps 21.18)

`csi_gate_ranked_dec` (`CompSccLoopStrDec.lean`) for `c := cfgRealShape r xs order kids` (the
sweeps modelled by track A's `+run-shape`, `lazeReal`), `bs := r.scc` and track K's `QK`: the
`%may` gate by `memGate_may_K`, the `%done` gate by `memGate_done_KStr` (for the `RealCfg` with
`laze := lazeReal xs`), the `%must` gate by `memGate_must_K` at every `TOP` of `TopN`.  What is left
is what one call of each mode takes: `MemSweepCall` (`%may`, `%must`: the branch's pill computation
`MemShapeBranch`, track A, and the cache it leaves, track K) and `MemDoneCallStr` (`%done`: the run
`CompRunAtXT`, track K), with `hS`, `hxS` and the cache shape `hQ`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

/-- **The loop's gate for a real SCC, every member gate discharged up to its calls.** -/
theorem csi_gate_ranked_shape (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (rk : Ranked (cfgRealShape r xs order kids)) (outC : Noun → List Noun) (nout : Noun → NeedOrd)
    (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P : Noun → Prop) (x : GenRest)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf (cfgRealShape r xs order kids) SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
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
      MemDoneCallStr { r with laze := lazeReal xs } order kids outC nout env (RK SC0 inl) P SCC x st keep (A 1)
        (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR) b ML
        CACHE)
    (st0 : St Noun NeedOrd)
    (hcallMust : ∀ TOP, TopN (maySweep (cfgRealShape r xs order kids) st0).ml TOP →
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc outC nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemSweepCall r xs order kids outC nout env (RK SC0 inl) P SCC x Mode.must
        (topOf (cfgRealShape r xs order kids) (maySweep (cfgRealShape r xs order kids) st0)) TOP st keep
        (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR)
        b ML CACHE)
    (hQ : ∀ CA, QK env (RK SC0 inl) P SCC x CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds r.scc st0.sure (C NARY CR))
    (hq0 : QK env (RK SC0 inl) P SCC x (C NARY CR)) :
    ∃ s, compileSccIn (cfgRealShape r xs order kids) false
        (4 * (cfgRealShape r xs order kids).scc.length + (cfgRealShape r xs order kids).order.length * (rk.H + 1) + 2)
        st0 = some s ∧
      (∀ b ∈ (cfgRealShape r xs order kids).scc, (s.ml b).isSome) ∧
      (∀ k, k ∉ (cfgRealShape r xs order kids).scc → s.ml k = none) ∧
      ∃ M NR REST NARYU, LoopRS r.scc outC nout (QK env (RK SC0 inl) P SCC x) s.ml s.sure M (C NR REST) ∧
        IsMap mugF NR ∧ IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
        nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
          = some (C M (C NARYU REST)) ∧
        ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun ∧
          ∀ b : Bell, (m.1 b).map Straight.need = s.ml b.toNoun :=
  csi_gate_ranked_dec (cfgRealShape r xs order kids) rk r.scc outC nout (QK env (RK SC0 inl) P SCC x)
    SCC CODE JETS CALLS JH NARY CR hsam hmiss hnd hcfg hbell
    (memGate_may_K r xs order kids outC nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS hcallMay)
    (memGate_done_KStr { r with laze := lazeReal xs } order kids outC nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR
      hS hxS hcallDone)
    st0 (fun TOP hT => memGate_must_K r xs order kids outC nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS
      _ TOP hT (hcallMust TOP hT))
    hQ hml0 hsu0 hq0

end Compiler
end Formalization
