import lemmas.Compiler.CompRunShapeTDefs
import lemmas.Compiler.CompRunShapeSixNTail

/-!
# `+run-shape`, case `%6`: the tail, threading the rest (track A, 2026-11-28)

`six_tail` (`CompRunShapeSixNTail.lean`) on `RsAtT`: the runs of `r`, `q`, `p` may move the rest of
`gen` (a miss of `+callee-need` compiles a callee and returns a bigger cache), so every helper arm
after a run (`+laze-sect`, `+laze-past-fork`, `+laze-big`, `+laze-copy`) is read at the rest that
run returned.

* **`six_tailT`**: on every subject `[X [LEP rsS]]` whose `F1`, `F2`, `F3` give the goals' nouns,
  from the runs of `r`, `q`, `p` on `RsAtT`, the tail returns the model's result with some rest `y'`
  of `E` that `Rl` relates to `y`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop}

set_option hygiene false in
/-- The simp set of the leaves of `six_tailT`. -/
local macro "tail_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [nock_exec, rsS,
  rsCoreG, rsDoor, sixTailM, bind, StateT.bind, get, getThe, MonadState.get, StateT.get, shLiftS, pure,
  StateT.pure, rs6_get, thisL_noun, eqCode_atom, hF1, hF2, hF3, $xs,*])

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The tail of the case `%6`, threading the rest**, on the subject `[X [LEP rsS]]`, the goals
given by `F1`, `F2`, `F3`. -/
theorem six_tailT (env : ShapeEnv) (hR : RlPre Rl) (p q r : Nomm) (sup : Option Nomm) (gr gq gp : GoalS CSet)
    (st : RSt CSet) (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p)
    (hr : ∀ st1, RsAtT ctx env E Rl r sup gr st1)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup gq st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup gp st1)
    (X LEP s goalN F1 F2 F3 : Noun)
    (hF1 : ∀ Z, nock (C X Z) F1 = some gr.toNoun)
    (hF2 : ∀ a Z, nock (C a (C X Z)) F2 = some gq.toNoun)
    (hF3 : ∀ a b c Z, nock (C a (C b (C c (C X (C LEP (C s (C (C (C (C (A 0x73696874) (A 0)) (A 0)) (C (A 0) (A 0)))
      Z))))))) F3 = some gp.toNoun) :
    ∃ y', Rl y y' ∧ E y' ∧
      nock (C X (C LEP (rsS s (Nomm.n6 p q r).toNoun goalN (supNoun sup) (rsDoor st y ctx)))) (sixTailN F1 F2 F3)
        = (sixTailM env (runShape env sup p) (runShape env sup q) (runShape env sup r) p gr gq gp st).map
            fun p => C p.1.toNoun (rsGenNoun p.2 y') := by
  unfold sixTailN
  obtain ⟨y1, hR1, hy1, hr'⟩ := hr st y hy
  simp only [rsCoreG, rsDoor] at hr'
  cases e1 : runShape env sup r gr st with
  | none => rw [e1] at hr'; exact ⟨y1, hR1, hy1, by tail_simp [hr', e1]⟩
  | some r1 =>
    obtain ⟨l1, st1⟩ := r1
    rw [e1] at hr'
    obtain ⟨y2, hR2, hy2, hq'⟩ := hq st1 y1 hy1
    have hR12 := hR.trans hR1 hR2
    simp only [rsCoreG, rsDoor] at hq'
    cases e2 : runShape env sup q gq st1 with
    | none => rw [e2] at hq'; exact ⟨y2, hR12, hy2, by tail_simp [hr', e1, hq', e2]⟩
    | some r2 =>
      obtain ⟨l0, st2⟩ := r2
      rw [e2] at hq'
      have hs := lzs_gate (ctx := ctx) st2 y2 l0 l1
      simp only [rsDoor] at hs
      cases e3 : lazeSect l0 l1 st2 with
      | none => rw [e3] at hs; exact ⟨y2, hR12, hy2, by tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3]⟩
      | some r3 =>
        obtain ⟨lz, st3⟩ := r3
        rw [e3] at hs
        have hpf := lpf_gate hc h7 hcode env p hcp (rsGenNoun st3 y2) lz
        cases e4 : lazePastFork env lz p with
        | none =>
          rw [e4] at hpf
          exact ⟨y2, hR12, hy2, by tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4]⟩
        | some lz' =>
          rw [e4] at hpf
          have hbg := lbg_gate hc h7 st3 y2 lz'
          simp only [rsDoor] at hbg
          obtain ⟨y3, hR3, hy3, hp'⟩ := hp st3 y2 hy2
          have hR123 := hR.trans hR12 hR3
          simp only [rsCoreG, rsDoor] at hp'
          cases e5 : runShape env sup p gp st3 with
          | none =>
            rw [e5] at hp'
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true <;>
            · exact ⟨y3, hR123, hy3, by
                tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5]⟩
          | some r5 =>
            obtain ⟨lc, st4⟩ := r5
            rw [e5] at hp'
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true
            · have hlc := lc_all hc h7 (rsGenNoun st4 y3) lc thisL
              rw [thisL_noun] at hlc
              cases e6 : lazeCopy lc thisL with
              | none =>
                rw [e6] at hlc
                exact ⟨y3, hR123, hy3, by
                  tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                    lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]⟩
              | some l =>
                rw [e6] at hlc
                exact ⟨y3, hR123, hy3, by
                  tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                    lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]⟩
            · simp only [Bool.not_eq_true] at hb
              have hlc := lc_all hc h7 (rsGenNoun st4 y3) lc lz'
              cases e6 : lazeCopy lc lz' with
              | none =>
                rw [e6] at hlc
                exact ⟨y3, hR123, hy3, by
                  tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                    lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]⟩
              | some l =>
                rw [e6] at hlc
                exact ⟨y3, hR123, hy3, by
                  tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                    lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]⟩

end

end Compiler
end Formalization
