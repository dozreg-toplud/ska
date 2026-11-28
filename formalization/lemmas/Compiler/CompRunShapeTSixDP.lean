import lemmas.Compiler.CompRunShapeTDefs
import lemmas.Compiler.CompRunShapeECases

/-!
# `+run-shape` threading the rest: `%6` under `%done` / `%pick` (track A, 2026-11-28)

`rs_n6DPE` (`CompRunShapeECases.lean`) on `RsAtT`: each recursive run moves the rest of `gen` from
`y` to some `y'` (`Rl y y'`, a miss in `+callee-need` grows the cache), and every helper arm and later
run after it is read at the new rest.

* **`rs_n6DPT`**: the case `[6 p q r]` under `%done` and `%pick`, threaded.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop}

set_option hygiene false in
/-- The simp set of the leaves of `rs_n6DP`. -/
local macro "six_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [nock_exec, rsS,
  rsCoreG, rsDoor, sixBranch, bind, StateT.bind, get, getThe, MonadState.get, StateT.get, shLiftS, pure,
  StateT.pure, rs6_get, hne, hne', rs6Lep, rs6Tk, rs6Gb, rs6Rest, GoalS.toNoun, thisL_noun, eqCode_atom, $xs,*])

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[6 p q r]` under `%done` and `%pick`, threading the rest**: the runs of `r` and `q`
on the goal, `+laze-sect`, `+laze-past-fork` over `p`, `this` if `+laze-big`, the run of `p` under
`%pick`, `+laze-copy` (`sixBranch`), each read at the rest the run before it left. -/
theorem rs_n6DPT (env : ShapeEnv) (hR : RlPre Rl) (p q r : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (hnn : goal = GoalS.done ∨ goal = GoalS.pick) (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hr : ∀ st1, RsAtT ctx env E Rl r sup goal st1)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup goal st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup GoalS.pick st1) :
    RsAtT ctx env E Rl (Nomm.n6 p q r) sup goal st := by
  intro y hy
  obtain ⟨tag, htag, hne⟩ := rs6_goal goal hnn
  have hne' : ¬ (0x7478656e = tag) := fun h => hne h.symm
  rw [rs6_model env sup p q r goal hnn]
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n6, rsK6_eq, htag]
  unfold rs6Arm
  obtain ⟨y1, hR1, hy1, hr'⟩ := hr st y hy
  simp only [rsCoreG, rsDoor, htag] at hr'
  cases e1 : runShape env sup r goal st with
  | none => rw [e1] at hr'; exact ⟨y1, hR1, hy1, by six_simp [hr', e1]⟩
  | some r1 =>
    obtain ⟨l1, st1⟩ := r1
    rw [e1] at hr'
    obtain ⟨y2, hR2, hy2, hq'⟩ := hq st1 y1 hy1
    have hR12 := hR.trans hR1 hR2
    simp only [rsCoreG, rsDoor, htag] at hq'
    cases e2 : runShape env sup q goal st1 with
    | none => rw [e2] at hq'; exact ⟨y2, hR12, hy2, by six_simp [hr', e1, hq', e2]⟩
    | some r2 =>
      obtain ⟨l0, st2⟩ := r2
      rw [e2] at hq'
      have hs := lzs_gate (ctx := ctx) st2 y2 l0 l1
      simp only [rsDoor] at hs
      cases e3 : lazeSect l0 l1 st2 with
      | none => rw [e3] at hs; exact ⟨y2, hR12, hy2, by six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3]⟩
      | some r3 =>
        obtain ⟨lz, st3⟩ := r3
        rw [e3] at hs
        have hpf := lpf_gate hc h7 hcode env p hcp (rsGenNoun st3 y2) lz
        cases e4 : lazePastFork env lz p with
        | none =>
          rw [e4] at hpf
          exact ⟨y2, hR12, hy2, by six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4]⟩
        | some lz' =>
          rw [e4] at hpf
          have hbg := lbg_gate hc h7 st3 y2 lz'
          simp only [rsDoor] at hbg
          obtain ⟨y3, hR3, hy3, hp'⟩ := hp st3 y2 hy2
          have hR123 := hR.trans hR12 hR3
          simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
          cases e5 : runShape env sup p GoalS.pick st3 with
          | none =>
            rw [e5] at hp'
            refine ⟨y3, hR123, hy3, ?_⟩
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true <;>
            · six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                lbg_at', lbg_arm, hbg, hb, loob, hp', e5]
          | some r5 =>
            obtain ⟨lc, st4⟩ := r5
            rw [e5] at hp'
            refine ⟨y3, hR123, hy3, ?_⟩
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true
            · have hlc := lc_all hc h7 (rsGenNoun st4 y3) lc thisL
              rw [thisL_noun] at hlc
              cases e6 : lazeCopy lc thisL with
              | none =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
              | some l =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
            · simp only [Bool.not_eq_true] at hb
              have hlc := lc_all hc h7 (rsGenNoun st4 y3) lc lz'
              cases e6 : lazeCopy lc lz' with
              | none =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
              | some l =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]

end

end Compiler
end Formalization
