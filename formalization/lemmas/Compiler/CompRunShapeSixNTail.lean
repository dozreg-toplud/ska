import lemmas.Compiler.CompRunShapeECases
import lemmas.Compiler.CompRunShapeSixNCut

/-!
# `+run-shape`, case `%6`: the tail shared by `goal-branch` and the fork (track A, 2026-11-28)

`sixTailN F1 F2 F3` (`CompRunShapeSixNCut.lean`) is the end of the case `%6` both under `%done` /
`%pick` / `goal-branch` (`rs6Rest`) and in the fork of the kerf: the run of `r` on the goal `F1`
gives, of `q` on `F2`, `+laze-sect`, `+laze-past-fork` over `p`, `this` if `+laze-big`, the run of
`p` on `F3`, `+laze-copy`.  Its model is `sixTailM`: `sixBranch` is it on `gb`, `gb`, `%pick`
(`sixBranch_tail`), `sixFork` is `+laze-branch` then it on `[%next g1]`, `[%next g0]`,
`[%next this]` (`sixFork_tail`).

* **`six_tail`**: on every subject `[X [LEP rsS]]` whose `F1`, `F2`, `F3` give the goals' nouns
  (`F3` reads at most `this` of the subject),
  from the runs of `r`, `q`, `p` on `RsAtE` at the rest `y`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop}

/-- The model of the tail. -/
noncomputable def sixTailM (env : ShapeEnv) (rp rq rr : GoalS CSet → SM CSet (Laze CSet)) (p : Nomm)
    (gr gq gp : GoalS CSet) : SM CSet (Laze CSet) := do
  let l1 ← rr gr
  let l0 ← rq gq
  let lazy ← lazeSect l0 l1
  let lazy ← shLiftS (lazePastFork env lazy p)
  let st ← get
  let lazy := if lazeBig (sofsHas st.sofs) lazy then thisL else lazy
  let lc ← rp gp
  shLiftS (lazeCopy lc lazy)

theorem sixBranch_tail (env : ShapeEnv) (rp rq rr : GoalS CSet → SM CSet (Laze CSet)) (p : Nomm)
    (gb : GoalS CSet) : sixBranch env rp rq rr p gb = sixTailM env rp rq rr p gb gb GoalS.pick := rfl

theorem sixFork_tail (env : ShapeEnv) (rp rq rr : GoalS CSet → SM CSet (Laze CSet)) (p : Nomm)
    (laz : Laze CSet) (st : RSt CSet) :
    sixFork env rp rq rr p laz st = (lazeBranch laz st).bind fun r =>
      sixTailM env rp rq rr p (GoalS.next r.1.2) (GoalS.next r.1.1) (GoalS.next thisL) r.2 := by
  simp only [sixFork, sixTailM, bind, StateT.bind]

set_option hygiene false in
/-- The simp set of the leaves of `six_tail`. -/
local macro "tail_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [nock_exec, rsS,
  rsCoreG, rsDoor, sixTailM, bind, StateT.bind, get, getThe, MonadState.get, StateT.get, shLiftS, pure,
  StateT.pure, rs6_get, thisL_noun, eqCode_atom, hF1, hF2, hF3, $xs,*])

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The tail of the case `%6`** on the subject `[X [LEP rsS]]`, the goals given by `F1`, `F2`,
`F3`. -/
theorem six_tail (env : ShapeEnv) (p q r : Nomm) (sup : Option Nomm) (gr gq gp : GoalS CSet)
    (st : RSt CSet) (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p)
    (hr : ∀ st1, RsAtE ctx env E r sup gr st1)
    (hq : ∀ st1, RsAtE ctx env E q sup gq st1)
    (hp : ∀ st1, RsAtE ctx env E p sup gp st1)
    (X LEP s goalN F1 F2 F3 : Noun)
    (hF1 : ∀ Z, nock (C X Z) F1 = some gr.toNoun)
    (hF2 : ∀ a Z, nock (C a (C X Z)) F2 = some gq.toNoun)
    (hF3 : ∀ a b c Z, nock (C a (C b (C c (C X (C LEP (C s (C (C (C (C (A 0x73696874) (A 0)) (A 0)) (C (A 0) (A 0)))
      Z))))))) F3 = some gp.toNoun) :
    nock (C X (C LEP (rsS s (Nomm.n6 p q r).toNoun goalN (supNoun sup) (rsDoor st y ctx)))) (sixTailN F1 F2 F3)
      = (sixTailM env (runShape env sup p) (runShape env sup q) (runShape env sup r) p gr gq gp st).map
          fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  unfold sixTailN
  have hr' := hr st y hy
  simp only [rsCoreG, rsDoor] at hr'
  cases e1 : runShape env sup r gr st with
  | none => rw [e1] at hr'; tail_simp [hr', e1]
  | some r1 =>
    obtain ⟨l1, st1⟩ := r1
    rw [e1] at hr'
    have hq' := hq st1 y hy
    simp only [rsCoreG, rsDoor] at hq'
    cases e2 : runShape env sup q gq st1 with
    | none => rw [e2] at hq'; tail_simp [hr', e1, hq', e2]
    | some r2 =>
      obtain ⟨l0, st2⟩ := r2
      rw [e2] at hq'
      have hs := lzs_gate (ctx := ctx) st2 y l0 l1
      simp only [rsDoor] at hs
      cases e3 : lazeSect l0 l1 st2 with
      | none => rw [e3] at hs; tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3]
      | some r3 =>
        obtain ⟨lz, st3⟩ := r3
        rw [e3] at hs
        have hpf := lpf_gate hc h7 hcode env p hcp (rsGenNoun st3 y) lz
        cases e4 : lazePastFork env lz p with
        | none =>
          rw [e4] at hpf
          tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4]
        | some lz' =>
          rw [e4] at hpf
          have hbg := lbg_gate hc h7 st3 y lz'
          simp only [rsDoor] at hbg
          have hp' := hp st3 y hy
          simp only [rsCoreG, rsDoor] at hp'
          cases e5 : runShape env sup p gp st3 with
          | none =>
            rw [e5] at hp'
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true <;>
            · tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                lbg_at', lbg_arm, hbg, hb, loob, hp', e5]
          | some r5 =>
            obtain ⟨lc, st4⟩ := r5
            rw [e5] at hp'
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true
            · have hlc := lc_all hc h7 (rsGenNoun st4 y) lc thisL
              rw [thisL_noun] at hlc
              cases e6 : lazeCopy lc thisL with
              | none =>
                rw [e6] at hlc
                tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
              | some l =>
                rw [e6] at hlc
                tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
            · simp only [Bool.not_eq_true] at hb
              have hlc := lc_all hc h7 (rsGenNoun st4 y) lc lz'
              cases e6 : lazeCopy lc lz' with
              | none =>
                rw [e6] at hlc
                tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
              | some l =>
                rw [e6] at hlc
                tail_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]

end

end Compiler
end Formalization
