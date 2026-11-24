import lemmas.Ska.CompConsN
import lemmas.Ska.CompN5

/-!
# `[5 p q]` whose operands have `%6` in them

`runOKG_n5`: the case `[5 p q]` of `runL` for a fork-free goal, from
`NextOK` and `CleanN` of `p` and `q`, through `binaryN_ok`.  The case first
takes two fresh registers `rp` and `rq` and emits the block that compares
them (`n5Pre`, the same computation in `run` and in `runL` on a fork-free
goal, `runL_n5_toL`), then compiles `q` for `%next` of `rq` into that block
and `p` for `%next` of `rp` into the block of `q`, and puts the two needs
side by side with `+copy`.

`n5Pre_ok` is the block part of `run_n5_ok` (`CompN5.lean`) with what
`binaryN_ok` asks besides: the block grows the state (`Grow`), keeps `cond`,
and its label is in `[1, bo)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The block of `[5 p q]` that compares `rp` and `rq`, for a fork-free
goal: for `%pick` a branch to the goal's jumps, for `%done` a branch to two
blocks that return `0` and `1`, for `%next` through `+collapse-lazy-atom` and
`+forl`, or `%equ` when the goal asks nothing of the product. -/
def n5Pre (rp rq : Nat) : CGoal S → CM Map Nat
  | CGoal.pick z o => emit ⟨[], [], Termin.eqq rp rq z o⟩
  | CGoal.done => do
      let (o0, o1) ← doneBlocks
      emit ⟨[], [], Termin.eqq rp rq (jmp0 o0) (jmp0 o1)⟩
  | CGoal.next laz th => do
      let a ← collapseLazyAtom ⟨laz, th⟩
      match a with
      | Option.none =>
          if th.args = [] then emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩
          else fun _ => Option.none
      | some (r, o) => do
          let (z, o') ← forl r o
          emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩

/-- **The case `%5` of `runL` on a fork-free goal.** -/
theorem runL_n5_toL (p q : Nomm) (goal : CGoal S) (region : List Nat) :
    (runL (Nomm.n5 p q) (CGoal.toL goal) region : CM Map (NextL S)) = (do
      let rp ← re
      let rq ← re
      let o ← n5Pre rp rq goal
      let nexq ← runL q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL noCode nexq p region
      let nexp ← runL p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz) := by
  cases goal with
  | pick z o => conv => lhs; unfold runL
                rfl
  | done => conv => lhs; unfold runL
            rfl
  | next laz th =>
    conv => lhs; unfold runL
    simp only [CGoal.toL, n5Pre, collapseLazyAtomL_mk]
    rfl

theorem kc_n5Pre (rp rq : Nat) (goal : CGoal S) : KC (n5Pre rp rq goal : CM Map Nat) := by
  cases goal with
  | pick z o => exact KC.emit' _
  | done => exact KC.bind' kc_doneBlocks fun _ => KC.emit' _
  | next laz th =>
    refine KC.bind' (kc_collapseLazyAtom _) fun a => ?_
    split
    · exact KC.ite' _ (KC.emit' _) KC.fail
    · exact KC.bind' (kc_forl _ _) fun _ => KC.emit' _

/-- **The block of `%5`**: the block part of `run_n5_ok`, with `Grow`, and
the label of the block in `[1, bo)`. -/
theorem n5Pre_ok {lib : Lib} {goal : CGoal S} {g0 g2 : Gen Map} {o : Nat}
    (h2 : n5Pre g0.re (g0.re + 1) goal { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } = some (o, g2))
    (hg : GoalOK g0 goal) (hj : GJ g0.bo goal) (b0 : 1 ≤ g0.bo) :
    Ext g0 g2 ∧ Grow g0 g2 ∧ g0.re + 2 ≤ g2.re ∧ 1 ≤ o ∧ o < g2.bo ∧
    ∀ (c : Straight Map), Agree c g0 g2 → g0.drop = false → ∀ (σ : Type) (O : Oracle σ) st regs t gul x y,
      SkaModel.read g0.re regs = some x → SkaModel.read (g0.re + 1) regs = some y →
      GoalSem lib O c gul st (Keep g0 g2 goal) regs t (jmp0 o) goal (some (eqCode x y)) := by
  have G0 : Ext g0 { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } := (ext_re _).trans (ext_re _)
  have G0g : Grow g0 { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } := (grow_re _).trans (grow_re _)
  cases goal with
  | pick z o' =>
    simp only [n5Pre, emit_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine ⟨G0.trans (ext_emit _ _), G0g.trans (grow_emit (jumpsBelow_two rfl hj.1 hj.2)),
      by simp [emitted_re], b0, by simp [emitted_bo], fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
    have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    by_cases e : x = y
    · rw [if_pos e] at hj
      simp only [eqCode, if_pos e]
      exact ⟨regs, fun _ _ => rfl, hj⟩
    · rw [if_neg e] at hj
      simp only [eqCode, if_neg e]
      exact ⟨regs, fun _ _ => rfl, hj⟩
  | done =>
    simp only [n5Pre] at h2
    obtain ⟨⟨o0, o1⟩, g5, h5, h2⟩ := bind_some h2
    have B := doneBlocks_down h5 b0
    obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h5
    rw [emit_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine ⟨G0.trans (D.trans (ext_emit _ _)), G0g.trans (B.1.trans (grow_emit (jumpsBelow_two rfl B.2.1 B.2.2))),
      by simp only [emitted_re, er]; omega, Nat.le_trans b0 B.1.bo, by simp [emitted_bo],
      fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
    have hd5 : g5.drop = false := D.2.2.1.trans hd
    have hb := emitted_get' hd5 (hc _ (by simp only [eb]; omega) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    have DB' := DB c hd ((hc.right G0).left D (ext_emit _ _)) lib σ O st regs t gul
    show goJ lib O c gul st regs t (jmp0 g5.bo) = some (toneOf t (some (eqCode x y)), st)
    by_cases e : x = y
    · rw [if_pos e] at hj; simp only [eqCode, if_pos e]; exact hj.trans DB'.1
    · rw [if_neg e] at hj; simp only [eqCode, if_neg e]; exact hj.trans DB'.2
  | next laz th =>
    simp only [n5Pre] at h2
    obtain ⟨a, g5, h5, h2⟩ := bind_some h2
    obtain ⟨E5, ea, hnone, hsome⟩ := collapse_ok h5
    have C := collapse_down h5 hj.1 hj.2 b0
    have l5 := E5.1
    simp only at l5
    cases a with
    | none =>
      obtain ⟨hn, hl⟩ := hnone rfl
      simp only at h2
      rw [if_pos ea, emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      refine ⟨G0.trans (E5.trans (ext_emit _ _)),
        G0g.trans (C.1.trans (grow_emit (jumpsBelow_one rfl ⟨hj.1, Nat.lt_of_lt_of_le hj.2 C.1.bo⟩))),
        by simp only [emitted_re]; omega, Nat.le_trans b0 C.1.bo, by simp [emitted_bo],
        fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
      have hd5 : g5.drop = false := E5.2.2.1.trans hd
      have hb := emitted_get' hd5 (hc _ (by have := E5.2.1; simp at this; omega) (by simp [emitted_bo]))
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
      rw [show [Pole.equ g0.re (g0.re + 1)] = [Pole.equ g0.re (g0.re + 1)] ++ [] from rfl, runs_equ hx hy,
        execBlob_hop, jmp0_of_args ea] at hj
      exact ⟨fun _ => ⟨regs, by rw [hn]; trivial, fun _ _ => rfl, hj⟩,
        fun hf => absurd ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩ hf⟩
    | some ro =>
      obtain ⟨r, o''⟩ := ro
      obtain ⟨hmr, _, hs⟩ := hsome r o'' rfl
      have Co := C.2 r o'' rfl
      simp only at h2
      obtain ⟨⟨z, o'⟩, g6, h6, h2⟩ := bind_some h2
      have hr : r < g5.re := by
        rcases hmr with hm | ⟨_, h⟩
        · have := hg.2 r hm; omega
        · exact h
      have Fd := forl_down h6 Co.1 Co.2 (Nat.le_trans b0 C.1.bo)
      obtain ⟨E6, er6, eb6, F⟩ := forl_ok h6 hr
      rw [emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have Ep := ext_emit g6 ⟨[], [], Termin.eqq g0.re (g0.re + 1) (jmp0 z) (jmp0 o')⟩
      refine ⟨G0.trans (E5.trans (E6.trans Ep)),
        G0g.trans (C.1.trans (Fd.1.trans (grow_emit (jumpsBelow_two rfl Fd.2.1 Fd.2.2)))),
        by simp only [emitted_re, er6]; omega, Nat.le_trans b0 (Nat.le_trans C.1.bo Fd.1.bo), by simp [emitted_bo],
        fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
      have hd5 : g5.drop = false := E5.2.2.1.trans hd
      have hd6 : g6.drop = false := E6.2.2.1.trans hd5
      have hb := emitted_get' hd6 (hc _ (by have := E5.2.1; have := E6.2.1; simp at *; omega)
        (by simp [emitted_bo]))
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
      rw [execBlob_eqq, hx, hy] at hj
      simp only [Option.bind_some] at hj
      have F' := F hd5 c ((hc.right (G0.trans E5)).left E6 Ep) lib σ O st regs t gul
      have hagX := (hc.right G0).left E5 (E6.trans Ep)
      have keep : ∀ (v : Noun) (k rr : Nat), g5.re ≤ k → k < g5.re + 2 →
          Keep g0 (g6.emitted ⟨[], [], Termin.eqq g0.re (g0.re + 1) (jmp0 z) (jmp0 o')⟩) (CGoal.next laz th) rr →
          SkaModel.read rr (store r v (store k v regs)) = SkaModel.read rr regs := by
        intro v k rr hk hk' ⟨k1, k2⟩
        simp only [emitted_re, er6] at k1
        have hne : rr ≠ r := fun e => by
          subst e
          rcases hmr with hm | ⟨hm, _⟩
          · exact k2 hm
          · simp at hm; omega
        rw [read_store_ne hne, read_store_ne (show rr ≠ k by omega)]
      by_cases e : x = y
      · rw [if_pos e] at hj
        simp only [eqCode, if_pos e]
        exact GoalSem.transfer (hj.trans F'.1) (keep (A 0) g5.re · (Nat.le_refl _) (by omega))
          (hs hd c hagX lib σ O st _ t gul 0 (read_store_eq _ _ _))
      · rw [if_neg e] at hj
        simp only [eqCode, if_neg e]
        exact GoalSem.transfer (hj.trans F'.2) (keep (A 1) (g5.re + 1) · (Nat.le_succ _) (by omega))
          (hs hd c hagX lib σ O st _ t gul 1 (read_store_eq _ _ _))

theorem sixCount_n5 (p q : Nomm) : sixCount (Nomm.n5 p q) = sixCount p + sixCount q := rfl

/-- **`[5 p q]` for a fork-free goal**, from `NextOK` and `CleanN` of the
operands. -/
theorem runOKG_n5 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (hq : NextOK (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q) (hpp : p.pure = true)
    {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hg : GoalOK g0 goal) (hj : GJ g0.bo goal) (hcount : sixCount (Nomm.n5 p q) ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n5 p q) (CGoal.toL goal) region g0 = some (nex, g1)) :
    RunOKG (Map := Map) lib (Nomm.n5 p q) goal g0 g1 nex := by
  rw [runL_n5_toL] at h
  obtain ⟨rp, gA, hA, h⟩ := bind_some h
  obtain ⟨rq, gB, hB, h⟩ := bind_some h
  rw [re_apply] at hA hB
  simp only [Option.some.injEq, Prod.mk.injEq] at hA hB
  obtain ⟨rfl, rfl⟩ := hA
  obtain ⟨rfl, rfl⟩ := hB
  obtain ⟨o, g2, h2, h⟩ := bind_some h
  have c2 : g2.cond = g0.cond := ((kc_n5Pre _ _ goal).keep _ o g2 h2).trans rfl
  obtain ⟨E2, G2, hre, o1, o2, B⟩ := n5Pre_ok (lib := lib) h2 hg hj b0
  obtain ⟨nexq, g3, h3, h⟩ := bind_some h
  obtain ⟨nexq', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, g4, h4, hc⟩ := bind_some h
  rw [sixCount_n5] at hcount
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (G2.toU hu).up hu
  have Rq := hq (sur := lazyReg (g0.re + 1)) (th := jmp0 o) ⟨o1, o2⟩ rfl
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; omega⟩ trivial (by omega)
    (Nat.le_trans b0 G2.bo) d2 u2 h3
  have Rp := hp (sur := lazyReg g0.re) (th := nexq.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; have := Rq.ext.1; omega⟩ trivial (by omega)
    (Nat.le_trans b0 (Nat.le_trans G2.bo Rq.grow.bo)) (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) h4
  exact binaryN_ok (pureEval_n5 p q) hg E2 (G2.toU hu) c2
    (fun r hr => by simp only [lazyReg, NMem] at hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r hr => by simp only [lazyReg, NMem] at hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r h1 h2 => by simp only [lazyReg, NMem] at h1 h2; omega) Rq Rp
    (cq (sur := lazyReg _) trivial h3) (cp (sur := lazyReg _) trivial h4) hc hu d0 (Nat.le_of_eq (sixCount_n5 p q).symm)
    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_lazyReg _ x)) (fun a => a (fitsS_lazyReg _ y))) id)
    (fun c hc σ O st regs t gul x y _ _ hx hy => B c hc d0 σ O st regs t gul x y hx hy)

end Comp
end SkaModel
end Formalization
