import lemmas.Compiler.CompRunShapeThree
import lemmas.Compiler.CompRunShapePast
import lemmas.Compiler.CompRunShapeCopy
import lemmas.Compiler.CompRunShapeSplit

/-!
# `+run-shape`: the cons case and `[5 p q]` (track A, 2026-11-27)

Both cases end in `+laze-copy` (`lc_all`) after `+laze-past` (`lzp_gate`); the cons case under
`%next` starts with `+laze-split` (`lsp_all`).  `+laze-past` reads the code table, so these
cases carry `slot? 7 ctx = some compK`, `slot? 52 ctx = some cod` and `CallCode cod (shapeCE
env)` of the nomm (`CallCode` of a cons or a `%5` is that of both halves).

* `lazePast_nz`: `+laze-past` keeps `LzNZ`.
* **`rs_n5W`**: `[5 p q]` from the runs of `q` and `p` under `[%next this]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **`+laze-past` keeps `LzNZ`.** -/
theorem lazePast_nz (env : ShapeEnv) (laz : Laze CSet) (nom : Nomm) (st : RSt CSet) (r : Laze CSet)
    (st1 : RSt CSet) (hl : LzNZ laz) (e : lazePast env laz nom st = some (r, st1)) : LzNZ r := by
  unfold lazePast at e
  split at e
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]; exact hl
  · simp only [bind, StateT.bind, liftS] at e
    cases e1 : hinted env.pure nom with
    | none => rw [e1] at e; cases e
    | some b =>
      rw [e1] at e
      cases b
      · simp only [Option.map_some, Option.bind_some, Bool.not_false, if_true, pure, StateT.pure,
          Option.some.injEq, Prod.mk.injEq] at e
        rw [← e.1]; exact hl
      · obtain ⟨s, f, bd⟩ := laz
        obtain ⟨hs, hf, hb⟩ := hl
        simp [Option.map_some, Option.bind_some, Bool.not_true, idS, pure, StateT.pure, StateT.bind,
          Laze.sure, Laze.fork, Laze.bond] at e
        rw [← e.1]
        exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, ⟨hs, hf, trivial⟩, hb⟩

theorem rs_disp_n5 (t s goal sup D : Noun) :
    nock (rsS s (C (A 5) t) goal sup D) rsDol = nock (rsS s (C (A 5) t) goal sup D) rsK5 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

theorem rs_nomm_cell (nm : Nomm) : ∃ a b, nm.toNoun = C a b := by
  cases nm <;> exact ⟨_, _, rfl⟩

theorem rs_disp_c (p : Nomm) (Q s goal sup D : Noun) :
    nock (rsS s (C p.toNoun Q) goal sup D) rsDol = nock (rsS s (C p.toNoun Q) goal sup D) rsKc := by
  obtain ⟨a, b, hp⟩ := rs_nomm_cell p
  rw [hp]
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[5 p q]`**: the run of `q` under `[%next this]`, `+laze-past` of its `laze` over
`p`, the run of `p` under `[%next this]`, `+laze-copy` of the two. -/
theorem rs_n5W (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAt ctx env q sup (GoalS.next thisL) st1)
    (hp : ∀ st1, RsAt ctx env p sup (GoalS.next thisL) st1) :
    RsAt ctx env (Nomm.n5 p q) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n5]
  have hq' := hq st y
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hq'
  unfold rsK5
  cases e1 : runShape env sup q (GoalS.next thisL) st with
  | none =>
    rw [e1] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      have hp' := hp st2 y
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hp'
      cases e3 : runShape env sup p (GoalS.next thisL) st2 with
      | none =>
        rw [e3] at hp'
        simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
          hp', e3]
      | some r3 =>
        obtain ⟨lp, st3⟩ := r3
        rw [e3] at hp'
        have hlc := lc_all hc h7 (rsGenNoun st3 y) lp lq'
        cases e4 : lazeCopy lp lq' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, liftS]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, liftS]


/-- **The cons case under `[%next laz]`**: `+laze-split` of `laz`, `+laze-past` of the head
over `q`, the run of `q` on the tail, `+laze-past` of its `laze` over `p`, the run of `p` on
the head, `+laze-copy` of the two (`consNext`). -/
theorem rs_consN (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (laz : Laze CSet) (hl : LzNZ laz)
    (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p) (hcq : CallCode cod (shapeCE env) q)
    (hq : ∀ l st1, LzNZ l → RsAt ctx env q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAt ctx env p sup (GoalS.next l) st1) :
    RsAt ctx env (Nomm.cons p q) sup (GoalS.next laz) st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_c]
  obtain ⟨hed, tel, es⟩ := lazeSplit_ex laz hl
  obtain ⟨hnz, tnz⟩ := lazeSplit_nz laz hl hed tel es
  have hsp := lsp_all hc (rsGenNoun st y) laz hl
  rw [es] at hsp
  simp only [Option.map_some] at hsp
  have hpa1 := lzp_gate h7 hcode env q hcq st y hed
  simp only [rsDoor] at hpa1
  unfold rsKc
  cases e2 : lazePast env hed q st with
  | none =>
    rw [e2] at hpa1
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, liftS,
      bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2]
  | some r2 =>
    obtain ⟨hed', st1⟩ := r2
    rw [e2] at hpa1
    have hq' := hq tel st1 tnz y
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
    cases e3 : runShape env sup q (GoalS.next tel) st1 with
    | none =>
      rw [e3] at hq'
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, liftS,
        bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3]
    | some r3 =>
      obtain ⟨l2, st2⟩ := r3
      rw [e3] at hq'
      have hpa2 := lzp_gate h7 hcode env p hcp st2 y l2
      simp only [rsDoor] at hpa2
      cases e4 : lazePast env l2 p st2 with
      | none =>
        rw [e4] at hpa2
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, liftS,
          bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4]
      | some r4 =>
        obtain ⟨l2', st3⟩ := r4
        rw [e4] at hpa2
        have hp' := hp hed' st3 (lazePast_nz env hed q st hed' st1 hnz e2) y
        simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
        cases e5 : runShape env sup p (GoalS.next hed') st3 with
        | none =>
          rw [e5] at hp'
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, liftS,
            bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4, hp', e5]
        | some r5 =>
          obtain ⟨l1, st4⟩ := r5
          rw [e5] at hp'
          have hlc := lc_all hc h7 (rsGenNoun st4 y) l1 l2'
          cases e6 : lazeCopy l1 l2' with
          | none =>
            rw [e6] at hlc
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es,
              liftS, bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4, hp',
              e5, lc_at', lc_arm, hlc, e6]
          | some l =>
            rw [e6] at hlc
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es,
              liftS, bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4, hp',
              e5, lc_at', lc_arm, hlc, e6]

/-- **The cons case under `%pick`**: the run of `q` under `[%next none]`, `+laze-past` over `p`,
the run of `p` under `[%next none]`, `+laze-copy`. -/
theorem rs_consP (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (st : RSt CSet)
    (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAt ctx env q sup (GoalS.next noneL) st1)
    (hp : ∀ st1, RsAt ctx env p sup (GoalS.next noneL) st1) :
    RsAt ctx env (Nomm.cons p q) sup GoalS.pick st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_c]
  have hq' := hq st y
  simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hq'
  unfold rsKc
  cases e1 : runShape env sup q (GoalS.next noneL) st with
  | none =>
    rw [e1] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm,
        hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      have hp' := hp st2 y
      simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hp'
      cases e3 : runShape env sup p (GoalS.next noneL) st2 with
      | none =>
        rw [e3] at hp'
        simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm,
          hpa, e2, hp', e3]
      | some r3 =>
        obtain ⟨lp, st3⟩ := r3
        rw [e3] at hp'
        have hlc := lc_all hc h7 (rsGenNoun st3 y) lp lq'
        cases e4 : lazeCopy lp lq' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at',
            lzpArm, hpa, e2, hp', e3, lc_at', lc_arm, hlc, e4, liftS]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at',
            lzpArm, hpa, e2, hp', e3, lc_at', lc_arm, hlc, e4, liftS]

/-- **The cons case under `%done`**: the gate runs again under `[%next this]`. -/
theorem rs_consD (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (st : RSt CSet)
    (hn : RsAt ctx env (Nomm.cons p q) sup (GoalS.next thisL) st) :
    RsAt ctx env (Nomm.cons p q) sup GoalS.done st := by
  intro y
  have hn' := hn y
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun, Nomm.toNoun] at hn'
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_c]
  unfold rsKc
  simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hn']
  rfl

/-- **The cons case** on every goal of `GoalNZ`. -/
theorem rs_consW (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (hg : GoalNZ goal)
    (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p) (hcq : CallCode cod (shapeCE env) q)
    (hq : ∀ l st1, LzNZ l → RsAt ctx env q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAt ctx env p sup (GoalS.next l) st1) :
    RsAt ctx env (Nomm.cons p q) sup goal st := by
  cases goal with
  | next laz => exact rs_consN hc h7 hcode env p q sup laz hg st hcp hcq hq hp
  | pick =>
    exact rs_consP hc h7 hcode env p q sup st hcp (fun st1 => hq _ st1 lzNZ_noneL) (fun st1 => hp _ st1 lzNZ_noneL)
  | done =>
    exact rs_consD hc h7 hcode env p q sup st (rs_consN hc h7 hcode env p q sup thisL lzNZ_thisL st hcp hcq hq hp)

end

end Compiler
end Formalization
