import lemmas.Compiler.CompPastLink

/-!
# More cases of `+run`: `%4`, ...

Each case is a theorem `comp_run_nK` of the form of `comp_run_n7`:
`CompRunAt` of the case from `CompRunAt` of its recursive calls.  The goal of
a recursive call is a fork-free `%next` goal, so the hypotheses quantify over
its registers and labels and over the state.

`lazy-from-reg` (arm `92` of the types core `compTypes`, axis `15` of `ctx`)
is `lazyNoun (lazyReg r)`: `[[[%this r] ~] ~ ~]` (`ct_lfr_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-! ## `lazy-from-reg` -/

def lfrBat : Noun :=
  C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6))) (C (A 1) (A 0))) (C (A 1) (C (A 0) (A 0)))

def lfrArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) lfrBat) (C (A 0) (A 1))))

theorem ct_lfr_at : slot? 92 compTypes = some lfrArm := by kernel_rfl

theorem ct_lfr_arm (d : Noun) : nock d lfrArm = some (C lfrBat (C (A 0) d)) := by
  unfold lfrArm; simp only [nock_exec]

theorem ct_lfr_gate (r d : Noun) :
    nock (C lfrBat (C r d)) lfrBat = some (C (C (C (A 0x73696874) r) (A 0)) (C (A 0) (A 0))) := by
  nock_open lfrBat; simp only [nock_exec]

variable {ctx : Noun}

theorem cr_ctx15 (h7 : slot? 7 ctx = some compK) : slot? 15 ctx = some compTypes := by
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have := slot_spine (by omega) (by omega) h1 1
  simp only [show 2 ^ 1 * (7 + 1) - 1 = 15 from rfl, show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  rw [this]; rfl

/-! ## The case `%4` -/

/-- The arm `+collapse-lazy-atom` builds its gate. -/
theorem cr_cla_arm (d : Noun) : nock d claArm = some (C claBat (C (C (A 0x7478656e)
    (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) d)) := by
  unfold claArm; simp only [nock_exec]

/-- The block `[~ [%inc a b]~ %hop ~ t]`. -/
theorem cr_blob_inc_hop (a b t : Nat) : Blob.toNoun ⟨[], [Pole.inc a b], Termin.hop (jmp0 t)⟩
    = C (A 0) (C (C (C (A 0x636e69) (C (A a) (A b))) (A 0)) (C (A 0x706f68) (C (A 0) (A t)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.inc, Jmp.toNoun, jmp0]

/-- The noun of the goal `[%next (lazy-from-reg r) ~ o]`. -/
theorem cr_goal_reg (r o : Nat) : (CGoal.toL (CGoal.next (lazyReg r) (jmp0 o)) : CGoalL CSet).toNoun
    = C (A 0x7478656e) (C (C (C (C (A 0x73696874) (A r)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A o))) := by
  simp [CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, lazyNoun, lazyReg, Sure.toNoun, Need.toNoun,
    HoonSet.toNoun_empty, Jmp.toNoun, jmp0, listNoun, Tag.this]

theorem cr_disp_n4 (t mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 4) t) goal region sup D) crDol
      = nock (crSubj mono (C (A 4) t) goal region sup D) crK4 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- **The case `%4` of `+run`** on a fork-free goal with no look at `0`:
`%done` and `%pick` take two registers and emit the increment; `%next` runs
`+collapse-lazy-atom` (or takes a fresh register when the goal needs nothing,
where the `?>` on the arguments of `then` crashes as the model does), then the
increment with a `%hop`; then `p` into the argument register. -/
theorem comp_run_n4 (h7 : slot? 7 ctx = some compK) (p : Nomm) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hlok : crLokOk gl)
    (hp : ∀ r o g1, CompRunAt ctx p (CGoal.toL (CGoal.next (lazyReg r) (jmp0 o))) region g1) :
    CompRunAt ctx (Nomm.n4 p) (CGoal.toL gl) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  intro x mono sup hx
  simp only [Nomm.toNoun]
  rw [cr_disp_n4]
  cases gl with
  | done =>
    have hre := comp_re' ctx x g
    have hre2 := comp_re' ctx x { g with re := g.re + 1 }
    have he := cf_emit (x := x) hc { g with re := g.re + 1 + 1 }
      ⟨[], [Pole.inc (g.re + 1) g.re], Termin.don g.re⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.don, Tag.inc] at he
    have hr := hp (g.re + 1) g.bo (cfEmitG ⟨[], [Pole.inc (g.re + 1) g.re], Termin.don g.re⟩
      { g with re := g.re + 1 + 1 }) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre hre2 ⊢
    generalize comp.door = Dr at hD1 hD2 he hre hre2 hr ⊢
    nock_open crK4
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hre2, hD1, hD2, comp_emit_arm, he,
      cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr, runL, re, bind, StateT.bind, cf_emit_g]
  | pick z o =>
    have hre := comp_re' ctx x g
    have hre2 := comp_re' ctx x { g with re := g.re + 1 }
    have he := cf_emit (x := x) hc { g with re := g.re + 1 + 1 }
      ⟨[], [Pole.inc (g.re + 1) g.re], Termin.brn g.re z o⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.brn, Tag.inc] at he
    have hr := hp (g.re + 1) g.bo (cfEmitG ⟨[], [Pole.inc (g.re + 1) g.re], Termin.brn g.re z o⟩
      { g with re := g.re + 1 + 1 }) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre hre2 ⊢
    generalize comp.door = Dr at hD1 hD2 he hre hre2 hr ⊢
    nock_open crK4
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hre2, hD1, hD2, comp_emit_arm, he,
      cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr, runL, re, bind, StateT.bind, cf_emit_g]
  | next laz th =>
    obtain ⟨args, there⟩ := th
    have hcl := comp_collapse_lazy_atom h7 x g laz ⟨args, there⟩ hlok (hx there) (fun _ g' _ => hx g'.bo)
    have hDc := comp_cla_at
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore, Jmp.toNoun] at hcl ⊢
    rcases ecl : collapseLazyAtomL (⟨Lazy.ofSure laz, ⟨args, there⟩⟩ : NextL CSet) g with _ | ⟨a, g1⟩
    · rw [ecl] at hcl
      generalize comp.door = Dr at hDc hD1 hD2 hcl ⊢
      nock_open crK4
      simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runL, ecl, bind,
        StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure]
    · rw [ecl] at hcl
      rcases a with _ | ⟨pro, th'⟩
      · cases args with
        | cons a0 rest =>
          have hre := comp_re' ctx x g1
          simp only [listNoun, unitNoun, Option.map_some] at hcl
          generalize comp.door = Dr at hDc hD1 hD2 hcl hre ⊢
          nock_open crK4
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runL, ecl, bind,
            StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure, hre, hD1, unitNoun, listNoun, re]
        | nil =>
          simp only [listNoun] at hcl
          have hre := comp_re' ctx x g1
          have hre2 := comp_re' ctx x { g1 with re := g1.re + 1 }
          have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 + 1 }
            ⟨[], [Pole.inc (g1.re + 1) g1.re], Termin.hop (jmp0 there)⟩
          rw [cr_blob_inc_hop] at he
          have hr := hp (g1.re + 1) g1.bo (cfEmitG ⟨[], [Pole.inc (g1.re + 1) g1.re], Termin.hop (jmp0 there)⟩
            { g1 with re := g1.re + 1 + 1 }) x mono sup hx
          rw [cr_goal_reg] at hr
          simp only [crSubj, compCore] at hr hre hre2
          generalize comp.door = Dr at hDc hD1 hD2 hcl hre hre2 he hr ⊢
          nock_open crK4
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runL, ecl, bind,
            StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure, hre, hre2, hD1, hD2, comp_emit_arm, he, unitNoun,
            listNoun, re, pure, StateT.pure, cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr,
            cf_emit_g]
      · have hre := comp_re' ctx x g1
        have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 }
          ⟨[], [Pole.inc g1.re pro], Termin.hop (jmp0 th')⟩
        rw [cr_blob_inc_hop] at he
        have hr := hp g1.re g1.bo (cfEmitG ⟨[], [Pole.inc g1.re pro], Termin.hop (jmp0 th')⟩
          { g1 with re := g1.re + 1 }) x mono sup hx
        rw [cr_goal_reg] at hr
        simp only [crSubj, compCore] at hr hre
        generalize comp.door = Dr at hDc hD1 hD2 hcl hre he hr ⊢
        nock_open crK4
        simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runL, ecl, bind,
          StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure, hre, hD1, hD2, comp_emit_arm, he, unitNoun,
          listNoun, re, pure, StateT.pure, cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr,
          cf_emit_g]

end Compiler
end Formalization
