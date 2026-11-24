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

/-! ## `lazy-from-need` and the case `%3` -/

def lfnBat : Noun :=
  C (C (C (A 0) (A 6)) (C (A 1) (A 0))) (C (A 1) (C (A 0) (A 0)))

def lfnArm : Noun := C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) lfnBat) (C (A 0) (A 1))))

/-- `lazy-from-need` is arm `94` of the types core: `[[ned ~] ~ ~]`. -/
theorem ct_lfn_at : slot? 94 compTypes = some lfnArm := by kernel_rfl

theorem ct_lfn_arm (d : Noun) : nock d lfnArm = some (C lfnBat (C (C (A 0x656e6f6e) (A 0)) d)) := by
  unfold lfnArm; simp only [nock_exec]

theorem ct_lfn_gate (n d : Noun) :
    nock (C lfnBat (C n d)) lfnBat = some (C (C n (A 0)) (C (A 0) (A 0))) := by
  nock_open lfnBat; simp only [nock_exec]

/-- The block `[~ ~ %clq r z o]`. -/
theorem cr_blob_clq (r : Nat) (z o : Jmp) : Blob.toNoun ⟨[], [], Termin.clq r z o⟩
    = C (A 0) (C (A 0) (C (A 0x716c63) (C (A r) (C z.toNoun o.toNoun)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.clq]

/-- The block `[~ ~ %clq r [~ z] [~ o]]`. -/
theorem cr_blob_clq0 (r z o : Nat) : Blob.toNoun ⟨[], [], Termin.clq r (jmp0 z) (jmp0 o)⟩
    = C (A 0) (C (A 0) (C (A 0x716c63) (C (A r) (C (C (A 0) (A z)) (C (A 0) (A o)))))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.clq, Jmp.toNoun, jmp0]

/-- The block `[~ [%imm k r]~ %don r]`. -/
theorem cr_blob_imm_don (k : Noun) (r : Nat) : Blob.toNoun ⟨[], [Pole.imm k r], Termin.don r⟩
    = C (A 0) (C (C (C (A 0x6d6d69) (C k (A r))) (A 0)) (C (A 0x6e6f64) (A r))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.don, Tag.imm]

theorem cr_disp_n3 (t mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 3) t) goal region sup D) crDol
      = nock (crSubj mono (C (A 3) t) goal region sup D) crK3 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- **The case `%3` of `+run`** on a fork-free goal with no look at `0`: on a
`%next` goal whose need is `+none-equivalent`, `p` with the same goal;
otherwise `%done` makes the two blocks of `0` and `1`, `%next` runs
`+collapse-lazy-atom` (a crash on `~`) and `+forl`, and a `%clq` block on a
fresh register is the goal of `p` (`lazy-from-need`). -/
theorem comp_run_n3 (h7 : slot? 7 ctx = some compK) (p : Nomm) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hlok : crLokOk gl)
    (hg : CompRunAt ctx p (CGoal.toL gl) region g)
    (hp : ∀ r o g1, CompRunAt ctx p (CGoal.toL (CGoal.next (lazyReg r) (jmp0 o))) region g1) :
    CompRunAt ctx (Nomm.n3 p) (CGoal.toL gl) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  intro x mono sup hx
  simp only [Nomm.toNoun]
  rw [cr_disp_n3]
  cases gl with
  | pick z o =>
    have hre := comp_re' ctx x g
    have he := cf_emit (x := x) hc { g with re := g.re + 1 } ⟨[], [], Termin.clq g.re z o⟩
    rw [cr_blob_clq] at he
    have hr := hp g.re g.bo (cfEmitG ⟨[], [], Termin.clq g.re z o⟩ { g with re := g.re + 1 }) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre ⊢
    generalize comp.door = Dr at hD1 hD2 he hre hr ⊢
    nock_open crK3
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hD1, hD2, comp_emit_arm, he,
      cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hr, runL, re, bind, StateT.bind, cf_emit_g]
  | done =>
    have hre0 := comp_re' ctx x g
    have hre1 := comp_re' ctx x { g with re := g.re + 1 }
    have he0 := cf_emit (x := x) hc { g with re := g.re + 1 + 1 } ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩
    rw [cr_blob_imm_don] at he0
    have he1 := cf_emit (x := x) hc (cfEmitG ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩
      { g with re := g.re + 1 + 1 }) ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩
    rw [cr_blob_imm_don] at he1
    generalize hgC : cfEmitG ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩
      (cfEmitG ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩ { g with re := g.re + 1 + 1 }) = gC at he1
    have hre2 := comp_re' ctx x gC
    have he2 := cf_emit (x := x) hc { gC with re := gC.re + 1 }
      ⟨[], [], Termin.clq gC.re (jmp0 g.bo) (jmp0 (g.bo + 1))⟩
    rw [cr_blob_clq0] at he2
    have hr := hp gC.re gC.bo (cfEmitG ⟨[], [], Termin.clq gC.re (jmp0 g.bo) (jmp0 (g.bo + 1))⟩
      { gC with re := gC.re + 1 }) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore, cf_emitG_bo] at hre0 hre1 hre2 he1 ⊢
    have hm : runL (S := CSet) (Map := TreapMap mugF) (Nomm.n3 p) (CGoal.toL CGoal.done) region g
        = runL p (CGoal.toL (CGoal.next (lazyReg gC.re) (jmp0 gC.bo))) region
            (cfEmitG ⟨[], [], Termin.clq gC.re (jmp0 g.bo) (jmp0 (g.bo + 1))⟩ { gC with re := gC.re + 1 }) := by
      rw [← hgC]
      simp [runL, CGoal.toL, doneBlocks, re, bind, StateT.bind, pure, StateT.pure, cf_emit_g, cf_emitG_bo,
        cf_emitG_re]
    rw [hm]
    generalize comp.door = Dr at hD1 hD2 he0 he1 he2 hre0 hre1 hre2 hr ⊢
    nock_open crK3
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre0, hre1, hre2, hD1, hD2, comp_emit_arm, he0, he1,
      he2, cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hr, cf_emitG_bo]
  | next laz th =>
    obtain ⟨args, there⟩ := th
    have hD0 := compK_ne
    by_cases hne : noneEquivalent laz = true
    · have hr := hg x mono sup hx
      simp only [crSubj, compCore, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure] at hr
      simp only [compCore]
      generalize comp.door = Dr at hr ⊢
      nock_open crK3
      simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, h7, hD0, ne_arm, ne_gate,
        hne, loob, cr_bat_dol, hr, runL, Lazy.noneEquivalentL_ofSure]
    · have hne' : noneEquivalent laz = false := by simpa using hne
      have hcl := comp_collapse_lazy_atom h7 x g laz ⟨args, there⟩ hlok (hx there) (fun _ g' _ => hx g'.bo)
      have hDc := comp_cla_at
      have hD1 := comp_re_at
      have hD2 := comp_emit_at
      have hDf := comp_fl_at
      simp only [compCore, Jmp.toNoun] at hcl ⊢
      rcases ecl : collapseLazyAtomL (⟨Lazy.ofSure laz, ⟨args, there⟩⟩ : NextL CSet) g with _ | ⟨a, g1⟩
      · rw [ecl] at hcl
        generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
        nock_open crK3
        simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, h7, hD0, ne_arm, ne_gate,
          hne', loob, hDc, cr_cla_arm, hcl, runL, ecl, bind, StateT.bind, Jmp.toNoun,
          Lazy.noneEquivalentL_ofSure]
      · rw [ecl] at hcl
        rcases a with _ | ⟨r, o⟩
        · generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
          nock_open crK3
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, h7, hD0, ne_arm, ne_gate,
            hne', loob, hDc, cr_cla_arm, hcl, runL, ecl, bind, StateT.bind, Jmp.toNoun,
            Lazy.noneEquivalentL_ofSure, unitNoun]
        · have hfl := comp_forl (x := x) hc g1 r o
          rw [fl_forl_eq] at hfl
          simp only [cf_emitG_bo, Option.map_some] at hfl
          generalize hg2 : cfEmitG (flB3 (g1.re + 1) g1.bo) (cfEmitG (flB2 g1.re g1.bo)
            (cfEmitG (flB1 r o) { g1 with re := g1.re + 1 + 1 })) = g2 at hfl
          have hre := comp_re' ctx x g2
          have he := cf_emit (x := x) hc { g2 with re := g2.re + 1 }
            ⟨[], [], Termin.clq g2.re (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
          rw [cr_blob_clq0] at he
          have hr := hp g2.re g2.bo (cfEmitG ⟨[], [], Termin.clq g2.re (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
            { g2 with re := g2.re + 1 }) x mono sup hx
          rw [cr_goal_reg] at hr
          simp only [crSubj, compCore, cf_emitG_bo, Option.map_some] at hr hre hfl
          have hm : runL (S := CSet) (Map := TreapMap mugF) (Nomm.n3 p) (CGoal.toL (CGoal.next laz ⟨args, there⟩))
              region g = runL p (CGoal.toL (CGoal.next (lazyReg g2.re) (jmp0 g2.bo))) region
                (cfEmitG ⟨[], [], Termin.clq g2.re (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
                  { g2 with re := g2.re + 1 }) := by
            rw [← hg2]
            simp [runL, CGoal.toL, Lazy.noneEquivalentL_ofSure, hne', ecl, fl_forl_eq, re, bind, StateT.bind,
              pure, StateT.pure, cf_emit_g, cf_emitG_bo, cf_emitG_re]
          rw [hm]
          generalize comp.door = Dr at hDc hD1 hD2 hDf hcl hre he hr hfl ⊢
          nock_open crK3
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, h7, hD0, ne_arm, ne_gate,
            hne', loob, hDc, cr_cla_arm, hcl, Jmp.toNoun, unitNoun, hDf, comp_fl_arm, hfl, hre, hD1, hD2,
            comp_emit_arm, he, cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hr, cf_emitG_bo]


/-! ## The case `%5`

The body `crK5` is cut into named parts (`cr5_eq`): the two fresh registers,
the branch over the goal `cr5Br` that returns the block `o` of the
comparison, and the tail `cr5Tail` = the run of `q` (`cr5Tail`), `+past`
(`cr5T2`), the run of `p` and `+copy` (`cr5T3`). -/

def cr5Br : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 1004)))) (C (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 502)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 1004)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 63)))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 1)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 126)) (C (C (A 0) (A 62)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 1004))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55fe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1014))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 8118)))) (C (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x757165)) (C (C (A 0) (A 14)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 0x3fb7))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 0))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabffa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 0) (A 27)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 30)) (C (C (A 0) (A 14)) (C (C (C (A 1) (A 0)) (C (A 0) (A 4))) (C (C (A 1) (A 0)) (C (A 0) (A 5)))))))))))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))

def cr5T3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 62)))))) (C (A 0) (A 2)))))))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 8170))) (C (A 0) (A 63)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))))))))))))

def cr5T2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 8170)) (C (A 0) (A 8174))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr5T3))))))))

def cr5Tail : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6)))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 2027))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr5T2))))))))

def cr5Head : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) cr5Br)) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) cr5Tail))))))))))))))))))))))))

theorem cr5_eq : crK5 = cr5Head := by kernel_rfl

theorem cr_disp_n5 (t mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 5) t) goal region sup D) crDol
      = nock (crSubj mono (C (A 5) t) goal region sup D) crK5 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]


/-- The side condition of `+copy` (`comp_copy`) on the needs it joins, at
the state where it runs: every register below the counter, and no `%mov`
that joins a register to itself. -/
def CrCopyOk (g : Gen (TreapMap mugF)) (f : Next CSet) (s : Sure CSet) : Prop :=
  cnLt g.re f.laz.ned ∧ cnLt g.re s.ned ∧ cnMeet f.laz.ned s.ned

/-- The noun of a fork-free `next` as a goal. -/
theorem cr_next_noun (n : Next CSet) : (Next.toL n).goal.toNoun
    = C (A 0x7478656e) (C (lazyNoun n.laz) n.th.toNoun) := by
  simp [Next.toL, NextL.goal, CGoalL.toNoun, Lazy.toNoun_ofSure]

theorem cr_next_noun' (n : Next CSet) : n.goal.toNoun
    = C (A 0x7478656e) (C (lazyNoun n.laz) n.th.toNoun) := by
  simp [Next.goal, CGoal.toNoun]

/-- The noun of the goal `[%next (lazy-from-reg r) th]`. -/
theorem cr_goal_reg' (r : Nat) (th : Jmp) : (CGoal.toL (CGoal.next (lazyReg r) th) : CGoalL CSet).toNoun
    = C (A 0x7478656e) (C (C (C (C (A 0x73696874) (A r)) (A 0)) (C (A 0) (A 0))) th.toNoun) := by
  simp [CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, lazyNoun, lazyReg, Sure.toNoun, Need.toNoun,
    HoonSet.toNoun_empty, Tag.this]

/-- `CompRunAt` on a pure nomm with no `%6`, in terms of `run`. -/
theorem cr_at_run {n : Nomm} (hn : n.pure = true) (h6 : noSix n = true) {gl : CGoal CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)} (h : CompRunAt ctx n (CGoal.toL gl) region g)
    (x : GenRest) (mono sup : Noun) (hx : x.NoSoft) :
    nock (crSubj mono n.toNoun (CGoal.toL gl).toNoun (listNoun A region) sup (compCore g x ctx)) crDol
      = (run n gl g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  rw [h x mono sup hx, runL_toL n hn h6, map_apply, Option.map_map]
  rfl

theorem cr_past_at : slot? 7166 comp.door = some paArm := comp_past_at

theorem cr_past_arm (d : Noun) : nock d paArm = some (C paBat (C (C (C (A 0x7478656e)
    (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (C (C (A 0) (A 0)) (A 0))) d)) := by
  unfold paArm; simp only [nock_exec]

theorem cr_cp_arm (d : Noun) : nock d cpArm = some (C cpBat (C (C (C (A 0x7478656e)
    (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0))))
    (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) d)) := by
  unfold cpArm; simp only [nock_exec]

/-- `+past` of a fork-free `next` and a pure nomm returns it unchanged. -/
theorem cr_past_pure (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (x : GenRest) (g : Gen (TreapMap mugF)) (n : Next CSet) (nom : Nomm) (hn : nom.pure = true)
    (region : List Nat) :
    nock (C paBat (C (C (C (A 0x7478656e) (C (lazyNoun n.laz) n.th.toNoun)) (C nom.toNoun (listNoun A region)))
      (C comp.door (C (genNoun g x) ctx)))) paBat
      = some (C (C (A 0x7478656e) (C (lazyNoun n.laz) n.th.toNoun)) (genNoun g x)) := by
  have h := comp_past h7 hcode x g (Next.toL n) nom region (by rw [hinted_pure noCode nom hn]; simp)
  rw [pastL_pure noCode _ hn, cr_next_noun] at h
  simpa [pure, StateT.pure, cr_next_noun] using h

/-- **The tail of `%5`**: the run of `q` into the block `o` of the
comparison, `+past` (the identity on a pure `p`), the run of `p` with the
`then` of `q`, and `+copy`. -/
theorem cr5_tail (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (p q : Nomm) (hpp : p.pure = true) (hqp : q.pure = true) (hp6 : noSix p = true) (hq6 : noSix q = true)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun) (rp rq o : Nat)
    (g1 : Gen (TreapMap mugF))
    (hq : CompRunAt ctx q (CGoal.toL (CGoal.next (lazyReg rq) (jmp0 o))) region g1)
    (hp : ∀ th g2, CompRunAt ctx p (CGoal.toL (CGoal.next (lazyReg rp) th)) region g2)
    (hcp : ∀ nexq g2 nexp g3, run q (CGoal.next (lazyReg rq) (jmp0 o)) g1 = some (nexq, g2) →
      run p (CGoal.next (lazyReg rp) nexq.th) g2 = some (nexp, g3) → CrCopyOk g3 nexp nexq.laz) :
    nock (C (A o) (C (A rq) (C (A rp) (crSubj mono (Nomm.n5 p q).toNoun goalN (listNoun A region) sup
      (compCore g1 x ctx))))) cr5Tail
      = ((do
          let nexq ← run q (CGoal.next (lazyReg rq) (jmp0 o))
          let nexp ← run p (CGoal.next (lazyReg rp) nexq.th)
          copy nexp nexq.laz : CM (TreapMap mugF) (Next CSet)) g1).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, hl, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  have hq1 := cr_at_run hqp hq6 hq x mono sup hx
  rw [cr_goal_reg] at hq1
  simp only [crSubj, compCore] at hq1
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases eq : run (S := CSet) (Map := TreapMap mugF) q (CGoal.next (lazyReg rq) (jmp0 o)) g1 with
  | none =>
    rw [eq] at hq1
    generalize comp.door = Dr at hq1 hD1 hD2 ⊢
    nock_open cr5Tail
    simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
      StateT.bind, eq]
  | some r =>
    obtain ⟨nexq, g2⟩ := r
    rw [eq] at hq1
    simp only [Option.map_some, cr_next_noun'] at hq1
    have hpa := cr_past_pure h7 hcode x g2 nexq p hpp region
    have hp1 := cr_at_run hpp hp6 (hp nexq.th g2) x mono sup hx
    rw [cr_goal_reg'] at hp1
    simp only [crSubj, compCore] at hp1
    cases eq2 : run (S := CSet) (Map := TreapMap mugF) p (CGoal.next (lazyReg rp) nexq.th) g2 with
    | none =>
      rw [eq2] at hp1
      generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 ⊢
      unfold cr5Tail cr5T2 cr5T3
      simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
        StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, eq]
    | some r' =>
      obtain ⟨nexp, g3⟩ := r'
      rw [eq2] at hp1
      simp only [Option.map_some, cr_next_noun'] at hp1
      obtain ⟨hlt, hrt, hm⟩ := hcp nexq g2 nexp g3 eq eq2
      have hcpy := comp_copy (x := x) hc hl g3 nexp nexq.laz hlt hrt hm
      simp only [compCore, cr_next_noun'] at hcpy
      generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 hcpy ⊢
      unfold cr5Tail cr5T2 cr5T3
      simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
        StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, hD2, cr_cp_arm, hcpy, eq, cr_next_noun']


/-- The branch of `%5` over the goal: the block `o` that compares `rp` with
`rq`. -/
noncomputable def cr5BrM (rp rq : Nat) : CGoal CSet → CM (TreapMap mugF) Nat
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

theorem cr_blob_eqq (l r : Nat) (z o : Jmp) : Blob.toNoun ⟨[], [], Termin.eqq l r z o⟩
    = C (A 0) (C (A 0) (C (A 0x717165) (C (A l) (C (A r) (C z.toNoun o.toNoun))))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.eqq]

theorem cr_blob_eqq0 (l r z o : Nat) : Blob.toNoun ⟨[], [], Termin.eqq l r (jmp0 z) (jmp0 o)⟩
    = C (A 0) (C (A 0) (C (A 0x717165) (C (A l) (C (A r) (C (C (A 0) (A z)) (C (A 0) (A o))))))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.eqq, Jmp.toNoun, jmp0]

theorem cr_blob_equ (l r t : Nat) : Blob.toNoun ⟨[], [Pole.equ l r], Termin.hop (jmp0 t)⟩
    = C (A 0) (C (C (C (A 0x757165) (C (A l) (A r))) (A 0)) (C (A 0x706f68) (C (A 0) (A t)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.equ, Jmp.toNoun, jmp0]

/-- **The branch of `%5`** is `cr5BrM`, on a fork-free goal with no look at
`0` (`+collapse-lazy-atom` and `+forl` for a `%next` goal). -/
theorem cr5_br (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (gl : CGoal CSet)
    (hlok : crLokOk gl) (mono nomm region sup : Noun) (rp rq : Nat) (g : Gen (TreapMap mugF)) :
    nock (C (A rq) (C (A rp) (crSubj mono nomm (CGoal.toL gl).toNoun region sup (compCore g x ctx)))) cr5Br
      = (cr5BrM rp rq gl g).map fun p => C (A p.1) (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hD1 := comp_re_at
  have hD2 := comp_emit_at
  cases gl with
  | pick z o =>
    have he := cf_emit (x := x) hc g ⟨[], [], Termin.eqq rp rq z o⟩
    rw [cr_blob_eqq] at he
    simp only [compCore]
    generalize comp.door = Dr at hD1 hD2 he ⊢
    nock_open cr5Br
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hD2, comp_emit_arm, he, cr5BrM, cf_emit_g]
  | done =>
    have hre0 := comp_re' ctx x g
    have hre1 := comp_re' ctx x { g with re := g.re + 1 }
    have he0 := cf_emit (x := x) hc { g with re := g.re + 1 + 1 } ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩
    rw [cr_blob_imm_don] at he0
    have he1 := cf_emit (x := x) hc (cfEmitG ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩
      { g with re := g.re + 1 + 1 }) ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩
    rw [cr_blob_imm_don] at he1
    generalize hgC : cfEmitG ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩
      (cfEmitG ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩ { g with re := g.re + 1 + 1 }) = gC at he1
    have he2 := cf_emit (x := x) hc gC ⟨[], [], Termin.eqq rp rq (jmp0 g.bo) (jmp0 (g.bo + 1))⟩
    rw [cr_blob_eqq0] at he2
    simp only [compCore, cf_emitG_bo] at hre0 hre1 he1 ⊢
    have hm : cr5BrM rp rq CGoal.done g = some (gC.bo, cfEmitG ⟨[], [], Termin.eqq rp rq (jmp0 g.bo)
        (jmp0 (g.bo + 1))⟩ gC) := by
      rw [← hgC]
      simp [cr5BrM, doneBlocks, re, bind, StateT.bind, pure, StateT.pure, cf_emit_g, cf_emitG_bo, cf_emitG_re]
    rw [hm]
    generalize comp.door = Dr at hD1 hD2 he0 he1 he2 hre0 hre1 ⊢
    nock_open cr5Br
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre0, hre1, hD1, hD2, comp_emit_arm, he0, he1,
      he2, cf_emitG_bo]
  | next laz th =>
    obtain ⟨args, there⟩ := th
    have hcl := comp_collapse_lazy_atom h7 x g laz ⟨args, there⟩ hlok (hx there) (fun _ g' _ => hx g'.bo)
    rw [collapseLazyAtomL_mk] at hcl
    have hDc := comp_cla_at
    have hDf := comp_fl_at
    simp only [compCore, Jmp.toNoun] at hcl ⊢
    rcases ecl : collapseLazyAtom (⟨laz, ⟨args, there⟩⟩ : Next CSet) g with _ | ⟨a, g1⟩
    · rw [ecl] at hcl
      generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
      nock_open cr5Br
      simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, hDc, cr_cla_arm, hcl, cr5BrM,
        ecl, bind, StateT.bind, Jmp.toNoun]
    · rw [ecl] at hcl
      rcases a with _ | ⟨r, o⟩
      · cases args with
        | cons a0 rest =>
          simp only [listNoun, unitNoun, Option.map_some] at hcl
          generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
          nock_open cr5Br
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, hDc, cr_cla_arm, hcl,
            cr5BrM, ecl, bind, StateT.bind, Jmp.toNoun, unitNoun, listNoun]
        | nil =>
          simp only [listNoun] at hcl
          have he := cf_emit (x := x) hc g1 ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 there)⟩
          rw [cr_blob_equ] at he
          generalize comp.door = Dr at hDc hD1 hD2 hDf hcl he ⊢
          nock_open cr5Br
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, hDc, cr_cla_arm, hcl,
            cr5BrM, ecl, bind, StateT.bind, Jmp.toNoun, unitNoun, listNoun, hD2, comp_emit_arm, he, cf_emit_g]
      · have hfl := comp_forl (x := x) hc g1 r o
        rw [fl_forl_eq] at hfl
        simp only [cf_emitG_bo, Option.map_some] at hfl
        generalize hg2 : cfEmitG (flB3 (g1.re + 1) g1.bo) (cfEmitG (flB2 g1.re g1.bo)
          (cfEmitG (flB1 r o) { g1 with re := g1.re + 1 + 1 })) = g2 at hfl
        have he := cf_emit (x := x) hc g2 ⟨[], [], Termin.eqq rp rq (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
        rw [cr_blob_eqq0] at he
        simp only [compCore] at hfl
        have hm : cr5BrM rp rq (CGoal.next laz ⟨args, there⟩) g = some (g2.bo,
            cfEmitG ⟨[], [], Termin.eqq rp rq (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩ g2) := by
          rw [← hg2]
          simp [cr5BrM, ecl, fl_forl_eq, bind, StateT.bind, pure, StateT.pure, cf_emit_g, cf_emitG_bo]
        rw [hm]
        generalize comp.door = Dr at hDc hD1 hD2 hDf hcl he hfl ⊢
        nock_open cr5Br
        simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, hDc, cr_cla_arm, hcl,
          Jmp.toNoun, unitNoun, hDf, comp_fl_arm, hfl, hD2, comp_emit_arm, he]


/-- `CompRunAt` from the model `run`, on a pure nomm with no `%6`. -/
theorem cr_at_of_run {n : Nomm} (hn : n.pure = true) (h6 : noSix n = true) {gl : CGoal CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)}
    (h : ∀ (x : GenRest) (mono sup : Noun), x.NoSoft →
      nock (crSubj mono n.toNoun (CGoal.toL gl).toNoun (listNoun A region) sup (compCore g x ctx)) crDol
        = (run n gl g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    CompRunAt ctx n (CGoal.toL gl) region g := by
  intro x mono sup hx
  rw [h x mono sup hx, runL_toL n hn h6, map_apply, Option.map_map]
  rfl

/-- The model's `+past` of a pure nomm is the identity. -/
theorem cr_past_model {nom : Nomm} (hn : nom.pure = true) (n : Next CSet) :
    (past noCode n nom : CM (TreapMap mugF) (Next CSet)) = pure n := by
  unfold past
  rw [hinted_pure noCode nom hn]
  split <;> rfl

/-- The model of `%5` with its branch named and `+past` dropped. -/
theorem cr_run_n5_eq (p q : Nomm) (hpp : p.pure = true) (gl : CGoal CSet) (g : Gen (TreapMap mugF)) :
    run (Nomm.n5 p q) gl g = (do
      let o ← cr5BrM g.re (g.re + 1) gl
      let nexq ← run q (CGoal.next (lazyReg (g.re + 1)) (jmp0 o))
      let nexp ← run p (CGoal.next (lazyReg g.re) nexq.th)
      copy nexp nexq.laz : CM (TreapMap mugF) (Next CSet)) { g with re := g.re + 1 + 1 } := by
  cases gl <;> simp [run, cr5BrM, cr_past_model hpp, re, bind, StateT.bind, pure, StateT.pure] <;> rfl

/-- **The case `%5` of `+run`** on a fork-free goal with no look at `0`, for
pure `p` and `q` with no `%6`: two fresh registers, the comparison block
(`cr5BrM`), `q` into it, `+past`, `p` with the `then` of `q`, and `+copy`,
whose side condition `CrCopyOk` is a hypothesis on the states the model
reaches. -/
theorem comp_run_n5 (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (p q : Nomm) (hpp : p.pure = true) (hqp : q.pure = true) (hp6 : noSix p = true) (hq6 : noSix q = true)
    (gl : CGoal CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hlok : crLokOk gl)
    (hq : ∀ r o g1, CompRunAt ctx q (CGoal.toL (CGoal.next (lazyReg r) (jmp0 o))) region g1)
    (hp : ∀ r th g1, CompRunAt ctx p (CGoal.toL (CGoal.next (lazyReg r) th)) region g1)
    (hcp : ∀ o g1 nexq g2 nexp g3, cr5BrM g.re (g.re + 1) gl { g with re := g.re + 1 + 1 } = some (o, g1) →
      run q (CGoal.next (lazyReg (g.re + 1)) (jmp0 o)) g1 = some (nexq, g2) →
      run p (CGoal.next (lazyReg g.re) nexq.th) g2 = some (nexp, g3) → CrCopyOk g3 nexp nexq.laz) :
    CompRunAt ctx (Nomm.n5 p q) (CGoal.toL gl) region g := by
  apply cr_at_of_run (by simp [Nomm.pure, hpp, hqp]) (by simp [noSix, hp6, hq6])
  intro x mono sup hx
  have hre0 := comp_re' ctx x g
  have hre1 := comp_re' ctx x { g with re := g.re + 1 }
  have hbr := cr5_br h7 x hx gl hlok mono (Nomm.n5 p q).toNoun (listNoun A region) sup g.re (g.re + 1)
    { g with re := g.re + 1 + 1 }
  have hD1 := comp_re_at
  have hnn : (Nomm.n5 p q).toNoun = C (A 5) (C p.toNoun q.toNoun) := rfl
  rw [cr_run_n5_eq p q hpp, hnn, cr_disp_n5, cr5_eq]
  rw [hnn] at hbr
  cases eb : cr5BrM g.re (g.re + 1) gl { g with re := g.re + 1 + 1 } with
  | none =>
    rw [eb] at hbr
    simp only [crSubj, compCore, Option.map_none] at hbr hre0 hre1 ⊢
    generalize (CGoal.toL gl).toNoun = GN at hbr ⊢
    generalize C (A 5) (C p.toNoun q.toNoun) = NN at hbr ⊢
    generalize comp.door = Dr at hD1 hre0 hre1 hbr ⊢
    nock_open cr5Head
    simp [nock_exec, hre0, hre1, hD1, hbr, bind, StateT.bind, eb]
  | some r =>
    obtain ⟨o, g1⟩ := r
    rw [eb] at hbr
    have ht := cr5_tail h7 hcode p q hpp hqp hp6 hq6 region x hx mono (CGoal.toL gl).toNoun sup g.re (g.re + 1)
      o g1 (hq _ _ _) (fun th g2 => hp _ th g2) (fun nexq g2 nexp g3 e1 e2 => hcp o g1 nexq g2 nexp g3 eb e1 e2)
    rw [hnn] at ht
    simp only [crSubj, compCore, Option.map_some] at hbr hre0 hre1 ht ⊢
    generalize (CGoal.toL gl).toNoun = GN at hbr ht ⊢
    generalize C (A 5) (C p.toNoun q.toNoun) = NN at hbr ht ⊢
    generalize comp.door = Dr at hD1 hre0 hre1 hbr ht ⊢
    nock_open cr5Head
    simp [nock_exec, hre0, hre1, hD1, hbr, ht, bind, StateT.bind, eb]


end Compiler
end Formalization
