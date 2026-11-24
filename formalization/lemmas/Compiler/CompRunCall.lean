import lemmas.Compiler.CompRunTwo

/-!
# `+run` on the fragment with indirect calls

The cases of `+run` against `runLC env msup` (`CompRunAtR`, `CompRunAtC` of
`CompRunTwo.lean`): `%3` and `%4` (`comp_run_n3C`, `comp_run_n4C`, the
proofs of `comp_run_n3` and `comp_run_n4` with `runLC` for `runL`: the
bodies of the two models are the same), `%7` (`comp_run_n7C`: the model
compiles `q` with `sup` set to `p`, as the Hoon does), `%5` with a `q` that
may call (`comp_run_n5C`, through `cr5_tailC` of `CompRunTwo.lean`), and
`%2` for an indirect call (`comp_run_n2`).

## The fragment

`indOk` is the fragment where no bond arises (the header of
`CompRunTwo.lean`): the pure nomms with no `%6` whose `%10` axes are not
`0` (`tenOk`), closed under the indirect call `[2 p q ~]` and the test
`[5 p q]` with `p` pure (no `%6`, `tenOk`) and `q` in the fragment, under
`%3`, `%4`, and under `%7` with both parts in it.  In Nock order `p` runs
before `q`, so its run comes after `q`'s in the compilation, and `+past`
over `p` is the identity exactly because `p` is pure; `q` may call.  So `[7 c [2 [0 1] [0 b]]]` (a
Nock `9`) is in it for every `c` in it, and so are calls in sequence
(`[7 [2 a b] [2 c d]]`) and a call whose formula is the product of a call
(`[2 [0 1] [2 [0 3] [0 2]]]`).  A cons, `%5` or `%10` whose part that runs
first calls is not (it makes a bond).

## What is proved

* `crf_run`: the invariant.  A run of `runLC env msup` of a nomm of the
  fragment from a goal with `CrInv` returns a fork-free `next` (`CrRes`):
  below the new counter, made of fresh registers and the goal's need,
  distinct, no look at `0`.
* `comp_run_all_c`: **`CompRunAtC` on every nomm of the fragment**, on every
  goal and state with `CrInv`, every region, given only `slot? 7 ctx = some
  compK` and `slot? 52 ctx = some cod`, for every `env`.  `comp_run_all'`
  stays as it was; on a pure nomm `runLC env msup` is `runL`.
* `comp_run_entry_c`: from the bunt state with `[%done ~]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## `%4` and `%3` against `runLC` -/

/-- **The case `%4` of `+run`** on a fork-free goal with no look at `0`:
`%done` and `%pick` take two registers and emit the increment; `%next` runs
`+collapse-lazy-atom` (or takes a fresh register when the goal needs nothing,
where the `?>` on the arguments of `then` crashes as the model does), then the
increment with a `%hop`; then `p` into the argument register. -/
theorem comp_run_n4C (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p : Nomm) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hinv : CrInv g gl)
    (hp : ∀ s th g1, CrInv g1 (CGoal.next s th) → CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next s th)) region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n4 p) (CGoal.toL gl) region g := by
  have hlok := hinv.1
  have hd := hinv.2.1
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
    have hr := hp (lazyReg (g.re + 1)) (jmp0 g.bo) (cfEmitG ⟨[], [Pole.inc (g.re + 1) g.re], Termin.don g.re⟩
      { g with re := g.re + 1 + 1 }) (cri_reg_emit _ _ _ _ _ (by omega) hd) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre hre2 ⊢
    generalize comp.door = Dr at hD1 hD2 he hre hre2 hr ⊢
    nock_open crK4
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hre2, hD1, hD2, comp_emit_arm, he,
      cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr, runLC, re, bind, StateT.bind, cf_emit_g]
  | pick z o =>
    have hre := comp_re' ctx x g
    have hre2 := comp_re' ctx x { g with re := g.re + 1 }
    have he := cf_emit (x := x) hc { g with re := g.re + 1 + 1 }
      ⟨[], [Pole.inc (g.re + 1) g.re], Termin.brn g.re z o⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.brn, Tag.inc] at he
    have hr := hp (lazyReg (g.re + 1)) (jmp0 g.bo) (cfEmitG ⟨[], [Pole.inc (g.re + 1) g.re], Termin.brn g.re z o⟩
      { g with re := g.re + 1 + 1 }) (cri_reg_emit _ _ _ _ _ (by omega) hd) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre hre2 ⊢
    generalize comp.door = Dr at hD1 hD2 he hre hre2 hr ⊢
    nock_open crK4
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hre2, hD1, hD2, comp_emit_arm, he,
      cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr, runLC, re, bind, StateT.bind, cf_emit_g]
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
      simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
        StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure]
    · rw [ecl] at hcl
      rcases a with _ | ⟨pro, th'⟩
      · cases args with
        | cons a0 rest =>
          have hre := comp_re' ctx x g1
          simp only [listNoun, unitNoun, Option.map_some] at hcl
          generalize comp.door = Dr at hDc hD1 hD2 hcl hre ⊢
          nock_open crK4
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
            StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure, hre, hD1, unitNoun, listNoun, re]
        | nil =>
          simp only [listNoun] at hcl
          have hre := comp_re' ctx x g1
          have hre2 := comp_re' ctx x { g1 with re := g1.re + 1 }
          have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 + 1 }
            ⟨[], [Pole.inc (g1.re + 1) g1.re], Termin.hop (jmp0 there)⟩
          rw [cr_blob_inc_hop] at he
          have hr := hp (lazyReg (g1.re + 1)) (jmp0 g1.bo) (cfEmitG ⟨[], [Pole.inc (g1.re + 1) g1.re], Termin.hop (jmp0 there)⟩
            { g1 with re := g1.re + 1 + 1 }) (cri_reg_emit _ _ _ _ _ (by omega) (cri_cla hd ecl).2) x mono sup hx
          rw [cr_goal_reg] at hr
          simp only [crSubj, compCore] at hr hre hre2
          generalize comp.door = Dr at hDc hD1 hD2 hcl hre hre2 he hr ⊢
          nock_open crK4
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
            StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure, hre, hre2, hD1, hD2, comp_emit_arm, he, unitNoun,
            listNoun, re, pure, StateT.pure, cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr,
            cf_emit_g]
      · have hre := comp_re' ctx x g1
        have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 }
          ⟨[], [Pole.inc g1.re pro], Termin.hop (jmp0 th')⟩
        rw [cr_blob_inc_hop] at he
        have hr := hp (lazyReg g1.re) (jmp0 g1.bo) (cfEmitG ⟨[], [Pole.inc g1.re pro], Termin.hop (jmp0 th')⟩
          { g1 with re := g1.re + 1 }) (cri_reg_emit _ _ _ _ _ (by omega) (cri_cla hd ecl).2) x mono sup hx
        rw [cr_goal_reg] at hr
        simp only [crSubj, compCore] at hr hre
        generalize comp.door = Dr at hDc hD1 hD2 hcl hre he hr ⊢
        nock_open crK4
        simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
          StateT.bind, Jmp.toNoun, Lazy.toNoun_ofSure, hre, hD1, hD2, comp_emit_arm, he, unitNoun,
          listNoun, re, pure, StateT.pure, cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr,
          cf_emit_g]

/-- **The case `%3` of `+run`** on a fork-free goal with no look at `0`: on a
`%next` goal whose need is `+none-equivalent`, `p` with the same goal;
otherwise `%done` makes the two blocks of `0` and `1`, `%next` runs
`+collapse-lazy-atom` (a crash on `~`) and `+forl`, and a `%clq` block on a
fresh register is the goal of `p` (`lazy-from-need`). -/
theorem comp_run_n3C (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p : Nomm) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hinv : CrInv g gl)
    (hg : CompRunAtR (runLC env msup) ctx p (CGoal.toL gl) region g)
    (hp : ∀ s th g1, CrInv g1 (CGoal.next s th) → CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next s th)) region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n3 p) (CGoal.toL gl) region g := by
  have hlok := hinv.1
  have hd := hinv.2.1
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
    have hr := hp (lazyReg g.re) (jmp0 g.bo) (cfEmitG ⟨[], [], Termin.clq g.re z o⟩ { g with re := g.re + 1 })
      (cri_reg_emit _ _ _ _ _ (by omega) hd) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre ⊢
    generalize comp.door = Dr at hD1 hD2 he hre hr ⊢
    nock_open crK3
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hD1, hD2, comp_emit_arm, he,
      cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hr, runLC, re, bind, StateT.bind, cf_emit_g]
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
    have hr := hp (lazyReg gC.re) (jmp0 gC.bo) (cfEmitG ⟨[], [], Termin.clq gC.re (jmp0 g.bo) (jmp0 (g.bo + 1))⟩
      { gC with re := gC.re + 1 }) (cri_reg_emit _ _ _ _ _ (by omega)
        (by rw [← hgC, cf_emitG_drop, cf_emitG_drop]; exact hd)) x mono sup hx
    rw [cr_goal_reg] at hr
    simp only [crSubj, compCore] at hr
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore, cf_emitG_bo] at hre0 hre1 hre2 he1 ⊢
    have hm : runLC (S := CSet) (Map := TreapMap mugF) env msup (Nomm.n3 p) (CGoal.toL CGoal.done) region g
        = runLC env msup p (CGoal.toL (CGoal.next (lazyReg gC.re) (jmp0 gC.bo))) region
            (cfEmitG ⟨[], [], Termin.clq gC.re (jmp0 g.bo) (jmp0 (g.bo + 1))⟩ { gC with re := gC.re + 1 }) := by
      rw [← hgC]
      simp [runLC, CGoal.toL, doneBlocks, re, bind, StateT.bind, pure, StateT.pure, cf_emit_g, cf_emitG_bo,
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
        hne, loob, cr_bat_dol, hr, runLC, Lazy.noneEquivalentL_ofSure]
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
          hne', loob, hDc, cr_cla_arm, hcl, runLC, ecl, bind, StateT.bind, Jmp.toNoun,
          Lazy.noneEquivalentL_ofSure]
      · rw [ecl] at hcl
        rcases a with _ | ⟨r, o⟩
        · generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
          nock_open crK3
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, h7, hD0, ne_arm, ne_gate,
            hne', loob, hDc, cr_cla_arm, hcl, runLC, ecl, bind, StateT.bind, Jmp.toNoun,
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
          have hr := hp (lazyReg g2.re) (jmp0 g2.bo) (cfEmitG ⟨[], [], Termin.clq g2.re (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
            { g2 with re := g2.re + 1 }) (cri_reg_emit _ _ _ _ _ (by omega)
              (by rw [← hg2, cf_emitG_drop, cf_emitG_drop, cf_emitG_drop]; exact (cri_cla hd ecl).2)) x mono sup hx
          rw [cr_goal_reg] at hr
          simp only [crSubj, compCore, cf_emitG_bo, Option.map_some] at hr hre hfl
          have hm : runLC (S := CSet) (Map := TreapMap mugF) env msup (Nomm.n3 p) (CGoal.toL (CGoal.next laz ⟨args, there⟩))
              region g = runLC env msup p (CGoal.toL (CGoal.next (lazyReg g2.re) (jmp0 g2.bo))) region
                (cfEmitG ⟨[], [], Termin.clq g2.re (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
                  { g2 with re := g2.re + 1 }) := by
            rw [← hg2]
            simp [runLC, CGoal.toL, Lazy.noneEquivalentL_ofSure, hne', ecl, fl_forl_eq, re, bind, StateT.bind,
              pure, StateT.pure, cf_emit_g, cf_emitG_bo, cf_emitG_re]
          rw [hm]
          generalize comp.door = Dr at hDc hD1 hD2 hDf hcl hre he hr hfl ⊢
          nock_open crK3
          simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, Lazy.toNoun_ofSure, h7, hD0, ne_arm, ne_gate,
            hne', loob, hDc, cr_cla_arm, hcl, Jmp.toNoun, unitNoun, hDf, comp_fl_arm, hfl, hre, hD1, hD2,
            comp_emit_arm, he, cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hr, cf_emitG_bo]

/-! ## `%7` against `runLC` -/

/-- **The case `%7` of `+run` against `runLC`**: `q` with the goal and `sup`
set to `p` (the Hoon's `$(nomm q.nomm, sup `p.nomm)`), then `p` with the
goal that `q` returns. -/
theorem comp_run_n7C (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF))
    (hq : CompRunAtR (runLC env (some p)) ctx q goal region g)
    (hp : ∀ nex g1, runLC env (some p) q goal region g = some (nex, g1) →
      CompRunAtR (runLC env msup) ctx p nex.goal region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n7 p q) goal region g := by
  intro x mono sup hx
  have h1 := hq x mono (C (A 0) p.toNoun) hx
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runLC (S := CSet) (Map := TreapMap mugF) env (some p) q goal region g with
  | none =>
    rw [e] at h1
    simp only [compCore]
    generalize comp.door = Dr at h1 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, runLC, e, bind, StateT.bind]
  | some r =>
    obtain ⟨nex, g1⟩ := r
    rw [e] at h1
    have h2 := hp nex g1 e x mono sup hx
    simp only [crSubj, compCore] at h2 h1
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, h2, runLC, e, bind, StateT.bind]

/-! ## `%5` against `runLC`, with `q` that may call -/

/-- The model of `%5` against `runLC` on a fork-free goal: two registers,
the branch `cr5BrM`, then the tail. -/
theorem cr5_modelC (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) :
    (runLC env msup (Nomm.n5 p q) (CGoal.toL gl) region : CM (TreapMap mugF) (NextL CSet)) g = (do
      let o ← cr5BrM g.re (g.re + 1) gl
      let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg (g.re + 1)) (jmp0 o))) region
      let nexF ← pastL env.cod nexF p region
      let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg g.re) nexF.th)) region
      copyL nexS nexF.laz : CM (TreapMap mugF) (NextL CSet)) { g with re := g.re + 1 + 1 } := by
  cases gl <;> simp [runLC, CGoal.toL, cr5BrM, collapseLazyAtomL_mk, re, bind, StateT.bind, pure, StateT.pure] <;> rfl

/-- **The case `%5` of `+run` against `runLC`**, on a fork-free goal with
the invariant, for `p` pure with no `%6` and `q` given as for `%2`
(`Cr2Parts`): `q` may call. -/
theorem comp_run_n5C (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpp : p.pure = true) (hp6 : noSix p = true)
    (gl : CGoal CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : CrInv g gl)
    (P : Cr2Parts env msup ctx p q region) :
    CompRunAtR (runLC env msup) ctx (Nomm.n5 p q) (CGoal.toL gl) region g := by
  have hlok := hinv.1
  intro x mono sup hx
  have hre0 := comp_re' ctx x g
  have hre1 := comp_re' ctx x { g with re := g.re + 1 }
  have hbr := cr5_br h7 x hx gl hlok mono (Nomm.n5 p q).toNoun (listNoun A region) sup g.re (g.re + 1)
    { g with re := g.re + 1 + 1 }
  have hD1 := comp_re_at
  have hnn : (Nomm.n5 p q).toNoun = C (A 5) (C p.toNoun q.toNoun) := rfl
  rw [cr5_modelC, hnn, cr_disp_n5, cr5_eq]
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
    obtain ⟨l1, d1⟩ := cr5_br_keeps (g := { g with re := g.re + 1 + 1 }) hinv.2.1 eb
    have l1' : g.re + 1 + 1 ≤ g1.re := l1
    have iq : CrInv g1 (CGoal.next (lazyReg (g.re + 1)) (jmp0 o)) := cri_reg o (by omega) d1
    have hip : ∀ (nexF : Next CSet) g6,
        runLC env msup q (CGoal.toL (CGoal.next (lazyReg (g.re + 1)) (jmp0 o))) region g1 = some (Next.toL nexF, g6) →
        CrOut g1 (CGoal.next (lazyReg (g.re + 1)) (jmp0 o)) g6 nexF ∧
          CrInv g6 (CGoal.next (lazyReg g.re) nexF.th) := by
      intro nexF g6 e
      have O := crr_out (P.resQ _ _ _ _ _ iq e)
      exact ⟨O, cra_lok_reg _, O.2.1, ⟨nb_this (by have := O.1; omega), O.2.2.1.2⟩, by simp [GDist, lazyReg, Distinct]⟩
    have ht := cr5_tailC h7 hcode env msup p q hpp hp6 region x hx mono (CGoal.toL gl).toNoun sup g.re (g.re + 1)
      o g1 (P.runQ _ _ _ iq)
      (fun nex g6 e => let ⟨n, e', _⟩ := P.resQ _ _ _ _ _ iq e; ⟨n, e'⟩)
      (fun nexF g6 e => P.runP _ _ _ (hip nexF g6 e).2)
      (fun nexF g6 nexS g7 e e2 => crf_copy_ok (nb_this (by omega))
        (fun y e1 e2' => by simp only [lazyReg, NMem] at e1 e2'; omega) (hip nexF g6 e).1
        (cro_run hpp hp6 (hip nexF g6 e).2 e2))
    rw [hnn] at ht
    simp only [crSubj, compCore, Option.map_some] at hbr hre0 hre1 ht ⊢
    generalize (CGoal.toL gl).toNoun = GN at hbr ht ⊢
    generalize C (A 5) (C p.toNoun q.toNoun) = NN at hbr ht ⊢
    generalize comp.door = Dr at hD1 hre0 hre1 hbr ht ⊢
    nock_open cr5Head
    simp [nock_exec, hre0, hre1, hD1, hbr, ht, bind, StateT.bind, eb]

/-! ## The fragment -/

/-- **The fragment with indirect calls**: pure with no `%6` and `tenOk`,
or an indirect call `[2 p q ~]` or a `[5 p q]` with `p` so and `q` in the
fragment, or `%3`, `%4` of it, or `%7` of two of it. -/
def indOk : Nomm → Bool
  | Nomm.n2 p q Option.none => (p.pure && noSix p && tenOk p) && indOk q
  | Nomm.n3 p => indOk p
  | Nomm.n4 p => indOk p
  | Nomm.n5 p q => (p.pure && noSix p && tenOk p) && indOk q
  | Nomm.n7 p q => indOk p && indOk q
  | n => n.pure && noSix n && tenOk n

/-- Every nomm of the old fragment is in it. -/
theorem indOk_of_pure : ∀ (n : Nomm), n.pure = true → noSix n = true → tenOk n = true → indOk n = true
  | Nomm.n3 p, h1, h2, h3 => by
    simp only [Nomm.pure] at h1; simp only [noSix] at h2; simp only [tenOk] at h3
    simp only [indOk]; exact indOk_of_pure p h1 h2 h3
  | Nomm.n4 p, h1, h2, h3 => by
    simp only [Nomm.pure] at h1; simp only [noSix] at h2; simp only [tenOk] at h3
    simp only [indOk]; exact indOk_of_pure p h1 h2 h3
  | Nomm.n7 p q, h1, h2, h3 => by
    simp only [Nomm.pure, Bool.and_eq_true] at h1; simp only [noSix, Bool.and_eq_true] at h2
    simp only [tenOk, Bool.and_eq_true] at h3
    simp only [indOk, Bool.and_eq_true]
    exact ⟨indOk_of_pure p h1.1 h2.1 h3.1, indOk_of_pure q h1.2 h2.2 h3.2⟩
  | Nomm.n2 _ _ _, h1, _, _ => by simp [Nomm.pure] at h1
  | Nomm.cons _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n0 _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n1 _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n5 p q, h1, h2, h3 => by
    simp only [Nomm.pure, Bool.and_eq_true] at h1; simp only [noSix, Bool.and_eq_true] at h2
    simp only [tenOk, Bool.and_eq_true] at h3
    simp only [indOk, Bool.and_eq_true]
    exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, indOk_of_pure q h1.2 h2.2 h3.2⟩
  | Nomm.n6 _ _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n10 _ _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n11s _ _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n11d _ _ _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.n12 _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]
  | Nomm.mean _ _ _ _ _, h1, h2, h3 => by simp only [indOk, h1, h2, h3, Bool.and_self]

/-! ## The invariant -/

/-- A goal `[%next (lazy-from-reg r) j]` below the counter. -/
theorem cri_reg_j {r : Nat} {j : Jmp} {g : Gen (TreapMap mugF)} (hr : r < g.re) (hj : JmpIn (· < g.re) j)
    (hd : g.drop = false) : CrInv g (CGoal.next (lazyReg r) j) :=
  ⟨cra_lok_reg r, hd, ⟨nb_this hr, hj⟩, by simp [GDist, lazyReg, Distinct]⟩

/-- A run for a fresh register's goal, seen from an earlier state. -/
theorem crr_fresh {g g1 g' : Gen (TreapMap mugF)} {gl : CGoal CSet} {r : Nat} {j : Jmp} {nex : NextL CSet}
    (h : CrRes g1 (CGoal.next (lazyReg r) j) g' nex) (hr : g.re ≤ r) (hl : g.re ≤ g1.re) : CrRes g gl g' nex := by
  obtain ⟨n, e, l, d, ni, s, D, L⟩ := h
  refine ⟨n, e, by omega, d, ni, fun y hy => ?_, D, L⟩
  rcases s y hy with e' | e'
  · exact Or.inl (by omega)
  · simp only [GMem, lazyReg, NMem] at e'; exact Or.inl (by omega)

/-- Two runs in sequence, the second for the goal the first returns. -/
theorem cro_comp {g g1 g' : Gen (TreapMap mugF)} {gl : CGoal CSet} {n1 n2 : Next CSet}
    (O1 : CrOut g gl g1 n1) (O2 : CrOut g1 n1.goal g' n2) : CrOut g gl g' n2 := by
  obtain ⟨l1, -, -, s1, -, -⟩ := O1
  obtain ⟨l2, d2, ni2, s2, D2, L2⟩ := O2
  refine ⟨by omega, d2, ni2, fun y hy => ?_, D2, L2⟩
  rcases s2 y hy with e | e
  · exact Or.inl (by omega)
  · exact s1 y e

/-- The run of `p` for a fresh register's goal at a state where `re` and
the mode are as needed. -/
theorem crf_tail {p : Nomm} {env : CallEnv} {msup : Option Nomm} {region : List Nat}
    (ih : ∀ (gl : CGoal CSet) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), CrInv g gl →
      runLC env msup p (CGoal.toL gl) region g = some (nex, g') → CrRes g gl g' nex)
    {g g1 g' : Gen (TreapMap mugF)} {gl : CGoal CSet} {r o : Nat} {nex : NextL CSet}
    (hr : g.re ≤ r) (hr1 : r < g1.re) (hd : g1.drop = false)
    (h : runLC env msup p (CGoalL.next (Lazy.ofSure (lazyReg r)) (jmp0 o)) region g1 = some (nex, g')) :
    CrRes g gl g' nex :=
  crr_fresh (ih (CGoal.next (lazyReg r) (jmp0 o)) g1 g' nex (cri_reg_j hr1 (jmpIn_jmp0 _ _) hd) h) hr (by omega)

/-- `emit` keeps the counter and the mode (on the states of `cri_emit`). -/
theorem crf_emit {b : Blob} {g g' : Gen (TreapMap mugF)} {o : Nat} (h : emit b g = some (o, g')) (hd : g.drop = false) :
    g'.re = g.re ∧ g'.drop = false := by
  obtain ⟨a, b⟩ := cri_emit h
  exact ⟨a, b.trans hd⟩

theorem crf_map_some {α β : Type} {x : Option (α × Gen (TreapMap mugF))} {f : α → β} {a : β}
    {g1 : Gen (TreapMap mugF)} (h : x.map (fun p => (f p.1, p.2)) = some (a, g1)) :
    ∃ b, x = some (b, g1) ∧ a = f b := by
  cases x with
  | none => cases h
  | some r =>
    obtain ⟨b, g⟩ := r
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, rfl, rfl⟩

/-- The pure nomms of the fragment meet `CrRes`. -/
theorem crf_pure {env : CallEnv} {msup : Option Nomm} {region : List Nat} {n : Nomm}
    (h : (n.pure && noSix n && tenOk n) = true) {gl : CGoal CSet} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (hi : CrInv g gl) (e : runLC env msup n (CGoal.toL gl) region g = some (nex, g')) : CrRes g gl g' nex := by
  simp only [Bool.and_eq_true] at h
  exact crr_pure env msup h.1.1 h.1.2 region hi e

/-- **The invariant on the fragment**: a run of `runLC env msup` of a nomm
of the fragment from a fork-free goal with `CrInv` returns a fork-free
`next` that meets `CrOut`. -/
theorem crf_run (env : CallEnv) : ∀ (n : Nomm), indOk n = true → ∀ (msup : Option Nomm) (region : List Nat)
    (gl : CGoal CSet) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), CrInv g gl →
    runLC env msup n (CGoal.toL gl) region g = some (nex, g') → CrRes g gl g' nex
  | Nomm.n2 p q Option.none, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hpp, hp6⟩, _⟩, hq⟩ := hok
    have ihq := crf_run env q hq msup region
    obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
      runLC_n2_none h
    rw [simpleNextL_toL, map_apply] at h1
    obtain ⟨n0, e1, rfl⟩ := crf_map_some h1
    obtain ⟨k1, -⟩ := keeps_simpleNext hi.2.1 hi.2.2.1 e1
    have d1 := k1.dropF hi.2.1
    have l1 := k1.le
    have h2' : kerf (⟨Lazy.ofSure n0.laz, n0.th⟩ : NextL CSet) g1 = some ((out, pro), g2) := h2
    obtain ⟨-, -, -, ed2, -, -, l2, -⟩ := kerf_ofSure h2' d1
    have d2 : g2.drop = false := ed2.trans d1
    obtain ⟨r3, d3⟩ := crf_emit h3 d2
    simp only at r3
    obtain ⟨nF, rfl, OF⟩ := ihq (CGoal.next (lazyReg (g2.re + 1)) (jmp0 o)) g3 g4 nexF
      (cri_reg o (by omega) d3) h4
    rw [pastL_pure env.cod _ hpp region, pure_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    have h6' : runLC env msup p (CGoal.toL (CGoal.next (lazyReg g2.re) nF.th)) region g4 = some (nexS, g6) := h6
    rw [cr2_run_pure env msup hpp hp6, map_apply] at h6'
    obtain ⟨nS, e6, rfl⟩ := crf_map_some h6'
    have l4 := OF.1
    have ip : CrInv g4 (CGoal.next (lazyReg g2.re) nF.th) :=
      cri_reg_j (by omega) OF.2.2.1.2 OF.2.1
    have OS := cro_run hpp hp6 ip e6
    have h7' : copyL (Next.toL nS) (Lazy.ofSure nF.laz) g6 = some (nex, g') := h7
    rw [copyL_toL, map_apply] at h7'
    obtain ⟨n', e7, rfl⟩ := crf_map_some h7'
    obtain ⟨l7, d7, ni7, s7, D7, L7⟩ := crf_copy_out (nb_this (show g2.re < g3.re by omega))
      (fun y e1 e2 => by simp only [lazyReg, NMem] at e1 e2; omega) OF OS e7
    refine ⟨n', rfl, by omega, d7, ni7, fun y hy => ?_, D7, L7⟩
    rcases s7 y hy with e | e | e
    · exact Or.inl (by omega)
    · simp only [lazyReg, NMem] at e; exact Or.inl (by omega)
    · simp only [lazyReg, NMem] at e; exact Or.inl (by omega)
  | Nomm.n3 p, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk] at hok
    have ih := crf_run env p hok msup region
    cases gl with
    | next laz th =>
      simp only [CGoal.toL, runLC] at h
      split at h
      · exact ih (CGoal.next laz th) g g' nex hi h
      · obtain ⟨a, g1, h1, h⟩ := bind_some h
        obtain ⟨l1, d1⟩ := cri_cla hi.2.1 h1
        rcases a with _ | ⟨r, o⟩
        · simp at h
        · obtain ⟨⟨z, o'⟩, g2, h2, h⟩ := bind_some h
          have k2 := keepsA_forl (P := fun _ => True) d1 trivial (fun _ _ => trivial) h2
          have l2 := k2.le
          obtain ⟨r', g3, h3, h⟩ := bind_some h
          rw [re_apply] at h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          obtain ⟨oc, g4, h4, h⟩ := bind_some h
          obtain ⟨r4, d4⟩ := crf_emit h4 (k2.dropF d1)
          simp only at r4
          exact crf_tail ih (by omega) (by omega) d4 h
    | pick z o =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨r, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨oc, g2, h2, h⟩ := bind_some h
      obtain ⟨r2, d2⟩ := crf_emit h2 hi.2.1
      simp only at r2
      exact crf_tail ih (Nat.le_refl _) (by omega) d2 h
    | done =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨⟨o0, o1⟩, g1, h1, h⟩ := bind_some h
      have k1 := keepsA_doneBlocks (P := fun _ => True) hi.2.1 (fun _ _ => trivial) h1
      have l1 := k1.le
      obtain ⟨r, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨oc, g3, h3, h⟩ := bind_some h
      obtain ⟨r3, d3⟩ := crf_emit h3 (k1.dropF hi.2.1)
      simp only at r3
      exact crf_tail ih (by omega) (by omega) d3 h
  | Nomm.n4 p, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk] at hok
    have ih := crf_run env p hok msup region
    cases gl with
    | done =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨pro, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨arg, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨o, g3, h3, h⟩ := bind_some h
      obtain ⟨r3, d3⟩ := crf_emit h3 hi.2.1
      simp only at r3
      exact crf_tail ih (by simp) (by omega) d3 h
    | pick z o =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨pro, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨arg, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨o', g3, h3, h⟩ := bind_some h
      obtain ⟨r3, d3⟩ := crf_emit h3 hi.2.1
      simp only at r3
      exact crf_tail ih (by simp) (by omega) d3 h
    | next laz th =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨a, g1, h1, h⟩ := bind_some h
      obtain ⟨l1, d1⟩ := cri_cla hi.2.1 h1
      obtain ⟨⟨pro, th'⟩, g2, h2, h⟩ := bind_some h
      have k2 : g1.re ≤ g2.re ∧ g2.drop = false := by
        rcases a with _ | x
        · simp only at h2
          obtain ⟨r, g5, h5, h2⟩ := bind_some h2
          rw [re_apply] at h5
          simp only [Option.some.injEq, Prod.mk.injEq] at h5
          obtain ⟨rfl, rfl⟩ := h5
          split at h2
          · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
            obtain ⟨-, rfl⟩ := h2
            exact ⟨by simp, d1⟩
          · cases h2
        · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨-, rfl⟩ := h2
          exact ⟨Nat.le_refl _, d1⟩
      obtain ⟨arg, g3, h3, h⟩ := bind_some h
      rw [re_apply] at h3
      simp only [Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      obtain ⟨o, g4, h4, h⟩ := bind_some h
      obtain ⟨r4, d4⟩ := crf_emit h4 k2.2
      simp only at r4
      exact crf_tail ih (by omega) (by omega) d4 h
  | Nomm.n5 p q, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hpp, hp6⟩, _⟩, hq⟩ := hok
    have ihq := crf_run env q hq msup region
    rw [cr5_modelC] at h
    obtain ⟨o, g1, h1, h⟩ := bind_some h
    obtain ⟨l1, d1⟩ := cr5_br_keeps (g := { g with re := g.re + 1 + 1 }) hi.2.1 h1
    have l1' : g.re + 1 + 1 ≤ g1.re := l1
    obtain ⟨nexF, g4, h4, h⟩ := bind_some h
    obtain ⟨nF, rfl, OF⟩ := ihq (CGoal.next (lazyReg (g.re + 1)) (jmp0 o)) g1 g4 nexF (cri_reg o (by omega) d1) h4
    obtain ⟨nexF', g5, h5, h⟩ := bind_some h
    rw [pastL_pure env.cod _ hpp region, pure_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨nexS, g6, h6, h7⟩ := bind_some h
    rw [cr2_run_pure env msup hpp hp6, map_apply] at h6
    obtain ⟨nS, e6, rfl⟩ := crf_map_some h6
    have l4 := OF.1
    have ip : CrInv g4 (CGoal.next (lazyReg g.re) nF.th) := cri_reg_j (by omega) OF.2.2.1.2 OF.2.1
    have OS := cro_run hpp hp6 ip e6
    have h7' : copyL (Next.toL nS) (Lazy.ofSure nF.laz) g6 = some (nex, g') := h7
    rw [copyL_toL, map_apply] at h7'
    obtain ⟨n', e7, rfl⟩ := crf_map_some h7'
    obtain ⟨l7, d7, ni7, s7, D7, L7⟩ := crf_copy_out (nb_this (show g.re < g1.re by omega))
      (fun y e1 e2 => by simp only [lazyReg, NMem] at e1 e2; omega) OF OS e7
    refine ⟨n', rfl, by omega, d7, ni7, fun y hy => ?_, D7, L7⟩
    rcases s7 y hy with e | e | e
    · exact Or.inl (by omega)
    · simp only [lazyReg, NMem] at e; exact Or.inl (by omega)
    · simp only [lazyReg, NMem] at e; exact Or.inl (by omega)
  | Nomm.n7 p q, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk, Bool.and_eq_true] at hok
    simp only [runLC] at h
    obtain ⟨nex1, g1, h1, h⟩ := bind_some h
    obtain ⟨n1, rfl, O1⟩ := crf_run env q hok.2 (some p) region gl g g1 nex1 hi h1
    rw [Next.goal_toL] at h
    obtain ⟨n2, rfl, O2⟩ := crf_run env p hok.1 msup region n1.goal g1 g' nex (cro_goal O1) h
    exact ⟨n2, rfl, cro_comp O1 O2⟩
  | Nomm.n2 _ _ (some _), hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.cons _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n0 _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n1 _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n6 _ _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n10 _ _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n11s _ _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n11d _ _ _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.n12 _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h
  | Nomm.mean _ _ _ _ _, hok, _, _, _, _, _, _, hi, h => crf_pure hok hi h

/-! ## The summary -/

/-- **`+run` on every nomm of the fragment with indirect calls**: for every
nomm of `indOk` (pure with no `%6` and `tenOk`, closed under `[2 p q ~]`
with `p` pure, under `%3`, `%4` and `%7`), every goal and state with
`CrInv`, every region and every `env`, the `$` arm of `+run` is `runLC env
msup` for every `msup` (and every `mono`, Hoon `sup` and rest of the state
with an empty `soft`), given only `slot? 7 ctx = some compK` and `slot? 52
ctx = some cod`. -/
theorem comp_run_all_c (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) : ∀ (n : Nomm), indOk n = true → ∀ (gl : CGoal CSet) (region : List Nat)
      (g : Gen (TreapMap mugF)), CrInv g gl → CompRunAtC env ctx n (CGoal.toL gl) region g
  | Nomm.n2 p q Option.none, hok, gl, region, g, hinv => by
    have hok' := hok
    simp only [indOk, Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨hpp, hp6⟩, htp⟩, hq⟩ := hok'
    have ihq := comp_run_all_c h7 hcode env q hq
    intro msup
    exact comp_run_n2 h7 hcode env msup p q hpp hp6 gl region g hinv
      ⟨fun s th g1 hi => ihq (CGoal.next s th) region g1 hi msup,
       fun s th g1 nex g2 hi e => crf_run env q hq msup region (CGoal.next s th) g1 g2 nex hi e,
       fun s th g1 hi => comp_run_all' h7 hcode p hpp hp6 htp (CGoal.next s th) region g1 hi⟩
  | Nomm.n3 p, hok, gl, region, g, hinv => by
    simp only [indOk] at hok
    have ih := comp_run_all_c h7 hcode env p hok
    intro msup
    exact comp_run_n3C h7 env msup p gl region g hinv (ih gl region g hinv msup)
      (fun s th g1 hi => ih (CGoal.next s th) region g1 hi msup)
  | Nomm.n4 p, hok, gl, region, g, hinv => by
    simp only [indOk] at hok
    have ih := comp_run_all_c h7 hcode env p hok
    intro msup
    exact comp_run_n4C h7 env msup p gl region g hinv (fun s th g1 hi => ih (CGoal.next s th) region g1 hi msup)
  | Nomm.n7 p q, hok, gl, region, g, hinv => by
    simp only [indOk, Bool.and_eq_true] at hok
    have ihp := comp_run_all_c h7 hcode env p hok.1
    have ihq := comp_run_all_c h7 hcode env q hok.2
    intro msup
    refine comp_run_n7C env msup p q (CGoal.toL gl) region g (ihq gl region g hinv (some p)) (fun nex g1 e => ?_)
    obtain ⟨n1, rfl, O1⟩ := crf_run env q hok.2 (some p) region gl g g1 nex hinv e
    rw [Next.goal_toL]
    exact ihp n1.goal region g1 (cro_goal O1) msup
  | Nomm.n2 _ _ (some _), hok, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.cons p q, hok, gl, region, g, hinv => by
    simp only [indOk, Bool.and_eq_true] at hok
    exact crc_of_pure env hok.1.1 (comp_run_all' h7 hcode _ hok.1.1 hok.1.2 hok.2 gl region g hinv)
  | Nomm.n0 _, hok, gl, region, g, hinv => by
    simp only [indOk, Bool.and_eq_true] at hok
    exact crc_of_pure env hok.1.1 (comp_run_all' h7 hcode _ hok.1.1 hok.1.2 hok.2 gl region g hinv)
  | Nomm.n1 _, hok, gl, region, g, hinv => by
    simp only [indOk, Bool.and_eq_true] at hok
    exact crc_of_pure env hok.1.1 (comp_run_all' h7 hcode _ hok.1.1 hok.1.2 hok.2 gl region g hinv)
  | Nomm.n5 p q, hok, gl, region, g, hinv => by
    have hok' := hok
    simp only [indOk, Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨hpp, hp6⟩, htp⟩, hq⟩ := hok'
    have ihq := comp_run_all_c h7 hcode env q hq
    intro msup
    exact comp_run_n5C h7 hcode env msup p q hpp hp6 gl region g hinv
      ⟨fun s th g1 hi => ihq (CGoal.next s th) region g1 hi msup,
       fun s th g1 nex g2 hi e => crf_run env q hq msup region (CGoal.next s th) g1 g2 nex hi e,
       fun s th g1 hi => comp_run_all' h7 hcode p hpp hp6 htp (CGoal.next s th) region g1 hi⟩
  | Nomm.n6 _ _ _, hok, _, _, _, _ => by simp [indOk, noSix] at hok
  | Nomm.n10 _ _ _, hok, gl, region, g, hinv => by
    simp only [indOk, Bool.and_eq_true] at hok
    exact crc_of_pure env hok.1.1 (comp_run_all' h7 hcode _ hok.1.1 hok.1.2 hok.2 gl region g hinv)
  | Nomm.n11s _ _ _, hok, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.n11d _ _ _ _, hok, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.n12 _ _, hok, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.mean _ _ _ _ _, hok, _, _, _, _ => by simp [indOk, Nomm.pure] at hok

/-- **`+run` with indirect calls at the entry of `+comp`**: on every nomm of
the fragment, from the bunt state with the goal `[%done ~]` and the region
`~`, the `$` arm of `+run` is `runLC env msup` (`comp_run_entry` for the
fragment with calls). -/
theorem comp_run_entry_c (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (n : Nomm) (hn : indOk n = true) :
    CompRunAtC env ctx n (CGoal.toL CGoal.done) [] genEntry :=
  comp_run_all_c h7 hcode env n hn CGoal.done [] genEntry cri_entry

/-- **An example**: the Nock `9` of arm `2` of the subject's head, then a
call whose formula is the product of a call, `[7 [0 2] [2 [0 1] [2 [0 3] [0
2] ~] ~]]`, under `%done`, from every state that does not drop: the link
with no hypothesis but the context. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (region : List Nat) (g : Gen (TreapMap mugF)) (hd : g.drop = false) :
    CompRunAtC env ctx (Nomm.n7 (Nomm.n2 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) Option.none)
      (Nomm.n0 2)) (CGoal.toL CGoal.done) region g :=
  comp_run_all_c h7 hcode env _ rfl CGoal.done region g ⟨trivial, hd, trivial, trivial⟩

end Compiler
end Formalization
