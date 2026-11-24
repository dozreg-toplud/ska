import lemmas.Compiler.CompRunResAll

/-!
# The leaves, `%3` and `%4` of `+run` on lazy goals

The cases `%0`, `%1`, `%3`, `%4` of `+run` on every goal with `GInv`.  The
goals `%done` and `%pick` are fork-free, so the old theorems on `CGoal.toL`
give them (`gInv_crInv`).  On `%next laz th` with any lazy need (forks and
bonds to any depth) the proofs are those of `comp_run_n0`, `comp_run_n1`,
`comp_run_n3C`, `comp_run_n4C` with the links on lazy needs in place of the
fork-free ones: `+from` is `cfr_all`, `+mede` is `comp_mede_all`,
`+none-equivalent` is `ne_all`, `+collapse-lazy-atom` is
`comp_collapse_lazy_atom_all`, each given the looks of `GInv` and an empty
`soft` (`crInvL_lok`, `crInvL_mdP`, `walk_mdP_parts`).  The Hoon and the
models were compared again on these branches: `+from` turns the forks and
the bonds with the same gate, `+mede` and `+collapse-lazy-atom` walk them
(`+walk-lazy`), no departure.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## `GInv` and `CrInv` on fork-free goals -/

theorem gInv_crInv {g : Gen (TreapMap mugF)} {gl : CGoal CSet} (h : GInv g (CGoal.toL gl)) : CrInv g gl := by
  cases gl with
  | next s th =>
    obtain ⟨⟨⟨⟨l, n⟩, -, -⟩, nd, -, -⟩, d, j⟩ := h
    exact ⟨l, d, ⟨n, j⟩, by simp only [GDist]; exact (distinct_iff_nodup _).2 (by simpa [lregs_ofSure] using nd)⟩
  | pick z o => exact ⟨trivial, h.1, ⟨h.2.1, h.2.2⟩, trivial⟩
  | done => exact ⟨trivial, h, trivial, trivial⟩

theorem crInv_gInv {g : Gen (TreapMap mugF)} {gl : CGoal CSet} (h : CrInv g gl) : GInv g (CGoal.toL gl) := by
  obtain ⟨l, d, gi, D⟩ := h
  cases gl with
  | next s th =>
    refine ⟨⟨⟨⟨l, gi.1⟩, trivial, trivial⟩, by simpa [lregs_ofSure] using (distinct_iff_nodup _).1 D,
      lkeys_ofSure _, by simp [llabs_ofSure]⟩, d, gi.2⟩
  | pick z o => exact ⟨d, gi.1, gi.2⟩
  | done => exact d

/-- The fork-free hypothesis on the parts from the general one. -/
theorem hp_toL {env : CallEnv} {msup : Option Nomm} {p : Nomm} {region : List Nat}
    (hp : ∀ (goal : CGoalL CSet) (g1 : Gen (TreapMap mugF)), GInv g1 goal →
      CompRunAtR (runLC env msup) ctx p goal region g1) :
    ∀ s th g1, CrInv g1 (CGoal.next s th) →
      CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next s th)) region g1 :=
  fun s th g1 hi => hp _ g1 (crInv_gInv hi)

/-! ## `%0` -/

/-- **The case `%0` of `+run` on a lazy `%next` goal**: `(bomb ..)` on axis
`0`, otherwise the goal itself, then `+from` (`cfr_all`) unless the axis is
`1`. -/
theorem comp_run_n0_next (h7 : slot? 7 ctx = some compK) (ax : Nat) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (g : Gen (TreapMap mugF)) (hlok : WalkP lok0 0 laz) :
    CompRunAt ctx (Nomm.n0 ax) (CGoalL.next laz th) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  intro x mono sup _
  simp only [Nomm.toNoun]
  rw [cr_disp_n0]
  by_cases h0 : ax = 0
  · subst h0
    have hD := comp_bomb_at
    simp only [compCore]
    have hb := comp_bomb (S := CSet) x hc g (some th.there)
    simp [compCore, bomb, cd_emit_eq, bind, StateT.bind, pure, StateT.pure, unitNoun, Next.goal,
      CGoal.toNoun, Jmp.toNoun, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty,
      listNoun] at hb
    generalize comp.door = Dr at hb hD ⊢
    nock_open crK0
    simp [nock_exec, crSubj, hD, comp_bomb_arm, CGoalL.toNoun, Jmp.toNoun, unitNoun, hb,
      runL, bombL, cd_emit_eq, NextL.goal, Next.goal, CGoal.toNoun, Lazy.toNoun_ofSure, Functor.map,
      StateT.map, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, listNoun]
  · have h0' : ¬ (0 = ax) := fun h => h0 h.symm
    have hD2 := comp_from_at
    have hsn := comp_simple_next hc x g (CGoalL.next laz th) mono (C (A 0) (A ax)) (listNoun A region) sup
    have e : simpleNextL (CGoalL.next laz th) g = some (⟨laz, th⟩, g) := rfl
    rw [e] at hsn
    simp only [crSubj, compCore, Option.map_some] at hsn
    have hng : (NextL.goal ⟨laz, th⟩ : CGoalL CSet).toNoun = C (A 0x7478656e) (C laz.toNoun th.toNoun) := rfl
    rw [hng] at hsn
    have hf := cfr_all hc (genNoun g x) ax laz 0 hlok
    simp only [compCore]
    generalize comp.door = Dr at hsn hD2 hf ⊢
    nock_open crK0
    by_cases h1 : ax = 1
    · subst h1
      simp [nock_exec, crSubj, hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind, StateT.bind]
    · have h1' : ¬ (1 = ax) := fun h => h1 h.symm
      cases ef : Lazy.fromL ax laz with
      | none =>
        rw [ef] at hf
        simp [nock_exec, crSubj, h0, h0', h1, h1', hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind,
          StateT.bind, hD2, comp_from_arm, hf, ef, simpleNextL]
      | some laz' =>
        rw [ef] at hf
        simp [nock_exec, crSubj, h0, h0', h1, h1', hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind,
          StateT.bind, hD2, comp_from_arm, hf, ef, simpleNextL]
        simp [NextL.goal, CGoalL.toNoun]

/-- **The case `%0` on every goal with the invariant.** -/
theorem comp_run_n0L (h7 : slot? 7 ctx = some compK) (ax : Nat) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hi : GInv g goal) : CompRunAt ctx (Nomm.n0 ax) goal region g := by
  cases goal with
  | next laz th => exact comp_run_n0_next h7 ax laz th region g (crInvL_lok (crInvL_of_gInv hi) 0)
  | pick z o => exact comp_run_n0 h7 ax (CGoal.pick z o) region g trivial
  | done => exact comp_run_n0 h7 ax CGoal.done region g trivial

/-! ## `%1` -/

/-- **The case `%1` of `+run` on a lazy `%next` goal**: `+mede`
(`comp_mede_all`). -/
theorem comp_run_n1_next (h7 : slot? 7 ctx = some compK) (k : Noun) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (g : Gen (TreapMap mugF)) (hlok : LAll CrLok laz) :
    CompRunAt ctx (Nomm.n1 k) (CGoalL.next laz th) region g := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  intro x mono sup hx
  simp only [Nomm.toNoun]
  rw [cr_disp_n1]
  have hmd := comp_mede_all hc hl hm x g th k laz (walk_mdP hx g.bo hlok)
  have hD := comp_md_at
  simp only [compCore, Jmp.toNoun] at hmd ⊢
  generalize comp.door = Dr at hmd hD ⊢
  nock_open crK1
  cases e : medeL th k laz g with
  | none =>
    rw [e] at hmd
    simp [nock_exec, crSubj, hD, comp_md_arm, CGoalL.toNoun, Jmp.toNoun, hmd, runL, e, bind, StateT.bind]
  | some r =>
    rw [e] at hmd
    simp [nock_exec, crSubj, hD, comp_md_arm, CGoalL.toNoun, Jmp.toNoun, hmd, runL, e, bind, StateT.bind,
      pure, StateT.pure, NextL.goal, Lazy.toNoun_ofSure, cr_bunt_noun, cr_bunt_lazy, jmp0, listNoun]

/-- **The case `%1` on every goal with the invariant.** -/
theorem comp_run_n1L (h7 : slot? 7 ctx = some compK) (k : Noun) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hi : GInv g goal) : CompRunAt ctx (Nomm.n1 k) goal region g := by
  cases goal with
  | next laz th => exact comp_run_n1_next h7 k laz th region g (lall_mono (fun _ hs => hs.1) hi.1.1)
  | pick z o => exact comp_run_n1 h7 k (CGoal.pick z o) region g trivial
  | done => exact comp_run_n1 h7 k CGoal.done region g trivial

/-! ## `%4` -/

/-- **The case `%4` of `+run` on a lazy `%next` goal**: `+collapse-lazy-atom`
(`comp_collapse_lazy_atom_all`), or a fresh register when the goal needs
nothing, then the increment and `p` into the argument register. -/
theorem comp_run_n4_next (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p : Nomm)
    (sur : Sure CSet) (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) (args : List (Option Nat))
    (there : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) (hd : g.drop = false)
    (hlok : LAll CrLok (Lazy.mk sur fk bd))
    (hp : ∀ s th g1, CrInv g1 (CGoal.next s th) → CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next s th)) region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n4 p) (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  intro x mono sup hx
  simp only [Nomm.toNoun]
  rw [cr_disp_n4]
  obtain ⟨hF, hB⟩ := walk_mdP_parts hx hlok
  have hcl := comp_collapse_lazy_atom_all h7 x g sur fk bd ⟨args, there⟩ hlok.1 hF hB (hx there)
    (fun _ g' _ => hx g'.bo)
  have hDc := comp_cla_at
  have hD1 := comp_re_at
  have hD2 := comp_emit_at
  simp only [compCore, Jmp.toNoun] at hcl ⊢
  rcases ecl : collapseLazyAtomL (⟨Lazy.mk sur fk bd, ⟨args, there⟩⟩ : NextL CSet) g with _ | ⟨a, g1⟩
  · rw [ecl] at hcl
    generalize comp.door = Dr at hDc hD1 hD2 hcl ⊢
    nock_open crK4
    simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind, StateT.bind, Jmp.toNoun]
  · rw [ecl] at hcl
    have d1 := (km_drop (km_collapseLazyAtomL _) ecl hd).2.2
    rcases a with _ | ⟨pro, th'⟩
    · cases args with
      | cons a0 rest =>
        have hre := comp_re' ctx x g1
        simp only [listNoun, unitNoun, Option.map_some] at hcl
        generalize comp.door = Dr at hDc hD1 hD2 hcl hre ⊢
        nock_open crK4
        simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
          StateT.bind, Jmp.toNoun, hre, hD1, unitNoun, listNoun, re]
      | nil =>
        simp only [listNoun] at hcl
        have hre := comp_re' ctx x g1
        have hre2 := comp_re' ctx x { g1 with re := g1.re + 1 }
        have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 + 1 }
          ⟨[], [Pole.inc (g1.re + 1) g1.re], Termin.hop (jmp0 there)⟩
        rw [cr_blob_inc_hop] at he
        have hr := hp (lazyReg (g1.re + 1)) (jmp0 g1.bo) (cfEmitG ⟨[], [Pole.inc (g1.re + 1) g1.re], Termin.hop (jmp0 there)⟩
          { g1 with re := g1.re + 1 + 1 }) (cri_reg_emit _ _ _ _ _ (by omega) d1) x mono sup hx
        rw [cr_goal_reg] at hr
        simp only [crSubj, compCore] at hr hre hre2
        generalize comp.door = Dr at hDc hD1 hD2 hcl hre hre2 he hr ⊢
        nock_open crK4
        simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
          StateT.bind, Jmp.toNoun, hre, hre2, hD1, hD2, comp_emit_arm, he, unitNoun,
          listNoun, re, pure, StateT.pure, cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr, CGoal.toL,
          cf_emit_g]
    · have hre := comp_re' ctx x g1
      have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 }
        ⟨[], [Pole.inc g1.re pro], Termin.hop (jmp0 th')⟩
      rw [cr_blob_inc_hop] at he
      have hr := hp (lazyReg g1.re) (jmp0 g1.bo) (cfEmitG ⟨[], [Pole.inc g1.re pro], Termin.hop (jmp0 th')⟩
        { g1 with re := g1.re + 1 }) (cri_reg_emit _ _ _ _ _ (by omega) d1) x mono sup hx
      rw [cr_goal_reg] at hr
      simp only [crSubj, compCore] at hr hre
      generalize comp.door = Dr at hDc hD1 hD2 hcl hre he hr ⊢
      nock_open crK4
      simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, runLC, ecl, bind,
        StateT.bind, Jmp.toNoun, hre, hD1, hD2, comp_emit_arm, he, unitNoun,
        listNoun, re, pure, StateT.pure, cr_bat_dol, h15, ct_lfr_at, ct_lfr_arm, ct_lfr_gate, hr, CGoal.toL,
        cf_emit_g]

/-- **The case `%4` on every goal with the invariant.** -/
theorem comp_run_n4L (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p : Nomm)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal)
    (hp : ∀ (goal' : CGoalL CSet) (g1 : Gen (TreapMap mugF)), GInv g1 goal' →
      CompRunAtR (runLC env msup) ctx p goal' region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n4 p) goal region g := by
  cases goal with
  | next laz th =>
    obtain ⟨sur, fk, bd⟩ := laz
    obtain ⟨args, there⟩ := th
    exact comp_run_n4_next h7 env msup p sur fk bd args there region g hi.2.1 (lall_mono (fun _ hs => hs.1) hi.1.1)
      (hp_toL hp)
  | pick z o => exact comp_run_n4C h7 env msup p (CGoal.pick z o) region g (gInv_crInv hi) (hp_toL hp)
  | done => exact comp_run_n4C h7 env msup p CGoal.done region g (gInv_crInv hi) (hp_toL hp)

/-! ## `%3` -/

/-- **The case `%3` of `+run` on a lazy `%next` goal**: `+none-equivalent`
(`ne_all`), then either `p` for the goal itself, or `+collapse-lazy-atom`,
`+forl` and a `%clq` block on a fresh register for `p`. -/
theorem comp_run_n3_next (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p : Nomm)
    (sur : Sure CSet) (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) (args : List (Option Nat))
    (there : Nat) (region : List Nat) (g : Gen (TreapMap mugF)) (hd : g.drop = false)
    (hlok : LAll CrLok (Lazy.mk sur fk bd))
    (hg : CompRunAtR (runLC env msup) ctx p (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩) region g)
    (hp : ∀ s th g1, CrInv g1 (CGoal.next s th) → CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next s th)) region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n3 p) (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  intro x mono sup hx
  simp only [Nomm.toNoun]
  rw [cr_disp_n3]
  have hD0 := compK_ne
  have hne0 := ne_all (Lazy.mk sur fk bd)
  by_cases hne : Lazy.noneEquivalentL (Lazy.mk sur fk bd) = true
  · have hr := hg x mono sup hx
    simp only [crSubj, compCore, CGoalL.toNoun] at hr
    simp only [compCore]
    generalize comp.door = Dr at hr ⊢
    nock_open crK3
    simp [nock_exec, crSubj, CGoalL.toNoun, h7, hD0, ne_arm, hne0, hne, loob, cr_bat_dol, hr, runLC]
  · have hne' : Lazy.noneEquivalentL (Lazy.mk sur fk bd) = false := by simpa using hne
    obtain ⟨hF, hB⟩ := walk_mdP_parts hx hlok
    have hcl := comp_collapse_lazy_atom_all h7 x g sur fk bd ⟨args, there⟩ hlok.1 hF hB (hx there)
      (fun _ g' _ => hx g'.bo)
    have hDc := comp_cla_at
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    have hDf := comp_fl_at
    simp only [compCore, Jmp.toNoun] at hcl ⊢
    rcases ecl : collapseLazyAtomL (⟨Lazy.mk sur fk bd, ⟨args, there⟩⟩ : NextL CSet) g with _ | ⟨a, g1⟩
    · rw [ecl] at hcl
      generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
      nock_open crK3
      simp [nock_exec, crSubj, CGoalL.toNoun, h7, hD0, ne_arm, hne0, hne', loob, hDc, cr_cla_arm, hcl, runLC,
        ecl, bind, StateT.bind, Jmp.toNoun]
    · rw [ecl] at hcl
      have d1 := (km_drop (km_collapseLazyAtomL _) ecl hd).2.2
      rcases a with _ | ⟨r, o⟩
      · generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
        nock_open crK3
        simp [nock_exec, crSubj, CGoalL.toNoun, h7, hD0, ne_arm, hne0, hne', loob, hDc, cr_cla_arm, hcl, runLC,
          ecl, bind, StateT.bind, Jmp.toNoun, unitNoun]
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
            (by rw [← hg2, cf_emitG_drop, cf_emitG_drop, cf_emitG_drop]; exact d1)) x mono sup hx
        rw [cr_goal_reg] at hr
        simp only [crSubj, compCore, cf_emitG_bo, Option.map_some] at hr hre hfl
        have hm : runLC (S := CSet) (Map := TreapMap mugF) env msup (Nomm.n3 p)
            (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩) region g
            = runLC env msup p (CGoal.toL (CGoal.next (lazyReg g2.re) (jmp0 g2.bo))) region
              (cfEmitG ⟨[], [], Termin.clq g2.re (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
                { g2 with re := g2.re + 1 }) := by
          rw [← hg2]
          simp [runLC, CGoal.toL, hne', ecl, fl_forl_eq, re, bind, StateT.bind,
            pure, StateT.pure, cf_emit_g, cf_emitG_bo, cf_emitG_re]
        rw [hm]
        generalize comp.door = Dr at hDc hD1 hD2 hDf hcl hre he hr hfl ⊢
        nock_open crK3
        simp [nock_exec, crSubj, CGoalL.toNoun, h7, hD0, ne_arm, hne0, hne', loob, hDc, cr_cla_arm, hcl,
          Jmp.toNoun, unitNoun, hDf, comp_fl_arm, hfl, hre, hD1, hD2, comp_emit_arm, he, cr_bat_dol, h15,
          ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hr, cf_emitG_bo]

/-- **The case `%3` on every goal with the invariant.** -/
theorem comp_run_n3L (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p : Nomm)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal)
    (hp : ∀ (goal' : CGoalL CSet) (g1 : Gen (TreapMap mugF)), GInv g1 goal' →
      CompRunAtR (runLC env msup) ctx p goal' region g1) :
    CompRunAtR (runLC env msup) ctx (Nomm.n3 p) goal region g := by
  cases goal with
  | next laz th =>
    obtain ⟨sur, fk, bd⟩ := laz
    obtain ⟨args, there⟩ := th
    exact comp_run_n3_next h7 env msup p sur fk bd args there region g hi.2.1 (lall_mono (fun _ hs => hs.1) hi.1.1)
      (hp _ g hi) (hp_toL hp)
  | pick z o =>
    exact comp_run_n3C h7 env msup p (CGoal.pick z o) region g (gInv_crInv hi) (hp _ g hi) (hp_toL hp)
  | done => exact comp_run_n3C h7 env msup p CGoal.done region g (gInv_crInv hi) (hp _ g hi) (hp_toL hp)

end Compiler
end Formalization
