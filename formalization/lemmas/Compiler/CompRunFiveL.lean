import lemmas.Compiler.CompRunConsL

/-!
# `%5` and `%2` of `+run` on lazy goals, with lazy results

`%5` and the indirect call `[2 p q ~]` share their shape: two fresh
registers (`rp`, `rq`; `r-sub`, `r-fol`), a block that reads them (the
comparison of `%5` after its branch over the goal; the `%nok` block of the
call after `+kerf`), then the tail: `q` for the whole value in the second
register, `+past` over `p`, `p` for the first register, `+copy`.  Both parts
may call, so `+past` may park `q`'s need in a bond, and the `+copy` joins
two lazy needs.

* `%5` (`comp_run_n5L`): the branch over a lazy `%next` goal uses
  `+collapse-lazy-atom` on the lazy need (`cr5_brL`, through
  `comp_collapse_lazy_atom_all`), the other goals are fork-free
  (`cr5_br`); the tail is `cr5_tailL` (`comp_past`, `comp_copy_all`).
* `%2` (`comp_run_n2L`): `+simple-next` of any goal, `+kerf` of a lazy
  `next` (`comp_kerf_all`: the walk of the lazy need with `+kern`, a proxy
  at each bond block), the call block, and `cr2_tailL`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## The tails -/

/-- **The tail of `%5`** with lazy results: `q` into the comparison block
`o`, `+past` over `p`, `p` with the `then` of `q`'s `+past`, `+copy`. -/
theorem cr5_tailL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun) (rp rq o : Nat)
    (g1 : Gen (TreapMap mugF))
    (hq : CompRunAtR (runLC env msup) ctx q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rq) (jmp0 o))) region g1)
    (hp : ∀ nexF g2 nexF' g3, runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rq) (jmp0 o))) region g1 = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rp) nexF'.th)) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rq) (jmp0 o))) region g1 = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      runLC env msup p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rp) nexF'.th)) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (C (A o) (C (A rq) (C (A rp)
      (crSubj mono (Nomm.n5 p q).toNoun goalN (listNoun A region) sup (compCore g1 x ctx))))) cr5Tail
      = ((do
          let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rq) (jmp0 o))) region
          let nexF ← pastL noCode nexF p region
          let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rp) nexF.th)) region
          copyL nexS nexF.laz : CM (TreapMap mugF) (NextL CSet)) g1).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h15 := cr_ctx15 h7
  have hq1 := hq x mono sup hx
  rw [cr_goal_reg] at hq1
  simp only [crSubj, compCore] at hq1
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases eq : runLC (S := CSet) (Map := TreapMap mugF) env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rq) (jmp0 o)))
      region g1 with
  | none =>
    rw [eq] at hq1
    generalize comp.door = Dr at hq1 hD1 hD2 ⊢
    nock_open cr5Tail
    simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
      StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hq1
    simp only [Option.map_some, cr_next_nounL] at hq1
    have hpa := comp_past h7 hcode x g2 nexF p region hpn
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode nexF p region g2 with
    | none =>
      rw [e3] at hpa
      generalize comp.door = Dr at hq1 hD1 hD2 hpa ⊢
      unfold cr5Tail cr5T2 cr5T3
      simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
        StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      have hp1 := hp nexF g2 nexF' g3 eq e3 x mono sup hx
      rw [cr_goal_reg'] at hp1
      simp only [crSubj, compCore] at hp1
      cases eq2 : runLC (S := CSet) (Map := TreapMap mugF) env msup p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rp) nexF'.th))
          region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 ⊢
        unfold cr5Tail cr5T2 cr5T3
        simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
          StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, eq, e3]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 hcpy ⊢
        unfold cr5Tail cr5T2 cr5T3
        simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
          StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, hD2, cr_cp_arm, hcpy, eq, e3, cr_next_nounL]

/-! ## `%5` -/

/-- The branch of `%5` over a lazy goal: the block `o` that compares `rp`
with `rq`. -/
noncomputable def cr5BrML (rp rq : Nat) : CGoalL CSet → CM (TreapMap mugF) Nat
  | CGoalL.pick z o => emit ⟨[], [], Termin.eqq rp rq z o⟩
  | CGoalL.done => do
      let (o0, o1) ← doneBlocks
      emit ⟨[], [], Termin.eqq rp rq (jmp0 o0) (jmp0 o1)⟩
  | CGoalL.next laz th => do
      let a ← collapseLazyAtomL ⟨laz, th⟩
      match a with
      | Option.none =>
          if th.args = [] then emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩
          else fun _ => Option.none
      | some (r, o) => do
          let (z, o') ← forl r o
          emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩

theorem km_cr5BrML (rp rq : Nat) (goal : CGoalL CSet) : KM (cr5BrML rp rq goal) := by
  cases goal with
  | pick z o => exact KM.emit' _
  | done => exact KM.bind' km_doneBlocks fun _ => KM.emit' _
  | next laz th =>
    refine KM.bind' (km_collapseLazyAtomL _) fun a => ?_
    rcases a with _ | ⟨r, o⟩
    · exact KM.ite' _ (KM.emit' _) KM.fail
    · exact KM.bind' (km_forl _ _) fun _ => KM.emit' _

/-- The model of `%5` against `runLC` on a lazy goal. -/
theorem cr5_modelL (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) :
    (runLC env msup (Nomm.n5 p q) goal region : CM (TreapMap mugF) (NextL CSet)) g = (do
      let o ← cr5BrML g.re (g.re + 1) goal
      let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) (g.re + 1)) (jmp0 o))) region
      let nexF ← pastL env.cod nexF p region
      let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg (S := CSet) g.re) nexF.th)) region
      copyL nexS nexF.laz : CM (TreapMap mugF) (NextL CSet)) { g with re := g.re + 1 + 1 } := by
  cases goal <;> simp [runLC, CGoal.toL, cr5BrML, re, bind, StateT.bind, pure, StateT.pure] <;> rfl

/-- **The branch of `%5` on a lazy `%next` goal**: `+collapse-lazy-atom`
of the lazy need (`comp_collapse_lazy_atom_all`), then the comparison
block, through `+forl` when an atom is wanted. -/
theorem cr5_br_next (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (sur : Sure CSet)
    (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) (args : List (Option Nat)) (there : Nat)
    (hlok : LAll CrLok (Lazy.mk sur fk bd)) (mono nomm region sup : Noun) (rp rq : Nat) (g : Gen (TreapMap mugF)) :
    nock (C (A rq) (C (A rp) (crSubj mono nomm (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩).toNoun region sup
      (compCore g x ctx)))) cr5Br
      = (cr5BrML rp rq (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩) g).map fun p => C (A p.1) (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hD1 := comp_re_at
  have hD2 := comp_emit_at
  obtain ⟨hF, hB⟩ := walk_mdP_parts hx hlok
  have hcl := comp_collapse_lazy_atom_all h7 x g sur fk bd ⟨args, there⟩ hlok.1 hF hB (hx there)
    (fun _ g' _ => hx g'.bo)
  have hDc := comp_cla_at
  have hDf := comp_fl_at
  simp only [compCore, Jmp.toNoun] at hcl ⊢
  rcases ecl : collapseLazyAtomL (⟨Lazy.mk sur fk bd, ⟨args, there⟩⟩ : NextL CSet) g with _ | ⟨a, g1⟩
  · rw [ecl] at hcl
    generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
    nock_open cr5Br
    simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, cr5BrML, ecl, bind, StateT.bind, Jmp.toNoun]
  · rw [ecl] at hcl
    rcases a with _ | ⟨r, o⟩
    · cases args with
      | cons a0 rest =>
        simp only [listNoun, unitNoun, Option.map_some] at hcl
        generalize comp.door = Dr at hDc hD1 hD2 hDf hcl ⊢
        nock_open cr5Br
        simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, cr5BrML, ecl, bind, StateT.bind, Jmp.toNoun,
          unitNoun, listNoun]
      | nil =>
        simp only [listNoun] at hcl
        have he := cf_emit (x := x) hc g1 ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 there)⟩
        rw [cr_blob_equ] at he
        generalize comp.door = Dr at hDc hD1 hD2 hDf hcl he ⊢
        nock_open cr5Br
        simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, cr5BrML, ecl, bind, StateT.bind, Jmp.toNoun,
          unitNoun, listNoun, hD2, comp_emit_arm, he, cf_emit_g]
    · have hfl := comp_forl (x := x) hc g1 r o
      rw [fl_forl_eq] at hfl
      simp only [cf_emitG_bo, Option.map_some] at hfl
      generalize hg2 : cfEmitG (flB3 (g1.re + 1) g1.bo) (cfEmitG (flB2 g1.re g1.bo)
        (cfEmitG (flB1 r o) { g1 with re := g1.re + 1 + 1 })) = g2 at hfl
      have he := cf_emit (x := x) hc g2 ⟨[], [], Termin.eqq rp rq (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩
      rw [cr_blob_eqq0] at he
      simp only [compCore] at hfl
      have hm : cr5BrML rp rq (CGoalL.next (Lazy.mk sur fk bd) ⟨args, there⟩) g = some (g2.bo,
          cfEmitG ⟨[], [], Termin.eqq rp rq (jmp0 (g1.bo + 1)) (jmp0 (g1.bo + 1 + 1))⟩ g2) := by
        rw [← hg2]
        simp [cr5BrML, ecl, fl_forl_eq, bind, StateT.bind, pure, StateT.pure, cf_emit_g, cf_emitG_bo]
      rw [hm]
      generalize comp.door = Dr at hDc hD1 hD2 hDf hcl he hfl ⊢
      nock_open cr5Br
      simp [nock_exec, crSubj, CGoalL.toNoun, hDc, cr_cla_arm, hcl, Jmp.toNoun, unitNoun, hDf, comp_fl_arm, hfl, hD2,
        comp_emit_arm, he]

/-- **The branch of `%5` on every goal with the invariant.** -/
theorem cr5_brL (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (goal : CGoalL CSet)
    (g0 : Gen (TreapMap mugF)) (hi : GInv g0 goal) (mono nomm region sup : Noun) (rp rq : Nat) (g : Gen (TreapMap mugF)) :
    nock (C (A rq) (C (A rp) (crSubj mono nomm goal.toNoun region sup (compCore g x ctx)))) cr5Br
      = (cr5BrML rp rq goal g).map fun p => C (A p.1) (genNoun p.2 x) := by
  cases goal with
  | next laz th =>
    obtain ⟨sur, fk, bd⟩ := laz
    obtain ⟨args, there⟩ := th
    exact cr5_br_next h7 x hx sur fk bd args there (lall_mono (fun _ hs => hs.1) hi.1.1) mono nomm region sup rp rq g
  | pick z o => exact cr5_br h7 x hx (CGoal.pick z o) trivial mono nomm region sup rp rq g
  | done => exact cr5_br h7 x hx CGoal.done trivial mono nomm region sup rp rq g

/-- **The case `%5` of `+run` on every goal with the invariant**, `p` and
`q` of the plain class (`PartL`). -/
theorem comp_run_n5L (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtR (runLC env msup) ctx (Nomm.n5 p q) goal region g := by
  obtain ⟨hpc, hpn⟩ := hinted_nd env.cod P.nd
  have hd := ginv_drop hinv
  intro x mono sup hx
  have hre0 := comp_re' ctx x g
  have hre1 := comp_re' ctx x { g with re := g.re + 1 }
  have hbr := cr5_brL h7 x hx goal g hinv mono (Nomm.n5 p q).toNoun (listNoun A region) sup g.re (g.re + 1)
    { g with re := g.re + 1 + 1 }
  have hD1 := comp_re_at
  have hnn : (Nomm.n5 p q).toNoun = C (A 5) (C p.toNoun q.toNoun) := rfl
  rw [cr5_modelL, hnn, cr_disp_n5, cr5_eq]
  simp only [pastL_cod hpc]
  rw [hnn] at hbr
  cases eb : cr5BrML g.re (g.re + 1) goal { g with re := g.re + 1 + 1 } with
  | none =>
    rw [eb] at hbr
    simp only [crSubj, compCore, Option.map_none] at hbr hre0 hre1 ⊢
    generalize goal.toNoun = GN at hbr ⊢
    generalize C (A 5) (C p.toNoun q.toNoun) = NN at hbr ⊢
    generalize comp.door = Dr at hD1 hre0 hre1 hbr ⊢
    nock_open cr5Head
    simp [nock_exec, hre0, hre1, hD1, hbr, bind, StateT.bind, eb]
  | some r =>
    obtain ⟨o, g1⟩ := r
    rw [eb] at hbr
    obtain ⟨l1, b1, d1⟩ := km_drop (km_cr5BrML _ _ _) eb hd
    simp only at l1
    have iq : GInv g1 (CGoal.toL (CGoal.next (lazyReg (S := CSet) (g.re + 1)) (jmp0 o))) := ginv_reg o (by omega) d1
    have lp : LInv g1.re g1.bo (Lazy.ofSure (lazyReg (S := CSet) g.re)) := linv_reg (by omega)
    have ap : (lregs (Lazy.ofSure (lazyReg (S := CSet) g.re)) ++ lregs (Lazy.ofSure (lazyReg (S := CSet) (g.re + 1)))).Nodup := by
      simp [lregs_reg]
    have ht := cr5_tailL h7 hcode env msup p q hpn region x hx mono goal.toNoun sup g.re (g.re + 1) o g1
      (Q.link _ _ iq)
      (fun nexF g2 nexF' g3 e e3 => P.link _ _ (tail_pgoal iq lp (Q.res _ _ _ _ iq e) e3).1)
      (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => by
        have R2 := Q.res _ _ _ _ iq e
        exact (tail_copyH iq lp ap R2 e3 (P.res _ _ _ _ (tail_pgoal iq lp R2 e3).1 e4)).1)
    rw [hnn] at ht
    simp only [crSubj, compCore, Option.map_some] at hbr hre0 hre1 ht ⊢
    generalize goal.toNoun = GN at hbr ht ⊢
    generalize C (A 5) (C p.toNoun q.toNoun) = NN at hbr ht ⊢
    generalize comp.door = Dr at hD1 hre0 hre1 hbr ht ⊢
    nock_open cr5Head
    simp [nock_exec, hre0, hre1, hD1, hbr, ht, bind, StateT.bind, eb]

/-! ## The indirect call `%2` -/

/-- **The tail of the indirect call** with lazy results: `q` into the call
block `o`, `+past` over `p`, `p` with the `then` of `q`'s `+past`, `+copy`. -/
theorem cr2_tailL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup nexN : Noun) (out pro rSub rFol o : Nat)
    (g1 : Gen (TreapMap mugF))
    (hq : CompRunAtR (runLC env msup) ctx q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rFol) (jmp0 o))) region g1)
    (hp : ∀ nexF g2 nexF' g3, runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rFol) (jmp0 o))) region g1
      = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      CompRunAtR (runLC env msup) ctx p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rSub) nexF'.th)) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rFol) (jmp0 o)))
      region g1 = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      runLC env msup p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rSub) nexF'.th)) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (C (A o) (C (A rFol) (C (A rSub) (C (C (A out) (A pro)) (C nexN
      (crSubj mono (Nomm.n2 p q Option.none).toNoun goalN (listNoun A region) sup (compCore g1 x ctx))))))) cr2Tail
      = ((do
          let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg (S := CSet) rFol) (jmp0 o))) region
          let nexF ← pastL noCode nexF p region
          let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg (S := CSet) rSub) nexF.th)) region
          copyL nexS nexF.laz : CM (TreapMap mugF) (NextL CSet)) g1).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h15 := cr_ctx15 h7
  have hq1 := hq x mono sup hx
  rw [cr_goal_reg] at hq1
  simp only [crSubj, compCore] at hq1
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases eq : runLC (S := CSet) (Map := TreapMap mugF) env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o)))
      region g1 with
  | none =>
    rw [eq] at hq1
    generalize comp.door = Dr at hq1 hD1 hD2 ⊢
    nock_open cr2Tail
    simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
      StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hq1
    simp only [Option.map_some, cr_next_nounL] at hq1
    have hpa := comp_past h7 hcode x g2 nexF p region hpn
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode nexF p region g2 with
    | none =>
      rw [e3] at hpa
      generalize comp.door = Dr at hq1 hD1 hD2 hpa ⊢
      unfold cr2Tail cr2T2 cr2T3
      simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
        StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      have hp1 := hp nexF g2 nexF' g3 eq e3 x mono sup hx
      rw [cr_goal_reg'] at hp1
      simp only [crSubj, compCore] at hp1
      cases eq2 : runLC (S := CSet) (Map := TreapMap mugF) env msup p (CGoal.toL (CGoal.next (lazyReg rSub) nexF'.th))
          region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 ⊢
        unfold cr2Tail cr2T2 cr2T3
        simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
          StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, eq, e3]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hq1 hD1 hD2 hpa hp1 hcpy ⊢
        unfold cr2Tail cr2T2 cr2T3
        simp [nock_exec, crSubj, Nomm.toNoun, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, cr_bat_dol, hq1, bind,
          StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, hp1, eq2, hD2, cr_cp_arm, hcpy, eq, e3, cr_next_nounL,
          Function.comp_def]

/-- The model of the indirect call from `+kerf` on, with `+past` on the
empty code table. -/
noncomputable def cr2KfML (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (region : List Nat) (nex : NextL CSet) :
    CM (TreapMap mugF) (NextL CSet) := do
  let (out, pro) ← kerf nex
  let rSub ← re
  let rFol ← re
  let o ← emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩
  let nexF ← runLC env msup q (CGoal.toL (CGoal.next (lazyReg rFol) (jmp0 o))) region
  let nexF ← pastL noCode nexF p region
  let nexS ← runLC env msup p (CGoal.toL (CGoal.next (lazyReg rSub) nexF.th)) region
  copyL nexS nexF.laz

/-- **From `+kerf` on, on a lazy `next`**: `+kerf` (`comp_kerf_all`), the
two registers, the call block and `cr2_tailL`. -/
theorem cr2_kfL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region)
    (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun) (nex0 : NextL CSet)
    (g1 : Gen (TreapMap mugF)) (hd : g1.drop = false) (hlok : LAll CrLok nex0.laz) :
    nock (C nex0.goal.toNoun
      (crSubj mono (Nomm.n2 p q Option.none).toNoun goalN (listNoun A region) sup (compCore g1 x ctx))) cr2Kf
      = (cr2KfML env msup p q region nex0 g1).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  obtain ⟨-, hpn⟩ := hinted_nd env.cod P.nd
  have hk := comp_kerf_all hc hl hm x g1 nex0 (walk_mdP hx g1.bo hlok)
  have hD1 := comp_kerf_at
  have hD2 := comp_re_at
  have hD3 := comp_emit_at
  rw [cr_next_nounL]
  simp only [compCore] at hk ⊢
  cases ek : kerf nex0 g1 with
  | none =>
    rw [ek] at hk
    generalize comp.door = Dr at hk hD1 hD2 hD3 ⊢
    nock_open cr2Kf
    simp [nock_exec, crSubj, hD1, comp_kerf_arm, hk, cr2KfML, bind, StateT.bind, ek]
  | some r =>
    obtain ⟨⟨out, pro⟩, g2⟩ := r
    rw [ek] at hk
    simp only [Option.map_some] at hk
    obtain ⟨-, -, d2⟩ := km_drop (km_kerf _) ek hd
    have hre0 := comp_re' ctx x g2
    have hre1 := comp_re' ctx x { g2 with re := g2.re + 1 }
    have he := cf_emit (x := x) hc { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }
      ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
    rw [cr_blob_nok_hop] at he
    generalize hg5 : cfEmitG ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
      { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = g5 at he
    have r5 : g5.re = g2.re + 1 + 1 := by rw [← hg5, cf_emitG_re]
    have d5 : g5.drop = false := by rw [← hg5, cf_emitG_drop]; exact d2
    have iq : GInv g5 (CGoal.toL (CGoal.next (lazyReg (S := CSet) (g2.re + 1)) (jmp0 g2.bo))) :=
      ginv_reg g2.bo (by omega) d5
    have lp : LInv g5.re g5.bo (Lazy.ofSure (lazyReg (S := CSet) g2.re)) := linv_reg (by omega)
    have ap : (lregs (Lazy.ofSure (lazyReg (S := CSet) g2.re)) ++
        lregs (Lazy.ofSure (lazyReg (S := CSet) (g2.re + 1)))).Nodup := by simp [lregs_reg]
    have ht := cr2_tailL h7 hcode env msup p q hpn region x hx mono goalN sup
      (C (A 0x7478656e) (C nex0.laz.toNoun nex0.th.toNoun)) out pro g2.re (g2.re + 1) g2.bo g5 (Q.link _ _ iq)
      (fun nexF g6 nexF' g7 e e3 => P.link _ _ (tail_pgoal iq lp (Q.res _ _ _ _ iq e) e3).1)
      (fun nexF g6 nexF' g7 nexS g8 e e3 e4 => by
        have R2 := Q.res _ _ _ _ iq e
        exact (tail_copyH iq lp ap R2 e3 (P.res _ _ _ _ (tail_pgoal iq lp R2 e3).1 e4)).1)
    simp only [crSubj, compCore] at ht hre0 hre1
    generalize comp.door = Dr at hk hD1 hD2 hD3 hre0 hre1 he ht ⊢
    nock_open cr2Kf
    simp [nock_exec, crSubj, hD1, comp_kerf_arm, hk, hD2, hre0, hre1, hD3, comp_emit_arm, he, ht, cr2KfML, bind,
      StateT.bind, ek, re, cf_emit_g, hg5]

/-- **The case `%2` of `+run` for an indirect call on every goal with the
invariant**, `p` and `q` of the plain class (`PartL`): `+simple-next`,
`+kerf` of the lazy `next`, two registers, the block `[%nok r-sub r-fol
pro]`, `q`, `+past` over `p`, `p`, `+copy`. -/
theorem comp_run_n2L (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtR (runLC env msup) ctx (Nomm.n2 p q Option.none) goal region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨hpc, -⟩ := hinted_nd env.cod P.nd
  intro x mono sup hx
  have hmod : (runLC env msup (Nomm.n2 p q Option.none) goal region : CM (TreapMap mugF) (NextL CSet)) =
      simpleNextL goal >>= cr2KfML env msup p q region := by
    rw [cr2_model]; unfold cr2KfM cr2KfML; simp only [pastL_cod hpc]
  rw [hmod, cr2_noun, cr_disp_n2, cr2_ind]
  have hsn := comp_simple_next hc x g goal mono (C (A 2) (C p.toNoun (C q.toNoun (A 0)))) (listNoun A region) sup
  rw [bind_apply]
  cases e : simpleNextL (S := CSet) (Map := TreapMap mugF) goal g with
  | none =>
    rw [e] at hsn
    simp only [Option.map_none] at hsn
    simp only [crSubj, compCore] at hsn ⊢
    generalize comp.door = Dr at hsn ⊢
    nock_open cr2Ind
    simp [nock_exec, crSubj, hsn, cr_bat_sn]
  | some r =>
    obtain ⟨nex0, g1⟩ := r
    rw [e] at hsn
    simp only [Option.map_some] at hsn
    obtain ⟨-, -, ⟨⟨lnb, -⟩, d1, -⟩, -⟩ := simpleNextL_res hinv e
    have hk := cr2_kfL h7 hcode env msup p q P Q x hx mono goal.toNoun sup nex0 g1 d1 (lall_mono (fun _ hs => hs.1) lnb)
    rw [cr2_noun] at hk
    simp only [crSubj, compCore] at hsn hk ⊢
    generalize comp.door = Dr at hsn hk ⊢
    nock_open cr2Ind
    simp [nock_exec, crSubj, hsn, cr_bat_sn, hk]

end Compiler
end Formalization
