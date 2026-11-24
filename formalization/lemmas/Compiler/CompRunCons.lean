import lemmas.Compiler.CompRunCases
import lemmas.Ska.CompCollapseThree

/-!
# The cons case of `+run`

`crKc` is `crcHead` (`crc_eq`, `Compiler/CompRunCases.lean`): the `=>` that
turns a `%done` goal into `[%next (lazy-from-reg r) ~ o]` (a fresh register
`r` and a block `[%don r]`), then the `?-` over the goal: `crcPick` for
`%pick` (a `[%bom ~]` block, `q` on `[%next *need-lazy ~ o]`, `+past`, `p` on
`[%next *need-lazy then]`, `+copy`) and, behind a `%toss` hint, `+split`
followed by `crcNTail` for `%next` (`crc_ntail`).  The `%done` branch of the
`?-` is never reached.

`crc_pick` links the branch `%pick`, `crc_next` the `+split` with its tail,
and `comp_run_cons` the whole case, for pure `p` and `q` with no `%6`, on a
fork-free goal with no look at `0`, given `CompRunAt` of `p` and `q` on every
fork-free `%next` goal with no look at `0`, and the side conditions on the
states the model reaches: the needs that `+split` returns have no look at
`0` (`hsp`), and the `+copy` meets `CrCopyOk` (`hcp`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The block `[~ ~ %bom ~]`. -/
theorem crc_blob_bom : Blob.toNoun ⟨[], [], Termin.bom Option.none⟩
    = C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.bom, unitNoun]

/-- The noun of the goal `[%next *need-lazy th]`. -/
theorem crc_goal_bunt (th : Jmp) : (CGoal.toL (CGoal.next Sure.bunt th) : CGoalL CSet).toNoun
    = C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) th.toNoun) := by
  rw [cr_goal_sure, cr_bunt_lazy]

/-- **The branch `%pick` of the cons case**: the `[%bom ~]` block `o`, the
run of `q` on `[%next *need-lazy ~ o]`, `+past` (the identity on a pure
`p`), the run of `p` on `[%next *need-lazy then]`, `+copy`. -/
theorem crc_pick (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (p q : Nomm) (hpp : p.pure = true) (hqp : q.pure = true) (hp6 : noSix p = true)
    (hq6 : noSix q = true) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun)
    (g : Gen (TreapMap mugF))
    (hq : CompRunAt ctx q (CGoal.toL (CGoal.next Sure.bunt (jmp0 g.bo))) region (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g))
    (hp : ∀ th g2, CompRunAt ctx p (CGoal.toL (CGoal.next Sure.bunt th)) region g2)
    (hcp : ∀ nex2 g2 nex1 g3, run q (CGoal.next Sure.bunt (jmp0 g.bo)) (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g) = some (nex2, g2) →
      run p (CGoal.next Sure.bunt nex2.th) g2 = some (nex1, g3) → CrCopyOk g3 nex1 nex2.laz) :
    nock (crSubj mono (Nomm.cons p q).toNoun goalN (listNoun A region) sup (compCore g x ctx)) crcPick
      = ((do
          let nex2 ← run q (CGoal.next Sure.bunt (jmp0 g.bo))
          let nex1 ← run p (CGoal.next Sure.bunt nex2.th)
          copy nex1 nex2.laz : CM (TreapMap mugF) (Next CSet)) (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g)).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, hl, -⟩ := comp_ctx_pill ctx h7
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.bom Option.none⟩
  rw [crc_blob_bom] at he
  have hv1 := cr_at_run hqp hq6 hq x mono sup hx
  rw [crc_goal_bunt, cr_jmp0] at hv1
  simp only [crSubj, compCore] at hv1
  have hD0 := comp_emit_at
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases eq : run (S := CSet) (Map := TreapMap mugF) q (CGoal.next Sure.bunt (jmp0 g.bo)) (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g) with
  | none =>
    rw [eq] at hv1
    generalize comp.door = Dr at hv1 hD0 hD1 hD2 he ⊢
    nock_open crcPick
    simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nex2, g2⟩ := r
    rw [eq] at hv1
    simp only [Option.map_some, cr_next_noun'] at hv1
    have hpa2 := cr_past_pure h7 hcode x g2 nex2 p hpp region
    have hq1 := cr_at_run hpp hp6 (hp nex2.th g2) x mono sup hx
    rw [crc_goal_bunt] at hq1
    simp only [crSubj, compCore] at hq1
    cases eq2 : run (S := CSet) (Map := TreapMap mugF) p (CGoal.next Sure.bunt nex2.th) g2 with
    | none =>
      rw [eq2] at hq1
      generalize comp.door = Dr at hv1 hD0 hD1 hD2 he hpa2 hq1 ⊢
      nock_open crcPick
      simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq,
        h7, hcode, hD1, cr_past_arm, hpa2, hq1, eq2]
    | some r' =>
      obtain ⟨nex1, g3⟩ := r'
      rw [eq2] at hq1
      simp only [Option.map_some, cr_next_noun'] at hq1
      obtain ⟨hlt, hrt, hm⟩ := hcp nex2 g2 nex1 g3 eq eq2
      have hcpy := comp_copy (x := x) hc hl g3 nex1 nex2.laz hlt hrt hm
      simp only [compCore, cr_next_noun'] at hcpy
      generalize comp.door = Dr at hv1 hD0 hD1 hD2 he hpa2 hq1 hcpy ⊢
      nock_open crcPick
      simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq,
        h7, hcode, hD1, cr_past_arm, hpa2, hq1, eq2, hD2, cr_cp_arm, hcpy, cr_next_noun']

/-! ## The `%next` branch and the whole case -/

theorem crc_split_arm (d : Noun) : nock d comp.split.arm = some (C comp.split.battery
    (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) d)) := by
  nock_open comp.split.arm; simp only [nock_exec]

/-- The noun of every nomm is a cell. -/
theorem crc_nomm_cell (n : Nomm) : ∃ a b, n.toNoun = C a b := by
  cases n <;> exact ⟨_, _, rfl⟩

theorem cr_disp_cons (a b t mono goal region sup D : Noun) :
    nock (crSubj mono (C (C a b) t) goal region sup D) crDol
      = nock (crSubj mono (C (C a b) t) goal region sup D) crKc := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- The model of the cons case on a `%next` goal, both `+past` dropped. -/
theorem crc_run_next (p q : Nomm) (hpp : p.pure = true) (hqp : q.pure = true) (s : Sure CSet) (th : Jmp)
    (g : Gen (TreapMap mugF)) :
    run (Nomm.cons p q) (CGoal.next s th) g = (do
      let (hed, tel, o) ← split ⟨s, th⟩
      let nex2 ← run q (CGoal.next tel (jmp0 o))
      let nex1 ← run p (CGoal.next hed nex2.th)
      copy nex1 nex2.laz : CM (TreapMap mugF) (Next CSet)) g := by
  simp [run, cr_past_model hpp, cr_past_model hqp, bind, StateT.bind, pure, StateT.pure]

/-- The model of the cons case on a `%pick` goal, `+past` dropped. -/
theorem crc_run_pick (p q : Nomm) (hpp : p.pure = true) (z o : Jmp) (g : Gen (TreapMap mugF)) :
    run (Nomm.cons p q) (CGoal.pick z o) g = (do
      let nex2 ← run q (CGoal.next Sure.bunt (jmp0 g.bo))
      let nex1 ← run p (CGoal.next Sure.bunt nex2.th)
      copy nex1 nex2.laz : CM (TreapMap mugF) (Next CSet)) (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g) := by
  simp [run, cr_past_model hpp, bind, StateT.bind, pure, StateT.pure, cf_emit_g]

/-- The model of the cons case on `%done`: a fresh register `r`, the block
`[%don r]`, then the case on `[%next (lazy-from-reg r) ~ o]`. -/
theorem crc_run_done (p q : Nomm) (g : Gen (TreapMap mugF)) :
    run (S := CSet) (Nomm.cons p q) CGoal.done g = run (Nomm.cons p q) (CGoal.next (lazyReg g.re) (jmp0 g.bo))
      (cfEmitG ⟨[], [], Termin.don g.re⟩ { g with re := g.re + 1 }) := by
  simp [run, re, bind, StateT.bind, pure, StateT.pure, cf_emit_g]

/-- `+split` returns needs with no look at `0` (it crashes on one). -/
theorem crc_split_lok (nex : Next CSet) (g g1 : Gen (TreapMap mugF)) (hed tel : Sure CSet) (o : Nat)
    (h : split nex g = some ((hed, tel, o), g1)) :
    (∀ y ∈ HoonSet.toList hed.lok, y ≠ 0) ∧ (∀ y ∈ HoonSet.toList tel.lok, y ≠ 0) := by
  simp only [Comp.split, splitSure, bind, StateT.bind, cf_emit_g] at h
  cases e : splitLok nex.laz.lok with
  | none => simp [e] at h
  | some lt =>
    obtain ⟨lh, lt'⟩ := lt
    have := splitLok_ne0 e
    cases e2 : splitNeed nex.laz.ned g.bo (cfEmitG ⟨[], [], Termin.hop nex.th⟩ g) with
    | none => simp [e, e2] at h
    | some r =>
      simp [e, e2, pure, StateT.pure] at h
      obtain ⟨⟨rfl, rfl, -⟩, -⟩ := h
      exact this

/-- **The `%next` branch of the cons case**: `+split` (no look at `0` in the
goal), then `crcNTail`. -/
theorem crc_next (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (p q : Nomm) (hpp : p.pure = true) (hqp : q.pure = true) (hp6 : noSix p = true)
    (hq6 : noSix q = true) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono sup : Noun)
    (s : Sure CSet) (th : Jmp) (hlok : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) (g : Gen (TreapMap mugF))
    (hp : ∀ s th g1, (∀ y ∈ HoonSet.toList s.lok, y ≠ 0) → CompRunAt ctx p (CGoal.toL (CGoal.next s th)) region g1)
    (hq : ∀ s th g1, (∀ y ∈ HoonSet.toList s.lok, y ≠ 0) → CompRunAt ctx q (CGoal.toL (CGoal.next s th)) region g1)
    (hcp : ∀ hed tel o g1 nex2 g2 nex1 g3, split ⟨s, th⟩ g = some ((hed, tel, o), g1) →
      run q (CGoal.next tel (jmp0 o)) g1 = some (nex2, g2) →
      run p (CGoal.next hed nex2.th) g2 = some (nex1, g3) → CrCopyOk g3 nex1 nex2.laz) :
    nock (crSubj mono (Nomm.cons p q).toNoun (CGoal.toL (CGoal.next s th)).toNoun (listNoun A region) sup
      (compCore g x ctx)) crKc
      = (run (Nomm.cons p q) (CGoal.next s th) g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hsp := comp_split (x := x) hc g ⟨s, th⟩ hlok
  simp only [Next.goal, CGoal.toNoun, compCore] at hsp
  have hDs := cr_split_at
  rw [crc_run_next p q hpp hqp, crc_eq, cr_goal_sure]
  cases es : split (Map := TreapMap mugF) ⟨s, th⟩ g with
  | none =>
    rw [es] at hsp
    simp only [crSubj, compCore, Option.map_none] at hsp ⊢
    generalize comp.door = Dr at hDs hsp ⊢
    nock_open crcHead
    simp [nock_exec, hDs, crc_split_arm, hsp, bind, StateT.bind, es]
  | some r =>
    obtain ⟨⟨hed, tel, o⟩, g1⟩ := r
    rw [es] at hsp
    obtain ⟨hh0, ht0⟩ := crc_split_lok _ g g1 hed tel o es
    have ht := crc_ntail h7 hcode p q hpp hqp hp6 hq6 region x hx mono
      (C (A 0x7478656e) (C (lazyNoun s) th.toNoun)) sup hed tel o g1 (hq tel (jmp0 o) g1 ht0)
      (fun th2 g2 => hp hed th2 g2 hh0)
      (fun nex2 g2 nex1 g3 e1 e2 => hcp hed tel o g1 nex2 g2 nex1 g3 es e1 e2)
    simp only [crSubj, compCore, Option.map_some] at hsp ht ⊢
    generalize (Nomm.cons p q).toNoun = NN at ht ⊢
    generalize comp.door = Dr at hDs hsp ht ⊢
    nock_open crcHead
    simp [nock_exec, hDs, crc_split_arm, hsp, ht, bind, StateT.bind, es]

/-- The block `[~ ~ %don r]`. -/
theorem crc_blob_don (r : Nat) : Blob.toNoun ⟨[], [], Termin.don r⟩
    = C (A 0) (C (A 0) (C (A 0x6e6f64) (A r))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.don]

/-- **The `=>` of the cons case on `%done`**: a fresh register `r`, the
block `[%don r]` under a fresh label `o`, and the body runs on the goal
`[%next (lazy-from-reg r) ~ o]`, on which the `=>` keeps the subject. -/
theorem crc_done_step (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (mono nn region sup : Noun) :
    nock (crSubj mono nn (CGoal.toL (CGoal.done : CGoal CSet)).toNoun region sup (compCore g x ctx)) crcHead
      = nock (crSubj mono nn (CGoal.toL (CGoal.next (lazyReg g.re) (jmp0 g.bo)) : CGoalL CSet).toNoun region sup
          (compCore (cfEmitG ⟨[], [], Termin.don g.re⟩ { g with re := g.re + 1 }) x ctx)) crcHead := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  have hre := comp_re' ctx x g
  have he := cf_emit (x := x) hc { g with re := g.re + 1 } ⟨[], [], Termin.don g.re⟩
  rw [crc_blob_don] at he
  simp only at he
  have hD1 := comp_re_at
  have hD2 := comp_emit_at
  have hDs := cr_split_at
  rw [cr_goal_reg]
  simp only [compCore] at hre ⊢
  generalize comp.door = Dr at hD1 hD2 hDs he hre ⊢
  nock_open crcHead
  conv => { rhs; arg 2; unfold crcHead }
  simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hD1, hD2, comp_emit_arm, he, h15, ct_lfr_at,
    ct_lfr_arm, ct_lfr_gate, hDs, crc_split_arm]

/-- The side condition of `+copy` in the cons case on a `%next` goal, at
the states the model reaches. -/
def CrcNextCopy (p q : Nomm) (s : Sure CSet) (th : Jmp) (g : Gen (TreapMap mugF)) : Prop :=
  ∀ hed tel o g1 nex2 g2 nex1 g3, split ⟨s, th⟩ g = some ((hed, tel, o), g1) →
    run q (CGoal.next tel (jmp0 o)) g1 = some (nex2, g2) →
    run p (CGoal.next hed nex2.th) g2 = some (nex1, g3) → CrCopyOk g3 nex1 nex2.laz

/-- The side condition of `+copy` in the cons case, at the states the model
reaches from the goal `gl` and the state `g`. -/
def CrcCopy (p q : Nomm) (gl : CGoal CSet) (g : Gen (TreapMap mugF)) : Prop :=
  match gl with
  | CGoal.next s th => CrcNextCopy p q s th g
  | CGoal.done => CrcNextCopy p q (lazyReg g.re) (jmp0 g.bo)
      (cfEmitG ⟨[], [], Termin.don g.re⟩ { g with re := g.re + 1 })
  | CGoal.pick _ _ => ∀ nex2 g2 nex1 g3,
      run q (CGoal.next Sure.bunt (jmp0 g.bo)) (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g) = some (nex2, g2) →
      run p (CGoal.next Sure.bunt nex2.th) g2 = some (nex1, g3) → CrCopyOk g3 nex1 nex2.laz

/-- **The cons case of `+run`** on a fork-free goal with no look at `0`, for
pure `p` and `q` with no `%6`: the `=>` for `%done`, then `crcPick` for
`%pick` and `+split` with `crcNTail` for `%next`.  The needs that `+split`
returns have no look at `0` (`crc_split_lok`, no hypothesis); the `+copy`
meets `CrCopyOk` at the states the model reaches (`CrcCopy`). -/
theorem comp_run_cons (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (p q : Nomm) (hpp : p.pure = true) (hqp : q.pure = true) (hp6 : noSix p = true)
    (hq6 : noSix q = true) (gl : CGoal CSet) (region : List Nat) (g : Gen (TreapMap mugF))
    (hlok : crLokOk gl)
    (hp : ∀ s th g1, (∀ y ∈ HoonSet.toList s.lok, y ≠ 0) → CompRunAt ctx p (CGoal.toL (CGoal.next s th)) region g1)
    (hq : ∀ s th g1, (∀ y ∈ HoonSet.toList s.lok, y ≠ 0) → CompRunAt ctx q (CGoal.toL (CGoal.next s th)) region g1)
    (hcp : CrcCopy p q gl g) :
    CompRunAt ctx (Nomm.cons p q) (CGoal.toL gl) region g := by
  apply cr_at_of_run (by simp [Nomm.pure, hpp, hqp]) (by simp [noSix, hp6, hq6])
  intro x mono sup hx
  obtain ⟨a, b, hab⟩ := crc_nomm_cell p
  have hnn : (Nomm.cons p q).toNoun = C (C a b) q.toNoun := by
    rw [show (Nomm.cons p q).toNoun = C p.toNoun q.toNoun from rfl, hab]
  rw [hnn, cr_disp_cons, ← hnn]
  have hbunt : ∀ y ∈ HoonSet.toList (Sure.bunt : Sure CSet).lok, y ≠ 0 :=
    fun y hy => absurd hy (HoonSet.mem_empty y)
  cases gl with
  | next s th =>
    exact crc_next h7 hcode p q hpp hqp hp6 hq6 region x hx mono sup s th hlok g hp hq hcp
  | done =>
    have hreg : ∀ y ∈ HoonSet.toList (lazyReg (S := CSet) g.re).lok, y ≠ 0 :=
      fun y hy => absurd hy (HoonSet.mem_empty y)
    rw [crc_eq, crc_done_step h7, ← crc_eq, crc_run_done]
    exact crc_next h7 hcode p q hpp hqp hp6 hq6 region x hx mono sup _ _ hreg _ hp hq hcp
  | pick z o =>
    have hpk := crc_pick h7 hcode p q hpp hqp hp6 hq6 region x hx mono (CGoal.toL (CGoal.pick (S := CSet) z o)).toNoun sup g
      (hq _ _ _ hbunt) (fun th g2 => hp _ th g2 hbunt) hcp
    rw [crc_run_pick p q hpp, crc_eq]
    simp only [crSubj, compCore, CGoal.toL, CGoalL.toNoun] at hpk ⊢
    generalize (Nomm.cons p q).toNoun = NN at hpk ⊢
    generalize comp.door = Dr at hpk ⊢
    nock_open crcHead
    simp [nock_exec, CGoal.toL, CGoalL.toNoun, hpk]

end Compiler
end Formalization
