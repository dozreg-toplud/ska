import lemmas.Compiler.CompCopyMerge

/-!
# `+copy-lazy` and `+copy` on every pair of lazy needs

`comp_copy_lazy_all`: `+copy-lazy` is `copyLazyL` on every pair of lazy needs
(forks and bonds to any depth, merged where they name the same block) whose
registers are all below the counter and apart (`CopyH`), by a mutual
induction over `first` (`copy_all`, with the spin gates `copy_fgates`,
`copy_bgates`): the merge copies a fork's or bond's need of `first` into
the need of `second` under the same block, which `CopyH` covers as parts of
the two.  `comp_copy_all`: `+copy`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The model's `copyLazyL` with its fork and bond parts named. -/
theorem copyLazyL_eq (o : Nat) (sf ss : Sure CSet) (ff fs : List (Lazy.ForkE CSet))
    (bf bs : List (Nat × Lazy CSet)) :
    Lazy.copyLazyL o (Lazy.mk sf ff bf) (Lazy.mk ss fs bs) = (do
      let (ned, ops) ← copyNeed sf.ned ss.ned []
      addOps o ops
      let fork ← forkPart ff fs
      let bond ← bondPart bf bs
      pure (Lazy.mk ⟨ned, HoonSet.uni sf.lok ss.lok⟩ fork bond) : CM (TreapMap mugF) (Lazy CSet)) := by
  rfl

theorem forkPart_le {ff fs : List (Lazy.ForkE CSet)} {g g' : Gen (TreapMap mugF)} {r : List (Lazy.ForkE CSet)}
    (h : forkPart ff fs g = some (r, g')) : g.re ≤ g'.re := by
  unfold forkPart at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
  · split at h
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
    · obtain ⟨m, g1, e1, h⟩ := bind_some h
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact mergeForks_le _ _ _ _ _ e1

theorem h15_of (h7 : slot? 7 ctx = some compK) : slot? 15 ctx = some compTypes := by
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have := slot_spine (by omega) (by omega) h1 1
  simp only [show 2 ^ 1 * (7 + 1) - 1 = 15 from rfl, show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  rw [this]; rfl

section
variable (h7 : slot? 7 ctx = some compK) (x : GenRest)
include h7

mutual
theorem copy_all : ∀ (f : Lazy CSet) (o : Nat) (s : Lazy CSet) (g : Gen (TreapMap mugF)), CopyH g.re f s →
    nock (C clBat (C (C (A o) (C f.toNoun s.toNoun)) (compCore g x ctx))) clBat
      = (Lazy.copyLazyL o f s g).map (clEnc x)
  | Lazy.mk sf ff bf, o, Lazy.mk ss fs bs, g, hH => by
    obtain ⟨hc, hl, -⟩ := comp_ctx_pill ctx h7
    have h15 := h15_of h7
    obtain ⟨hlt, hrt, hme⟩ := copyH_root hH
    simp only [Lazy.sure_mk] at hlt hrt hme
    obtain ⟨n, ops, g1, e, _, _⟩ := cnm_seg (x := x) (B := cnmBat) (S := C (A 0) (A 0)) hl sf.ned ss.ned
      [] [] [] g hlt hrt hme
    have hcn := comp_copy_need (x := x) hl g sf.ned ss.ned hlt hrt hme
    rw [e] at hcn
    have hr1 : g.re ≤ g1.re := by
      obtain ⟨A0, -, c1⟩ := copyNeed_spec (Map := TreapMap mugF) _ _ _ _ _ _ e
      exact c1.le
    have hao := comp_add_ops x hc g1 o ops
    have huni := cs_uni_is sf.lok ss.lok
    have hD1 := comp_cnm_at
    have hD2 := comp_add_ops_at
    -- the pairs of entries under the same block
    have hPF : ∀ e ∈ ff, ∀ v ∈ fs, CopyH g.re e.1.2 v.1.2 ∧ CopyH g.re e.2.2 v.2.2 := by
      intro e he v hv
      have pf := fun (Q : Sure CSet → Prop) (hQ : LAll Q (Lazy.mk sf ff bf)) => walkPF_mem ff hQ.2.1 e he
      have ps := fun (Q : Sure CSet → Prop) (hQ : LAll Q (Lazy.mk ss fs bs)) => walkPF_mem fs hQ.2.1 v hv
      exact ⟨copyH_part (fun Q hQ => (pf Q hQ).1) (fun Q hQ => (ps Q hQ).1) hH,
        copyH_part (fun Q hQ => (pf Q hQ).2) (fun Q hQ => (ps Q hQ).2) hH⟩
    have hPB : ∀ e ∈ bf, ∀ v ∈ bs, CopyH g.re e.2 v.2 := by
      intro e he v hv
      exact copyH_part (fun Q (hQ : LAll Q (Lazy.mk sf ff bf)) => walkPB_mem bf hQ.2.2 e he)
        (fun Q (hQ : LAll Q (Lazy.mk ss fs bs)) => walkPB_mem bs hQ.2.2 v hv) hH
    rw [copyLazyL_eq, lazy_toNoun_mk, lazy_toNoun_mk]
    simp only [compCore] at hcn hao ⊢
    conv => { lhs; arg 2; rw [cl_bat_eq2]; unfold clBatS2 }
    cases ea : addOps (Map := TreapMap mugF) o ops g1 with
    | none =>
      rw [ea] at hao
      generalize comp.door = Dr at hD1 hD2 hcn hao ⊢
      simp [nock_exec, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao, e, ea, bind,
        StateT.bind]
    | some p =>
      obtain ⟨u, g2⟩ := p
      rw [ea] at hao
      have r2 := addOps_re ea
      have hF := cl_fpart hc h15 x (C n.toNoun (listNoun Pole.toNoun ops)) o sf ss ff fs bf bs g2
        (fun e he g' hle NO' SAMPLE G' => copy_fgates ff fs g.re hPF e he g'
          (by rw [r2] at hle; omega) NO' SAMPLE G')
      simp only [Sure.toNoun] at hF
      cases eF : forkPart ff fs g2 with
      | none =>
        rw [eF] at hF
        generalize comp.door = Dr at hD1 hD2 hcn hao hF ⊢
        simp [nock_exec, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao, e, ea, bind,
          StateT.bind, hF, eF]
      | some q =>
        obtain ⟨fk, g3⟩ := q
        rw [eF] at hF
        have r3 := forkPart_le eF
        have hB := cl_bpart hc h15 x (listN (fk.map forkE)) (C n.toNoun (listNoun Pole.toNoun ops)) o sf ss
          ff fs bf bs g3
          (fun e he g' hle NO' SAMPLE G' FN' => copy_bgates bf bs g.re hPB e he g'
            (by rw [r2] at r3; omega) NO' SAMPLE G' FN')
        simp only [Sure.toNoun] at hB
        cases eB : bondPart bf bs g3 with
        | none =>
          rw [eB] at hB
          generalize comp.door = Dr at hD1 hD2 hcn hao hF hB ⊢
          simp [nock_exec, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao, e, ea, bind,
            StateT.bind, hF, eF, hB, eB]
        | some q2 =>
          obtain ⟨bd, g4⟩ := q2
          rw [eB] at hB
          generalize comp.door = Dr at hD1 hD2 hcn hao hF hB ⊢
          simp [nock_exec, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao, e, ea, bind,
            StateT.bind, hF, eF, hB, eB, hc, in_arm, in.arm_at, in.uni.arm_at, cl_uni_arm, huni, pure,
            StateT.pure, clEnc, lazy_toNoun_mk]

theorem copy_fgates : ∀ (ff fs : List (Lazy.ForkE CSet)) (k0 : Nat),
    (∀ e ∈ ff, ∀ v ∈ fs, CopyH k0 e.1.2 v.1.2 ∧ CopyH k0 e.2.2 v.2.2) →
    ∀ e ∈ ff, ∀ g' : Gen (TreapMap mugF), k0 ≤ g'.re → ∀ (NO' SAMPLE G' : Noun),
      nock (C clSGF (C (C (forkE e) (genNoun g' x))
        (C (HoonMap.toNoun forkE (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs))
          (C NO' (C clBat (C SAMPLE (C comp.door (C G' ctx)))))))) clSGF
      = (mgF (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) e g').map
          fun r => C (forkE r.1) (genNoun r.2 x)
  | [], _, _, _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, fs, k0, hP, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro g' hk NO' SAMPLE G'
      obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
      exact cl_fgate hc x _ NO' SAMPLE G' _ g'
        (fun m g'' hle ⟨v, hv, hmv⟩ => copy_all y oy m g'' (by
          subst hmv
          exact copyH_mono (Nat.le_trans hk hle) (hP _ List.mem_cons_self v (index_mem' _ _ _ _ hv)).1))
        (fun m g'' hle ⟨v, hv, hmv⟩ => copy_all n on m g'' (by
          subst hmv
          exact copyH_mono (Nat.le_trans hk hle) (hP _ List.mem_cons_self v (index_mem' _ _ _ _ hv)).2))
    · exact copy_fgates rest fs k0 (fun e' he'' v hv => hP e' (List.mem_cons_of_mem _ he'') v hv) e he'

theorem copy_bgates : ∀ (bf bs : List (Nat × Lazy CSet)) (k0 : Nat),
    (∀ e ∈ bf, ∀ v ∈ bs, CopyH k0 e.2 v.2) →
    ∀ e ∈ bf, ∀ g' : Gen (TreapMap mugF), k0 ≤ g'.re → ∀ (NO' SAMPLE G' FN' : Noun),
      nock (C clSGB (C (C (bondE e) (genNoun g' x))
        (C (HoonMap.toNoun bondE (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs))
          (C FN' (C NO' (C clBat (C SAMPLE (C comp.door (C G' ctx))))))))) clSGB
      = (mgB (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) e g').map
          fun r => C (bondE r.1) (genNoun r.2 x)
  | [], _, _, _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, bs, k0, hP, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro g' hk NO' SAMPLE G' FN'
      obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
      exact cl_bgate hc x _ FN' NO' SAMPLE G' _ g'
        (fun m g'' hle ⟨v, hv, hmv⟩ => copy_all l ob m g'' (by
          subst hmv
          exact copyH_mono (Nat.le_trans hk hle) (hP _ List.mem_cons_self v (index_mem' _ _ _ _ hv))))
    · exact copy_bgates rest bs k0 (fun e' he'' v hv => hP e' (List.mem_cons_of_mem _ he'') v hv) e he'
end

end

/-- **`+copy-lazy` on every pair of lazy needs** (forks and bonds to any
depth, the entries of the two under the same block merged), in the pill's
context (`K` at axis `7`), where every register of both is below the counter
and none is in both (`CopyH`). -/
theorem comp_copy_lazy_all (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (o : Nat) (f s : Lazy CSet) (hH : CopyH g.re f s) :
    nock (C clBat (C (C (A o) (C f.toNoun s.toNoun)) (compCore g x ctx))) clBat
      = (Lazy.copyLazyL o f s g).map fun p => C p.1.toNoun (genNoun p.2 x) :=
  copy_all h7 x f o s g hH

/-- **`+copy` on every pair of lazy needs**: `+emit` of `[~ ~ %hop
then.first]`, then `+copy-lazy` into the new block. -/
theorem comp_copy_all (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (first : NextL CSet) (second : Lazy CSet) (hH : CopyH g.re first.laz second) :
    nock (C cpBat (C (C first.goal.toNoun second.toNoun) (compCore g x ctx))) cpBat
      = (copyL first second g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨laz, th⟩ := first
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Jmp.toNoun] at he
  have hre := cf_emitG_re ⟨[], [], Termin.hop th⟩ g
  have hcl := comp_copy_lazy_all h7 x (cfEmitG ⟨[], [], Termin.hop th⟩ g) g.bo laz second
    (by rw [hre]; exact hH)
  have hD1 := comp_cp_at
  have hD2 := comp_emit_at
  have hD3 := comp_cl_at
  simp only [compCore] at hcl ⊢
  unfold cpBat
  generalize comp.door = Dr at hD1 hD2 hD3 he hcl ⊢
  cases ec : Lazy.copyLazyL (Map := TreapMap mugF) g.bo laz second (cfEmitG ⟨[], [], Termin.hop th⟩ g) with
  | none =>
    rw [ec] at hcl
    simp [nock_exec, NextL.goal, CGoalL.toNoun, hD2, hD3, comp_emit_arm, he, comp_cl_arm, hcl, copyL,
      cf_emit_g, ec, bind, StateT.bind, Jmp.toNoun]
  | some p =>
    obtain ⟨l2, g2⟩ := p
    rw [ec] at hcl
    simp [nock_exec, NextL.goal, CGoalL.toNoun, hD2, hD3, comp_emit_arm, he, comp_cl_arm, hcl, copyL,
      cf_emit_g, ec, bind, StateT.bind, pure, StateT.pure, Jmp.toNoun, jmp0, listNoun]

end Compiler
end Formalization
