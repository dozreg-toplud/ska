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

/-! ## The invariant through `+copy-lazy` -/

theorem lnb_root_copy {sf ss : Sure CSet} {ned : Need} {ops : List Pole} {g g1 : Gen (TreapMap mugF)}
    (hf : LNB g.re sf) (hs : LNB g.re ss) (e : copyNeed sf.ned ss.ned [] g = some ((ned, ops), g1)) :
    g.re ≤ g1.re ∧ LNB g1.re ⟨ned, HoonSet.uni sf.lok ss.lok⟩ := by
  obtain ⟨A0, -, c1⟩ := copyNeed_spec (Map := TreapMap mugF) _ _ _ _ _ _ e
  refine ⟨c1.le, fun y hy => ?_, fun r hr => ?_⟩
  · rcases (HoonSet.mem_uni sf.lok ss.lok y).1 hy with h | h
    · exact hf.1 y h
    · exact hs.1 y h
  · rcases c1.mem r hr with (h | h) | h
    · have := hf.2 r h; have := c1.le; omega
    · have := hs.2 r h; have := c1.le; omega
    · exact h.2

theorem walkPF_append {P : Nat → Sure CSet → Prop} : ∀ (a b : List (Lazy.ForkE CSet)),
    WalkPF P a → WalkPF P b → WalkPF P (a ++ b)
  | [], b, _, hb => hb
  | ((oy, y), (on, n)) :: rest, b, ⟨hy, hn, hr⟩, hb => ⟨hy, hn, walkPF_append rest b hr hb⟩

theorem walkPB_append {P : Nat → Sure CSet → Prop} : ∀ (a b : List (Nat × Lazy CSet)),
    WalkPB P a → WalkPB P b → WalkPB P (a ++ b)
  | [], b, _, hb => hb
  | (ob, l) :: rest, b, ⟨hl, hr⟩, hb => ⟨hl, walkPB_append rest b hr hb⟩

theorem lall_of_walkP {Q : Sure CSet → Prop} {o : Nat} {l : Lazy CSet} (h : WalkP (fun _ s => Q s) o l) :
    LAll Q l := Eq.mp (walkP_irrel Q o 0 l) h

theorem walkP_of_lall {Q : Sure CSet → Prop} (o : Nat) {l : Lazy CSet} (h : LAll Q l) :
    WalkP (fun _ s => Q s) o l := Eq.mpr (walkP_irrel Q o 0 l) h

mutual
/-- **`+copy-lazy` keeps the looks and the registers below the counter** on
every pair of lazy needs (the merge included). -/
theorem copy_lnb : ∀ (f : Lazy CSet) (o : Nat) (s : Lazy CSet) (g g' : Gen (TreapMap mugF)) (r : Lazy CSet),
    LAll (LNB g.re) f → LAll (LNB g.re) s → Lazy.copyLazyL o f s g = some (r, g') → LAll (LNB g'.re) r
  | Lazy.mk sf ff bf, o, Lazy.mk ss fs bs, g, g', r, ⟨hsf, hff, hbf⟩, ⟨hss, hfs, hbs⟩, h => by
    rw [copyLazyL_eq] at h
    obtain ⟨⟨ned, ops⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨l1, hroot⟩ := lnb_root_copy hsf hss e1
    obtain ⟨u, g2, e2, h⟩ := bind_some h
    have r2 := addOps_re e2
    obtain ⟨fk, g3, e3, h⟩ := bind_some h
    obtain ⟨bd, g4, e4, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l3 := forkPart_le e3
    -- the forks
    have hfk : WalkPF (fun _ s => LNB g3.re s) fk := by
      unfold forkPart at e3
      split at e3
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
        obtain ⟨rfl, rfl⟩ := e3; exact walkPF_lnb_mono (by omega) hff
      · split at e3
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
          obtain ⟨rfl, rfl⟩ := e3; exact walkPF_lnb_mono (by omega) hfs
        · obtain ⟨m, g5, e5, e3⟩ := bind_some e3
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
          obtain ⟨rfl, rfl⟩ := e3
          have l5 := mergeForks_le _ _ _ _ _ e5
          have hm := mforks_lnb ff fs g.re g2 g5 m (by omega) (fun v hv => walkPF_mem fs hfs v hv)
            (walkPF_lnb_mono (by omega) hff) e5
          exact walkPF_append _ _ hm (walkPF_filter _ fs (walkPF_lnb_mono (by omega) hfs))
    -- the bonds
    have l4 : g3.re ≤ g4.re ∧ WalkPB (fun _ s => LNB g4.re s) bd := by
      unfold bondPart at e4
      split at e4
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
        obtain ⟨rfl, rfl⟩ := e4; exact ⟨Nat.le_refl _, walkPB_lnb_mono (by omega) hbf⟩
      · split at e4
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
          obtain ⟨rfl, rfl⟩ := e4; exact ⟨Nat.le_refl _, walkPB_lnb_mono (by omega) hbs⟩
        · obtain ⟨m, g5, e5, e4⟩ := bind_some e4
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
          obtain ⟨rfl, rfl⟩ := e4
          have l5 := mergeBonds_le _ _ _ _ _ e5
          have hm := mbonds_lnb bf bs g.re g3 g5 m (by omega) (fun v hv => walkPB_mem bs hbs v hv)
            (walkPB_lnb_mono (by omega) hbf) e5
          exact ⟨l5, walkPB_append _ _ hm (walkPB_filter _ bs (walkPB_lnb_mono (by omega) hbs))⟩
    exact ⟨⟨hroot.1, hroot.2.mono (by omega)⟩, walkPF_lnb_mono l4.1 hfk, l4.2⟩

theorem mforks_lnb : ∀ (ff fs : List (Lazy.ForkE CSet)) (k : Nat) (g g' : Gen (TreapMap mugF))
    (r : List (Lazy.ForkE CSet)), k ≤ g.re →
    (∀ v ∈ fs, LAll (LNB k) v.1.2 ∧ LAll (LNB k) v.2.2) → WalkPF (fun _ s => LNB g.re s) ff →
    Lazy.mergeForks (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) ff g
      = some (r, g') → WalkPF (fun _ s => LNB g'.re s) r
  | [], fs, k, g, g', r, _, _, _, h => by
    simp only [Lazy.mergeForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial
  | ((oy, y), (on, n)) :: rest, fs, k, g, g', r, hk, hfs, ⟨hy, hn, hr⟩, h => by
    simp only [Lazy.mergeForks] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l2 := mergeForks_le _ _ _ _ _ e2
    cases hg : (HoonMap.get (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) oy
        : Option (Lazy.ForkE CSet)) with
    | none =>
      simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨lnb_mono l2 oy hy, lnb_mono l2 on hn, mforks_lnb rest fs k g g2 r' hk hfs hr e2⟩
    | some v =>
      obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := v
      have hv := hfs _ (index_mem' _ _ _ _ hg)
      simp only [hg] at e1
      split at e1
      · obtain ⟨y', g3, e3, e1⟩ := bind_some e1
        obtain ⟨n', g4, e4, e1⟩ := bind_some e1
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        have l3 := copyLazyL_le _ _ _ _ _ _ e3
        have hy' := copy_lnb y oy my g g3 y' (lall_of_walkP hy) (lall_mono (fun _ h => ⟨h.1, h.2.mono hk⟩) hv.1) e3
        have hn' := copy_lnb n on mn g3 g4 n' (lall_of_walkP (lnb_mono l3 on hn))
          (lall_mono (fun _ h => ⟨h.1, h.2.mono (by omega)⟩) hv.2) e4
        have l4 := copyLazyL_le _ _ _ _ _ _ e4
        exact ⟨lnb_mono (by omega) oy (walkP_of_lall oy hy'), lnb_mono l2 on (walkP_of_lall on hn'),
          mforks_lnb rest fs k g4 g2 r' (by omega) hfs (walkPF_lnb_mono (by omega) hr) e2⟩
      · cases e1

theorem mbonds_lnb : ∀ (bf bs : List (Nat × Lazy CSet)) (k : Nat) (g g' : Gen (TreapMap mugF))
    (r : List (Nat × Lazy CSet)), k ≤ g.re →
    (∀ v ∈ bs, LAll (LNB k) v.2) → WalkPB (fun _ s => LNB g.re s) bf →
    Lazy.mergeBonds (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) bf g
      = some (r, g') → WalkPB (fun _ s => LNB g'.re s) r
  | [], bs, k, g, g', r, _, _, _, h => by
    simp only [Lazy.mergeBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial
  | (ob, l) :: rest, bs, k, g, g', r, hk, hbs, ⟨hl, hr⟩, h => by
    simp only [Lazy.mergeBonds] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l2 := mergeBonds_le _ _ _ _ _ e2
    cases hg : (HoonMap.get (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) ob
        : Option (Nat × Lazy CSet)) with
    | none =>
      simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨lnb_mono l2 ob hl, mbonds_lnb rest bs k g g2 r' hk hbs hr e2⟩
    | some v =>
      obtain ⟨ob', m⟩ := v
      have hv := hbs _ (index_mem' _ _ _ _ hg)
      simp only [hg] at e1
      obtain ⟨l', g3, e3, e1⟩ := bind_some e1
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      have l3 := copyLazyL_le _ _ _ _ _ _ e3
      have hl' := copy_lnb l ob m g g3 l' (lall_of_walkP hl) (lall_mono (fun _ h => ⟨h.1, h.2.mono hk⟩) hv) e3
      exact ⟨lnb_mono l2 ob (walkP_of_lall ob hl'),
        mbonds_lnb rest bs k g3 g2 r' (by omega) hbs (walkPB_lnb_mono l3 hr) e2⟩
end

/-- **`+copy` keeps the invariant's lazy part**: the result of `+copy` of a
goal's need and a lazy need, both with their looks and registers below the
counter, has its looks and registers below the counter it returns. -/
theorem crInvL_copy {g g' : Gen (TreapMap mugF)} {first : NextL CSet} {second : Lazy CSet} {nex : NextL CSet}
    (hf : LAll (LNB g.re) first.laz) (hs : LAll (LNB g.re) second) (h : copyL first second g = some (nex, g')) :
    g.re ≤ g'.re ∧ LAll (LNB g'.re) nex.laz := by
  simp only [copyL] at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  rw [cf_emit_g] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨laz, g2, e2, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hre := cf_emitG_re ⟨[], [], Termin.hop first.th⟩ g
  have l2 := copyLazyL_le _ _ _ _ _ _ e2
  refine ⟨by omega, copy_lnb first.laz g.bo second _ _ laz ?_ ?_ e2⟩
  · rw [hre]; exact hf
  · rw [hre]; exact hs

end Compiler
end Formalization
