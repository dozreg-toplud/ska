import lemmas.Ska.RawInvCLRunLD
import lemmas.Ska.RawInvCLSARunD
import lemmas.Glue.GuardCalls

/-!
# The liveness of the direct call (`callDM`, `runLCM env true` on `PlainD`)

README Gaps 14 (b), track D (fork `kdm`).  The arm `hDM` of
`liveRunM_plainD_of` (`RawInvCLRunLD.lean`): `LRL` of `[2 p q]` with a
direct call, from `LRL` of `p` and `q`.

* `kdm_il_bunt`: the goal "nothing at `th`" from any `IL` goal at `th`.
* `kdm_lrl_fol`: the first run of the chain (`kdlFol`: `q`, or nothing when
  `safeFolFol`), from the goal "nothing at `j`".
* `kdm_tailR`: the chain `q`, `+past`, `p` for "`rp` at the continuation",
  `+copy` (the `monoBlocks` path; `kdl_five_tailL` with `kdlFol` from `bunt`);
  `kdm_tailB`: the same with `p` for "nothing" (the drop path).
* `KdmMonoSpec`: what `+need-ord-alloc-regs` and the call blocks
  (`monoBlocks`, `+mono-try-call`) leave, the `OPh` of the direct call: the
  goal "nothing at the entry block" holds `IL`, a register other than
  `sub-pes` live there is one the outer goal may leave live, `sub-pes` is
  below `re`, undefined and no key.
* `kdm_dmPath`, **`kdm_liveRun_callDM_of`**: the arm, from `KdmMonoSpec`
  (the drop path needs nothing: `lazK_none`).
* **`liveRunM_plainD_ofM`**: the liveness of every run on `PlainD` from
  `KdmMonoSpec` alone.
* `kdm_topU`, `kdm_final`, `optIn_finishLUCM_ofD`, `readsIn_finishLUCM_ofD`:
  the top run with its `+kerf` on `PlainD` (`topSAU_plainD` of
  `RawInvCLSARunD.lean` for single assignment), and the two whole-subject
  leaves of track G on `PlainDM := liftMC PlainD`:
  **`Glue.optInMono_plainD_of`**, **`Glue.readsInMono_plainD_of`**, each from
  `KdmMonoSpec` alone.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Small steps -/

/-- **The goal "nothing at `th`"** from any `IL` goal at `th`. -/
theorem kdm_il_bunt {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g : Comp.Gen Map}
    (hI : IL K (CGoalL.next laz th) g) : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) th) g := by
  have hF := (hI.goal : GoalL g (CGoalL.next laz th)).1
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, hF, ?_, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    exact ⟨k1, k2, fun hg => lReg_bunt (gregL_next.mp hg), k4, k5⟩
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hF
    exact ⟨⟨b, hb, hp⟩, trivial, fun y hy => (show NMem Need.none y from hy).elim⟩

/-- **The first run of the chain** from the goal "nothing at `j`". -/
theorem kdm_lrl_fol (env : CallEnv) (sup : Option Nomm) {q : Nomm} (ihq : kdlLRLM S Map env sup q)
    {K : Nat → Nat → Prop} {j : Jmp} {region : List Nat} {g3 g4 : Comp.Gen Map} {nq : NextL S}
    (hI : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3)
    (h : kdlFol q (runLCM (S := S) (Map := Map) env true sup q) (CGoalL.next (ofSure Sure.bunt) j) region g3 =
      some (nq, g4)) :
    JL K nq g4 ∧ LiveC K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3 g4 nq := by
  simp only [kdlFol] at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, liveC_refl⟩
  · exact ihq K _ region g3 g4 nq hI (lg_ofSure _ _ _) h

/-- A frame for the goal "nothing" is a frame for any goal. -/
theorem kdm_frX_bunt {th : Jmp} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (h : FrX (CGoalL.next (ofSure (Sure.bunt : Sure S)) th) g0 g1 nex) : FrX goal g0 g1 nex := by
  obtain ⟨⟨a, b, c⟩, d⟩ := h
  refine ⟨⟨a, b, fun y hy => ?_⟩, fun y hy => ?_⟩
  · rcases c y hy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (gregL_next.mp h) lReg_bunt
  · rcases d y hy with h | h
    · exact absurd (gregL_next.mp h) lReg_bunt
    · exact Or.inr h

/-! ## The chain -/

/-- **The chain of the `monoBlocks` path**: `kdlFol` from "nothing at `j`",
`+past`, `p` for "`rp` at the continuation", `+copy`. -/
theorem kdm_tailR (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {rp : Nat} {j : Jmp} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3)
    (hrp : rp < g3.re) (hdp : ¬ Defd g3.blocks rp) (hkp : HoonMap.get g3.cond rp = Option.none)
    (h1 : kdlFol q (runLCM (S := S) (Map := Map) env true sup q) (CGoalL.next (ofSure Sure.bunt) j) region g3 =
      some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLCM env true sup p (CGoalL.next (ofSure (lazyReg (S := S) rp)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      r ≠ rp ∧ GLiveKL (unpM g3) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) r := by
  obtain ⟨Jq, Lq⟩ := kdm_lrl_fol env sup ihq hI h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := kdl_frame_fol q (frameRunM_plainD env q hq sup) _ region g3 g4 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (kdl_hrl_fol q (labRunM_plainD (S := S) (Map := Map) env q hq sup)
    (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hrs : ∀ y, LReg second y → y ≠ rp := by
    intro y hy e
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact lReg_bunt (gregL_next.mp h)
    · omega
  have FL : FrL (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3 g5 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) g5 :=
    il_lazyReg_after (il_addKills Ip) FL hrp hdp hkp (fun hg => lReg_bunt (gregL_next.mp hg)) Ip.goal.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := frameRunM_plainD env p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRunM_plainD (S := S) (Map := Map) env p hp sup
    (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glue Ip Jp (fun x y h => Or.inl h) Fp KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact hrs y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_ofSure.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure (lazyReg (S := S) rp)) x y) s2 r := Lp r (Lc r hl)
  have hne' : r ≠ rp := fun e => h5.nk (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩))
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact ⟨hne', Lq r (Lpast r h5')⟩

/-- **The chain of the drop path**: `kdlFol` from "nothing at `j`",
`+past`, `p` for "nothing at the continuation", `+copy`. -/
theorem kdm_tailB (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {j : Jmp} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3)
    (h1 : kdlFol q (runLCM (S := S) (Map := Map) env true sup q) (CGoalL.next (ofSure Sure.bunt) j) region g3 =
      some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLCM env true sup p (CGoalL.next (ofSure (Sure.bunt : Sure S)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      GLiveKL (unpM g3) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) r := by
  obtain ⟨Jq, Lq⟩ := kdm_lrl_fol env sup ihq hI h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (kdl_hrl_fol q (labRunM_plainD (S := S) (Map := Map) env q hq sup)
    (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hsl : ∀ y, LReg second y → y < g5.re := by
    intro y hy
    rcases hy with hy | ⟨e, he, hy⟩
    · exact (((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 _ List.mem_cons_self).2.2 y hy).1
    · exact (((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e
        (List.mem_cons_of_mem _ he)).2.2 y hy).1
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure (Sure.bunt : Sure S)) (⟨[], s2⟩ : Jmp)) g5 := kdm_il_bunt (il_addKills Ip)
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := frameRunM_plainD env p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRunM_plainD (S := S) (Map := Map) env p hp sup
    (CGoalL.next (ofSure (Sure.bunt : Sure S)) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have hrs : ∀ y, LReg second y → y ≠ g5.re := fun y hy e => by have := hsl y hy; omega
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glue (rp := g5.re) Ip Jp (fun x y h => Or.inl h) (kdm_frX_bunt Fp) KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact lReg_bunt (gregL_next.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure (Sure.bunt : Sure S)) x y) s2 r := Lp r (Lc r hl)
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact Lq r (Lpast r h5')

/-! ## The call blocks -/

/-- **What `+need-ord-alloc-regs` and the call blocks leave** (the `OPh`
of the direct call): the goal "nothing at the entry block `x.2`" holds
`IL`; a register other than `sub-pes` (`x.1`) live there is one the outer
goal may leave live; `sub-pes` is below `re`, undefined and no key. -/
def KdmMonoSpec (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (goal : CGoalL S) (bNed : NeedOrd) (b : Bell) (g0 g1 g2 : Comp.Gen Map)
    (subNed : Need) (x : Nat × Nat),
    IL K goal g0 → needOrdAllocRegs bNed g0 = some (subNed, g1) → monoBlocks b subNed goal g1 = some (x, g2) →
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 x.2)) g2 ∧
    (∀ r, r ≠ x.1 → GLiveKL (unpM g2) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 x.2)) r →
      GLiveKL (unpM g0) K goal r) ∧
    x.1 < g2.re ∧ ¬ Defd g2.blocks x.1 ∧ HoonMap.get g2.cond x.1 = Option.none

/-- **The `monoBlocks` path of a direct call**, from `KdmMonoSpec`. -/
theorem kdm_dmPath (hM : KdmMonoSpec S Map) (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : PlainD p) (hq : PlainD q) (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q)
    (b : Bell) (bNed : NeedOrd) {K : Nat → Nat → Prop} (goal : CGoalL S) (region : List Nat)
    {g0 g' : Comp.Gen Map} {nex : NextL S} (hI : IL K goal g0)
    (h : (needOrdAllocRegs bNed >>= fun subNed => monoBlocks b subNed goal >>= fun x =>
        (if safeFolFol q = true then pure ⟨ofSure Sure.bunt, jmp0 x.2⟩
          else runLCM env true sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 x.2)) region : CM Map (NextL S))
          >>= fun nexFol =>
        pastL env.cod nexFol p region >>= fun nexFol =>
        runLCM env true sup p (CGoalL.next (ofSure (lazyReg x.1)) nexFol.th) region >>= fun nexSub =>
        copyL nexSub nexFol.laz : CM Map (NextL S)) g0 = some (nex, g')) :
    JL K nex g' ∧ LiveC K goal g0 g' nex := by
  obtain ⟨subNed, ga, h1, h⟩ := bind_some h
  obtain ⟨⟨sp, cb⟩, gb, h2, h⟩ := bind_some h
  obtain ⟨O1, O2, O3, O4, O5⟩ := hM K goal bNed b g0 ga gb subNed (sp, cb) hI h1 h2
  obtain ⟨nq, gc, h3, h⟩ := bind_some h
  obtain ⟨nq', gd, h4, h⟩ := bind_some h
  obtain ⟨np, ge, h5, h6⟩ := bind_some h
  have h3' : kdlFol q (runLCM (S := S) (Map := Map) env true sup q) (CGoalL.next (ofSure Sure.bunt) (jmp0 cb))
      region gb = some (nq, gc) := h3
  obtain ⟨J, L⟩ := kdm_tailR (rp := sp) env sup hp hq ihp ihq O1 O3 O4 O5 h3' h4 h5 h6
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  exact O2 r hr hg

/-! ## The arm -/

/-- **The liveness arm of the direct call** (`hDM` of `liveRunM_plainD_of`),
from `KdmMonoSpec`: the drop path with no hypothesis, the `monoBlocks` path
from the spec of the call blocks. -/
theorem kdm_liveRun_callDM_of (hM : KdmMonoSpec S Map) (env : CallEnv) :
    ∀ sup p q b key, PlainD p → PlainD q → kdlLRLM S Map env sup p → kdlLRLM S Map env sup q →
      kdlLRLM S Map env sup (Nomm.n2 p q (some (b, key))) := by
  intro sup p q b key hp hq ihp ihq K goal region g0 g1 nex hI hG h
  simp only [runLCM, callLM] at h
  cases goal with
  | next laz th =>
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [callDM, hd, if_true] at h
      obtain ⟨nq, ga, h1, h⟩ := bind_some h
      obtain ⟨nq', gb, h2, h⟩ := bind_some h
      obtain ⟨np, gc, h3, h4⟩ := bind_some h
      have h1' : kdlFol q (runLCM (S := S) (Map := Map) env true sup q) (CGoalL.next (ofSure Sure.bunt) th) region g0 =
          some (nq, ga) := h1
      have hn : noneEquivalentL laz = true := ((Bool.and_eq_true _ _).mp hd).2
      obtain ⟨J, L⟩ := kdm_tailB env sup hp hq ihp ihq (kdm_il_bunt hI) h1' h2 h3 h4
      refine ⟨J, fun r hl => ?_⟩
      exact (L r hl).mono fun x y hxy => hxy.elim Or.inl fun hz => absurd hz (lazK_none hn)
    · simp only [callDM, hd, Bool.false_eq_true, if_false] at h
      cases key with
      | some k => simp only at h <;> cases h
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr] at h <;> cases h
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn] at h <;> cases h
          | some bNed =>
            simp only [hr, hn] at h
            exact kdm_dmPath hM env sup hp hq ihp ihq b bNed _ region hI h
  | pick z o =>
    simp only [callDM] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          exact kdm_dmPath hM env sup hp hq ihp ihq b bNed _ region hI h
  | done =>
    simp only [callDM] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          exact kdm_dmPath hM env sup hp hq ihp ihq b bNed _ region hI h

/-- **The liveness of every run on `PlainD`** (direct calls included), from
the spec of the call blocks alone. -/
theorem liveRunM_plainD_ofM (hM : KdmMonoSpec S Map) (env : CallEnv) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kdlLRLM S Map env sup nm :=
  liveRunM_plainD_of env (kdm_liveRun_callDM_of hM env)

/-! ## The top run and the leaves -/

/-- **The top run on `PlainD` and its `+kerf`** (`topU_of` for `runLCM`). -/
theorem kdm_topU (hM : KdmMonoSpec S Map) (env : CallEnv) {nm : Nomm} (hp : PlainD nm)
    {nex : NextL S} {g1 g2 : Comp.Gen Map} {o sub : Nat}
    (h1 : runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1))
    (h2 : (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2)) : TopU (S := S) g2 o sub := by
  obtain ⟨J1, L1⟩ := liveRunM_plainD_ofM hM env nm hp Option.none _ _ _ _ _ _ il_gen0 trivial h1
  obtain ⟨I2, L2⟩ := kerfSpecL (fun _ _ => False) nex g1 g2 o sub J1 h2
  refine ⟨I2, fun r hl => ?_⟩
  apply Classical.byContradiction
  intro hr
  have hk : LiveK (unpM g2) (fun x y => (fun _ _ => False) x y ∨ lazK (jmp0 o).there (ofSure (lazyReg (S := S) sub)) x y)
      (jmp0 o).there r := by
    refine tu_liveK hl fun x hx => ?_
    rcases hx with hx | ⟨e, he, -, hm⟩
    · exact hx
    · simp only [ofSure, entries, List.mem_cons] at he
      rcases he with rfl | he
      · exact hr hm
      · simp [bondEntries, forkEntries] at he
  exact L1 r (L2 r hk)

theorem kdm_final {env : CallEnv} {nm : Nomm} {c : Straight Map}
    (h : finishLUCM (S := S) (Map := Map) env nm = some c) :
    ∃ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
      runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) ∧
      (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2) ∧
      toStraightF g2.cond g2.blocks (Need.this sub) o = some c := by
  unfold finishLUCM at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨nex, g1, g2, o, sub, h1, h2, h⟩

variable [MapKeys Map]

/-- **`OptIn` of the whole-subject code with direct calls on `PlainD`.** -/
theorem optIn_finishLUCM_ofD (hM : KdmMonoSpec S Map) {env : CallEnv} {nm : Nomm} (hp : PlainD nm)
    {c : Straight Map} (h : finishLUCM (S := S) (Map := Map) env nm = some c) : OptIn c.blocks := by
  obtain ⟨nex, g1, g2, o, sub, h1, h2, h3⟩ := kdm_final h
  exact (tu_out (kdm_topU hM env hp h1 h2) (topSAU_plainD hp nex g1 g2 o sub h1 h2) h3).1

/-- **`ReadsIn` of the whole-subject code with direct calls on `PlainD`.** -/
theorem readsIn_finishLUCM_ofD (hM : KdmMonoSpec S Map) {env : CallEnv} {nm : Nomm} (hp : PlainD nm)
    {c : Straight Map} (h : finishLUCM (S := S) (Map := Map) env nm = some c) :
    Compiler.ReadsIn c.nargs c.blocks := by
  obtain ⟨nex, g1, g2, o, sub, h1, h2, h3⟩ := kdm_final h
  exact (tu_out (kdm_topU hM env hp h1 h2) (topSAU_plainD hp nex g1 g2 o sub h1 h2) h3).2

end Raw

namespace Glue

open Nock Opt Comp Raw

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map] [Opt.MapKeys Map]
variable {S : Type} [Comp.HoonSet S]

/-- **The whole-subject class with direct and indirect calls and no `%6`**:
`PlainD`. -/
def PlainDM : MonoClass := liftMC Raw.PlainD

/-- **Leaf `OptInMono` on `PlainDM`**, from the spec of the call blocks. -/
theorem optInMono_plainD_of (hM : Raw.KdmMonoSpec S Map) : OptInMono S Map PlainDM := by
  intro env N bl nm s hf hs
  exact optIn_finishLUCM_ofD hM hf hs

/-- **Leaf `ReadsInMono` on `PlainDM`**, from the spec of the call blocks. -/
theorem readsInMono_plainD_of (hM : Raw.KdmMonoSpec S Map) : ReadsInMono S Map PlainDM := by
  intro env N bl nm s hf hs
  exact readsIn_finishLUCM_ofD hM hf hs

end Glue
end SkaModel
end Formalization
