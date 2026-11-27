import lemmas.Ska.RawInvCLIJ

/-!
# The run-level liveness with calls: both halves of the arms

README Gaps 14 (b), track D.  Each arm of `runLC` on `PlainN` as ONE lemma
`LiveRun IL JL (runLC env sup nm)`: the postcondition `JL` (the
precondition `IL` of a run for the result) and the liveness spec `LiveC`.

* `il_emitGoal`: a fresh block emitted after fresh registers, with a goal
  `ofSure s` at it whose need is fresh: `IL` of the new goal.
* `il_fromL`: `+from` keeps `IL` (`fromEnt_back`, `needsApart_fromEnt`).
* `RInv C g`: every block's registers below `re`, no key of `C` defined;
  `walkList_inv`, `walkLazy_inv` (any walk whose gate keeps a state
  invariant keeps it), `rinv_addOps`, `medeLoop_rinv`, `medeGate_rinv`.
* **`liveRun_n0`**, **`liveRun_n1`**: the cases `%0` and `%1`, both halves;
  **`liveRun_n7`**: `%7` from its parts.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Small facts -/

/-- A defined register of blocks below `R` is below `R`. -/
theorem defd_lt {bl : Map Blob} {R : Nat} (h : ∀ k b, HoonMap.get bl k = some b → BlobIn (· < R) b) {r : Nat}
    (hd : Defd bl r) : r < R := by
  obtain ⟨o, b, hb, hm⟩ := defd_iff.mp hd
  have hB := h o b hb
  rcases mem_blockDefs.mp hm with hm | hm
  · exact hB.1 r hm
  · obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hm
    exact hB.2.1 op hop r (dst_mem_regs hd)

theorem gregL_ofSure {s : Sure S} {j : Jmp} {r : Nat} : GRegL (CGoalL.next (ofSure s) j) r ↔ NMem s.ned r := by
  simp only [GRegL, entries_ofSure, List.mem_singleton, exists_eq_left]
  rfl

theorem ATS.free {g : Comp.Gen Map} (h : ATS g) : HoonMap.get g.blocks g.bo = Option.none := by
  cases e : HoonMap.get g.blocks g.bo with
  | none => rfl
  | some b => exact absurd (h.2.2 _ b e).1 (Nat.lt_irrefl _)

theorem blobIn_nil_fin {P : Nat → Prop} {fin : Termin} (h : FinIn P fin) : BlobIn P ⟨[], [], fin⟩ :=
  ⟨fun x hx => absurd hx List.not_mem_nil, RegsIn.nil _, h⟩

theorem jmpIn_nil {P : Nat → Prop} {j : Jmp} (h : j.args = []) : JmpIn P j := fun x hx => by
  rw [h] at hx; exact absurd hx List.not_mem_nil

/-! ## A fresh block with a fresh goal at it -/

/-- **A block emitted after fresh registers, with a goal `ofSure s` at it**
whose need's registers are fresh and not defined by the block. -/
theorem il_emitGoal {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {R : Nat}
    (hR : g.re ≤ R) {b : Blob} {s : Sure S} (hp : b.par = []) (hbat : BATC g.blocks b) (hin : BlobIn (· < R) b)
    (hdef : ∀ r ∈ blockDefs b, g.re ≤ r) (hs : ∀ r, NMem s.ned r → g.re ≤ r ∧ r < R ∧ r ∉ blockDefs b)
    (hds : Distinct s.ned) :
    IL K (CGoalL.next (ofSure s) (jmp0 g.bo)) (({ g with re := R } : Comp.Gen Map).emitted b) := by
  have hd : g.drop = false := hI.ats.1
  have A : ATS ({ g with re := R } : Comp.Gen Map) := hI.ats
  obtain ⟨A1, -, hget⟩ := ats_emit A hbat
  have hfree : HoonMap.get g.blocks g.bo = Option.none := hI.ats.free
  have hD : ∀ r, Defd (({ g with re := R } : Comp.Gen Map).emitted b).blocks r ↔ Defd g.blocks r ∨ r ∈ blockDefs b :=
    fun r => by
      show Defd (if g.drop then g.blocks else HoonMap.put g.blocks g.bo b) r ↔ _
      simp only [hd, Bool.false_eq_true, if_false]
      exact defd_put hfree
  refine ⟨A1, fun k b' hb' => ?_, fun k v hk => ?_, hI.kvan.mono (Nat.le_succ _), ?_⟩
  · rw [em_get (g := ({ g with re := R } : Comp.Gen Map)) hd] at hb'
    split at hb'
    · cases hb'; exact hin
    · exact (hI.regs k b' hb').mono fun x hx => Nat.lt_of_lt_of_le hx hR
  · obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v hk
    refine ⟨Nat.lt_of_lt_of_le k1 hR, fun hdk => ?_, fun hg => ?_, Nat.lt_of_lt_of_le k4 hR, k5⟩
    · rcases (hD k).mp hdk with h | h
      · exact k2 h
      · have := hdef k h; omega
    · have := (hs k (gregL_ofSure.mp hg)).1; omega
  · refine ⟨⟨b, hget, hp, rfl⟩, ?_, fun e he => ?_⟩
    · rw [entries_ofSure]; exact List.pairwise_singleton _ _
    · rw [entries_ofSure, List.mem_singleton] at he
      subst he
      refine ⟨⟨b, hget, hp⟩, hds, fun r hr => ⟨(hs r hr).2.1, fun hdr => ?_⟩⟩
      rcases (hD r).mp hdr with h | h
      · have := defd_lt hI.regs h; have := (hs r hr).1; omega
      · exact (hs r hr).2.2 h

/-- **A goal jump of the state, with nothing asked at it.** -/
theorem il_bunt {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {j : Jmp}
    (hj : Fresh g j) : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g := by
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, hj, ?_, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    exact ⟨k1, k2, fun hg => (gregL_ofSure.mp hg).elim, k4, k5⟩
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hj
    exact ⟨⟨b, hb, hp⟩, trivial, fun r hr => hr.elim⟩

/-! ## `+from` -/

theorem fromSure_nmem_back {axe : Nat} {s s' : Sure S} (h : fromSure axe s = some s') {r : Nat}
    (hr : NMem s'.ned r) : NMem s.ned r := by
  unfold fromSure at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · cases h; exact hr.elim
  · cases h; exact nmem_fromPath _ axe r hr

theorem fromEnt_back {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) {e' : Nat × Lazy S}
    (he : e' ∈ b) : ∃ e ∈ a, e.1 = e'.1 ∧ (∀ r, NMem e'.2.sure.ned r → NMem e.2.sure.ned r) ∧
      (Distinct e.2.sure.ned → Distinct e'.2.sure.ned) := by
  obtain ⟨l, h1, h2⟩ := h.mem_right he
  exact ⟨(e'.1, l), h2, rfl, fun r hr => fromSure_nmem_back (fromL_sure h1) hr,
    fun hd => fromSure_dist (fromL_sure h1) hd⟩

/-- **`+from` keeps the precondition.** -/
theorem il_fromL {K : Nat → Nat → Prop} {laz laz' : Lazy S} {th : Jmp} {g : Comp.Gen Map} {axe : Nat}
    (hI : IL K (CGoalL.next laz th) g) (hf : fromL axe laz = some laz') : IL K (CGoalL.next laz' th) g := by
  have FE : FromEnt axe ((th.there, laz) :: entries laz) ((th.there, laz') :: entries laz') :=
    FromEnt.cons hf (fromL_ent axe laz laz' hf)
  obtain ⟨hfr, hap, hent⟩ := (hI.goal : GoalL g (CGoalL.next laz th))
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, hfr, needsApart_fromEnt FE hap, fun e' he' => ?_⟩
  · obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v hk
    refine ⟨k1, k2, fun ⟨e', he', hm⟩ => k3 ?_, k4, k5⟩
    obtain ⟨e, he, -, hn, -⟩ := fromEnt_back FE he'
    exact ⟨e, he, hn k hm⟩
  · obtain ⟨e, he, ee, hn, hdd⟩ := fromEnt_back FE he'
    obtain ⟨hb, hd, hr⟩ := hent e he
    exact ⟨ee ▸ hb, hdd hd, fun r hr' => hr r (hn r hr')⟩

/-! ## `+bomb` and `+simple-next` -/

theorem il_bombL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    {miss : Option Nat} (hI : IL K goal g0) (h : (bombL miss : CM Map (NextL S)) g0 = some (nex, g1)) :
    JL K nex g1 := by
  simp only [bombL] at h
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact il_emitGoal (R := g0.re) hI (Nat.le_refl _) rfl (batc_fresh fun j hj => by simp [finJumps] at hj)
    (blobIn_nil_fin trivial) (fun r hr => by simp [blockDefs] at hr) (fun r hr => hr.elim) trivial

theorem il_simpleNextL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K goal g0) (h : (simpleNextL goal : CM Map (NextL S)) g0 = some (nex, g1)) : JL K nex g1 := by
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hI
  | done =>
    simp only [simpleNextL] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    rw [re_apply] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨o, gb, hb, h⟩ := bind_some h
    rw [emit_apply] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact il_emitGoal (R := g0.re + 1) (s := ⟨Need.this g0.re, HoonSet.empty⟩) hI (Nat.le_succ _) rfl
      (batc_fresh fun j hj => by simp [finJumps] at hj) (blobIn_nil_fin (show g0.re < g0.re + 1 by omega))
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial
  | pick z o =>
    obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
    have az : z.args = [] := by obtain ⟨_, _, _, a⟩ := hz; exact a
    have ao : o.args = [] := by obtain ⟨_, _, _, a⟩ := ho; exact a
    simp only [simpleNextL] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    rw [re_apply] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨o', gb, hb, h⟩ := bind_some h
    rw [emit_apply] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact il_emitGoal (R := g0.re + 1) (b := ⟨[], [], Termin.brn g0.re z o⟩) (s := ⟨Need.this g0.re, HoonSet.empty⟩)
      hI (Nat.le_succ _) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hz
        · exact ho)
      (blobIn_nil_fin ⟨show g0.re < g0.re + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩)
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial

/-! ## `%0` -/

/-- **`%0`, both halves.** -/
theorem liveRun_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) :
    LiveRun (Map := Map) IL JL (runLC (S := S) env sup (Nomm.n0 ax)) := by
  intro K goal region g0 g1 nex hI h
  refine ⟨?_, liveC_n0 env sup hI h⟩
  simp only [runLC] at h
  split at h
  · exact il_bombL hI h
  obtain ⟨nx, ga, ha, h⟩ := bind_some h
  have J := il_simpleNextL hI ha
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact J
  · cases hf : fromL ax nx.laz with
    | none => simp only [hf] at h; cases h
    | some laz' =>
      simp only [hf, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact il_fromL J hf

/-! ## A state invariant of walks -/

/-- Every block's registers below `re`, no key of `C` defined. -/
def RInv (C : Map (Nat × List Nat)) (g : Comp.Gen Map) : Prop :=
  (∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b) ∧
    ∀ y, Defd g.blocks y → HoonMap.get C y = Option.none

/-- **A walk over a list keeps every invariant its gate keeps.** -/
theorem walkList_inv {f : Nat → Sure S → CM Map Unit} {W : Comp.Gen Map → Prop} :
    ∀ (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map),
    (∀ e ∈ es, ∀ a b, W a → f e.1 e.2.sure a = some ((), b) → W b) → W g →
      walkList f es g = some ((), g') → W g'
  | [], g, g', _, h0, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact h0
  | (x, l) :: rest, g, g', hf, h0, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    exact walkList_inv rest g1 g' (fun e he => hf e (List.mem_cons_of_mem _ he))
      (hf (x, l) List.mem_cons_self g g1 h0 h1) h2

/-- **A walk of the lazy tree keeps every invariant its gate keeps** at the
tree's entries. -/
theorem walkLazy_inv {f : Nat → Sure S → CM Map Unit} {W : Comp.Gen Map → Prop} {o : Nat} {l : Lazy S}
    {g g' : Comp.Gen Map} (hf : ∀ e ∈ (o, l) :: entries l, ∀ a b, W a → f e.1 e.2.sure a = some ((), b) → W b)
    (h0 : W g) (h : walkLazy f o l g = some ((), g')) : W g' := by
  have e : (walkLazy f o l : CM Map Unit) = walkList f ((o, l) :: wentries l) := by
    rw [walkLazy_flat]; rfl
  rw [e] at h
  exact walkList_inv _ g g' (fun e he => hf e (((wentries_perm l).cons (o, l)).mem_iff.mp he)) h0 h

theorem rinv_addOps {C : Map (Nat × List Nat)} {o : Nat} {A : List Pole} {g g' : Comp.Gen Map} (hd : g.drop = false)
    (hI : RInv C g) (hA : ∀ p ∈ A, ∀ x ∈ Comp.poleRegs p, x < g.re ∧ HoonMap.get C x = Option.none)
    (h : addOps o A g = some ((), g')) : RInv C g' := by
  obtain ⟨⟨-, -, -, hre, -, -⟩, -, hP⟩ := addOps_step hd h
  refine ⟨fun k b hb => ?_, fun y hy => ?_⟩
  · rw [hP k] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    have B := (hI.1 k b0 h0).mono fun x hx => Nat.lt_of_lt_of_le hx hre
    refine ⟨B.1, ?_, B.2.2⟩
    show RegsIn _ ((if k = o then A else []) ++ b0.body)
    refine RegsIn.append ?_ B.2.1
    split
    · exact fun p hp x hx => Nat.lt_of_lt_of_le (hA p hp x hx).1 hre
    · exact RegsIn.nil _
  · obtain ⟨k, b, hb, hm⟩ := (defd_prep hP).mp hy
    rcases hm with hm | hm
    · exact hI.2 y (defd_iff.mpr ⟨k, b, hb, hm⟩)
    · split at hm
      · obtain ⟨op, hop, hd'⟩ := mem_defsOf.mp hm
        exact (hA op hop y (dst_mem_regs hd')).2
      · simp [defsOf] at hm

theorem RInv.re_up {C : Map (Nat × List Nat)} {g : Comp.Gen Map} (h : RInv C g) {R : Nat} (hR : g.re ≤ R) :
    RInv C ({ g with re := R } : Comp.Gen Map) :=
  ⟨fun k b hb => (h.1 k b hb).mono fun _ hx => Nat.lt_of_lt_of_le hx hR, h.2⟩

/-- **The loop of `+mede` keeps `RInv`**: its ops mention the need's
registers and fresh ones. -/
theorem medeLoop_rinv {C : Map (Nat × List Nat)} {L o : Nat} (hC : ∀ k v, HoonMap.get C k = some v → k < L) :
    ∀ (ned : Need) (som : Noun) (g g' : Comp.Gen Map), g.drop = false → L ≤ g.re → RInv C g →
      (∀ x, NMem ned x → x < g.re ∧ HoonMap.get C x = Option.none) → medeLoop o som ned g = some ((), g') →
      RInv C g'
  | Need.none, som, g, g', _, _, hI, _, h => by
    have e : g' = g := by cases som <;> simp_all [medeLoop, pure_apply]
    subst e; exact hI
  | Need.this r, som, g, g', hd, _, hI, hn, h => by
    unfold medeLoop at h
    refine rinv_addOps hd hI (fun p hp x hx => ?_) h
    rw [List.mem_singleton] at hp; subst hp
    simp only [Comp.poleRegs, List.mem_singleton] at hx; subst hx
    exact hn x rfl
  | Need.pair p q, Noun.atom n, g, g', hd, hL, hI, hn, h => by
    unfold medeLoop at h; exact crash_rinv hC hd hL hI hn h
  | Need.both r p q, Noun.atom n, g, g', hd, hL, hI, hn, h => by
    unfold medeLoop at h; exact crash_rinv hC hd hL hI hn h
  | Need.pair p q, Noun.cell a b, g, g', hd, hL, hI, hn, h => by
    simp only [medeLoop] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    have s1 := (medeLoop_step p a g g1 hd h1).1
    have r1 := medeLoop_rinv hC p a g g1 hd hL hI (fun x hx => hn x (Or.inl hx)) h1
    exact medeLoop_rinv hC q b g1 g' (s1.2.1.trans hd) (Nat.le_trans hL s1.2.2.2.1) r1
      (fun x hx => ⟨Nat.lt_of_lt_of_le (hn x (Or.inr hx)).1 s1.2.2.2.1, (hn x (Or.inr hx)).2⟩) h2
  | Need.both r p q, Noun.cell a b, g, g', hd, hL, hI, hn, h => by
    simp only [medeLoop] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨u', g2, h2, h3⟩ := bind_some h2
    have s1 := (medeS_imm (ned := Need.this r) hd (fun y hy => hy) h1).1
    have r1 := rinv_addOps hd hI (fun p hp x hx => by
      rw [List.mem_singleton] at hp; subst hp
      simp only [Comp.poleRegs, List.mem_singleton] at hx; subst hx
      exact hn x (Or.inl rfl)) h1
    have hd1 : g1.drop = false := s1.2.1.trans hd
    have s2 := (medeLoop_step p a g1 g2 hd1 h2).1
    have r2 := medeLoop_rinv hC p a g1 g2 hd1 (Nat.le_trans hL s1.2.2.2.1) r1
      (fun x hx => ⟨Nat.lt_of_lt_of_le (hn x (Or.inr (Or.inl hx))).1 s1.2.2.2.1, (hn x (Or.inr (Or.inl hx))).2⟩) h2
    exact medeLoop_rinv hC q b g2 g' (s2.2.1.trans hd1) (Nat.le_trans (Nat.le_trans hL s1.2.2.2.1) s2.2.2.2.1) r2
      (fun x hx => ⟨Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hn x (Or.inr (Or.inr hx))).1 s1.2.2.2.1)
        s2.2.2.2.1, (hn x (Or.inr (Or.inr hx))).2⟩) h3
where
  crash_rinv {C : Map (Nat × List Nat)} {L o n : Nat} {ned : Need} {g g' : Comp.Gen Map}
      (hC : ∀ k v, HoonMap.get C k = some v → k < L) (hd : g.drop = false) (hL : L ≤ g.re) (hI : RInv C g)
      (hn : ∀ x, NMem ned x → x < g.re ∧ HoonMap.get C x = Option.none)
      (h : crashNeed o (Sum.inl n) ned g = some ((), g')) : RInv C g' := by
    simp only [crashNeed] at h
    obtain ⟨r, g1, h1, h2⟩ := bind_some h
    rw [re_apply] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hfr : HoonMap.get C g.re = Option.none := by
      cases e : HoonMap.get C g.re with
      | none => rfl
      | some v => have := hC _ v e; omega
    refine rinv_addOps (g := ({ g with re := g.re + 1 } : Comp.Gen Map)) hd (hI.re_up (Nat.le_succ _))
      (fun p hp x hx => ?_) h2
    simp only [List.mem_cons, List.mem_map] at hp
    show x < g.re + 1 ∧ _
    rcases hp with rfl | rfl | ⟨y, hy, rfl⟩
    · simp only [Comp.poleRegs, List.mem_singleton] at hx; subst hx; exact ⟨Nat.lt_succ_self _, hfr⟩
    · simp only [Comp.poleRegs, List.mem_singleton] at hx; subst hx; exact ⟨Nat.lt_succ_self _, hfr⟩
    · simp only [Comp.poleRegs, List.mem_singleton] at hx; subst hx
      have := hn x ((mem_flatten ned x).mp hy)
      exact ⟨Nat.lt_succ_of_lt this.1, this.2⟩

/-- **The gate of `+mede` keeps `RInv`** when the entry's need is old and
names no key. -/
theorem medeGate_rinv {C : Map (Nat × List Nat)} {L : Nat} (hC : ∀ k v, HoonMap.get C k = some v → k < L)
    {som : Noun} {x : Nat} {s : Sure S} (hs : ∀ y, NMem s.ned y → y < L ∧ HoonMap.get C y = Option.none)
    {g g' : Comp.Gen Map} (hd : g.drop = false) (hL : L ≤ g.re) (hI : RInv C g)
    (h : (do let ned ← sureRequireLook s; medeLoop x som ned : CM Map Unit) g = some ((), g')) : RInv C g' := by
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have Lk := sureRequireLook_spec h1
  obtain ⟨k, rfl⟩ := Lk.gen
  refine medeLoop_rinv hC ned som ({ g with re := k } : Comp.Gen Map) g' hd (Nat.le_trans hL Lk.le) (hI.re_up Lk.le)
    (fun y hy => ?_) h2
  rcases Lk.mem y hy with h | ⟨h1, h2⟩
  · exact ⟨Nat.lt_of_lt_of_le (hs y h).1 (Nat.le_trans hL Lk.le), (hs y h).2⟩
  · refine ⟨h2, ?_⟩
    cases e : HoonMap.get C y with
    | none => rfl
    | some v => have := hC _ v e; omega

/-- What the goal's lazy entries offer a walk: old registers, no key. -/
theorem IL.entry_regs {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g : Comp.Gen Map}
    (hI : IL K (CGoalL.next laz th) g) {o : Nat} :
    ∀ e ∈ (o, laz) :: entries laz, ∀ y, NMem e.2.sure.ned y → y < g.re ∧ HoonMap.get g.cond y = Option.none := by
  obtain ⟨-, -, hent⟩ := (hI.goal : GoalL g (CGoalL.next laz th))
  intro e he y hy
  have he' : ∃ e' ∈ (th.there, laz) :: entries laz, NMem e'.2.sure.ned y := by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨(th.there, laz), List.mem_cons_self, hy⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, hy⟩
  obtain ⟨e', he', hy'⟩ := he'
  refine ⟨((hent e' he').2.2 y hy').1, ?_⟩
  cases c : HoonMap.get g.cond y with
  | none => rfl
  | some v => exact absurd (⟨e', he', hy'⟩ : GRegL (CGoalL.next laz th) y) (hI.cond y v c).2.2.1

theorem IL.cond_lt {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) :
    ∀ k v, HoonMap.get g.cond k = some v → k < g.re := fun k v h => (hI.cond k v h).1

/-- The goal of nothing asked at a fresh jump. -/
theorem goalL_bunt {g : Comp.Gen Map} {j : Jmp} (hj : Fresh g j) :
    GoalL g (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) := by
  refine ⟨hj, ?_, fun e he => ?_⟩
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hj
    exact ⟨⟨b, hb, hp⟩, trivial, fun r hr => hr.elim⟩

/-! ## `%1` -/

/-- **`+mede` keeps the precondition** for its fresh hop block with nothing
asked. -/
theorem il_medeL {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {som : Noun} {g0 g1 : Comp.Gen Map}
    {o : Nat} (hI : IL K (CGoalL.next laz th) g0) (h : medeL th som laz g0 = some (o, g1)) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 o)) g1 := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hth, -, -⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  have targs : th.args = [] := by obtain ⟨_, _, _, a⟩ := hth; exact a
  obtain ⟨A1, -, hfr⟩ := (ht_medeL th som laz).run g0 o g1 hI.ats hth h
  obtain ⟨eo, ⟨hst, hcond⟩, -⟩ := medeL_walk hd h
  subst eo
  -- the walk keeps `RInv` of the old `cond`
  have R1 : RInv g0.cond g1 := by
    simp only [medeL] at h
    obtain ⟨o', ge, he, h⟩ := bind_some h
    rw [emit_apply] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨g', gg, hg, h⟩ := bind_some h
    rw [get_apply] at hg
    simp only [Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    have hde : (g0.emitted ⟨[], [], Termin.hop th⟩).drop = false := hd
    simp only [hde, Bool.false_eq_true, if_false] at h
    obtain ⟨u, g2, h2, h3⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨-, rfl⟩ := h3
    have W := walkLazy_inv (W := fun a : Comp.Gen Map => a.drop = false ∧ g0.re ≤ a.re ∧ RInv g0.cond a)
      (fun e he a b ⟨d, l, r⟩ hg => by
        have M := (medeGate_step d e.1 e.2.sure a b ⟨AddSt.refl a, rfl⟩ hg).1.1
        exact ⟨M.2.1.trans d, Nat.le_trans l M.2.2.2.1,
          medeGate_rinv hI.cond_lt (hI.entry_regs e he) d l r hg⟩)
      ⟨hde, Nat.le_refl _, fun k b hb => ?_, fun y hy => ?_⟩ h2
    · exact W.2.2
    · rw [em_get hd] at hb
      split at hb
      · cases hb; exact blobIn_nil_fin (jmpIn_nil targs)
      · exact hI.regs k b hb
    · have hy' : Defd g0.blocks y ∨ y ∈ blockDefs ⟨[], [], Termin.hop th⟩ := by
        have := (defd_put (b := (⟨[], [], Termin.hop th⟩ : Blob)) hI.ats.free (r := y)).mp
        exact this (by simpa [Gen.emitted, hd] using hy)
      rcases hy' with hy' | hy'
      · cases c : HoonMap.get g0.cond y with
        | none => rfl
        | some v => exact absurd hy' (hI.cond y v c).2.1
      · simp [blockDefs] at hy'
  have hre : g0.re ≤ g1.re := hst.2.2.2.1
  refine ⟨A1, R1.1, fun k v hk => ?_, hI.kvan.mono (by rw [hst.1]; exact Nat.le_succ _), goalL_bunt hfr⟩
  rw [hcond] at hk
  obtain ⟨k1, -, -, k4, k5⟩ := hI.cond k v hk
  refine ⟨Nat.lt_of_lt_of_le k1 hre, fun hdk => ?_, fun hg => (gregL_ofSure.mp hg).elim,
    Nat.lt_of_lt_of_le k4 hre, by rw [hcond]; exact k5⟩
  have := R1.2 k hdk
  have e : HoonMap.get g0.cond k = some v := hk
  rw [e] at this; cases this

/-- **`%1`, both halves.** -/
theorem liveRun_n1 (env : CallEnv) (sup : Option Nomm) (k : Noun) :
    LiveRun (Map := Map) IL JL (runLC (S := S) env sup (Nomm.n1 k)) := by
  intro K goal region g0 g1 nex hI h
  refine ⟨?_, liveC_n1 env sup hI h⟩
  have hd : g0.drop = false := hI.ats.1
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    rw [re_apply] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨o, gb, hb, h⟩ := bind_some h
    rw [emit_apply] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact il_emitGoal (R := g0.re + 1) (b := ⟨[], [Pole.imm k g0.re], Termin.don g0.re⟩)
      (s := (Sure.bunt : Sure S)) hI (Nat.le_succ _) rfl
      (batc_fresh fun j hj => by simp [finJumps] at hj)
      ⟨fun x hx => absurd hx List.not_mem_nil, fun p hp x hx => by
        rw [List.mem_singleton] at hp; subst hp
        simp only [Comp.poleRegs, List.mem_singleton] at hx; subst hx; exact Nat.lt_succ_self _,
        show g0.re < g0.re + 1 from Nat.lt_succ_self _⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega) (fun r hr => hr.elim) trivial
  | pick z o =>
    obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
    simp only [runLC] at h
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact il_bunt hI hz
    · split at h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact il_bunt hI ho
      · exact il_bombL hI h
  | next laz th =>
    simp only [runLC] at h
    obtain ⟨o, ga, ha, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact il_medeL hI ha

/-- **`%7`, both halves**, from its parts. -/
theorem liveRun_n7 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hq : LiveRun (Map := Map) IL JL (runLC (S := S) env (some p) q))
    (hp : LiveRun (Map := Map) IL JL (runLC (S := S) env sup p)) :
    LiveRun (Map := Map) IL JL (runLC (S := S) env sup (Nomm.n7 p q)) :=
  liveRun_seven env sup hq hp fun _ _ _ h => jl_il h

end Raw
end SkaModel
end Formalization
