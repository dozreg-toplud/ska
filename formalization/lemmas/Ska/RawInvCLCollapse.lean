import lemmas.Ska.RawInvCLPair

/-!
# The gate of `+collapse-lazy-atom` as a walk that only puts ops in front

README Gaps 14 (b), track D.  The arms `%3`, `%4`, `%5` under `%next` walk
the goal's lazy tree with `collapseGate r there`; its ops read first only
`r` or a proxy of `r`, and define the entry's need except `r` itself and
registers made during the walk.  So the walk lemma is needed with an
exception set `D` for the definitions (`GStepD`, `WalkPD`,
`walkList_prepD`, `walkLazy_prepD`; `walkLazy_prepG` is the case `D := ⊥`).

* `CSt a b`: `AddSt` and "every key of `cond` is below `re`" carried.
* `srcStep`: the source `r` or `+proxy r oLaz` (a fresh key standing for `r`).
* **`collapseGate_step`**: the gate is a `GStepD` with
  `R g y := y = r ∨ ∃ t, cond y = (r, t)` and `D y := y = r ∨ g0.re ≤ y`.
* **`collapseWalk_prep`**: the walk of `+collapse-lazy-atom` as `WalkPD`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Walks with an exception set for the definitions -/

/-- `GStep` with the need's registers in `D` exempt from being defined. -/
def GStepD (R : Comp.Gen Map → Nat → Prop) (D : Nat → Prop) (x : Nat) (s : Sure S) (g g' : Comp.Gen Map) : Prop :=
  ∃ A, Prep (fun k => if k = x then A else []) g.blocks g'.blocks ∧ (∀ r, NMem s.ned r → D r ∨ r ∈ defsOf A) ∧
    ∀ y, OpsRF A y → R g' y

/-- `WalkP` with the exception set `D`. -/
def WalkPD (R : Comp.Gen Map → Nat → Prop) (D : Nat → Prop) (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map) :
    Prop :=
  ∃ P, Prep P g.blocks g'.blocks ∧ (∀ e ∈ es, ∀ r, NMem e.2.sure.ned r → D r ∨ r ∈ defsOf (P e.1)) ∧
    (∀ k y, OpsRF (P k) y → R g' y) ∧ ∀ k, P k ≠ [] → ∃ e ∈ es, e.1 = k

theorem walkList_prepD {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {D : Nat → Prop} {g0 : Comp.Gen Map}
    (hf : ∀ x s g g', St g0 g → f x s g = some ((), g') → St g g' ∧ GStepD R D x s g g') :
    ∀ (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map), St g0 g → walkList f es g = some ((), g') →
      St g g' ∧ WalkPD R D es g g'
  | [], g, g', _, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hrf g, fun _ => [], prep_nil _, fun e he => absurd he List.not_mem_nil, fun _ _ h => h.elim,
      fun _ h => absurd rfl h⟩
  | (x, l) :: rest, g, g', h0, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨s1, A, pA, kA, rA⟩ := hf x l.sure g g1 h0 h1
    obtain ⟨s2, Q, pQ, kQ, rQ, eQ⟩ := walkList_prepD hrf htr hR hf rest g1 g' (htr _ _ _ h0 s1) h2
    refine ⟨htr _ _ _ s1 s2, _, prep_trans pA pQ, fun e he r hr => ?_, fun k y hy => ?_, fun k hk => ?_⟩
    · rw [defsOf_append, List.mem_append]
      rcases List.mem_cons.mp he with rfl | he
      · rcases kA r hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (by simp only [if_pos rfl]; exact h))
      · rcases kQ e he r hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · rcases opsRF_append.mp hy with h | ⟨-, h⟩
      · exact rQ k y h
      · by_cases e : k = x
        · rw [if_pos e] at h
          exact hR _ _ _ s2 (rA y h)
        · rw [if_neg e] at h; exact h.elim
    · by_cases e : k = x
      · exact ⟨(x, l), List.mem_cons_self, e.symm⟩
      · have : Q k ≠ [] := by
          intro hq; apply hk; simp [hq, e]
        obtain ⟨e', he', ee⟩ := eQ k this
        exact ⟨e', List.mem_cons_of_mem _ he', ee⟩

theorem walkLazy_prepD {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {D : Nat → Prop} {g0 : Comp.Gen Map}
    (hf : ∀ x s g g', St g0 g → f x s g = some ((), g') → St g g' ∧ GStepD R D x s g g')
    {o : Nat} {l : Lazy S} {g' : Comp.Gen Map} (h : walkLazy f o l g0 = some ((), g')) :
    St g0 g' ∧ WalkPD R D ((o, l) :: entries l) g0 g' := by
  have e : (walkLazy f o l : CM Map Unit) = walkList f ((o, l) :: wentries l) := by
    rw [walkLazy_flat]; rfl
  rw [e] at h
  obtain ⟨s, P, pP, kP, rP, eP⟩ := walkList_prepD hrf htr hR hf _ g0 g' (hrf g0) h
  have hm : ∀ e, e ∈ (o, l) :: entries l ↔ e ∈ (o, l) :: wentries l := fun e =>
    ((wentries_perm l).cons (o, l)).mem_iff.symm
  refine ⟨s, P, pP, fun e he => kP e ((hm e).mp he), rP, fun k hk => ?_⟩
  obtain ⟨e, he, ee⟩ := eP k hk
  exact ⟨e, (hm e).mpr he, ee⟩

/-! ## The steps of the gate -/

/-- Every key of `cond` is below `re`. -/
def CondLt (g : Comp.Gen Map) : Prop := ∀ k v, HoonMap.get g.cond k = some v → k < g.re

/-- The relation of the walk of `+collapse-lazy-atom`. -/
def CSt (a b : Comp.Gen Map) : Prop := AddSt a b ∧ (CondLt a → CondLt b)

theorem CSt.refl (a : Comp.Gen Map) : CSt a a := ⟨AddSt.refl a, id⟩

theorem CSt.trans {a b c : Comp.Gen Map} (h1 : CSt a b) (h2 : CSt b c) : CSt a c :=
  ⟨h1.1.trans h2.1, fun h => h2.2 (h1.2 h)⟩

/-- What the ops of the gate may read first: `r` or a proxy of it. -/
def RCol (r : Nat) (g : Comp.Gen Map) (y : Nat) : Prop := y = r ∨ ∃ t, HoonMap.get g.cond y = some (r, t)

theorem rCol_mono {r : Nat} {a b : Comp.Gen Map} {y : Nat} (h : CSt a b) (hy : RCol r a y) : RCol r b y := by
  rcases hy with hy | ⟨t, ht⟩
  · exact Or.inl hy
  · exact Or.inr ⟨t, h.1.2.2.2.2.1 _ _ ht⟩

/-- **The source of the gate**: `r` itself, or a fresh proxy of `r`. -/
theorem srcStep {r o oLaz src : Nat} {g g' : Comp.Gen Map} (hd : g.drop = false) (hc0 : CondLt g)
    (h : (if oLaz = o then pure r else proxy r oLaz : CM Map Nat) g = some (src, g')) :
    CSt g g' ∧ RCol r g' src ∧ (src = r ∨ g.re ≤ src) ∧ g'.blocks = g.blocks := by
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨CSt.refl _, Or.inl rfl, Or.inl rfl, rfl⟩
  · unfold proxy at h
    dsimp only at h
    simp only [hd, Bool.false_eq_true, if_false] at h
    obtain ⟨tag, -, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨⟨⟨rfl, hd.symm, rfl, Nat.le_succ _, fun k v hk => ?_, fun k v hk => ?_⟩, fun hc k v hk => ?_⟩,
      Or.inr ⟨tag, by simp [HoonMap.get_put]⟩, Or.inr (Nat.le_refl _), rfl⟩
    · show HoonMap.get (HoonMap.put g.cond g.re (r, tag)) k = some v
      rw [HoonMap.get_put]
      split
      · rename_i e
        have := hc0 k v hk; omega
      · exact hk
    · change HoonMap.get (HoonMap.put g.cond g.re (r, tag)) k = some v at hk
      rw [HoonMap.get_put] at hk
      split at hk
      · rename_i e; exact Or.inr (Nat.le_of_eq e.symm)
      · exact Or.inl hk
    · change HoonMap.get (HoonMap.put g.cond g.re (r, tag)) k = some v at hk
      show k < g.re + 1
      rw [HoonMap.get_put] at hk
      split at hk
      · rename_i e; omega
      · exact Nat.lt_succ_of_lt (hc k v hk)

/-- **The gate of `+collapse-lazy-atom` only puts ops in front**: they read
first `r` or a proxy of `r`, and define the entry's need but `r` and the
registers made during the walk. -/
theorem collapseGate_step {r o : Nat} {g0 : Comp.Gen Map} (hd : g0.drop = false) (hc0 : CondLt g0) (x : Nat)
    (s : Sure S) (g g' : Comp.Gen Map) (h0 : CSt g0 g) (h : collapseGate r o x s g = some ((), g')) :
    CSt g g' ∧ GStepD (RCol r) (fun y => y = r ∨ g0.re ≤ y) x s g g' := by
  have hdg : g.drop = false := h0.1.2.1.trans hd
  have hcg : CondLt g := h0.2 hc0
  have hg0 : g0.re ≤ g.re := h0.1.2.2.2.1
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨k, rfl⟩ := L.gen
  have S1 : CSt g ({ g with re := k } : Comp.Gen Map) :=
    ⟨⟨rfl, rfl, rfl, L.le, fun _ _ h => h, fun _ _ h => Or.inl h⟩, fun hc k' v hk => Nat.lt_of_lt_of_le (hc k' v hk) L.le⟩
  have hkeep : ∀ y, NMem s.ned y → NMem ned y := fun y hy => sureRequireLook_keeps h1 hy
  have hdk : ({ g with re := k } : Comp.Gen Map).drop = false := hdg
  have hck : CondLt ({ g with re := k } : Comp.Gen Map) := S1.2 hcg
  have hgk : g.re ≤ k := L.le
  -- the ops after the source, from the state after it
  have tail : ∀ (src : Nat) (A : List Pole) (g2 : Comp.Gen Map), CSt ({ g with re := k } : Comp.Gen Map) g2 →
      g2.blocks = g.blocks → RCol r g2 src → addOps x A g2 = some ((), g') →
      CSt g g' ∧ Prep (fun k => if k = x then A else []) g.blocks g'.blocks ∧ ∀ y, RCol r g2 y → RCol r g' y := by
    intro src A g2 S2 hb2 _ h4
    obtain ⟨A3, c3, P3⟩ := addOps_step (S2.1.2.1.trans hdk) h4
    refine ⟨S1.trans (S2.trans ⟨A3, fun hc k' v hk => ?_⟩), hb2 ▸ P3, fun y hy => rCol_mono ⟨A3, fun hc k' v hk => ?_⟩ hy⟩
    · rw [c3] at hk; exact Nat.lt_of_lt_of_le (hc k' v hk) A3.2.2.2.1
    · rw [c3] at hk; exact Nat.lt_of_lt_of_le (hc k' v hk) A3.2.2.2.1
  have crashC : ∀ ned' : Need, (∀ y, NMem s.ned y → NMem ned' y) →
      (do let src ← (if x = o then pure r else proxy r x : CM Map Nat); crashNeed x (Sum.inr src) ned' : CM Map Unit)
        ({ g with re := k } : Comp.Gen Map) = some ((), g') →
      CSt g g' ∧ GStepD (RCol r) (fun y => y = r ∨ g0.re ≤ y) x s g g' := by
    intro ned' hkeep' h2
    obtain ⟨src, g2, h3, h4⟩ := bind_some h2
    obtain ⟨S2, R2, F2, B2⟩ := srcStep hdk hck h3
    simp only [crashNeed] at h4
    obtain ⟨St, Pr, Rm⟩ := tail src _ g2 S2 B2 R2 h4
    refine ⟨St, _, Pr, fun y hy => ?_, fun y hy => ?_⟩
    · have hf := (mem_flatten ned' y).mpr (hkeep' y hy)
      by_cases e : y = src
      · subst e
        rcases F2 with F2 | F2
        · exact Or.inl (Or.inl F2)
        · exact Or.inl (Or.inr (Nat.le_trans hg0 (Nat.le_trans hgk F2)))
      · refine Or.inr ?_
        simp only [defsOf_cons, aliasDst, Option.toList_none, List.nil_append, defsOf_fill]
        exact List.mem_filter.mpr ⟨hf, by simp [e]⟩
    · rcases hy with hy | ⟨-, hy⟩
      · rw [reads_cel] at hy; subst hy; exact Rm _ R2
      · exact (opsRF_fill _ hy).elim
  cases ned with
  | none =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, true_and] at h2
    subst h2
    exact ⟨S1, [], prep_same, fun y hy => (hkeep y hy).elim, fun y hy => hy.elim⟩
  | this r' =>
    dsimp only at h2
    split at h2
    · rename_i e
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, true_and] at h2
      subst h2
      refine ⟨S1, [], prep_same, fun y hy => Or.inl (Or.inl ?_), fun y hy => hy.elim⟩
      have e' : y = r' := hkeep y hy
      exact e'.trans e.symm
    · obtain ⟨src, g2, h3, h4⟩ := bind_some h2
      obtain ⟨S2, R2, -, B2⟩ := srcStep hdk hck h3
      obtain ⟨St, Pr, Rm⟩ := tail src _ g2 S2 B2 R2 h4
      refine ⟨St, [Pole.mov src r'], Pr, fun y hy => Or.inr ?_, fun y hy => ?_⟩
      · have e : y = r' := hkeep y hy
        subst e; simp [defsOf, aliasDst]
      · rcases hy with hy | ⟨-, hy⟩
        · rw [reads_mov] at hy; subst hy; exact Rm _ R2
        · exact hy.elim
  | pair p q => exact crashC _ hkeep h2
  | both r0 p q => exact crashC _ hkeep h2

/-- **The walk of `+collapse-lazy-atom`** as a walk that only puts ops in
front, under any `cond` whose keys are below `re`. -/
theorem collapseWalk_prep {r o : Nat} {l : Lazy S} {g0 g1 : Comp.Gen Map} (hd : g0.drop = false)
    (hc0 : CondLt g0) (h : walkLazy (collapseGate r o) o l g0 = some ((), g1)) :
    CSt g0 g1 ∧ WalkPD (RCol r) (fun y => y = r ∨ g0.re ≤ y) ((o, l) :: entries l) g0 g1 :=
  walkLazy_prepD (R := RCol r) (D := fun y => y = r ∨ g0.re ≤ y) CSt.refl (fun _ _ _ h1 h2 => h1.trans h2) (fun _ _ _ h hy => rCol_mono h hy)
    (fun x s g g' h0 h => collapseGate_step hd hc0 x s g g' h0 h) h

/-! ## Liveness through such a walk -/

/-- A register the gate may read first is `r` once unproxied. -/
theorem rCol_unproxy {r : Nat} {g : Comp.Gen Map} (hr : HoonMap.get g.cond r = Option.none) {x : Nat}
    (h : RCol r g x) : unproxy g.cond x = r := by
  rcases h with rfl | ⟨t, ht⟩
  · exact unproxy_none hr
  · simp [unproxy, ht]

/-- **A register other than the walk's source, live after a walk whose ops
read first only what unproxies to `R0`**, is live before it with the kills
the unproxied ops define (`unpM_prepG`, `liveK_prepK`, `opsRF_ren_back`):
the step of every walking arm (`+collapse-lazy-atom`, `+kern`). -/
theorem liveK_walkR {R0 : Nat} {P : Nat → List Pole} {g g' : Comp.Gen Map} (hP : Prep P g.blocks g'.blocks)
    (hc : ∀ x, x < g.re → HoonMap.get g'.cond x = HoonMap.get g.cond x)
    (hR : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b)
    (hread : ∀ k x, OpsRF (P k) x → unproxy g'.cond x = R0) {K : Nat → Nat → Prop} {k y : Nat} (hy : y ≠ R0)
    (h : LiveK (unpM g') K k y) :
    LiveK (unpM g) (fun x z => K x z ∨ z ∈ defsOf ((P x).map (renPole (unproxy g'.cond)))) k y := by
  have pU := unpM_prepG hP hc hR
  refine (liveK_prepK pU (K' := fun x z => z ∈ defsOf ((P x).map (renPole (unproxy g'.cond)))) (fun _ _ h => h)
    h).resolve_right fun ⟨k', hk'⟩ => ?_
  obtain ⟨x, ex, hx⟩ := opsRF_ren_back _ hk'
  exact hy (ex.symm.trans (hread k' x hx))

end Raw
end SkaModel
end Formalization
