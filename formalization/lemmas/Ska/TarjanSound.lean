import lemmas.Ska.TarjanTotal

/-!
# `tarjanM`'s components are the SCCs, callers first

On top of `TarjanTotal.lean` (totality, partition), the classical invariants,
in the arm's terms, for any result of `connect` / `kidsLoop` (the facts of
`connect_ok` about the same result come by determinism):

* `TjInv2`: indices are below `idx`; every emitted set is strongly
  connected; every kid of a member of `fin[i]` is in some `fin[j]`, `i ≤ j`
  (emitted at the same time or earlier: `FinClosed`);
* in the kids fold of `v` from the state `s0` before `enter`: `lowest` is
  `s0.idx` or the index of a vertex of the old stack that `v` reaches
  (`TjBR`); every new vertex on the stack reaches `v` or a vertex of the old
  stack with an index at least `lowest` (`TjKR`); every edge from a vertex
  visited in the fold to a vertex of the old stack has its index at least
  `lowest`.

At the pop (`lowest = s.idx`) the second case of `TjKR` is empty (old
indices are below `s.idx`), so the popped set reaches `v` and `v` reaches it;
an edge out of it to the old stack would lower `lowest`, so its kids are
popped with it or emitted before.  From `FinClosed` on the end state and the
partition: each component is a full SCC, and `flop` of the list is callees
first.
-/

namespace Formalization
namespace Tarjan

variable {V : Type} [DecidableEq V]

set_option linter.unusedSectionVars false

/-- Reachability along `kidsOf`. -/
inductive TjReach (G : Gr V) : V → V → Prop
  | refl (a : V) : TjReach G a a
  | step {a b c : V} : b ∈ kidsOf G a → TjReach G b c → TjReach G a c

theorem TjReach.trans {G : Gr V} {a b c : V} (h1 : TjReach G a b) (h2 : TjReach G b c) : TjReach G a c := by
  induction h1 with
  | refl => exact h2
  | step e _ ih => exact TjReach.step e (ih h2)

theorem TjReach.edge {G : Gr V} {a b : V} (e : b ∈ kidsOf G a) : TjReach G a b := TjReach.step e (TjReach.refl b)

/-- Kids of a member of `F[i]` are in some `F[j]`, `i ≤ j`. -/
def FinClosed (G : Gr V) (F : List (List V)) : Prop :=
  ∀ i (hi : i < F.length), ∀ x ∈ F[i], ∀ w ∈ kidsOf G x, ∃ j, ∃ hj : j < F.length, i ≤ j ∧ w ∈ F[j]

/-- The second invariant of the state. -/
structure TjInv2 (G : Gr V) (s : St V) : Prop where
  lt : ∀ u i, s.vis u = some i → i < s.idx
  sc : ∀ S ∈ s.fin, ∀ a ∈ S, ∀ b ∈ S, TjReach G a b
  clo : FinClosed G s.fin

/-- `lowest` against the state `s0` before `enter v`. -/
def TjBR (G : Gr V) (s0 : St V) (v : V) (lo : Nat) : Prop :=
  lo = s0.idx ∨ ∃ w ∈ s0.stk, s0.vis w = some lo ∧ TjReach G v w

/-- The new vertices on the stack reach `v` or an old stack vertex at or
above `lowest`. -/
def TjKR (G : Gr V) (s0 : St V) (v : V) (lo : Nat) (acc : St V) : Prop :=
  ∀ x ∈ acc.stk, s0.vis x = none →
    TjReach G x v ∨ ∃ w ∈ s0.stk, ∃ j, s0.vis w = some j ∧ lo ≤ j ∧ TjReach G x w

/-- The extra spec of `connect`, for any result. -/
def ConnOK2 (G : Gr V) (U : List V) (n : Nat) (rec : V → List V → St V → Option (Nat × St V)) : Prop :=
  ∀ v s lo s', v ∈ U → s.vis v = none → tjMeas U s < n → TjInv s → TjInU U s → TjInv2 G s →
    rec v (kidsOf G v) s = some (lo, s') →
    (∀ x, s.vis x = none → (s'.vis x).isSome → TjReach G v x) ∧ TjBR G s v lo ∧
    (∀ x ∈ s'.stk, s.vis x = none → ∃ w ∈ s.stk, ∃ j, s.vis w = some j ∧ lo ≤ j ∧ TjReach G x w) ∧
    (∀ x, s.vis x = none → (s'.vis x).isSome → ∀ w ∈ kidsOf G x, w ∈ s.stk → ∀ j, s.vis w = some j → lo ≤ j) ∧
    TjInv2 G s'

/-- A vertex of a later stack that is not new is on the old stack. -/
theorem old_of_stk {s0 acc : St V} (hE : TjExt s0 acc) {w : V} (hw : w ∈ acc.stk) (hv : s0.vis w ≠ none) :
    w ∈ s0.stk := by
  obtain ⟨X, hX, hn⟩ := hE.stk
  rw [hX] at hw
  rcases List.mem_append.1 hw with hw | hw
  · exact absurd (hn w hw) hv
  · exact hw

theorem stk_sub {s0 acc : St V} (hE : TjExt s0 acc) {w : V} (hw : w ∈ s0.stk) : w ∈ acc.stk := by
  obtain ⟨X, hX, -⟩ := hE.stk
  rw [hX]; exact List.mem_append_right _ hw

theorem tjBR_min {G : Gr V} {s0 : St V} {v : V} {lo x : Nat} (hL : lo ≤ s0.idx) (hB : TjBR G s0 v lo)
    (h : s0.idx ≤ x ∨ ∃ w ∈ s0.stk, s0.vis w = some x ∧ TjReach G v w) : TjBR G s0 v (min lo x) := by
  rcases h with h | h
  · rw [Nat.min_eq_left (Nat.le_trans hL h)]; exact hB
  · by_cases e : lo ≤ x
    · rw [Nat.min_eq_left e]; exact hB
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le e))]; exact Or.inr h

theorem tjKR_mono {G : Gr V} {s0 : St V} {v : V} {lo lo' : Nat} {acc : St V} (h : lo' ≤ lo)
    (hK : TjKR G s0 v lo acc) : TjKR G s0 v lo' acc := by
  intro x hx hn
  rcases hK x hx hn with h1 | ⟨w, hw, j, hj, hl, hr⟩
  · exact Or.inl h1
  · exact Or.inr ⟨w, hw, j, hj, Nat.le_trans h hl, hr⟩

theorem tjInv2_enter {G : Gr V} {s : St V} (h : TjInv2 G s) (v : V) : TjInv2 G (enter v s) := by
  refine ⟨fun u i hu => ?_, h.sc, h.clo⟩
  simp only [enter] at hu ⊢
  by_cases e : u = v
  · simp [e] at hu; omega
  · simp only [e, if_false] at hu; have := h.lt u i hu; omega

theorem some_inj2 {a b : Nat × St V} (h1 : x = some a) (h2 : x = some b) : a = b :=
  Option.some.inj (h1.symm.trans h2)

theorem isSome_of_ne {o : Option Nat} (h : o ≠ none) : o.isSome = true := by
  cases o with
  | none => exact absurd rfl h
  | some _ => rfl

theorem ne_of_isSome {o : Option Nat} (h : o.isSome = true) : o ≠ none := by
  cases o with
  | none => cases h
  | some _ => intro h'; cases h'

/-- **The kids fold keeps the invariants**, for any result. -/
theorem kidsLoop_ok2 {G : Gr V} {U : List V} {n : Nat} {rec : V → List V → St V → Option (Nat × St V)}
    (hU : ∀ u w, w ∈ kidsOf G u → w ∈ U) (hrec : ConnOK G U n rec) (hrec2 : ConnOK2 G U n rec)
    {s0 : St V} (hI0 : TjInv s0) {v : V} :
    ∀ (ks : List V) (lo : Nat) (acc : St V) (lo' : Nat) (acc' : St V),
      (∀ k ∈ ks, k ∈ kidsOf G v) → tjMeas U acc < n → TjInv acc → TjInU U acc → TjExt s0 acc → TjLoB s0 lo →
      TjInv2 G acc → TjBR G s0 v lo → TjKR G s0 v lo acc →
      kidsLoop G rec ks lo acc = some (lo', acc') →
      (∀ x, acc.vis x = none → (acc'.vis x).isSome → TjReach G v x) ∧ TjBR G s0 v lo' ∧ TjKR G s0 v lo' acc' ∧
      (∀ x, acc.vis x = none → (acc'.vis x).isSome → ∀ w ∈ kidsOf G x, w ∈ s0.stk → ∀ j, s0.vis w = some j → lo' ≤ j) ∧
      (∀ k ∈ ks, k ∈ s0.stk → ∀ j, s0.vis k = some j → lo' ≤ j) ∧ lo' ≤ lo ∧ TjInv2 G acc'
  | [], lo, acc, lo', acc', _, _, _, _, _, _, hI2, hB, hK, h => by
    simp only [kidsLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun x h1 h2 => (by rw [h1] at h2; cases h2), hB, hK, fun x h1 h2 => (by rw [h1] at h2; cases h2),
      (by simp), Nat.le_refl _, hI2⟩
  | k :: ks, lo, acc, lo', acc', hks, hm, hI, hIU, hE, hL, hI2, hB, hK, h => by
    have hkv := hks k List.mem_cons_self
    have hks' : ∀ k ∈ ks, k ∈ kidsOf G v := fun k' h => hks k' (List.mem_cons_of_mem _ h)
    cases e : acc.vis k with
    | some ki =>
      simp only [kidsLoop, e] at h
      have hlo1 : (if acc.cur k then min lo ki else lo) ≤ lo := by
        split
        · exact Nat.min_le_left _ _
        · exact Nat.le_refl _
      have hL1 : TjLoB s0 (if acc.cur k then min lo ki else lo) := by
        by_cases hc : acc.cur k = true
        · simp only [hc, if_true]
          exact tjLoB_min hL (stk_cases hI0 hE ((hI.cur k).1 hc) e)
        · simp only [hc]; exact hL
      have hB1 : TjBR G s0 v (if acc.cur k then min lo ki else lo) := by
        by_cases hc : acc.cur k = true
        · simp only [hc, if_true]
          apply tjBR_min hL.1 hB
          have hk := (hI.cur k).1 hc
          by_cases h0 : s0.vis k = none
          · exact Or.inl (hE.vis_new k ki h0 e)
          · right
            refine ⟨k, old_of_stk hE hk h0, ?_, TjReach.edge hkv⟩
            cases e0 : s0.vis k with
            | none => exact absurd e0 h0
            | some j => rw [hE.vis_ext k j e0] at e; rw [e]
        · simp only [hc]; exact hB
      obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := kidsLoop_ok2 hU hrec hrec2 hI0 ks _ acc lo' acc' hks' hm hI hIU hE
        hL1 hI2 hB1 (tjKR_mono hlo1 hK) h
      refine ⟨i1, i2, i3, i4, ?_, Nat.le_trans i6 hlo1, i7⟩
      intro k' hk' hs j hj
      rcases List.mem_cons.1 hk' with rfl | hk'
      · have hj' := hE.vis_ext k' j hj
        rw [e] at hj'
        cases hj'
        have hc : acc.cur k' = true := (hI.cur k').2 (stk_sub hE hs)
        simp only [hc, if_true] at i6
        exact Nat.le_trans i6 (Nat.min_le_right _ _)
      · exact i5 k' hk' hs j hj
    | none =>
      simp only [kidsLoop, e] at h
      cases hr : rec k (kidsOf G k) acc with
      | none => rw [hr] at h; cases h
      | some p =>
        obtain ⟨lk, a1⟩ := p
        rw [hr] at h
        simp only at h
        have hkU := hU v k hkv
        obtain ⟨lk2, a2, r1, r2, r3, r4, r5, r6, r7, -⟩ := hrec k acc hkU e hm hI hIU
        have := some_inj2 hr r1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        obtain ⟨c1, c2, c3, c4, c5⟩ := hrec2 k acc lk a1 hkU e hm hI hIU hI2 hr
        have hB1 : TjBR G s0 v (min lo lk) := by
          apply tjBR_min hL.1 hB
          rcases c2 with c2 | ⟨w, hw, hwl, hwr⟩
          · exact Or.inl (c2 ▸ hE.idx_le)
          · by_cases h0 : s0.vis w = none
            · exact Or.inl (hE.vis_new w lk h0 hwl)
            · right
              refine ⟨w, old_of_stk hE hw h0, ?_, TjReach.step hkv hwr⟩
              cases e0 : s0.vis w with
              | none => exact absurd e0 h0
              | some j => rw [hE.vis_ext w j e0] at hwl; rw [hwl]
        have hK1 : TjKR G s0 v (min lo lk) a1 := by
          intro x hx hn
          by_cases hx0 : acc.vis x = none
          · obtain ⟨w, hw, j, hj, hl, hr⟩ := c3 x hx hx0
            by_cases hw0 : s0.vis w = none
            · rcases hK w hw hw0 with h1 | ⟨w', hw', j', hj', hl', hr'⟩
              · exact Or.inl (hr.trans h1)
              · exact Or.inr ⟨w', hw', j', hj', Nat.le_trans (Nat.min_le_left _ _) hl', hr.trans hr'⟩
            · right
              refine ⟨w, old_of_stk hE hw hw0, j, ?_, Nat.le_trans (Nat.min_le_right _ _) hl, hr⟩
              cases e0 : s0.vis w with
              | none => exact absurd e0 hw0
              | some j0 => rw [hE.vis_ext w j0 e0] at hj; rw [hj]
          · exact tjKR_mono (Nat.min_le_left _ _) hK x (old_of_stk r2 hx hx0) hn
        obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := kidsLoop_ok2 hU hrec hrec2 hI0 ks _ a1 lo' acc' hks'
          (Nat.lt_of_le_of_lt (tjMeas_le r2.vis_ext) hm) r3 r4 (tjExt_trans hE r2) (tjLoB_rec hI0 hE hL r7)
          c5 hB1 hK1 h
        refine ⟨?_, i2, i3, ?_, ?_, Nat.le_trans i6 (Nat.min_le_left _ _), i7⟩
        · intro x hx hx'
          by_cases hx1 : a1.vis x = none
          · exact i1 x hx1 hx'
          · exact TjReach.step hkv (c1 x hx (isSome_of_ne hx1))
        · intro x hx hx' w hw hws j hj
          by_cases hx1 : a1.vis x = none
          · exact i4 x hx1 hx' w hw hws j hj
          · have := c4 x hx (isSome_of_ne hx1) w hw (stk_sub hE hws) j (hE.vis_ext w j hj)
            exact Nat.le_trans i6 (Nat.le_trans (Nat.min_le_right _ _) this)
        · intro k' hk' hs j hj
          rcases List.mem_cons.1 hk' with rfl | hk'
          · have := hE.vis_ext k' j hj
            rw [e] at this; cases this
          · exact i5 k' hk' hs j hj

theorem mem_of_count {s : St V} (hI : TjInv s) {w : V} (h : (s.vis w).isSome = true) :
    w ∈ s.stk ∨ w ∈ s.fin.flatten := by
  have hc := hI.count w
  rw [h, if_pos rfl] at hc
  have : w ∈ s.stk ++ s.fin.flatten := List.count_pos_iff.1 (by omega)
  exact List.mem_append.1 this

/-- **`connect` keeps the invariants**, at every fuel, for any result. -/
theorem connect_ok2 {G : Gr V} {U : List V} (hU : ∀ u w, w ∈ kidsOf G u → w ∈ U) :
    ∀ n, ConnOK2 G U n (connect G n)
  | 0 => fun _ _ _ _ _ _ hm => absurd hm (Nat.not_lt_zero _)
  | n + 1 => by
    intro v s lo s' hv hn hm hI hIU hI2 h
    have hm1 : tjMeas U (enter v s) < n := by have := tjMeas_enter (U := U) hv hn; omega
    have hE1 := tjExt_enter s hn
    have hKR0 : TjKR G s v s.idx (enter v s) := by
      intro x hx hx0
      simp only [enter, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl (TjReach.refl _)
      · have := vis_of_stk hI hx; rw [hx0] at this; cases this
    obtain ⟨lo1, a, h1, h2, h3, h4, h5, h6, h7⟩ := kidsLoop_ok hU (connect_ok hU n) hI (kidsOf G v) s.idx
      (enter v s) (fun k hk => hU v k hk) hm1 (tjInv_enter hI hn) (tjInU_enter hIU hv) hE1
      ⟨Nat.le_refl _, Or.inl rfl⟩
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := kidsLoop_ok2 hU (connect_ok hU n) (connect_ok2 hU n) hI (v := v)
      (kidsOf G v) s.idx (enter v s) lo1 a (fun k hk => hk) hm1 (tjInv_enter hI hn) (tjInU_enter hIU hv) hE1
      ⟨Nat.le_refl _, Or.inl rfl⟩ (tjInv2_enter hI2 v) (Or.inl rfl) hKR0 h1
    have henter : ∀ x, s.vis x = none → x ≠ v → (enter v s).vis x = none := by
      intro x hx hxv; simp [enter, hxv, hx]
    have hF : ∀ x, s.vis x = none → (a.vis x).isSome → TjReach G v x := by
      intro x hx hx'
      by_cases e : x = v
      · subst e; exact TjReach.refl _
      · exact k1 x (henter x hx e) hx'
    have hLE : ∀ x, s.vis x = none → (a.vis x).isSome → ∀ w ∈ kidsOf G x, w ∈ s.stk → ∀ j, s.vis w = some j →
        lo1 ≤ j := by
      intro x hx hx' w hw hws j hj
      by_cases e : x = v
      · subst e; exact k5 w hw hws j hj
      · exact k4 x (henter x hx e) hx' w hw hws j hj
    simp only [connect, h1] at h
    by_cases hl : s.idx = lo1
    · obtain ⟨X, hX, hXn⟩ := h2.stk
      have hvX : v ∉ X := fun h => by have := hXn v h; simp [enter] at this
      have hX' : a.stk = X ++ v :: s.stk := by rw [hX]; rfl
      have hXs : ∀ x ∈ X, s.vis x = none ∧ x ≠ v := by
        intro x hx
        have := hXn x hx
        simp only [enter] at this
        by_cases e : x = v
        · simp [e] at this
        · simp only [e, if_false] at this; exact ⟨this, e⟩
      obtain ⟨cur', hp, hc⟩ := popLoop_split v s.stk X [] a.cur hvX
      rw [if_pos hl] at h
      simp only [hX', hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hXa : ∀ x ∈ X, x ∈ a.stk := fun x hx => by rw [hX']; exact List.mem_append_left _ hx
      have hXv : ∀ x ∈ X, TjReach G x v := by
        intro x hx
        rcases k3 x (hXa x hx) (hXs x hx).1 with h | ⟨w, hw, j, hj, hl', -⟩
        · exact h
        · have := hI2.lt w j hj; omega
      have hva : (a.vis v).isSome := by rw [h2.vis_ext v s.idx (by simp [enter])]; rfl
      have hPv : ∀ x ∈ v :: (X.reverse ++ []), TjReach G x v ∧ TjReach G v x ∧ s.vis x = none ∧ (a.vis x).isSome := by
        intro x hx
        simp only [List.append_nil, List.mem_cons, List.mem_reverse] at hx
        rcases hx with rfl | hx
        · exact ⟨TjReach.refl _, TjReach.refl _, hn, hva⟩
        · have hs := vis_of_stk h3 (hXa x hx)
          exact ⟨hXv x hx, hF x (hXs x hx).1 hs, (hXs x hx).1, hs⟩
      refine ⟨hF, k2, fun x hx hx0 => ?_, hLE, ⟨k7.lt, ?_, ?_⟩⟩
      · have := vis_of_stk hI hx; rw [hx0] at this; cases this
      · intro S hS a1 ha1 b1 hb1
        rcases List.mem_cons.1 hS with rfl | hS
        · exact (hPv a1 ha1).1.trans (hPv b1 hb1).2.1
        · exact k7.sc S hS a1 ha1 b1 hb1
      · intro i hi x hx w hw
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero] at hx
          obtain ⟨-, -, hxn, hxa⟩ := hPv x hx
          have hCloA : (a.vis w).isSome := by
            by_cases e : x = v
            · subst e; exact h6 w hw
            · exact h5 x (henter x hxn e) hxa w hw
          rcases mem_of_count h3 hCloA with hws | hwf
          · rw [hX'] at hws
            rcases List.mem_append.1 hws with hws | hws
            · exact ⟨0, by simp, Nat.le_refl _, by simp [hws]⟩
            · rcases List.mem_cons.1 hws with rfl | hws
              · exact ⟨0, by simp, Nat.le_refl _, by simp⟩
              · exfalso
                have hs := vis_of_stk hI hws
                cases e : s.vis w with
                | none => rw [e] at hs; cases hs
                | some j =>
                  have := hLE x hxn hxa w hw hws j e
                  have := hI2.lt w j e
                  omega
          · obtain ⟨S, hS, hwS⟩ := List.mem_flatten.1 hwf
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hS
            exact ⟨j + 1, by simp; omega, Nat.zero_le _, by simpa using hwS⟩
        | succ i =>
          simp only [List.getElem_cons_succ] at hx
          simp only [List.length_cons] at hi
          obtain ⟨j, hj, hij, hw'⟩ := k7.clo i (by omega) x hx w hw
          exact ⟨j + 1, by simp; omega, by omega, by simpa using hw'⟩
    · rw [if_neg hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hF, k2, fun x hx hx0 => ?_, hLE, k7⟩
      rcases k3 x hx hx0 with h | h
      · rcases k2 with k2 | ⟨w, hw, hwl, hwr⟩
        · exact absurd k2.symm hl
        · exact ⟨w, hw, lo1, hwl, Nat.le_refl _, h.trans hwr⟩
      · exact h

/-- The outer fold keeps `TjInv2`, for any result. -/
theorem outer_ok2 {G : Gr V} {U : List V} (hU : ∀ u w, w ∈ kidsOf G u → w ∈ U)
    (hK : ∀ p ∈ G, kidsOf G p.1 = p.2) {n : Nat} :
    ∀ (rest : Gr V) (acc s' : St V), (∀ p ∈ rest, p ∈ G) → (∀ p ∈ rest, p.1 ∈ U) → tjMeas U acc < n →
      TjInv acc → TjInU U acc → acc.stk = [] → TjInv2 G acc → outer G n rest acc = some s' → TjInv2 G s'
  | [], acc, s', _, _, _, _, _, _, hI2, h => by
    simp only [outer, Option.some.injEq] at h; subst h; exact hI2
  | (v, kids) :: rest, acc, s', hG, hR, hm, hI, hIU, hs, hI2, h => by
    have hG' : ∀ p ∈ rest, p ∈ G := fun p h => hG p (List.mem_cons_of_mem _ h)
    have hR' : ∀ p ∈ rest, p.1 ∈ U := fun p h => hR p (List.mem_cons_of_mem _ h)
    cases e : acc.vis v with
    | some i =>
      simp only [outer, e] at h
      exact outer_ok2 hU hK rest acc s' hG' hR' hm hI hIU hs hI2 h
    | none =>
      have hk : kids = kidsOf G v := (hK (v, kids) (hG _ List.mem_cons_self)).symm
      obtain ⟨lo, a, r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        connect_ok hU n v acc (hR _ List.mem_cons_self) e hm hI hIU
      have hlo : lo = acc.idx := by
        rcases r7.2 with h | ⟨w, hw, -⟩
        · exact h
        · rw [hs] at hw; cases hw
      have hsa : a.stk = [] := by rw [r8 hlo, hs]
      have c5 := (connect_ok2 hU n v acc lo a (hR _ List.mem_cons_self) e hm hI hIU hI2 r1).2.2.2.2
      simp only [outer, e, hk, r1] at h
      exact outer_ok2 hU hK rest a s' hG' hR' (Nat.lt_of_le_of_lt (tjMeas_le r2.vis_ext) hm) r3 r4 hsa c5 h

end Tarjan
end Formalization
