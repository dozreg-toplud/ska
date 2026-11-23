import lemmas.Ska.ConvArms

/-!
# Convergence: `+cull`, `+sweep`, and the stable pass

`+cull` keeps the convergence invariant with the same frozen entries: a live
member's callees among the members are live (`liveLoop_closed`), and every
member it keeps above the root is reachable from the root
(`liveLoop_sound`).  `+sweep` lists every member reachable from the root
(`sweepLoop_closed`), so after a cull the sweep of the next pass lists every
member above the root.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## Reachability over the callees -/

/-- `c` is reachable from `a` over the callees in `st`, through identities
in `W`. -/
inductive Reach (st : SkaState M R) (W : Ident → Prop) (a : Ident) : Ident → Prop where
  | refl : Reach st W a a
  | step {b c : Ident} : Reach st W a b → c ∈ kids st b → W c → Reach st W a c

/-- **The live set of `+cull` is closed**: a live member's callees among the
members are live. -/
theorem liveLoop_closed {st : SkaState M R} {members : M Ident Unit} :
    ∀ (n : Nat) (q : List Ident) (live live' : M Ident Unit), liveLoop st members n q live = some live' →
    (∀ x, Treap.has live x = true → ∀ k ∈ kids st x, Treap.has members k = true → Treap.has live k = true ∨ k ∈ q) →
    ∀ x, Treap.has live' x = true → ∀ k ∈ kids st x, Treap.has members k = true → Treap.has live' k = true
  | 0, _, _, _, h, _ => by simp [liveLoop] at h
  | n + 1, [], live, live', h, hI => by
    simp only [liveLoop, Option.some.injEq] at h; subst h
    intro x hx k hk hm
    rcases hI x hx k hk hm with h | h
    · exact h
    · cases h
  | n + 1, i :: q, live, live', h, hI => by
    unfold liveLoop at h
    split at h
    · rename_i hc
      refine liveLoop_closed n q live live' h (fun x hx k hk hm => ?_)
      rcases hI x hx k hk hm with h1 | h1
      · exact Or.inl h1
      · rcases List.mem_cons.mp h1 with rfl | h1
        · rcases hc with hc | hc
          · exact Or.inl hc
          · rw [hm] at hc; cases hc
        · exact Or.inr h1
    · refine liveLoop_closed n _ _ live' h (fun x hx k hk hm => ?_)
      rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
      · exact Or.inr (List.mem_append_right _ hk)
      · rcases hI x hx k hk hm with h1 | h1
        · exact Or.inl ((Treap.has_ins _ _ _).mpr (Or.inr h1))
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inl ((Treap.has_ins _ _ _).mpr (Or.inl rfl))
          · exact Or.inr (List.mem_append_left _ h1)

/-- **The live set of `+cull` is reachable** from the root, through members. -/
theorem liveLoop_sound {st : SkaState M R} {members : M Ident Unit} {a : Ident} :
    ∀ (n : Nat) (q : List Ident) (live live' : M Ident Unit), liveLoop st members n q live = some live' →
    (∀ x, Treap.has live x = true → Reach st (fun y => Treap.has members y = true) a x) →
    (∀ x ∈ q, Reach st (fun y => Treap.has members y = true) a x ∨
      ∃ y, Reach st (fun y => Treap.has members y = true) a y ∧ x ∈ kids st y) →
    ∀ x, Treap.has live' x = true → Reach st (fun y => Treap.has members y = true) a x
  | 0, _, _, _, h, _, _ => by simp [liveLoop] at h
  | n + 1, [], live, live', h, hL, _ => by
    simp only [liveLoop, Option.some.injEq] at h; subst h; exact hL
  | n + 1, i :: q, live, live', h, hL, hQ => by
    unfold liveLoop at h
    split at h
    · exact liveLoop_sound n q live live' h hL (fun x hx => hQ x (List.mem_cons_of_mem _ hx))
    · rename_i hc
      have hmi : Treap.has members i = true := by
        cases e : Treap.has members i
        · exact absurd (Or.inr (by simp [e])) hc
        · rfl
      have hri : Reach st (fun y => Treap.has members y = true) a i := by
        rcases hQ i List.mem_cons_self with h1 | ⟨y, hy, hk⟩
        · exact h1
        · exact Reach.step hy hk hmi
      refine liveLoop_sound n _ _ live' h (fun x hx => ?_) (fun x hx => ?_)
      · rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
        · exact hri
        · exact hL x hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hQ x (List.mem_cons_of_mem _ hx)
        · exact Or.inr ⟨i, hri, hx⟩

/-! ## `+sweep` lists what the root reaches -/

/-- **`+sweep` lists every member the root reaches**: its output is closed
under the callees in `was`, and holds the root. -/
theorem sweepLoop_closed {st : SkaState M R} {was : M Ident Unit} :
    ∀ (n : Nat) (seen : M Ident Unit) (stack : List (Ident × List Ident)) (out res : List Ident),
    sweepLoop st was n seen stack out = some res →
    (∀ x, Treap.has seen x = true → x ∈ out ∨ x ∈ stack.map (·.1)) →
    (∀ y ∈ out, ∀ k ∈ kids st y, Treap.has was k = true → Treap.has seen k = true) →
    (∀ p ∈ stack, ∃ pre, kids st p.1 = pre ++ p.2 ∧
      ∀ k ∈ pre, Treap.has was k = true → Treap.has seen k = true) →
    (∀ x, Treap.has seen x = true → x ∈ res) ∧
      ∀ y ∈ res, ∀ k ∈ kids st y, Treap.has was k = true → k ∈ res
  | 0, _, _, _, _, h, _, _, _ => by simp [sweepLoop] at h
  | n + 1, seen, [], out, res, h, hA, hB, _ => by
    simp only [sweepLoop, Option.some.injEq] at h
    subst h
    refine ⟨fun x hx => ?_, fun y hy k hk hw => ?_⟩
    · rcases hA x hx with h1 | h1
      · exact List.mem_reverse.mpr h1
      · simp at h1
    · rcases hA k (hB y (List.mem_reverse.mp hy) k hk hw) with h1 | h1
      · exact List.mem_reverse.mpr h1
      · simp at h1
  | n + 1, seen, (i, []) :: rest, out, res, h, hA, hB, hC => by
    simp only [sweepLoop] at h
    refine sweepLoop_closed n seen rest (i :: out) res h (fun x hx => ?_) (fun y hy k hk hw => ?_)
      (fun p hp => hC p (List.mem_cons_of_mem _ hp))
    · rcases hA x hx with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · simp only [List.map_cons, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h1
    · rcases List.mem_cons.mp hy with rfl | hy
      · obtain ⟨pre, hpre, hp⟩ := hC (y, []) List.mem_cons_self
        simp only [List.append_nil] at hpre
        rw [hpre] at hk
        exact hp k hk hw
      · exact hB y hy k hk hw
  | n + 1, seen, (i, k :: ks) :: rest, out, res, h, hA, hB, hC => by
    unfold sweepLoop at h
    split at h
    · rename_i hc
      refine sweepLoop_closed n seen ((i, ks) :: rest) out res h (fun x hx => ?_) hB (fun p hp => ?_)
      · rcases hA x hx with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (by simpa using h1)
      · rcases List.mem_cons.mp hp with rfl | hp
        · obtain ⟨pre, hpre, hp'⟩ := hC (i, k :: ks) List.mem_cons_self
          refine ⟨pre ++ [k], by rw [hpre]; simp, fun k' hk' hw => ?_⟩
          rcases List.mem_append.mp hk' with hk' | hk'
          · exact hp' k' hk' hw
          · rw [List.mem_singleton.mp hk'] at hw ⊢
            rcases hc with hc | hc
            · exact hc
            · rw [hw] at hc; cases hc
        · exact hC p (List.mem_cons_of_mem _ hp)
    · refine (fun key => ⟨fun x hx => key.1 x ((Treap.has_ins _ _ _).mpr (Or.inr hx)), key.2⟩)
        (sweepLoop_closed n (Treap.ins seen k) ((k, kids st k) :: (i, ks) :: rest) out res h (fun x hx => ?_)
        (fun y hy k' hk' hw => (Treap.has_ins _ _ _).mpr (Or.inr (hB y hy k' hk' hw))) (fun p hp => ?_))
      · rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
        · exact Or.inr (by simp)
        · rcases hA x hx with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by simp at h1 ⊢; rcases h1 with h1 | h1 <;> simp [h1])
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · exact ⟨[], by simp, fun _ h => by simp at h⟩
        · obtain ⟨pre, hpre, hp'⟩ := hC (i, k :: ks) List.mem_cons_self
          refine ⟨pre ++ [k], by rw [hpre]; simp, fun k' hk' hw => ?_⟩
          rcases List.mem_append.mp hk' with hk' | hk'
          · exact (Treap.has_ins _ _ _).mpr (Or.inr (hp' k' hk' hw))
          · rw [List.mem_singleton.mp hk']; exact (Treap.has_ins _ _ _).mpr (Or.inl rfl)
        · obtain ⟨pre, hpre, hp'⟩ := hC p (List.mem_cons_of_mem _ hp)
          exact ⟨pre, hpre, fun k' hk' hw => (Treap.has_ins _ _ _).mpr (Or.inr (hp' k' hk' hw))⟩

/-- **The sweep from `id` lists everything `id` reaches through `was`.** -/
theorem sweep_reach {n : Nat} {id : Ident} {was : M Ident Unit} {st : SkaState M R} {res : List Ident}
    (h : sweep n id was st = some res) {x : Ident} (hx : Reach st (fun y => Treap.has was y = true) id x) :
    x ∈ res := by
  unfold sweep at h
  obtain ⟨h1, h2⟩ := sweepLoop_closed n _ _ [] res h
    (fun x hx => by
      rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
      · exact Or.inr (by simp)
      · simp [Treap.has, Treap.get_empty] at hx)
    (fun y hy => by simp at hy)
    (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp
      exact ⟨[], by simp, fun _ h => by simp at h⟩)
  induction hx with
  | refl => exact h1 id ((Treap.has_ins _ _ _).mpr (Or.inl rfl))
  | step _ hk hw ih => exact h2 _ ih _ hk hw

/-! ## `+cull` -/

theorem cullFold_more : ∀ (l : List (Ident × Unit)) (st : SkaState M R),
    (∀ k, Treap.get (l.foldl cullStep st).ticks k = if k ∈ l.map (·.1) then none else Treap.get st.ticks k) ∧
    (l.foldl cullStep st).next = st.next ∧ (l.foldl cullStep st).tick = st.tick
  | [], st => ⟨fun k => by simp, rfl, rfl⟩
  | x :: l, st => by
    obtain ⟨a1, a2, a3⟩ := cullFold_more l (cullStep st x)
    refine ⟨fun k => ?_, a2, a3⟩
    rw [List.foldl_cons, a1]
    simp only [cullStep, Treap.get_del, List.map_cons, List.mem_cons]
    by_cases h1 : k ∈ l.map (·.1) <;> by_cases h2 : k = x.1 <;> simp [h1, h2]

/-- **What `+cull` does**: it deletes the dead members, those above the root
that the root does not reach, from the stack, `order`, `ticks` and the
graph. -/
theorem cull_eff {n : Nat} {id : Ident} {st st' : SkaState M R} {ab0 rest : List Ident} (hi : SInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cull n id st = some st') :
    ∃ live, liveLoop st (Treap.silt (ab0 ++ [id])) n [id] Treap.empty = some live ∧
      (∀ j, Treap.get st'.order j =
        if j ∈ ab0 ++ [id] ∧ Treap.has live j = false then none else Treap.get st.order j) ∧
      (∀ j, Treap.get st'.g j = if j ∈ ab0 ++ [id] ∧ Treap.has live j = false then none else Treap.get st.g j) ∧
      (∀ j, Treap.get st'.ticks j =
        if j ∈ ab0 ++ [id] ∧ Treap.has live j = false then none else Treap.get st.ticks j) ∧
      st'.stk = st.stk.filter (fun j => !(decide (j ∈ ab0 ++ [id]) && !Treap.has live j)) ∧
      st'.done = st.done ∧ st'.next = st.next ∧ st'.tick = st.tick := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, hab, live, hlive, hst⟩ := h
  obtain ⟨ab0', rest', rfl, hs', _⟩ := above_eq hab
  obtain ⟨rfl, rfl⟩ := nodup_split_unique (hs ▸ hi.nodup) (hs.symm.trans hs')
  refine ⟨live, hlive, ?_⟩
  have hdead : ∀ j, Treap.has (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) j = true ↔
      (j ∈ ab0 ++ [id] ∧ Treap.has live j = false) := by
    intro j
    have e : Treap.has (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) j =
        (Treap.get (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) j).isSome := rfl
    rw [e, Treap.get_dif]
    by_cases hl : Treap.has live j = true
    · simp [hl]
    · have hl' : Treap.has live j = false := by simpa using hl
      rw [if_neg hl, ← Treap.has, Treap.has_silt]
      simp [hl']
  generalize hdd : (Treap.dif (Treap.silt (ab0 ++ [id])) live : M Ident Unit) = dead at hst hdead
  have hL : ∀ k, k ∈ (Treap.rap dead).map (·.1) ↔ (k ∈ ab0 ++ [id] ∧ Treap.has live k = false) :=
    fun k => (mem_rap_keys dead k).trans (hdead k)
  split at hst
  · rename_i hemp
    subst hst
    have hnone : ∀ j, ¬ (j ∈ ab0 ++ [id] ∧ Treap.has live j = false) := by
      intro j hj
      obtain ⟨v, hv⟩ := (Treap.has_iff dead j).mp ((hdead j).mpr hj)
      have := (Treap.mem_tap dead j v).mpr hv
      rw [hemp] at this; cases this
    refine ⟨fun j => by rw [if_neg (hnone j)], fun j => by rw [if_neg (hnone j)],
      fun j => by rw [if_neg (hnone j)], ?_, rfl, rfl, rfl⟩
    symm
    apply List.filter_eq_self.mpr
    intro j _
    have := hnone j
    by_cases h1 : j ∈ ab0 ++ [id] <;> by_cases h2 : Treap.has live j = true <;> simp_all
  · subst hst
    obtain ⟨a1, a2, a3, a4, _⟩ := cullFold_ok (Treap.rap dead)
      { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt dead },
                stk := st.stk.filter (fun i => !Treap.has dead i), moved := Treap.dif st.moved dead }
    obtain ⟨b1, b2, b3⟩ := cullFold_more (Treap.rap dead)
      { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt dead },
                stk := st.stk.filter (fun i => !Treap.has dead i), moved := Treap.dif st.moved dead }
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, ?_, a2, b2, b3⟩
    · rw [a3]; simp only [hL]
    · rw [a4]; simp only [hL]
    · rw [b1]; simp only [hL]
    · rw [a1]
      show List.filter (fun i => !Treap.has dead i) st.stk = _
      congr 1
      funext j
      by_cases h1 : j ∈ ab0 ++ [id] <;> by_cases h2 : Treap.has live j = true
      all_goals
        have h3 := hdead j
        cases e : Treap.has dead j <;> simp_all

/-- The live set is reachable through live identities. -/
theorem liveLoop_reach {st : SkaState M R} {members : M Ident Unit} {a : Ident} {live' : M Ident Unit} :
    ∀ (n : Nat) (q : List Ident) (live : M Ident Unit), liveLoop st members n q live = some live' →
    (∀ x, Treap.has live x = true → Reach st (fun y => Treap.has live' y = true) a x) →
    (∀ x ∈ q, Reach st (fun y => Treap.has live' y = true) a x ∨
      ∃ y, Reach st (fun y => Treap.has live' y = true) a y ∧ x ∈ kids st y) →
    ∀ x, Treap.has live' x = true → Reach st (fun y => Treap.has live' y = true) a x
  | 0, _, _, h, _, _ => by simp [liveLoop] at h
  | n + 1, [], live, h, hL, _ => by
    simp only [liveLoop, Option.some.injEq] at h; subst h; exact hL
  | n + 1, i :: q, live, h, hL, hQ => by
    have hfin := h
    unfold liveLoop at h
    split at h
    · exact liveLoop_reach n q live h hL (fun x hx => hQ x (List.mem_cons_of_mem _ hx))
    · have hli : Treap.has live' i = true :=
        liveLoop_mono n _ _ live' h i ((Treap.has_ins _ _ _).mpr (Or.inl rfl))
      have hri : Reach st (fun y => Treap.has live' y = true) a i := by
        rcases hQ i List.mem_cons_self with h1 | ⟨y, hy, hk⟩
        · exact h1
        · exact Reach.step hy hk hli
      refine liveLoop_reach n _ _ h (fun x hx => ?_) (fun x hx => ?_)
      · rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
        · exact hri
        · exact hL x hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hQ x (List.mem_cons_of_mem _ hx)
        · exact Or.inr ⟨i, hri, hx⟩

theorem liveLoop_sub {st : SkaState M R} {members : M Ident Unit} :
    ∀ (n : Nat) (q : List Ident) (live live' : M Ident Unit), liveLoop st members n q live = some live' →
    (∀ x, Treap.has live x = true → Treap.has members x = true) →
    ∀ x, Treap.has live' x = true → Treap.has members x = true
  | 0, _, _, _, h, _ => by simp [liveLoop] at h
  | n + 1, [], live, live', h, hL => by
    simp only [liveLoop, Option.some.injEq] at h; subst h; exact hL
  | n + 1, i :: q, live, live', h, hL => by
    unfold liveLoop at h
    split at h
    · exact liveLoop_sub n q live live' h hL
    · rename_i hc
      refine liveLoop_sub n _ _ live' h (fun x hx => ?_)
      rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
      · cases e : Treap.has members x
        · exact absurd (Or.inr (by simp [e])) hc
        · rfl
      · exact hL x hx

theorem kids_of_inCallees {st : SkaState M R} {m c : Ident} (h : InCallees (calleesOf st m) c) : c ∈ kids st m := by
  obtain ⟨seat, hs⟩ := h
  obtain ⟨v, hv⟩ := (Treap.has_iff _ _).mp hs
  exact List.mem_map.mpr ⟨(⟨seat, c⟩, v), (Treap.mem_tap _ _ _).mpr hv, rfl⟩

theorem reach_cases {st : SkaState M R} {W : Ident → Prop} {a b : Ident} (h : Reach st W a b) : b = a ∨ W b := by
  cases h with
  | refl => exact Or.inl rfl
  | step _ _ hw => exact Or.inr hw

/-- **`+cull` keeps the convergence invariant**, with the same frozen
entries, given that the members below the root read only below it; it
leaves every member above the root reachable from the root. -/
theorem cull_ok2 {memoF : Memo M} {n : Nat} {id : Ident} {st st' : SkaState M R} {F : Entry → Prop}
    {ab0 rest : List Ident} {index : Nat} (hc : CInv memoF st F) (hs : st.stk = ab0 ++ id :: rest)
    (hidx : Treap.get st.order id = some index)
    (hrest : ∀ m ∈ rest, MemOK st F m index) (h : cull n id st = some st') :
    CInv memoF st' F ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep (id :: rest) (· ∈ id :: rest) st st' ∧
    Frame (· ∈ id :: rest) st st' ∧
    (∀ x, Treap.get st'.order x ≠ none → Treap.get st'.g x = Treap.get st.g x ∧
      Treap.get st'.ticks x = Treap.get st.ticks x ∧ Treap.get st'.order x = Treap.get st.order x) ∧
    (∀ x o, Treap.get st'.order x = some o → x ∉ rest →
      Reach st' (fun y => Treap.get st'.order y ≠ none ∧ y ∉ rest) id x) := by
  obtain ⟨si, sg, sk⟩ := cull_ok hc.s h hs
  obtain ⟨live, hlive, eo, eg, et, es, ed, en, etk⟩ := cull_eff hc.s hs h
  have hnd : (ab0 ++ id :: rest).Nodup := hs ▸ hc.s.nodup
  have hnd2 : ((ab0 ++ [id]) ++ rest).Nodup := by simpa using hnd
  have hmem : ∀ k, Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) k = true ↔ k ∈ ab0 ++ [id] :=
    fun k => Treap.has_silt _ k
  have hid : Treap.has live id = true := liveLoop_head hlive ((hmem id).mpr (by simp))
  -- the dead identities
  let D : Ident → Prop := fun j => j ∈ ab0 ++ [id] ∧ Treap.has live j = false
  have hDo : ∀ j, ¬ D j → Treap.get st'.order j = Treap.get st.order j := fun j hj => by
    rw [eo, if_neg hj]
  have hDg : ∀ j, ¬ D j → Treap.get st'.g j = Treap.get st.g j := fun j hj => by rw [eg, if_neg hj]
  have hDt : ∀ j, ¬ D j → Treap.get st'.ticks j = Treap.get st.ticks j := fun j hj => by rw [et, if_neg hj]
  have hDo' : ∀ j, D j → Treap.get st'.order j = none := fun j hj => by rw [eo, if_pos hj]
  have hDg' : ∀ j, D j → Treap.get st'.g j = none := fun j hj => by rw [eg, if_pos hj]
  have hDt' : ∀ j, D j → Treap.get st'.ticks j = none := fun j hj => by rw [et, if_pos hj]
  have hrestD : ∀ j ∈ rest, ¬ D j := fun j hj hD =>
    (List.nodup_append.mp hnd2).2.2 j hD.1 j hj rfl
  have hidD : ¬ D id := fun hD => by have h2 := hD.2; rw [hid] at h2; cases h2
  have hPstk : ∀ j ∈ ab0 ++ [id], j ∈ st.stk := fun j hj => by
    rw [hs]
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ h
    · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ List.mem_cons_self
  have hfinD : ∀ j, Treap.get st.order j = none → ¬ D j := fun j hj hD => by
    obtain ⟨o, ho⟩ := (hc.s.ord_stk j).mpr (hPstk j hD.1)
    rw [hj] at ho; cases ho
  have hsurv : ∀ x, Treap.get st'.order x ≠ none → ¬ D x := fun x hx hD => hx (hDo' x hD)
  have hran : ∀ x, ¬ D x → ranOf st' x = ranOf st x := fun x hx => by simp only [ranOf, Treap.gut, hDt x hx]
  have hchg : ∀ x, ¬ D x → chgOf st' x = chgOf st x := fun x hx => by simp only [chgOf, Treap.gut, hDt x hx]
  have hcal : ∀ x, ¬ D x → calleesOf st' x = calleesOf st x := fun x hx => by
    simp only [calleesOf, gitG, Treap.gut, hDg x hx]
  -- the closure of the live set
  have hclosed := liveLoop_closed n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx)
  obtain ⟨hup, hdown⟩ := ordInv_split hc.ord hs hidx
  -- the members keep their answers
  have hmemOK : ∀ m L Lm, ¬ D m → MemOK st F m L → (∀ c, InCallees (calleesOf st m) c → ∀ o,
      Treap.get st.order c = some o → o < L → ¬ D c) → L ≤ Lm → MemOK st' F m Lm := by
    intro m L Lm hm h hw hL
    intro d hd hr
    rw [hDg m hm] at hd; rw [hran m hm] at hr
    obtain ⟨P, L', hL', hrun, hP⟩ := h d hd hr
    refine ⟨P, L', Nat.le_trans hL' hL, hrun, fun s f a hp => (hP s f a hp).mono (fun e he => ?_)⟩
    rcases he with he | ⟨hce, ⟨o, hco, hlt⟩, htab⟩
    · exact Or.inl he
    · have hcD := hw _ hce o hco (Nat.lt_of_lt_of_le hlt hL')
      refine Or.inr ⟨by rw [hcal m hm]; exact hce, ⟨o, by rw [hDo _ hcD]; exact hco, hlt⟩, fun hlt' => ?_⟩
      rw [hchg _ hcD, hran m hm] at hlt'
      obtain ⟨dc, hdc, htc⟩ := htab hlt'
      exact ⟨dc, by rw [hDg _ hcD]; exact hdc, htc⟩
  refine ⟨⟨si, fun m => ?_, ⟨fun i o hio => ?_, ?_⟩, ⟨hc.frz.ok, fun i d h1 h2 => ?_, fun e he => ?_, hc.frz.wf,
    fun f ms s ent h1 h2 => ?_⟩, fun m o hmo => ?_, fun j hj => ?_⟩, sg, sk, ⟨fun i d h1 h2 => ?_, fun j hj => ?_,
    by rw [en]; exact Nat.le_refl _, by rw [etk]; exact Nat.le_refl _, fun x o hxo hx => ?_⟩, fun x hx => ?_,
    fun x o hxo hx => ?_⟩
  · -- ticks
    by_cases hm : D m
    · simp only [ranOf, chgOf, Treap.gut, hDt' m hm, etk]; simp
    · rw [hran m hm, hchg m hm, etk]; exact hc.tick m
  · by_cases hi : D i
    · rw [hDo' i hi] at hio; cases hio
    · rw [hDo i hi] at hio; rw [en]; exact hc.ord.1 i o hio
  · rw [es]
    refine (List.Pairwise.filter _ hc.ord.2).imp_of_mem (fun {a b} ha hb hab oa ob h1 h2 => ?_)
    have ha' : ¬ D a := fun hD => by
      have := (List.mem_filter.mp ha).2
      simp [hD.1, hD.2] at this
    have hb' : ¬ D b := fun hD => by
      have := (List.mem_filter.mp hb).2
      simp [hD.1, hD.2] at this
    rw [hDo a ha'] at h1; rw [hDo b hb'] at h2
    exact hab oa ob h1 h2
  · by_cases hi : D i
    · rw [hDg' i hi] at h1; cases h1
    · rw [hDg i hi] at h1; rw [hDo i hi] at h2; exact hc.frz.cover i d h1 h2
  · obtain ⟨⟨d, hd⟩, ho⟩ := hc.frz.sub e he
    have hn := hfinD _ ho
    exact ⟨⟨d, by rw [hDg _ hn]; exact hd⟩, by rw [hDo _ hn]; exact ho⟩
  · rw [ed] at h1
    obtain ⟨hF, hk, hge⟩ := hc.frz.done f ms s ent h1 h2
    have hn : ¬ D ent.1 := hfinD _ (by simpa [entOf] using (hc.frz.sub _ hF).2)
    exact ⟨hF, hk, by rw [hDg _ hn]; exact hge⟩
  · -- the members
    have hm := hsurv m (by rw [hmo]; simp)
    rw [hDo m hm] at hmo
    rw [en]
    have hms : m ∈ st.stk := (hc.s.ord_stk m).mp ⟨o, hmo⟩
    rw [hs] at hms
    simp only [List.mem_append, List.mem_cons] at hms
    by_cases hmr : m ∈ rest
    · refine hmemOK m index _ hm (hrest m hmr) (fun c _ oc hco hlt hcD => ?_)
        (Nat.le_of_lt (hc.ord.1 id index hidx))
      have := hup c hcD.1 oc hco
      omega
    · have hml : m ∈ ab0 ++ [id] := by
        rcases hms with h | rfl | h
        · simp [h]
        · simp
        · exact absurd h hmr
      have hlm : Treap.has live m = true := by
        cases e : Treap.has live m
        · exact absurd ⟨hml, e⟩ hm
        · rfl
      refine hmemOK m st.next _ hm (hc.mem m o hmo) (fun c hce oc hco _ hcD => ?_) (Nat.le_refl _)
      have := hclosed m hlm c (kids_of_inCallees hce) ((hmem c).mpr hcD.1)
      have h2 := hcD.2
      rw [this] at h2; cases h2
  · -- the keys of the ticks
    by_cases hjD : D j
    · rw [hDt' j hjD] at hj; exact absurd rfl hj
    · rw [hDt j hjD] at hj; rw [hDo j hjD]; exact hc.tkeys j hj
  · -- frame: finalized
    have hn := hfinD i h2
    exact ⟨by rw [hDg i hn]; exact h1, by rw [hDo i hn]; exact h2⟩
  · -- frame: ticks
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hDt _ hidD
    · exact hDt j (hrestD j hj)
  · -- frame: no new members
    have hxD := hsurv x (by rw [hxo]; simp)
    rw [hDo x hxD] at hxo
    exact absurd ((hc.s.ord_stk x).mp ⟨o, hxo⟩) hx
  · have hxD := hsurv x hx
    exact ⟨hDg x hxD, hDt x hxD, hDo x hxD⟩
  · -- reachability
    have hxD := hsurv x (by rw [hxo]; simp)
    rw [hDo x hxD] at hxo
    have hxs : x ∈ st.stk := (hc.s.ord_stk x).mp ⟨o, hxo⟩
    have hxl : x ∈ ab0 ++ [id] := by
      rw [hs] at hxs
      simp only [List.mem_append, List.mem_cons] at hxs
      rcases hxs with h | rfl | h
      · simp [h]
      · simp
      · exact absurd h hx
    have hlx : Treap.has live x = true := by
      cases e : Treap.has live x
      · exact absurd ⟨hxl, e⟩ hxD
      · rfl
    have hR := liveLoop_reach n [id] Treap.empty hlive (fun y hy => by simp [Treap.has, Treap.get_empty] at hy)
      (fun y hy => by simp at hy; subst hy; exact Or.inl Reach.refl) x hlx
    have hsub := liveLoop_sub n [id] Treap.empty live hlive (fun y hy => by simp [Treap.has, Treap.get_empty] at hy)
    -- carry the path over to `st'`
    have key : ∀ y, Reach st (fun y => Treap.has live y = true) id y →
        Reach st' (fun y => Treap.get st'.order y ≠ none ∧ y ∉ rest) id y := by
      intro y hy
      induction hy with
      | refl => exact Reach.refl
      | @step b c hr hk hw ih =>
        have hbD : ¬ D b := by
          rcases reach_cases hr with rfl | hb
          · exact hidD
          · intro hD; have h2 := hD.2; rw [hb] at h2; cases h2
        have hcD : ¬ D c := fun hD => by have h2 := hD.2; rw [hw] at h2; cases h2
        have hcl : c ∈ ab0 ++ [id] := (hmem c).mp (hsub c hw)
        refine Reach.step ih ?_ ⟨?_, ?_⟩
        · unfold kids; rw [show gitG st'.g b = gitG st.g b by simp only [gitG, Treap.gut, hDg b hbD]]; exact hk
        · obtain ⟨oc, hoc⟩ := (hc.s.ord_stk c).mpr (hPstk c hcl)
          rw [hDo c hcD, hoc]; simp
        · exact fun hcr => (List.nodup_append.mp hnd2).2.2 c hcl c hcr rfl
    exact key x hR

end Ana
end SkaModel
end Formalization
