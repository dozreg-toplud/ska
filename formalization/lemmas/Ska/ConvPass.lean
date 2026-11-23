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

/-! ## The member loop -/

theorem dirty_eq (m : Ident) (st : SkaState M R) :
    dirty m st = (Treap.tap (calleesOf st m)).any (fun ce => decide (ranOf st m ≤ chgOf st ce.1.id)) := rfl

/-- A member that is not dirty: its callees changed before its last run. -/
theorem not_dirty {m : Ident} {st : SkaState M R} (h : dirty m st = false) :
    ∀ c, InCallees (calleesOf st m) c → chgOf st c < ranOf st m := by
  intro c ⟨seat, hs⟩
  rw [dirty_eq, List.any_eq_false] at h
  obtain ⟨v, hv⟩ := (Treap.has_iff _ _).mp hs
  have := h (⟨seat, c⟩, v) ((Treap.mem_tap _ _ _).mpr hv)
  simp only [decide_eq_true_eq] at this
  omega

theorem dirty_false_of {m : Ident} {st : SkaState M R}
    (h : ∀ c, InCallees (calleesOf st m) c → chgOf st c < ranOf st m) : dirty m st = false := by
  rw [dirty_eq, List.any_eq_false]
  intro ce hce
  have hin : InCallees (calleesOf st m) ce.1.id :=
    ⟨ce.1.seat, (Treap.has_iff _ _).mpr ⟨ce.2, (Treap.mem_tap _ _ _).mp (by simpa using hce)⟩⟩
  have := h _ hin
  simp only [decide_eq_true_eq]
  omega

/-- What the member loop of a pass at the root `id` keeps and gives: the
members below the root keep their answers with the bound `index`; every
member above the root has run and reads nothing below the `low` it returns;
and in a pass with no change and no new function, the members listed are not
dirty at the end, and nothing else moved. -/
def MemP2 (memoF : Memo M) (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st' (F : Entry → Prop) (ab0 rest : List Ident) (id : Ident),
    CInv memoF st F → st.stk = ab0 ++ id :: rest → Treap.get st.order id = some index →
    (∀ m ∈ ms, m ∈ st.stk ∧ m ∉ rest) → (∀ m ∈ rest, MemOK st F m index) →
    (∀ x o, Treap.get st.order x = some o → x ∉ rest → 1 ≤ ranOf st x ∧ LowB st x index) →
    mem index pass ms st = some (r, st') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F' ∧ ∀ m ∈ rest, MemOK st' F' m index) ∧
    GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ rest) st st' ∧ Frame (· ∈ rest) st st' ∧
    r.1 ≤ index ∧ (∀ x o, Treap.get st'.order x = some o → x ∉ rest → 1 ≤ ranOf st' x ∧ LowB st' x r.1) ∧
    (r.1 = index → r.2 = false → st'.next = st.next →
      (∀ x, Treap.get st'.order x = Treap.get st.order x) ∧ (∀ j, chgOf st' j = chgOf st j) ∧
      (∀ j ∈ st.stk, j ∉ ms → ranOf st' j = ranOf st j ∧ calleesOf st' j = calleesOf st j) ∧
      ∀ m ∈ ms, dirty m st' = false)

theorem lowB_mono {st : SkaState M R} {x : Ident} {a b : Nat} (h : LowB st x b) (hab : a ≤ b) : LowB st x a :=
  fun c hc o ho => Nat.le_trans hab (h c hc o ho)

/-- The part of the member loop after the dirty check, at `st1`, which is
`st` up to the statistics. -/
theorem member_tail2 {memoF : Memo M} {run : RunGo M R} {mem : MemGo M R} (hrun : RunP2 memoF run)
    (hmem : MemP2 memoF mem) {index pass : Nat} {m : Ident} {ms : List Ident} {st st1 st' : SkaState M R}
    {r : Nat × Bool} {F : Entry → Prop} {ab0 rest : List Ident} {id : Ident}
    (hc : CInv memoF st F) (hs : st.stk = ab0 ++ id :: rest) (hidx : Treap.get st.order id = some index)
    (hm : m ∈ st.stk ∧ m ∉ rest) (hms : ∀ m ∈ ms, m ∈ st.stk ∧ m ∉ rest)
    (hrest : ∀ m ∈ rest, MemOK st F m index)
    (hcl : ∀ x o, Treap.get st.order x = some o → x ∉ rest → 1 ≤ ranOf st x ∧ LowB st x index)
    (h1 : st1.g = st.g) (h2 : st1.done = st.done) (h3 : st1.order = st.order) (h4 : st1.stk = st.stk)
    (h5 : st1.next = st.next) (h6 : st1.tick = st.tick) (h7 : st1.ticks = st.ticks)
    (e : ((Treap.get st.order m).bind fun o => (run m o st1).bind fun q =>
      if q.1.1 < index then some ((q.1.1, q.1.2.2), q.2) else
      (mem index pass ms q.2).map fun t => ((min q.1.1 t.1.1, q.1.2.2 || t.1.2), t.2)) = some (r, st')) :
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F' ∧ ∀ m ∈ rest, MemOK st' F' m index) ∧
    GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ rest) st st' ∧ Frame (· ∈ rest) st st' ∧
    r.1 ≤ index ∧ (∀ x o, Treap.get st'.order x = some o → x ∉ rest → 1 ≤ ranOf st' x ∧ LowB st' x r.1) ∧
    (r.1 = index → r.2 = false → st'.next = st.next →
      (∀ x, Treap.get st'.order x = Treap.get st.order x) ∧ (∀ j, chgOf st' j = chgOf st j) ∧
      (∀ j ∈ st.stk, j ∉ m :: ms → ranOf st' j = ranOf st j ∧ calleesOf st' j = calleesOf st j) ∧
      dirty m st' = false ∧ ∀ m' ∈ ms, dirty m' st' = false) := by
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
  have c1 : CInv memoF st1 F := hc.congr h1 h2 h3 h4 h5 h6 h7
  obtain ⟨⟨F2, hF2, c2, hmo2⟩, s2, k2, fr2, hran2, htick2, hch2, _, hlow2, hlb2, hpush2, _⟩ :=
    hrun m o st1 r1 st2 F c1 (by rw [h4]; exact hm.1) (by rw [h3]; exact ho) hr
  have hrest1 : ∀ x ∈ rest, MemOK st1 F x index := fun x hx => memOK_congr h1 h3 h7 (hrest x hx)
  have hrest2 : ∀ x ∈ rest, MemOK st2 F2 x index := fun x hx =>
    hmo2 x index (by rw [h4, hs]; simp [hx]) (fun e => hm.2 (e ▸ hx)) (hrest1 x hx)
  have hS1 : ∀ j ∈ st.stk, j ≠ m → Treap.get st2.g j = Treap.get st.g j ∧
      Treap.get st2.order j = Treap.get st.order j ∧ Treap.get st2.ticks j = Treap.get st.ticks j := by
    intro j hj hjm
    refine ⟨by rw [k2.2.2 j ⟨by rw [h4]; exact hj, hjm⟩, h1], by rw [k2.2.1 j (by rw [h4]; exact hj), h3],
      by rw [fr2.ticks j ⟨by rw [h4]; exact hj, hjm⟩, h7]⟩
  have hordm : Treap.get st2.order m = Treap.get st.order m := by rw [k2.2.1 m (by rw [h4]; exact hm.1), h3]
  have hst2 : ∃ l, st2.stk = l ++ st.stk := by obtain ⟨l, el⟩ := k2.1; exact ⟨l, by rw [el, h4]⟩
  have hnew : ∀ c oc, Treap.get st2.order c = some oc → c ∉ st.stk → st.next ≤ oc := fun c oc hco hcn => by
    have := fr2.newOrd c oc hco (by rw [h4]; exact hcn); rw [h5] at this; exact this
  have hidx0 : index < st.next := hc.ord.1 id index hidx
  have hcalm : ∀ j ∈ st.stk, j ≠ m → calleesOf st2 j = calleesOf st j := fun j hj hjm => by
    simp only [calleesOf, gitG, Treap.gut, (hS1 j hj hjm).1]
  have hranj : ∀ j ∈ st.stk, j ≠ m → ranOf st2 j = ranOf st j := fun j hj hjm => by
    simp only [ranOf, Treap.gut, (hS1 j hj hjm).2.2]
  have hchgj : ∀ j ∈ st.stk, j ≠ m → chgOf st2 j = chgOf st j := fun j hj hjm => by
    simp only [chgOf, Treap.gut, (hS1 j hj hjm).2.2]
  -- the members after the run read nothing below `low` of the run
  have hcl2 : ∀ L, L ≤ index → L ≤ r1.1 → ∀ x ox, Treap.get st2.order x = some ox → x ∉ rest →
      1 ≤ ranOf st2 x ∧ LowB st2 x L := by
    intro L hL hL' x ox hxo hxr
    by_cases hxs : x ∈ st.stk
    · by_cases hxm : x = m
      · subst hxm
        refine ⟨by rw [hran2]; have := htick2; omega, lowB_mono hlb2 hL'⟩
      · have hox : Treap.get st.order x = some ox := by rw [← (hS1 x hxs hxm).2.1]; exact hxo
        obtain ⟨hr0, hlb0⟩ := hcl x ox hox hxr
        refine ⟨by rw [hranj x hxs hxm]; exact hr0, fun c hce oc hco => ?_⟩
        rw [hcalm x hxs hxm] at hce
        by_cases hcs : c ∈ st.stk
        · by_cases hcm : c = m
          · subst hcm; rw [hordm] at hco; exact Nat.le_trans hL (hlb0 c hce oc hco)
          · rw [(hS1 c hcs hcm).2.1] at hco; exact Nat.le_trans hL (hlb0 c hce oc hco)
        · have := hnew c oc hco hcs; omega
    · exact ⟨(hpush2 x ox hxo (by rw [h4]; exact hxs)).1,
        lowB_mono (hpush2 x ox hxo (by rw [h4]; exact hxs)).2 hL'⟩
  have hkeep2 : Keep st.stk (· ∈ rest) st st2 := by
    obtain ⟨l, el⟩ := hst2
    refine ⟨⟨l, el⟩, fun j hj => by rw [k2.2.1 j (by rw [h4]; exact hj), h3], fun j hj => ?_⟩
    have hjs : j ∈ st.stk := by rw [hs]; simp [hj]
    exact (hS1 j hjs (fun e => hm.2 (e ▸ hj))).1
  have hfr2 : Frame (· ∈ rest) st st2 := by
    refine ⟨fun i d a b => ?_, fun j hj => ?_, by rw [← h5]; exact fr2.next, by rw [← h6]; exact fr2.tick,
      fun x ox hxo hx => ?_⟩
    · exact fr2.fin i d (by rw [h1]; exact a) (by rw [h3]; exact b)
    · have hjs : j ∈ st.stk := by rw [hs]; simp [hj]
      exact (hS1 j hjs (fun e => hm.2 (e ▸ hj))).2.2
    · rw [← h5]; exact fr2.newOrd x ox hxo (by rw [h4]; exact hx)
  split at e
  · -- the run reached below the root: the pass stops
    rename_i hlt
    simp only at hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨⟨F2, hF2, c2, hrest2⟩, by rw [← h1]; exact s2, hkeep2, hfr2, by omega,
      hcl2 r1.1 (by omega) (Nat.le_refl _), fun h => absurd h (by omega)⟩
  · rename_i hge
    simp only at hge
    simp only [Option.map_eq_some_iff] at e
    obtain ⟨⟨t, st3⟩, ht, e⟩ := e
    cases e
    have hst2' : st2.stk = ((st2.stk.take (st2.stk.length - st.stk.length)) ++ ab0) ++ id :: rest := by
      obtain ⟨l, el⟩ := hst2
      rw [el, hs]; simp
    obtain ⟨⟨F3, hF3, c3, hrest3⟩, s3, k3, fr3, hlow3, hcl3, hstab3⟩ :=
      hmem index pass ms st2 t st3 F2 _ rest id c2 hst2'
        (by rw [k2.2.1 id (by rw [h4, hs]; simp), h3]; exact hidx)
        (fun m' hm' => by
          obtain ⟨hm1, hm2⟩ := hms m' hm'
          obtain ⟨l, el⟩ := hst2
          exact ⟨by rw [el]; exact List.mem_append_right _ hm1, hm2⟩)
        hrest2 (hcl2 index (Nat.le_refl _) (by omega)) ht
    have hk23 : Keep st.stk (· ∈ rest) st st3 := by
      obtain ⟨l, el⟩ := hst2
      refine hkeep2.trans (k3.weaken ⟨l, el⟩ (fun j hj => hj))
    refine ⟨⟨F3, fun e he => hF3 e (hF2 e he), c3, hrest3⟩, gStepsR_trans (by rw [← h1]; exact s2) s3, hk23,
      hfr2.trans fr3 (fun j hj => hj) k3.2.1 c2.s, by simp only; omega,
      fun x ox hxo hxr => ⟨(hcl3 x ox hxo hxr).1, lowB_mono (hcl3 x ox hxo hxr).2 (Nat.min_le_right _ _)⟩, ?_⟩
    intro hidx' hch hnx
    simp only at hidx' hch hnx
    have hchb : r1.2.2 = false ∧ t.2 = false := by simpa using hch
    obtain ⟨hch1, hch2'⟩ := hchb
    have ht1 : t.1 = index := by have := Nat.min_le_right r1.1 t.1; omega
    have hn12 : st2.next = st.next := by
      have a := fr2.next; have b := fr3.next; rw [h5] at a; omega
    obtain ⟨o3, c3', rc3, d3⟩ := hstab3 ht1 hch2' (by rw [hnx, hn12])
    -- the run made no new member and no change
    have hord2 : ∀ x, Treap.get st2.order x = Treap.get st.order x := by
      intro x
      by_cases hxs : x ∈ st.stk
      · by_cases hxm : x = m
        · rw [hxm, hordm]
        · exact (hS1 x hxs hxm).2.1
      · cases hx2 : Treap.get st2.order x with
        | none =>
          cases hx1 : Treap.get st.order x with
          | none => rfl
          | some ox => exact absurd ((hc.s.ord_stk x).mp ⟨ox, hx1⟩) hxs
        | some ox =>
          have a := hnew x ox hx2 hxs
          have b := c2.ord.1 x ox hx2
          omega
    have hchg2 : ∀ j, chgOf st2 j = chgOf st j := by
      intro j
      by_cases hjs : j ∈ st.stk
      · by_cases hjm : j = m
        · subst hjm
          rw [(hch2 hch1).1]
          simp only [chgOf, Treap.gut, h7]
        · exact hchgj j hjs hjm
      · have hn1 : Treap.get st.order j = none := by
          cases e1 : Treap.get st.order j with
          | none => rfl
          | some oj => exact absurd ((hc.s.ord_stk j).mp ⟨oj, e1⟩) hjs
        have t1 : Treap.get st.ticks j = none := by
          cases e2 : Treap.get st.ticks j with
          | none => rfl
          | some v => exact absurd hn1 (hc.tkeys j (by rw [e2]; simp))
        have t2 : Treap.get st2.ticks j = none := by
          cases e2 : Treap.get st2.ticks j with
          | none => rfl
          | some v => exact absurd (by rw [hord2 j]; exact hn1) (c2.tkeys j (by rw [e2]; simp))
        simp only [chgOf, Treap.gut, t1, t2]
    have hdm2 : dirty m st2 = false := by
      apply dirty_false_of
      intro c _
      rw [hran2, hchg2 c]
      have := (hc.tick c).2
      have := htick2
      rw [h6] at this
      omega
    refine ⟨fun x => by rw [o3, hord2], fun j => by rw [c3', hchg2], fun j hj hjn => ?_, ?_, d3⟩
    · have hjm : j ≠ m := fun e => hjn (e ▸ List.mem_cons_self)
      have hjms : j ∉ ms := fun h => hjn (List.mem_cons_of_mem _ h)
      obtain ⟨l, el⟩ := hst2
      obtain ⟨a1, a2⟩ := rc3 j (by rw [el]; exact List.mem_append_right _ hj) hjms
      exact ⟨by rw [a1, hranj j hj hjm], by rw [a2, hcalm j hj hjm]⟩
    · by_cases hmm : m ∈ ms
      · exact d3 m hmm
      · obtain ⟨l, el⟩ := hst2
        obtain ⟨a1, a2⟩ := rc3 m (by rw [el]; exact List.mem_append_right _ hm.1) hmm
        rw [dirty_eq, a1, a2]
        have hc3 : (fun ce : CalleeEntry × Unit => decide (ranOf st2 m ≤ chgOf st3 ce.1.id)) =
            (fun ce => decide (ranOf st2 m ≤ chgOf st2 ce.1.id)) := by funext ce; rw [c3']
        rw [hc3, ← dirty_eq]; exact hdm2

theorem dirty_congr {m : Ident} {st st' : SkaState M R} (h1 : ranOf st' m = ranOf st m)
    (h2 : calleesOf st' m = calleesOf st m) (h3 : ∀ j, chgOf st' j = chgOf st j) : dirty m st' = dirty m st := by
  rw [dirty_eq, dirty_eq, h1, h2]
  have : (fun ce : CalleeEntry × Unit => decide (ranOf st m ≤ chgOf st' ce.1.id)) =
      (fun ce => decide (ranOf st m ≤ chgOf st ce.1.id)) := by funext ce; rw [h3]
  rw [this]

/-- **The member loop keeps the convergence invariant.** -/
theorem memberStep_ok2 {memoF : Memo M} {run : RunGo M R} {mem : MemGo M R} (hrun : RunP2 memoF run)
    (hmem : MemP2 memoF mem) : MemP2 memoF (memberStep run mem) := by
  intro index pass ms st r st' F ab0 rest id hc hs hidx hms hrest hcl e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨⟨F, fun _ h => h, hc, hrest⟩, GStepsR.refl _, Keep.refl' _ rfl rfl rfl,
      Frame.refl' rfl rfl rfl rfl rfl rfl hc.s, Nat.le_refl _, hcl,
      fun _ _ _ => ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ h => by simp at h⟩⟩
  | cons m ms =>
    have hm := hms m List.mem_cons_self
    have hms' : ∀ m' ∈ ms, m' ∈ st.stk ∧ m' ∉ rest := fun m' h => hms m' (List.mem_cons_of_mem _ h)
    simp only [memberStep] at e
    split at e
    · rename_i hd
      obtain ⟨A, B, C, D, E, G, H⟩ := hmem index pass ms st r st' F ab0 rest id hc hs hidx hms' hrest hcl e
      refine ⟨A, B, C, D, E, G, fun h1 h2 h3 => ?_⟩
      obtain ⟨o1, o2, o3, o4⟩ := H h1 h2 h3
      refine ⟨o1, o2, fun j hj hjn => o3 j hj (fun h => hjn (List.mem_cons_of_mem _ h)), fun m' hm' => ?_⟩
      rcases List.mem_cons.mp hm' with rfl | hm'
      · by_cases hmm : m' ∈ ms
        · exact o4 m' hmm
        · obtain ⟨a1, a2⟩ := o3 m' hm.1 hmm
          rw [dirty_congr a1 a2 o2]; exact hd
      · exact o4 m' hm'
    · have fin : ∀ (st1 : SkaState M R), st1.g = st.g → st1.done = st.done → st1.order = st.order →
          st1.stk = st.stk → st1.next = st.next → st1.tick = st.tick → st1.ticks = st.ticks →
          ((Treap.get st.order m).bind fun o => (run m o st1).bind fun q =>
            if q.1.1 < index then some ((q.1.1, q.1.2.2), q.2) else
            (mem index pass ms q.2).map fun t => ((min q.1.1 t.1.1, q.1.2.2 || t.1.2), t.2)) = some (r, st') →
          (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F' ∧ ∀ m ∈ rest, MemOK st' F' m index) ∧
          GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ rest) st st' ∧ Frame (· ∈ rest) st st' ∧
          r.1 ≤ index ∧ (∀ x o, Treap.get st'.order x = some o → x ∉ rest → 1 ≤ ranOf st' x ∧ LowB st' x r.1) ∧
          (r.1 = index → r.2 = false → st'.next = st.next →
            (∀ x, Treap.get st'.order x = Treap.get st.order x) ∧ (∀ j, chgOf st' j = chgOf st j) ∧
            (∀ j ∈ st.stk, j ∉ m :: ms → ranOf st' j = ranOf st j ∧ calleesOf st' j = calleesOf st j) ∧
            ∀ m' ∈ m :: ms, dirty m' st' = false) := by
        intro st1 h1 h2 h3 h4 h5 h6 h7 e
        obtain ⟨A, B, C, D, E, G, H⟩ := member_tail2 hrun hmem hc hs hidx hm hms' hrest hcl h1 h2 h3 h4 h5 h6 h7 e
        refine ⟨A, B, C, D, E, G, fun a b c => ?_⟩
        obtain ⟨o1, o2, o3, o4, o5⟩ := H a b c
        exact ⟨o1, o2, o3, fun m' hm' => by
          rcases List.mem_cons.mp hm' with rfl | hm'
          · exact o4
          · exact o5 m' hm'⟩
      by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact fin { st with stats := { st.stats with lateRuns := st.stats.lateRuns + 1 } }
          rfl rfl rfl rfl rfl rfl rfl e
      · simp only [hp, if_false] at e
        exact fin _ rfl rfl rfl rfl rfl rfl rfl e

end Ana
end SkaModel
end Formalization
