import lemmas.Ska.Tarjan

/-!
# `tarjanM` returns, and its components partition the vertices

The invariant of the state, in the arm's own terms (`TjInv`):

* `cur v` holds exactly when `v` is on the stack;
* every visited vertex occurs once in the stack and the emitted components
  together, and an unvisited one never (`count`).

What a `connect` from `s` keeps and makes (`TjExt s s'`): the indices of
`s` stay; a vertex it visits gets an index at least `s.idx`; the stack is
the old one under new vertices.  Its `lowest` is `s.idx` or the index of a
vertex of the OLD stack (`TjLoB`), and when it is `s.idx` the stack is back
to the old one (the pop).  Every vertex it visits has all its kids visited
(`TjClo`).  The fuel bounds the number of unvisited vertices (`tjMeas`).

So from the empty state every root pops to the empty stack, and at the end
the stack is empty, every vertex is visited (`tjVerts G`: the keys and their
kids), and the components hold each vertex exactly once:

* **`tarjanM_total`**: `tarjanM G` returns on every nonempty graph with
  distinct keys;
* **`tarjanM_count`**: and each vertex occurs exactly once in the flattened
  result, nothing else occurs.
-/

namespace Formalization
namespace Tarjan

variable {V : Type} [DecidableEq V]

set_option linter.unusedSectionVars false

/-- The vertices: the keys and their kids. -/
def tjVerts : Gr V → List V
  | [] => []
  | p :: G => p.1 :: (p.2 ++ tjVerts G)

/-- The number of unvisited vertices of `U` (with repetitions). -/
def tjMeas (U : List V) (s : St V) : Nat := U.countP fun u => (s.vis u).isNone

/-- The invariant of the state. -/
structure TjInv (s : St V) : Prop where
  cur : ∀ u, s.cur u = true ↔ u ∈ s.stk
  count : ∀ u, (s.stk ++ s.fin.flatten).count u = if (s.vis u).isSome then 1 else 0

/-- What a step from `s` to `s'` keeps. -/
structure TjExt (s s' : St V) : Prop where
  vis_ext : ∀ u i, s.vis u = some i → s'.vis u = some i
  vis_new : ∀ u i, s.vis u = none → s'.vis u = some i → s.idx ≤ i
  idx_le : s.idx ≤ s'.idx
  stk : ∃ X, s'.stk = X ++ s.stk ∧ ∀ x ∈ X, s.vis x = none

/-- Visited vertices are vertices of `U`. -/
def TjInU (U : List V) (s : St V) : Prop := ∀ u, (s.vis u).isSome → u ∈ U

/-- Every vertex visited from `s` to `s'` has its kids visited in `s'`. -/
def TjClo (G : Gr V) (s s' : St V) : Prop :=
  ∀ u, s.vis u = none → (s'.vis u).isSome → ∀ w ∈ kidsOf G u, (s'.vis w).isSome

/-- The bound on `lowest`, against the state before `enter`. -/
def TjLoB (s : St V) (lo : Nat) : Prop :=
  lo ≤ s.idx ∧ (lo = s.idx ∨ ∃ w ∈ s.stk, s.vis w = some lo)

/-! ## Small facts -/

theorem tjExt_refl (s : St V) : TjExt s s :=
  ⟨fun _ _ h => h, fun _ _ h h' => (by rw [h] at h'; cases h'), Nat.le_refl _, ⟨[], rfl, by simp⟩⟩

theorem tjExt_trans {s1 s2 s3 : St V} (a : TjExt s1 s2) (b : TjExt s2 s3) : TjExt s1 s3 := by
  refine ⟨fun u i h => b.vis_ext u i (a.vis_ext u i h), fun u i h h3 => ?_, Nat.le_trans a.idx_le b.idx_le, ?_⟩
  · cases e : s2.vis u with
    | none => exact Nat.le_trans a.idx_le (b.vis_new u i e h3)
    | some j =>
      have hij : j = i := Option.some.inj ((b.vis_ext u j e).symm.trans h3)
      subst hij
      exact a.vis_new u j h e
  · obtain ⟨X1, h1, n1⟩ := a.stk
    obtain ⟨X2, h2, n2⟩ := b.stk
    refine ⟨X2 ++ X1, by rw [h2, h1, List.append_assoc], fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · have h2x := n2 x hx
      cases e : s1.vis x with
      | none => rfl
      | some j => rw [a.vis_ext x j e] at h2x; cases h2x
    · exact n1 x hx

theorem tjClo_trans {G : Gr V} {s1 s2 s3 : St V} (a : TjExt s2 s3) (c1 : TjClo G s1 s2) (c2 : TjClo G s2 s3) :
    TjClo G s1 s3 := by
  intro u h1 h3 w hw
  cases e : s2.vis u with
  | none => exact c2 u e h3 w hw
  | some j =>
    have hw2 := c1 u h1 (by rw [e]; rfl) w hw
    cases e2 : s2.vis w with
    | none => rw [e2] at hw2; cases hw2
    | some k => rw [a.vis_ext w k e2]; rfl

theorem tjMeas_le {U : List V} {s s' : St V} (h : ∀ u i, s.vis u = some i → s'.vis u = some i) :
    tjMeas U s' ≤ tjMeas U s := by
  unfold tjMeas
  apply List.countP_mono_left
  intro x _ hx
  cases e : s.vis x with
  | none => rfl
  | some i => rw [h x i e] at hx; cases hx

theorem countP_lt_of {l : List V} {p q : V → Bool} (h : ∀ x ∈ l, q x = true → p x = true) {v : V}
    (hv : v ∈ l) (hp : p v = true) (hq : q v = false) : l.countP q < l.countP p := by
  induction l with
  | nil => cases hv
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons]
    have hl : l.countP q ≤ l.countP p := List.countP_mono_left fun x hx => h x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.1 hv with rfl | hv
    · simp [hp, hq]; omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hv
      by_cases hqa : q a = true
      · simp [hqa, h a List.mem_cons_self hqa]; omega
      · simp [hqa]; split <;> omega

theorem tjMeas_enter {U : List V} {s : St V} {v : V} (hv : v ∈ U) (hn : s.vis v = none) :
    tjMeas U (enter v s) < tjMeas U s := by
  unfold tjMeas
  refine countP_lt_of (fun x _ hx => ?_) hv (by simp [hn]) (by simp [enter])
  simp only [enter] at hx
  by_cases e : x = v
  · simp [e] at hx
  · simpa [e] using hx

theorem count_le_one_stk {s : St V} (hI : TjInv s) (u : V) : s.stk.count u ≤ 1 := by
  have := hI.count u
  rw [List.count_append] at this
  split at this <;> omega

theorem vis_of_stk {s : St V} (hI : TjInv s) {u : V} (hu : u ∈ s.stk) : (s.vis u).isSome := by
  have h := hI.count u
  rw [List.count_append] at h
  have : 0 < s.stk.count u := List.count_pos_iff.2 hu
  cases e : (s.vis u).isSome
  · rw [e] at h; simp at h; omega
  · rfl

/-! ## `enter` -/

theorem tjInv_enter {s : St V} (hI : TjInv s) {v : V} (hn : s.vis v = none) : TjInv (enter v s) := by
  constructor
  · intro u
    simp only [enter, List.mem_cons]
    by_cases e : u = v
    · simp [e]
    · simp [e, hI.cur u]
  · intro u
    simp only [enter, List.cons_append, List.count_cons]
    have h := hI.count u
    by_cases e : u = v
    · subst e
      rw [hn] at h
      simp only [Option.isSome_none] at h
      simp [h]
    · have : (v == u) = false := by simp [Ne.symm e]
      simp [e, this, h]

theorem tjExt_enter (s : St V) {v : V} (hn : s.vis v = none) : TjExt s (enter v s) := by
  refine ⟨fun u i h => ?_, fun u i h h' => ?_, by simp [enter], ⟨[v], rfl, by simp [hn]⟩⟩
  · simp only [enter]
    by_cases e : u = v
    · subst e; rw [hn] at h; cases h
    · simp [e, h]
  · simp only [enter] at h'
    by_cases e : u = v
    · simp [e] at h'; omega
    · simp [e, h] at h'

/-! ## The pop loop -/

theorem popLoop_split (v : V) (rest : List V) :
    ∀ (X out : List V) (cur : V → Bool), v ∉ X →
      ∃ cur', popLoop v (X ++ v :: rest) out cur = some (v :: (X.reverse ++ out), rest, cur') ∧
        ∀ x, cur' x = if x ∈ X ∨ x = v then false else cur x
  | [], out, cur, _ => by
    refine ⟨fun x => if x = v then false else cur x, by simp [popLoop], fun x => ?_⟩
    by_cases e : x = v <;> simp [e]
  | p :: X, out, cur, hv => by
    have hpv : v ≠ p := fun h => hv (h ▸ List.mem_cons_self)
    have hvX : v ∉ X := fun h => hv (List.mem_cons_of_mem _ h)
    obtain ⟨cur', h1, h2⟩ := popLoop_split v rest X (p :: out) (fun x => if x = p then false else cur x) hvX
    refine ⟨cur', ?_, fun x => ?_⟩
    · simp only [List.cons_append, popLoop, hpv, if_false]
      rw [h1]; simp
    · rw [h2]
      by_cases e1 : x ∈ X
      · simp [e1]
      · by_cases e2 : x = v
        · simp [e2]
        · by_cases e3 : x = p <;> simp [e1, e2, e3]

theorem tjInv_pop {a : St V} (hI : TjInv a) {X rest : List V} {v : V} (hs : a.stk = X ++ v :: rest)
    {cur' : V → Bool} (hc : ∀ x, cur' x = if x ∈ X ∨ x = v then false else a.cur x) :
    TjInv { a with stk := rest, cur := cur', fin := (v :: (X.reverse ++ [])) :: a.fin } := by
  constructor
  · intro x
    simp only
    rw [hc]
    have h1 := count_le_one_stk hI x
    rw [hs] at h1
    have hcur := hI.cur x
    rw [hs] at hcur
    by_cases e : x ∈ X ∨ x = v
    · simp only [e, if_true]
      constructor
      · intro h; cases h
      · intro hr
        exfalso
        rw [List.count_append, List.count_cons] at h1
        have : 0 < rest.count x := List.count_pos_iff.2 hr
        rcases e with e | e
        · have : 0 < X.count x := List.count_pos_iff.2 e
          omega
        · subst e; simp at h1; omega
    · simp only [e, if_false]
      rw [hcur]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact absurd (Or.inl h) e
        · exact absurd (Or.inr h) e
        · exact h
      · intro h; exact Or.inr (Or.inr h)
  · intro x
    have h := hI.count x
    rw [hs] at h
    simp only [List.flatten_cons, List.append_nil]
    simp only [List.count_append, List.count_cons, List.count_reverse] at h ⊢
    omega

/-! ## The bound on `lowest` -/

theorem tjLoB_min {s0 : St V} {lo x : Nat} (hL : TjLoB s0 lo)
    (h : s0.idx ≤ x ∨ ∃ w ∈ s0.stk, s0.vis w = some x) : TjLoB s0 (min lo x) := by
  obtain ⟨h1, h2⟩ := hL
  rcases h with h | h
  · rw [Nat.min_eq_left (Nat.le_trans h1 h)]; exact ⟨h1, h2⟩
  · by_cases e : lo ≤ x
    · rw [Nat.min_eq_left e]; exact ⟨h1, h2⟩
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le e))]
      exact ⟨by omega, Or.inr h⟩

/-- A vertex on the stack of a later state: new (index at least `s0.idx`) or
on the old stack with its old index. -/
theorem stk_cases {s0 acc : St V} (hI0 : TjInv s0) (hE : TjExt s0 acc) {w : V} {i : Nat}
    (hw : w ∈ acc.stk) (hi : acc.vis w = some i) : s0.idx ≤ i ∨ ∃ w ∈ s0.stk, s0.vis w = some i := by
  obtain ⟨X, hX, hn⟩ := hE.stk
  rw [hX] at hw
  rcases List.mem_append.1 hw with hw | hw
  · exact Or.inl (hE.vis_new w i (hn w hw) hi)
  · right
    refine ⟨w, hw, ?_⟩
    have := vis_of_stk hI0 hw
    cases e : s0.vis w with
    | none => rw [e] at this; cases this
    | some j => rw [hE.vis_ext w j e] at hi; rw [hi]

theorem tjLoB_rec {s0 acc : St V} (hI0 : TjInv s0) (hE : TjExt s0 acc) {lo lk : Nat} (hL : TjLoB s0 lo)
    (hk : TjLoB acc lk) : TjLoB s0 (min lo lk) := by
  apply tjLoB_min hL
  rcases hk.2 with h | ⟨w, hw, hi⟩
  · exact Or.inl (h ▸ hE.idx_le)
  · exact stk_cases hI0 hE hw hi

/-! ## The kids loop and `connect` -/

/-- The spec of `connect` at a fuel, on `rec`. -/
def ConnOK (G : Gr V) (U : List V) (n : Nat) (rec : V → List V → St V → Option (Nat × St V)) : Prop :=
  ∀ v s, v ∈ U → s.vis v = none → tjMeas U s < n → TjInv s → TjInU U s →
    ∃ lo s', rec v (kidsOf G v) s = some (lo, s') ∧ TjExt s s' ∧ TjInv s' ∧ TjInU U s' ∧ TjClo G s s' ∧
      (s'.vis v).isSome ∧ TjLoB s lo ∧ (lo = s.idx → s'.stk = s.stk)

theorem tjClo_refl (G : Gr V) (s : St V) : TjClo G s s := by
  intro u h h'; rw [h] at h'; cases h'

theorem kidsLoop_ok {G : Gr V} {U : List V} {n : Nat} {rec : V → List V → St V → Option (Nat × St V)}
    (hU : ∀ u w, w ∈ kidsOf G u → w ∈ U) (hrec : ConnOK G U n rec) {s0 : St V} (hI0 : TjInv s0) :
    ∀ (ks : List V) (lo : Nat) (acc : St V), (∀ k ∈ ks, k ∈ U) → tjMeas U acc < n → TjInv acc → TjInU U acc →
      TjExt s0 acc → TjLoB s0 lo →
      ∃ lo' acc', kidsLoop G rec ks lo acc = some (lo', acc') ∧ TjExt acc acc' ∧ TjInv acc' ∧
        TjInU U acc' ∧ TjClo G acc acc' ∧ (∀ k ∈ ks, (acc'.vis k).isSome) ∧ TjLoB s0 lo'
  | [], lo, acc, _, _, hI, hIU, _, hL =>
    ⟨lo, acc, rfl, tjExt_refl _, hI, hIU, tjClo_refl G acc, by simp, hL⟩
  | k :: ks, lo, acc, hks, hm, hI, hIU, hE, hL => by
    have hkU := hks k List.mem_cons_self
    have hksU : ∀ k ∈ ks, k ∈ U := fun k' h => hks k' (List.mem_cons_of_mem _ h)
    cases e : acc.vis k with
    | some ki =>
      have hL' : TjLoB s0 (if acc.cur k then min lo ki else lo) := by
        by_cases hc : acc.cur k = true
        · simp only [hc, if_true]
          exact tjLoB_min hL (stk_cases hI0 hE ((hI.cur k).1 hc) e)
        · simp only [hc]; exact hL
      obtain ⟨lo', acc', h1, h2, h3, h4, h5, h6, h7⟩ := kidsLoop_ok hU hrec hI0 ks _ acc hksU hm hI hIU hE hL'
      refine ⟨lo', acc', ?_, h2, h3, h4, h5, ?_, h7⟩
      · simp only [kidsLoop, e]; exact h1
      · intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | hk'
        · rw [h2.vis_ext _ ki e]; rfl
        · exact h6 k' hk'
    | none =>
      obtain ⟨lk, a1, r1, r2, r3, r4, r5, r6, r7, -⟩ := hrec k acc hkU e hm hI hIU
      have hm1 : tjMeas U a1 < n := Nat.lt_of_le_of_lt (tjMeas_le r2.vis_ext) hm
      obtain ⟨lo', acc', h1, h2, h3, h4, h5, h6, h7⟩ :=
        kidsLoop_ok hU hrec hI0 ks _ a1 hksU hm1 r3 r4 (tjExt_trans hE r2) (tjLoB_rec hI0 hE hL r7)
      refine ⟨lo', acc', ?_, tjExt_trans r2 h2, h3, h4, tjClo_trans h2 r5 h5, ?_, h7⟩
      · simp only [kidsLoop, e, r1]; exact h1
      · intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | hk'
        · cases e6 : a1.vis k' with
          | none => rw [e6] at r6; cases r6
          | some j => rw [h2.vis_ext _ j e6]; rfl
        · exact h6 k' hk'

theorem tjInU_enter {U : List V} {s : St V} (h : TjInU U s) {v : V} (hv : v ∈ U) : TjInU U (enter v s) := by
  intro u hu
  simp only [enter] at hu
  by_cases e : u = v
  · exact e ▸ hv
  · simp only [e, if_false] at hu; exact h u hu

/-- **`connect` meets its spec at every fuel.** -/
theorem connect_ok {G : Gr V} {U : List V} (hU : ∀ u w, w ∈ kidsOf G u → w ∈ U) :
    ∀ n, ConnOK G U n (connect G n)
  | 0 => fun _ _ _ _ hm => absurd hm (Nat.not_lt_zero _)
  | n + 1 => by
    intro v s hv hn hm hI hIU
    have hm1 : tjMeas U (enter v s) < n := by have := tjMeas_enter (U := U) hv hn; omega
    have hE1 := tjExt_enter s hn
    obtain ⟨lo, a, h1, h2, h3, h4, h5, h6, h7⟩ := kidsLoop_ok hU (connect_ok hU n) hI (kidsOf G v) s.idx
      (enter v s) (fun k hk => hU v k hk) hm1 (tjInv_enter hI hn) (tjInU_enter hIU hv) hE1
      ⟨Nat.le_refl _, Or.inl rfl⟩
    have hEa := tjExt_trans hE1 h2
    have hva : (a.vis v).isSome := by rw [h2.vis_ext v s.idx (by simp [enter])]; rfl
    have hCloA : TjClo G s a := by
      intro u hu hua w hw
      by_cases e : u = v
      · subst e; exact h6 w hw
      · exact h5 u (by simp [enter, e, hu]) hua w hw
    by_cases hl : s.idx = lo
    · obtain ⟨X, hX, hXn⟩ := h2.stk
      have hvX : v ∉ X := fun h => by have := hXn v h; simp [enter] at this
      have hX' : a.stk = X ++ v :: s.stk := by rw [hX]; rfl
      obtain ⟨cur', hp, hc⟩ := popLoop_split v s.stk X [] a.cur hvX
      refine ⟨lo, { a with stk := s.stk, cur := cur', fin := (v :: (X.reverse ++ [])) :: a.fin }, ?_,
        ⟨hEa.vis_ext, hEa.vis_new, hEa.idx_le, ⟨[], rfl, by simp⟩⟩, tjInv_pop h3 hX' hc, h4, hCloA, hva, h7,
        fun _ => rfl⟩
      simp only [connect, h1]
      rw [if_pos hl]
      simp only [hX', hp]
    · refine ⟨lo, a, ?_, hEa, h3, h4, hCloA, hva, h7, fun h => absurd h.symm hl⟩
      simp only [connect, h1]
      rw [if_neg hl]

/-- **The outer fold**: from an empty stack, every root pops back to it. -/
theorem outer_ok {G : Gr V} {U : List V} (hU : ∀ u w, w ∈ kidsOf G u → w ∈ U)
    (hK : ∀ p ∈ G, kidsOf G p.1 = p.2) {n : Nat} :
    ∀ (rest : Gr V) (acc : St V), (∀ p ∈ rest, p ∈ G) → (∀ p ∈ rest, p.1 ∈ U) → tjMeas U acc < n →
      TjInv acc → TjInU U acc → acc.stk = [] →
      ∃ s', outer G n rest acc = some s' ∧ TjExt acc s' ∧ TjInv s' ∧ TjInU U s' ∧ TjClo G acc s' ∧
        s'.stk = [] ∧ ∀ p ∈ rest, (s'.vis p.1).isSome
  | [], acc, _, _, _, hI, hIU, hs => ⟨acc, rfl, tjExt_refl _, hI, hIU, tjClo_refl G acc, hs, by simp⟩
  | (v, kids) :: rest, acc, hG, hR, hm, hI, hIU, hs => by
    have hG' : ∀ p ∈ rest, p ∈ G := fun p h => hG p (List.mem_cons_of_mem _ h)
    have hR' : ∀ p ∈ rest, p.1 ∈ U := fun p h => hR p (List.mem_cons_of_mem _ h)
    cases e : acc.vis v with
    | some i =>
      obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := outer_ok hU hK rest acc hG' hR' hm hI hIU hs
      refine ⟨s', ?_, h2, h3, h4, h5, h6, ?_⟩
      · simp only [outer, e]; exact h1
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · rw [h2.vis_ext _ i e]; rfl
        · exact h7 p hp
    | none =>
      have hk : kids = kidsOf G v := (hK (v, kids) (hG _ List.mem_cons_self)).symm
      obtain ⟨lo, a, r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        connect_ok hU n v acc (hR _ List.mem_cons_self) e hm hI hIU
      have hlo : lo = acc.idx := by
        rcases r7.2 with h | ⟨w, hw, -⟩
        · exact h
        · rw [hs] at hw; cases hw
      have hsa : a.stk = [] := by rw [r8 hlo, hs]
      obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ :=
        outer_ok hU hK rest a hG' hR' (Nat.lt_of_le_of_lt (tjMeas_le r2.vis_ext) hm) r3 r4 hsa
      refine ⟨s', ?_, tjExt_trans r2 h2, h3, h4, tjClo_trans h2 r5 h5, h6, ?_⟩
      · simp only [outer, e, hk, r1]; exact h1
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · cases e6 : a.vis v with
          | none => rw [e6] at r6; cases r6
          | some j => rw [h2.vis_ext _ j e6]; rfl
        · exact h7 p hp

/-! ## The graph -/

theorem kidsOf_cons (q : V × List V) (G : Gr V) (v : V) :
    kidsOf (q :: G) v = if q.1 = v then q.2 else kidsOf G v := by
  unfold kidsOf
  rw [List.find?_cons]
  by_cases h : q.1 = v <;> simp [h]

theorem mem_tjVerts {G : Gr V} {u : V} : u ∈ tjVerts G ↔ ∃ p ∈ G, u = p.1 ∨ u ∈ p.2 := by
  induction G with
  | nil => simp [tjVerts]
  | cons q G ih =>
    simp only [tjVerts, List.mem_cons, List.mem_append, ih]
    constructor
    · rintro (h | h | ⟨p, hp, h⟩)
      · exact ⟨q, Or.inl rfl, Or.inl h⟩
      · exact ⟨q, Or.inl rfl, Or.inr h⟩
      · exact ⟨p, Or.inr hp, h⟩
    · rintro ⟨p, rfl | hp, h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨p, hp, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨p, hp, Or.inr h⟩)

theorem kidsOf_sub (G : Gr V) (u w : V) (h : w ∈ kidsOf G u) : w ∈ tjVerts G := by
  induction G with
  | nil => simp [kidsOf] at h
  | cons q G ih =>
    rw [kidsOf_cons] at h
    simp only [tjVerts, List.mem_cons, List.mem_append]
    by_cases e : q.1 = u
    · rw [if_pos e] at h; exact Or.inr (Or.inl h)
    · rw [if_neg e] at h; exact Or.inr (Or.inr (ih h))

theorem kidsOf_key {G : Gr V} (hk : (G.map Prod.fst).Nodup) : ∀ p ∈ G, kidsOf G p.1 = p.2 := by
  induction G with
  | nil => intro p hp; cases hp
  | cons q G ih =>
    intro p hp
    simp only [List.map_cons, List.nodup_cons] at hk
    rw [kidsOf_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · have hne : q.1 ≠ p.1 := fun h => hk.1 (h ▸ List.mem_map_of_mem hp)
      rw [if_neg hne]; exact ih hk.2 p hp

theorem fuelOf_eq (G : Gr V) : fuelOf G = (tjVerts G).length + 1 := by
  induction G with
  | nil => rfl
  | cons q G ih =>
    simp only [fuelOf, tjVerts, List.length_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem tjInv_init : TjInv (St.init : St V) :=
  ⟨fun u => by simp [St.init], fun u => by simp [St.init]⟩

/-- **`tarjanM` returns, and its components hold each vertex exactly once**
(on a nonempty graph with distinct keys). -/
theorem tarjanM_count (G : Gr V) (hne : G ≠ []) (hk : (G.map Prod.fst).Nodup) :
    ∃ L, tarjanM G = some L ∧ ∀ u, L.flatten.count u = if u ∈ tjVerts G then 1 else 0 := by
  have hU : ∀ u w, w ∈ kidsOf G u → w ∈ tjVerts G := kidsOf_sub G
  have hm : tjMeas (tjVerts G) (St.init : St V) < fuelOf G := by
    rw [fuelOf_eq]; exact Nat.lt_succ_of_le (List.countP_le_length)
  obtain ⟨s, h1, -, h3, h4, h5, h6, h7⟩ := outer_ok hU (kidsOf_key hk) G St.init (fun p h => h)
    (fun p hp => mem_tjVerts.2 ⟨p, hp, Or.inl rfl⟩) hm tjInv_init (fun u h => by simp [St.init] at h) rfl
  refine ⟨s.fin, ?_, fun u => ?_⟩
  · cases G with
    | nil => exact absurd rfl hne
    | cons q G' => simp only [tarjanM]; rw [h1]; rfl
  · have hc := h3.count u
    rw [h6, List.nil_append] at hc
    rw [hc]
    have : (s.vis u).isSome = true ↔ u ∈ tjVerts G := by
      refine ⟨h4 u, fun hu => ?_⟩
      obtain ⟨p, hp, h | h⟩ := mem_tjVerts.1 hu
      · exact h ▸ h7 p hp
      · exact h5 p.1 rfl (h7 p hp) u (by rw [kidsOf_key hk p hp]; exact h)
    by_cases e : u ∈ tjVerts G
    · rw [if_pos e, if_pos (this.2 e)]
    · rw [if_neg e]
      have : (s.vis u).isSome = false := by
        cases h : (s.vis u).isSome
        · rfl
        · exact absurd (this.1 h) e
      rw [this]; rfl

/-- **Totality**: `tarjanM` returns on every nonempty graph with distinct keys. -/
theorem tarjanM_total (G : Gr V) (hne : G ≠ []) (hk : (G.map Prod.fst).Nodup) : ∃ L, tarjanM G = some L :=
  (tarjanM_count G hne hk).imp fun _ h => h.1

end Tarjan
end Formalization
