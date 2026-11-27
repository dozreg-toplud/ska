import lemmas.Ska.PassMeasureB

/-!
# The pieces of the halting argument that hold whatever the measure (track F, Gaps 16)

`memberLoop_le` of `Ska/PassMeasureP.lean` compares the members' entries only
when `next` is the same, that is when no function was pushed.  Here the
comparison holds always, for the identities on the stack before:

* `valE_run_ext`: a `+run` of `m` that keeps the old stack at the bottom of the
  new one (`Keep` of `RunP`) keeps or lowers the value of every identity of the
  old stack, and lowers the value of `m` when its five fields changed;
* `memberLoop_old`: the member loop, pushes or not, keeps the old stack at the
  bottom, keeps or lowers the value of every identity on it, and when it
  reports `changed` (and its members are on the stack) lowers the value of one
  of its members;
* `passOn_old`: a pass that goes on keeps or lowers the value of every identity
  that was on the stack at its start (a culled one falls to `none`), keeps the
  root on the stack, and lowers one of them or pushes;
* `chain_present_const`: along any infinite sequence of passes, an identity
  that is on the stack from some pass on has an eventually constant value; the
  root is on the stack at every pass (`chain_root_mem`), so its entry is
  eventually constant (`chain_root_const`).

The fuel of `+sweep` and `+cull` (the loops `sweepLoop` and `liveLoop`, which
the model runs on the fuel of the arm around them): each returns as soon as the
fuel is above an explicit potential (`sweepLoop_ends`, `liveLoop_ends`,
`sweep_ends`, `cull_ends`): the frames left on the work stack, each one more
than its kids, plus, for every identity of the set that is not marked yet, its
number of kids plus 2 (`+sweep`) or plus 1 (`+cull`).

On the real compiler (`tools/hoon/passmeasure.py`, the print `%pm-ent`: at the
start of every pass, every member with its DFS number, how its entry changed
since the start of the previous pass, and its callees) the comparison of
`passOn_old` held at every pair recorded (README Gaps 16 gives the counts).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. Every identity of the old stack keeps or lowers its value -/

/-- **A run of `m` that keeps the old stack at the bottom** keeps or lowers the
value of every identity of the old stack, and lowers the value of `m` when its
five fields changed. -/
theorem valE_run_ext {st st' : SkaState M R} {m : Ident} {old new : Datum}
    (hs : ∃ l, st'.stk = l ++ st.stk)
    (hg : ∀ j, j ∈ st.stk ∧ j ≠ m → Treap.get st'.g j = Treap.get st.g j)
    (ho : gCore st.g m = some old) (hn : gCore st'.g m = some new)
    (hst : EntrySame new old ∨ EntryLt m.1 new old) :
    (∀ i ∈ st.stk, SkaModel.OLe (valE st' i) (valE st i)) ∧
      (¬ EntrySame new old → m ∈ st.stk → SkaModel.OLt (valE st' m) (valE st m)) := by
  obtain ⟨l, hl⟩ := hs
  have mem' : ∀ i ∈ st.stk, i ∈ st'.stk := fun i hi => by rw [hl]; exact List.mem_append_right _ hi
  have em : m ∈ st.stk → valE st' m = some (entryM m.1 new) ∧ valE st m = some (entryM m.1 old) := by
    intro hm
    unfold valE; simp [hm, mem' m hm, ho, hn]
  refine ⟨fun i hi => ?_, fun hne hm => ?_⟩
  · by_cases e : i = m
    · subst e
      obtain ⟨e1, e2⟩ := em hi
      rw [e1, e2]
      rcases hst with h | h
      · exact Or.inl (by rw [entryM_same h])
      · exact Or.inr h
    · left
      unfold valE; simp [hi, mem' i hi, gCore, hg i ⟨hi, e⟩]
  · obtain ⟨e1, e2⟩ := em hm
    rw [e1, e2]
    exact hst.resolve_left hne

/-- **The member loop, whether or not it pushes**, keeps the old stack at the
bottom, keeps or lowers the value of every identity on it, keeps `WInv`, and
when it reports `changed` and its members are on the stack, it lowers the value
of one of its members. -/
theorem memberLoop_old (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) :
    ∀ n index pass ms (st : SkaState M R) r st', SInv st → TInv st → WInv st →
      memberLoop env memoF n index pass ms st = some (r, st') →
      WInv st' ∧ (∃ l, st'.stk = l ++ st.stk) ∧
        (∀ i ∈ st.stk, SkaModel.OLe (valE st' i) (valE st i)) ∧
        (r.2 = true → (∀ m ∈ ms, m ∈ st.stk) → ∃ i ∈ ms, SkaModel.OLt (valE st' i) (valE st i))
  | 0 => by
    intro index pass ms st r st' _ _ _ h
    rw [memberLoop_zero] at h; cases h
  | n + 1 => by
    intro index pass ms st r st' hi ht hw h
    rw [memberLoop_succ] at h
    cases ms with
    | nil =>
      simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw, ⟨[], rfl⟩, fun i _ => Or.inl rfl, fun h => by cases h⟩
    | cons m ms =>
      have key : ∀ st1 : SkaState M R,
          ((Treap.get st.order m).bind fun o => (run env memoF n m o st1).bind fun r =>
            if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
            (memberLoop env memoF n index pass ms r.2).map fun t =>
              ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
          st1.g = st.g → st1.done = st.done → st1.order = st.order → st1.stk = st.stk →
          WInv st' ∧ (∃ l, st'.stk = l ++ st.stk) ∧
            (∀ i ∈ st.stk, SkaModel.OLe (valE st' i) (valE st i)) ∧
            (r.2 = true → (∀ m' ∈ m :: ms, m' ∈ st.stk) →
              ∃ i ∈ m :: ms, SkaModel.OLt (valE st' i) (valE st i)) := by
        intro st1 e h1 h2 h3 h4
        simp only [Option.bind_eq_some_iff] at e
        obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
        have i1 : SInv st1 := hi.congr h1 h2 h3 h4
        have t1 : TInv st1 := ht.congr h1 h2
        have w1 : WInv st1 := hw.congr h1 h2 h4
        have hm1 : m ∈ st1.stk := (i1.ord_stk m).mp ⟨o, by rw [h3]; exact ho⟩
        obtain ⟨i2, _, k2⟩ := run_ok env memoF hmF n m o st1 r1 st2 i1 hm1 hr
        have t2 := (allPT env memoF hmF hmT n n (Nat.le_refl n)).2.2.1 m o st1 r1 st2 i1 t1 hm1 hr
        have w2 := hRW n m o st1 r1 st2 i1 t1 w1 hm1 hr
        have v1 : valE st1 = valE st := valE_congr h1 h4
        obtain ⟨old, new, ho', hn', hst⟩ := run_entry_step env memoF n i1 t1 hm1 hr (w1.stk m hm1)
        obtain ⟨A, B⟩ := valE_run_ext k2.1 (fun j hj => k2.2.2 j hj) ho' hn' hst
        have Bm : r1.2.2 = true → SkaModel.OLt (valE st2 m) (valE st1 m) :=
          fun hc => B (run_changed env memoF n i1 hm1 hr ho' hn' hc) hm1
        obtain ⟨l2, e2⟩ := k2.1
        rw [h4] at e2 A
        split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          refine ⟨w2, ⟨l2, e2⟩, fun i hi' => ?_, fun hc _ => ⟨m, List.mem_cons_self, ?_⟩⟩
          · rw [← v1]; exact A i hi'
          · rw [← v1]; exact Bm hc
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨⟨t1', st3⟩, ht', e⟩ := e
          cases e
          obtain ⟨w3, ⟨l3, e3⟩, A3, B3⟩ :=
            memberLoop_old env memoF hmF hmT hRW n index pass ms st2 t1' st3 i2 t2 w2 ht'
          have mem2 : ∀ i ∈ st.stk, i ∈ st2.stk := fun i hi' => by
            rw [e2]; exact List.mem_append_right _ hi'
          refine ⟨w3, ⟨l3 ++ l2, by rw [e3, e2, List.append_assoc]⟩, fun i hi' => ?_, fun hc hms => ?_⟩
          · rw [← v1]; exact ole_trans (A3 i (mem2 i hi')) (A i hi')
          · simp only [Bool.or_eq_true] at hc
            rw [← v1]
            rcases hc with hc | hc
            · exact ⟨m, List.mem_cons_self,
                ole_lt_trans (A3 m (mem2 m (hms m List.mem_cons_self))) (Bm hc)⟩
            · obtain ⟨i, hi', hlt⟩ := B3 hc (fun m' hm' => mem2 m' (hms m' (List.mem_cons_of_mem _ hm')))
              exact ⟨i, List.mem_cons_of_mem _ hi',
                olt_le_trans hlt (A i (hms i (List.mem_cons_of_mem _ hi')))⟩
      simp only [memberStep] at h
      split at h
      · obtain ⟨w', s', A', B'⟩ := memberLoop_old env memoF hmF hmT hRW n index pass ms st r st' hi ht hw h
        refine ⟨w', s', A', fun hc hms => ?_⟩
        obtain ⟨i, hi', hlt⟩ := B' hc (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))
        exact ⟨i, List.mem_cons_of_mem _ hi', hlt⟩
      · by_cases hp : pass > 1
        · simp only [hp, if_true] at h
          exact key _ h rfl rfl rfl rfl
        · simp only [hp, if_false] at h
          exact key _ h rfl rfl rfl rfl

theorem mem_of_above {id : Ident} {stk ab : List Ident} (h : above id stk = some ab) :
    ∀ x, Treap.has (Treap.silt ab : M Ident Unit) x = true → x ∈ stk := by
  intro x hx
  obtain ⟨ab0, rest, rfl, rfl, _⟩ := above_eq h
  rcases List.mem_append.mp ((Treap.has_silt _ x).mp hx) with h | h
  · exact List.mem_append_left _ h
  · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ List.mem_cons_self

/-- **A pass that goes on, whether or not it pushes**, keeps or lowers the
value of every identity that was on the stack at its start (one that `+cull`
drops falls to `none`), keeps the root on the stack, and lowers the value of
one of them or pushes. -/
theorem passOn_old (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hi : SInv st) (ht : TInv st) (hw : WInv st)
    (h : PassOn env memoF n id index pass st st') :
    (∀ i ∈ st.stk, SkaModel.OLe (valE st' i) (valE st i)) ∧ id ∈ st'.stk ∧
      ((∃ i ∈ st.stk, SkaModel.OLt (valE st' i) (valE st i)) ∨ st.next < st'.next) := by
  have hle := (passOn_inv env memoF hmF hmT hRW hi ht hw h).2.2.2.1
  obtain ⟨ab, members, r, st2, h1, h2, h3, _, h5, h6⟩ := h
  have i1 : SInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hi.congr rfl rfl rfl rfl
  have t1 : TInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    ht.congr rfl rfl
  obtain ⟨_, ⟨l2, e2⟩, A, B⟩ :=
    memberLoop_old env memoF hmF hmT hRW n index pass members _ r st2 i1 t1 (hw.congr rfl rfl rfl) h3
  have v1 : valE ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) =
      valE st := valE_congr rfl rfl
  rw [v1] at A B
  have S := cull_sub h5
  obtain ⟨ab0, rest, _, hs, _⟩ := above_eq h1
  have hs2 : st2.stk = (l2 ++ ab0) ++ id :: rest := by
    rw [e2]; show l2 ++ st.stk = _; rw [hs, List.append_assoc]
  obtain ⟨_, _, ⟨⟨l', e'⟩, _, _⟩⟩ := cull_ok (allP env memoF hmF n n (Nat.le_refl n) |>.2.2.2.2 index pass
    members _ r st2 [] (fun _ => False) i1 ⟨st.stk, (List.append_nil _).symm⟩ (fun _ h => h.elim)
    (fun _ _ h => h) h3).1 h5 hs2
  have hroot : id ∈ st'.stk := by rw [e']; exact List.mem_append_right _ List.mem_cons_self
  refine ⟨fun i hi' => ole_trans (valE_sub S i) (A i hi'), hroot, ?_⟩
  cases hr : r.2 with
  | true =>
    have hms : ∀ m ∈ members, m ∈ st.stk := by
      intro m hm
      rcases sweep_mem h2 m hm with rfl | hm'
      · rw [hs]; exact List.mem_append_right _ List.mem_cons_self
      · exact mem_of_above h1 m hm'
    obtain ⟨i, hi', hlt⟩ := B hr hms
    exact Or.inl ⟨i, hms i hi', ole_lt_trans (valE_sub S i) hlt⟩
  | false =>
    refine Or.inr (Nat.lt_of_le_of_ne hle fun e => h6 ⟨hr, e.symm⟩)

/-! ## 2. Along a chain of passes -/

/-- **The root is on the stack at every pass of a chain.** -/
theorem chain_root_mem (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) (id : Ident) (index p : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : WInv (f 0))
    (hon : ∀ k, ∃ n, PassOn env memoF n id index (p + k) (f k) (f (k + 1))) :
    (∀ k, SInv (f k) ∧ TInv (f k) ∧ WInv (f k)) ∧ ∀ k, id ∈ (f (k + 1)).stk := by
  have inv : ∀ k, SInv (f k) ∧ TInv (f k) ∧ WInv (f k) := by
    intro k
    induction k with
    | zero => exact ⟨h0i, h0t, h0w⟩
    | succ k ih =>
      obtain ⟨a, b, c, _, _⟩ := passOn_inv env memoF hmF hmT hRW ih.1 ih.2.1 ih.2.2 (hon k).choose_spec
      exact ⟨a, b, c⟩
  exact ⟨inv, fun k => (passOn_old env memoF hmF hmT hRW (inv k).1 (inv k).2.1 (inv k).2.2
    (hon k).choose_spec).2.1⟩

/-- **An identity on the stack from some pass on has an eventually constant
value** along any infinite chain of passes: its entry changes finitely often,
whatever is pushed meanwhile. -/
theorem chain_present_const (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) (id : Ident) (index p : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : WInv (f 0))
    (hon : ∀ k, ∃ n, PassOn env memoF n id index (p + k) (f k) (f (k + 1)))
    (i : Ident) (K : Nat) (hK : ∀ k, K ≤ k → i ∈ (f k).stk) :
    ∃ K', K ≤ K' ∧ ∀ k, K' ≤ k → valE (f (k + 1)) i = valE (f k) i := by
  obtain ⟨inv, _⟩ := chain_root_mem env memoF hmF hmT hRW id index p f h0i h0t h0w hon
  have step : ∀ k, K ≤ k → SkaModel.OLe (valE (f (k + 1)) i) (valE (f k) i) := fun k hk =>
    (passOn_old env memoF hmF hmT hRW (inv k).1 (inv k).2.1 (inv k).2.2 (hon k).choose_spec).1 i (hK k hk)
  obtain ⟨K0, hK0⟩ := ev_const (r := SkaModel.OLt) oLt_wf oLt_trans (fun k => valE (f (K + k)) i)
    (fun k => by
      have := step (K + k) (Nat.le_add_right _ _)
      rcases this with e | e
      · exact Or.inl e
      · exact Or.inr e)
  refine ⟨K + K0, Nat.le_add_right _ _, fun k hk => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have := hK0 (K0 + d) (Nat.le_add_right _ _)
  rw [show K + (K0 + d + 1) = K + K0 + d + 1 by omega, show K + (K0 + d) = K + K0 + d by omega] at this
  exact this

/-- **The root's entry is eventually constant** along any infinite chain of
passes. -/
theorem chain_root_const (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) (id : Ident) (index p : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : WInv (f 0))
    (hon : ∀ k, ∃ n, PassOn env memoF n id index (p + k) (f k) (f (k + 1))) :
    ∃ K, ∀ k, K ≤ k → valE (f (k + 1)) id = valE (f k) id := by
  obtain ⟨_, hroot⟩ := chain_root_mem env memoF hmF hmT hRW id index p f h0i h0t h0w hon
  obtain ⟨K', _, h⟩ := chain_present_const env memoF hmF hmT hRW id index p f h0i h0t h0w hon id 1
    (fun k hk => by obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk; rw [Nat.add_comm]; exact hroot j)
  exact ⟨K', h⟩

/-! ## 3. The fuel of `+sweep` and `+cull` -/

theorem has_ins_ident (s : M Ident Unit) (i k : Ident) :
    Treap.has (Treap.ins s i) k = if k = i then true else Treap.has s k := by
  unfold Treap.has Treap.ins
  rw [Treap.get_put]
  split <;> simp

/-- The part of an identity of the set that is not marked yet. -/
def leftTerm (s : M Ident Unit) (w : Ident → Nat) (e : Ident × Unit) : Nat :=
  if Treap.has s e.1 = true then 0 else w e.1

/-- What is left to mark: the weight of every listed identity not in `s`. -/
def leftSum (s : M Ident Unit) (w : Ident → Nat) (l : List (Ident × Unit)) : Nat :=
  (l.map (leftTerm s w)).sum

theorem leftSum_ins_le {s : M Ident Unit} {w : Ident → Nat} {i : Ident} :
    ∀ l : List (Ident × Unit), leftSum (Treap.ins s i) w l ≤ leftSum s w l
  | [] => Nat.le_refl _
  | e :: l => by
    simp only [leftSum, List.map_cons, List.sum_cons] at *
    have h1 : leftTerm (Treap.ins s i) w e ≤ leftTerm s w e := by
      unfold leftTerm; rw [has_ins_ident]
      split
      · simp
      · exact Nat.le_refl _
    exact Nat.add_le_add h1 (leftSum_ins_le l)

theorem leftSum_ins_lt {s : M Ident Unit} {w : Ident → Nat} {i : Ident} (hi : ¬ Treap.has s i = true) :
    ∀ l : List (Ident × Unit), (i, ()) ∈ l → leftSum (Treap.ins s i) w l + w i ≤ leftSum s w l
  | [], h => by simp at h
  | e :: l, h => by
    simp only [leftSum, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have h1 : leftTerm (Treap.ins s i) w (i, ()) = 0 := by
        unfold leftTerm; rw [has_ins_ident]; simp
      have h2 : leftTerm s w (i, ()) = w i := by
        unfold leftTerm; simp [hi]
      have := leftSum_ins_le (s := s) (w := w) (i := i) l
      simp only [leftSum] at this
      omega
    · have := leftSum_ins_lt (w := w) hi l h
      have h3 : leftTerm (Treap.ins s i) w e ≤ leftTerm s w e := by
        unfold leftTerm; rw [has_ins_ident]
        split
        · simp
        · exact Nat.le_refl _
      simp only [leftSum] at this
      omega

theorem mem_tap_of_has {s : M Ident Unit} {i : Ident} (h : Treap.has s i = true) : (i, ()) ∈ Treap.tap s := by
  obtain ⟨v, hv⟩ := (Treap.has_iff s i).mp h
  cases v
  exact (Treap.mem_tap s i ()).mpr hv

/-- **The loop of `+cull` returns** as soon as its fuel is above the length of
its queue plus, for every member not live yet, one more than its number of
kids. -/
theorem liveLoop_ends (st : SkaState M R) (members : M Ident Unit) :
    ∀ (n : Nat) (q : List Ident) (live : M Ident Unit),
      q.length + leftSum live (fun k => 1 + (kids st k).length) (Treap.tap members) < n →
      ∃ live', liveLoop st members n q live = some live'
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], live, _ => ⟨live, by simp [liveLoop]⟩
  | n + 1, i :: q, live, hn => by
    simp only [liveLoop]
    by_cases hc : Treap.has live i = true ∨ Treap.has members i = false
    · rw [if_pos hc]
      refine liveLoop_ends st members n q live ?_
      simp only [List.length_cons] at hn
      omega
    · rw [if_neg hc]
      have hl : ¬ Treap.has live i = true := fun h => hc (Or.inl h)
      have hm : Treap.has members i = true := by
        cases e : Treap.has members i
        · exact absurd (Or.inr e) hc
        · rfl
      have := leftSum_ins_lt (w := fun k => 1 + (kids st k).length) hl _ (mem_tap_of_has hm)
      refine liveLoop_ends st members n _ _ ?_
      simp only [List.length_append, List.length_cons] at hn ⊢
      omega

/-- The frames of the work stack of `+sweep`: each one more than its kids
left. -/
def stackPot (l : List (Ident × List Ident)) : Nat := (l.map (fun e => 1 + e.2.length)).sum

/-- **The loop of `+sweep` returns** as soon as its fuel is above the frames
left (`stackPot`) plus, for every member not seen yet, its number of kids plus
2. -/
theorem sweepLoop_ends (st : SkaState M R) (was : M Ident Unit) :
    ∀ (n : Nat) (seen : M Ident Unit) (l : List (Ident × List Ident)) (out : List Ident),
      stackPot l + leftSum seen (fun k => 2 + (kids st k).length) (Treap.tap was) < n →
      ∃ res, sweepLoop st was n seen l out = some res
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, seen, [], out, _ => ⟨out.reverse, by simp [sweepLoop]⟩
  | n + 1, seen, (i, []) :: rest, out, hn => by
    simp only [sweepLoop]
    refine sweepLoop_ends st was n seen rest (i :: out) ?_
    simp only [stackPot, List.map_cons, List.sum_cons, List.length_nil] at hn ⊢
    omega
  | n + 1, seen, (i, k :: ks) :: rest, out, hn => by
    simp only [sweepLoop]
    by_cases hc : Treap.has seen k = true ∨ Treap.has was k = false
    · rw [if_pos hc]
      refine sweepLoop_ends st was n seen ((i, ks) :: rest) out ?_
      simp only [stackPot, List.map_cons, List.sum_cons, List.length_cons] at hn ⊢
      omega
    · rw [if_neg hc]
      have hl : ¬ Treap.has seen k = true := fun h => hc (Or.inl h)
      have hm : Treap.has was k = true := by
        cases e : Treap.has was k
        · exact absurd (Or.inr e) hc
        · rfl
      have := leftSum_ins_lt (w := fun k => 2 + (kids st k).length) hl _ (mem_tap_of_has hm)
      refine sweepLoop_ends st was n _ _ out ?_
      simp only [stackPot, List.map_cons, List.sum_cons, List.length_cons] at hn ⊢
      omega

/-- **`+sweep` returns** at every fuel above `sweepFuel`. -/
def sweepFuel (id : Ident) (was : M Ident Unit) (st : SkaState M R) : Nat :=
  1 + (kids st id).length + leftSum (Treap.ins (Treap.empty : M Ident Unit) id) (fun k => 2 + (kids st k).length) (Treap.tap was)

theorem sweep_ends {n : Nat} (id : Ident) (was : M Ident Unit) (st : SkaState M R) (h : sweepFuel id was st < n) :
    ∃ res, sweep n id was st = some res := by
  unfold sweep
  refine sweepLoop_ends st was n _ _ [] ?_
  simp only [sweepFuel, stackPot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h ⊢
  omega

/-- **`+cull` returns** at every fuel above `cullFuel`, for a root on the
stack. -/
def cullFuel (ab : List Ident) (st : SkaState M R) : Nat :=
  1 + leftSum (Treap.empty : M Ident Unit) (fun k => 1 + (kids st k).length) (Treap.tap (Treap.silt ab : M Ident Unit))

theorem cull_ends {n : Nat} {id : Ident} {st : SkaState M R} {ab : List Ident} (hab : above id st.stk = some ab)
    (h : cullFuel ab st < n) : ∃ st', cull n id st = some st' := by
  unfold cull
  rw [hab]
  simp only [Option.bind_some]
  obtain ⟨live', hl⟩ := liveLoop_ends st (Treap.silt ab) n [id] Treap.empty (by
    simp only [cullFuel, List.length_cons, List.length_nil] at h ⊢; omega)
  rw [hl]
  exact ⟨_, rfl⟩

end Ana

end SkaModel
end Formalization
