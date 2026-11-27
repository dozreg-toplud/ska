import lemmas.Ska.PassMoves

/-!
# Quiet passes (track F, Gaps 16)

Since dab8478 a pass of the loop of `+analyze` can go on with no change and
no push: `passEnd` finds a member that `id` reaches dirty at the end of the
pass (a QUIET pass, `PassQuiet`).  Here: **a quiet pass lowers the number of
dirty members of the stack** (`passQuiet_step`), so quiet passes in a row are
at most the members, and **no infinite sequence of passes that go on, with
or without a change, pushes finitely often** (`passMixed_wf`); hence the pass
loop returns when each of its passes does and every chain of them pushes
finitely often (`passLoop_returns_q`).

The argument of a quiet pass, from the stable part of `MemP2`
(`Ska/ConvPass.lean`): in a pass with no change and no push, no `chg` tick
moves, a member that the pass does not run keeps its `ran` tick and its
callees, and every member the sweep lists is clean at the end (it was clean at
its turn, or it ran, which leaves it clean).  So a member dirty at the end was
dirty at the start and not swept.  And a quiet pass that goes on had a swept
member dirty at the start: otherwise the member loop runs nothing
(`memberLoop_clean`), the end sweep is the start sweep (`sweep_congr`) and the
end test finds no dirty member.  So `dcount` (the dirty members of the stack,
the same stack before and after) falls strictly.  "At most one quiet pass in
a row" is NOT what this gives, and it is not what the traces support as a
proof: a run with no `changed` can change its callee set (936 runs on the
fixed library, `tools/hoon/passmeasure-quiet.py`), so the reached set can move
in a quiet pass.  No quiet pass that went on was seen in 2,612 cases.

The invariant that carries the hypotheses of `MemP2` from pass to pass is
`PStart` (the convergence invariant with the fixed bottom `rest`, as in
`passStep_ok2`); `pstart_mem` is the first half of `passStep_ok2`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. Small facts -/

theorem filter_length_le {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ j ∈ l, q j = true → p j = true) → (l.filter q).length ≤ (l.filter p).length
  | [], _ => Nat.le_refl _
  | a :: l, hi => by
    have ih := filter_length_le l (fun j hj => hi j (List.mem_cons_of_mem _ hj))
    have ha := hi a List.mem_cons_self
    simp only [List.filter_cons]
    cases hq : q a with
    | true =>
      rw [ha hq]; simp only [if_true, List.length_cons]; omega
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases p a <;> simp only [Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

theorem filter_length_lt {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ j ∈ l, q j = true → p j = true) → (∃ j ∈ l, p j = true ∧ q j = false) →
      (l.filter q).length < (l.filter p).length
  | [], _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | a :: l, hi, ⟨j, hj, hpj, hqj⟩ => by
    have hl : ∀ j ∈ l, q j = true → p j = true := fun j hj => hi j (List.mem_cons_of_mem _ hj)
    have hle := filter_length_le l hl
    have ha := hi a List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · rw [hpj, hqj]; simp only [Bool.false_eq_true, if_false, if_true, List.length_cons]; omega
    · have ih := filter_length_lt l hl ⟨j, hj', hpj, hqj⟩
      cases hq : q a with
      | true => rw [ha hq]; simp only [if_true, List.length_cons]; omega
      | false =>
        simp only [Bool.false_eq_true, if_false]
        cases p a <;> simp only [Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

theorem sweepLoop_congr {st st' : SkaState M R} (h : st'.g = st.g) (was : M Ident Unit) :
    ∀ n seen stack out, sweepLoop st' was n seen stack out = sweepLoop st was n seen stack out
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | n + 1, seen, (i, []) :: rest, out => by
    simp only [sweepLoop]; exact sweepLoop_congr h was n _ _ _
  | n + 1, seen, (i, k :: ks) :: rest, out => by
    have hk : kids st' k = kids st k := by simp only [kids, h]
    simp only [sweepLoop, hk, sweepLoop_congr h was n]

theorem sweep_congr {st st' : SkaState M R} (h : st'.g = st.g) (n : Nat) (id : Ident) (was : M Ident Unit) :
    sweep n id was st' = sweep n id was st := by
  have hk : kids st' id = kids st id := by simp only [kids, h]
  unfold sweep; rw [hk]; exact sweepLoop_congr h was n _ _ _

/-- The dirty members of the stack. -/
def dcount (st : SkaState M R) : Nat := (st.stk.filter (fun j => dirty j st)).length

/-! ## 2. The invariant at a pass start -/

/-- The convergence invariant at the start of a pass of the component of
`id`, over the fixed bottom `rest` (the hypotheses of `MemP2` and `PassP2`). -/
def PStart (memoF : Memo M) (id : Ident) (index : Nat) (rest : List Ident) (st : SkaState M R) : Prop :=
  ∃ F ab0, CInv memoF st F ∧ st.stk = ab0 ++ id :: rest ∧ Treap.get st.order id = some index ∧
    (∀ m ∈ rest, MemOK st F m index) ∧ (MemoNoCallees memoF → RestBelow st rest index) ∧
    (∀ x o, Treap.get st.order x = some o → x ∉ rest → 1 ≤ ranOf st x ∧ LowB st x index)

/-- **The member loop of a pass keeps `PStart`**, and with no change and no
push it keeps every `chg` tick, the `ran` tick and callees of every stack
identity it does not list, and leaves every listed member clean (the first
half of `passStep_ok2`). -/
theorem pstart_mem (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmN : MemoNorm memoF) {n : Nat}
    {id : Ident} {index pass : Nat} {rest : List Ident} {st st2 : SkaState M R} {ab members : List Ident}
    {r : Nat × Bool} (hP : PStart memoF id index rest st) (hab : above id st.stk = some ab)
    (hsw : sweep n id (Treap.silt ab) st = some members)
    (hml : memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st2))
    (hr1 : r.1 = index) :
    PStart memoF id index rest st2 ∧ (∀ m ∈ members, m ∈ st.stk) ∧
    (r.2 = false → st2.next = st.next → (∀ j, chgOf st2 j = chgOf st j) ∧
      (∀ j ∈ st.stk, j ∉ members → ranOf st2 j = ranOf st j ∧ calleesOf st2 j = calleesOf st j) ∧
      ∀ m ∈ members, dirty m st2 = false) := by
  obtain ⟨F, ab0, hc, hs, hidx, hrest, hrb, hcl⟩ := hP
  obtain ⟨ab0', rest', rfl, hs', _⟩ := above_eq hab
  obtain ⟨rfl, rfl⟩ := nodup_split_unique (hs ▸ hc.s.nodup) (hs.symm.trans hs')
  have hnd2 : ((ab0 ++ [id]) ++ rest).Nodup := by simpa using (hs ▸ hc.s.nodup)
  have hmembers : ∀ m ∈ members, m ∈ st.stk ∧ m ∉ rest := by
    intro m hm
    have hm' : m ∈ ab0 ++ [id] := by
      rcases sweep_mem hsw m hm with rfl | h
      · simp
      · exact (Treap.has_silt _ _).mp h
    exact ⟨by rw [hs]; exact mem_split_of hm', fun hr => (List.nodup_append.mp hnd2).2.2 m hm' m hr rfl⟩
  obtain ⟨⟨F2, _, c2, hrest2⟩, _, k2, fr2, _, hcl2, hstab2⟩ :=
    (allP2 env memoF hmF hmN n n (Nat.le_refl n)).2.2.2.2 index pass members
      ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R)
      r st2 F ab0 rest id (hc.congr rfl rfl rfl rfl rfl rfl rfl) hs hidx hmembers
      (fun m hm => memOK_congr rfl rfl rfl (hrest m hm)) hcl hml
  have fr2' : Frame (· ∈ rest) st st2 := ⟨fr2.fin, fr2.ticks, fr2.next, fr2.tick, fr2.newOrd⟩
  have hidx2 : Treap.get st2.order id = some index := by
    rw [k2.2.1 id (by rw [hs]; simp)]; exact hidx
  have hst2 : ∃ l, st2.stk = (l ++ ab0) ++ id :: rest := by
    obtain ⟨l, el⟩ := k2.1; exact ⟨l, by rw [el]; show l ++ st.stk = _; rw [hs]; simp⟩
  obtain ⟨l2, el2⟩ := hst2
  have hsub : ∀ m ∈ rest, m ∈ st.stk := fun m hm => by rw [hs]; simp [hm]
  have hrb2 : MemoNoCallees memoF → RestBelow st2 rest index := fun hm =>
    restBelow_keep hc.s (hc.clo hm).1 (hrb hm) hsub (fun m hm' => k2.2.2 m hm')
      (fun c hc' => k2.2.1 c (hsub c hc')) fr2' (up_of_split hc.ord hs hidx)
  have hcl2' : ∀ x o, Treap.get st2.order x = some o → x ∉ rest → 1 ≤ ranOf st2 x ∧ LowB st2 x index := by
    intro x o hxo hx; rw [← hr1]; exact hcl2 x o hxo hx
  refine ⟨⟨F2, l2 ++ ab0, c2, el2, hidx2, hrest2, hrb2, hcl2'⟩, fun m hm => (hmembers m hm).1,
    fun h2 h3 => ?_⟩
  obtain ⟨_, a, b, c⟩ := hstab2 hr1 h2 h3
  exact ⟨a, b, c⟩

/-! ## 3. A quiet pass -/

/-- **A quiet pass**: the member loop returns at the root with no change and
no push, and a member that `id` reaches is dirty at the end, so `passEnd`
starts another pass. -/
def PassQuiet (env : Env R) (memoF : Memo M) (n : Nat) (id : Ident) (index pass : Nat)
    (st st' : SkaState M R) : Prop :=
  ∃ ab members r, above id st.stk = some ab ∧ sweep n id (Treap.silt ab) st = some members ∧
    memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st') ∧
    r.1 = index ∧ r.2 = false ∧ st'.next = st.next ∧
    ∃ ab' ms', above id st'.stk = some ab' ∧ sweep n id (Treap.silt ab') st' = some ms' ∧
      ms'.any (fun m => dirty m st') = true

/-- **A quiet pass is the pass loop calling itself.** -/
theorem passLoop_of_quiet {env : Env R} {memoF : Memo M} {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (h : PassQuiet env memoF n id index pass st st') :
    passLoop env memoF (n + 1) id index pass st = passLoop env memoF n id index (pass + 1) st' := by
  obtain ⟨ab, members, r, h1, h2, h3, h4, h5, h6, ab', ms', h7, h8, h9⟩ := h
  rw [passLoop_succ]
  unfold passStep
  simp only [h1, h2, Option.bind_some, h3]
  rw [if_neg (fun hc => hc h4), if_pos ⟨h5, h6⟩]
  unfold passEnd
  simp only [h7, h8, Option.bind_some, h9, if_true]

theorem passQuiet_mono {env : Env R} {memoF : Memo M} {m m' : Nat} (h : m ≤ m') {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hp : PassQuiet env memoF m id index pass st st') :
    PassQuiet env memoF m' id index pass st st' := by
  obtain ⟨ab, members, r, h1, h2, h3, h4, h5, h6, ab', ms', h7, h8, h9⟩ := hp
  exact ⟨ab, members, r, h1,
    fuel_chain (f := fun k => sweep k id (Treap.silt ab) st) (fun k => sweep_fuel k id _ st) h _ h2,
    memberLoop_fuel_le env memoF h _ _ _ _ _ h3, h4, h5, h6, ab', ms', h7,
    fuel_chain (f := fun k => sweep k id (Treap.silt ab') st') (fun k => sweep_fuel k id _ st') h _ h8, h9⟩

/-- **A quiet pass lowers the dirty members of the stack**, keeps `next`, the
stack and `PStart`. -/
theorem passQuiet_step (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmN : MemoNorm memoF) {n : Nat}
    {id : Ident} {index pass : Nat} {rest : List Ident} {st st' : SkaState M R}
    (hP : PStart memoF id index rest st) (h : PassQuiet env memoF n id index pass st st') :
    PStart memoF id index rest st' ∧ st'.next = st.next ∧ st'.stk = st.stk ∧ dcount st' < dcount st := by
  obtain ⟨ab, members, r, h1, h2, h3, h4, h5, h6, ab', ms', h7, h8, h9⟩ := h
  obtain ⟨hP2, hmem, hq⟩ := pstart_mem env hmF hmN hP h1 h2 h3 h4
  obtain ⟨hchg, hkeep, hcln⟩ := hq h5 h6
  have hstk : st'.stk = st.stk :=
    ((allN env memoF n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st' h3).2 h6
  -- a swept member was dirty at the start
  have hwit : ∃ m ∈ members, dirty m st = true := by
    refine Classical.byContradiction fun hn => ?_
    have hc : ∀ m ∈ members,
        dirty m ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) = false := by
      intro m hm
      cases e : dirty m st with
      | false => exact e
      | true => exact absurd ⟨m, hm, e⟩ hn
    obtain ⟨_, rfl⟩ := memberLoop_clean env memoF n index pass members _ r st' hc h3
    have e7 : ab' = ab := by
      have : above id st.stk = some ab' := h7
      rw [h1] at this; cases this; rfl
    subst e7
    have e8 : ms' = members := by
      have e := sweep_congr (st := st)
        (st' := ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R)) rfl n id
        (Treap.silt ab')
      rw [e, h2] at h8; cases h8; rfl
    subst e8
    obtain ⟨m, hm, hd⟩ := List.any_eq_true.mp h9
    rw [hc m hm] at hd; cases hd
  obtain ⟨m, hm, hdm⟩ := hwit
  refine ⟨hP2, h6, hstk, ?_⟩
  unfold dcount
  rw [hstk]
  refine filter_length_lt st.stk (fun j hj hd' => ?_) ⟨m, hmem m hm, hdm, hcln m hm⟩
  by_cases hjm : j ∈ members
  · rw [hcln j hjm] at hd'; cases hd'
  · obtain ⟨a, b⟩ := hkeep j hj hjm
    rw [dirty_congr a b hchg] at hd'; exact hd'

/-- The invariants of `passOn_inv` across a quiet pass, with every value kept
or lowered. -/
theorem passQuiet_inv (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hi : SInv st) (ht : TInv st) (hw : WInv st)
    (h : PassQuiet env memoF n id index pass st st') :
    SInv st' ∧ TInv st' ∧ WInv st' ∧ ∀ i, SkaModel.OLe (valE st' i) (valE st i) := by
  obtain ⟨ab, members, r, _, _, h3, _, _, h6, _⟩ := h
  have i1 : SInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hi.congr rfl rfl rfl rfl
  have t1 : TInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    ht.congr rfl rfl
  obtain ⟨i2, _, _⟩ := (allP env memoF hmF n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st' []
    (fun _ => False) i1 ⟨st.stk, (List.append_nil _).symm⟩ (fun _ h => h.elim) (fun _ _ h => h) h3
  have t2 := (allPT env memoF hmF hmT n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st' i1 t1 h3
  obtain ⟨w2, L2⟩ := memberLoop_le env memoF hmF hmT hRW n index pass members _ r st' i1 t1 (hw.congr rfl rfl rfl) h3
  have v1 : valE ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) =
      valE st := valE_congr rfl rfl
  have A := (L2 h6).1
  rw [v1] at A
  exact ⟨i2, t2, w2, A⟩

/-! ## 4. Chains of passes, with and without a change -/

section Fam

variable {β : Type} {r : β → β → Prop}

/-- **`fam_finite` with a second way down**: finitely many non-increasing
sequences in a well-founded order and a number, where at every step one of
the sequences falls or the number does, do not exist. -/
theorem fam_finite_q {ι : Type} (wf : WellFounded r) (tr : ∀ a b c, r a b → r b c → r a c) :
    ∀ (L : List ι) (x : ι → Nat → β) (μ : Nat → Nat),
      (∀ k, ∀ i ∈ L, x i (k + 1) = x i k ∨ r (x i (k + 1)) (x i k)) →
      (∀ k, (∃ i ∈ L, r (x i (k + 1)) (x i k)) ∨ μ (k + 1) < μ k) → False
  | [], _, μ, _, hs => by
    have h : ∀ k, μ k + k ≤ μ 0 := by
      intro k
      induction k with
      | zero => exact Nat.le_refl _
      | succ k ih =>
        rcases hs k with ⟨i, hi, _⟩ | h
        · cases hi
        · omega
    have := h (μ 0 + 1); omega
  | a :: L, x, μ, hle, hs => by
    obtain ⟨K, hK⟩ := ev_const wf tr (x a) (fun k => hle k a List.mem_cons_self)
    refine fam_finite_q wf tr L (fun i k => x i (k + K)) (fun k => μ (k + K)) (fun k i hi => ?_) (fun k => ?_)
    · have h := hle (k + K) i (List.mem_cons_of_mem _ hi)
      show x i (k + 1 + K) = x i (k + K) ∨ r (x i (k + 1 + K)) (x i (k + K))
      rw [Nat.add_right_comm k 1 K]; exact h
    · rcases hs (k + K) with ⟨i, hi, h⟩ | h
      · rcases List.mem_cons.mp hi with rfl | hi
        · rw [hK (k + K) (Nat.le_add_left _ _)] at h; exact absurd h (wf_irrefl wf _)
        · refine Or.inl ⟨i, hi, ?_⟩
          show r (x i (k + 1 + K)) (x i (k + K))
          rw [Nat.add_right_comm k 1 K]; exact h
      · refine Or.inr ?_
        show μ (k + 1 + K) < μ (k + K)
        rw [Nat.add_right_comm k 1 K]; exact h

end Fam

/-- A pass that goes on: with a change or a push (`PassOn`), or quiet. -/
def PassGoOn (env : Env R) (memoF : Memo M) (n : Nat) (id : Ident) (index pass : Nat)
    (st st' : SkaState M R) : Prop :=
  PassOn env memoF n id index pass st st' ∨ PassQuiet env memoF n id index pass st st'

/-- The invariant of a chain of passes. -/
def ChainInv (memoF : Memo M) (id : Ident) (index : Nat) (rest : List Ident) (st : SkaState M R) : Prop :=
  SInv st ∧ TInv st ∧ WInv st ∧ PStart memoF id index rest st

theorem passGoOn_inv (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {n : Nat} {id : Ident} {index pass : Nat} {rest : List Ident}
    {st st' : SkaState M R} (hc : ChainInv memoF id index rest st)
    (h : PassGoOn env memoF n id index pass st st') :
    ChainInv memoF id index rest st' ∧ st.next ≤ st'.next ∧
      (st'.next = st.next → (∀ i, SkaModel.OLe (valE st' i) (valE st i)) ∧
        ((∃ i, OLt (valE st' i) (valE st i)) ∨ dcount st' < dcount st)) := by
  obtain ⟨hi, ht, hw, hP⟩ := hc
  rcases h with hon | hq
  · obtain ⟨a, b, c, d, e⟩ := passOn_inv env memoF hmF hmT (run_winv env memoF hmF hmT hmI) hi ht hw hon
    obtain ⟨ab, members, r, h1, h2, h3, h4, _⟩ := hon
    obtain ⟨hP2, _, _⟩ := pstart_mem env hmF hmN hP h1 h2 h3 h4
    exact ⟨⟨a, b, c, hP2⟩, d, fun en => ⟨(e en).1, Or.inl (e en).2⟩⟩
  · obtain ⟨a, b, c, d⟩ := passQuiet_inv env memoF hmF hmT (run_winv env memoF hmF hmT hmI) hi ht hw hq
    obtain ⟨hP2, en, _, hlt⟩ := passQuiet_step env hmF hmN hP hq
    exact ⟨⟨a, b, c, hP2⟩, Nat.le_of_eq en.symm, fun _ => ⟨d, Or.inr hlt⟩⟩

/-- **No infinite sequence of passes that go on, with or without a change,
with `next` bounded**, from a state with `ChainInv`. -/
theorem passMixed_wf (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (id : Ident) (index p B : Nat) (rest : List Ident)
    (f : Nat → SkaState M R) (h0 : ChainInv memoF id index rest (f 0))
    (hon : ∀ k, ∃ n, PassGoOn env memoF n id index (p + k) (f k) (f (k + 1)))
    (hB : ∀ k, (f k).next ≤ B) : False := by
  have inv : ∀ k, ChainInv memoF id index rest (f k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact (passGoOn_inv env hmF hmT hmN hmI ih (hon k).choose_spec).1
  have step := fun k => passGoOn_inv env hmF hmT hmN hmI (inv k) (hon k).choose_spec
  obtain ⟨K, hK⟩ := ev_const (r := fun a b : Nat => a < b) Nat.lt_wfRel.wf (fun _ _ _ => Nat.lt_trans)
    (fun k => B - (f k).next) (fun k => by
      have h1 := (step k).2.1
      have h2 := hB (k + 1)
      show B - (f (k + 1)).next = B - (f k).next ∨ B - (f (k + 1)).next < B - (f k).next
      omega)
  have same : ∀ k, (f (K + k + 1)).next = (f (K + k)).next := by
    intro k
    have h1 := hK (K + k) (Nat.le_add_right _ _)
    have h2 := hB (K + k + 1)
    have h3 := hB (K + k)
    have h4 := (step (K + k)).2.1
    have h1' : B - (f (K + k + 1)).next = B - (f (K + k)).next := h1
    omega
  have le := fun k => ((step (K + k)).2.2 (same k)).1
  have back : ∀ j i, valE (f (K + j)) i ≠ none → valE (f K) i ≠ none := by
    intro j
    induction j with
    | zero => exact fun _ h => h
    | succ j ih => exact fun i h => ih i (ole_ne_none (le j i) h)
  refine fam_finite_q (r := OLt) oLt_wf oLt_trans (f K).stk (fun i k => valE (f (K + k)) i)
    (fun k => dcount (f (K + k))) (fun k i _ => le k i) (fun k => ?_)
  rcases ((step (K + k)).2.2 (same k)).2 with ⟨i, hlt⟩ | hlt
  · exact Or.inl ⟨i, valE_mem (back k i (olt_ne_none hlt)), hlt⟩
  · exact Or.inr hlt

/-! ## 5. The pass loop returns -/

/-- The states that the passes of the component of `id` reach from `x`, each
pass going on (with or without a change) at some fuel. -/
inductive PassReachQ (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R) :
    Nat × SkaState M R → Prop
  | refl : PassReachQ env memoF id index x x
  | step {y : Nat × SkaState M R} {st' : SkaState M R} {m : Nat} :
      PassReachQ env memoF id index x y → PassGoOn env memoF m id index y.1 y.2 st' →
      PassReachQ env memoF id index x (y.1 + 1, st')

theorem passReachQ_inv (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {id : Ident} {index : Nat} {rest : List Ident}
    {x y : Nat × SkaState M R} (h : PassReachQ env memoF id index x y) (hc : ChainInv memoF id index rest x.2) :
    ChainInv memoF id index rest y.2 := by
  induction h with
  | refl => exact hc
  | step _ hp ih => exact (passGoOn_inv env hmF hmT hmN hmI ih hp).1

/-- One pass that goes on, among the states reached from `x`: from `b` to `a`. -/
def PassNextQ (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R)
    (a b : Nat × SkaState M R) : Prop :=
  PassReachQ env memoF id index x b ∧ ∃ m, a.1 = b.1 + 1 ∧ PassGoOn env memoF m id index b.1 b.2 a.2

/-- **Finitely many pushes along every chain of passes from `x`**, quiet
passes included (`FinPushes` over `PassNextQ`). -/
def FinPushesQ (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R) : Prop :=
  ∀ f : Nat → Nat × SkaState M R, (∀ k, PassNextQ env memoF id index x (f (k + 1)) (f k)) →
    ∃ B, ∀ k, (f k).2.next ≤ B

/-- A bound on `next` over the reached states gives `FinPushesQ`. -/
theorem finPushesQ_of_bound {env : Env R} {memoF : Memo M} {id : Ident} {index B : Nat}
    {x : Nat × SkaState M R} (hB : ∀ y, PassReachQ env memoF id index x y → y.2.next ≤ B) :
    FinPushesQ env memoF id index x :=
  fun f hf => ⟨B, fun k => hB _ (hf k).1⟩

theorem passNextQ_acc (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {id : Ident} {index : Nat} {rest : List Ident}
    (x : Nat × SkaState M R) (hc : ChainInv memoF id index rest x.2) (hB : FinPushesQ env memoF id index x) :
    Acc (PassNextQ env memoF id index x) x := by
  refine acc_of_no_chain (fun f hf => ?_) x
  obtain ⟨B, hB'⟩ := hB f hf
  have hreach : ∀ k, PassReachQ env memoF id index x (f k) := fun k => (hf k).1
  have hidx : ∀ k, (f k).1 = (f 0).1 + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      obtain ⟨_, m, e, _⟩ := hf k
      rw [e, ih]; rfl
  exact passMixed_wf env hmF hmT hmN hmI id index (f 0).1 B rest (fun k => (f k).2)
    (passReachQ_inv env hmF hmT hmN hmI (hreach 0) hc)
    (fun k => by obtain ⟨_, m, _, hp⟩ := hf k; exact ⟨m, by rw [← hidx k]; exact hp⟩) hB'

/-- **The pass loop returns at some fuel** from a state with `ChainInv`, if at
every state the passes reach the pass stops on its own, goes on with a change,
or goes on quietly, at some fuel, and every chain of passes pushes finitely
often.  Quiet passes are no longer excluded (compare `passLoop_returns_fin`). -/
theorem passLoop_returns_q (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (id : Ident) (index : Nat) (rest : List Ident)
    (x : Nat × SkaState M R) (hc : ChainInv memoF id index rest x.2)
    (hB : FinPushesQ env memoF id index x)
    (hparts : ∀ y, PassReachQ env memoF id index x y → ∃ m,
      (∃ r, passStep m (memberLoop env memoF m) (fun _ _ _ _ => none) id index y.1 y.2 = some r) ∨
      ∃ st', PassGoOn env memoF m id index y.1 y.2 st') :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r := by
  suffices H : ∀ y, Acc (PassNextQ env memoF id index x) y → PassReachQ env memoF id index x y →
      ∃ n r, passLoop env memoF n id index y.1 y.2 = some r from
    H x (passNextQ_acc env hmF hmT hmN hmI x hc hB) PassReachQ.refl
  intro y hacc
  induction hacc with
  | intro y _ ih =>
    intro hy
    obtain ⟨m, hstop | ⟨st', hon⟩⟩ := hparts y hy
    · obtain ⟨r, hr⟩ := hstop
      refine ⟨m + 2, r, ?_⟩
      rw [passLoop_succ]
      exact passStep_le m (fun index pass ms st => (fuelStep env memoF m).mem index pass ms st)
        (fun _ _ _ _ _ h => by cases h) id index y.1 y.2 r hr
    · obtain ⟨n', r', hr'⟩ := ih (y.1 + 1, st') ⟨hy, m, rfl, hon⟩ (PassReachQ.step hy hon)
      refine ⟨max m n' + 1, r', ?_⟩
      have e : passLoop env memoF (max m n' + 1) id index y.1 y.2 =
          passLoop env memoF (max m n') id index (y.1 + 1) st' := by
        rcases hon with hon | hon
        · exact passLoop_of_on (passOn_mono (Nat.le_max_left m n') hon)
        · exact passLoop_of_quiet (passQuiet_mono (Nat.le_max_left m n') hon)
      rw [e]
      exact passLoop_fuel_le env memoF (Nat.le_max_right m n') id index (y.1 + 1) st' r' hr'

end Ana
end SkaModel
end Formalization
