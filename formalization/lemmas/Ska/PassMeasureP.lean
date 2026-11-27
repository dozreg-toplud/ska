import lemmas.Ska.PassMeasureN

/-!
# The pass loop of `+analyze` ends (track F, Gaps 16)

The measure of a component: `next` (`B - next`, for a bound `B` on it), then
the members' entries, each as `valE st i` (the tuple `entryM` of the entry of
`i` if `i` is on the stack, else `none`, below every tuple), compared
pointwise: every identity stays or falls (`OLe`), one falls (`OLt`).

A pass that goes on (`PassOn`: the member loop came back with the lowlink
`index`, `+cull` ran, and `changed` or `next` grew; then the pass loop calls
itself, `passLoop_of_on`) raises `next`, or leaves it and lowers the entries:
with `next` the same the member loop runs on the same stack (`allN`), each
`+run` keeps its entry or lowers its tuple (`Ana.run_entry_step`), one run
reported `changed` (so lowered it, `runDatum_changed`), the other members'
entries are left alone (`Keep` of `RunP`), and `+cull` drops members, which
lowers their value to `none` (`valE_sub`).  `passOn_wf`: there is no infinite
sequence of such passes, by `ev_const` (`next` is bounded, so it stops
growing) and `fam_finite` (finitely many identities, each non-increasing in a
well-founded order, one falling at every step).

Two hypotheses are named:
* `RunStkW`: a `+run` keeps every stack member's entry `RunW` (the stack
  invariant of `Ska/PassMeasureE.lean`; `runW_bunt`, `runW_runDatum` show it
  of the writes, with the normality of the `indi` of `fol-loop` open);
* the bound `B` on `next` along the passes: `next` counts the pushes, and a
  push is at an identity not in the graph; this follows from finitely many
  identities (`+he-sock` is Kruskal's embedding over finitely many leaves,
  argued in `Ska/AnaEnds.lean`, not proved) and point (b) (an identity that
  `+cull` drops is not pushed again: on the compiler 21 members culled, none
  analysed again).  Without (b) a pass could push an identity, `+cull` drop
  it and the next pass push it again; the bound `B` rules that out with the
  rest.

`tools/hoon/passmeasure.py --passes` checks this measure on the recorded
corpus: 5,058 passes that reached `%pm-end`, 2,446 went on (947 with a push,
1,499 with `next` the same, every run of those kept or lowered its tuple and
one lowered it, and the next pass had no more members), 0 against it.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## 1. Orders -/

theorem lex_trans {α β : Type} {ra : α → α → Prop} {rb : β → β → Prop}
    (ha : ∀ a b c, ra a b → ra b c → ra a c) (hb : ∀ a b c, rb a b → rb b c → rb a c) :
    ∀ a b c, Prod.Lex ra rb a b → Prod.Lex ra rb b c → Prod.Lex ra rb a c := by
  intro a b c h1 h2
  cases h1 with
  | left _ _ h =>
    cases h2 with
    | left _ _ h' => exact Prod.Lex.left _ _ (ha _ _ _ h h')
    | right _ _ => exact Prod.Lex.left _ _ h
  | right _ h =>
    cases h2 with
    | left _ _ h' => exact Prod.Lex.left _ _ h'
    | right _ h' => exact Prod.Lex.right _ (hb _ _ _ h h')

theorem nat_lt_trans' : ∀ a b c : Nat, a < b → b < c → a < c := fun _ _ _ => Nat.lt_trans

theorem lexM8_trans : ∀ a b c : M8, lexM8.rel a b → lexM8.rel b c → lexM8.rel a c :=
  lex_trans nat_lt_trans' (lex_trans nat_lt_trans' (lex_trans nat_lt_trans' (lex_trans nat_lt_trans'
    (lex_trans nat_lt_trans' (lex_trans nat_lt_trans' (lex_trans nat_lt_trans' nat_lt_trans'))))))

theorem wf_irrefl {β : Type} {r : β → β → Prop} (wf : WellFounded r) (a : β) : ¬ r a a := by
  have h := wf.apply a
  induction h with
  | intro y _ ih => exact fun hy => ih y hy hy

/-- The order of a member's value: `none` (not on the stack) below every tuple. -/
def OLt : Option M8 → Option M8 → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some x, some y => lexM8.rel x y

def OLe (a b : Option M8) : Prop := a = b ∨ OLt a b

theorem oLt_trans (a b c : Option M8) (h1 : OLt a b) (h2 : OLt b c) : OLt a c := by
  cases a <;> cases b <;> cases c <;> simp only [OLt] at h1 h2 ⊢
  exact lexM8_trans _ _ _ h1 h2

theorem oLt_wf : WellFounded OLt := by
  have hn : Acc OLt none := ⟨_, fun y h => by cases y <;> simp [OLt] at h⟩
  have hs : ∀ x, Acc OLt (some x) := by
    intro x
    have hx := lexM8.wf.apply x
    induction hx with
    | intro x _ ih =>
      exact ⟨_, fun y h => by
        cases y with
        | none => exact hn
        | some y => exact ih y h⟩
  exact ⟨fun a => by cases a with | none => exact hn | some x => exact hs x⟩

theorem ole_trans {a b c : Option M8} (h1 : OLe a b) (h2 : OLe b c) : OLe a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (oLt_trans _ _ _ h1 h2)

theorem ole_lt_trans {a b c : Option M8} (h1 : OLe a b) (h2 : OLt b c) : OLt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact oLt_trans _ _ _ h1 h2

theorem olt_le_trans {a b c : Option M8} (h1 : OLt a b) (h2 : OLe b c) : OLt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact oLt_trans _ _ _ h1 h2

theorem ole_none (a : Option M8) : OLe none a := by
  cases a with
  | none => exact Or.inl rfl
  | some _ => exact Or.inr trivial

theorem olt_ne_none {a b : Option M8} (h : OLt a b) : b ≠ none := by
  intro e; subst e; cases a <;> exact h

theorem ole_ne_none {a b : Option M8} (h : OLe a b) (ha : a ≠ none) : b ≠ none := by
  rcases h with rfl | h
  · exact ha
  · exact olt_ne_none h

/-! ## 2. Non-increasing families in a well-founded order -/

section Fam

variable {β : Type} {r : β → β → Prop}

/-- **A non-increasing sequence in a well-founded order is eventually constant.** -/
theorem ev_const (wf : WellFounded r) (tr : ∀ a b c, r a b → r b c → r a c)
    (x : Nat → β) (hx : ∀ k, x (k + 1) = x k ∨ r (x (k + 1)) (x k)) :
    ∃ K, ∀ k, K ≤ k → x (k + 1) = x k := by
  have le_d : ∀ K d, x (K + d) = x K ∨ r (x (K + d)) (x K) := by
    intro K d
    induction d with
    | zero => exact Or.inl rfl
    | succ d ih =>
      show x (K + d + 1) = x K ∨ r (x (K + d + 1)) (x K)
      rcases hx (K + d) with e | e
      · rw [e]; exact ih
      · rcases ih with ih | ih
        · rw [← ih]; exact Or.inr e
        · exact Or.inr (tr _ _ _ e ih)
  have key : ∀ v, Acc r v → ∀ K, x K = v → ∃ K', ∀ k, K' ≤ k → x (k + 1) = x k := by
    intro v hv
    induction hv with
    | intro v _ ih =>
      intro K hK
      by_cases h : ∀ k, K ≤ k → x (k + 1) = x k
      · exact ⟨K, h⟩
      · have : ∃ k, K ≤ k ∧ x (k + 1) ≠ x k := by
          apply Classical.byContradiction
          intro hn
          apply h
          intro k hk
          apply Classical.byContradiction
          intro hne
          exact hn ⟨k, hk, hne⟩
        obtain ⟨k, hk, hne⟩ := this
        have h1 : r (x (k + 1)) (x k) := (hx k).resolve_left hne
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
        have h2 : r (x (K + d + 1)) v := by
          rcases le_d K d with e | e
          · rw [e, hK] at h1; exact h1
          · rw [hK] at e; exact tr _ _ _ h1 e
        exact ih _ h2 (K + d + 1) rfl
  exact key _ (wf.apply _) 0 rfl

/-- **Finitely many non-increasing sequences, one falling at every step, do
not exist** in a well-founded order. -/
theorem fam_finite {ι : Type} (wf : WellFounded r) (tr : ∀ a b c, r a b → r b c → r a c) :
    ∀ (L : List ι) (x : ι → Nat → β), (∀ k, ∀ i ∈ L, x i (k + 1) = x i k ∨ r (x i (k + 1)) (x i k)) →
      (∀ k, ∃ i ∈ L, r (x i (k + 1)) (x i k)) → False
  | [], _, _, hs => by obtain ⟨i, hi, _⟩ := hs 0; cases hi
  | a :: L, x, hle, hs => by
    obtain ⟨K, hK⟩ := ev_const wf tr (x a) (fun k => hle k a List.mem_cons_self)
    refine fam_finite wf tr L (fun i k => x i (k + K)) (fun k i hi => ?_) (fun k => ?_)
    · have h := hle (k + K) i (List.mem_cons_of_mem _ hi)
      show x i (k + 1 + K) = x i (k + K) ∨ r (x i (k + 1 + K)) (x i (k + K))
      rw [Nat.add_right_comm k 1 K]; exact h
    · obtain ⟨i, hi, h⟩ := hs (k + K)
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hK (k + K) (Nat.le_add_left _ _)] at h; exact absurd h (wf_irrefl wf _)
      · refine ⟨i, hi, ?_⟩
        show r (x i (k + 1 + K)) (x i (k + K))
        rw [Nat.add_right_comm k 1 K]; exact h

end Fam

/-! ## 3. The members' values -/

theorem entryM_same {bus : Sock} {d old : Datum} (h : EntrySame d old) : entryM bus d = entryM bus old := by
  obtain ⟨a, b, c, e, f⟩ := h
  unfold entryM; rw [a, b, c, e, f]

/-- **`changed` of `+run` is the change of the five fields.** -/
theorem runDatum_changed (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (h : (runDatum moved bus out gen' old).2.2 = true) : ¬ EntrySame (runDatum moved bus out gen' old).1 old := by
  intro hs
  have e : (runDatum moved bus out gen' old).2.2 = decide (((runDatum moved bus out gen' old).1.less,
      (runDatum moved bus out gen' old).1.prod, (runDatum moved bus out gen' old).1.map,
      (runDatum moved bus out gen' old).1.indi, (runDatum moved bus out gen' old).1.seek) ≠
      (old.less, old.prod, old.map, old.indi, old.seek)) := rfl
  rw [e] at h
  obtain ⟨a, b, c, d, f⟩ := hs
  rw [a, b, c, d, f] at h
  simp at h

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- The value of `i` in the measure: the tuple of its entry if it is on the stack. -/
def valE (st : SkaState M R) (i : Ident) : Option M8 :=
  if i ∈ st.stk then (gCore st.g i).map (entryM i.1) else none

theorem valE_congr {st st' : SkaState M R} (h1 : st'.g = st.g) (h2 : st'.stk = st.stk) :
    valE st' = valE st := by
  funext i; unfold valE; rw [h1, h2]

theorem valE_mem {st : SkaState M R} {i : Ident} (h : valE st i ≠ none) : i ∈ st.stk := by
  unfold valE at h
  split at h
  · assumption
  · exact absurd rfl h

/-- `st'` has fewer stack members than `st`, with the same entries. -/
def SubSt (st' st : SkaState M R) : Prop :=
  (∀ i ∈ st'.stk, i ∈ st.stk) ∧ ∀ i ∈ st'.stk, ∀ d, gCore st'.g i = some d → gCore st.g i = some d

theorem SubSt.trans {a b c : SkaState M R} (h1 : SubSt a b) (h2 : SubSt b c) : SubSt a c :=
  ⟨fun i hi => h2.1 i (h1.1 i hi), fun i hi d hd => h2.2 i (h1.1 i hi) d (h1.2 i hi d hd)⟩

theorem valE_sub {st st' : SkaState M R} (h : SubSt st' st) (i : Ident) : OLe (valE st' i) (valE st i) := by
  unfold valE
  by_cases hi : i ∈ st'.stk
  · rw [if_pos hi, if_pos (h.1 i hi)]
    cases e : gCore st'.g i with
    | none => exact ole_none _
    | some d => rw [h.2 i hi d e]; exact Or.inl rfl
  · rw [if_neg hi]; exact ole_none _

theorem cullFold_sub (l : List (Ident × Unit)) (st : SkaState M R) : SubSt (l.foldl cullStep st) st := by
  obtain ⟨a1, _, _, a4, _⟩ := cullFold_ok l st
  refine ⟨fun i hi => a1 ▸ hi, fun i _ d hd => ?_⟩
  simp only [gCore] at hd ⊢
  rw [a4] at hd
  split at hd
  · simp at hd
  · exact hd

/-- **`+cull` drops members and keeps the others' entries.** -/
theorem cull_sub {n : Nat} {id : Ident} {st st' : SkaState M R} (h : cull n id st = some st') :
    SubSt st' st := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, _, live, _, hst⟩ := h
  split at hst
  · subst hst; exact ⟨fun i h => h, fun i _ d h => h⟩
  · subst hst
    exact SubSt.trans (cullFold_sub _ _) ⟨fun i hi => (List.mem_filter.mp hi).1, fun i _ d h => h⟩

theorem cull_above {n : Nat} {id : Ident} {st st' : SkaState M R} (h : cull n id st = some st') :
    ∃ ab, above id st.stk = some ab := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨ab, hab, _⟩ := h
  exact ⟨ab, hab⟩

/-- A run of `m` on the same stack: the others stay, `m` stays or falls. -/
theorem valE_run {st st' : SkaState M R} {m : Ident} {old new : Datum} (hs : st'.stk = st.stk)
    (hg : ∀ j, j ∈ st.stk ∧ j ≠ m → Treap.get st'.g j = Treap.get st.g j)
    (ho : gCore st.g m = some old) (hn : gCore st'.g m = some new)
    (hst : EntrySame new old ∨ EntryLt m.1 new old) :
    (∀ i, OLe (valE st' i) (valE st i)) ∧ (¬ EntrySame new old → m ∈ st.stk → OLt (valE st' m) (valE st m)) := by
  have em : m ∈ st.stk → valE st' m = some (entryM m.1 new) ∧ valE st m = some (entryM m.1 old) := by
    intro hm
    unfold valE; rw [hs]; simp [hm, ho, hn]
  refine ⟨fun i => ?_, fun hne hm => ?_⟩
  · by_cases hi : i ∈ st.stk
    · by_cases e : i = m
      · subst e
        obtain ⟨e1, e2⟩ := em hi
        rw [e1, e2]
        rcases hst with h | h
        · exact Or.inl (by rw [entryM_same h])
        · exact Or.inr h
      · left
        unfold valE; rw [hs]; simp [hi, gCore, hg i ⟨hi, e⟩]
    · left; unfold valE; rw [hs]; simp [hi]
  · obtain ⟨e1, e2⟩ := em hm
    rw [e1, e2]
    exact hst.resolve_left hne

/-! ## 4. The stack invariant, named -/

/-- **The stack invariant**: every stack member's entry is `RunW`. -/
def StkW (st : SkaState M R) : Prop := ∀ i ∈ st.stk, ∀ d, gCore st.g i = some d → RunW i.1 d

theorem stkW_sub {st st' : SkaState M R} (h : StkW st) (hs : SubSt st' st) : StkW st' :=
  fun i hi d hd => h i (hs.1 i hi) d (hs.2 i hi d hd)

/-- **The named hypothesis**: a `+run` of a stack member keeps the stack invariant. -/
def RunStkW (run : RunGo M R) : Prop :=
  ∀ id index st r st', SInv st → TInv st → StkW st → id ∈ st.stk → run id index st = some (r, st') → StkW st'

/-- **`changed` of a run means its entry changed.** -/
theorem run_changed (env : Env R) (memoF : Memo M) (n : Nat) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {r : Nat × Bool × Bool} (hi : SInv st) (hid : id ∈ st.stk)
    (h : run env memoF n id index st = some (r, st')) {old new : Datum}
    (ho : gCore st.g id = some old) (hn : gCore st'.g id = some new) (hc : r.2.2 = true) :
    ¬ EntrySame new old := by
  cases n with
  | zero => rw [run_zero] at h; cases h
  | succ n =>
    rw [run_succ] at h
    unfold runStep at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨out, gs⟩, _, e⟩ := h
    cases e
    obtain ⟨d0, hd0⟩ := hi.mem_g hid
    have hgit : gitG ({ st with stats := { st.stats with runs := st.stats.runs + 1 } } : SkaState M R).g id = d0 := by
      simp [gitG, Treap.gut, hd0]
    have eo : old = d0.core := by simp [gCore, hd0] at ho; exact ho.symm
    have hn' := (runEnd_get id _ out gs).symm.trans hn
    rw [hgit] at hn'
    have en := Option.some.inj hn'
    have hc' : (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen
        (gitG ({ st with stats := { st.stats with runs := st.stats.runs + 1 } } : SkaState M R).g id).core).2.2 = true := hc
    rw [hgit] at hc'
    rw [← en, eo]
    exact runDatum_changed _ _ _ _ _ hc'

/-! ## 5. The member loop -/

/-- **The member loop with `next` the same** keeps every member's value or
lowers it, and lowers one when it reports `changed`; it keeps the stack
invariant. -/
theorem memberLoop_le (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) :
    ∀ n index pass ms (st : SkaState M R) r st', SInv st → TInv st → StkW st →
      memberLoop env memoF n index pass ms st = some (r, st') →
      StkW st' ∧ (st'.next = st.next → (∀ i, OLe (valE st' i) (valE st i)) ∧
        (r.2 = true → ∃ i, OLt (valE st' i) (valE st i)))
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
      exact ⟨hw, fun _ => ⟨fun i => Or.inl rfl, fun h => by cases h⟩⟩
    | cons m ms =>
      have key : ∀ st1 : SkaState M R,
          ((Treap.get st.order m).bind fun o => (run env memoF n m o st1).bind fun r =>
            if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
            (memberLoop env memoF n index pass ms r.2).map fun t =>
              ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
          st1.g = st.g → st1.done = st.done → st1.order = st.order → st1.stk = st.stk →
          st1.next = st.next →
          StkW st' ∧ (st'.next = st.next → (∀ i, OLe (valE st' i) (valE st i)) ∧
            (r.2 = true → ∃ i, OLt (valE st' i) (valE st i))) := by
        intro st1 e h1 h2 h3 h4 h5
        simp only [Option.bind_eq_some_iff] at e
        obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
        have i1 : SInv st1 := hi.congr h1 h2 h3 h4
        have t1 : TInv st1 := ht.congr h1 h2
        have w1 : StkW st1 := by
          intro i hi' d hd; rw [h4] at hi'; rw [h1] at hd; exact hw i hi' d hd
        have hm1 : m ∈ st1.stk := (i1.ord_stk m).mp ⟨o, by rw [h3]; exact ho⟩
        obtain ⟨i2, _, k2⟩ := run_ok env memoF hmF n m o st1 r1 st2 i1 hm1 hr
        have t2 := (allPT env memoF hmF hmT n n (Nat.le_refl n)).2.2.1 m o st1 r1 st2 i1 t1 hm1 hr
        have w2 := hRW n m o st1 r1 st2 i1 t1 w1 hm1 hr
        have n2 := (allN env memoF n n (Nat.le_refl n)).2.2.1 m o st1 r1 st2 hr
        have v1 : valE st1 = valE st := valE_congr h1 h4
        have runle : st2.next = st1.next → (∀ i, OLe (valE st2 i) (valE st1 i)) ∧
            (r1.2.2 = true → ∃ i, OLt (valE st2 i) (valE st1 i)) := by
          intro en
          obtain ⟨old, new, ho', hn', hst⟩ := run_entry_step env memoF n i1 t1 hm1 hr (w1 m hm1)
          have hs2 : st2.stk = st1.stk := n2.2 en
          obtain ⟨A, B⟩ := valE_run hs2 (fun j hj => k2.2.2 j hj) ho' hn' hst
          exact ⟨A, fun hc => ⟨m, B (run_changed env memoF n i1 hm1 hr ho' hn' hc) hm1⟩⟩
        split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          refine ⟨w2, fun en => ?_⟩
          rw [← v1]
          exact runle (en.trans h5.symm)
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨⟨t1', st3⟩, ht', e⟩ := e
          cases e
          obtain ⟨w3, L3⟩ := memberLoop_le env memoF hmF hmT hRW n index pass ms st2 t1' st3 i2 t2 w2 ht'
          refine ⟨w3, fun en => ?_⟩
          have n3 := (allN env memoF n n (Nat.le_refl n)).2.2.2.2 index pass ms st2 t1' st3 ht'
          have e2 : st2.next = st1.next := Nat.le_antisymm (by rw [h5, ← en]; exact n3.1) n2.1
          have e3 : st3.next = st2.next := by rw [en, ← h5, e2]
          obtain ⟨A1, B1⟩ := runle e2
          obtain ⟨A2, B2⟩ := L3 e3
          rw [← v1]
          refine ⟨fun i => ole_trans (A2 i) (A1 i), fun hc => ?_⟩
          simp only [Bool.or_eq_true] at hc
          rcases hc with hc | hc
          · obtain ⟨i, hlt⟩ := B1 hc
            exact ⟨i, ole_lt_trans (A2 i) hlt⟩
          · obtain ⟨i, hlt⟩ := B2 hc
            exact ⟨i, olt_le_trans hlt (A1 i)⟩
      simp only [memberStep] at h
      split at h
      · exact memberLoop_le env memoF hmF hmT hRW n index pass ms st r st' hi ht hw h
      · by_cases hp : pass > 1
        · simp only [hp, if_true] at h
          exact key _ h rfl rfl rfl rfl rfl
        · simp only [hp, if_false] at h
          exact key _ h rfl rfl rfl rfl rfl

/-! ## 6. The pass loop -/

/-- **One pass of the component of `id` that goes on**: the member loop came
back with the lowlink `index`, `+cull` ran, and `changed` was reported or
`next` grew. -/
def PassOn (env : Env R) (memoF : Memo M) (n : Nat) (id : Ident) (index pass : Nat)
    (st st' : SkaState M R) : Prop :=
  ∃ ab members r st2, above id st.stk = some ab ∧ sweep n id (Treap.silt ab) st = some members ∧
    memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st2) ∧
    r.1 = index ∧ cull n id st2 = some st' ∧ ¬ (r.2 = false ∧ st'.next = st.next)

/-- **A pass that goes on is the pass loop calling itself.** -/
theorem passLoop_of_on {env : Env R} {memoF : Memo M} {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (h : PassOn env memoF n id index pass st st') :
    passLoop env memoF (n + 1) id index pass st = passLoop env memoF n id index (pass + 1) st' := by
  obtain ⟨ab, members, r, st2, h1, h2, h3, h4, h5, h6⟩ := h
  rw [passLoop_succ]
  unfold passStep
  simp only [h1, h2, Option.bind_some, h3]
  split
  · rename_i hc; exact absurd h4 hc
  · simp only [h5, Option.bind_some]
    split
    · rename_i hc; exact absurd hc h6
    · rfl

/-- The invariants along a sequence of passes. -/
theorem passOn_inv (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hi : SInv st) (ht : TInv st) (hw : StkW st)
    (h : PassOn env memoF n id index pass st st') :
    SInv st' ∧ TInv st' ∧ StkW st' ∧ st.next ≤ st'.next ∧
      (st'.next = st.next → (∀ i, OLe (valE st' i) (valE st i)) ∧ ∃ i, OLt (valE st' i) (valE st i)) := by
  obtain ⟨ab, members, r, st2, _, _, h3, _, h5, h6⟩ := h
  have i1 : SInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hi.congr rfl rfl rfl rfl
  have t1 : TInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    ht.congr rfl rfl
  obtain ⟨i2, _, _⟩ := (allP env memoF hmF n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st2 []
    (fun _ => False) i1 ⟨st.stk, (List.append_nil _).symm⟩ (fun _ h => h.elim) (fun _ _ h => h) h3
  have t2 := (allPT env memoF hmF hmT n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st2 i1 t1 h3
  obtain ⟨w2, L2⟩ := memberLoop_le env memoF hmF hmT hRW n index pass members _ r st2 i1 t1 hw h3
  have n2 := (allN env memoF n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st2 h3
  have c5 := cull_next h5
  obtain ⟨ab', hab'⟩ := cull_above h5
  obtain ⟨ab0, rest, _, hs', _⟩ := above_eq hab'
  obtain ⟨i3, _, _⟩ := cull_ok i2 h5 hs'
  have S := cull_sub h5
  refine ⟨i3, cull_tp t2 h5, stkW_sub w2 S, by rw [c5]; exact n2.1, fun en => ?_⟩
  have en2 : st2.next = st.next := c5.symm.trans en
  obtain ⟨A, B⟩ := L2 en2
  have hr : r.2 = true := by
    cases e : r.2 with
    | true => rfl
    | false => exact absurd ⟨e, en⟩ h6
  obtain ⟨i, hlt⟩ := B hr
  have v1 : valE ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) =
      valE st := valE_congr rfl rfl
  rw [v1] at A hlt
  exact ⟨fun j => ole_trans (valE_sub S j) (A j), i, ole_lt_trans (valE_sub S i) hlt⟩

/-- **The pass loop of `+analyze` ends**: there is no infinite sequence of
passes of a component that go on, from a state with the construction, tidy
and stack invariants, when `+run` keeps the stack invariant (`RunStkW`) and
`next` stays below a bound `B` along the passes (the bound on the number of
functions analysed: finitely many identities and no culled member pushed
again). -/
theorem passOn_wf (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) (n : Nat) (id : Ident) (index p B : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : StkW (f 0))
    (hon : ∀ k, PassOn env memoF n id index (p + k) (f k) (f (k + 1)))
    (hB : ∀ k, (f k).next ≤ B) : False := by
  have inv : ∀ k, SInv (f k) ∧ TInv (f k) ∧ StkW (f k) := by
    intro k
    induction k with
    | zero => exact ⟨h0i, h0t, h0w⟩
    | succ k ih =>
      obtain ⟨a, b, c, _, _⟩ := passOn_inv env memoF hmF hmT hRW ih.1 ih.2.1 ih.2.2 (hon k)
      exact ⟨a, b, c⟩
  have step := fun k => passOn_inv env memoF hmF hmT hRW (inv k).1 (inv k).2.1 (inv k).2.2 (hon k)
  obtain ⟨K, hK⟩ := ev_const (r := fun a b : Nat => a < b) Nat.lt_wfRel.wf (fun _ _ _ => Nat.lt_trans)
    (fun k => B - (f k).next) (fun k => by
      have h1 := (step k).2.2.2.1
      have h2 := hB (k + 1)
      show B - (f (k + 1)).next = B - (f k).next ∨ B - (f (k + 1)).next < B - (f k).next
      omega)
  have same : ∀ k, (f (K + k + 1)).next = (f (K + k)).next := by
    intro k
    have h1 := hK (K + k) (Nat.le_add_right _ _)
    have h2 := hB (K + k + 1)
    have h3 := hB (K + k)
    have h4 := (step (K + k)).2.2.2.1
    have h1' : B - (f (K + k + 1)).next = B - (f (K + k)).next := h1
    omega
  have le := fun k => ((step (K + k)).2.2.2.2 (same k)).1
  have back : ∀ j i, valE (f (K + j)) i ≠ none → valE (f K) i ≠ none := by
    intro j
    induction j with
    | zero => exact fun _ h => h
    | succ j ih => exact fun i h => ih i (ole_ne_none (le j i) h)
  refine fam_finite (r := OLt) oLt_wf oLt_trans (f K).stk (fun i k => valE (f (K + k)) i)
    (fun k i _ => le k i) (fun k => ?_)
  obtain ⟨i, hlt⟩ := ((step (K + k)).2.2.2.2 (same k)).2
  exact ⟨i, valE_mem (back k i (olt_ne_none hlt)), hlt⟩

end Ana

end SkaModel
end Formalization
