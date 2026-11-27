import lemmas.Ska.SccLoop

/-! # Where the loop of `+compile-scc-in` puts entries (README Gaps 21.13)

* `compileSccIn_ml_some`: after `compileSccIn c false`, every member has an entry (the final pass
  compiles each member of `c.scc`).
* `compileSccIn_ml_out`: a bell outside `c.scc` has none (the sweeps run over `c.order`, inside
  `c.scc`, and the final pass over `c.scc`; the loop starts from no entry). -/

namespace Formalization.SkaModel.SccLoop

variable {B N : Type} [DecidableEq B] [DecidableEq N]

theorem foldl_member_some (c : Cfg B N) (top : B → N) (m : Mode) (keep : Bool) :
    ∀ (l : List B) (st : St B N) (b : B), (b ∈ l ∨ (st.ml b).isSome) →
      ((l.foldl (fun st x => (member c top x m keep st).2) st).ml b).isSome := by
  intro l
  induction l with
  | nil => intro st b h; simpa using h
  | cons x l ih =>
    intro st b h
    simp only [List.foldl_cons]
    apply ih
    by_cases hb : b = x
    · subst hb; right; exact (member_ml_some c top b m keep st).1
    · rcases h with h | h
      · rcases List.mem_cons.1 h with h | h
        · exact absurd h hb
        · left; exact h
      · right; rw [(member_ml_ne c top x m keep st hb).1]; exact h

theorem final_ml_some (c : Cfg B N) (keep : Bool) (st : St B N) :
    ∀ b ∈ c.scc, ((final c keep st).ml b).isSome :=
  fun b hb => foldl_member_some c _ _ _ c.scc st b (Or.inl hb)

/-- **Every member has an entry** after `compileSccIn c false`. -/
theorem compileSccIn_ml_some (c : Cfg B N) (fuel : Nat) (st0 s : St B N)
    (h : compileSccIn c false fuel st0 = some s) : ∀ b ∈ c.scc, (s.ml b).isSome := by
  unfold compileSccIn at h
  simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at h
  obtain ⟨s', -, rfl⟩ := h
  exact final_ml_some c true s'

theorem foldl_member_out (c : Cfg B N) (top : B → N) (m : Mode) (keep : Bool) :
    ∀ (l : List B) (st : St B N) (k : B), k ∉ l →
      (l.foldl (fun st x => (member c top x m keep st).2) st).ml k = st.ml k := by
  intro l
  induction l with
  | nil => intro st k _; rfl
  | cons x l ih =>
    intro st k hk
    simp only [List.foldl_cons]
    rw [ih _ k (fun h => hk (List.mem_cons_of_mem _ h))]
    exact (member_ml_ne c top x m keep st (fun h => hk (h ▸ List.mem_cons_self ..))).1

theorem sweepStep_ml_ne (c : Cfg B N) (top : B → N) (st : St B N) {b k : B} (hk : k ≠ b) :
    (sweepStep c top st b).ml k = st.ml k := by
  unfold sweepStep
  split
  · exact (member_ml_ne c top b Mode.must _ st hk).1
  · rfl

theorem sweep_ml_out (c : Cfg B N) (top : B → N) (k : B) (hk : k ∉ c.order) :
    ∀ st : St B N, (sweep c top st).ml k = st.ml k := by
  unfold sweep
  generalize c.order = l at hk
  induction l with
  | nil => intro st; rfl
  | cons x l ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih (fun h => hk (List.mem_cons_of_mem _ h))]
    exact sweepStep_ml_ne c top st (fun h => hk (h ▸ List.mem_cons_self ..))

theorem loop_ml_out (c : Cfg B N) (top : B → N) (k : B) (hk : k ∉ c.order) :
    ∀ (n : Nat) (st s : St B N), loop c top n st = some s → s.ml k = st.ml k := by
  intro n
  induction n with
  | zero => intro st s h; simp [loop] at h
  | succ n ih =>
    intro st s h
    simp only [loop] at h
    split at h
    · rw [ih _ _ h]; exact sweep_ml_out c top k hk st
    · simp only [Option.some.injEq] at h; subst h; exact sweep_ml_out c top k hk st

/-- **No entry outside the SCC** after `compileSccIn c false`, when `order` is inside `scc`. -/
theorem compileSccIn_ml_out (c : Cfg B N) (hsub : ∀ b ∈ c.order, b ∈ c.scc) (fuel : Nat)
    (st0 s : St B N) (h : compileSccIn c false fuel st0 = some s) (k : B) (hk : k ∉ c.scc) :
    s.ml k = none := by
  unfold compileSccIn at h
  simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at h
  obtain ⟨s', hl, rfl⟩ := h
  unfold final
  rw [foldl_member_out c _ _ _ c.scc s' k hk, loop_ml_out c _ k (fun h => hk (hsub k h)) fuel _ s' hl]

end Formalization.SkaModel.SccLoop
