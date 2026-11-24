import lemmas.Ska.OptAlias

/-!
# The facts of `InfoReg` and the pure steps of `+alias` that keep them

`InfoHolds R i v`: the facts of `i` hold of the value `v`, with `R x` the
value register `x` holds (clause 2 of `InfoOK`, header of `OptAliasField.lean`):
`isCell` a cell, `isLoob` `0` or `1`, `hasImm = some n` the value `n`,
`hasHed = some d` (`hasTel`) a cell whose head (tail) `R d` holds, `hedOf ∋ x`
(`telOf`) that `R x` holds a cell with head (tail) `v`, `decOf = some d` an
atom `n` with `R d` holding `n + 1`.

**`info_joinL`**, **`info_joinR`**: `joinReg a b` is weaker than each side, so
the join over the predecessors holds on whichever edge was taken.
**`info_param`**: `paramInfo ins` holds of the value an edge passed whenever
the facts of that edge's argument held of it (the fold of `joinReg`,
`info_fold`; dropping the facts that name registers when some edge passes `~`
only weakens, `info_clear`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

/-- **The facts of `i` hold of the value `v`** in the register file read
through `R`. -/
abbrev InfoHolds (R : Nat → Option Noun) (i : InfoReg) (v : Noun) : Prop :=
  (i.isCell = true → ∃ h t, v = Noun.cell h t) ∧
  (i.isLoob = true → v = Noun.atom 0 ∨ v = Noun.atom 1) ∧
  (∀ n, i.hasImm = some n → v = n) ∧
  (∀ d, i.hasHed = some d → ∃ h t, v = Noun.cell h t ∧ R d = some h) ∧
  (∀ d, i.hasTel = some d → ∃ h t, v = Noun.cell h t ∧ R d = some t) ∧
  (∀ x ∈ i.hedOf, ∃ t, R x = some (Noun.cell v t)) ∧
  (∀ x ∈ i.telOf, ∃ h, R x = some (Noun.cell h v)) ∧
  (∀ d, i.decOf = some d → ∃ n, v = Noun.atom n ∧ R d = some (Noun.atom (n + 1)))

variable {R : Nat → Option Noun} {v : Noun}

/-- No fact holds of every value. -/
theorem info_empty : InfoHolds R {} v := by
  refine ⟨fun e => ?_, fun e => ?_, fun _ e => ?_, fun _ e => ?_, fun _ e => ?_, fun _ e => ?_,
    fun _ e => ?_, fun _ e => ?_⟩ <;> simp at e

/-- A loobean fact, or a loobean immediate, makes the value `0` or `1`. -/
theorem info_loob {a : InfoReg} (h : InfoHolds R a v) (hl : (a.isLoob || a.loobImm) = true) :
    v = Noun.atom 0 ∨ v = Noun.atom 1 := by
  rcases Bool.or_eq_true_iff.mp hl with hl | hl
  · exact h.2.1 hl
  · cases e : a.hasImm with
    | none => simp [InfoReg.loobImm, e] at hl
    | some n =>
      rw [h.2.2.1 n e]
      rcases n with k | ⟨x, y⟩
      · rcases k with _ | _ | k
        · exact Or.inl rfl
        · exact Or.inr rfl
        · simp [InfoReg.loobImm, e] at hl
      · simp [InfoReg.loobImm, e] at hl

/-- **The join is weaker than its left side.** -/
theorem info_joinL {a b : InfoReg} (h : InfoHolds R a v) : InfoHolds R (joinReg a b) v := by
  obtain ⟨c, l, im, hh, ht, ho, to, dc⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, fun n e => ?_, fun d e => ?_, fun d e => ?_, fun x hx => ?_,
    fun x hx => ?_, fun d e => ?_⟩
  · simp only [joinReg, Bool.and_eq_true] at e; exact c e.1
  · simp only [joinReg, Bool.and_eq_true] at e; exact info_loob ⟨c, l, im, hh, ht, ho, to, dc⟩ e.1
  · simp only [joinReg] at e; split at e
    · exact im n e
    · cases e
  · simp only [joinReg] at e; split at e
    · exact hh d e
    · cases e
  · simp only [joinReg] at e; split at e
    · exact ht d e
    · cases e
  · simp only [joinReg, List.mem_filter] at hx; exact ho x hx.1
  · simp only [joinReg, List.mem_filter] at hx; exact to x hx.1
  · simp only [joinReg] at e; split at e
    · exact dc d e
    · cases e

/-- **The join is weaker than its right side.** -/
theorem info_joinR {a b : InfoReg} (h : InfoHolds R b v) : InfoHolds R (joinReg a b) v := by
  obtain ⟨c, l, im, hh, ht, ho, to, dc⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, fun n e => ?_, fun d e => ?_, fun d e => ?_, fun x hx => ?_,
    fun x hx => ?_, fun d e => ?_⟩
  · simp only [joinReg, Bool.and_eq_true] at e; exact c e.2
  · simp only [joinReg, Bool.and_eq_true] at e; exact info_loob ⟨c, l, im, hh, ht, ho, to, dc⟩ e.2
  · simp only [joinReg] at e; split at e
    · rename_i heq; rw [heq] at e; exact im n e
    · cases e
  · simp only [joinReg] at e; split at e
    · rename_i heq; rw [heq] at e; exact hh d e
    · cases e
  · simp only [joinReg] at e; split at e
    · rename_i heq; rw [heq] at e; exact ht d e
    · cases e
  · simp only [joinReg, List.mem_filter, decide_eq_true_eq] at hx; exact ho x hx.2
  · simp only [joinReg, List.mem_filter, decide_eq_true_eq] at hx; exact to x hx.2
  · simp only [joinReg] at e; split at e
    · rename_i heq; rw [heq] at e; exact dc d e
    · cases e

theorem info_fold (R : Nat → Option Noun) (v : Noun) : ∀ (t : List InfoReg) (acc : InfoReg),
    (InfoHolds R acc v ∨ ∃ c ∈ t, InfoHolds R c v) → InfoHolds R (t.foldl (fun b a => joinReg a b) acc) v
  | [], acc, h => by
    rcases h with h | ⟨c, hc, -⟩
    · exact h
    · cases hc
  | c :: t, acc, h => by
    simp only [List.foldl_cons]
    apply info_fold R v t
    rcases h with h | ⟨c', hc', h'⟩
    · exact Or.inl (info_joinR h)
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · exact Or.inl (info_joinL h')
      · exact Or.inr ⟨c', hc', h'⟩

/-- Dropping the facts that name registers only weakens. -/
theorem info_clear {j : InfoReg} (h : InfoHolds R j v) :
    InfoHolds R { j with hedOf := [], telOf := [], hasHed := none, hasTel := none, decOf := none } v := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun _ e => ?_, fun _ e => ?_, fun _ e => ?_, fun _ e => ?_, fun _ e => ?_⟩ <;>
    simp at e

/-- **`param-info` keeps the facts of the argument of the edge taken**: if
the facts of some edge's argument hold of the value that edge passed, the facts
of the parameter hold of it. -/
theorem info_param {ins : List (Option InfoReg)} {a : InfoReg} (ha : some a ∈ ins) (h : InfoHolds R a v) :
    InfoHolds R (paramInfo ins) v := by
  have hm : a ∈ ins.filterMap id := List.mem_filterMap.mpr ⟨some a, ha, rfl⟩
  unfold paramInfo
  split
  · exact info_empty
  · rename_i hd tl heq
    rw [heq] at hm
    have hj : InfoHolds R (tl.foldl (fun b a => joinReg a b) hd) v := info_fold R v tl hd (by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl h
      · exact Or.inr ⟨a, hm, h⟩)
    dsimp only
    split
    · exact hj
    · exact info_clear hj

end Opt
end SkaModel
end Formalization
