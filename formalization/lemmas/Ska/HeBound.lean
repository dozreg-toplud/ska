import lemmas.Ska.HeTurn
import lemmas.Ska.AnaInv

/-!
# The `resolve` loop makes boundedly many `%he` turns

A `%he` turn of `resolve` (`Ana.resolveStep`) happens at an identity `i` that
is not in the graph, after a miss of `+git:mi` at the loop's `orig`, when
`+recursive-call` answers `%he` with `[(msg-sock i.1 b) i.2]` for the subject
sock `b` of a frame of `i.2` on the stack with `(he-sock i.1 b)`.  The state
does not change across the turn.  The frames are in the graph (`SInv`), so
`b ≠ i.1`, and `msgSock_he_lt` of `HeTurn.lean` gives a new subject sock of
smaller `heMeasure` (cape size plus leaves `&`).

`resolve_he_bound`: from any identity `i`, the loop reaches, after `k` turns
`%he` with `k ≤ heMeasure i.1 ≤ 2 * sockSize i.1`, an identity whose turn is
not `%he`, and at every fuel `n + k` the loop at `i` is the loop at that
identity at fuel `n`.  For example a call whose subject sock is `&+[5 6]`
(measure `2`) makes at most two turns `%he`.
-/

namespace Formalization
namespace SkaModel

open Nock Compiler

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- `+recursive-call` answers `%he` only for a frame of the same formula on the
stack whose subject sock `+he-sock` embeds, with `+msg-sock` of the two. -/
theorem recLoop_he {he : Sock → Sock → Bool} {heOn : Bool} {g : Sock × Noun → Option Datum}
    {kid : Sock × Noun} : ∀ {stk : List (Sock × Noun)} {i : Sock × Noun},
    recLoop he heOn g kid stk = some (some (false, i)) →
    ∃ j ∈ stk, he kid.1 j.1 = true ∧ j.2 = kid.2 ∧ msgSock kid.1 j.1 = some i.1 ∧ i.2 = kid.2
  | [], _, h => by simp [recLoop] at h
  | j :: stk, i, h => by
    unfold recLoop at h
    split at h
    · obtain ⟨j', hj', a, b, c, d⟩ := recLoop_he h
      exact ⟨j', List.mem_cons_of_mem _ hj', a, b, c, d⟩
    · rename_i hf
      split at h
      · cases h
      · simp at h
      · split at h
        · rename_i hc
          simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨m, hm, -, rfl⟩ := h
          exact ⟨j, List.mem_cons_self, hc.2, (by simpa using hf : kid.2 = j.2).symm, hm, rfl⟩
        · obtain ⟨j', hj', a, b, c, d⟩ := recLoop_he h
          exact ⟨j', List.mem_cons_of_mem _ hj', a, b, c, d⟩

/-- **A `%he` answer of `+recursive-call` for an identity off the stack has a
smaller subject sock**, by `heMeasure`, and the same formula. -/
theorem recursiveCall_he_lt {th : Nat} {kid : Ident} {stk : List Ident} {g : Ident → Option Datum} {i : Ident}
    (h : recursiveCall heSock th kid stk g = some (some (false, i))) (hk : kid ∉ stk) :
    heMeasure i.1 < heMeasure kid.1 ∧ i.2 = kid.2 := by
  obtain ⟨j, hj, hhe, hf, hm, hi⟩ := recLoop_he h
  have hne : kid.1 ≠ j.1 := fun e => hk (by rw [show kid = j from Prod.ext e hf.symm]; exact hj)
  exact ⟨msgSock_he_lt hhe hne hm, hi⟩

/-- A `%he` turn of the `resolve` loop begun with `orig`, in the run state
`gen`, from `i` to `j`: `i` is not in the graph, the memo lookup at the
formula `orig.2` and the current sock `i.1` misses, and `+recursive-call`
generalizes `i` to `j`. -/
def HeTurn (env : Env R) (orig : Ident) (gen : GenS M R) (i j : Ident) : Prop :=
  Treap.get gen.st.g i = none ∧ gitMi gen.st.done orig.2 i.1 = some none ∧
    recursiveCall env.he env.threshold i gen.st.stk (gCore gen.st.g) = some (some (false, j))

/-- A `%he` turn is one unit of the loop's fuel, in the same state. -/
theorem resolve_heTurn {env : Env R} {memoF : Memo M} {orig i j : Ident} {gen : GenS M R}
    (h : HeTurn env orig gen i j) (n : Nat) :
    resolve env memoF (n + 1) orig i gen = resolve env memoF n orig j gen := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [resolve, resolveStep, h1, h2, h3]

/-- **A `%he` turn cuts `heMeasure`** when the frames are in the graph. -/
theorem heTurn_lt {env : Env R} (hhe : env.he = heSock) {orig i j : Ident} {gen : GenS M R}
    (hs : SInv gen.st) (h : HeTurn env orig gen i j) : heMeasure j.1 < heMeasure i.1 ∧ j.2 = i.2 := by
  obtain ⟨h1, -, h3⟩ := h
  rw [hhe] at h3
  exact recursiveCall_he_lt h3 (hs.not_mem h1)

/-- **The `resolve` loop makes at most `heMeasure i.1` turns `%he` in a row**:
from `i` it reaches, after `k` such turns, an identity `j` whose turn is not
`%he`, with `k + heMeasure j.1 ≤ heMeasure i.1`, and at every fuel `n + k`
the loop at `i` is the loop at `j` at fuel `n`. -/
theorem resolve_he_bound {env : Env R} (memoF : Memo M) (hhe : env.he = heSock) {orig : Ident}
    {gen : GenS M R} (hs : SInv gen.st) :
    ∀ (m : Nat) (i : Ident), heMeasure i.1 ≤ m → ∃ k j, k + heMeasure j.1 ≤ heMeasure i.1 ∧
      (∀ j', ¬ HeTurn env orig gen j j') ∧
      ∀ n, resolve env memoF (n + k) orig i gen = resolve env memoF n orig j gen := by
  intro m
  induction m with
  | zero =>
    intro i hi
    refine ⟨0, i, by omega, fun j' hj => ?_, fun n => rfl⟩
    have := (heTurn_lt hhe hs hj).1; omega
  | succ m ih =>
    intro i hi
    by_cases hx : ∃ j', HeTurn env orig gen i j'
    · obtain ⟨j', hj'⟩ := hx
      have hlt := (heTurn_lt hhe hs hj').1
      obtain ⟨k, j, hk, hj, hr⟩ := ih j' (by omega)
      refine ⟨k + 1, j, by omega, hj, fun n => ?_⟩
      rw [← Nat.add_assoc, resolve_heTurn hj', hr]
    · exact ⟨0, i, by omega, fun j' hj => hx ⟨j', hj⟩, fun n => rfl⟩

/-- **The bound**: at most `2 * sockSize i.1` turns `%he` in a row, the size
of the cape of the subject sock twice. -/
theorem resolve_he_bound' {env : Env R} (memoF : Memo M) (hhe : env.he = heSock) {orig : Ident}
    {gen : GenS M R} (hs : SInv gen.st) (i : Ident) :
    ∃ k j, k ≤ 2 * sockSize i.1 ∧ (∀ j', ¬ HeTurn env orig gen j j') ∧
      ∀ n, resolve env memoF (n + k) orig i gen = resolve env memoF n orig j gen := by
  obtain ⟨k, j, hk, hj, hr⟩ := resolve_he_bound memoF hhe hs _ i (Nat.le_refl _)
  exact ⟨k, j, by have := heMeasure_le i.1; omega, hj, hr⟩

end Ana

end SkaModel
end Formalization
