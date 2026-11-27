import lemmas.Ska.PassFreeze

/-!
# (i) `FinIdents` from finite branching, Kruskal and König (track F, Gaps 16)

`FinIdents` (the members of all passes of one chain lie in one finite list) is
what the freezing argument assumes as (i).  Here it is reduced to three
claims about a push relation `P` (`P x y`: `y` was pushed, numbered by
`+analyze`, during a run of `x`), all over abstract identities:

* `FinBranch P`: each identity pushes finitely many identities, over the
  whole chain;
* every member of every pass is reached from the root by pushes;
* no infinite path of pushes from the root.

König's lemma for finitely branching relations (`konig`, proved here in Lean
core with `Classical.choice`) turns the last two into a finite list
(`finIdents_of_tree`).  The third comes from Kruskal's theorem (`KruskalBT` of
`PassFreeze.lean`, stated, not proved: Kruskal 1960, "Well-quasi-ordering,
the tree theorem, and Vazsonyi's conjecture", Trans. AMS 95, in the form for
binary trees over a finite set of leaves with the homeomorphic embedding,
which is Higman's lemma for trees, Nash-Williams 1963 gives a short proof) and
two facts of `+recursive-call` stated as hypotheses (`noPath_of_kruskal`):
the formulas along a path are among finitely many, and past some point of a
path no earlier subject of a formula embeds in a later subject of the same
formula (else the analysis generalizes with `%he` instead of pushing).

`FinBranch` is not a fact of the model alone: a run pushes at most one
identity per call site it reaches, but the subject of a site is computed from
the subject of the run and from the products of the callees before it, and
across infinitely many passes those products can take infinitely many values
unless the callees that come and go (culled and pushed again) settle.  So it
is entangled with R (`EvFrozen`) through the same transient callees.
-/

namespace Formalization
namespace SkaModel
namespace Ana

/-- `z` is reached from `x` by `P`-steps. -/
inductive PReach {α : Type} (P : α → α → Prop) (x : α) : α → Prop where
  | refl : PReach P x x
  | step {y z : α} : PReach P x y → P y z → PReach P x z

/-- Each element has finitely many `P`-successors. -/
def FinBranch {α : Type} (P : α → α → Prop) : Prop := ∀ x, ∃ L : List α, ∀ y, P x y → y ∈ L

/-- Some list holds every element reached from `x`. -/
def Covered {α : Type} (P : α → α → Prop) (x : α) : Prop := ∃ I : List α, ∀ y, PReach P x y → y ∈ I

theorem preach_head {α : Type} {P : α → α → Prop} {x z : α} (h : PReach P x z) :
    z = x ∨ ∃ y, P x y ∧ PReach P y z := by
  induction h with
  | refl => exact Or.inl rfl
  | @step z' z _ hp ih =>
    rcases ih with rfl | ⟨y, hy, hr⟩
    · exact Or.inr ⟨z, hp, PReach.refl⟩
    · exact Or.inr ⟨y, hy, PReach.step hr hp⟩

theorem covered_list {α : Type} {P : α → α → Prop} (Q : α → Prop) :
    ∀ L : List α, (∀ y ∈ L, Q y → Covered P y) → ∃ I : List α, ∀ y ∈ L, Q y → ∀ z, PReach P y z → z ∈ I
  | [], _ => ⟨[], fun _ h => by cases h⟩
  | a :: L, h => by
    obtain ⟨I, hI⟩ := covered_list Q L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hq : Q a
    · obtain ⟨J, hJ⟩ := h a List.mem_cons_self hq
      refine ⟨J ++ I, fun y hy hqy z hz => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_append_left _ (hJ z hz)
      · exact List.mem_append_right _ (hI y hy hqy z hz)
    · refine ⟨I, fun y hy hqy z hz => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd hqy hq
      · exact hI y hy hqy z hz

/-- If every successor is covered, so is `x`. -/
theorem covered_of_succ {α : Type} {P : α → α → Prop} {x : α} (L : List α) (hL : ∀ y, P x y → y ∈ L)
    (h : ∀ y, P x y → Covered P y) : Covered P x := by
  obtain ⟨I, hI⟩ := covered_list (P x) L (fun y _ hy => h y hy)
  refine ⟨x :: I, fun z hz => ?_⟩
  rcases preach_head hz with rfl | ⟨y, hy, hr⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hI y (hL y hy) hy z hr)

/-- **König's lemma** for a finitely branching relation: if what `x` reaches
is in no finite list, there is an infinite path from `x`. -/
theorem konig {α : Type} (P : α → α → Prop) (hfb : FinBranch P) (x : α) (hnot : ¬ Covered P x) :
    ∃ p : Nat → α, p 0 = x ∧ ∀ n, P (p n) (p (n + 1)) := by
  have step : ∀ y, ¬ Covered P y → ∃ z, P y z ∧ ¬ Covered P z := by
    intro y hy
    obtain ⟨L, hL⟩ := hfb y
    exact Classical.byContradiction fun hn => hy (covered_of_succ L hL fun z hz =>
      Classical.byContradiction fun hc => hn ⟨z, hz, hc⟩)
  let S := { y : α // ¬ Covered P y }
  let nx : S → S := fun a => ⟨Classical.choose (step a.1 a.2), (Classical.choose_spec (step a.1 a.2)).2⟩
  let q : Nat → S := fun n => Nat.rec ⟨x, hnot⟩ (fun _ a => nx a) n
  refine ⟨fun n => (q n).1, rfl, fun n => ?_⟩
  show P (q n).1 (nx (q n)).1
  exact (Classical.choose_spec (step (q n).1 (q n).2)).1

/-- **`FinIdents` from a push tree**: if every member of every pass is reached
from the root by pushes, the pushes branch finitely, and there is no infinite
path of pushes from the root, the members lie in one finite list. -/
theorem finIdents_of_tree {M : Type → Type → Type} [Treap M] {R : Type} (rest : List Ident)
    (f : Nat → SkaState M R) (P : Ident → Ident → Prop) (root : Ident) (hfb : FinBranch P)
    (hreach : ∀ k x, MembR rest (f k) x → PReach P root x)
    (hpath : ¬ ∃ p : Nat → Ident, p 0 = root ∧ ∀ n, P (p n) (p (n + 1))) : FinIdents rest f := by
  by_cases hc : Covered P root
  · obtain ⟨I, hI⟩ := hc
    exact ⟨I, fun k x hx => hI x (hreach k x hx)⟩
  · exact absurd (konig P hfb root hc) hpath

/-! ## No infinite path, from Kruskal -/

/-- **Pigeonhole for an infinite sequence in a finite list**: some value is
taken infinitely often. -/
theorem pigeon_inf {β : Type _} : ∀ (Fs : List β) (g : Nat → β), (∀ n, g n ∈ Fs) →
    ∃ a, ∀ N, ∃ n, N ≤ n ∧ g n = a
  | [], g, h => absurd (h 0) (by simp)
  | a :: Fs, g, h => by
    by_cases ha : ∀ N, ∃ n, N ≤ n ∧ g n = a
    · exact ⟨a, ha⟩
    · have : ∃ N0, ∀ n, N0 ≤ n → g n ≠ a := by
        refine Classical.byContradiction fun hn => ha fun N => ?_
        exact Classical.byContradiction fun hm => hn ⟨N, fun n hn' e => hm ⟨n, hn', e⟩⟩
      obtain ⟨N0, hN0⟩ := this
      obtain ⟨b, hb⟩ := pigeon_inf Fs (fun n => g (N0 + n)) (fun n => by
        rcases List.mem_cons.mp (h (N0 + n)) with e | e
        · exact absurd e (hN0 _ (Nat.le_add_right _ _))
        · exact e)
      refine ⟨b, fun N => ?_⟩
      obtain ⟨n, hn, e⟩ := hb N
      exact ⟨N0 + n, by omega, e⟩

/-- An increasing sequence of indices at which `g` takes the value `a`. -/
theorem subseq_of_inf {β : Type _} {g : Nat → β} {a : β} (h : ∀ N, ∃ n, N ≤ n ∧ g n = a) :
    ∃ s : Nat → Nat, (∀ n, s n < s (n + 1)) ∧ ∀ n, g (s n) = a := by
  let nx : Nat → Nat := fun m => Classical.choose (h (m + 1))
  have hnx : ∀ m, m + 1 ≤ nx m ∧ g (nx m) = a := fun m => Classical.choose_spec (h (m + 1))
  let s : Nat → Nat := fun n => Nat.rec (Classical.choose (h 0)) (fun _ m => nx m) n
  refine ⟨s, fun n => ?_, fun n => ?_⟩
  · show s n < nx (s n); have := (hnx (s n)).1; omega
  · cases n with
    | zero => exact (Classical.choose_spec (h 0)).2
    | succ n => exact (hnx (s n)).2

theorem strictMono_le {s : Nat → Nat} (hs : ∀ n, s n < s (n + 1)) : ∀ {i j : Nat}, i < j → s i < s j := by
  intro i j hij
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl
    · exact Nat.lt_trans (ih h) (hs j)
    · exact hs i

/-- **No infinite path of pushes, from Kruskal**: if the formulas along any
path are among a finite list, and past some point of any path no earlier
subject embeds in a later subject of the same formula (what `+recursive-call`
does: it generalizes with `%he` instead of pushing), then by `KruskalBT` no
path is infinite. -/
theorem noPath_of_kruskal {α : Type _} {L : Type} (hK : KruskalBT) (ls : List L) (hls : ∀ a : L, a ∈ ls)
    (P : α → α → Prop) (form : α → Nock.Noun) (sub : α → BT L) (root : α)
    (hforms : ∃ Fs : List Nock.Noun, ∀ x, PReach P root x → form x ∈ Fs)
    (hguard : ∀ p : Nat → α, p 0 = root → (∀ n, P (p n) (p (n + 1))) →
      ∃ N, ∀ i j, N ≤ i → i < j → form (p i) = form (p j) → ¬ BTEmb (sub (p i)) (sub (p j))) :
    ¬ ∃ p : Nat → α, p 0 = root ∧ ∀ n, P (p n) (p (n + 1)) := by
  rintro ⟨p, h0, hp⟩
  have hr : ∀ n, PReach P root (p n) := by
    intro n
    induction n with
    | zero => rw [h0]; exact PReach.refl
    | succ n ih => exact PReach.step ih (hp n)
  obtain ⟨Fs, hFs⟩ := hforms
  obtain ⟨N, hN⟩ := hguard p h0 hp
  obtain ⟨a, ha⟩ := pigeon_inf Fs (fun n => form (p (N + n))) (fun n => hFs _ (hr _))
  obtain ⟨s, hs, hsa⟩ := subseq_of_inf ha
  obtain ⟨i, j, hij, he⟩ := hK L ls hls (fun n => sub (p (N + s n)))
  have hlt := strictMono_le hs hij
  exact hN (N + s i) (N + s j) (Nat.le_add_right _ _) (by omega) (by rw [hsa i, hsa j]) he

/-- **(i) from finite branching, Kruskal and König**: `FinIdents` along a
chain, given a push relation that branches finitely, reaches every member of
every pass from the root, keeps its formulas among finitely many, and obeys
the `%he` guard of `+recursive-call` past some point of each path; Kruskal's
theorem (`KruskalBT`) is the one named hypothesis that is a known theorem. -/
theorem finIdents_of_kruskal {M : Type → Type → Type} [Treap M] {R : Type} {L : Type} (hK : KruskalBT)
    (ls : List L) (hls : ∀ a : L, a ∈ ls) (rest : List Ident) (f : Nat → SkaState M R)
    (P : Ident → Ident → Prop) (root : Ident) (sub : Ident → BT L) (hfb : FinBranch P)
    (hreach : ∀ k x, MembR rest (f k) x → PReach P root x)
    (hforms : ∃ Fs : List Nock.Noun, ∀ x, PReach P root x → x.2 ∈ Fs)
    (hguard : ∀ p : Nat → Ident, p 0 = root → (∀ n, P (p n) (p (n + 1))) →
      ∃ N, ∀ i j, N ≤ i → i < j → (p i).2 = (p j).2 → ¬ BTEmb (sub (p i)) (sub (p j))) :
    FinIdents rest f :=
  finIdents_of_tree rest f P root hfb hreach
    (noPath_of_kruskal hK ls hls P (fun x => x.2) sub root hforms hguard)

end Ana
end SkaModel
end Formalization
