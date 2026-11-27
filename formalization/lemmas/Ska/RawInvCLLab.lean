import lemmas.Ska.RawInvCLCopy

/-!
# `LabUniq` at run level: the statement and the tree lemma

README Gaps 14 (b), track D.  `CopySpecL` takes `LabUniq` of both trees
(at every node, bonds at distinct labels and forks at distinct `yes`
labels).  It is a property of every run of `PlainN` from a goal whose tree
has it, carried through the triple `HT` of `RawInvCAT.lean`:

* `labUniq_mk`: `LabUniq` of a node is distinct labels there and `LabUniq`
  of every child (by `mem_bondEntries`, `mem_forkEntries`).
* `labUniq_ofSure`, `labUniq_prune`.
* `LG goal g`: the goal's tree is `LabUniq` and its entries lie below
  `g.bo` (so the label of a block emitted later is not one of them);
  `stab_lg` (`KP` keeps it).
* `HRL rp`: every run of `rp` from a `Fresh`, `LG` goal ends `Fresh` with an
  `LG` result (`HR` of `ht_runLC` with the label clause).
* `HT.pureR`: an `HT` with a fact about the product read off the run.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Membership in the entries -/

theorem mem_bondEntries {e : Nat × Lazy S} : ∀ {b : List (Nat × Lazy S)},
    e ∈ bondEntries b → ∃ x ∈ b, e = x ∨ e ∈ entries x.2
  | [], h => by simp [bondEntries] at h
  | (o, l) :: rest, h => by
    simp only [bondEntries, List.mem_append, List.mem_cons] at h
    rcases h with (h | h) | h
    · exact ⟨(o, l), List.mem_cons_self, Or.inl h⟩
    · exact ⟨(o, l), List.mem_cons_self, Or.inr h⟩
    · obtain ⟨x, hx, h⟩ := mem_bondEntries h
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem bondEntries_of_mem {e : Nat × Lazy S} : ∀ {b : List (Nat × Lazy S)}, e ∈ b →
    e ∈ bondEntries b ∧ ∀ y ∈ entries e.2, y ∈ bondEntries b
  | [], h => absurd h List.not_mem_nil
  | (o, l) :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨by simp [bondEntries], fun y hy => by simp [bondEntries, hy]⟩
    · obtain ⟨h1, h2⟩ := bondEntries_of_mem h
      exact ⟨by simp [bondEntries, h1], fun y hy => by simp [bondEntries, h2 y hy]⟩

theorem mem_forkEntries {e : Nat × Lazy S} : ∀ {f : List (ForkE S)},
    e ∈ forkEntries f → ∃ x ∈ f, e = x.1 ∨ e ∈ entries x.1.2 ∨ e = x.2 ∨ e ∈ entries x.2.2
  | [], h => by simp [forkEntries] at h
  | ((oy, y), (on, n)) :: rest, h => by
    simp only [forkEntries, List.mem_append, List.mem_cons] at h
    rcases h with ((h | h) | (h | h)) | h
    · exact ⟨_, List.mem_cons_self, Or.inl h⟩
    · exact ⟨_, List.mem_cons_self, Or.inr (Or.inl h)⟩
    · exact ⟨_, List.mem_cons_self, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨_, List.mem_cons_self, Or.inr (Or.inr (Or.inr h))⟩
    · obtain ⟨x, hx, h⟩ := mem_forkEntries h
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem forkEntries_of_mem {x : ForkE S} : ∀ {f : List (ForkE S)}, x ∈ f →
    x.1 ∈ forkEntries f ∧ (∀ y ∈ entries x.1.2, y ∈ forkEntries f) ∧
      x.2 ∈ forkEntries f ∧ ∀ y ∈ entries x.2.2, y ∈ forkEntries f
  | [], h => absurd h List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · refine ⟨by simp [forkEntries], fun z hz => by simp [forkEntries, hz], by simp [forkEntries],
        fun z hz => by simp [forkEntries, hz]⟩
    · obtain ⟨h1, h2, h3, h4⟩ := forkEntries_of_mem h
      exact ⟨by simp [forkEntries, h1], fun z hz => by simp [forkEntries, h2 z hz], by simp [forkEntries, h3],
        fun z hz => by simp [forkEntries, h4 z hz]⟩

/-! ## `LabUniq` node by node -/

/-- **`LabUniq` of a node**: distinct labels there, `LabUniq` of every
child. -/
theorem labUniq_mk (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    LabUniq (mk s f b) ↔ (b.map (·.1)).Nodup ∧ (f.map (·.1.1)).Nodup ∧
      (∀ e ∈ b, LabUniq e.2) ∧ ∀ x ∈ f, LabUniq x.1.2 ∧ LabUniq x.2.2 := by
  constructor
  · intro h
    have hr := h _ List.mem_cons_self
    have hE : ∀ e ∈ entries (mk s f b), (e.2.bond.map (·.1)).Nodup ∧ (e.2.fork.map (·.1.1)).Nodup :=
      fun e he => h e (List.mem_cons_of_mem _ he)
    refine ⟨hr.1, hr.2, fun e he => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := bondEntries_of_mem he
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hE e (by simp only [entries, List.mem_append]; exact Or.inl h1)
      · exact hE y (by simp only [entries, List.mem_append]; exact Or.inl (h2 y hy))
    · obtain ⟨h1, h2, _, _⟩ := forkEntries_of_mem hx
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hE x.1 (by simp only [entries, List.mem_append]; exact Or.inr h1)
      · exact hE y (by simp only [entries, List.mem_append]; exact Or.inr (h2 y hy))
    · obtain ⟨_, _, h3, h4⟩ := forkEntries_of_mem hx
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hE x.2 (by simp only [entries, List.mem_append]; exact Or.inr h3)
      · exact hE y (by simp only [entries, List.mem_append]; exact Or.inr (h4 y hy))
  · rintro ⟨hb, hf, hB, hF⟩ e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hb, hf⟩
    simp only [entries, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨x, hx, h⟩ := mem_bondEntries he
      rcases h with rfl | h
      · exact hB e hx (0, e.2) List.mem_cons_self
      · exact hB x hx e (List.mem_cons_of_mem _ h)
    · obtain ⟨x, hx, h⟩ := mem_forkEntries he
      rcases h with rfl | h | rfl | h
      · exact (hF x hx).1 (0, x.1.2) List.mem_cons_self
      · exact (hF x hx).1 e (List.mem_cons_of_mem _ h)
      · exact (hF x hx).2 (0, x.2.2) List.mem_cons_self
      · exact (hF x hx).2 e (List.mem_cons_of_mem _ h)

theorem labUniq_ofSure (s : Sure S) : LabUniq (ofSure s) :=
  (labUniq_mk s [] []).mpr ⟨List.nodup_nil, List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem labUniq_prune {l : Lazy S} (h : LabUniq l) : LabUniq (lazyPrune l) := by
  rcases l with ⟨s, f, b⟩
  obtain ⟨hb, hf, hB, hF⟩ := (labUniq_mk s f b).mp h
  refine (labUniq_mk _ _ _).mpr ⟨?_, ?_, fun e he => hB e (List.mem_filter.mp he).1,
    fun x hx => hF x (List.mem_filter.mp hx).1⟩
  · exact (List.filter_sublist).map _ |>.nodup hb
  · exact (List.filter_sublist).map _ |>.nodup hf

/-! ## The statement at run level -/

/-- **The label clause of a goal**: its tree is `LabUniq` and its entries
lie below `bo`. -/
def LG : CGoalL S → Comp.Gen Map → Prop
  | CGoalL.next laz _, g => LabUniq laz ∧ ∀ e ∈ entries laz, e.1 < g.bo
  | _, _ => True

theorem stab_lg (goal : CGoalL S) : Stab (Map := Map) (LG goal) := by
  intro g g' k h
  cases goal with
  | next laz th => exact ⟨h.1, fun e he => Nat.lt_of_lt_of_le (h.2 e he) k.2.1⟩
  | pick _ _ => trivial
  | done => trivial

theorem lg_ofSure (s : Sure S) (th : Jmp) (g : Comp.Gen Map) : LG (CGoalL.next (ofSure s) th) g :=
  ⟨labUniq_ofSure s, fun e he => by rw [entries_ofSure] at he; exact absurd he List.not_mem_nil⟩

/-- **What a run owes, with labels**: `Fresh` and `LG` goal in, `Fresh` and
`LG` result out. -/
abbrev HRL (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ goal region, HT (fun g => GFL (Map := Map) goal g ∧ LG goal g) (rp goal region)
    (fun nex g => Fresh g nex.th ∧ LG nex.goal g)

/-- An `HT` with a fact about the product and the two states that a run
gives. -/
theorem HT.pureR {α : Type} {P : Comp.Gen Map → Prop} {Q : α → Comp.Gen Map → Prop} {m : CM Map α}
    {R : Comp.Gen Map → α → Comp.Gen Map → Prop} (h : HT P m Q)
    (hr : ∀ g x g', ATS g → P g → m g = some (x, g') → R g x g') :
    HT P m (fun x g' => Q x g' ∧ ∃ g, R g x g' ∧ g.bo ≤ g'.bo ∧ P g) := by
  constructor
  intro g x g' A p e
  obtain ⟨A1, K1, q1⟩ := h.run g x g' A p e
  exact ⟨A1, K1, q1, g, hr g x g' A p e, K1.2.1, p⟩

end Raw
end SkaModel
end Formalization
