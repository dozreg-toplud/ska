import lemmas.Compiler.CompSccLoopSoftEmit
import lemmas.Ska.SccLoopSoftFin

/-! # `+soft-emit` without tries: the shared nouns (README Gaps 21.17)

The nouns and the relation the pushes of `seBat` (`CompSccLoopSoftEmitCut.lean`) are linked
with:

* `seTopN`, `seCutN`: the nouns of an entry `[q r ned]` of `tops` and of `[ops tops]`;
* **`AxsRel M l`**: the map noun `M` (`(map @uvre @)`, the product of `+soft-axes`) holds the
  pairs `[r q]` of the association list `l` (its first match), `axsRel_nil`, `axsRel_put`,
  `axsRel_get_some`, `axsRel_get_none`;
* the subjects: `seS0` the gate's (`[seBat [[o s] core]]`), `seS1` after `seAxs`, `seS4` after
  the `=^` of `seCut` (`[cut [axs [seBat [[o s] [door [gen' ctx]]]]]]`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The noun of an entry `[q r ned]` of `tops`. -/
def seTopN (t : Nat × Nat × Need) : Noun := C (A t.1) (C (A t.2.1) t.2.2.toNoun)

/-- The noun of `[ops tops]`. -/
def seCutN (c : List Pole × List (Nat × Nat × Need)) : Noun :=
  C (listNoun Pole.toNoun c.1) (listNoun seTopN c.2)

/-- **The map of `+soft-axes`**: a map noun whose pairs are the `[r q]` of `l`, first match. -/
def AxsRel (M : Noun) (l : List (Nat × Nat)) : Prop :=
  IsMap mugF M ∧ ∀ k v, Get M k v ↔ ∃ r q, k = A r ∧ v = A q ∧ l.lookup r = some q

theorem axsRel_nil : AxsRel (A 0) [] :=
  ⟨IsMap.nil, fun k v => by
    constructor
    · intro h; cases h
    · rintro ⟨r, q, -, -, h⟩; simp at h⟩

/-- `+put:by` of `[r q]`: the list with `(r, q)` in front. -/
theorem axsRel_put {M : Noun} {l : List (Nat × Nat)} (h : AxsRel M l) (r q : Nat) :
    ∃ M', putF mugF (A r) (A q) M = some M' ∧ AxsRel M' ((r, q) :: l) := by
  obtain ⟨hm, hg⟩ := h
  obtain ⟨out, hput, hmap, hget⟩ := putF_spec mugF M (A r) (A q) hm
  refine ⟨out, hput, hmap, fun k v => ?_⟩
  rw [hget k v, hg k v]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hne, r', q', rfl, rfl, hl⟩)
    · exact ⟨r, q, rfl, rfl, by simp [List.lookup]⟩
    · refine ⟨r', q', rfl, rfl, ?_⟩
      have : r' ≠ r := fun e => hne (by rw [e])
      have hb : (r' == r) = false := by simp [this]
      simp [List.lookup, hb, hl]
  · rintro ⟨r', q', rfl, rfl, hl⟩
    by_cases e : r' = r
    · subst e
      simp [List.lookup] at hl
      exact Or.inl ⟨rfl, by rw [hl]⟩
    · refine Or.inr ⟨fun h => e (by injection h), r', q', rfl, rfl, ?_⟩
      have : (r' == r) = false := by simp [e]
      simpa [List.lookup, this] using hl

theorem axsRel_get_some {M : Noun} {l : List (Nat × Nat)} (h : AxsRel M l) {r q : Nat}
    (hl : l.lookup r = some q) : getF mugF (A r) M = some (C (A 0) (A q)) :=
  getF_some h.1 ((h.2 _ _).2 ⟨r, q, rfl, rfl, hl⟩)

theorem axsRel_get_none {M : Noun} {l : List (Nat × Nat)} (h : AxsRel M l) {r : Nat}
    (hl : l.lookup r = none) : getF mugF (A r) M = some (A 0) := by
  refine getF_none h.1 fun v hv => ?_
  obtain ⟨r', q', e, -, hl'⟩ := (h.2 _ _).1 hv
  injection e with e
  subst e
  rw [hl] at hl'
  cases hl'

/-- The subject of `seBat`: `[seBat [[o s] core]]`. -/
abbrev seS0 (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) (o : Nat) (s : SoftCall) : Noun :=
  C seBat (C (C (A o) (Compiler.SoftCall.toNoun s)) (compCore g x ctx))

/-- The subject after `seAxs`: `[axs [seBat [[o s] core]]]`. -/
abbrev seS1 (M : Noun) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) (o : Nat) (s : SoftCall) :
    Noun :=
  C M (seS0 g x ctx o s)

/-- The subject after the `=^` of `seCut`: `[cut [axs [seBat [[o s] [door [gen' ctx]]]]]]`. -/
abbrev seS4 (CUT M : Noun) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) (o : Nat)
    (s : SoftCall) : Noun :=
  C CUT (seS1 M g x ctx o s)

end Compiler
end Formalization
