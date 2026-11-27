import lemmas.Ska.PokeFlagsOf
import lemmas.Compiler.CompTarjanBunt

/-!
# The jug `+ska-poke` hands to `+tarjan` (track Q)

Push 8 of `spRest` (`desk/lib/nock-compilation.hoon`, `=/  sccs`):

    %-  tarjan
    %-  ~(rep by new-code)
    |=  [[b=bell v=[=nomm calls=(set bell) seek=cape]] acc=(jug bell bell)]
    %+  ~(put by acc)  b
    %-  silt
    (skim ~(tap in calls.v) |=(c=bell (~(has by new-code) c)))

* `keysIn nc S`: the members of `S` that are keys of `nc` (the `skim`);
* `jugOf nc`: every key `b` of `nc` with `keysIn nc calls.b` (the `rep`);
* `jugNoun nc`: its noun, the sample of `+tarjan`.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF

open Classical in
/-- The members of `S` that are keys of `nc`. -/
noncomputable def keysIn (nc : FinMap Bell (VarEntry FinMap)) (S : FinMap Bell Unit) : FinMap Bell Unit :=
  ⟨fun c => if (FinMap.get S c).isSome = true ∧ (FinMap.get nc c).isSome = true then some () else none, by
    obtain ⟨l, hl⟩ := S.2
    refine ⟨l, fun k hk => hl k ?_⟩
    by_cases h : (FinMap.get S k).isSome = true ∧ (FinMap.get nc k).isSome = true
    · intro h0
      have : FinMap.get S k = none := h0
      rw [this] at h; simp at h
    · simp [h] at hk⟩

/-- **The jug of push 8**: each key `b` of `nc` with its callees that are keys. -/
noncomputable def jugOf (nc : FinMap Bell (VarEntry FinMap)) : FinMap Bell (FinMap Bell Unit) :=
  ⟨fun b => (FinMap.get nc b).map fun e => keysIn nc e.calls, by
    obtain ⟨l, hl⟩ := nc.2
    refine ⟨l, fun k hk => hl k ?_⟩
    intro h0
    have : FinMap.get nc k = none := h0
    simp [this] at hk⟩

/-- The noun of the jug: the sample of `+tarjan`. -/
noncomputable def jugNoun (nc : FinMap Bell (VarEntry FinMap)) : Noun := (jugOf nc).toNoun FinMap.setNoun

theorem keysIn_get (nc : FinMap Bell (VarEntry FinMap)) (S : FinMap Bell Unit) (c : Bell) :
    FinMap.get (keysIn nc S) c = some () ↔ FinMap.get S c = some () ∧ ∃ e, FinMap.get nc c = some e := by
  unfold keysIn FinMap.get
  simp only
  constructor
  · intro h
    split at h
    · rename_i hc
      obtain ⟨h1, h2⟩ := hc
      refine ⟨?_, ?_⟩
      · cases e : S.1 c with
        | none => simp [FinMap.get, e] at h1
        | some u => rfl
      · cases e : nc.1 c with
        | none => simp [FinMap.get, e] at h2
        | some v => exact ⟨v, rfl⟩
    · cases h
  · rintro ⟨h1, e, h2⟩
    rw [if_pos]
    exact ⟨by simp [FinMap.get, h1], by simp [FinMap.get, h2]⟩

theorem jugOf_get (nc : FinMap Bell (VarEntry FinMap)) (b : Bell) :
    FinMap.get (jugOf nc) b = (FinMap.get nc b).map fun e => keysIn nc e.calls := rfl

/-- The fold of push 8 builds `jugOf`: `+put:by` of each key with its `keysIn`
over `rap nc`, from `~`. -/
theorem jugOf_foldl (nc : FinMap Bell (VarEntry FinMap)) :
    (FinMap.rap nc).foldl (fun acc p => FinMap.put acc p.1 (keysIn nc p.2.calls)) FinMap.empty = jugOf nc := by
  have key : ∀ (L : List (Bell × VarEntry FinMap)) (acc : FinMap Bell (FinMap Bell Unit)),
      (∀ p ∈ L, FinMap.get nc p.1 = some p.2) → ∀ b,
      FinMap.get (L.foldl (fun acc p => FinMap.put acc p.1 (keysIn nc p.2.calls)) acc) b =
        if ∃ p ∈ L, p.1 = b then (FinMap.get nc b).map fun e => keysIn nc e.calls else FinMap.get acc b := by
    intro L
    induction L with
    | nil => intro acc _ b; simp
    | cons p L ih =>
      intro acc hL b
      simp only [List.foldl_cons]
      rw [ih _ (fun q hq => hL q (List.mem_cons_of_mem _ hq)) b]
      by_cases h1 : ∃ q ∈ L, q.1 = b
      · rw [if_pos h1, if_pos (by obtain ⟨q, hq, e⟩ := h1; exact ⟨q, List.mem_cons_of_mem _ hq, e⟩)]
      · rw [if_neg h1]
        by_cases h2 : p.1 = b
        · rw [if_pos ⟨p, List.mem_cons_self, h2⟩]
          subst h2
          have hp : nc.1 p.1 = some p.2 := hL p List.mem_cons_self
          simp [FinMap.get, FinMap.put, hp]
        · rw [if_neg (by rintro ⟨q, hq, e⟩; rcases List.mem_cons.1 hq with rfl | hq; exact h2 e; exact h1 ⟨q, hq, e⟩)]
          simp [FinMap.get, FinMap.put, Ne.symm h2]
  apply Subtype.ext
  funext b
  have := key (FinMap.rap nc) FinMap.empty (fun p hp => (FinMap.mem_rap nc p.1 p.2).1 hp) b
  show FinMap.get _ b = FinMap.get (jugOf nc) b
  rw [this, jugOf_get]
  split
  · rfl
  · rename_i h
    cases e : FinMap.get nc b with
    | none => rfl
    | some v => exact absurd ⟨(b, v), (FinMap.mem_rap nc b v).2 e, rfl⟩ h

end Compiler
end Formalization
