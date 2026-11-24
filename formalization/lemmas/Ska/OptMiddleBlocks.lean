import lemmas.Ska.OptMiddle
import lemmas.Ska.OptHops
import lemmas.Ska.OptBranch

/-!
# The blocks after `+remove-empty-middle`, and what two passes keep of them

`mid_blocks`: after `+remove-empty-middle` every block keeps its label, its
parameters and its body, and its end is what `middleFin` gives (`MidBlocks`),
on the pattern of `rub_blocks`.  So the pass keeps distinct parameters
(`mid_parNodup`), with no hypothesis.  It keeps `PassOK` only under its own
hypothesis, which is `PassOK` of the result (`mid_passOK`): a hop `[0v1]` to
an empty block with parameters `[0v2]` that hops `[0v2]` to a block with
parameters `[0v1]` passes the check twice before and fails it after, and the
Hoon does not test for it (on the real compiler no such jump occurs on 135
cases, `tools/hoon/optcheck.hoon`).

`+remove-useless-branching` keeps both with no hypothesis (`rub_parNodup`,
`rub_passOK`): it keeps parameters, and a new end is a hop that passes nothing.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

section
variable [MapKeys Map]

/-- The step of the `+rep:by` of `+remove-empty-middle`. -/
def midStep (fuel : Nat) (bl : Map Blob) (acc : Option (Bool × Map Blob)) (o : Nat) : Option (Bool × Map Blob) :=
  acc.bind fun (ch, nw) => (HoonMap.get bl o).bind fun b =>
    (middleFin bl (readersOf bl) fuel b.fin).map fun f' =>
      (ch || decide (f' ≠ b.fin), HoonMap.put nw o { b with fin := f' })

theorem removeEmptyMiddle_eq (fuel : Nat) (bl : Map Blob) :
    removeEmptyMiddle fuel bl = (MapKeys.keys bl).foldl (midStep fuel bl) (some (false, HoonMap.empty)) := rfl

theorem midFold_none (fuel : Nat) (bl : Map Blob) : ∀ ks : List Nat, ks.foldl (midStep fuel bl) none = none
  | [] => rfl
  | _ :: ks => by simp only [List.foldl_cons, midStep, Option.bind_none]; exact midFold_none fuel bl ks

theorem midFold_get (fuel : Nat) (bl : Map Blob) : ∀ (ks : List Nat) (acc : Option (Bool × Map Blob))
    (r : Bool × Map Blob), ks.foldl (midStep fuel bl) acc = some r → ∃ a, acc = some a ∧
      (∀ k b, k ∈ ks → HoonMap.get bl k = some b → ∃ f', middleFin bl (readersOf bl) fuel b.fin = some f' ∧
        HoonMap.get r.2 k = some { b with fin := f' }) ∧
      (∀ k, (k ∉ ks ∨ HoonMap.get bl k = none) → HoonMap.get r.2 k = HoonMap.get a.2 k)
  | [], acc, r, h => by
    simp only [List.foldl_nil] at h; subst h
    exact ⟨r, rfl, fun _ _ hk => absurd hk List.not_mem_nil, fun _ _ => rfl⟩
  | k0 :: ks, acc, r, h => by
    simp only [List.foldl_cons] at h
    cases hs : midStep fuel bl acc k0 with
    | none => rw [hs, midFold_none] at h; cases h
    | some a' =>
      rw [hs] at h
      obtain ⟨a'', ha'', hin, hout⟩ := midFold_get fuel bl ks _ r h
      cases ha''
      unfold midStep at hs
      obtain ⟨⟨ch, nw⟩, ha, hs1⟩ := Option.bind_eq_some_iff.mp hs
      subst ha
      obtain ⟨b0, hb0, hs2⟩ := Option.bind_eq_some_iff.mp hs1
      obtain ⟨f0, hf0, hs3⟩ := Option.map_eq_some_iff.mp hs2
      subst hs3
      refine ⟨(ch, nw), rfl, ?_, ?_⟩
      · intro k b hk hb
        by_cases hks : k ∈ ks
        · exact hin k b hks hb
        · have hk0 : k = k0 := by
            rcases List.mem_cons.mp hk with h | h
            · exact h
            · exact absurd h hks
          subst hk0
          rw [hb0] at hb; cases hb
          refine ⟨f0, hf0, ?_⟩
          rw [hout k (Or.inl hks)]; simp [HoonMap.get_put]
      · intro k hk
        have hk' : k ∉ ks ∨ HoonMap.get bl k = none := by
          rcases hk with hk | hk
          · exact Or.inl (fun h => hk (List.mem_cons_of_mem _ h))
          · exact Or.inr hk
        rw [hout k hk']
        simp only [HoonMap.get_put]
        by_cases e : k = k0
        · subst e
          rcases hk with hk | hk
          · exact absurd (List.mem_cons_self) hk
          · rw [hk] at hb0; cases hb0
        · simp [e]

end

/-- The blocks after `+remove-empty-middle`, block by block. -/
def MidBlocks [MapKeys Map] (fuel : Nat) (bl bl' : Map Blob) : Prop :=
  ∀ k, (HoonMap.get bl k = none → HoonMap.get bl' k = none) ∧
    ∀ b, HoonMap.get bl k = some b → ∃ f', middleFin bl (readersOf bl) fuel b.fin = some f' ∧
      HoonMap.get bl' k = some { b with fin := f' }

theorem mid_blocks [MapKeys Map] {fuel : Nat} {bl bl' : Map Blob} {ch : Bool}
    (h : removeEmptyMiddle fuel bl = some (ch, bl')) : MidBlocks fuel bl bl' := by
  rw [removeEmptyMiddle_eq] at h
  obtain ⟨a, ha, hin, hout⟩ := midFold_get fuel bl _ _ _ h
  cases ha
  intro k
  refine ⟨fun hk => ?_, fun b hb => hin k b ((MapKeys.mem_keys bl k).mpr (by simp [hb])) hb⟩
  rw [hout k (Or.inr hk)]; exact HoonMap.get_empty k

theorem MidBlocks.back [MapKeys Map] {fuel : Nat} {bl bl' : Map Blob} (h : MidBlocks fuel bl bl') {k : Nat}
    {b' : Blob} (hb : HoonMap.get bl' k = some b') : ∃ b f', HoonMap.get bl k = some b ∧
      middleFin bl (readersOf bl) fuel b.fin = some f' ∧ b' = { b with fin := f' } := by
  cases e : HoonMap.get bl k with
  | none => rw [(h k).1 e] at hb; cases hb
  | some b =>
    obtain ⟨f', hf', hb'⟩ := (h k).2 b e
    rw [hb'] at hb; cases hb
    exact ⟨b, f', rfl, hf', rfl⟩

/-- **`+remove-empty-middle` keeps distinct parameters.** -/
theorem mid_parNodup [MapKeys Map] {fuel : Nat} {bl bl' : Map Blob} {ch : Bool}
    (h : removeEmptyMiddle fuel bl = some (ch, bl')) (hnd : ParNodup bl) : ParNodup bl' := by
  intro o m hm
  obtain ⟨b, f', hb, -, rfl⟩ := (mid_blocks h).back hm
  exact hnd o b hb

/-- **`+remove-empty-middle` keeps the check of `+eval-pass`** exactly when
its hypothesis (the one of `MiddleKeeps`) holds: that hypothesis is `PassOK`
of the result. -/
theorem mid_passOK {bl' : Map Blob}
    (hyp : ∀ o b' j b2, HoonMap.get bl' o = some b' → j ∈ getJmps b'.fin → HoonMap.get bl' j.there = some b2 →
      ∀ r, some r ∈ j.args → r ∉ b2.par) : PassOK bl' := hyp

/-- **`+remove-useless-branching` keeps distinct parameters.** -/
theorem rub_parNodup [MapKeys Map] {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hnd : ParNodup bl) : ParNodup bl' := by
  intro o m hm
  obtain ⟨b, e, hb, -, rfl⟩ := (rub_blocks h).back hm
  exact hnd o b hb

/-- **`+remove-useless-branching` keeps the check of `+eval-pass`**: a new end
is the old one or a hop that passes nothing. -/
theorem rub_passOK [MapKeys Map] {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hpc : PassOK bl) : PassOK bl' := by
  have H := rub_blocks h
  intro o m j m2 hm hj hm2 r hr
  obtain ⟨b, e, hb, he, rfl⟩ := H.back hm
  obtain ⟨b2, e2, hb2, -, rfl⟩ := H.back hm2
  rcases rubFin_cases he with rfl | ⟨z, o', nz, -, -, -, -, h2, -⟩
  · exact hpc o b j b2 hb hj hb2 r hr
  · simp only [rubBlob, h2, getJmps, List.mem_singleton] at hj
    subst hj; simp at hr

end Opt
end SkaModel
end Formalization
