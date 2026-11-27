import lemmas.Glue.GuardCalls
import lemmas.Glue.GuardStep
import lemmas.Ska.CompDirectM

/-!
# `+mono-try-call` keeps the all-blocks form with the annotation

LEDGER 2.c (track G, eighth pass), step 3 started: the arm of the direct
call that makes the path-guarded splits.  `InvA K g`: `BlocksOKA g.blocks K`,
not dropping, every block and every jump below `bo`, every label with `K`
below `bo`.

* `emitA`: `+emit` of a block whose jumps go below `bo`, pass no `~`, whose
  edges into labels with `K` are `ClqYes` or `CellOut`, and whose splits are
  guarded by a `%cel` or by the new annotation `S` at the fresh label; the
  annotation grows by `S` at `bo` only.
* **`mtl_kpa`**: every run of `monoTryLoop fail ned r o` from `InvA K g`,
  with `r` below `re`, `o` and `fail` below `bo` and without `K`, ends in
  `InvA K' g'` for a `K'` that agrees with `K` below the old `bo`, with a
  result below `bo` and without `K'`.  The split block `[hed r rh, tal r rt]`
  gets `K' os r`; the `%clq r (jmp0 os) (jmp0 fail)` block emitted right
  after is its only way in.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-- **The state invariant of a run with path-guarded splits.** -/
structure InvA (K : Nat → Nat → Prop) (g : Comp.Gen Map) : Prop where
  ok : BlocksOKA g.blocks K
  drop : g.drop = false
  below : ∀ o b, HoonMap.get g.blocks o = some b → o < g.bo ∧ ∀ j ∈ getJmps b.fin, j.there < g.bo
  kin : ∀ o s, K o s → o < g.bo

theorem cellOut_mono {K K' : Nat → Nat → Prop} (hK : ∀ l s, K l s → K' l s) {o : Nat} {b : Blob} {s : Nat}
    (h : CellOut K o b s) : CellOut K' o b s := by
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨hK _ _ h1, h2⟩
  · exact Or.inr h

/-- **`+emit` with the annotation.** -/
theorem emitA {K : Nat → Nat → Prop} {g : Comp.Gen Map} (hI : InvA K g) (h0 : 0 < g.bo) {b : Blob}
    (S : Nat → Prop) (hpar : ∀ s, S s → s ∉ b.par)
    (hj : ∀ j ∈ getJmps b.fin, j.there < g.bo ∧ Option.none ∉ j.args)
    (he : ∀ j ∈ getJmps b.fin, ∀ s, K j.there s →
      ClqYes b.fin s j.there ∨ CellOut (fun l s => K l s ∨ (l = g.bo ∧ S s)) g.bo b s)
    (hs : ∀ i p s, b.body[i]? = some p → splitReg p = some s →
      (∃ j : Nat, j < i ∧ b.body[j]? = some (Pole.cel s) ∧
        ∀ l, j < l → l < i → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s) ∨
      (S s ∧ NoWriteBefore b.body i s)) :
    InvA (fun l s => K l s ∨ (l = g.bo ∧ S s)) (g.emitted b) := by
  have hget : ∀ o, HoonMap.get (g.emitted b).blocks o = if o = g.bo then some b else HoonMap.get g.blocks o := by
    intro o; simp only [Gen.emitted, hI.drop, Bool.false_eq_true, if_false]; rw [HoonMap.get_put]
  have hsub : ∀ l s, K l s → K l s ∨ (l = g.bo ∧ S s) := fun l s h => Or.inl h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro o b' hb' j hjm
    rw [hget] at hb'; split at hb'
    · cases hb'; exact (hj j hjm).2
    · exact hI.ok.noNone o b' hb' j hjm
  · intro o b' s hb' hk
    rw [hget] at hb'; split at hb'
    · rename_i e; cases hb'
      rcases hk with hk | ⟨-, hk⟩
      · exact absurd e (Nat.ne_of_lt (hI.kin o s hk))
      · exact hpar s hk
    · rename_i e
      rcases hk with hk | ⟨e', -⟩
      · exact hI.ok.par o b' s hb' hk
      · exact absurd e' e
  · intro s hk
    rcases hk with hk | ⟨e, -⟩
    · exact hI.ok.zero s hk
    · omega
  · intro o b' j s hb' hjm hk
    rw [hget] at hb'; split at hb'
    · rename_i e; cases hb'; subst e
      have hlt := (hj j hjm).1
      rcases hk with hk | ⟨e, -⟩
      · exact he j hjm s hk
      · omega
    · rename_i e
      have hlt := (hI.below o b' hb').2 j hjm
      rcases hk with hk | ⟨e', -⟩
      · rcases hI.ok.edge o b' j s hb' hjm hk with h | h
        · exact Or.inl h
        · exact Or.inr (cellOut_mono hsub h)
      · omega
  · intro o b' hb' i p s hp hsp
    rw [hget] at hb'; split at hb'
    · rename_i e; cases hb'; subst e
      rcases hs i p s hp hsp with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr ⟨rfl, h1⟩, h2⟩
    · rcases hI.ok.split o b' hb' i p s hp hsp with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl h1, h2⟩
  · exact hI.drop
  · intro o b' hb'
    rw [hget] at hb'; split at hb'
    · rename_i e; cases hb'
      refine ⟨by simp [Gen.emitted]; omega, fun j hjm => ?_⟩
      have := (hj j hjm).1; simp only [Gen.emitted]; omega
    · obtain ⟨h1, h2⟩ := hI.below o b' hb'
      exact ⟨by simp only [Gen.emitted]; omega, fun j hjm => by have := h2 j hjm; simp only [Gen.emitted]; omega⟩
  · intro o s hk
    rcases hk with hk | ⟨e, -⟩
    · have := hI.kin o s hk; simp only [Gen.emitted]; omega
    · simp only [Gen.emitted]; omega

/-- What a run of `monoTryLoop` ends in. -/
def MtlPost (K : Nat → Nat → Prop) (g : Comp.Gen Map) (x : Nat) (g' : Comp.Gen Map) : Prop :=
  ∃ K', InvA K' g' ∧ x < g'.bo ∧ (∀ s, ¬ K' x s) ∧ (∀ l s, l < g.bo → (K' l s ↔ K l s)) ∧
    g.bo ≤ g'.bo ∧ g.re ≤ g'.re

theorem getJmps_hop (j : Jmp) : getJmps (Termin.hop j) = [j] := rfl
theorem getJmps_clq (r : Nat) (z w : Jmp) : getJmps (Termin.clq r z w) = [z, w] := rfl

/-- The split block of a pair or a `%both`, then its `%clq` block. -/
theorem mtl_tail {K : Nat → Nat → Prop} {g : Comp.Gen Map} (hI : InvA K g) (h0 : 0 < g.bo)
    {r rh oh fail : Nat} (hrh : r ≠ rh) (hoh : oh < g.bo) (hkoh : ∀ s, ¬ K oh s) (hf : fail < g.bo)
    (hkf : ∀ s, ¬ K fail s) (extra : List Pole) (hex : ∀ q ∈ extra, splitReg q = Option.none)
    (rt : Nat) :
    let b1 : Blob := ⟨[], [Pole.hed r rh, Pole.tal r rt] ++ extra, Termin.hop (jmp0 oh)⟩
    let K1 := fun l s => K l s ∨ (l = g.bo ∧ s = r)
    let g1 := g.emitted b1
    let b2 : Blob := ⟨[], [], Termin.clq r (jmp0 g.bo) (jmp0 fail)⟩
    InvA (fun l s => K1 l s ∨ (l = g1.bo ∧ False)) (g1.emitted b2) := by
  intro b1 K1 g1 b2
  have hI1 : InvA K1 g1 := by
    refine emitA hI h0 (fun s => s = r) (fun s _ => by simp [b1]) ?_ ?_ ?_
    · intro j hj; simp only [b1, getJmps_hop, List.mem_singleton] at hj; subst hj
      exact ⟨hoh, by simp [jmp0]⟩
    · intro j hj s hk; simp only [b1, getJmps_hop, List.mem_singleton] at hj; subst hj
      exact absurd hk (hkoh s)
    · intro i p s hp hs
      right
      have hi : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
      rcases hi with rfl | rfl | hi
      · simp [b1] at hp; subst hp; simp [splitReg] at hs; exact ⟨hs.symm, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
      · simp [b1] at hp; subst hp; simp [splitReg] at hs
        refine ⟨hs.symm, fun l hl q hq => ?_⟩
        have : l = 0 := by omega
        subst this; simp [b1] at hq; subst hq; simp [aliasDst]; intro e; exact hrh (by omega)
      · have hp' : extra[i - 2]? = some p := by
          simp only [b1, List.cons_append] at hp
          rw [show i = (i - 2) + 1 + 1 by omega] at hp; simpa using hp
        rw [hex p (List.mem_of_getElem? hp')] at hs; cases hs
  have h1 : 0 < g1.bo := by simp [g1, Gen.emitted]
  refine emitA hI1 h1 (fun _ => False) (fun _ h => h.elim) ?_ ?_ ?_
  · intro j hj; simp only [b2, getJmps_clq, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨by simp [jmp0, g1, Gen.emitted], by simp [jmp0]⟩
    · exact ⟨by simp [jmp0, g1, Gen.emitted]; omega, by simp [jmp0]⟩
  · intro j hj s hk; simp only [b2, getJmps_clq, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rcases hk with hk | ⟨-, rfl⟩
      · exact absurd (hI.kin _ _ hk) (by simp [jmp0])
      · exact Or.inl ⟨jmp0 g.bo, jmp0 fail, rfl, by simp [jmp0]; omega⟩
    · rcases hk with hk | ⟨e, -⟩
      · exact absurd hk (hkf s)
      · simp [jmp0] at e; omega
  · intro i p s hp; simp [b2] at hp

theorem invA_re {K : Nat → Nat → Prop} {g : Comp.Gen Map} (h : InvA K g) :
    InvA K { g with re := g.re + 1 } := ⟨h.ok, h.drop, h.below, h.kin⟩

/-- **`+mono-try-call` keeps `InvA`**, the annotation growing only above the
old `bo`, with a result below `bo` that has no annotation. -/
theorem mtl_kpa (fail : Nat) : ∀ (ned : Comp.Need) (r o : Nat) (K : Nat → Nat → Prop) (g : Comp.Gen Map)
    (x : Nat) (g' : Comp.Gen Map), InvA K g → monoTryLoop fail ned r o g = some (x, g') → r < g.re →
    o < g.bo → fail < g.bo → (∀ s, ¬ K o s) → (∀ s, ¬ K fail s) → MtlPost K g x g'
  | Need.none, r, o, K, g, x, g', hI, e, hr, ho, hf, hko, hkf => by
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨K, hI, ho, hko, fun _ _ _ => Iff.rfl, Nat.le_refl _, Nat.le_refl _⟩
  | Need.this rn, r, o, K, g, x, g', hI, e, hr, ho, hf, hko, hkf => by
    simp only [monoTryLoop] at e
    split at e
    · cases e
    rw [emit_apply] at e; cases e
    have h0 : 0 < g.bo := by omega
    refine ⟨_, emitA hI h0 (fun _ => False) (fun _ h => h.elim) ?_ ?_ ?_, by simp [Gen.emitted], ?_, ?_,
      by simp [Gen.emitted], by simp [Gen.emitted]⟩
    · intro j hj; simp only [getJmps_hop, List.mem_singleton] at hj; subst hj
      exact ⟨ho, by simp [jmp0]⟩
    · intro j hj s hk; simp only [getJmps_hop, List.mem_singleton] at hj; subst hj
      exact absurd hk (hko s)
    · intro i p s hp hs
      have : i = 0 ∨ 1 ≤ i := by omega
      rcases this with rfl | hi
      · simp at hp; subst hp; simp [splitReg] at hs
      · simp at hp; rw [List.getElem?_eq_none (by simp; omega)] at hp; cases hp
    · intro s hk; rcases hk with hk | ⟨-, hk⟩
      · exact absurd (hI.kin _ _ hk) (Nat.lt_irrefl _)
      · exact hk
    · intro l s hl; constructor
      · intro hk; rcases hk with hk | ⟨e, -⟩
        · exact hk
        · omega
      · exact Or.inl
  | Need.pair h t, r, o, K, g, x, g', hI, e, hr, ho, hf, hko, hkf => by
    simp only [monoTryLoop] at e
    obtain ⟨rt, gA, hA, e⟩ := bind_some e
    rw [re_apply] at hA; cases hA
    obtain ⟨rh, gB, hB, e⟩ := bind_some e
    rw [re_apply] at hB; cases hB
    obtain ⟨ot, gC, hC, e⟩ := bind_some e
    obtain ⟨oh, gD, hD, e⟩ := bind_some e
    obtain ⟨os, g1, h1, e⟩ := bind_some e
    rw [emit_apply] at h1; cases h1
    rw [emit_apply] at e; cases e
    obtain ⟨K1, hI1, hot, hkot, hag1, hbo1, hre1⟩ := mtl_kpa fail t g.re o K _ ot gC (invA_re (invA_re hI)) hC
      (by show g.re < g.re + 1 + 1; omega) ho hf hko hkf
    simp only at hbo1 hre1
    obtain ⟨K2, hI2, hoh, hkoh, hag2, hbo2, hre2⟩ := mtl_kpa fail h (g.re + 1) ot K1 gC oh gD hI1 hD
      (by omega) hot (by omega) hkot (fun s hk => hkf s ((hag1 fail s hf).mp hk))
    have hkf2 : ∀ s, ¬ K2 fail s := fun s hk => hkf s ((hag1 fail s hf).mp ((hag2 fail s (by omega)).mp hk))
    have hT := mtl_tail (r := r) (rh := g.re + 1) hI2 (by omega) (by omega) hoh hkoh (by omega) hkf2 []
      (fun q hq => absurd hq List.not_mem_nil) g.re
    simp only [List.append_nil] at hT
    refine ⟨_, hT, by simp [Gen.emitted], ?_, ?_, by simp [Gen.emitted]; omega, by simp [Gen.emitted]; omega⟩
    · intro s hk
      rcases hk with (hk | ⟨e, -⟩) | ⟨-, hk⟩
      · have := hI2.kin _ _ hk; simp only [Gen.emitted] at this; omega
      · simp [Gen.emitted] at e
      · exact hk
    · intro l s hl; constructor
      · intro hk
        rcases hk with (hk | ⟨e, -⟩) | ⟨e, -⟩
        · exact (hag1 l s hl).mp ((hag2 l s (by omega)).mp hk)
        · omega
        · simp [Gen.emitted] at e; omega
      · intro hk; exact Or.inl (Or.inl ((hag2 l s (by omega)).mpr ((hag1 l s hl).mpr hk)))
  | Need.both rn h t, r, o, K, g, x, g', hI, e, hr, ho, hf, hko, hkf => by
    simp only [monoTryLoop] at e
    obtain ⟨rt, gA, hA, e⟩ := bind_some e
    rw [re_apply] at hA; cases hA
    obtain ⟨rh, gB, hB, e⟩ := bind_some e
    rw [re_apply] at hB; cases hB
    obtain ⟨ot, gC, hC, e⟩ := bind_some e
    obtain ⟨oh, gD, hD, e⟩ := bind_some e
    split at e
    · cases e
    obtain ⟨os, g1, h1, e⟩ := bind_some e
    rw [emit_apply] at h1; cases h1
    rw [emit_apply] at e; cases e
    obtain ⟨K1, hI1, hot, hkot, hag1, hbo1, hre1⟩ := mtl_kpa fail t g.re o K _ ot gC (invA_re (invA_re hI)) hC
      (by show g.re < g.re + 1 + 1; omega) ho hf hko hkf
    simp only at hbo1 hre1
    obtain ⟨K2, hI2, hoh, hkoh, hag2, hbo2, hre2⟩ := mtl_kpa fail h (g.re + 1) ot K1 gC oh gD hI1 hD
      (by omega) hot (by omega) hkot (fun s hk => hkf s ((hag1 fail s hf).mp hk))
    have hkf2 : ∀ s, ¬ K2 fail s := fun s hk => hkf s ((hag1 fail s hf).mp ((hag2 fail s (by omega)).mp hk))
    have hT := mtl_tail (r := r) (rh := g.re + 1) hI2 (by omega) (by omega) hoh hkoh (by omega) hkf2
      [Pole.mov r rn] (fun q hq => by simp at hq; subst hq; rfl) g.re
    simp only [List.cons_append, List.nil_append] at hT
    refine ⟨_, hT, by simp [Gen.emitted], ?_, ?_, by simp [Gen.emitted]; omega, by simp [Gen.emitted]; omega⟩
    · intro s hk
      rcases hk with (hk | ⟨e, -⟩) | ⟨-, hk⟩
      · have := hI2.kin _ _ hk; simp only [Gen.emitted] at this; omega
      · simp [Gen.emitted] at e
      · exact hk
    · intro l s hl; constructor
      · intro hk
        rcases hk with (hk | ⟨e, -⟩) | ⟨e, -⟩
        · exact (hag1 l s hl).mp ((hag2 l s (by omega)).mp hk)
        · omega
        · simp [Gen.emitted] at e; omega
      · intro hk; exact Or.inl (Or.inl ((hag2 l s (by omega)).mpr ((hag1 l s hl).mpr hk)))

end Glue
end SkaModel
end Formalization
