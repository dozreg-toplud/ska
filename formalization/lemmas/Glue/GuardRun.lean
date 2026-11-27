import lemmas.Glue.GuardKern

/-!
# `BlocksOK` kept by the steps of `+comp` (track G, step 1 of `GuardMonoX`)

The steps of a raw run that touch the blocks, each keeping `BlocksOK` (no
block passes `~`, every body is guarded; `Glue/Entry.lean`):

* `blocksOK_emitted`: `+emit` of a block that passes no `~` and has a
  guarded body;
* `addOps_ok`: `+add-ops` of a guarded list (`guardedBody_append`: the
  guards of the old body lie inside it);
* `blocksOK_insertHop`: `+insert-hop` moves a body and its end to a new
  label and leaves an empty body with a jump without arguments;
* `sureLoop_guard`: `+sure-loop` (what `+coerce-lazy` and the prologue of
  `finishLF` run) puts in front only the output of `+kern-need`
  (`kernNeed_guarded`) and single `%mov`s, under track D's hypotheses of
  `raw_sureLoop` (a `Distinct` target below `re`, the input need below
  `re`, apart from the target).

Where `~` comes from: only `+sect`'s threading (`sectStep`) passes `~`, for
a proxy one branch made and the other did not.  On `FragX` a run leaves
`cond` as it is (track D's `KeepX`, field `cnd`), so the threading leaves the
blocks as they are (`sect_spec`: `SameBlocks`, used in `atx_sixN`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

variable {Map : Type → Type} [HoonMap Map]

/-- A block passes no `~` and has a guarded body. -/
def BlockOK (b : Blob) : Prop := (∀ j ∈ getJmps b.fin, Option.none ∉ j.args) ∧ GuardedBody b.body

theorem blocksOK_put {bl : Map Blob} {o : Nat} {b : Blob} (h : BlocksOK bl) (hb : BlockOK b) :
    BlocksOK (HoonMap.put bl o b) := by
  intro k x hx
  by_cases e : k = o
  · subst e; rw [get_put_self] at hx; cases hx; exact hb
  · rw [get_put_ne e] at hx; exact h k x hx

theorem blocksOK_emitted {g : Comp.Gen Map} {b : Blob} (h : BlocksOK g.blocks) (hb : BlockOK b) :
    BlocksOK (g.emitted b).blocks := by
  simp only [Gen.emitted]
  split
  · exact h
  · exact blocksOK_put h hb

/-- **`+add-ops` of a guarded list** keeps `BlocksOK` and the registers. -/
theorem addOps_ok {g g' : Comp.Gen Map} {o : Nat} {A : List Pole} {u : Unit} (h : BlocksOK g.blocks)
    (hA : GuardedBody A) (ha : addOps o A g = some (u, g')) : BlocksOK g'.blocks ∧ g'.re = g.re := by
  unfold addOps at ha
  split at ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha; rw [← ha.2]; exact ⟨h, rfl⟩
  · cases hb : HoonMap.get g.blocks o with
    | none => rw [hb] at ha; cases ha
    | some b =>
      rw [hb] at ha
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at ha
      rw [← ha.2]
      exact ⟨blocksOK_put h ⟨(h o b hb).1, guardedBody_append hA (h o b hb).2⟩, rfl⟩

/-- **`+insert-hop`** keeps `BlocksOK`. -/
theorem blocksOK_insertHop {g g' : Comp.Gen Map} {a o1 o2 : Nat} {u : Unit} (h : BlocksOK g.blocks)
    (hi : insertHop a o1 o2 g = some (u, g')) : BlocksOK g'.blocks := by
  unfold insertHop at hi
  split at hi
  · simp only [Option.some.injEq, Prod.mk.injEq] at hi; rw [← hi.2]; exact h
  · cases hb : HoonMap.get g.blocks a with
    | none => rw [hb] at hi; cases hi
    | some b =>
      rw [hb] at hi
      simp only [Option.bind_some] at hi
      split at hi
      · split at hi
        · cases hi
        · simp only [Option.some.injEq, Prod.mk.injEq] at hi
          rw [← hi.2]
          refine blocksOK_put (blocksOK_put h ⟨(h a b hb).1, (h a b hb).2⟩) ⟨?_, guardedBody_nil⟩
          intro j hj
          simp only [getJmps, List.mem_singleton] at hj
          subst hj; simp
      · cases hi

/-- **`+sure-loop` keeps `BlocksOK`**: it puts in front of the block only
`+kern-need`'s output and single `%mov`s. -/
theorem sureLoop_guard {o : Nat} : ∀ (ned tgt : Need) (g g' : Comp.Gen Map) (u : Unit),
    BlocksOK g.blocks → Distinct tgt → NB g.re tgt → NB g.re ned → (∀ y, NMem ned y → ¬ NMem tgt y) →
    sureLoop o ned tgt g = some (u, g') → BlocksOK g'.blocks ∧ g.re ≤ g'.re := by
  intro ned
  induction ned with
  | none =>
    intro tgt g g' u h dt nt nn ap hs
    simp only [sureLoop] at hs
    by_cases e : tgt = Need.none
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs; exact ⟨h, Nat.le_refl _⟩
    · rw [if_neg e] at hs; cases hs
  | this r =>
    intro tgt g g' u h dt nt nn ap hs
    simp only [sureLoop] at hs
    obtain ⟨ops, g1, h1, hs⟩ := bind_some hs
    obtain ⟨B, eB, K, G⟩ := kernLoop_guarded tgt r [] g g1 ops h1 (nn r rfl) (fun e => ap r rfl e) nt dt
    simp only [List.append_nil] at eB
    rw [eB] at hs
    have b1 : g1.blocks = g.blocks := by rw [K.gen]
    have A := addOps_ok (by rw [b1]; exact h) G hs
    exact ⟨A.1, by have := K.le; omega⟩
  | pair p q ihp ihq =>
    intro tgt g g' u h dt nt nn ap hs
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs; exact ⟨h, Nat.le_refl _⟩
    | pair tp tq =>
      simp only [sureLoop] at hs
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dp, dq, apq⟩ := dt
      obtain ⟨B1, l1⟩ := ihp tp g g1 u1 h dp (fun y hy => nt y (Or.inl hy)) (fun y hy => nn y (Or.inl hy))
        (fun y hy e => ap y (Or.inl hy) (Or.inl e)) h1
      obtain ⟨B2, l2⟩ := ihq tq g1 g' u B1 dq (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr hy)) l1) (fun y hy e => ap y (Or.inr hy) (Or.inr e)) hs
      exact ⟨B2, by omega⟩
    | this d => simp [sureLoop, crashM] at hs
    | both d th tt => simp [sureLoop, crashM] at hs
  | both r hh tt ihh iht =>
    intro tgt g g' u h dt nt nn ap hs
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs; exact ⟨h, Nat.le_refl _⟩
    | this d =>
      simp only [sureLoop] at hs
      by_cases e : r = d
      · rw [if_pos e] at hs; cases hs
      rw [if_neg e] at hs
      have A := addOps_ok h (guardedBody_cons rfl guardedBody_nil) hs
      exact ⟨A.1, by omega⟩
    | pair tp tq =>
      simp only [sureLoop] at hs
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dp, dq, apq⟩ := dt
      obtain ⟨B1, l1⟩ := ihh tp g g1 u1 h dp (fun y hy => nt y (Or.inl hy))
        (fun y hy => nn y (Or.inr (Or.inl hy))) (fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inl e)) h1
      obtain ⟨B2, l2⟩ := iht tq g1 g' u B1 dq (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr (Or.inr hy))) l1)
        (fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr e)) hs
      exact ⟨B2, by omega⟩
    | both d th tt' =>
      simp only [sureLoop] at hs
      by_cases e : r = d
      · rw [if_pos e] at hs; cases hs
      rw [if_neg e] at hs
      obtain ⟨u0, g0, h0, hs⟩ := bind_some hs
      have A0 := addOps_ok h (guardedBody_cons rfl guardedBody_nil) h0
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dh, dtt, apq, ndh, ndt⟩ := dt
      obtain ⟨B1, l1⟩ := ihh th g0 g1 u1 A0.1 dh (fun y hy => by rw [A0.2]; exact nt y (Or.inr (Or.inl hy)))
        (fun y hy => by rw [A0.2]; exact nn y (Or.inr (Or.inl hy)))
        (fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inr (Or.inl e))) h1
      obtain ⟨B2, l2⟩ := iht tt' g1 g' u B1 dtt
        (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr (Or.inr hy))) (by omega))
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr (Or.inr hy))) (by omega))
        (fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr (Or.inr e))) hs
      exact ⟨B2, by omega⟩

end Glue
end SkaModel
end Formalization
