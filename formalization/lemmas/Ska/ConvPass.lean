import lemmas.Ska.ConvArms

/-!
# Convergence: `+cull`, `+sweep`, and the stable pass

`+cull` keeps the convergence invariant with the same frozen entries: a live
member's callees among the members are live (`liveLoop_closed`), and every
member it keeps above the root is reachable from the root
(`liveLoop_sound`).  `+sweep` lists every member reachable from the root
(`sweepLoop_closed`), so after a cull the sweep of the next pass lists every
member above the root.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## Reachability over the callees -/

/-- `c` is reachable from `a` over the callees in `st`, through identities
in `W`. -/
inductive Reach (st : SkaState M R) (W : Ident → Prop) (a : Ident) : Ident → Prop where
  | refl : Reach st W a a
  | step {b c : Ident} : Reach st W a b → c ∈ kids st b → W c → Reach st W a c

/-- **The live set of `+cull` is closed**: a live member's callees among the
members are live. -/
theorem liveLoop_closed {st : SkaState M R} {members : M Ident Unit} :
    ∀ (n : Nat) (q : List Ident) (live live' : M Ident Unit), liveLoop st members n q live = some live' →
    (∀ x, Treap.has live x = true → ∀ k ∈ kids st x, Treap.has members k = true → Treap.has live k = true ∨ k ∈ q) →
    ∀ x, Treap.has live' x = true → ∀ k ∈ kids st x, Treap.has members k = true → Treap.has live' k = true
  | 0, _, _, _, h, _ => by simp [liveLoop] at h
  | n + 1, [], live, live', h, hI => by
    simp only [liveLoop, Option.some.injEq] at h; subst h
    intro x hx k hk hm
    rcases hI x hx k hk hm with h | h
    · exact h
    · cases h
  | n + 1, i :: q, live, live', h, hI => by
    unfold liveLoop at h
    split at h
    · rename_i hc
      refine liveLoop_closed n q live live' h (fun x hx k hk hm => ?_)
      rcases hI x hx k hk hm with h1 | h1
      · exact Or.inl h1
      · rcases List.mem_cons.mp h1 with rfl | h1
        · rcases hc with hc | hc
          · exact Or.inl hc
          · rw [hm] at hc; cases hc
        · exact Or.inr h1
    · refine liveLoop_closed n _ _ live' h (fun x hx k hk hm => ?_)
      rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
      · exact Or.inr (List.mem_append_right _ hk)
      · rcases hI x hx k hk hm with h1 | h1
        · exact Or.inl ((Treap.has_ins _ _ _).mpr (Or.inr h1))
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inl ((Treap.has_ins _ _ _).mpr (Or.inl rfl))
          · exact Or.inr (List.mem_append_left _ h1)

/-- **The live set of `+cull` is reachable** from the root, through members. -/
theorem liveLoop_sound {st : SkaState M R} {members : M Ident Unit} {a : Ident} :
    ∀ (n : Nat) (q : List Ident) (live live' : M Ident Unit), liveLoop st members n q live = some live' →
    (∀ x, Treap.has live x = true → Reach st (fun y => Treap.has members y = true) a x) →
    (∀ x ∈ q, Reach st (fun y => Treap.has members y = true) a x ∨
      ∃ y, Reach st (fun y => Treap.has members y = true) a y ∧ x ∈ kids st y) →
    ∀ x, Treap.has live' x = true → Reach st (fun y => Treap.has members y = true) a x
  | 0, _, _, _, h, _, _ => by simp [liveLoop] at h
  | n + 1, [], live, live', h, hL, _ => by
    simp only [liveLoop, Option.some.injEq] at h; subst h; exact hL
  | n + 1, i :: q, live, live', h, hL, hQ => by
    unfold liveLoop at h
    split at h
    · exact liveLoop_sound n q live live' h hL (fun x hx => hQ x (List.mem_cons_of_mem _ hx))
    · rename_i hc
      have hmi : Treap.has members i = true := by
        cases e : Treap.has members i
        · exact absurd (Or.inr (by simp [e])) hc
        · rfl
      have hri : Reach st (fun y => Treap.has members y = true) a i := by
        rcases hQ i List.mem_cons_self with h1 | ⟨y, hy, hk⟩
        · exact h1
        · exact Reach.step hy hk hmi
      refine liveLoop_sound n _ _ live' h (fun x hx => ?_) (fun x hx => ?_)
      · rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
        · exact hri
        · exact hL x hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hQ x (List.mem_cons_of_mem _ hx)
        · exact Or.inr ⟨i, hri, hx⟩

/-! ## `+sweep` lists what the root reaches -/

/-- **`+sweep` lists every member the root reaches**: its output is closed
under the callees in `was`, and holds the root. -/
theorem sweepLoop_closed {st : SkaState M R} {was : M Ident Unit} :
    ∀ (n : Nat) (seen : M Ident Unit) (stack : List (Ident × List Ident)) (out res : List Ident),
    sweepLoop st was n seen stack out = some res →
    (∀ x, Treap.has seen x = true → x ∈ out ∨ x ∈ stack.map (·.1)) →
    (∀ y ∈ out, ∀ k ∈ kids st y, Treap.has was k = true → Treap.has seen k = true) →
    (∀ p ∈ stack, ∃ pre, kids st p.1 = pre ++ p.2 ∧
      ∀ k ∈ pre, Treap.has was k = true → Treap.has seen k = true) →
    (∀ x, Treap.has seen x = true → x ∈ res) ∧
      ∀ y ∈ res, ∀ k ∈ kids st y, Treap.has was k = true → k ∈ res
  | 0, _, _, _, _, h, _, _, _ => by simp [sweepLoop] at h
  | n + 1, seen, [], out, res, h, hA, hB, _ => by
    simp only [sweepLoop, Option.some.injEq] at h
    subst h
    refine ⟨fun x hx => ?_, fun y hy k hk hw => ?_⟩
    · rcases hA x hx with h1 | h1
      · exact List.mem_reverse.mpr h1
      · simp at h1
    · rcases hA k (hB y (List.mem_reverse.mp hy) k hk hw) with h1 | h1
      · exact List.mem_reverse.mpr h1
      · simp at h1
  | n + 1, seen, (i, []) :: rest, out, res, h, hA, hB, hC => by
    simp only [sweepLoop] at h
    refine sweepLoop_closed n seen rest (i :: out) res h (fun x hx => ?_) (fun y hy k hk hw => ?_)
      (fun p hp => hC p (List.mem_cons_of_mem _ hp))
    · rcases hA x hx with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · simp only [List.map_cons, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h1
    · rcases List.mem_cons.mp hy with rfl | hy
      · obtain ⟨pre, hpre, hp⟩ := hC (y, []) List.mem_cons_self
        simp only [List.append_nil] at hpre
        rw [hpre] at hk
        exact hp k hk hw
      · exact hB y hy k hk hw
  | n + 1, seen, (i, k :: ks) :: rest, out, res, h, hA, hB, hC => by
    unfold sweepLoop at h
    split at h
    · rename_i hc
      refine sweepLoop_closed n seen ((i, ks) :: rest) out res h (fun x hx => ?_) hB (fun p hp => ?_)
      · rcases hA x hx with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (by simpa using h1)
      · rcases List.mem_cons.mp hp with rfl | hp
        · obtain ⟨pre, hpre, hp'⟩ := hC (i, k :: ks) List.mem_cons_self
          refine ⟨pre ++ [k], by rw [hpre]; simp, fun k' hk' hw => ?_⟩
          rcases List.mem_append.mp hk' with hk' | hk'
          · exact hp' k' hk' hw
          · rw [List.mem_singleton.mp hk'] at hw ⊢
            rcases hc with hc | hc
            · exact hc
            · rw [hw] at hc; cases hc
        · exact hC p (List.mem_cons_of_mem _ hp)
    · refine (fun key => ⟨fun x hx => key.1 x ((Treap.has_ins _ _ _).mpr (Or.inr hx)), key.2⟩)
        (sweepLoop_closed n (Treap.ins seen k) ((k, kids st k) :: (i, ks) :: rest) out res h (fun x hx => ?_)
        (fun y hy k' hk' hw => (Treap.has_ins _ _ _).mpr (Or.inr (hB y hy k' hk' hw))) (fun p hp => ?_))
      · rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
        · exact Or.inr (by simp)
        · rcases hA x hx with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by simp at h1 ⊢; rcases h1 with h1 | h1 <;> simp [h1])
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · exact ⟨[], by simp, fun _ h => by simp at h⟩
        · obtain ⟨pre, hpre, hp'⟩ := hC (i, k :: ks) List.mem_cons_self
          refine ⟨pre ++ [k], by rw [hpre]; simp, fun k' hk' hw => ?_⟩
          rcases List.mem_append.mp hk' with hk' | hk'
          · exact (Treap.has_ins _ _ _).mpr (Or.inr (hp' k' hk' hw))
          · rw [List.mem_singleton.mp hk']; exact (Treap.has_ins _ _ _).mpr (Or.inl rfl)
        · obtain ⟨pre, hpre, hp'⟩ := hC p (List.mem_cons_of_mem _ hp)
          exact ⟨pre, hpre, fun k' hk' hw => (Treap.has_ins _ _ _).mpr (Or.inr (hp' k' hk' hw))⟩

/-- **The sweep from `id` lists everything `id` reaches through `was`.** -/
theorem sweep_reach {n : Nat} {id : Ident} {was : M Ident Unit} {st : SkaState M R} {res : List Ident}
    (h : sweep n id was st = some res) {x : Ident} (hx : Reach st (fun y => Treap.has was y = true) id x) :
    x ∈ res := by
  unfold sweep at h
  obtain ⟨h1, h2⟩ := sweepLoop_closed n _ _ [] res h
    (fun x hx => by
      rcases (Treap.has_ins _ _ _).mp hx with rfl | hx
      · exact Or.inr (by simp)
      · simp [Treap.has, Treap.get_empty] at hx)
    (fun y hy => by simp at hy)
    (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp
      exact ⟨[], by simp, fun _ h => by simp at h⟩)
  induction hx with
  | refl => exact h1 id ((Treap.has_ins _ _ _).mpr (Or.inl rfl))
  | step _ hk hw ih => exact h2 _ ih _ hk hw

end Ana
end SkaModel
end Formalization
