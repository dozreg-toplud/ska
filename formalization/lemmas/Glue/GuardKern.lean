import lemmas.Ska.RawInvKern
import lemmas.Glue.Entry

/-!
# The `%cel` guard of `+kern-need` (track G, step 1 of `GuardMonoX`)

`+kern-need` (`kernLoop`, through `kernBoth`) emits, for a pair of the need
at register `d`, `mov r d, cel d, hed d rh, Ah.., tal d rt, At..` (the
`%hed` part only if the head's ops `Ah` are not empty, the `%tal` part
likewise).  The `%tal d rt` relies on the `%cel d` across `hed d rh` and
`Ah`: the **freshness fact** is that none of them writes `d`.  It holds
because `rh` is a register allocated after `d` (`d < g.re ≤ rh`), and
track D's `KR.defs` says the ops of a sub-need `h` write only registers of
`h` or registers allocated during the call, and `Distinct` says `d` is not
a register of `h` (for a `%both d h t`; for a `%pair` the `d` is a fresh
register, above every register of the need).

* `GuardedPre d B`: every `%hed s` / `%tal s` of `B` is guarded inside `B`,
  or splits `s = d` with no write of `d` before it in `B`;
* `guardedBody_cel`: `GuardedPre d B` gives `GuardedBody (cel d :: B)`;
* `guardedPre_append`: two such lists, the first writing no `d`;
* `kernBoth_guard`, `kernLoop_guarded`: the ops of `+kern-need` are a
  `GuardedBody` (with track D's `KR`), so is `kernNeed`'s output.

The ops put IN FRONT of a body by `addOps` keep it guarded
(`guardedBody_append`) because `GuardedBody` is a property of a list on its
own: each `%hed` / `%tal` of the old body has its `%cel` in the old body, and
the indices between them do not change.  `addOps` never splits a guard: the
whole output of one `+kern-need` goes in front in one piece.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

/-! ## Guards across a prefix -/

/-- Every `%hed s` / `%tal s` of `B` is guarded inside `B`, or splits `d` with
no write of `d` before it in `B` (so a `%cel d` in front guards it). -/
def GuardedPre (d : Nat) (B : List Pole) : Prop :=
  ∀ i p s, B[i]? = some p → splitReg p = some s →
    (∃ j : Nat, j < i ∧ B[j]? = some (Pole.cel s) ∧
      ∀ l, j < l → l < i → ∀ q, B[l]? = some q → aliasDst q ≠ some s) ∨
    (s = d ∧ ∀ l, l < i → ∀ q, B[l]? = some q → aliasDst q ≠ some s)

theorem guardedPre_nil (d : Nat) : GuardedPre d [] := fun i p s h => by simp at h

theorem guardedBody_cel {d : Nat} {B : List Pole} (h : GuardedPre d B) : GuardedBody (Pole.cel d :: B) := by
  intro i p s hp hs
  cases i with
  | zero => simp at hp; subst hp; simp [splitReg] at hs
  | succ i =>
    simp only [List.getElem?_cons_succ] at hp
    rcases h i p s hp hs with ⟨j, hj, hjc, hw⟩ | ⟨rfl, hw⟩
    · refine ⟨j + 1, by omega, by simpa using hjc, fun l h1 h2 q hq => ?_⟩
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      simp only [List.getElem?_cons_succ] at hq
      exact hw l' (by omega) (by omega) q hq
    · refine ⟨0, by omega, by simp, fun l h1 h2 q hq => ?_⟩
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      simp only [List.getElem?_cons_succ] at hq
      exact hw l' (by omega) q hq

/-- An op that splits nothing in front of a guarded body. -/
theorem guardedBody_cons {p0 : Pole} {B : List Pole} (h0 : splitReg p0 = Option.none) (h : GuardedBody B) :
    GuardedBody (p0 :: B) :=
  guardedBody_append (A := [p0]) (fun i p s hp hs => by
    cases i with
    | zero => simp at hp; subst hp; rw [h0] at hs; cases hs
    | succ i => simp at hp) h

/-- A `%hed d x` / `%tal d x` in front of a guarded list. -/
theorem guardedPre_split {d x : Nat} {mk : Nat → Nat → Pole} (hmk : splitReg (mk d x) = some d)
    {A : List Pole} (h : GuardedBody A) : GuardedPre d (mk d x :: A) := by
  intro i p s hp hs
  cases i with
  | zero =>
    simp at hp; subst hp; rw [hmk] at hs; cases hs
    exact Or.inr ⟨rfl, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hp
    obtain ⟨j, hj, hjc, hw⟩ := h i p s hp hs
    refine Or.inl ⟨j + 1, by omega, by simpa using hjc, fun l h1 h2 q hq => ?_⟩
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    simp only [List.getElem?_cons_succ] at hq
    exact hw l' (by omega) (by omega) q hq

theorem guardedPre_append {d : Nat} {A B : List Pole} (hA : GuardedPre d A) (hB : GuardedPre d B)
    (hw : ∀ q ∈ A, aliasDst q ≠ some d) : GuardedPre d (A ++ B) := by
  intro i p s hp hs
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [List.getElem?_append_left hi] at hp
    rcases hA i p s hp hs with ⟨j, hj, hjc, hw'⟩ | ⟨e, hw'⟩
    · refine Or.inl ⟨j, hj, by rw [List.getElem?_append_left (by omega)]; exact hjc, fun l h1 h2 q hq => ?_⟩
      rw [List.getElem?_append_left (by omega)] at hq
      exact hw' l h1 h2 q hq
    · refine Or.inr ⟨e, fun l h1 q hq => ?_⟩
      rw [List.getElem?_append_left (by omega)] at hq
      exact hw' l h1 q hq
  · rw [List.getElem?_append_right hi] at hp
    rcases hB (i - A.length) p s hp hs with ⟨j, hj, hjc, hw'⟩ | ⟨e, hw'⟩
    · refine Or.inl ⟨j + A.length, by omega, by rw [List.getElem?_append_right (by omega)]; simpa using hjc,
        fun l h1 h2 q hq => ?_⟩
      rw [List.getElem?_append_right (by omega)] at hq
      exact hw' (l - A.length) (by omega) (by omega) q hq
    · refine Or.inr ⟨e, fun l h1 q hq => ?_⟩
      rcases Nat.lt_or_ge l A.length with hl | hl
      · rw [List.getElem?_append_left hl] at hq
        subst e
        exact hw q (List.mem_of_getElem? hq)
      · rw [List.getElem?_append_right hl] at hq
        exact hw' (l - A.length) (by omega) q hq

/-- The `%hed` / `%tal` part of `kernBoth`, guarded from a `%cel d` in front. -/
theorem guardedPre_part {d x : Nat} {mk : Nat → Nat → Pole} (hmk : splitReg (mk d x) = some d)
    {A : List Pole} (h : GuardedBody A) : GuardedPre d (if A = [] then [] else mk d x :: A) := by
  split
  · exact guardedPre_nil d
  · exact guardedPre_split hmk h

/-! ## `+kern-need` -/

variable {Map : Type → Type} [HoonMap Map]

/-- **The case `%both` of the loop of `+kern-need` is guarded** (the
freshness fact: the head's ops, between the `%cel d` and the `%tal d`, do
not write `d`). -/
theorem kernBoth_guard {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)} {h t : Need}
    {acc ops : List Pole} {g g' : Comp.Gen Map}
    (Kh : ∀ x acc g g' ops, kh x acc g = some (ops, g') → x < g.re → ¬ NMem h x → NB g.re h →
      ∃ A, ops = A ++ acc ∧ KR h x g g' A ∧ GuardedBody A)
    (Kt : ∀ x acc g g' ops, kt x acc g = some (ops, g') → x < g.re → ¬ NMem t x → NB g.re t →
      ∃ A, ops = A ++ acc ∧ KR t x g g' A ∧ GuardedBody A)
    (ndh : ¬ NMem h d) (bh : NB g.re h) (bt : NB g.re t) (hd : d < g.re)
    (hk : kernBoth r d kh kt acc g = some (ops, g')) :
    ∃ A, ops = A ++ acc ∧ GuardedBody A := by
  simp only [kernBoth] at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨ops1, g2, h2, hk⟩ := bind_some hk
  obtain ⟨At, eAt, Kt', Gt⟩ := Kt _ _ _ _ _ h2 (by simp) (fun e => by have := bt _ e; simp at this)
    (bt.mono (by simp))
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  rw [re_apply] at h3; simp only [Option.some.injEq, Prod.mk.injEq] at h3; obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨ops3, g4, h4, hk⟩ := bind_some hk
  have l2 := Kt'.le
  simp only at l2
  have hrt' : ¬ NMem h g2.re := fun e => by have := bh _ e; omega
  obtain ⟨Ah, eAh, Kh', Gh⟩ := Kh _ _ _ _ _ h4 (by simp) hrt' (bh.mono (by simp; omega))
  by_cases hrd : r = d
  · simp [hrd] at hk; cases hk
  simp only [hrd, if_false, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  have eT : (if ops1 ≠ acc then Pole.tal d g.re :: ops1 else ops1) =
      (if At = [] then [] else Pole.tal d g.re :: At) ++ acc := by
    rw [eAt]; by_cases e : At = [] <;> simp [e, app_eq_self]
  rw [eT] at eAh
  have eH : (if ops3 ≠ (if At = [] then [] else Pole.tal d g.re :: At) ++ acc then Pole.hed d g2.re :: ops3 else ops3) =
      (if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++ ((if At = [] then [] else Pole.tal d g.re :: At) ++ acc) := by
    rw [eAh]; by_cases e : Ah = [] <;> simp [e, app_eq_self]
  rw [eT, eH]
  refine ⟨Pole.mov r d :: Pole.cel d :: ((if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++
    (if At = [] then [] else Pole.tal d g.re :: At)), by simp, ?_⟩
  refine guardedBody_cons rfl (guardedBody_cel (guardedPre_append (guardedPre_part rfl Gh)
    (guardedPre_part rfl Gt) fun q hq => ?_))
  split at hq
  · simp at hq
  · rcases List.mem_cons.mp hq with rfl | hq
    · simp only [aliasDst, ne_eq, Option.some.injEq]; omega
    · intro e
      rcases Kh'.defs d (mem_defsOf.mpr ⟨q, hq, e⟩) with e' | e'
      · exact ndh e'
      · simp at e'; omega

theorem kr_guard {tgt : Need} {r : Nat} {acc ops : List Pole} {g g' : Comp.Gen Map}
    (h1 : ∃ A, ops = A ++ acc ∧ KR tgt r g g' A) (h2 : ∃ A, ops = A ++ acc ∧ GuardedBody A) :
    ∃ A, ops = A ++ acc ∧ KR tgt r g g' A ∧ GuardedBody A := by
  obtain ⟨A, eA, K⟩ := h1
  obtain ⟨A', eA', G⟩ := h2
  have e : A' = A := List.append_cancel_right (eA'.symm.trans eA)
  exact ⟨A, eA, K, e ▸ G⟩

/-- **The loop of `+kern-need` is guarded.** -/
theorem kernLoop_guard : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Comp.Gen Map) (ops : List Pole),
    kernLoop r tgt acc g = some (ops, g') → r < g.re → ¬ NMem tgt r → NB g.re tgt → Distinct tgt →
    ∃ A, ops = A ++ acc ∧ GuardedBody A := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h _ _ _ _
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, guardedBody_nil⟩
  | this d =>
    intro r acc g g' ops h hr hn nb _
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[Pole.mov r d], rfl, guardedBody_cons rfl guardedBody_nil⟩
  | pair p q ihp ihq =>
    intro r acc g g' ops h hr hn nb dn
    obtain ⟨dp, dq, ap⟩ := dn
    simp only [kernLoop] at h
    obtain ⟨rn, g1, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    exact kernBoth_guard (h := p) (t := q)
      (fun x acc g g' ops hk hx hnx bh =>
        kr_guard (kernLoop_raw p x acc g g' ops hk hx hnx bh dp) (ihp x acc g g' ops hk hx hnx bh dp))
      (fun x acc g g' ops hk hx hnx bt =>
        kr_guard (kernLoop_raw q x acc g g' ops hk hx hnx bt dq) (ihq x acc g g' ops hk hx hnx bt dq))
      (fun e => by have := nb _ (Or.inl e); simp at this)
      (fun y hy => by have := nb y (Or.inl hy); simp; omega) (fun y hy => by have := nb y (Or.inr hy); simp; omega)
      (by simp) h
  | both d h t ihh iht =>
    intro r acc g g' ops hk hr hn nb dn
    obtain ⟨dh, dt, ap, ndh, ndt⟩ := dn
    simp only [kernLoop] at hk
    exact kernBoth_guard (h := h) (t := t)
      (fun x acc g g' ops hk hx hnx bh =>
        kr_guard (kernLoop_raw h x acc g g' ops hk hx hnx bh dh) (ihh x acc g g' ops hk hx hnx bh dh))
      (fun x acc g g' ops hk hx hnx bt =>
        kr_guard (kernLoop_raw t x acc g g' ops hk hx hnx bt dt) (iht x acc g g' ops hk hx hnx bt dt))
      ndh (fun y hy => nb y (Or.inr (Or.inl hy))) (fun y hy => nb y (Or.inr (Or.inr hy))) (nb d (Or.inl rfl)) hk

/-- **The ops of `+kern-need` (track D's `KR`) are a guarded body.** -/
theorem kernLoop_guarded (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Comp.Gen Map) (ops : List Pole)
    (h : kernLoop r tgt acc g = some (ops, g')) (hr : r < g.re) (hn : ¬ NMem tgt r) (nb : NB g.re tgt)
    (dn : Distinct tgt) : ∃ A, ops = A ++ acc ∧ KR tgt r g g' A ∧ GuardedBody A :=
  kr_guard (kernLoop_raw tgt r acc g g' ops h hr hn nb dn) (kernLoop_guard tgt r acc g g' ops h hr hn nb dn)

/-- **`+kern-need`**: its output is a guarded body. -/
theorem kernNeed_guarded {tgt : Need} {r : Nat} {g g' : Comp.Gen Map} {ops : List Pole}
    (h : kernNeed r tgt g = some (ops, g')) (hr : r < g.re) (hn : ¬ NMem tgt r) (nb : NB g.re tgt)
    (dn : Distinct tgt) : GuardedBody ops := by
  obtain ⟨A, eA, -, G⟩ := kernLoop_guarded tgt r [] g g' ops h hr hn nb dn
  rw [eA, List.append_nil]; exact G

end Glue
end SkaModel
end Formalization
