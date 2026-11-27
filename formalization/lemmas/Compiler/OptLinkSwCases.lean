import lemmas.Compiler.OptLinkSwPlain
import lemmas.Hoon.SwArms

/-!
# `+switch-chains`: the gate `cases`

```hoon
  =/  cases
    |=  ces=(list case)
    ^-  (list case)
    =|  [saw=(set @) acc=(list case)]
    |-  ^+  acc
    ?~  ces  (sort acc |=([a=[c=@ *] b=[c=@ *]] (lth c.a c.b)))
    ?:  (~(has in saw) c.i.ces)  $(ces t.ces)
    $(ces t.ces, saw (~(put in saw) c.i.ces), acc [i.ces acc])
```

The model `casesOf` keeps the first case of each constant (`casesAcc`, `saw`
a list) and sorts with `hsort`, the quicksort of `+sort` with fuel; `+sort`
is `qsort` of `Hoon/ListsSort.lean`.

* `hsort_qsort`: with fuel at least the length, `hsort` returns, and the
  nouns of its result are `qsort` of the nouns, given that the order on
  nouns is the model's order on the values.
* `cs_trap`: the trap of `cases` is `qsort` of the nouns of `casesAcc`.
* `sw_cases`: **where `casesOf` returns `cas`, the gate `cases` returns the
  noun of `cas`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `hsort` is `qsort` -/

theorem qsort_nil (p : Noun → Noun → Bool) : qsort p [] = [] := by rw [qsort]

theorem qsort_cons (p : Noun → Noun → Bool) (x : Noun) (xs : List Noun) :
    qsort p (x :: xs) = qsort p (xs.filter (fun c => p c x)) ++ x :: qsort p (xs.filter (fun c => !p c x)) := by
  rw [qsort]

theorem hsort_qsort {α : Type} (f : α → Noun) (lt : α → α → Bool) (p : Noun → Noun → Bool)
    (hp : ∀ a b, p (f a) (f b) = lt a b) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → ∃ L, Opt.hsort lt n l = some L ∧ L.map f = qsort p (l.map f) := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], rfl, by simp [qsort_nil]⟩
  | succ n ih =>
    intro l hl
    cases l with
    | nil => exact ⟨[], rfl, by simp [qsort_nil]⟩
    | cons a t =>
      simp only [List.length_cons] at hl
      have h1 : (t.filter (fun c => lt c a)).length ≤ n := Nat.le_trans (List.length_filter_le _ _) (by omega)
      have h2 : (t.filter (fun c => !lt c a)).length ≤ n := Nat.le_trans (List.length_filter_le _ _) (by omega)
      obtain ⟨L1, e1, m1⟩ := ih _ h1
      obtain ⟨L2, e2, m2⟩ := ih _ h2
      refine ⟨L1 ++ a :: L2, ?_, ?_⟩
      · have e2' : List.filter (not ∘ fun c => lt c a) t = List.filter (fun c => !lt c a) t := rfl
        simp [Opt.hsort, List.partition_eq_filter_filter, e1, e2', e2]
      · rw [List.map_cons, qsort_cons, List.map_append, List.map_cons, m1, m2, List.filter_map, List.filter_map]
        have ef1 : ((fun c => p c (f a)) ∘ f) = fun c => lt c a := by funext c; simp [hp]
        have ef2 : ((fun c => !p c (f a)) ∘ f) = fun c => !lt c a := by funext c; simp [hp]
        rw [ef1, ef2]

/-! ## The trap -/

/-- The order of the `+sort` of `cases` on nouns: the heads as atoms. -/
def csP (x y : Noun) : Bool := decide (OptDec.atomOf (OptDec.hd x) < OptDec.atomOf (OptDec.hd y))

theorem csP_scase (a b : Opt.SCase) : csP (scaseN a) (scaseN b) = decide (a.c < b.c) := rfl

/-- The subject of the trap of `cases`. -/
def csT (CES S ACC BL TOPO REV USES : Noun) : Noun :=
  C swCST (C (C S ACC) (C swCSB (C CES (swS7 BL TOPO REV USES))))

theorem sortIn_layer2 : SortIn layer2 := ⟨skid.arm_at, weld.arm_at⟩

/-- The gate of the `+sort`: `(lth c.a c.b)`. -/
theorem cs_sortg (a b : Opt.SCase) (CES S ACC BL TOPO REV USES : Noun) :
    nock (C swCSSG (C (C (scaseN a) (scaseN b)) (csT CES S ACC BL TOPO REV USES))) swCSSG
      = some (loob (csP (scaseN a) (scaseN b))) := by
  have hL1 := optC_layer1
  have hlt := lth_gate layer1 decIn_layer1 a.c b.c
  rw [csP_scase]
  unfold csT swS7 swS6 swS5 swS4 swS3 swG
  generalize optC = OC at hL1
  simp [nock_exec, swCSSG, scaseN, hL1, lth.arm_at, lth_arm, hlt]

theorem cs_trap (BL TOPO REV USES : Noun) : ∀ (ces : List Opt.SCase) (saw : List Nat) (acc : List Opt.SCase)
    (S : Noun), SawRel S saw →
    nock (csT (listNoun scaseN ces) S (listNoun scaseN acc) BL TOPO REV USES) swCST
      = some (listN (qsort csP ((Opt.casesAcc ces saw acc).map scaseN))) := by
  have hL := optC_layer2
  intro ces
  induction ces with
  | nil =>
    intro saw acc S hS
    have hs := sort_gate layer2 sortIn_layer2 swCSSG (C (C (A 0) (A 0)) (C (A 0) (A 0)))
      (csT (A 0) S (listNoun scaseN acc) BL TOPO REV USES) csP (acc.map scaseN)
      (fun x hx y hy => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
        exact cs_sortg a b _ S _ BL TOPO REV USES)
    rw [← listNoun_map_listN] at hs
    simp only [Opt.casesAcc]
    unfold csT swS7 swS6 swS5 swS4 swS3 swG at *
    generalize optC = OC at hL hs
    conv => lhs; arg 2; unfold swCST
    simp [nock_exec, listNoun, hL, sort.arm_at, sort_arm, hs]
  | cons x t ih =>
    intro saw acc S hS
    have hh := saw_has hS x.c
    simp only [Opt.casesAcc]
    by_cases hx : x.c ∈ saw
    · rw [if_pos hx]
      have ih' := ih saw acc S hS
      unfold csT swS7 swS6 swS5 swS4 swS3 swG at *
      generalize optC = OC at hL ih'
      conv => lhs; arg 2; unfold swCST
      simp [nock_exec, listNoun, hL, in.arm_at, in_arm, in.has.arm_at, has_arm, hh, hx, scaseN, ih', loob]
    · rw [if_neg hx]
      obtain ⟨S', hp, hS'⟩ := saw_put hS x.c
      have ih' := ih (x.c :: saw) (x :: acc) S' hS'
      simp only [listNoun, scaseN] at ih'
      unfold csT swS7 swS6 swS5 swS4 swS3 swG at *
      generalize optC = OC at hL ih'
      conv => lhs; arg 2; unfold swCST
      simp [nock_exec, listNoun, hL, in.arm_at, in_arm, in.has.arm_at, has_arm, hh, hx, scaseN, ih', loob,
        in.put.arm_at, put_in_arm, hp]

/-! ## The gate -/

/-- **The gate `cases`**: where `casesOf` returns `cas`, the gate on the noun
of `ces` returns the noun of `cas`. -/
theorem sw_cases (BL TOPO REV USES : Noun) (ces cas : List Opt.SCase) (h : Opt.casesOf ces = some cas) :
    nock (C swCSB (C (listNoun scaseN ces) (swS7 BL TOPO REV USES))) swCSB = some (listNoun scaseN cas) := by
  have ht := cs_trap BL TOPO REV USES ces [] [] (A 0) sawRel_nil
  obtain ⟨L, e, m⟩ := hsort_qsort scaseN (fun a b => decide (a.c < b.c)) csP csP_scase
    (Opt.casesAcc ces [] []).length (Opt.casesAcc ces [] []) (Nat.le_refl _)
  unfold Opt.casesOf at h
  rw [e] at h
  cases h
  rw [← m, ← listNoun_map_listN] at ht
  unfold csT at ht
  simp only [listNoun] at ht
  conv => lhs; arg 2; unfold swCSB
  simp [nock_exec, listNoun, ht]

end Compiler
end Formalization
