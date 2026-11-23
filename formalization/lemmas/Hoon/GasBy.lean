module

public import lemmas.Hoon.PutBy
import all lemmas.Pill.Arm.By

/-!
`+gas:by` of the pill's `hoon.hoon` puts a list of pairs into a map, in the
order of the list.

```hoon
++  gas                                               ::  concatenate
  ~/  %gas
  |*  b=(list [p=_?>(?=(^ a) p.n.a) q=_?>(?=(^ a) q.n.a)])
  =>  .(b `(list _?>(?=(^ a) n.a))`b)
  |-  ^+  a
  ?~  b
    a
  $(b t.b, a (put p.i.b q.i.b))
```
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- A pair of nouns as a noun. -/
def pairNoun (x : Noun × Noun) : Noun := C x.1 x.2

/-- `+gas:by`: `putF` of each pair of the list, in order. -/
def gasF (mug : Noun → Nat) : Noun → List (Noun × Noun) → Option Noun
  | a, [] => some a
  | a, (k, v) :: rest =>
    match putF mug k v a with
    | some a' => gasF mug a' rest
    | none => none

@[nock_exec] theorem gas_arm (d : Noun) :
    nock d by.gas.arm = some (C by.gas.battery (C (A 0) d)) := by
  nock_open by.gas.arm; simp only [nock_exec]

theorem gas_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ (l : List (Noun × Noun)) (a out : Noun), gasF mug a l = some out →
      nock (C by.gas.loop (C by.gas.battery (C (listN (l.map pairNoun)) (C by.battery (C a ctx)))))
        by.gas.loop = some out := by
  intro l
  induction l with
  | nil =>
    intro a out h
    cases h
    nock_open by.gas.loop
    simp [nock_exec]
  | cons x rest ih =>
    intro a out h
    obtain ⟨k, v⟩ := x
    simp only [gasF] at h
    cases hp : putF mug k v a with
    | none => rw [hp] at h; cases h
    | some a' =>
      rw [hp] at h
      nock_open by.gas.loop
      simp [nock_exec, pairNoun, put_arm, put_gate ctx hc k v a a' hp, ih a' out h]

/-- The gate `gas` of the door `by` with map `a`, slammed on a list of pairs. -/
theorem gas_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (l : List (Noun × Noun)) (a out : Noun) (h : gasF mug a l = some out) :
    nock (C by.gas.battery (C (listN (l.map pairNoun)) (C by.battery (C a ctx)))) by.gas.battery
      = some out := by
  nock_open by.gas.battery
  simp only [nock_exec, gas_loop ctx hc l a out h]

/-- The value of the last pair of the list with key `k`. -/
def lastVal (k : Noun) : List (Noun × Noun) → Option Noun
  | [] => none
  | (k', v) :: rest =>
    match lastVal k rest with
    | some w => some w
    | none => if k' = k then some v else none

theorem gasF_spec {mug : Noun → Nat} : ∀ (l : List (Noun × Noun)) (a : Noun), IsMap mug a →
    ∃ out, gasF mug a l = some out ∧ IsMap mug out ∧
      ∀ k v, Get out k v ↔ lastVal k l = some v ∨ (lastVal k l = none ∧ Get a k v) := by
  intro l
  induction l with
  | nil => intro a h; exact ⟨a, rfl, h, fun k v => by simp [lastVal]⟩
  | cons x rest ih =>
    intro a h
    obtain ⟨k0, v0⟩ := x
    obtain ⟨a', hp, hm', hg'⟩ := putF_spec mug a k0 v0 h
    obtain ⟨out, ho, hm, hg⟩ := ih a' hm'
    refine ⟨out, by simp [gasF, hp, ho], hm, fun k v => ?_⟩
    rw [hg, hg']
    simp only [lastVal]
    cases hl : lastVal k rest with
    | some w => simp
    | none =>
      by_cases e : k0 = k
      · subst e; simp [eq_comm]
      · simp [e, Ne.symm e]

/-- `+gas:by` on a map: the result is a map, and each key holds its last value
in the list, or its old value if the list does not mention it. -/
theorem gas_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (a : Noun) (l : List (Noun × Noun)) (h : IsMap mug a) :
    ∃ out,
      Eval (C by.gas.battery (C (listN (l.map pairNoun)) (C by.battery (C a ctx))))
        by.gas.battery out ∧
      IsMap mug out ∧
      ∀ k v, Get out k v ↔ lastVal k l = some v ∨ (lastVal k l = none ∧ Get a k v) := by
  obtain ⟨out, hg, hm, hget⟩ := gasF_spec l a h
  exact ⟨out, eval_of_nock (gas_gate ctx hc l a out hg), hm, hget⟩

end Hoon
end Formalization

end
