import lemmas.Hoon.PutBy

/-!
`+get:by` and `+has:by` of the pill's `hoon.hoon` look a key up in a map.

```hoon
++  get
  ~/  %get
  |*  b=*
  =>  .(b `_?>(?=(^ a) p.n.a)`b)
  |-  ^-  (unit _?>(?=(^ a) q.n.a))
  ?~  a
    ~
  ?:  =(b p.n.a)
    (some q.n.a)
  ?:  (gor b p.n.a)
    $(a l.a)
  $(a r.a)
::
++  has
  ~/  %has
  |*  b=*
  !=(~ (get b))
```

As for `+put:by`, `get_loop` shows that the Nock computes the model `getF`,
and `getF_some`, `getF_none` show what `getF` returns on a map.  The gate of
`+get:by` reads `+gor` and `+some` from the context of the door.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The model -/

/-- `+get:by`: the value under the key `b` in the treap, as a unit. -/
def getF (mug : Noun → Nat) (b : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (A 0)
  | Noun.cell (Noun.cell p q) (Noun.cell l r) =>
    if b = p then some (C (A 0) q)
    else if gorF mug b p then getF mug b l else getF mug b r
  | _ => none

/-- On a map, `getF` finds the value of a key that the map holds. -/
theorem getF_some {mug : Noun → Nat} {a k v : Noun} (h : IsMap mug a) (hg : Get a k v) :
    getF mug k a = some (C (A 0) v) := by
  induction h with
  | nil => exact absurd hg Get_atom
  | @node p q l r hl hr hL hR ihl ihr =>
    rw [Get_node] at hg
    rcases hg with ⟨rfl, rfl⟩ | hg | hg
    · simp [getF]
    · have ⟨ne, g, _⟩ := hL _ _ hg
      simp [getF, ne, g, ihl hg]
    · have ⟨ne, g, _⟩ := hR _ _ hg
      have g' : ¬ gorF mug k p = true := fun g' => ne (gorF_antisymm mug g' g)
      simp [getF, ne, g', ihr hg]

/-- On a map, `getF` returns `~` for a key that the map does not hold. -/
theorem getF_none {mug : Noun → Nat} {a k : Noun} (h : IsMap mug a) (hg : ∀ v, ¬ Get a k v) :
    getF mug k a = some (A 0) := by
  induction h with
  | nil => rfl
  | @node p q l r hl hr hL hR ihl ihr =>
    have ne : k ≠ p := by
      rintro rfl
      exact hg q Get.here
    by_cases g : gorF mug k p = true
    · simp [getF, ne, g, ihl (fun v hv => hg v (Get.left hv))]
    · simp [getF, ne, g, ihr (fun v hv => hg v (Get.right hv))]

/-! ## The Nock -/

/-- `+some` is the gate `[[[1 0] 0 6] 0 c]`. -/
abbrev SomeIn (c : Noun) : Prop := slot? some.axis c = some some.arm

@[nock_exec] theorem some_arm (c : Noun) :
    nock c some.arm = some (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (A 0) c)) := by
  nock_open some.arm; simp only [nock_exec]

@[nock_exec] theorem get_arm (d : Noun) :
    nock d by.get.arm = some (C by.get.battery (C (A 0) d)) := by
  nock_open by.get.arm; simp only [nock_exec]

@[nock_exec] theorem has_arm (d : Noun) :
    nock d by.has.arm = some (C by.has.battery (C (A 0) d)) := by
  nock_open by.has.arm; simp only [nock_exec]

/-- The loop of `+get:by` in the door whose map is `a`, with sample `b`,
computes the model. -/
theorem get_loop {mug : Noun → Nat} (ctx : Noun) (hc : SomeIn ctx ∧ GorIn mug ctx)
    (b a : Noun) :
    ∀ out, getF mug b a = some out →
      nock (C by.get.loop (C by.get.battery (C b (C by.battery (C a ctx))))) by.get.loop
        = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.2.2
  obtain ⟨hs, hg, _⟩ := hc
  fun_induction getF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.get.loop
       simp [nock_exec, *]
       done)
    | (nock_open by.get.loop
       simp [nock_exec, gor_arm, *])

/-- The gate `get` of the door `by` with map `a`, slammed on `b`. -/
theorem get_gate {mug : Noun → Nat} (ctx : Noun) (hc : SomeIn ctx ∧ GorIn mug ctx)
    (b a out : Noun) (h : getF mug b a = some out) :
    nock (C by.get.battery (C b (C by.battery (C a ctx)))) by.get.battery = some out := by
  nock_open by.get.battery
  simp only [nock_exec, get_loop ctx hc b a out h]

/-- The gate `has` of the door `by` with map `a`, slammed on `b`. -/
theorem has_gate {mug : Noun → Nat} (ctx : Noun) (hc : SomeIn ctx ∧ GorIn mug ctx)
    (b a out : Noun) (h : getF mug b a = some out) :
    nock (C by.has.battery (C b (C by.battery (C a ctx)))) by.has.battery
      = some (loob (decide (out ≠ A 0))) := by
  nock_open by.has.battery
  simp only [nock_exec, get_arm, get_gate ctx hc b a out h]
  by_cases e : out = A 0
  · simp [nock_exec, e]
  · simp [nock_exec, e, Ne.symm e]

/-! ## On a map -/

/-- `+get:by` on a map: the unit of the value under the key `k`, or `~`. -/
theorem get_by {mug : Noun → Nat} (ctx : Noun) (hc : SomeIn ctx ∧ GorIn mug ctx)
    (a k : Noun) (h : IsMap mug a) :
    (∀ v, Get a k v →
      Eval (C by.get.battery (C k (C by.battery (C a ctx)))) by.get.battery (C (A 0) v)) ∧
    ((∀ v, ¬ Get a k v) →
      Eval (C by.get.battery (C k (C by.battery (C a ctx)))) by.get.battery (A 0)) :=
  ⟨fun _ hg => eval_of_nock (get_gate ctx hc k a _ (getF_some h hg)),
   fun hg => eval_of_nock (get_gate ctx hc k a _ (getF_none h hg))⟩

/-- `+has:by` on a map: whether the map holds the key `k`. -/
theorem has_by {mug : Noun → Nat} (ctx : Noun) (hc : SomeIn ctx ∧ GorIn mug ctx)
    (a k : Noun) (h : IsMap mug a) :
    ∃ f : Bool,
      Eval (C by.has.battery (C k (C by.battery (C a ctx)))) by.has.battery (loob f) ∧
      (f = true ↔ ∃ v, Get a k v) := by
  by_cases hk : ∃ v, Get a k v
  · obtain ⟨v, hv⟩ := hk
    refine ⟨true, eval_of_nock ?_, by simp; exact ⟨v, hv⟩⟩
    rw [has_gate ctx hc k a _ (getF_some h hv)]
    simp
  · have hn : ∀ v, ¬ Get a k v := fun v hv => hk ⟨v, hv⟩
    refine ⟨false, eval_of_nock ?_, by simp; exact hn⟩
    rw [has_gate ctx hc k a _ (getF_none h hn)]
    simp

/-- The pill's second layer holds `+some`. -/
theorem someIn_layer2 : SomeIn layer2 := some.arm_at

end Hoon
end Formalization
