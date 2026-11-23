module

public import lemmas.Hoon.Sets
public import lemmas.Hoon.RepBy
import all lemmas.Pill.Arm.By
import all lemmas.Pill.Arm.In

/-!
`+key:by`, `+run:by` and `+any:by` of the pill's `hoon.hoon`.

```hoon
++  key                                               ::  set of keys
  =<  $
  ~/  %key
  =+  b=`(set _?>(?=(^ a) p.n.a))`~
  |.  ^+  b
  ?~  a   b
  $(a r.a, b $(a l.a, b (~(put in b) p.n.a)))
::
++  run                                               ::  apply gate to values
  ~/  %run
  |*  b=gate
  |-
  ?~  a  a
  [n=[p=p.n.a q=(b q.n.a)] l=$(a l.a) r=$(a r.a)]
::
++  any                                               ::  logical OR
  ~/  %any
  |*  b=$-(* ?)
  |-  ^-  ?
  ?~  a
    |
  ?|((b q.n.a) $(a l.a) $(a r.a))
```

All three go through the nodes in pre-order: the root, then the left
subtree, then the right subtree.  `+key:by` puts each key into its set in that
order, `+run:by` slams the gate on the root's value before it maps the
subtrees, and `+any:by` stops at the first value in that order on which the
gate says yes.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

abbrev InIn (mug : Noun → Nat) (c : Noun) : Prop :=
  slot? in.axis c = some in.arm ∧ GorIn mug c ∧ MorIn mug c

/-! ## `+key:by` -/

/-- `+key:by` with the set `b` so far, as the Nock computes it. -/
def keyF (mug : Noun → Nat) : Noun → Noun → Option Noun
  | Noun.atom 0, b => some b
  | Noun.cell (Noun.cell p _) (Noun.cell l r), b =>
    match putInF mug p b with
    | some b1 =>
      match keyF mug l b1 with
      | some b2 => keyF mug r b2
      | none => none
    | none => none
  | _, _ => none

theorem key_arm (d : Noun) :
    nock d by.key.arm = nock (C by.key.battery (C (A 0) d)) by.key.battery := by
  nock_open by.key.arm; simp only [nock_exec]

theorem key_loop {mug : Noun → Nat} (ctx : Noun) (hc : InIn mug ctx) (B : Noun) :
    ∀ (a b out : Noun), keyF mug a b = some out →
      nock (C by.key.battery (C b (C B (C a ctx)))) by.key.battery = some out := by
  intro a b
  obtain ⟨hin, hgo, hmo⟩ := hc
  have hput := put_in_gate (mug := mug) ctx ⟨hgo, hmo⟩
  fun_induction keyF mug a b
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.key.battery
       simp [nock_exec, *]
       done)
    | (nock_open by.key.battery
       simp [nock_exec, in_arm, put_in_arm, *])

theorem keyF_spec {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) : ∀ b, IsSet mug b →
    ∃ out, keyF mug a b = some out ∧ IsSet mug out ∧
      ∀ k, Has out k ↔ Has b k ∨ ∃ v, Get a k v := by
  induction h with
  | nil => intro b hb; exact ⟨b, rfl, hb, fun k => by simp [Get_atom]⟩
  | @node p q l r hl hr hL hR ihl ihr =>
    intro b hb
    obtain ⟨b1, h1, hb1, hh1⟩ := putInF_spec mug b p hb
    obtain ⟨b2, h2, hb2, hh2⟩ := ihl b1 hb1
    obtain ⟨b3, h3, hb3, hh3⟩ := ihr b2 hb2
    refine ⟨b3, by simp [keyF, h1, h2, h3], hb3, fun k => ?_⟩
    rw [hh3, hh2, hh1]
    constructor
    · rintro (((rfl | h) | ⟨v, h⟩) | ⟨v, h⟩)
      · exact Or.inr ⟨q, Get.here⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, Get.left h⟩
      · exact Or.inr ⟨v, Get.right h⟩
    · rintro (h | ⟨v, h⟩)
      · exact Or.inl (Or.inl (Or.inr h))
      · rw [Get_node] at h
        rcases h with ⟨rfl, _⟩ | h | h
        · exact Or.inl (Or.inl (Or.inl rfl))
        · exact Or.inl (Or.inr ⟨v, h⟩)
        · exact Or.inr ⟨v, h⟩

/-- `~(key by a)` on a map: a set whose keys are exactly the keys of `a`. -/
theorem key_by {mug : Noun → Nat} (ctx : Noun) (hc : InIn mug ctx) (a : Noun) (h : IsMap mug a) :
    ∃ out, Eval (C by.battery (C a ctx)) by.key.arm out ∧ IsSet mug out ∧
      ∀ k, Has out k ↔ ∃ v, Get a k v := by
  obtain ⟨out, hk, hs, hh⟩ := keyF_spec h (A 0) IsMap.nil
  refine ⟨out, eval_of_nock ?_, hs, fun k => ?_⟩
  · rw [key_arm, key_loop ctx hc by.battery a (A 0) out hk]
  · rw [hh]
    constructor
    · rintro (h | h)
      · unfold Has at h; simp at h; exact absurd h Get_atom
      · exact h
    · exact Or.inr

/-! ## `+run:by` -/

/-- `+run:by` with the gate `f` on the values. -/
def runByF (f : Noun → Noun) : Noun → Option Noun
  | Noun.atom 0 => some (A 0)
  | Noun.cell (Noun.cell p q) (Noun.cell l r) =>
    match runByF f l with
    | some l' =>
      match runByF f r with
      | some r' => some (C (C p (f q)) (C l' r'))
      | none => none
    | none => none
  | _ => none

theorem run_by_loop (B ctx fp fs fc : Noun) (f : Noun → Noun)
    (hf : ∀ x, nock (C fp (C x fc)) fp = some (f x)) :
    ∀ (a out : Noun), runByF f a = some out →
      nock (C by.run.loop (C by.run.battery (C (C fp (C fs fc)) (C B (C a ctx))))) by.run.loop
        = some out := by
  intro a
  fun_induction runByF f a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.run.loop
       simp [nock_exec, *]
       done)
    | (nock_open by.run.loop
       simp [nock_exec, *])

theorem runByF_spec (f : Noun → Noun) {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) :
    ∃ out, runByF f a = some out ∧ IsMap mug out ∧
      ∀ k w, Get out k w ↔ ∃ v, Get a k v ∧ w = f v := by
  induction h with
  | nil => exact ⟨A 0, rfl, IsMap.nil, fun k w => by simp [Get_atom]⟩
  | @node p q l r hl hr hL hR ihl ihr =>
    obtain ⟨l', hl', hml, hgl⟩ := ihl
    obtain ⟨r', hr', hmr, hgr⟩ := ihr
    refine ⟨C (C p (f q)) (C l' r'), by simp [runByF, hl', hr'], ?_, fun k w => ?_⟩
    · refine IsMap.node hml hmr (fun k w hk => ?_) (fun k w hk => ?_)
      · obtain ⟨v, hv, _⟩ := (hgl k w).1 hk; exact hL k v hv
      · obtain ⟨v, hv, _⟩ := (hgr k w).1 hk; exact hR k v hv
    · rw [Get_node, hgl, hgr]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
        · exact ⟨q, Get.here, rfl⟩
        · exact ⟨v, Get.left hv, rfl⟩
        · exact ⟨v, Get.right hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        rw [Get_node] at hv
        rcases hv with ⟨rfl, rfl⟩ | hv | hv
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
        · exact Or.inr (Or.inr ⟨v, hv, rfl⟩)

/-- `+run:by` on a map with a gate that maps each value `v` to `f v`: the same
keys, the values mapped. -/
theorem run_by {mug : Noun → Nat} (ctx fp fs fc : Noun) (f : Noun → Noun)
    (hf : ∀ x, nock (C fp (C x fc)) fp = some (f x)) (a : Noun) (h : IsMap mug a) :
    ∃ out,
      Eval (C by.run.loop (C by.run.battery (C (C fp (C fs fc)) (C by.battery (C a ctx)))))
        by.run.loop out ∧
      IsMap mug out ∧ ∀ k w, Get out k w ↔ ∃ v, Get a k v ∧ w = f v := by
  obtain ⟨out, ho, hm, hg⟩ := runByF_spec f h
  exact ⟨out, eval_of_nock (run_by_loop by.battery ctx fp fs fc f hf a out ho), hm, hg⟩

/-! ## `+any:by` -/

/-- `+any:by` with the test `g` on the values. -/
def anyByF (g : Noun → Bool) : Noun → Option Bool
  | Noun.atom 0 => some false
  | Noun.cell (Noun.cell _ q) (Noun.cell l r) =>
    if g q then some true
    else
      match anyByF g l with
      | some true => some true
      | some false => anyByF g r
      | none => none
  | _ => none

theorem any_by_loop (B ctx fp fs fc : Noun) (g : Noun → Bool)
    (hg : ∀ x, nock (C fp (C x fc)) fp = some (loob (g x))) :
    ∀ (a : Noun) (t : Bool), anyByF g a = some t →
      nock (C by.any.loop (C by.any.battery (C (C fp (C fs fc)) (C B (C a ctx))))) by.any.loop
        = some (loob t) := by
  intro a
  fun_induction anyByF g a
  all_goals intro t h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.any.loop
       simp [nock_exec, *]
       done)
    | (nock_open by.any.loop
       cases t <;> simp [nock_exec, *])

theorem anyByF_spec (g : Noun → Bool) {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) :
    ∃ t, anyByF g a = some t ∧ (t = true ↔ ∃ k v, Get a k v ∧ g v = true) := by
  induction h with
  | nil => exact ⟨false, rfl, by simp [Get_atom]⟩
  | @node p q l r hl hr hL hR ihl ihr =>
    obtain ⟨tl, hl', htl⟩ := ihl
    obtain ⟨tr, hr', htr⟩ := ihr
    by_cases hq : g q = true
    · refine ⟨true, by simp [anyByF, hq], by simp; exact ⟨p, q, Get.here, hq⟩⟩
    · have hq' : g q = false := by simpa using hq
      cases tl with
      | true =>
        refine ⟨true, by simp [anyByF, hq', hl'], ?_⟩
        obtain ⟨k, v, hk, hv⟩ := htl.1 rfl
        simp; exact ⟨k, v, Get.left hk, hv⟩
      | false =>
        refine ⟨tr, by simp [anyByF, hq', hl', hr'], ?_⟩
        rw [htr]
        constructor
        · rintro ⟨k, v, hk, hv⟩; exact ⟨k, v, Get.right hk, hv⟩
        · rintro ⟨k, v, hk, hv⟩
          rw [Get_node] at hk
          rcases hk with ⟨rfl, rfl⟩ | hk | hk
          · exact absurd hv hq
          · exact absurd (htl.2 ⟨k, v, hk, hv⟩) (by simp)
          · exact ⟨k, v, hk, hv⟩

end Hoon
end Formalization

end
