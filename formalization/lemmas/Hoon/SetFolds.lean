module

public import lemmas.Hoon.TapIn
public import lemmas.Hoon.DelBy
public import lemmas.Hoon.MapFolds
import all lemmas.Pill.Arm.In

/-!
`+gas:in`, `+any:in`, `+run:in` and `+del:in` of the pill's `hoon.hoon`.

```hoon
++  gas                                               ::  concatenate
  ~/  %gas
  |=  b=(list _?>(?=(^ a) n.a))
  |-  ^+  a
  ?~  b
    a
  $(b t.b, a (put i.b))
::
++  any                                               ::  logical OR
  ~/  %any
  |*  b=$-(* ?)
  |-  ^-  ?
  ?~  a
    |
  ?|((b n.a) $(a l.a) $(a r.a))
::
++  run                                               ::  apply gate to values
  ~/  %run
  |*  b=gate
  =+  c=`(set _?>(?=(^ a) (b n.a)))`~
  |-  ?~  a  c
  =.  c  (~(put in c) (b n.a))
  =.  c  $(a l.a, c c)
  $(a r.a, c c)
```

`+del:in` is `+del:by` with keys in place of pairs.  `+any:in` and `+run:in`
go through the keys in pre-order (root, left subtree, right subtree);
`+run:in` puts the image of each key into a new set in that order.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

theorem has_node {n l r k : Noun} : Has (C n (C l r)) k ↔ k = n ∨ Has l k ∨ Has r k := by
  unfold Has
  rw [toMap_node, Get_node]
  simp

theorem not_has_atom {m : Nat} {k : Noun} : ¬ Has (A m) k := by
  unfold Has; simp; exact Get_atom

/-! ## `+gas:in` -/

/-- `+gas:in`: `putInF` of each key of the list, in order. -/
def gasInF (mug : Noun → Nat) : Noun → List Noun → Option Noun
  | a, [] => some a
  | a, k :: rest =>
    match putInF mug k a with
    | some a' => gasInF mug a' rest
    | none => none

@[nock_exec] theorem gas_in_arm (d : Noun) :
    nock d in.gas.arm = some (C in.gas.battery (C (A 0) d)) := by
  nock_open in.gas.arm; simp only [nock_exec]

theorem gas_in_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ (l : List Noun) (a out : Noun), gasInF mug a l = some out →
      nock (C in.gas.loop (C in.gas.battery (C (listN l) (C in.battery (C a ctx))))) in.gas.loop
        = some out := by
  intro l
  induction l with
  | nil =>
    intro a out h
    cases h
    nock_open in.gas.loop
    simp [nock_exec]
  | cons k rest ih =>
    intro a out h
    simp only [gasInF] at h
    cases hp : putInF mug k a with
    | none => rw [hp] at h; cases h
    | some a' =>
      rw [hp] at h
      nock_open in.gas.loop
      simp [nock_exec, put_in_arm, put_in_gate ctx hc k a a' hp, ih a' out h]

theorem gasInF_spec {mug : Noun → Nat} : ∀ (l : List Noun) (a : Noun), IsSet mug a →
    ∃ out, gasInF mug a l = some out ∧ IsSet mug out ∧ ∀ k, Has out k ↔ k ∈ l ∨ Has a k := by
  intro l
  induction l with
  | nil => intro a h; exact ⟨a, rfl, h, fun k => by simp⟩
  | cons k0 rest ih =>
    intro a h
    obtain ⟨a', hp, hs', hh'⟩ := putInF_spec mug a k0 h
    obtain ⟨out, ho, hs, hh⟩ := ih a' hs'
    refine ⟨out, by simp [gasInF, hp, ho], hs, fun k => ?_⟩
    rw [hh, hh']
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- `+gas:in` on a set: the keys of the set and those of the list. -/
theorem gas_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a : Noun)
    (l : List Noun) (h : IsSet mug a) :
    ∃ out,
      Eval (C in.gas.loop (C in.gas.battery (C (listN l) (C in.battery (C a ctx))))) in.gas.loop
        out ∧
      IsSet mug out ∧ ∀ k, Has out k ↔ k ∈ l ∨ Has a k := by
  obtain ⟨out, ho, hs, hh⟩ := gasInF_spec l a h
  exact ⟨out, eval_of_nock (gas_in_loop ctx hc l a out ho), hs, hh⟩

/-! ## `+any:in` -/

/-- `+any:in` with the test `g` on the keys. -/
def anyInF (g : Noun → Bool) : Noun → Option Bool
  | Noun.atom 0 => some false
  | Noun.cell n (Noun.cell l r) =>
    if g n then some true
    else
      match anyInF g l with
      | some true => some true
      | some false => anyInF g r
      | none => none
  | _ => none

theorem any_in_loop (B ctx fp fs fc : Noun) (g : Noun → Bool)
    (hg : ∀ x, nock (C fp (C x fc)) fp = some (loob (g x))) :
    ∀ (a : Noun) (t : Bool), anyInF g a = some t →
      nock (C in.any.loop (C in.any.battery (C (C fp (C fs fc)) (C B (C a ctx))))) in.any.loop
        = some (loob t) := by
  intro a
  fun_induction anyInF g a
  all_goals intro t h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open in.any.loop
       simp [nock_exec, *]
       done)
    | (nock_open in.any.loop
       cases t <;> simp [nock_exec, *])

theorem anyInF_spec (g : Noun → Bool) {a : Noun} (h : Tree a) :
    ∃ t, anyInF g a = some t ∧ (t = true ↔ ∃ k, k ∈ preorder a ∧ g k = true) := by
  induction h with
  | nil => exact ⟨false, rfl, by simp [preorder]⟩
  | @node n l r _ _ ihl ihr =>
    obtain ⟨tl, hl', htl⟩ := ihl
    obtain ⟨tr, hr', htr⟩ := ihr
    by_cases hq : g n = true
    · exact ⟨true, by simp [anyInF, hq], by simp [preorder]; exact Or.inl hq⟩
    · have hq' : g n = false := by simpa using hq
      cases tl with
      | true =>
        refine ⟨true, by simp [anyInF, hq', hl'], ?_⟩
        obtain ⟨k, hk, hv⟩ := htl.1 rfl
        simp [preorder]; exact Or.inr ⟨k, Or.inl hk, hv⟩
      | false =>
        refine ⟨tr, by simp [anyInF, hq', hl', hr'], ?_⟩
        rw [htr]
        simp only [preorder, List.mem_cons, List.mem_append]
        constructor
        · rintro ⟨k, hk, hv⟩; exact ⟨k, Or.inr (Or.inr hk), hv⟩
        · rintro ⟨k, (rfl | hk | hk), hv⟩
          · exact absurd hv hq
          · exact absurd (htl.2 ⟨k, hk, hv⟩) (by simp)
          · exact ⟨k, hk, hv⟩

/-! ## `+run:in` -/

/-- `+run:in` with the gate `f`, into the set `c`. -/
def runInF (mug : Noun → Nat) (f : Noun → Noun) : Noun → Noun → Option Noun
  | Noun.atom 0, c => some c
  | Noun.cell n (Noun.cell l r), c =>
    match putInF mug (f n) c with
    | some c1 =>
      match runInF mug f l c1 with
      | some c2 => runInF mug f r c2
      | none => none
    | none => none
  | _, _ => none

theorem run_in_loop {mug : Noun → Nat} (ctx : Noun) (hc : InIn mug ctx) (fp fs fc : Noun)
    (f : Noun → Noun) (hf : ∀ x, nock (C fp (C x fc)) fp = some (f x)) :
    ∀ (a c out : Noun), runInF mug f a c = some out →
      nock (C in.run.loop (C c (C in.run.battery (C (C fp (C fs fc)) (C in.battery (C a ctx))))))
        in.run.loop = some out := by
  intro a c
  obtain ⟨hin, hgo, hmo⟩ := hc
  have hput := put_in_gate (mug := mug) ctx ⟨hgo, hmo⟩
  fun_induction runInF mug f a c
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open in.run.loop
       simp [nock_exec, *]
       done)
    | (nock_open in.run.loop
       simp [nock_exec, in_arm, put_in_arm, *])

theorem runInF_spec {mug : Noun → Nat} (f : Noun → Noun) {a : Noun} (h : Tree a) :
    ∀ c, IsSet mug c →
      ∃ out, runInF mug f a c = some out ∧ IsSet mug out ∧
        ∀ x, Has out x ↔ Has c x ∨ ∃ y, y ∈ preorder a ∧ x = f y := by
  induction h with
  | nil => intro c hc; exact ⟨c, rfl, hc, fun x => by simp [preorder]⟩
  | @node n l r _ _ ihl ihr =>
    intro c hc
    obtain ⟨c1, h1, hs1, hh1⟩ := putInF_spec mug c (f n) hc
    obtain ⟨c2, h2, hs2, hh2⟩ := ihl c1 hs1
    obtain ⟨c3, h3, hs3, hh3⟩ := ihr c2 hs2
    refine ⟨c3, by simp [runInF, h1, h2, h3], hs3, fun x => ?_⟩
    rw [hh3, hh2, hh1]
    simp only [preorder, List.mem_cons, List.mem_append]
    constructor
    · rintro (((rfl | h) | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
      · exact Or.inr ⟨n, Or.inl rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, Or.inr (Or.inl hy), rfl⟩
      · exact Or.inr ⟨y, Or.inr (Or.inr hy), rfl⟩
    · rintro (h | ⟨y, (rfl | hy | hy), rfl⟩)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inr ⟨y, hy, rfl⟩)
      · exact Or.inr ⟨y, hy, rfl⟩

/-! ## `+del:in` -/

/-- The merge of `+del:in`. -/
def mergeInF (mug : Noun → Nat) (l r : Noun) : Option Noun :=
  match l, r with
  | Noun.atom 0, r => some r
  | Noun.cell n (Noun.cell ll lr), Noun.atom 0 => some (C n (C ll lr))
  | Noun.cell n (Noun.cell ll lr), Noun.cell n' (Noun.cell rl rr) =>
    if morF mug n n' then
      match mergeInF mug lr (C n' (C rl rr)) with
      | some x => some (C n (C ll x))
      | none => none
    else
      match mergeInF mug (C n (C ll lr)) rl with
      | some x => some (C n' (C x rr))
      | none => none
  | _, _ => none
termination_by sizeOf l + sizeOf r
decreasing_by all_goals simp_wf; omega

/-- `+del:in`: delete the key `b` from the set `a`. -/
def delInF (mug : Noun → Nat) (b : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (A 0)
  | Noun.cell n (Noun.cell l r) =>
    if b = n then mergeInF mug l r
    else if gorF mug b n then
      match delInF mug b l with
      | some x => some (C n (C x r))
      | none => none
    else
      match delInF mug b r with
      | some x => some (C n (C l x))
      | none => none
  | _ => none

@[nock_exec] theorem del_in_arm (d : Noun) :
    nock d in.del.arm = some (C in.del.battery (C (A 0) d)) := by
  nock_open in.del.arm; simp only [nock_exec]

theorem merge_in_loop {mug : Noun → Nat} (ctx : Noun) (hc : MorIn mug ctx) (b n B : Noun) :
    ∀ l r out, mergeInF mug l r = some out →
      nock (C in.del.loop0 (C in.del.loop1 (C in.del.battery (C b (C B (C (C n (C l r)) ctx))))))
        in.del.loop0 = some out := by
  intro l r
  have hmor := mor_gate (mug := mug) ctx hc.2
  have hm := hc.1
  fun_induction mergeInF mug l r
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open in.del.loop0
       simp [nock_exec, *]
       done)
    | (nock_open in.del.loop0
       simp [nock_exec, *])

theorem del_in_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (b a : Noun) :
    ∀ out, delInF mug b a = some out →
      nock (C in.del.loop1 (C in.del.battery (C b (C in.battery (C a ctx))))) in.del.loop1
        = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hg := hc.1.1
  have hmerge := merge_in_loop ctx hc.2 b
  fun_induction delInF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open in.del.loop1
       simp [nock_exec, *]
       done)
    | (nock_open in.del.loop1
       simp [nock_exec, *])

theorem del_in_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (b a out : Noun) (h : delInF mug b a = some out) :
    nock (C in.del.battery (C b (C in.battery (C a ctx)))) in.del.battery = some out := by
  nock_open in.del.battery
  simp only [nock_exec, del_in_loop ctx hc b a out h]

theorem mergeF_toMap {mug : Noun → Nat} : ∀ (n : Nat) (l r : Noun), sizeOf l + sizeOf r < n →
    IsSet mug l → IsSet mug r →
    mergeF mug (toMap l) (toMap r) = (mergeInF mug l r).map toMap := by
  intro n
  induction n with
  | zero => intro l r h; omega
  | succ n ih =>
    intro l r hs hl hr
    have tl := Tree.of_isSet hl
    have tr := Tree.of_isSet hr
    cases tl with
    | nil => simp [mergeF, mergeInF]
    | @node m ll lr tll tlr =>
      cases tr with
      | nil => simp [mergeF, mergeInF]
      | @node m' rl rr trl trr =>
        have hl' := hl
        have hr' := hr
        unfold IsSet at hl' hr'
        simp only [toMap_node] at hl' hr'
        cases hl' with
        | node hll hlr _ _ =>
          cases hr' with
          | node hrl hrr _ _ =>
            by_cases mm : morF mug m m' = true
            · have e := ih lr (C m' (C rl rr)) (by simp at hs ⊢; omega) hlr hr
              simp only [toMap_node] at e
              rw [toMap_node, toMap_node]
              simp only [mergeF, mergeInF, mm, if_true]
              rw [e]
              cases mergeInF mug lr (C m' (C rl rr)) <;> simp
            · have e := ih (C m (C ll lr)) rl (by simp at hs ⊢; omega) hl hrl
              simp only [toMap_node] at e
              rw [toMap_node, toMap_node]
              simp only [mergeF, mergeInF, mm]
              rw [e]
              cases mergeInF mug (C m (C ll lr)) rl <;> simp

theorem delF_toMap {mug : Noun → Nat} (b : Noun) : ∀ (a : Noun), IsSet mug a →
    delF mug b (toMap a) = (delInF mug b a).map toMap := by
  intro a ha
  have ta := Tree.of_isSet ha
  induction ta with
  | nil => rfl
  | @node m l r tl tr ihl ihr =>
    have ha' := ha
    unfold IsSet at ha'
    simp only [toMap_node] at ha'
    cases ha' with
    | node hl hr _ _ =>
      rw [toMap_node]
      by_cases e : b = m
      · simp only [delF, delInF, e, if_true]
        exact mergeF_toMap _ l r (Nat.lt_succ_self _) hl hr
      · by_cases g : gorF mug b m = true
        · simp only [delF, delInF, e, g, if_true, if_false]
          rw [ihl hl]
          cases delInF mug b l <;> simp
        · simp only [delF, delInF, e, g, if_false]
          rw [ihr hr]
          cases delInF mug b r <;> simp

/-- `+del:in` on a set deletes the key and keeps the invariant. -/
theorem del_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a k : Noun)
    (h : IsSet mug a) :
    ∃ out,
      Eval (C in.del.battery (C k (C in.battery (C a ctx)))) in.del.battery out ∧
      IsSet mug out ∧ ∀ k', Has out k' ↔ k' ≠ k ∧ Has a k' := by
  obtain ⟨out', hd, hm, hg⟩ := delF_spec k h
  rw [delF_toMap k a h] at hd
  cases hx : delInF mug k a with
  | none => rw [hx] at hd; cases hd
  | some out =>
    rw [hx] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    exact ⟨out, eval_of_nock (del_in_gate ctx hc k a out hx), hm, fun k' => hg k' (A 0)⟩

end Hoon
end Formalization

end
