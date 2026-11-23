import lemmas.Hoon.Maps

/-!
`+put:in` and `+has:in` of the pill's `hoon.hoon`: insertion into and lookup
in a set.

```hoon
++  has
  ~/  %has
  |*  b=*
  ^-  ?
  %.  [~ b]
  |=  b=(unit _?>(?=(^ a) n.a))
  =>  .(b ?>(?=(^ b) u.b))
  |-  ^-  ?
  ?~  a
    |
  ?:  =(b n.a)
    &
  ?:  (gor b n.a)
    $(a l.a)
  $(a r.a)
::
++  put
  ~/  %put
  |*  b=*
  |-  ^+  a
  ?~  a
    [b ~ ~]
  ?:  =(b n.a)
    a
  ?:  (gor b n.a)
    =+  c=$(a l.a)
    ?>  ?=(^ c)
    ?:  (mor n.a n.c)
      a(l c)
    c(r a(l r.c))
  =+  c=$(a r.a)
  ?>  ?=(^ c)
  ?:  (mor n.a n.c)
    a(r c)
  c(l a(r l.c))
```

A set is the treap of `+by` with keys only: `~` or `[n l r]`.  Rather than
redo `Treap.lean` for sets, a set `a` is read as the map `toMap a` with the
same keys and the value `~`: `IsSet` is `IsMap` of that map, and `Has a k` is
`Get (toMap a) k ~`.  The models `putInF` and `hasInF` agree with `putF` and
`getF` on that map, which carries the results of `Treap.lean` over.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## Sets as maps -/

/-- The map with the keys of the set `a` and the value `~` under each. -/
def toMap : Noun → Noun
  | Noun.cell n (Noun.cell l r) => C (C n (A 0)) (C (toMap l) (toMap r))
  | x => x

@[simp] theorem toMap_atom (k : Nat) : toMap (A k) = A k := by simp [toMap]

@[simp] theorem toMap_node (n l r : Noun) :
    toMap (C n (C l r)) = C (C n (A 0)) (C (toMap l) (toMap r)) := by
  simp [toMap]

@[simp] theorem toMap_cell_atom (n : Noun) (k : Nat) : toMap (C n (A k)) = C n (A k) := by
  simp [toMap]

/-- The invariant of `+in` sets: the map with the same keys satisfies `IsMap`. -/
def IsSet (mug : Noun → Nat) (a : Noun) : Prop := IsMap mug (toMap a)

/-- The set `a` holds the key `k`. -/
def Has (a k : Noun) : Prop := Get (toMap a) k (A 0)

/-- A map node of `toMap a` comes from a set node. -/
theorem toMap_eq_node {a p q l r : Noun} (h : toMap a = C (C p q) (C l r)) :
    ∃ l' r', a = C p (C l' r') ∧ q = A 0 ∧ l = toMap l' ∧ r = toMap r' := by
  cases a with
  | atom _ => simp at h
  | cell n rest =>
    cases rest with
    | atom _ => simp at h
    | cell l' r' =>
      simp only [toMap_node, Noun.cell.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
      exact ⟨l', r', rfl, rfl, rfl, rfl⟩

/-- Every value of the map of a set is `~`. -/
theorem Get_toMap {a k v : Noun} (h : Get (toMap a) k v) : v = A 0 := by
  generalize hm : toMap a = m at h
  induction h generalizing a with
  | here =>
    obtain ⟨_, _, _, rfl, _, _⟩ := toMap_eq_node hm
    rfl
  | left _ ih =>
    obtain ⟨l', _, _, _, rfl, _⟩ := toMap_eq_node hm
    exact ih rfl
  | right _ ih =>
    obtain ⟨_, r', _, _, _, rfl⟩ := toMap_eq_node hm
    exact ih rfl

/-! ## The models -/

/-- `+put:in`: insert the key `b` into the treap `a`. -/
def putInF (mug : Noun → Nat) (b : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (C b (C (A 0) (A 0)))
  | Noun.cell n (Noun.cell l r) =>
    if b = n then some (C n (C l r))
    else if gorF mug b n then
      match putInF mug b l with
      | some (Noun.cell dn (Noun.cell dl dr)) =>
        if morF mug n dn then some (C n (C (C dn (C dl dr)) r))
        else some (C dn (C dl (C n (C dr r))))
      | _ => none
    else
      match putInF mug b r with
      | some (Noun.cell dn (Noun.cell dl dr)) =>
        if morF mug n dn then some (C n (C l (C dn (C dl dr))))
        else some (C dn (C (C n (C l dl)) dr))
      | _ => none
  | _ => none

/-- `+has:in`: whether the treap `a` holds the key `b`. -/
def hasInF (mug : Noun → Nat) (b : Noun) : Noun → Option Bool
  | Noun.atom 0 => some false
  | Noun.cell n (Noun.cell l r) =>
    if b = n then some true
    else if gorF mug b n then hasInF mug b l else hasInF mug b r
  | _ => none

/-! ## The models agree with the map models -/

theorem putF_toMap (mug : Noun → Nat) (b a : Noun) :
    putF mug b (A 0) (toMap a) = (putInF mug b a).map toMap := by
  fun_induction putInF mug b a with
  | case1 => simp [putF]
  | case2 l r => simp [putF]
  | case3 n l r e g dn dl dr hput m ih =>
    rw [hput] at ih
    simp only [Option.map_some, toMap_node] at ih
    simp [putF, e, g, ih, m]
  | case4 n l r e g dn dl dr hput m ih =>
    rw [hput] at ih
    simp only [Option.map_some, toMap_node] at ih
    simp [putF, e, g, ih, m]
  | case5 n l r e g hx ih =>
    simp only [toMap_node, putF, e, ↓reduceIte, g, ih, Option.map_none]
    cases hp : putInF mug b l with
    | none => simp
    | some x =>
      cases x with
      | atom _ => simp
      | cell dn rest =>
        cases rest with
        | atom _ => simp
        | cell dl dr => exact absurd hp (hx dn dl dr)
  | case6 n l r e g dn dl dr hput m ih =>
    rw [hput] at ih
    simp only [Option.map_some, toMap_node] at ih
    simp [putF, e, g, ih, m]
  | case7 n l r e g dn dl dr hput m ih =>
    rw [hput] at ih
    simp only [Option.map_some, toMap_node] at ih
    simp [putF, e, g, ih, m]
  | case8 n l r e g hx ih =>
    simp only [toMap_node, putF, e, ↓reduceIte, g, ih, Option.map_none]
    cases hp : putInF mug b r with
    | none => simp
    | some x =>
      cases x with
      | atom _ => simp
      | cell dn rest =>
        cases rest with
        | atom _ => simp
        | cell dl dr => exact absurd hp (hx dn dl dr)
  | case9 x h0 hn =>
    cases x with
    | atom k =>
      cases k with
      | zero => exact absurd rfl h0
      | succ k => rfl
    | cell n rest =>
      cases rest with
      | atom _ => cases n <;> rfl
      | cell l r => exact absurd rfl (hn n l r)

theorem getF_toMap (mug : Noun → Nat) (b a : Noun) :
    getF mug b (toMap a) = (hasInF mug b a).map (fun t => if t then C (A 0) (A 0) else A 0) := by
  fun_induction hasInF mug b a with
  | case1 => simp [getF]
  | case2 l r => simp [getF]
  | case3 n l r e g ih => simp [getF, e, g, ih]
  | case4 n l r e g ih => simp [getF, e, g, ih]
  | case5 x h0 hn =>
    cases x with
    | atom k =>
      cases k with
      | zero => exact absurd rfl h0
      | succ k => rfl
    | cell n rest =>
      cases rest with
      | atom _ => cases n <;> rfl
      | cell l r => exact absurd rfl (hn n l r)

/-- `putInF` on a set succeeds, returns a set, and the keys of the result are
the old keys and `k`. -/
theorem putInF_spec (mug : Noun → Nat) (a k : Noun) (h : IsSet mug a) :
    ∃ out, putInF mug k a = some out ∧ IsSet mug out ∧
      ∀ k', Has out k' ↔ k' = k ∨ Has a k' := by
  obtain ⟨out, hput, hmap, hget⟩ := putF_spec mug (toMap a) k (A 0) h
  rw [putF_toMap] at hput
  cases hp : putInF mug k a with
  | none => rw [hp] at hput; cases hput
  | some out' =>
    rw [hp] at hput
    simp only [Option.map_some, Option.some.injEq] at hput
    subst hput
    refine ⟨out', rfl, hmap, fun k' => ?_⟩
    unfold Has
    rw [hget]
    by_cases e : k' = k
    · simp [e]
    · simp [e]

/-- `hasInF` on a set tells whether the set holds the key. -/
theorem hasInF_spec (mug : Noun → Nat) (a k : Noun) (h : IsSet mug a) :
    ∃ t, hasInF mug k a = some t ∧ (t = true ↔ Has a k) := by
  by_cases hk : Has a k
  · have hg := getF_some h hk
    rw [getF_toMap] at hg
    cases ht : hasInF mug k a with
    | none => rw [ht] at hg; cases hg
    | some t =>
      rw [ht] at hg
      cases t with
      | true => exact ⟨true, rfl, by simp [hk]⟩
      | false => simp at hg
  · have hn : ∀ v, ¬ Get (toMap a) k v := by
      intro v hv
      rw [Get_toMap hv] at hv
      exact hk hv
    have hg := getF_none h hn
    rw [getF_toMap] at hg
    cases ht : hasInF mug k a with
    | none => rw [ht] at hg; cases hg
    | some t =>
      rw [ht] at hg
      cases t with
      | true => simp at hg
      | false => exact ⟨false, rfl, by simp [hk]⟩

/-! ## The Nock -/

@[nock_exec] theorem in_arm (c : Noun) : nock c in.arm = some (C in.battery (C (A 0) c)) := by
  nock_open in.arm; simp only [nock_exec]

@[nock_exec] theorem put_in_arm (d : Noun) :
    nock d in.put.arm = some (C in.put.battery (C (A 0) d)) := by
  nock_open in.put.arm; simp only [nock_exec]

@[nock_exec] theorem has_in_arm (d : Noun) :
    nock d in.has.arm = some (C in.has.battery (C (A 0) d)) := by
  nock_open in.has.arm; simp only [nock_exec]

/-- The loop of `+put:in` in the door whose set is `a`, with sample `b`,
computes the model. -/
theorem put_in_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (b a : Noun) :
    ∀ out, putInF mug b a = some out →
      nock (C in.put.loop (C in.put.battery (C b (C in.battery (C a ctx))))) in.put.loop
        = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hmor := mor_gate (mug := mug) ctx hc.2.2
  obtain ⟨⟨hg, _⟩, ⟨hm, _⟩⟩ := hc
  fun_induction putInF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals
    cases h
    nock_open in.put.loop
    simp [nock_exec, gor_arm, mor_arm, *]

/-- The gate `put` of the door `in` with set `a`, slammed on `b`. -/
theorem put_in_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (b a out : Noun) (h : putInF mug b a = some out) :
    nock (C in.put.battery (C b (C in.battery (C a ctx)))) in.put.battery = some out := by
  nock_open in.put.battery
  simp only [nock_exec, put_in_loop ctx hc b a out h]

/-- The loop of `+has:in` in the door whose set is `a`, with sample `b`,
computes the model. -/
theorem has_in_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (b a : Noun) :
    ∀ out, hasInF mug b a = some out →
      nock (C in.has.loop (C in.has.gate (C b (C in.has.battery (C b (C in.battery (C a ctx)))))))
        in.has.loop = some (loob out) := by
  have hgor := gor_gate (mug := mug) ctx hc.2
  have hg := hc.1
  fun_induction hasInF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open in.has.loop
       simp [nock_exec, *]
       done)
    | (nock_open in.has.loop
       simp [nock_exec, gor_arm, *])

/-- The gate `has` of the door `in` with set `a`, slammed on `b`. -/
theorem has_in_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx)
    (b a : Noun) (out : Bool) (h : hasInF mug b a = some out) :
    nock (C in.has.battery (C b (C in.battery (C a ctx)))) in.has.battery = some (loob out) := by
  nock_open in.has.battery
  simp only [nock_exec]
  nock_open in.has.gate
  simp only [nock_exec, has_in_loop ctx hc b a out h]

/-! ## On a set -/

/-- `+put:in` on a set ends, its product is a set, and the product holds the
keys of `a` and `k`. -/
theorem put_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (a k : Noun) (h : IsSet mug a) :
    ∃ out,
      Eval (C in.put.battery (C k (C in.battery (C a ctx)))) in.put.battery out ∧
      IsSet mug out ∧ ∀ k', Has out k' ↔ k' = k ∨ Has a k' := by
  obtain ⟨out, hput, hset, hhas⟩ := putInF_spec mug a k h
  exact ⟨out, eval_of_nock (put_in_gate ctx hc k a out hput), hset, hhas⟩

/-- `+has:in` on a set: whether the set holds the key `k`. -/
theorem has_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (a k : Noun)
    (h : IsSet mug a) :
    ∃ t : Bool,
      Eval (C in.has.battery (C k (C in.battery (C a ctx)))) in.has.battery (loob t) ∧
      (t = true ↔ Has a k) := by
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mug a k h
  exact ⟨t, eval_of_nock (has_in_gate ctx hc k a t ht), hiff⟩

end Hoon
end Formalization
