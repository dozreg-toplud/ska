import lemmas.Hoon.DelBy
import lemmas.Hoon.Maps
import lemmas.Hoon.Mug
import lemmas.Ska.Types

/-!
# The treaps of `+by` as an instance of `HoonMap`

The interpreter model of `lemmas/Ska/Interp.lean` takes maps through the class
`HoonMap`.  This file gives the instance that the pill's Nock computes on:

* `Tr ν` is a treap whose keys are atoms and whose values are of type `ν`,
  laid out by `Tr.toNoun f` as Hoon lays out a `(map @ v)` whose values are
  laid out by `f`: `~` or `[[k v] l r]`.
* `Tr.get`, `Tr.put`, `Tr.del` (with `Tr.merge`) follow `getF`, `putF`,
  `delF` (with `mergeF`) of `lemmas/Hoon/`, which the pill's `+get:by`,
  `+put:by`, `+del:by` compute: `getF_toNoun`, `putF_toNoun`, `delF_toNoun`
  say that the noun models, on `toNoun f` of a treap, are `toNoun f` of these.
  The comparisons are `gorF mug` and `morF mug` on the keys, so the shape of a
  treap never depends on its values or on `f`.
* `TreapMap mug ν` is the treaps that satisfy `IsMap mug` under every layout of
  the values, and `instance : HoonMap (TreapMap mugF)` takes `mugF`, the
  `+mug` of the pill (`Hoon/Mug.lean`).  Its laws come from the specifications
  `putF_spec`, `delF_spec`, `getF_some`, `getF_none` of the noun models.

So `HoonMap.toNoun f m` is the noun that the Hoon holds for the map `m`, and
`HoonMap.get`, `put`, `del` are what `+get:by`, `+put:by` and `+del:by` do to
that noun.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel

/-- A treap with atom keys and values of type `ν`. -/
inductive Tr (ν : Type) where
  | nil : Tr ν
  | node (k : Nat) (v : ν) (l r : Tr ν) : Tr ν

namespace Tr

variable {ν : Type}

/-- The noun of a treap, the values laid out by `f`. -/
def toNoun (f : ν → Noun) : Tr ν → Noun
  | nil => A 0
  | node k v l r => C (C (A k) (f v)) (C (l.toNoun f) (r.toNoun f))

/-- `+get:by`. -/
def get (mug : Noun → Nat) (b : Nat) : Tr ν → Option ν
  | nil => none
  | node k v l r => if b = k then some v else if gorF mug (A b) (A k) then l.get mug b else r.get mug b

/-- `+put:by`. -/
def put (mug : Noun → Nat) (b : Nat) (c : ν) : Tr ν → Tr ν
  | nil => node b c nil nil
  | node p q l r =>
    if b = p then node b c l r
    else if gorF mug (A b) (A p) then
      match put mug b c l with
      | node dp dq dl dr =>
        if morF mug (A p) (A dp) then node p q (node dp dq dl dr) r
        else node dp dq dl (node p q dr r)
      | nil => nil
    else
      match put mug b c r with
      | node dp dq dl dr =>
        if morF mug (A p) (A dp) then node p q l (node dp dq dl dr)
        else node dp dq (node p q l dl) dr
      | nil => nil

/-- The size of a treap, the measure of `merge`. -/
def size : Tr ν → Nat
  | nil => 0
  | node _ _ l r => l.size + r.size + 1

/-- The merge of two treaps, by `+mor` at the roots, as `+del:by` makes it. -/
def merge (mug : Noun → Nat) : Tr ν → Tr ν → Tr ν
  | nil, r => r
  | node p q ll lr, nil => node p q ll lr
  | node p q ll lr, node p' q' rl rr =>
    if morF mug (A p) (A p') then node p q ll (merge mug lr (node p' q' rl rr))
    else node p' q' (merge mug (node p q ll lr) rl) rr
termination_by l r => l.size + r.size
decreasing_by all_goals simp only [size]; omega

/-- `+del:by`. -/
def del (mug : Noun → Nat) (b : Nat) : Tr ν → Tr ν
  | nil => nil
  | node p q l r =>
    if b = p then merge mug l r
    else if gorF mug (A b) (A p) then node p q (del mug b l) r else node p q l (del mug b r)

/-! ## The noun models on the noun of a treap -/

theorem getF_toNoun (mug : Noun → Nat) (f : ν → Noun) (b : Nat) :
    ∀ t : Tr ν, getF mug (A b) (t.toNoun f) = some (unitNoun f (t.get mug b))
  | nil => rfl
  | node k v l r => by
    have il := getF_toNoun mug f b l
    have ir := getF_toNoun mug f b r
    by_cases e : b = k
    · subst e; simp [toNoun, get, getF, unitNoun]
    · simp [toNoun, get, getF, e, il, ir]
      split <;> rfl

theorem put_node (mug : Noun → Nat) (b : Nat) (c : ν) :
    ∀ t : Tr ν, ∃ dp dq dl dr, t.put mug b c = node dp dq dl dr
  | nil => ⟨_, _, _, _, rfl⟩
  | node p q l r => by
    obtain ⟨dp, dq, dl, dr, hl⟩ := put_node mug b c l
    obtain ⟨ep, eq, el, er, hr⟩ := put_node mug b c r
    simp only [put]
    split
    · exact ⟨_, _, _, _, rfl⟩
    · split
      · simp only [hl]; split <;> exact ⟨_, _, _, _, rfl⟩
      · simp only [hr]; split <;> exact ⟨_, _, _, _, rfl⟩

theorem putF_toNoun (mug : Noun → Nat) (f : ν → Noun) (b : Nat) (c : ν) :
    ∀ t : Tr ν, putF mug (A b) (f c) (t.toNoun f) = some ((t.put mug b c).toNoun f)
  | nil => rfl
  | node p q l r => by
    have il := putF_toNoun mug f b c l
    have ir := putF_toNoun mug f b c r
    obtain ⟨dp, dq, dl, dr, hl⟩ := put_node mug b c l
    obtain ⟨ep, eq, el, er, hr⟩ := put_node mug b c r
    rw [hl] at il
    rw [hr] at ir
    by_cases e : b = p
    · subst e
      by_cases e' : f c = f q
      · simp [toNoun, put, putF, e']
      · simp [toNoun, put, putF, e']
    · by_cases g : gorF mug (A b) (A p) = true
      · simp only [toNoun] at il
        simp only [toNoun, put, putF, e, g, il, hl, Noun.atom.injEq, if_false, if_true]
        split <;> rfl
      · simp only [toNoun] at ir
        simp only [toNoun, put, putF, e, g, ir, hr, Noun.atom.injEq, if_false, Bool.false_eq_true]
        split <;> rfl

theorem mergeF_toNoun (mug : Noun → Nat) (f : ν → Noun) :
    ∀ (n : Nat) (l r : Tr ν), l.size + r.size < n →
    mergeF mug (l.toNoun f) (r.toNoun f) = some ((merge mug l r).toNoun f) := by
  intro n
  induction n with
  | zero => intro l r h; omega
  | succ n ih =>
    intro l r h
    cases l with
    | nil => rw [merge]; simp [toNoun, mergeF]
    | node p q ll lr =>
      cases r with
      | nil => rw [merge]; simp [toNoun, mergeF]
      | node p' q' rl rr =>
        simp only [size] at h
        have i1 := ih lr (node p' q' rl rr) (by simp only [size]; omega)
        have i2 := ih (node p q ll lr) rl (by simp only [size]; omega)
        simp only [toNoun] at i1 i2
        rw [merge]
        simp only [toNoun]
        rw [mergeF]
        by_cases m : morF mug (A p) (A p') = true
        · simp only [m, if_true, i1, toNoun]
        · simp only [m, if_false, Bool.false_eq_true, i2, toNoun]

theorem delF_toNoun (mug : Noun → Nat) (f : ν → Noun) (b : Nat) :
    ∀ t : Tr ν, delF mug (A b) (t.toNoun f) = some ((t.del mug b).toNoun f)
  | nil => rfl
  | node p q l r => by
    have il := delF_toNoun mug f b l
    have ir := delF_toNoun mug f b r
    by_cases e : b = p
    · subst e
      simp [toNoun, del, delF, mergeF_toNoun mug f _ l r (Nat.lt_succ_self _)]
    · by_cases g : gorF mug (A b) (A p) = true
      · simp [toNoun, del, delF, e, g, il]
      · simp [toNoun, del, delF, e, g, ir]

end Tr

/-! ## The instance -/

/-- The treaps that are maps under every layout of their values. -/
def TreapMap (mug : Noun → Nat) (ν : Type) : Type :=
  { t : Tr ν // ∀ f : ν → Noun, IsMap mug (t.toNoun f) }

/-- Two units that have the same noun under every layout are equal. -/
theorem unitNoun_inj {ν : Type} {x y : Option ν} (h : ∀ f : ν → Noun, unitNoun f x = unitNoun f y) :
    x = y := by
  classical
  rcases x with _ | a <;> rcases y with _ | b
  · rfl
  · have := h (fun _ => A 0); simp [unitNoun] at this
  · have := h (fun _ => A 0); simp [unitNoun] at this
  · have := h (fun w => if w = a then A 0 else A 1)
    simp only [unitNoun, Noun.cell.injEq, true_and] at this
    by_cases e : b = a
    · rw [e]
    · simp [e] at this

/-- On a map, `getF` of the result of a `putF` under another key is `getF` of
the map, and under the key itself the new value. -/
theorem getF_after_put {mug : Noun → Nat} {a out k v : Noun} (h : IsMap mug a) (ho : IsMap mug out)
    (hg : ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v')) (k' : Noun) :
    getF mug k' out = if k' = k then some (C (A 0) v) else getF mug k' a := by
  by_cases e : k' = k
  · subst e; simp only [if_true]; exact getF_some ho ((hg _ _).2 (Or.inl ⟨rfl, rfl⟩))
  · simp only [e, if_false]
    by_cases hv : ∃ w, Get a k' w
    · obtain ⟨w, hw⟩ := hv
      rw [getF_some h hw, getF_some ho ((hg _ _).2 (Or.inr ⟨e, hw⟩))]
    · have hn : ∀ w, ¬ Get a k' w := fun w hw => hv ⟨w, hw⟩
      rw [getF_none h hn, getF_none ho (fun w hw => by
        rcases (hg _ _).1 hw with ⟨e', _⟩ | ⟨_, hw'⟩
        · exact e e'
        · exact hn w hw')]

/-- The same for `delF`. -/
theorem getF_after_del {mug : Noun → Nat} {a out k : Noun} (h : IsMap mug a) (ho : IsMap mug out)
    (hg : ∀ k' v', Get out k' v' ↔ k' ≠ k ∧ Get a k' v') (k' : Noun) :
    getF mug k' out = if k' = k then some (A 0) else getF mug k' a := by
  by_cases e : k' = k
  · subst e; simp only [if_true]
    exact getF_none ho (fun w hw => ((hg _ _).1 hw).1 rfl)
  · simp only [e, if_false]
    by_cases hv : ∃ w, Get a k' w
    · obtain ⟨w, hw⟩ := hv
      rw [getF_some h hw, getF_some ho ((hg _ _).2 ⟨e, hw⟩)]
    · have hn : ∀ w, ¬ Get a k' w := fun w hw => hv ⟨w, hw⟩
      rw [getF_none h hn, getF_none ho (fun w hw => hn w ((hg _ _).1 hw).2)]

namespace TreapMap

variable {mug : Noun → Nat} {ν : Type}

def empty : TreapMap mug ν := ⟨Tr.nil, fun _ => IsMap.nil⟩

def get (m : TreapMap mug ν) (k : Nat) : Option ν := m.1.get mug k

def put (m : TreapMap mug ν) (k : Nat) (v : ν) : TreapMap mug ν :=
  ⟨m.1.put mug k v, fun f => by
    obtain ⟨out, hput, hmap, _⟩ := putF_spec mug (m.1.toNoun f) (A k) (f v) (m.2 f)
    rw [Tr.putF_toNoun] at hput
    exact (Option.some.inj hput) ▸ hmap⟩

def del (m : TreapMap mug ν) (k : Nat) : TreapMap mug ν :=
  ⟨m.1.del mug k, fun f => by
    obtain ⟨out, hdel, hmap, _⟩ := delF_spec (A k) (m.2 f)
    rw [Tr.delF_toNoun] at hdel
    exact (Option.some.inj hdel) ▸ hmap⟩

def toNoun (f : ν → Noun) (m : TreapMap mug ν) : Noun := m.1.toNoun f

theorem get_put (m : TreapMap mug ν) (k : Nat) (v : ν) (k' : Nat) :
    get (put m k v) k' = if k' = k then some v else get m k' := by
  apply unitNoun_inj
  intro f
  obtain ⟨out, hput, hmap, hg⟩ := putF_spec mug (m.1.toNoun f) (A k) (f v) (m.2 f)
  have e1 := getF_after_put (m.2 f) hmap hg (A k')
  rw [Tr.getF_toNoun] at e1
  rw [Tr.putF_toNoun] at hput
  rw [← Option.some.inj hput, Tr.getF_toNoun] at e1
  simp only [Noun.atom.injEq] at e1
  simp only [get, put]
  by_cases e : k' = k
  · simp only [e, if_true] at e1 ⊢; simpa [unitNoun] using e1
  · simp only [e, if_false] at e1 ⊢; exact Option.some.inj e1

theorem get_del (m : TreapMap mug ν) (k k' : Nat) :
    get (del m k) k' = if k' = k then none else get m k' := by
  apply unitNoun_inj
  intro f
  obtain ⟨out, hdel, hmap, hg⟩ := delF_spec (A k) (m.2 f)
  have e1 := getF_after_del (m.2 f) hmap hg (A k')
  rw [Tr.getF_toNoun] at e1
  rw [Tr.delF_toNoun] at hdel
  rw [← Option.some.inj hdel, Tr.getF_toNoun] at e1
  simp only [Noun.atom.injEq] at e1
  simp only [get, del]
  by_cases e : k' = k
  · simp only [e, if_true] at e1 ⊢; simpa [unitNoun] using e1
  · simp only [e, if_false] at e1 ⊢; exact Option.some.inj e1

end TreapMap

/-- The treaps of the pill's `+by`, with the pill's `+mug`. -/
instance : HoonMap (TreapMap mugF) where
  empty := TreapMap.empty
  get := TreapMap.get
  put := TreapMap.put
  del := TreapMap.del
  toNoun := TreapMap.toNoun
  get_empty _ := rfl
  get_put := TreapMap.get_put
  get_del := TreapMap.get_del
  toNoun_empty _ := rfl

/-! ## The links, as the interpreter arms use them -/

theorem hoonMap_get (m : TreapMap mugF ν) (k : Nat) : HoonMap.get m k = m.1.get mugF k := rfl

theorem hoonMap_toNoun (f : ν → Noun) (m : TreapMap mugF ν) : HoonMap.toNoun f m = m.1.toNoun f :=
  rfl

/-- `getF` on the noun of a map is the unit of `HoonMap.get`. -/
theorem getF_hoonMap (f : ν → Noun) (m : TreapMap mugF ν) (k : Nat) :
    getF mugF (A k) (HoonMap.toNoun f m) = some (unitNoun f (HoonMap.get m k)) :=
  Tr.getF_toNoun mugF f k m.1

/-- `putF` on the noun of a map is the noun of `HoonMap.put`. -/
theorem putF_hoonMap (f : ν → Noun) (m : TreapMap mugF ν) (k : Nat) (v : ν) :
    putF mugF (A k) (f v) (HoonMap.toNoun f m) = some (HoonMap.toNoun f (HoonMap.put m k v)) :=
  Tr.putF_toNoun mugF f k v m.1

/-- `delF` on the noun of a map is the noun of `HoonMap.del`. -/
theorem delF_hoonMap (f : ν → Noun) (m : TreapMap mugF ν) (k : Nat) :
    delF mugF (A k) (HoonMap.toNoun f m) = some (HoonMap.toNoun f (HoonMap.del m k)) :=
  Tr.delF_toNoun mugF f k m.1

/-- The noun of a map is a map. -/
theorem isMap_hoonMap (f : ν → Noun) (m : TreapMap mugF ν) : IsMap mugF (HoonMap.toNoun f m) :=
  m.2 f

end Compiler
end Formalization
