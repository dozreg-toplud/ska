import lemmas.Compiler.SkaArms
import lemmas.Hoon.DifIn
import lemmas.KernelRfl

/-!
# `+cull` of the core of `+ska-callgraph`

The arm `10` of the core `K` (`SkaCore.lean`) against `Ana.cull`, in every
context `K` with `ana` at axis `31`.

```hoon
++  cull
  |=  [id=identity st=ska-state]
  ^-  ska-state
  =/  members=(set identity)  (silt (above id stk.st))
  =/  live=(set identity)  ...                      ::  the loop live
  =/  dead=(set identity)  (~(dif in members) live)
  ?:  =(~ dead)  st
  =.  culled.stats.st  (add culled.stats.st ~(wyt in dead))
  =.  stk.st  (skip stk.st ~(has in dead))
  =.  moved.st  (~(dif in moved.st) dead)
  %-  ~(rep in dead)
  |=  [i=identity =_st]
  %=  st
    order  (~(del by order.st) i)
    ticks  (~(del by ticks.st) i)
    g      (~(del by g.st) i)
  ==
```

The generator names no noun of `+silt` (arm `767` of layer 2), so it is
defined here (`siltArm`, `silt_arm_at`, checked by the kernel); it is wanted
as `silt.*` at the next regeneration.  `+silt` is `+gas:in` from `~`.
The sample of the gate of `+rep` is `[*identity st]`; the bunt of
`identity` is computed by the mold at arm `186` of the tail of `ana`
(`identBunt`, `mold_bunt`, by the kernel through `evalFuel`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## `+silt` -/

/-- The battery of the gate `+silt`. -/
def siltBattery : Noun := C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 15)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))))

/-- The arm `+silt` of layer 2. -/
def siltArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) siltBattery) (C (A 0) (A 1))))

theorem silt_arm_at : slot? 767 layer2 = some siltArm := by kernel_rfl

@[nock_exec] theorem silt_arm (d : Noun) : nock d siltArm = some (C siltBattery (C (A 0) d)) := by
  unfold siltArm; simp only [nock_exec]

theorem gas_in_gate (l : List Noun) (a out : Noun) (h : gasInF mugF a l = some out) :
    nock (C in.gas.battery (C (listN l) (C in.battery (C a layer2)))) in.gas.battery = some out := by
  nock_open in.gas.battery
  simp only [nock_exec, gas_in_loop layer2 gorIn_morIn_layer2 l a out h]

/-- `+silt` is `+gas:in` from the empty set. -/
theorem silt_gate (l : List Noun) (out : Noun) (h : gasInF mugF (A 0) l = some out) :
    nock (C siltBattery (C (listN l) layer2)) siltBattery = some out := by
  have hg := gas_in_gate l (A 0) out h
  unfold siltBattery
  simp [nock_exec, in_arm, in.arm_at, in.gas.arm_at, gas_in_arm, hg]

/-! ## Sets of identities as nouns -/

theorem get_foldl_ins : ∀ (l : List Ident) (m : FinMap Ident Unit) (k : Ident),
    Treap.get (l.foldl Treap.ins m) k = some () ↔ k ∈ l ∨ Treap.get m k = some ()
  | [], m, k => by simp
  | x :: l, m, k => by
    rw [List.foldl_cons, get_foldl_ins l (Treap.ins m x) k]
    show k ∈ l ∨ Treap.get (Treap.put m x ()) k = some () ↔ _
    rw [Treap.get_put]
    by_cases e : k = x
    · subst e; simp
    · simp [e]

/-- `+silt` of a list of identities is the noun of `Treap.silt`. -/
theorem silt_setNoun (l : List Ident) :
    gasInF mugF (A 0) (l.map identNoun) = some (Treap.setNoun (Treap.silt l : FinMap Ident Unit)) := by
  obtain ⟨out, h, hs, hh⟩ := gasInF_spec (mug := mugF) (l.map identNoun) (A 0) isSet_nil
  rw [h]
  congr 1
  apply isSet_ext hs (FinMap.isSet_setNoun _)
  intro kn
  rw [hh, FinMap.has_setNoun]
  have e := get_foldl_ins l Treap.empty
  simp only [Treap.get_empty] at e
  constructor
  · rintro (h | h)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
      exact ⟨k, (e k).2 (Or.inl hk), rfl⟩
    · exact absurd h not_has_atom
  · rintro ⟨k, hk, rfl⟩
    have hk' : k ∈ l := by
      rcases (e k).1 hk with h | h
      · exact h
      · cases h
    exact Or.inl (List.mem_map.2 ⟨k, hk', rfl⟩)

theorem get_foldl_del (k : Ident) : ∀ (L : List (Ident × Unit)) (s : FinMap Ident Unit),
    Treap.get (L.foldl (fun s k => Treap.del s k.1) s) k
      = if k ∈ L.map Prod.fst then none else Treap.get s k
  | [], s => by simp
  | x :: L, s => by
    rw [List.foldl_cons, get_foldl_del k L, Treap.get_del]
    by_cases e : k = x.1
    · simp [e]
    · by_cases h : k ∈ L.map Prod.fst <;> simp [e, h]

theorem get_dif (a b : FinMap Ident Unit) (k : Ident) :
    Treap.get (Treap.dif a b) k = if Treap.has b k then none else Treap.get a k := by
  unfold Treap.dif
  rw [get_foldl_del]
  congr 1
  apply propext
  simp only [List.mem_map, Treap.has]
  constructor
  · rintro ⟨⟨k', u⟩, hk, rfl⟩
    cases u
    rw [(Treap.mem_tap b k' ()).1 hk]; rfl
  · intro h
    cases e : Treap.get b k with
    | none => rw [e] at h; cases h
    | some u => cases u; exact ⟨(k, ()), (Treap.mem_tap b k ()).2 e, rfl⟩

/-- `+dif:in` of two sets of identities is the noun of `Treap.dif`. -/
theorem dif_setNoun (a b : FinMap Ident Unit) :
    difInF mugF (Treap.setNoun a) (Treap.setNoun b) = some (Treap.setNoun (Treap.dif a b)) := by
  obtain ⟨out, h, hs, hh⟩ := difInF_spec (FinMap.isSet_setNoun b) _ (FinMap.isSet_setNoun a)
  show difInF mugF (FinMap.setNoun a) (FinMap.setNoun b) = _
  rw [h]
  congr 1
  apply isSet_ext hs (FinMap.isSet_setNoun _)
  intro kn
  rw [hh, FinMap.has_setNoun, FinMap.has_setNoun, FinMap.has_setNoun]
  have hd := get_dif a b
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hn⟩
    refine ⟨k, ?_, rfl⟩
    show Treap.get (Treap.dif a b) k = some ()
    rw [hd]
    have : Treap.has b k = false := by
      cases e : Treap.has b k
      · rfl
      · exfalso; apply hn
        refine ⟨k, ?_, rfl⟩
        simp only [Treap.has] at e
        cases e' : Treap.get b k with
        | none => rw [e'] at e; cases e
        | some u => cases u; exact e'
    rw [this]; exact hk
  · rintro ⟨k, hk, rfl⟩
    have hk' : Treap.get (Treap.dif a b) k = some () := hk
    rw [hd] at hk'
    cases e : Treap.has b k
    · rw [e] at hk'
      refine ⟨⟨k, hk', rfl⟩, ?_⟩
      rintro ⟨k', hk'', he⟩
      rw [← TKey.enc_inj _ _ he] at hk''
      have : Treap.has b k = true := by
        show (Treap.get b k).isSome = true
        rw [show Treap.get b k = b.1 k from rfl, hk'']; rfl
      rw [e] at this; cases this
    · rw [e] at hk'; simp at hk'

/-- The noun of a set is `~` exactly when the set is empty. -/
theorem setNoun_nil_iff (m : FinMap Ident Unit) : Treap.setNoun m = A 0 ↔ Treap.tap m = [] := by
  constructor
  · intro h
    have e := tapList_setNoun m
    rw [show FinMap.setNoun m = Treap.setNoun m from rfl, h] at e
    simp [tapList] at e
    exact e
  · intro h
    apply isSet_ext (FinMap.isSet_setNoun m) isSet_nil
    intro kn
    rw [FinMap.has_setNoun]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have := (Treap.mem_tap m k ()).2 hk
      rw [h] at this; cases this
    · intro h'; exact absurd h' not_has_atom

theorem preorder_toMap : ∀ a : Noun, preorder (toMap a) = (preorder a).map (fun n => C n (A 0))
  | Noun.atom k => by simp [preorder]
  | Noun.cell n (Noun.atom k) => by simp [preorder]
  | Noun.cell n (Noun.cell l r) => by
    rw [toMap_node]
    simp only [preorder, preorder_toMap l, preorder_toMap r, List.map_cons, List.map_append]

/-- The pre-order of `+rep` on the noun of a set lists `Treap.rap` of it. -/
theorem preorder_setNoun (m : FinMap Ident Unit) :
    preorder (Treap.setNoun m) = (Treap.rap m).map fun e => identNoun e.1 := by
  apply map_cell_inj (A 0)
  rw [← preorder_toMap, show Treap.setNoun m = FinMap.setNoun m from rfl, FinMap.toMap_setNoun,
    FinMap.preorder_toNoun, List.map_map]
  rfl

theorem length_preorder : ∀ a : Noun, (preorder a).length = (tapList a).length
  | Noun.atom k => by simp [preorder, tapList]
  | Noun.cell n (Noun.atom k) => by simp [preorder, tapList]
  | Noun.cell n (Noun.cell l r) => by
    simp only [preorder, tapList, List.length_cons, List.length_append, length_preorder l,
      length_preorder r]
    omega

theorem wyt_setNoun (m : FinMap Ident Unit) : (preorder (Treap.setNoun m)).length = Treap.wyt m := by
  rw [length_preorder, show Treap.setNoun m = FinMap.setNoun m from rfl, tapList_setNoun, List.length_map]
  rfl

end Compiler
end Formalization
