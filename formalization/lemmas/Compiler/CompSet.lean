import lemmas.Compiler.CompDoor
import lemmas.Compiler.SkaCull

/-!
# The pill's `(set @)` as an instance of `HoonSet`

`HoonSet` of `Ska/CompModel.lean` abstracts the sets of atoms of `+comp`
(the looked-at axes `lok` of a `sure`).  The instance here is the canonical
treap: a set is a `FinMap Nat Unit` (`CSet`), its noun is `FinMap.setNoun`
with the key `k` encoded as the atom `k` (`csTKeyNat`), so by `isSet_ext`
the noun of a set is the noun of every treap with these members, and
`toList` is the pre-order of that noun, the order in which `+rep:in` and
`+run:in` visit it (`cs_preorder`).

Where the order matters.  `setRun` (`+run:in`) and `splitLok` (the `+rep:in`
of `+split-sure`) give the same set in every order (`cs_mem_setRun`, and the
noun is fixed by the members), and so do `intoLok` and `+uni:in`.  Only
`sureRequireLook` (the `+rep:in` of `+sure-require-look`) allocates
registers in the order of the fold, and that order is the pre-order of the
canonical treap, which `toList` is.

The pill's gates: `+put:in` gives the noun of `HoonSet.put` (`cs_put_in`);
`+run:in` with a gate known on the members gives the noun of `setRun`
(`cs_run_in_gate_on`, `cs_runInF`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

/-- Atoms as treap keys: the key `k` is the atom `k`. -/
instance csTKeyNat : TKey Nat := ⟨A, fun _ _ h => by cases h; rfl⟩

/-- A `(set @)`: a finite set of atoms, laid out as the canonical treap. -/
abbrev CSet := FinMap Nat Unit

namespace CSet

theorem mem_keys (m : CSet) (x : Nat) : x ∈ m.rap.map Prod.fst ↔ m.1 x = some () := by
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨k, u⟩, h, rfl⟩
    exact (FinMap.mem_rap m k u).1 h
  · intro h
    exact ⟨(x, ()), (FinMap.mem_rap m x ()).2 h, rfl⟩

/-- The union. -/
noncomputable def uni (a b : CSet) : CSet :=
  ⟨fun k => if a.1 k = some () ∨ b.1 k = some () then some () else none, a.supp ++ b.supp,
    fun k h => by
      by_cases ha : a.1 k = some ()
      · exact List.mem_append_left _ (a.mem_supp (by rw [ha]; simp))
      · by_cases hb : b.1 k = some ()
        · exact List.mem_append_right _ (b.mem_supp (by rw [hb]; simp))
        · simp [ha, hb] at h⟩

theorem toNoun_empty : (FinMap.empty : CSet).setNoun = A 0 := by
  unfold FinMap.setNoun FinMap.toNoun
  generalize (FinMap.empty : CSet).supp = l
  induction l with
  | nil => rfl
  | cons k l ih => simpa [List.foldl, FinMap.step, FinMap.empty] using ih

end CSet

/-- The sets of `+comp` as canonical treaps. -/
noncomputable instance csHoonSet : HoonSet CSet where
  empty := FinMap.empty
  toList m := m.rap.map Prod.fst
  put m x := m.put x ()
  uni := CSet.uni
  isEmpty m := (m.rap.map Prod.fst).isEmpty
  small m := (m.rap.map Prod.fst).all (· == 1)
  toNoun m := m.setNoun
  mem_empty x := by rw [CSet.mem_keys]; simp [FinMap.empty]
  mem_put s x y := by
    rw [CSet.mem_keys, CSet.mem_keys]
    by_cases e : y = x <;> simp [FinMap.put, e]
  mem_uni a b y := by
    rw [CSet.mem_keys, CSet.mem_keys, CSet.mem_keys]
    by_cases ha : a.1 y = some () <;> by_cases hb : b.1 y = some () <;> simp [CSet.uni, ha, hb]
  isEmpty_iff s := List.isEmpty_iff
  small_iff s := by simp
  toNoun_empty := CSet.toNoun_empty

theorem cs_toList (m : CSet) : HoonSet.toList m = m.rap.map Prod.fst := rfl
theorem cs_toNoun (m : CSet) : HoonSet.toNoun m = m.setNoun := rfl
theorem cs_put (m : CSet) (x : Nat) : HoonSet.put m x = m.put x () := rfl
theorem cs_empty : (HoonSet.empty : CSet) = FinMap.empty := rfl

theorem cs_mem (m : CSet) (x : Nat) : x ∈ HoonSet.toList m ↔ m.1 x = some () := CSet.mem_keys m x

/-- Two sets with the same members are equal. -/
theorem cs_ext {a b : CSet} (h : ∀ x, x ∈ HoonSet.toList a ↔ x ∈ HoonSet.toList b) : a = b := by
  apply Subtype.ext
  funext x
  have hx := h x
  rw [cs_mem, cs_mem] at hx
  cases ea : a.1 x <;> cases eb : b.1 x <;> simp_all

/-- The pre-order of `+rep:in` on the noun of a set is `toList`. -/
theorem cs_preorder (m : CSet) : preorder (HoonSet.toNoun m) = (HoonSet.toList m).map A := by
  apply map_cell_inj (A 0)
  rw [cs_toNoun, ← preorder_toMap, FinMap.toMap_setNoun, FinMap.preorder_toNoun, List.map_map,
    cs_toList, List.map_map]
  rfl

theorem cs_isSet (m : CSet) : IsSet mugF (HoonSet.toNoun m) := FinMap.isSet_setNoun m

theorem cs_tree (m : CSet) : Tree (HoonSet.toNoun m) := Tree.of_isSet (cs_isSet m)

/-- The members of the noun of a set. -/
theorem cs_has (m : CSet) (k : Noun) : Has (HoonSet.toNoun m) k ↔ ∃ x ∈ HoonSet.toList m, k = A x := by
  rw [cs_toNoun, FinMap.has_setNoun]
  constructor
  · rintro ⟨x, h, rfl⟩
    exact ⟨x, (cs_mem m x).2 h, rfl⟩
  · rintro ⟨x, h, rfl⟩
    exact ⟨x, (cs_mem m x).1 h, rfl⟩

/-- `+put:in`'s model on the noun of a set. -/
theorem cs_putInF (m : CSet) (x : Nat) :
    putInF mugF (A x) (HoonSet.toNoun m) = some (HoonSet.toNoun (HoonSet.put m x)) :=
  FinMap.putInF_setNoun m x

/-- The pill's `+put:in`. -/
theorem cs_put_in (m : CSet) (x : Nat) :
    nock (C in.put.battery (C (A x) (C in.battery (C (HoonSet.toNoun m) layer2)))) in.put.battery
      = some (HoonSet.toNoun (HoonSet.put m x)) :=
  put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF m x)

/-- The noun of a set is `~` exactly when it has no member. -/
theorem cs_toNoun_nil (m : CSet) : HoonSet.toNoun m = A 0 ↔ HoonSet.toList m = [] := by
  constructor
  · intro h
    have hp := cs_preorder m
    rw [h] at hp
    simpa [preorder] using hp.symm
  · intro h
    have hm : m = HoonSet.empty := cs_ext fun x => by
      rw [h]; simp [HoonSet.mem_empty]
    rw [hm]; exact HoonSet.toNoun_empty

/-- The members of `setRun f s`, in any order of the fold. -/
theorem cs_mem_setRun (f : Nat → Nat) (s : CSet) (x : Nat) :
    x ∈ HoonSet.toList (setRun f s) ↔ ∃ y ∈ HoonSet.toList s, x = f y := by
  unfold setRun
  generalize HoonSet.toList s = l
  induction l with
  | nil => simp [HoonSet.mem_empty]
  | cons y l ih =>
    rw [List.foldr_cons, HoonSet.mem_put, ih]
    constructor
    · rintro (rfl | ⟨z, hz, rfl⟩)
      · exact ⟨y, List.mem_cons_self, rfl⟩
      · exact ⟨z, List.mem_cons_of_mem _ hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr ⟨z, hz, rfl⟩

/-- The gate of `+run:in` on nouns, from a function on atoms. -/
def csLift (f : Nat → Nat) : Noun → Noun
  | Noun.atom y => A (f y)
  | _ => A 0

/-- `+run:in`'s model from `~` on the noun of a set is the noun of `setRun`. -/
theorem cs_runInF (f : Nat → Nat) (s : CSet) :
    runInF mugF (csLift f) (HoonSet.toNoun s) (A 0) = some (HoonSet.toNoun (setRun f s)) := by
  obtain ⟨out, h, hs, hh⟩ := runInF_spec (mug := mugF) (csLift f) (cs_tree s) (A 0) (by
    unfold IsSet; exact IsMap.nil)
  rw [h, isSet_ext hs (cs_isSet (setRun f s))]
  intro k
  rw [hh, cs_has, cs_preorder]
  constructor
  · rintro (hk | ⟨y, hy, rfl⟩)
    · exact absurd hk not_has_atom
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact ⟨f z, (cs_mem_setRun f s _).2 ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (cs_mem_setRun f s x).1 hx
    exact Or.inr ⟨A z, List.mem_map.2 ⟨z, hz, rfl⟩, rfl⟩

/-! ## `+run:in` with a gate known on the members -/

theorem cs_run_in_loop_on {mug : Noun → Nat} (ctx : Noun) (hc : InIn mug ctx) (fp fs fc : Noun)
    (f : Noun → Noun) :
    ∀ (a : Noun), Tree a → (∀ x ∈ preorder a, nock (C fp (C x fc)) fp = some (f x)) →
    ∀ (c out : Noun), runInF mug f a c = some out →
      nock (C in.run.loop (C c (C in.run.battery (C (C fp (C fs fc)) (C in.battery (C a ctx))))))
        in.run.loop = some out := by
  obtain ⟨hin, hgo, hmo⟩ := hc
  have hput := put_in_gate (mug := mug) ctx ⟨hgo, hmo⟩
  intro a ha
  induction ha with
  | nil =>
    intro _ c out h
    simp only [runInF, Option.some.injEq] at h
    subst h
    nock_open in.run.loop
    simp [nock_exec]
  | @node n l r _ _ ihl ihr =>
    intro hg c out h
    have hn := hg n (by simp [preorder])
    simp only [runInF] at h
    cases e1 : putInF mug (f n) c with
    | none => simp [e1] at h
    | some c1 =>
      cases e2 : runInF mug f l c1 with
      | none => simp [e1, e2] at h
      | some c2 =>
        simp only [e1, e2] at h
        have hl := ihl (fun x hx => hg x (by simp [preorder, hx])) c1 c2 e2
        have hr := ihr (fun x hx => hg x (by simp [preorder, hx])) c2 out h
        have hp := hput _ _ _ e1
        nock_open in.run.loop
        simp [nock_exec, in_arm, put_in_arm, hin, hp, hn, hl, hr]

theorem cs_run_in_gate_on {mug : Noun → Nat} (ctx : Noun) (hc : InIn mug ctx) (fp fs fc : Noun)
    (f : Noun → Noun) (a : Noun) (ha : Tree a)
    (hf : ∀ x ∈ preorder a, nock (C fp (C x fc)) fp = some (f x)) (out : Noun)
    (h : runInF mug f a (A 0) = some out) :
    nock (C in.run.battery (C (C fp (C fs fc)) (C in.battery (C a ctx)))) in.run.battery
      = some out := by
  nock_open in.run.battery
  simp only [nock_exec, cs_run_in_loop_on ctx hc fp fs fc f a ha hf (A 0) out h]

@[nock_exec] theorem cs_run_in_arm (d : Noun) :
    nock d in.run.arm = some (C in.run.battery (C (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0)))) d)) := by
  nock_open in.run.arm; simp only [nock_exec]

theorem cs_inIn_layer2 : InIn mugF layer2 := ⟨in.arm_at, gorIn_morIn_layer2⟩

end Compiler
end Formalization
