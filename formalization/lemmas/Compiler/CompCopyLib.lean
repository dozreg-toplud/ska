import lemmas.Compiler.CompCopyGen
import lemmas.Hoon.ListsSort
import lemmas.Hoon.SetFolds
import lemmas.Hoon.GasBy

/-!
# The library arms of the merge of `+copy-lazy`

The merge branch of `+copy-lazy` uses, from layer 2: `+malt` (arm `382`,
through `+molt`, arm `766`, and `+gas:by` on the empty map), `+spin` (with a
gate that may crash), `+silt` and `+has:in`, `+skip`, `+weld`, `+turn`.
Here: `malt_gate` (`+malt` of a list of pairs is `gasF` from `~`), the arm
`+spin` built on layer 2 by the kernel (`spin_arm_l2`) and `spin_gate_T`
(the fold `spinM` in `Option` over an encoded list).  `+malt` and `+molt` are
written here, tied by `malt_at`, `molt_at`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- `+malt` of layer 2. -/
def maltArm : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 766) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))

/-- `+molt` of layer 2. -/
def moltArm : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 7)))) (C (A 9) (C (A 378) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))

theorem malt_at : slot? 382 layer2 = some maltArm := by kernel_rfl
theorem molt_at : slot? 766 layer2 = some moltArm := by kernel_rfl

/-- **`+malt`** of layer 2 on a list of pairs is `gasF` from the empty map. -/
theorem malt_gate (l : List (Noun × Noun)) (out : Noun) (h : gasF mugF (A 0) l = some out) :
    nock (C (C (A 8) (C (C (A 9) (C (A 766) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10)
      (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))
      (C (listN (l.map pairNoun)) layer2))
      (C (A 8) (C (C (A 9) (C (A 766) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10)
      (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))
      = some out := by
  have hg := gas_gate layer2 gorIn_morIn_layer2 l (A 0) out h
  simp [nock_exec, molt_at, moltArm, by_arm, by.arm_at, gas_arm, by.gas.arm_at, hg]

/-! ## `+spin` with a gate that may crash -/

/-- `+spin` in `Option`: the gate on each element in order with the state,
the products and the last state. -/
def spinM {α σ β : Type} (G : α → σ → Option (β × σ)) : List α → σ → Option (List β × σ)
  | [], s => some ([], s)
  | a :: l, s => (G a s).bind fun r => (spinM G l r.2).map fun q => (r.1 :: q.1, q.2)

theorem spin_loop_T {α σ β : Type} (E : α → Noun) (F : β → Noun) (Sn : σ → Noun) (ctx : Noun)
    (hc : SpinIn ctx) (cp cs cc : Noun) (G : α → σ → Option (β × σ)) : ∀ (l : List α),
    (∀ a ∈ l, ∀ s, nock (C cp (C (C (E a) (Sn s)) cc)) cp = (G a s).map fun r => C (F r.1) (Sn r.2)) →
    ∀ (acc : List Noun) (s : σ),
    nock (C spin.loop (C (listN acc) (C spin.battery
        (C (C (listN (l.map E)) (C (Sn s) (C cp (C cs cc)))) ctx)))) spin.loop
      = (spinM G l s).map fun r => C (listN (acc.reverse ++ r.1.map F)) (Sn r.2) := by
  obtain ⟨hflop, hhomo⟩ := hc
  intro l
  induction l with
  | nil =>
    intro _ acc s
    nock_open spin.loop
    simp [nock_exec, hflop, flop_gate ctx hhomo, spinM]
  | cons a xs ih =>
    intro hf acc s
    have ha := hf a (by simp) s
    cases e : G a s with
    | none =>
      rw [e] at ha
      nock_open spin.loop
      simp [nock_exec, ha, spinM, e]
    | some r =>
      obtain ⟨b, s'⟩ := r
      rw [e, Option.map_some] at ha
      have ihs := ih (fun y hy => hf y (by simp [hy])) (F b :: acc) s'
      simp only [listN_cons] at ihs
      nock_open spin.loop
      simp [nock_exec, ha, ihs, spinM, e, Function.comp_def]

/-- **`+spin`** slammed on an encoded list, a state and a gate `[cp [cs cc]]`
that is `G` on the state nouns: the products in order and the last state; a
crash where the gate crashes. -/
theorem spin_gate_T {α σ β : Type} (E : α → Noun) (F : β → Noun) (Sn : σ → Noun) (ctx : Noun)
    (hc : SpinIn ctx) (cp cs cc : Noun) (G : α → σ → Option (β × σ)) (l : List α) (s : σ)
    (hf : ∀ a ∈ l, ∀ s, nock (C cp (C (C (E a) (Sn s)) cc)) cp = (G a s).map fun r => C (F r.1) (Sn r.2)) :
    nock (C spin.battery (C (C (listN (l.map E)) (C (Sn s) (C cp (C cs cc)))) ctx)) spin.battery
      = (spinM G l s).map fun r => C (listN (r.1.map F)) (Sn r.2) := by
  have h := spin_loop_T E F Sn ctx hc cp cs cc G l hf [] s
  simp only [List.reverse_nil, List.nil_append] at h
  have h0 : listN [] = A 0 := rfl
  rw [h0] at h
  nock_open spin.battery
  simp [nock_exec, h]

/-- The gate `+spin` of layer 2 builds, computed by the kernel. -/
noncomputable def spinGateL2 : Noun := (evalFuel 2000 layer2 spin.arm).getD (A 0)

theorem spin_arm_l2 : nock layer2 spin.arm = some spinGateL2 := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

noncomputable def spinBuntL2 : Noun := (slot? 6 spinGateL2).getD (A 0)

theorem spin_gate_eq : spinGateL2 = C spin.battery (C spinBuntL2 layer2) := by kernel_rfl

theorem spinIn_layer2 : SpinIn layer2 := ⟨flop.arm_at, homoIn_layer2⟩

/-! ## The index and the seen set of the merge -/

/-- `+gas:by` of the pairs `[key e]` of a list onto the noun of a map is the
noun of the map with the entries put in order. -/
theorem gas_index {α : Type} (E : α → Noun) (key : α → Nat) :
    ∀ (l : List α) (m : TreapMap mugF α),
    gasF mugF (HoonMap.toNoun E m) (l.map fun e => (A (key e), E e))
      = some (HoonMap.toNoun E (l.foldl (fun m e => HoonMap.put m (key e) e) m))
  | [], m => rfl
  | e :: rest, m => by
    simp only [List.map_cons, gasF, putF_hoonMap, List.foldl_cons]
    exact gas_index E key rest _

/-- The index of the merge (`malt` of the pairs) is the noun of the model's
`index`. -/
theorem malt_index {α : Type} (E : α → Noun) (key : α → Nat) (l : List α) :
    gasF mugF (A 0) (l.map fun e => (A (key e), E e))
      = some (HoonMap.toNoun E (Lazy.index (Map := TreapMap mugF) key l)) := by
  have := gas_index E key l HoonMap.empty
  rw [HoonMap.toNoun_empty] at this
  exact this

/-- An entry of the index is an entry of the list. -/
theorem index_mem {α : Type} (key : α → Nat) :
    ∀ (l : List α) (m : TreapMap mugF α) (k : Nat) (v : α),
    HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = some v → v ∈ l ∨ HoonMap.get m k = some v
  | [], m, k, v, h => Or.inr h
  | e :: rest, m, k, v, h => by
    rw [List.foldl_cons] at h
    rcases index_mem key rest _ k v h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · rw [HoonMap.get_put] at h1
      split at h1
      · simp only [Option.some.injEq] at h1; subst h1; exact Or.inl List.mem_cons_self
      · exact Or.inr h1

theorem index_mem' {α : Type} (key : α → Nat) (l : List α) (k : Nat) (v : α)
    (h : HoonMap.get (Lazy.index (Map := TreapMap mugF) key l) k = some v) : v ∈ l := by
  rcases index_mem key l HoonMap.empty k v h with h1 | h1
  · exact h1
  · rw [HoonMap.get_empty] at h1; cases h1

theorem mem_foldl_put (k : Nat) : ∀ (l : List Nat) (s : CSet),
    k ∈ HoonSet.toList (l.foldl HoonSet.put s) ↔ k ∈ l ∨ k ∈ HoonSet.toList s
  | [], s => by simp
  | x :: l, s => by
    rw [List.foldl_cons, mem_foldl_put k l, HoonSet.mem_put]
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

/-- The model's `seen` is membership in the keys. -/
theorem seen_iff {α : Type} (key : α → Nat) (l : List α) (k : Nat) :
    Lazy.seen (S := CSet) key l k = decide (k ∈ l.map key) := by
  unfold Lazy.seen
  congr 1
  apply propext
  rw [mem_foldl_put]
  simp [HoonSet.mem_empty]

/-- `+spin` with an invariant of the states that the gate keeps: the gate need
only be `G` on states with the invariant. -/
theorem spin_loop_TI {α σ β : Type} (E : α → Noun) (F : β → Noun) (Sn : σ → Noun) (ctx : Noun)
    (hc : SpinIn ctx) (cp cs cc : Noun) (G : α → σ → Option (β × σ)) (I : σ → Prop) : ∀ (l : List α),
    (∀ a ∈ l, ∀ s, I s → nock (C cp (C (C (E a) (Sn s)) cc)) cp = (G a s).map fun r => C (F r.1) (Sn r.2)) →
    (∀ a ∈ l, ∀ s r, I s → G a s = some r → I r.2) →
    ∀ (acc : List Noun) (s : σ), I s →
    nock (C spin.loop (C (listN acc) (C spin.battery
        (C (C (listN (l.map E)) (C (Sn s) (C cp (C cs cc)))) ctx)))) spin.loop
      = (spinM G l s).map fun r => C (listN (acc.reverse ++ r.1.map F)) (Sn r.2) := by
  obtain ⟨hflop, hhomo⟩ := hc
  intro l
  induction l with
  | nil =>
    intro _ _ acc s _
    nock_open spin.loop
    simp [nock_exec, hflop, flop_gate ctx hhomo, spinM]
  | cons a xs ih =>
    intro hf hI acc s hs
    have ha := hf a (by simp) s hs
    cases e : G a s with
    | none =>
      rw [e] at ha
      nock_open spin.loop
      simp [nock_exec, ha, spinM, e]
    | some r =>
      obtain ⟨b, s'⟩ := r
      rw [e, Option.map_some] at ha
      have hs' := hI a (by simp) s _ hs e
      have ihs := ih (fun y hy => hf y (by simp [hy])) (fun y hy => hI y (by simp [hy])) (F b :: acc) s' hs'
      simp only [listN_cons] at ihs
      nock_open spin.loop
      simp [nock_exec, ha, ihs, spinM, e, Function.comp_def]

theorem spin_gate_TI {α σ β : Type} (E : α → Noun) (F : β → Noun) (Sn : σ → Noun) (ctx : Noun)
    (hc : SpinIn ctx) (cp cs cc : Noun) (G : α → σ → Option (β × σ)) (I : σ → Prop) (l : List α) (s : σ)
    (hf : ∀ a ∈ l, ∀ s, I s → nock (C cp (C (C (E a) (Sn s)) cc)) cp = (G a s).map fun r => C (F r.1) (Sn r.2))
    (hI : ∀ a ∈ l, ∀ s r, I s → G a s = some r → I r.2) (hs : I s) :
    nock (C spin.battery (C (C (listN (l.map E)) (C (Sn s) (C cp (C cs cc)))) ctx)) spin.battery
      = (spinM G l s).map fun r => C (listN (r.1.map F)) (Sn r.2) := by
  have h := spin_loop_TI E F Sn ctx hc cp cs cc G I l hf hI [] s hs
  simp only [List.reverse_nil, List.nil_append] at h
  have h0 : listN [] = A 0 := rfl
  rw [h0] at h
  nock_open spin.battery
  simp [nock_exec, h]

end Compiler
end Formalization
