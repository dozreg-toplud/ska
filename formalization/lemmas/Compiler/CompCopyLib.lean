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

end Compiler
end Formalization
