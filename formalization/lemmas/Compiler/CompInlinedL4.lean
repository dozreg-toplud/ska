import lemmas.Compiler.CompInlinedL3

/-!
# `+inlined`: the gate `hot` (track Q)

```hoon
=/  hot
  |=  c=bell
  ^-  ?
  ?=(^ (biff (~(get by call.cole.jets.long-ska) c) ~(get by jets-hot)))
```

`call.cole.jets.long-ska` is axis `126` of `jets.long-ska`.  `hotOf CALL JH c`
reads the ring of `c` in `CALL` and whether `jets-hot` has a driver for it.
`hotN_of`: the gate `hot` answers `hotOf` (`HotN`) on every gate core, when
the two maps are maps.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Glue

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The test of the gate `hot` on the nouns: `c` has a ring in `CALL` and the
ring has a driver in `JH`. -/
def hotOf (CALL JH : Noun) (c : Bell) : Bool :=
  match getF mugF c.toNoun CALL with
  | some (.cell _ u) =>
    match getF mugF u JH with
    | some (.cell _ _) => true
    | _ => false
  | _ => false

/-- **The gate `hot` is `hotOf`.** -/
theorem hotN_of {CODE JETS CALLS CALL JH : Noun} (hc : slot? 126 JETS = some CALL) (h1 : IsMap mugF CALL)
    (h2 : IsMap mugF JH) : HotN (C CODE (C JETS CALLS)) JH (hotOf CALL JH) := by
  intro c B CA
  have hL := compK_layer2
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hb : inlHB = (slot? 29 inlHot).getD (A 0) := rfl
  have hHB : inlHB = C (A 8) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fabe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 1014))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 3) (C (A 0) (A 2)))) := by
    kernel_rfl
  rw [hHB]
  obtain ⟨j1, j2, rfl⟩ : ∃ a b, JETS = C a b := by
    cases JETS with
    | atom _ => simp [nock_exec] at hc
    | cell a b => exact ⟨a, b, rfl⟩
  simp only [nock_exec] at hc
  rcases inl_getF_cases (k := c.toNoun) h1 with hg | ⟨u, hg⟩
  · have hG := get_gate layer2 hgc c.toNoun CALL _ hg
    have hv : hotOf CALL JH c = false := by simp [hotOf, hg]
    rw [hv]
    generalize compK = KC at hL ⊢
    simp [nock_exec, hL, biff.arm_at, biff_arm, by.arm_at, by_arm, by.get.arm_at, get_arm, hc, hG, loob]
  · have hG := get_gate layer2 hgc c.toNoun CALL _ hg
    rcases inl_getF_cases (k := u) h2 with hg2 | ⟨w, hg2⟩
    · have hG2 := get_gate layer2 hgc u JH _ hg2
      have hv : hotOf CALL JH c = false := by simp [hotOf, hg, hg2]
      rw [hv]
      generalize compK = KC at hL ⊢
      simp [nock_exec, hL, biff.arm_at, biff_arm, by.arm_at, by_arm, by.get.arm_at, get_arm, hc, hG, hG2, loob]
    · have hG2 := get_gate layer2 hgc u JH _ hg2
      have hv : hotOf CALL JH c = true := by simp [hotOf, hg, hg2]
      rw [hv]
      generalize compK = KC at hL ⊢
      simp [nock_exec, hL, biff.arm_at, biff_arm, by.arm_at, by_arm, by.get.arm_at, get_arm, hc, hG, hG2, loob]

end Compiler
end Formalization
