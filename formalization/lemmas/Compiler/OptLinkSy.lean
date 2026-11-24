import lemmas.Compiler.OptLinkBase

/-!
# `+sy`: a set from a list

```hoon
++  sy  si:nl                     ::  arm 42 of layer2
++  nl  |%  ...                   ::  arm 175 of layer2
  ++  si                          ::  arm 10 of the core
    |*  a=(list)
    =>  .(a ^+((le a) a))
    (~(gas in `(set _i.-.a)`~) a)
```

`+optimize-once` makes the set `topo-set` of `+rev-cfg` with `(sy topo)`.
The arm `42` of `layer2` is `[7 [9 175 0 1] 9 10 0 1]`: the core `nl`
(`[nlBat layer2]`, from the arm `175`, `[[1 nlBat] 0 1]`, `nl_at`) and its arm
`si` (`siArm`, `nl_si`).  The cast `^+` compiles to the edit of `a` by itself,
so the gate is `+gas:in` from `~` (`si_gate`): a set of atoms with the members
of the list (`SawRel`), which is what `rev_gate` takes.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false

/-- The body of the gate `si`. -/
def siBody : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 15)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))))

/-- The arm `si` of `nl`. -/
def siArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) siBody) (C (A 0) (A 1))))

/-- The battery of `nl`. -/
noncomputable def nlBat : Noun := ((slot? 175 layer2).bind (slot? 5)).getD (A 0)

theorem nl_at : slot? 175 layer2 = some (C (C (A 1) nlBat) (C (A 0) (A 1))) := by kernel_rfl

theorem nl_si : slot? 6 nlBat = some siArm := by kernel_rfl

/-- The arm `+sy` of `layer2`. -/
def syArm : Noun := C (A 7) (C (C (A 9) (C (A 175) (C (A 0) (A 1)))) (C (A 9) (C (A 10) (C (A 0) (A 1)))))

theorem sy_at : slot? 42 layer2 = some syArm := by kernel_rfl

/-- The arm `+sy` builds the gate `si` in the core `nl`. -/
theorem sy_arm : nock layer2 syArm = some (C siBody (C (A 0) (C nlBat layer2))) := by
  have h1 := nl_at
  have h2 := nl_si
  unfold syArm
  generalize nlBat = NB at h1 h2
  generalize layer2 = L2 at h1
  simp [nock_exec, h1, h2, siArm]

/-- **`(sy a)`** on a list of atoms: a set of atoms with its members. -/
theorem si_gate (l : List Nat) :
    ∃ S, nock (C siBody (C (listNoun A l) (C nlBat layer2))) siBody = some S ∧ SawRel S l := by
  obtain ⟨S, hg, hS⟩ := saw_gas sawRel_nil l
  rw [List.append_nil] at hS
  refine ⟨S, ?_, hS⟩
  unfold siBody
  simp [nock_exec, in_arm, in.arm_at, in.gas.arm_at, gas_in_arm, hg]

end Compiler
end Formalization
