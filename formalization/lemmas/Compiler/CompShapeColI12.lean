import lemmas.Compiler.CompShapeColMsg

/-!
# `+inter1-to-inter2` with forks

`i12_gate`: the gate body of `+inter1-to-inter2` (arm `0xbbbb` of `K`,
`i2Body` of `CompSureOf.lean`) on `[[intr less] K]` is `i12 less intr`
(`Ska/ShapeCol.lean`) for every `need-inter1` `intr` over `CSet`, forks to
any depth; a crash (a look at `0`) is `none`.  The `+rep:in` at the root is
`i2_rep`; the `+turn` over the forks (`turn_gate_mapM`) slams the gate
`[(this-buc y less) (this-buc n less)]` on each fork, which is the gate
again on the two branches (`i12_forks`, mutual with `i12_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns of `need-inter1` and `need-inter2` -/

mutual
/-- The noun of a `need-inter1` over `CSet`. -/
noncomputable def I1.toNounC : I1 CSet → Noun
  | I1.mk ned lok fk => C (C ned.toNoun (HoonSet.toNoun lok)) (I1.forksNounC fk)
/-- The noun of its forks. -/
noncomputable def I1.forksNounC : List (I1 CSet × I1 CSet) → Noun
  | [] => A 0
  | (y, n) :: r => C (C (I1.toNounC y) (I1.toNounC n)) (I1.forksNounC r)
end

/-- A fork of a `need-inter1`. -/
noncomputable def I1.forkN (p : I1 CSet × I1 CSet) : Noun := C (I1.toNounC p.1) (I1.toNounC p.2)

/-- A fork of a `need-inter2`. -/
def I2.forkN (p : I2 × I2) : Noun := C p.1.toNoun p.2.toNoun

theorem I1.forksNounC_eq : ∀ fk : List (I1 CSet × I1 CSet), I1.forksNounC fk = listN (fk.map I1.forkN)
  | [] => rfl
  | (y, n) :: r => by
    simp only [I1.forksNounC, List.map_cons, I1.forkN, I1.forksNounC_eq r]; rfl

theorem I2.forksNoun_eq : ∀ f : List (I2 × I2), I2.forksNoun f = listN (f.map I2.forkN)
  | [] => rfl
  | (y, n) :: r => by
    simp only [I2.forksNoun, List.map_cons, I2.forkN, I2.forksNoun_eq r]; rfl

theorem I1.toNounC_mk (ned : NeedOrd) (lok : CSet) (fk : List (I1 CSet × I1 CSet)) :
    I1.toNounC (I1.mk ned lok fk) = C (C ned.toNoun (HoonSet.toNoun lok)) (I1.forksNounC fk) := by
  rw [I1.toNounC]

theorem I2.toNoun_mk (s : NeedOrd) (f : List (I2 × I2)) : (I2.mk s f).toNoun = C s.toNoun (I2.forksNoun f) := by
  rw [I2.toNoun]

/-- `sureOfS` on `CSet` is `sureOf`. -/
theorem sureOfS_eqC (ned : NeedOrd) (lok : CSet) (less : Cape) : sureOfS ned lok less = sureOf ned lok less := by
  simp only [sureOfS, sureOf, sureStepS_eq]

/-! ## The `+turn` over the forks -/

/-- The gate of the `+turn` over `fork.intr`: the gate again on both branches. -/
def i2TG : Noun :=
  C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 12))) (C (A 0) (A 7))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 13))) (C (A 0) (A 7))))))

/-- The sample bunt of that gate. -/
def i2TB : Noun := C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0)) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0))

/-- `i2Turn` with its gate named. -/
def i2TurnN : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0)
    (A 57)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) i2TB) (C (C (A 1) i2TG) (C (A 0) (A 1))))))))) (C (A 0)
    (A 2))))))))

theorem i2Turn_eq : i2Turn = i2TurnN := rfl

mutual
/-- **`+inter1-to-inter2`** on every `need-inter1`. -/
theorem i12_gate (less : Cape) : ∀ intr : I1 CSet,
    nock (C i2Body (C (C (I1.toNounC intr) less.toNoun) compK)) i2Body = (i12 less intr).map I2.toNoun
  | I1.mk ned lok fk => by
    have hr := i2_rep ned lok (I1.forksNounC fk) less
    have hf := i12_forks less (I1.toNounC (I1.mk ned lok fk)) fk
    have hL := compK_layer2
    have ht := turn_gate_mapM layer2 homoIn_layer2 i2TG i2TB
      (C i2Body (C (C (I1.toNounC (I1.mk ned lok fk)) less.toNoun) compK))
      (fun x => nock (C i2TG (C x (C i2Body (C (C (I1.toNounC (I1.mk ned lok fk)) less.toNoun) compK)))) i2TG)
      (fk.map I1.forkN) (fun _ _ => rfl)
    rw [← I1.forksNounC_eq, hf] at ht
    rw [I1.toNounC_mk] at ht ⊢
    conv => { lhs; arg 2; unfold i2Body }
    rw [nock_op7]
    simp only [nock_op0, slot?_one, Option.bind_some]
    rw [nock_pair _ i2Rep i2Turn ⟨_, _, rfl⟩, hr, i2Turn_eq]
    simp only [i12, sureOfS_eqC]
    cases e : sureOf ned lok less with
    | none => rfl
    | some s =>
      simp only [Option.map_some, Option.bind_some]
      unfold i2TurnN
      generalize i2Body = BD at ht ⊢
      generalize compK = KC at hL ht ⊢
      cases e2 : i12Forks less fk with
      | none =>
        rw [e2] at ht
        simp [nock_exec, hL, turn.arm_at, turn_arm, ht]
      | some f =>
        rw [e2] at ht
        simp [nock_exec, hL, turn.arm_at, turn_arm, ht, I2.toNoun_mk, I2.forksNoun_eq]

/-- The gate of the `+turn` over the forks, on every fork list. -/
theorem i12_forks (less : Cape) (INTR : Noun) : ∀ fk : List (I1 CSet × I1 CSet),
    (fk.map I1.forkN).mapM (fun x => nock (C i2TG (C x (C i2Body (C (C INTR less.toNoun) compK)))) i2TG)
      = (i12Forks less fk).map (List.map I2.forkN)
  | [] => rfl
  | (y, n) :: r => by
    have hy := i12_gate less y
    have hn := i12_gate less n
    have hr := i12_forks less INTR r
    have hg : nock (C i2TG (C (I1.forkN (y, n)) (C i2Body (C (C INTR less.toNoun) compK)))) i2TG
        = (i12 less y).bind fun y' => (i12 less n).map fun n' => C y'.toNoun n'.toNoun := by
      unfold i2TG I1.forkN
      generalize i2Body = BD at hy hn ⊢
      generalize compK = KC at hy hn ⊢
      cases e1 : i12 less y with
      | none => rw [e1] at hy; simp [nock_exec, hy]
      | some y' =>
        cases e2 : i12 less n with
        | none => rw [e2] at hn; rw [e1] at hy; simp [nock_exec, hy, hn]
        | some n' => rw [e2] at hn; rw [e1] at hy; simp [nock_exec, hy, hn]
    simp only [List.map_cons, List.mapM_cons, hg, hr, i12Forks]
    cases i12 less y <;> cases i12 less n <;> cases i12Forks less r <;> simp [I2.forkN]
end

end Compiler
end Formalization
