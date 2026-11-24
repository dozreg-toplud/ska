import lemmas.Compiler.CompCopyLink

/-!
# `+crash-need`, `+mede`, `+lazy-bound` and `+proxy` of the door of `+comp`

`+crash-need` (door axis `27310`, core axis `43694`, no hint) adds to block
`o` a `%cel` of the atom (an immediate put in a fresh register, or a
register) and a zero into each register of the need: the fetch crashes
there.  It tests `(~(has by soft.gen) o)` in both branches: the link takes
the branch where `o` is not a key of `soft` (`GenRest.SoftOut`), where the
pill runs `+add-ops` as the model does, and otherwise the pill runs
`+soft-ask`, which has no model.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ctx : Noun}

/-! ## `+crash-need` -/

def crnG : Noun :=
  (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 6))))

def crnBat : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) crnG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 116)))) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x2aabe) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 245)) (C (A 0) (A 123))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 117))) (C (A 0) (A 2))))))) (C (A 0) (A 2))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 116))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x2aabe) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 491)) (C (A 0) (A 2)))) (C (A 1) (A 0))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 31)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 6)) (C (A 0) (A 251))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 491)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 2))) (C (A 0) (A 6)))))))) (C (A 0) (A 2))))))))))))))))))))))))))

def crnArm : Noun :=
  (C (A 8) (C (C (A 1) (C (A 0) (C (C (A 0) (C (A 0x6d6d69) (A 0))) (C (A 0x656e6f6e) (A 0))))) (C (C (A 1) crnBat) (C (A 0) (A 1)))))


/-- `+crash-need` is at door axis `27310` (core axis `43694`). -/
theorem comp_crn_at : slot? 27310 comp.door = some crnArm := by kernel_rfl

/-- The arm `crash-need` builds its gate. -/
theorem comp_crn_arm (d : Noun) : nock d crnArm =
    some (C crnBat (C (C (A 0) (C (C (A 0) (C (A 0x6d6d69) (A 0))) (C (A 0x656e6f6e) (A 0)))) d)) := by
  unfold crnArm; simp only [nock_exec]

/-- The sample `atom=(each [%imm n=@] @uvre)` of `+crash-need`. -/
def crnAtomNoun : Sum Nat Nat → Noun
  | Sum.inl n => C (A 0) (C (A 0x6d6d69) (A n))
  | Sum.inr r => C (A 1) (A r)

/-- The `+turn` of `+crash-need`: a zero into each register. -/
theorem crn_fill (ned : Need) (bc : Noun) :
    nock (C turn.battery (C (C (listNoun A (flattenNeed ned)) (C crnG (C (A 0) bc))) layer2))
      turn.battery = some (listNoun Pole.toNoun ((flattenNeed ned).map fun y => Pole.imm (A 0) y)) := by
  rw [cd_listNoun_listN, cd_listNoun_listN,
    turn_gate layer2 homoIn_layer2 crnG (A 0) bc (fun y => C (A 0x6d6d69) (C (A 0) y)) _
      (fun y _ => by unfold crnG; simp [nock_exec])]
  simp [List.map_map, Function.comp_def, Pole.toNoun, Tag.imm]

/-- `+has:by` on `soft` at a key it lacks. -/
theorem crn_has (x : GenRest) (o : Nat) (hs : x.SoftOut o) :
    nock (C by.has.battery (C (A o) (C by.battery (C x.soft layer2)))) by.has.battery
      = some (A 1) := by
  rw [has_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A o) x.soft (A 0) hs]
  rfl

/-- `+crash-need`, where `o` is not a key of `soft`: the model's ops added to
block `o` (`got` crashes on a missing block, where the model is `none`). -/
theorem comp_crash_need (hc : CompIn ctx) (x : GenRest) (g : Gen (TreapMap mugF)) (o : Nat)
    (atom : Sum Nat Nat) (ned : Need) (hs : x.SoftOut o) :
    nock (C crnBat (C (C (A o) (C (crnAtomNoun atom) ned.toNoun)) (compCore g x ctx))) crnBat
      = (crashNeed o atom ned g).map fun p => genNoun p.2 x := by
  have hfn := comp_flatten_need hc (genNoun g x) ned
  have hD1 := comp_fn_at
  have hD2 := comp_add_ops_at
  have hD3 := comp_re_at
  have hfill := crn_fill ned
  have hhas := crn_has x o hs
  cases atom with
  | inr r =>
    have hao := comp_add_ops x hc g o (Pole.cel r :: (flattenNeed ned).map fun y => Pole.imm (A 0) y)
    simp only [listNoun, Pole.toNoun, Tag.cel] at hao
    simp only [compCore] at hfn hao ⊢
    unfold crnBat
    generalize comp.door = Dr at hD1 hD2 hD3 hfn hao ⊢
    simp [nock_exec, crnAtomNoun, hD1, comp_fn_arm, hfn, hc, turn_arm, turn.arm_at, hfill, by_arm,
      by.arm_at, by.has.arm_at, has_arm, hhas, hD2, comp_add_ops_arm, hao, crashNeed]
  | inl n =>
    have hre := comp_re' ctx x g
    have hao := comp_add_ops x hc { g with re := g.re + 1 } o
      (Pole.imm (A n) g.re :: Pole.cel g.re :: (flattenNeed ned).map fun y => Pole.imm (A 0) y)
    simp only [listNoun, Pole.toNoun, Tag.cel, Tag.imm] at hao
    simp only [compCore] at hfn hao ⊢
    unfold crnBat
    generalize comp.door = Dr at hD1 hD2 hD3 hfn hao hre ⊢
    simp [nock_exec, crnAtomNoun, hD1, comp_fn_arm, hfn, hc, turn_arm, turn.arm_at, hfill, by_arm,
      by.arm_at, by.has.arm_at, has_arm, hhas, hD2, comp_add_ops_arm, hao, crashNeed, listNoun, Pole.toNoun, hD3, hre, re, bind, StateT.bind]

end Compiler
end Formalization
