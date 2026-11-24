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

/-! ## `+walk-lazy` on `[sure ~ ~]`

`+walk-lazy` (door axis `30`, core axis `46`) slams its gate `f` on `[o
sure.laz gen]`, puts the product in `gen`, and on `fork.laz = ~`,
`bond.laz = ~` returns it.  The model `walkLazy` of `Ska/CompLazyArms.lean`
does the same (`f o s`, then `pure ()`), and `mede` of `Ska/CompModel.lean`
inlines that single call.
-/

def mdLoop : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 0) (A 1022)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 1018)) (C (A 0) (A 13)))) (C (A 1) (A 0))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 1018))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 9) (C (A 0xaaae) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 1018)))))) (C (A 0) (A 14))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1018) (C (A 0) (A 2036))) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1018) (C (A 0) (A 2037))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 1018))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 9) (C (A 0xaaae) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 1018)))))) (C (A 0) (A 14))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 1018)) (C (A 0) (A 26)))) (C (A 1) (A 0))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1018) (C (A 0) (A 2036))) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1018) (C (A 0) (A 2037))) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 1))))))))))))))))))))))))))

def mdGate : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 27))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1399) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 1) mdLoop) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))

def mdBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 28)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 15)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 62))) (C (C (A 0) (A 2)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 123)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (C (A 7) (C (C (A 9) (C (A 4) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 62)))) (C (C (A 1) mdGate) (C (A 0) (A 1)))))))))) (C (A 0) (A 2))))))))))))))))))))

def mdArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0) (A 0)) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) mdBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6564656d2d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

def wlBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 0) (A 27)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 0) (A 116)) (C (A 0) (A 62))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 106)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 107)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 30))) (C (C (A 1) (C (A 7) (C (C (A 10) (C (C (A 13) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 13))) (C (A 10) (C (C (A 26) (C (A 0) (A 49))) (C (A 10) (C (C (A 12) (C (A 0) (A 48))) (C (A 0) (A 7))))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 13))) (C (A 10) (C (C (A 26) (C (A 0) (A 51))) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 7))))))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 30))) (C (C (A 1) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 13))) (C (A 10) (C (C (A 26) (C (A 0) (A 25))) (C (A 10) (C (C (A 12) (C (A 0) (A 24))) (C (A 0) (A 7))))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))))))

def wlArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (C (A 1) (A 0)) (C (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 7) (C (C (C (C (A 1) (A 0)) (C (C (A 7) (C (C (A 9) (C (A 4) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 6)))) (C (A 0) (A 6))) (C (A 8) (C (C (A 0) (A 2)) (C (C (A 1) (C (A 0) (A 15))) (C (A 0) (A 1))))))))) (C (C (A 1) wlBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x797a616c2d6b6c61772d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))


/-- `+walk-lazy` is at door axis `30` (core axis `46`). -/
theorem comp_wl_at : slot? 30 comp.door = some wlArm := by kernel_rfl

/-- `+mede` is at door axis `27307` (core axis `43691`). -/
theorem comp_md_at : slot? 27307 comp.door = some mdArm := by kernel_rfl

/-- `+walk-lazy` on `[s ~ ~]` is one slam of its gate `[Fb [Fs Fc]]`. -/
theorem comp_walk_lazy (Fb Fs Fc G : Noun) (o : Nat) (s : Sure CSet) (out : Option Noun)
    (hf : nock (C Fb (C (C (A o) (C s.toNoun G)) Fc)) Fb = out) :
    nock (C wlBat (C (C (A o) (C (lazyNoun s) (C Fb (C Fs Fc)))) (C comp.door (C G ctx)))) wlBat
      = out := by
  unfold wlBat
  cases out with
  | none => simp [nock_exec, lazyNoun, hf]
  | some R => simp [nock_exec, lazyNoun, hf]

/-! ## The loop of `+mede` -/

/-- The subject of the loop of the gate of `+mede`: the need, the gate with
its sample `[o' sur gen-init]`, and the context of the gate (`o` and the
gate of `+mede` with `som` in its sample). -/
def mdT (x : GenRest) (ctx SUR GI B TH LAZ : Noun) (o o' : Nat) (ned : Need) (som : Noun)
    (g : Gen (TreapMap mugF)) : Noun :=
  C mdLoop (C ned.toNoun (C mdGate (C (C (A o') (C SUR GI)) (C (A o) (C B (C (C TH (C som LAZ))
    (C comp.door (C (genNoun g x) ctx))))))))

/-- The loop of `+mede` is `medeLoop`, where the block `o'` is not a key of
`soft`. -/
theorem md_loop (hc : CompIn ctx) (x : GenRest) (SUR GI B TH LAZ : Noun) (o o' : Nat)
    (hs : x.SoftOut o') : ∀ (ned : Need) (som : Noun) (g : Gen (TreapMap mugF)),
    nock (mdT x ctx SUR GI B TH LAZ o o' ned som g) mdLoop
      = (medeLoop o' som ned g).map fun p => genNoun p.2 x := by
  have hD2 := comp_add_ops_at
  have hD4 := comp_crn_at
  intro ned
  induction ned with
  | none =>
    intro som g
    nock_open mdLoop
    simp [nock_exec, mdT, Need.toNoun, Tag.none, medeLoop, pure, StateT.pure]
  | this r =>
    intro som g
    have hao := comp_add_ops x hc g o' [Pole.imm som r]
    simp only [listNoun, Pole.toNoun, Tag.imm] at hao
    simp only [compCore] at hao
    unfold mdT
    nock_open mdLoop
    generalize comp.door = Dr at hD2 hD4 hao ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, medeLoop, hD2, comp_add_ops_arm, hao]
  | pair p q ihp ihq =>
    intro som g
    obtain ⟨u, v, hp⟩ := cd_need_cell p
    cases som with
    | atom n =>
      have hcr := comp_crash_need hc x g o' (Sum.inl n) (Need.pair p q) hs
      simp only [compCore, crnAtomNoun, Need.toNoun, hp] at hcr
      unfold mdT
      nock_open mdLoop
      generalize comp.door = Dr at hD2 hD4 hcr ⊢
      simp [nock_exec, Need.toNoun, hp, Tag.none, Tag.this, medeLoop, hD4, comp_crn_arm, hcr]
    | cell a b =>
      have h1 := ihp a g
      simp only [mdT, Need.toNoun, hp] at h1
      cases e1 : medeLoop o' a p g with
      | none =>
        rw [e1] at h1
        nock_open mdLoop
        simp [nock_exec, mdT, Need.toNoun, hp, Tag.none, Tag.this, medeLoop, h1, e1, bind,
          StateT.bind]
      | some r1 =>
        obtain ⟨u1, g1⟩ := r1
        rw [e1] at h1
        have h2 := ihq b g1
        simp only [mdT, Need.toNoun] at h2
        nock_open mdLoop
        simp [nock_exec, mdT, Need.toNoun, hp, Tag.none, Tag.this, medeLoop, h1, e1, h2, bind,
          StateT.bind]
  | both r h t ihh iht =>
    intro som g
    cases som with
    | atom n =>
      have hcr := comp_crash_need hc x g o' (Sum.inl n) (Need.both r h t) hs
      simp only [compCore, crnAtomNoun, Need.toNoun, Tag.both] at hcr
      unfold mdT
      nock_open mdLoop
      generalize comp.door = Dr at hD2 hD4 hcr ⊢
      simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, medeLoop, hD4, comp_crn_arm,
        hcr]
    | cell a b =>
      have hao := comp_add_ops x hc g o' [Pole.imm (C a b) r]
      simp only [listNoun, Pole.toNoun, Tag.imm] at hao
      simp only [compCore] at hao
      cases e0 : addOps (Map := TreapMap mugF) o' [Pole.imm (C a b) r] g with
      | none =>
        rw [e0] at hao
        unfold mdT
        nock_open mdLoop
        generalize comp.door = Dr at hD2 hD4 hao ⊢
        simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, medeLoop, hD2, comp_add_ops_arm,
          hao, e0, bind, StateT.bind]
      | some r0 =>
        obtain ⟨u0, g0⟩ := r0
        rw [e0] at hao
        have h1 := ihh a g0
        simp only [mdT] at h1
        cases e1 : medeLoop o' a h g0 with
        | none =>
          rw [e1] at h1
          unfold mdT
          nock_open mdLoop
          generalize comp.door = Dr at hD2 hD4 hao h1 ⊢
          simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, medeLoop, hD2, comp_add_ops_arm,
            hao, e0, h1, e1, bind, StateT.bind]
        | some r1 =>
          obtain ⟨u1, g1⟩ := r1
          rw [e1] at h1
          have h2 := iht b g1
          simp only [mdT] at h2
          unfold mdT
          nock_open mdLoop
          generalize comp.door = Dr at hD2 hD4 hao h1 h2 ⊢
          simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, medeLoop, hD2, comp_add_ops_arm,
            hao, e0, h1, e1, h2, bind, StateT.bind]

end Compiler
end Formalization
