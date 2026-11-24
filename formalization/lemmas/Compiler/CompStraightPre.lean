import lemmas.Compiler.CompUnaryTop
import lemmas.Compiler.CompCopyLink

/-!
# The pushes of `+to-straight` before its `|^` core

The gate battery `tsBat` of `+to-straight` (door arm `6892`) is thirteen
pushes and a call: `[8 F1 [8 F2 ... [8 [1 CORE] [9 190 0 1]]]]`.  Here it is
cut into its rests `tsR2`, ..., `tsR13` (`ts_bat_eq`, a kernel fact), the
pushed gates `tsUnBat` (`unproxy`), `tsRunTrap` (the trap `run`),
`tsRenBat` (`ren`) written out, and the battery `tsCoreBat` of the `|^`
core read from the pill (`slot? 268435453 tsBat`).

The pushes, in order: `blocks` (`[0 990]`, axis `62` of the state), the
gate `unproxy` (built, never run here), `proxies` (`[6 [5 [1 0] [0
0x3f7e]] [1 1] [1 0]]`, `|` when `cond` is `~`), `ins` (`+flatten-need` of
`ned.nex`, door arm `220`), `r0` (`?~(ins 0 i.ins)`), `n-in` (`+lent`,
arm `0x2fbd5` of the library), `run` (the trap, with `+add`), the gate
`ren` (built), `start` (`+got:by` of `then.nex`), the edits of `blocks` by
`+del:by` and `+put:by` at `0`, the bunt `[0 0]` of `[re-gen m]`, and the
core.

On the fragment's sample `[%next [[this+sub ~] ~ ~] ~ o]` with `cond`
empty: `ts_pre1` (pushes 1 to 5), `ts_pre2` (6 to 8: `n-in` is `1`, `run`
is `&`), `ts_pre3` (9 to 13), and `ts_pre` chains them from the state of
the door to the call of arm `190` of the core (`tsCoreSt`), with the
blocks of the model `HoonMap.put (HoonMap.del g.blocks o) 0 start`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The battery of the gate `unproxy`. -/
def tsUnBat : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0xff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 0) (A 14)) (C (A 0) (A 10)))))))

/-- The trap `run`: `?~  ins  &`, `?.  =(i.ins (add r0 i))  |`, recur. -/
def tsRunTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 62)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 124)) (C (A 8) (C (C (A 9) (C (A 36) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 125))) (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 6)))) (C (A 0) (A 1)))))))) (C (A 1) (A 1))))))))

/-- The battery of the gate `ren`. -/
def tsRenBat : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 126)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 36) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 62)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 36) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 0) (A 62)))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 79) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 126)))) (C (A 0) (A 2)))))))) (C (A 0) (A 6))))))))

/-- The battery of the `|^` core, read from the pill. -/
noncomputable def tsCoreBat : Noun := (slot? 268435453 tsBat).getD (A 0)

noncomputable def tsR13 : Noun := C (A 8) (C (C (A 1) tsCoreBat) (C (A 9) (C (A 190) (C (A 0) (A 1)))))
noncomputable def tsR12 : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) tsR13)
noncomputable def tsR11 : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) tsR12)
noncomputable def tsR10 : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfff7))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) tsR11)
noncomputable def tsR9 : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7))) (C (A 0) (A 2)))))))) tsR10)
noncomputable def tsR8 : Noun := C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) tsRenBat) (C (A 0) (A 1))))) tsR9)
noncomputable def tsR7 : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) tsRunTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) tsR8)
noncomputable def tsR6 : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) tsR7)
noncomputable def tsR5 : Noun :=
  C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 0) (A 4))))) tsR6)
noncomputable def tsR4 : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2024))) (C (A 0) (A 2)))))))) tsR5)
noncomputable def tsR3 : Noun :=
  C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0x3f7e)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) tsR4)
noncomputable def tsR2 : Noun := C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) tsUnBat) (C (A 0) (A 1))))) tsR3)

/-- **The gate of `+to-straight` cut into its pushes**, a kernel fact. -/
theorem ts_bat_eq : tsBat = C (A 8) (C (C (A 0) (A 990)) tsR2) := by kernel_rfl

/-- `+flatten-need` on `this+sub` is `[sub ~]`. -/
theorem ts_fn_this (sub : Nat) (d : Noun) :
    nock (C fnBat (C (C (A 0x73696874) (A sub)) d)) fnBat = some (C (A sub) (A 0)) := by
  unfold fnBat; simp [nock_exec]

/-- The subject after the first five pushes (`blocks` twice: the face `B`,
edited later, and the copy `Bo` in the context of `unproxy`). -/
def tsS5 (B Bo S0 : Noun) (sub : Nat) : Noun :=
  C (A sub) (C (C (A sub) (A 0)) (C (A 1) (C (C tsUnBat (C (A 0) (C Bo S0))) (C B S0))))

/-- The subject after `run`. -/
def tsS7 (B Bo S0 : Noun) (sub : Nat) : Noun := C (A 0) (C (A 1) (tsS5 B Bo S0 sub))

/-- The subject of the gate on the fragment's sample. -/
noncomputable def tsS0 (D G ctx : Noun) (o sub : Nat) : Noun := C tsBat (C (tsSample (A o) (A sub)) (C D (C G ctx)))

/-- **Pushes 1 to 5**: `blocks`, `unproxy`, `proxies` (`|`: `cond` is `~`),
`ins` (`[sub ~]`, `+flatten-need`), `r0` (`sub`). -/
theorem ts_pre1 (D G ctx BN : Noun) (o sub : Nat) (hb : slot? 62 G = some BN)
    (hcd : slot? 254 G = some (A 0)) (hD : slot? 220 D = some fnArm) :
    nock (tsS0 D G ctx o sub) tsBat = nock (tsS5 BN BN (tsS0 D G ctx o sub) sub) tsR6 := by
  conv => { lhs; arg 2; rw [ts_bat_eq] }
  have hf := ts_fn_this sub (C D (C G ctx))
  unfold tsR2 tsR3 tsR4 tsR5
  simp only [tsS0, tsS5, tsSample] at hf ⊢
  generalize tsBat = T at hf ⊢
  simp [nock_exec, hb, hcd, hD, comp_fn_arm, hf]

/-- `layer1` sits one step below `layer2` in the context. -/
theorem ts_layer1 {ctx : Noun} (hc : CompIn ctx) : slot? 524287 ctx = some layer1 := by
  have h1 : slot? 262143 ctx = slot? 1 layer2 := hc
  have := slot_spine (by omega) (by omega) h1 1
  simp only [show 2 ^ 1 * (262143 + 1) - 1 = 524287 from rfl,
    show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  rw [this]; exact layer2_layer1

/-- **Pushes 6 to 8**: `n-in` is `1` (`+lent`), the trap `run` gives `&`
(one step with `+add`, then `~`), the gate `ren` is built. -/
theorem ts_pre2 {ctx : Noun} (hc : CompIn ctx) (D G BN : Noun) (o sub : Nat) :
    nock (tsS5 BN BN (tsS0 D G ctx o sub) sub) tsR6
      = nock (C (C tsRenBat (C (A 0) (tsS7 BN BN (tsS0 D G ctx o sub) sub)))
          (tsS7 BN BN (tsS0 D G ctx o sub) sub)) tsR9 := by
  have hl := lent_gate layer2 [A sub]
  have hadd := add_gate layer1 decIn_layer1 sub 0
  have hl1 := ts_layer1 hc
  simp only [listN, appendN, List.length_singleton] at hl
  unfold tsR6 tsR7 tsR8
  simp only [tsS0, tsS5, tsS7, tsSample]
  generalize tsBat = T
  simp [nock_exec, hc, hl1, lent.arm_at, lent_arm, hl, add.arm_at, add_arm, hadd, tsRunTrap]

/-- The `|^` core on the subject after the pushes: the bunt `[0 0]` of
`[re-gen m]`, `start`, `ren`, and the subject of `run` with the face
`blocks` edited to `B`. -/
noncomputable def tsCoreSt (SB REN B Bo S0 : Noun) (sub : Nat) : Noun :=
  C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (tsS7 B Bo S0 sub))))

/-- **Pushes 9 to 13**: `start` (`+got:by` of `then.nex`), `blocks` edited by
`+del:by` and `+put:by` at `0`, the bunt, the core, and the call of its arm
`190`.  The three map facts are on the nouns (`got_gate`, `del_gate`,
`put_gate`). -/
theorem ts_pre3 {ctx : Noun} (hc : CompIn ctx) (D G BN SB BN1 BN2 REN : Noun) (o sub : Nat)
    (hget : getF mugF (A o) BN = some (C (A 0) SB)) (hdel : delF mugF (A o) BN = some BN1)
    (hput : putF mugF (A 0) SB BN1 = some BN2) :
    nock (C REN (tsS7 BN BN (tsS0 D G ctx o sub) sub)) tsR9
      = nock (tsCoreSt SB REN BN2 BN (tsS0 D G ctx o sub) sub) (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgot := got_gate layer2 hgc (A o) BN SB hget
  have hd := del_gate layer2 gorIn_morIn_layer2 (A o) BN BN1 hdel
  have hp := put_gate layer2 gorIn_morIn_layer2 (A 0) SB BN1 BN2 hput
  unfold tsR9 tsR10 tsR11 tsR12 tsR13
  simp only [tsCoreSt, tsS0, tsS5, tsS7, tsSample]
  generalize tsBat = T
  generalize tsCoreBat = K
  simp [nock_exec, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, by.del.arm_at, del_arm, hd,
    by.put.arm_at, put_arm, hp]

/-- `+got:by` crashes when `then.nex` is not a block. -/
theorem ts_pre3_nil {ctx : Noun} (hc : CompIn ctx) (D G BN REN : Noun) (o sub : Nat)
    (hget : getF mugF (A o) BN = some (A 0)) :
    nock (C REN (tsS7 BN BN (tsS0 D G ctx o sub) sub)) tsR9 = none := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgot := got_gate_nil layer2 hgc (A o) BN hget
  unfold tsR9
  simp only [tsS0, tsS5, tsS7, tsSample]
  generalize tsBat = T
  generalize tsR10 = R
  simp [nock_exec, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot]

/-- A map with no key is `~`. -/
theorem ts_map_nil {ν : Type} (f : ν → Noun) (m : TreapMap mugF ν)
    (h : ∀ k, HoonMap.get m k = Option.none) : HoonMap.toNoun f m = A 0 := by
  rw [hoonMap_toNoun]
  have hk : ∀ k, m.1.get mugF k = Option.none := fun k => by rw [← hoonMap_get]; exact h k
  generalize m.1 = t at hk ⊢
  cases t with
  | nil => rfl
  | node k v l r =>
    have := hk k
    simp [Tr.get] at this

/-- **The pushes of `+to-straight`** on the fragment's sample with `cond`
empty: the gate is the call of arm `190` of its `|^` core, on the blocks
`HoonMap.put (HoonMap.del g.blocks o) 0 start`, or a crash when `o` is not a
block (where `toStraightF` is `none`). -/
theorem ts_pre {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o sub : Nat)
    (hcond : ∀ k, HoonMap.get g.cond k = Option.none) :
    nock (C tsBat (C (tsSample (A o) (A sub)) (compCore g x ctx))) tsBat
      = (HoonMap.get g.blocks o).bind fun start =>
          nock (tsCoreSt (Blob.toNoun start)
            (C tsRenBat (C (A 0) (tsS7 (HoonMap.toNoun Blob.toNoun g.blocks)
              (HoonMap.toNoun Blob.toNoun g.blocks) (tsS0 comp.door (genNoun g x) ctx o sub) sub)))
            (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
            (HoonMap.toNoun Blob.toNoun g.blocks) (tsS0 comp.door (genNoun g x) ctx o sub) sub)
            (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  have hb := genNoun_blocks g x
  have hcd : slot? 254 (genNoun g x) = some (A 0) := by
    simp only [genNoun, nock_exec, ts_map_nil condValNoun g.cond hcond]
  have h1 := ts_pre1 comp.door (genNoun g x) ctx _ o sub hb hcd comp_fn_at
  have h2 := ts_pre2 hc comp.door (genNoun g x) (HoonMap.toNoun Blob.toNoun g.blocks) o sub
  have hget := getF_hoonMap Blob.toNoun g.blocks o
  simp only [compCore]
  change nock (tsS0 comp.door (genNoun g x) ctx o sub) tsBat = _
  rw [h1, h2]
  cases e : HoonMap.get g.blocks o with
  | none =>
    rw [e] at hget
    exact ts_pre3_nil hc _ _ _ _ o sub hget
  | some start =>
    rw [e] at hget
    exact ts_pre3 hc _ _ _ _ _ _ _ o sub hget (delF_hoonMap Blob.toNoun g.blocks o)
      (putF_hoonMap Blob.toNoun (HoonMap.del g.blocks o) 0 start)

end Compiler
end Formalization
