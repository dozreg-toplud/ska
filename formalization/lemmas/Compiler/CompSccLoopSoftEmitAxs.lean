import lemmas.Compiler.CompSccLoopSoftEmitBase

/-! # `+soft-axes` in the pill: the push `seAxs` of `+soft-emit` (README Gaps 21.17)

`+soft-axes` (line 5533, battery axis 6910 of the door `comp`, core axis `0x2afe`, 212 cells) is
the gate `[8 [1 saBunt] [1 saGBat] [0 1]]`; `saGBat` pushes `m` (`~`), `axe` (`1`) and the
trap `saTrap`, and runs it.  The trap's subject is `[saTrap [axe [m [saGBat [ned core]]]]]`.

* `sa_at`: the arm in the pill;
* `sa_trap`: the trap computes a map noun whose pairs are those of `softAxes ned axe l` from
  one whose pairs are those of `l` (`AxsRel`), with `+put:by` and `+peg`;
* **`se_axs`**: the push `seAxs` of `+soft-emit` on the gate's subject. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The trap of `+soft-axes`. -/
def saTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 124)))) (C (C (A 0) (A 14)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 124)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 124))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 125))) (C (A 10) (C (C (A 14) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 124))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 3)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 124))))) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 506)) (C (A 0) (A 14)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 503))) (C (A 10) (C (C (A 14) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 502))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 3)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))))))))))))))))

/-- The battery of the gate `+soft-axes`: `=|  m`, `=/  axe  1`, the trap. -/
def saGBat : Noun :=
  C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) saTrap)
    (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))

/-- `+soft-axes`: the gate `[8 [1 bunt] [1 saGBat] [0 1]]`. -/
def saArm : Noun :=
  C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) saGBat) (C (A 0) (A 1))))

/-- `+soft-axes` in the pill (battery axis 6910 of the door). -/
theorem sa_at : slot? 6910 comp.door = some saArm := by kernel_rfl

theorem sa_toNoun_cell (n : Need) : ∃ a b, n.toNoun = C a b := by
  cases n <;> exact ⟨_, _, rfl⟩

/-- **The trap of `+soft-axes`.** -/
theorem sa_trap {ctx : Noun} (hc : CompIn ctx) (Dr G : Noun) :
    ∀ (ned : Need) (axe : Nat) (Mm : Noun) (l : List (Nat × Nat)), 1 ≤ axe → AxsRel Mm l →
    ∃ M, nock (C saTrap (C (A axe) (C Mm (C saGBat (C ned.toNoun (C Dr (C G ctx))))))) saTrap
        = some M ∧ AxsRel M (softAxes ned axe l) := by
  have hl1 := cf_layer1 hc
  intro ned
  induction ned with
  | none =>
    intro axe Mm l _ hM
    refine ⟨Mm, ?_, hM⟩
    conv => { lhs; arg 2; unfold saTrap }
    simp [nock_exec, Need.toNoun, Tag.none]
  | this r =>
    intro axe Mm l _ hM
    obtain ⟨M', hput, hM'⟩ := axsRel_put hM r axe
    have hp := put_gate layer2 gorIn_morIn_layer2 (A r) (A axe) Mm M' hput
    refine ⟨M', ?_, hM'⟩
    conv => { lhs; arg 2; unfold saTrap }
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hc, by_arm, by.arm_at, by.put.arm_at, put_arm, hp]
  | pair h t ih1 ih2 =>
    intro axe Mm l ha hM
    have hp2 := peg_gate layer1 cf_arith axe ha 2 (by decide)
    have hp3 := peg_gate layer1 cf_arith axe ha 3 (by decide)
    have h2 : 1 ≤ pegF axe 2 := pegF_pos axe ha 2 (by decide)
    have h3 : 1 ≤ pegF axe 3 := pegF_pos axe ha 3 (by decide)
    obtain ⟨M1, e1, hM1⟩ := ih1 (pegF axe 2) Mm l h2 hM
    obtain ⟨M2, e2, hM2⟩ := ih2 (pegF axe 3) M1 _ h3 hM1
    refine ⟨M2, ?_, hM2⟩
    obtain ⟨a, b, hab⟩ := sa_toNoun_cell h
    rw [hab] at e1
    conv => { lhs; arg 2; unfold saTrap }
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hab, hl1, peg_arm, peg.arm_at, hp2, hp3, e1, e2]
  | both r h t ih1 ih2 =>
    intro axe Mm l ha hM
    have hp2 := peg_gate layer1 cf_arith axe ha 2 (by decide)
    have hp3 := peg_gate layer1 cf_arith axe ha 3 (by decide)
    have h2 : 1 ≤ pegF axe 2 := pegF_pos axe ha 2 (by decide)
    have h3 : 1 ≤ pegF axe 3 := pegF_pos axe ha 3 (by decide)
    obtain ⟨M', hput, hM'⟩ := axsRel_put hM r axe
    have hp := put_gate layer2 gorIn_morIn_layer2 (A r) (A axe) Mm M' hput
    obtain ⟨M1, e1, hM1⟩ := ih1 (pegF axe 2) M' _ h2 hM'
    obtain ⟨M2, e2, hM2⟩ := ih2 (pegF axe 3) M1 _ h3 hM1
    refine ⟨M2, ?_, hM2⟩
    conv => { lhs; arg 2; unfold saTrap }
    simp [nock_exec, nock_op11_cell, Need.toNoun, Tag.none, Tag.this, Tag.both, hc, by_arm, by.arm_at,
      by.put.arm_at, put_arm, hp, hl1, peg_arm, peg.arm_at, hp2, hp3, e1, e2]

/-- **The push `seAxs`**: `(soft-axes ned.s)` on the gate's subject, a map noun whose pairs are
those of `softAxes s.ned 1 []`. -/
theorem se_axs (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall) :
    ∃ M, nock (seS0 g x ctx o s) seAxs = some M ∧ AxsRel M (softAxes s.ned 1 []) := by
  have hA := sa_at
  obtain ⟨M, e, hM⟩ := sa_trap hc comp.door (genNoun g x) s.ned 1 (A 0) [] (Nat.le_refl 1) axsRel_nil
  refine ⟨M, ?_, hM⟩
  simp only [seS0, compCore] at e ⊢
  generalize comp.door = Dr at hA e
  generalize genNoun g x = GN at e
  simp [nock_exec, seAxs, saArm, saGBat, Compiler.SoftCall.toNoun, hA]
  simpa only [saGBat] using e

end Compiler
end Formalization
