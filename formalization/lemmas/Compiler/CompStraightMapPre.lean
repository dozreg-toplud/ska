import lemmas.Compiler.CompStraightMapTop

/-!
# The pushes of `+to-straight` with any `proxies`

Written by `tools/gen/tsmpre.py` (README Gaps 20).  The third push of the
gate is `proxies`, `?:(=(~ cond.gen) | &)`: `(A 1)` when the noun of `cond`
is `~` (`tsS5N`, `CompStraightN.lean`), `(A 0)` when it is a cell.  Here the
states with the noun `PX` of `proxies` as a parameter (`tsS5P`, `tsS7P`,
`tsCoreStP`), pushes 1 to 5 with `cond` a cell (`tsnp_pre1`), and the lemmas
of `CompStraightN.lean` that do not read `proxies`, copied with `PX`
(`tsnp_r_layer1`, `tsnp_pre2`, `tsnp_ren`, `tsnp_pre3`, `tsnp_pre3_nil`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The subject after the first five pushes, `proxies` being `PX`. -/
def tsS5P (PX B Bo S0 : Noun) (r0 : Nat) (INS : Noun) : Noun :=
  C (A r0) (C INS (C PX (C (C tsUnBat (C (A 0) (C Bo S0))) (C B S0))))

/-- The subject after `run`. -/
def tsS7P (PX B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) : Noun :=
  C RUN (C (A n) (tsS5P PX B Bo S0 r0 INS))

/-- The `|^` core. -/
noncomputable def tsCoreStP (PX SB REN B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) : Noun :=
  C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (tsS7P PX B Bo S0 r0 INS n RUN))))

theorem tsS5N_eq_P (B Bo S0 : Noun) (r0 : Nat) (INS : Noun) : tsS5N B Bo S0 r0 INS = tsS5P (A 1) B Bo S0 r0 INS := rfl

theorem tsCoreStN_eq_P (SB REN B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) :
    tsCoreStN SB REN B Bo S0 r0 INS n RUN = tsCoreStP (A 1) SB REN B Bo S0 r0 INS n RUN := rfl

/-! ## The pushes -/

/-- **Pushes 1 to 5** on any need with `cond` a cell (`proxies` is `&`): `ins` is `flattenNeed ned`, `r0` its
head or `0`. -/
theorem tsnp_pre1 {ctx : Noun} (hc : CompIn ctx) (G BN : Noun) (o : Nat) (ned : Need)
    (hb : slot? 62 G = some BN) (ca cb : Noun) (hcd : slot? 254 G = some (C ca cb)) :
    nock (tsS0N comp.door G ctx o ned.toNoun) tsBat
      = nock (tsS5P (A 0) BN BN (tsS0N comp.door G ctx o ned.toNoun) ((flattenNeed ned).headD 0)
          (listNoun A (flattenNeed ned))) tsR6 := by
  conv => { lhs; arg 2; rw [ts_bat_eq] }
  have hf := comp_flatten_need hc G ned
  have hD := comp_fn_at
  unfold tsR2 tsR3 tsR4 tsR5
  simp only [tsS0N, tsS5P, tsSampleN] at hf ⊢
  generalize ned.toNoun = NED at hf ⊢
  generalize flattenNeed ned = l at hf ⊢
  generalize tsBat = T at hf ⊢
  generalize comp.door = Dr at hf hD ⊢
  cases l with
  | nil => simp [nock_exec, hb, hcd, hD, comp_fn_arm, hf, listNoun]
  | cons r rs => simp [nock_exec, hb, hcd, hD, comp_fn_arm, hf, listNoun]

/-- `layer1` in the rest of the subject of `run`. -/
theorem tsnp_r_layer1 {ctx : Noun} (hc : CompIn ctx) (PX B Bo D G : Noun) (o : Nat) (NED : Noun) :
    slot? 0x3ffffff (C PX (C (C tsUnBat (C (A 0) (C Bo (tsS0N D G ctx o NED)))) (C B (tsS0N D G ctx o NED))))
      = some layer1 := by
  have hl1 := ts_layer1 hc
  simp only [tsS0N]
  generalize tsBat = T
  simp [nock_exec, hl1]

/-- **Pushes 6 to 8**: `n-in` is the length of `ins` (`+lent`), the trap
`run` gives `isRun ins r0 0`, the gate `ren` is built. -/
theorem tsnp_pre2 {ctx : Noun} (hc : CompIn ctx) (PX D G BN : Noun) (o : Nat) (NED : Noun) (r0 : Nat)
    (l : List Nat) :
    nock (tsS5P PX BN BN (tsS0N D G ctx o NED) r0 (listNoun A l)) tsR6
      = nock (C (C tsRenBat (C (A 0) (tsS7P PX BN BN (tsS0N D G ctx o NED) r0 (listNoun A l) l.length
            (loob (isRun l r0 0)))))
          (tsS7P PX BN BN (tsS0N D G ctx o NED) r0 (listNoun A l) l.length (loob (isRun l r0 0)))) tsR9 := by
  have hl := lent_gate layer2 (l.map A)
  have hR := tsnp_r_layer1 hc PX BN BN D G o NED
  have hrun := tsn_run l.length r0 _ hR l 0
  rw [← listNoun_map_listN] at hl
  simp only [List.length_map] at hl
  unfold tsR6 tsR7 tsR8
  simp only [tsS5P, tsS7P, tsS0N] at hrun ⊢
  generalize tsBat = T at hrun ⊢
  generalize tsRunTrap = RT at hrun ⊢
  simp [nock_exec, hc, lent.arm_at, lent_arm, hl, hrun]

/-- **The gate `ren`** on the state of the core: `renReg r0 n`. -/
theorem tsnp_ren {ctx : Noun} (hc : CompIn ctx) (PX B Bo D G : Noun) (o : Nat) (NED : Noun) (r0 : Nat)
    (INS : Noun) (n : Nat) (RUN : Noun) (r : Nat) :
    nock (C tsRenBat (C (A r) (tsS7P PX B Bo (tsS0N D G ctx o NED) r0 INS n RUN))) tsRenBat
      = some (A (renReg r0 n r)) := by
  have hl1 := ts_layer1 hc
  have hadd := add_gate layer1 decIn_layer1
  have hsub := sub_gate layer1 decIn_layer1
  have hlth := lth_gate layer1 decIn_layer1
  unfold renReg
  simp only [tsS0N, tsS7P, tsS5P]
  generalize tsBat = T
  by_cases h1 : r < r0
  · simp [nock_exec, tsRenBat, hl1, lth.arm_at, lth_arm, hlth, add.arm_at, add_arm, hadd, h1, loob]
  · by_cases h2 : r < r0 + n
    · have hs : r0 ≤ r := by omega
      simp [nock_exec, tsRenBat, hl1, lth.arm_at, lth_arm, hlth, add.arm_at, add_arm, hadd, h1, h2,
        loob, Pill.sub.arm_at, sub_arm, hsub r0 r hs]
    · simp [nock_exec, tsRenBat, hl1, lth.arm_at, lth_arm, hlth, add.arm_at, add_arm, hadd, h1, h2,
        loob]

/-- **Pushes 9 to 13**, on any state. -/
theorem tsnp_pre3 {ctx : Noun} (hc : CompIn ctx) (PX D G BN SB BN1 BN2 REN : Noun) (o : Nat) (NED : Noun)
    (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun)
    (hget : getF mugF (A o) BN = some (C (A 0) SB)) (hdel : delF mugF (A o) BN = some BN1)
    (hput : putF mugF (A 0) SB BN1 = some BN2) :
    nock (C REN (tsS7P PX BN BN (tsS0N D G ctx o NED) r0 INS n RUN)) tsR9
      = nock (tsCoreStP PX SB REN BN2 BN (tsS0N D G ctx o NED) r0 INS n RUN)
          (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgot := got_gate layer2 hgc (A o) BN SB hget
  have hd := del_gate layer2 gorIn_morIn_layer2 (A o) BN BN1 hdel
  have hp := put_gate layer2 gorIn_morIn_layer2 (A 0) SB BN1 BN2 hput
  unfold tsR9 tsR10 tsR11 tsR12 tsR13
  simp only [tsCoreStP, tsS0N, tsS5P, tsS7P, tsSampleN]
  generalize tsBat = T
  generalize tsCoreBat = K
  simp [nock_exec, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, by.del.arm_at, del_arm, hd,
    by.put.arm_at, put_arm, hp]

/-- `+got:by` crashes when `then.nex` is not a block. -/
theorem tsnp_pre3_nil {ctx : Noun} (hc : CompIn ctx) (PX D G BN REN : Noun) (o : Nat) (NED : Noun)
    (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun)
    (hget : getF mugF (A o) BN = some (A 0)) :
    nock (C REN (tsS7P PX BN BN (tsS0N D G ctx o NED) r0 INS n RUN)) tsR9 = none := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgot := got_gate_nil layer2 hgc (A o) BN hget
  unfold tsR9
  simp only [tsS0N, tsS5P, tsS7P, tsSampleN]
  generalize tsBat = T
  generalize tsR10 = R
  simp [nock_exec, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot]

end Compiler
end Formalization
