import lemmas.Compiler.CompSccIn

/-!
# `+to-straight` on an n-ary input need

`TsAt` (`CompUnaryTop.lean`) and its proof (`ts_pre`, `ts_dol`, `ts_rename`,
`ts_step`) are for the input `[%this sub]` of `+compile-unary`.  The final
pass of `+compile-scc-in` calls `+to-straight` on `[%next [[ned ~] ~ ~] ~ o]`
with `ned` the need that `+need-ord-alloc-regs` returns (after `+bake-need`).
Here the same chain for any need:

* the pushes (`tsn_pre1`, `tsn_pre2`, `tsn_pre3`, `tsn_pre`): `ins` is
  `flattenNeed ned` (`comp_flatten_need`), `r0` its head or `0`, `n-in` its
  length (`+lent`), `run` is `isRun ins r0 0` (the trap `run`, `tsn_run`);
* `ren` is `renReg r0 n-in` (`tsn_ren`), `rer` with `proxies` `|` and `run`
  `&` is `[(ren r) gen]` (`tsn_rer`);
* `+rewrite-input` walks the whole need and returns `needToOrd ned` with
  `gen` unchanged (`tsn_ri_trap`, `tsn_ri`);
* the arm `$` takes the renaming branch on `[(needToOrd ned) core]`
  (`tsn_dol`), which is `+count-args` (`ca_gate`) and the `+rep:by`
  (`tsn_rename`), whose gate is `renameStep` with `renReg r0 n-in`
  (`tsn_step`, the proof of `ts_step` over any core);
* `TsAtN`: on a run of inputs and with `cond` empty, the gate returns the
  noun of `toStraightF` (`tsn_at`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The states -/

/-- The sample `[%next [[NED ~] ~ ~] ~ o]` of `+to-straight`. -/
def tsSampleN (O NED : Noun) : Noun :=
  C (A 0x7478656e) (C (C (C NED (A 0)) (C (A 0) (A 0))) (C (A 0) O))

theorem tsSample_eq (O SUB : Noun) : tsSample O SUB = tsSampleN O (C (A 0x73696874) SUB) := rfl

/-- The subject of the gate on that sample. -/
noncomputable def tsS0N (D G ctx : Noun) (o : Nat) (NED : Noun) : Noun :=
  C tsBat (C (tsSampleN (A o) NED) (C D (C G ctx)))

/-- The subject after the first five pushes. -/
def tsS5N (B Bo S0 : Noun) (r0 : Nat) (INS : Noun) : Noun :=
  C (A r0) (C INS (C (A 1) (C (C tsUnBat (C (A 0) (C Bo S0))) (C B S0))))

/-- The subject after `run`. -/
def tsS7N (B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) : Noun :=
  C RUN (C (A n) (tsS5N B Bo S0 r0 INS))

/-- The `|^` core. -/
noncomputable def tsCoreStN (SB REN B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) : Noun :=
  C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (tsS7N B Bo S0 r0 INS n RUN))))

/-! ## The pushes -/

/-- **Pushes 1 to 5** on any need: `ins` is `flattenNeed ned`, `r0` its
head or `0`. -/
theorem tsn_pre1 {ctx : Noun} (hc : CompIn ctx) (G BN : Noun) (o : Nat) (ned : Need)
    (hb : slot? 62 G = some BN) (hcd : slot? 254 G = some (A 0)) :
    nock (tsS0N comp.door G ctx o ned.toNoun) tsBat
      = nock (tsS5N BN BN (tsS0N comp.door G ctx o ned.toNoun) ((flattenNeed ned).headD 0)
          (listNoun A (flattenNeed ned))) tsR6 := by
  conv => { lhs; arg 2; rw [ts_bat_eq] }
  have hf := comp_flatten_need hc G ned
  have hD := comp_fn_at
  unfold tsR2 tsR3 tsR4 tsR5
  simp only [tsS0N, tsS5N, tsSampleN] at hf ⊢
  generalize ned.toNoun = NED at hf ⊢
  generalize flattenNeed ned = l at hf ⊢
  generalize tsBat = T at hf ⊢
  generalize comp.door = Dr at hf hD ⊢
  cases l with
  | nil => simp [nock_exec, hb, hcd, hD, comp_fn_arm, hf, listNoun]
  | cons r rs => simp [nock_exec, hb, hcd, hD, comp_fn_arm, hf, listNoun]

/-- **The trap `run`**: `isRun` of the rest of `ins` from `i`. -/
theorem tsn_run (n r0 : Nat) (R : Noun) (hR : slot? 0x3ffffff R = some layer1) :
    ∀ (l : List Nat) (i : Nat),
    nock (C tsRunTrap (C (A i) (C (A n) (C (A r0) (C (listNoun A l) R))))) tsRunTrap
      = some (loob (isRun l r0 i))
  | [], i => by
    conv => { lhs; arg 2; unfold tsRunTrap }
    simp [nock_exec, listNoun, isRun, loob]
  | r :: rs, i => by
    have ih := tsn_run n r0 R hR rs (i + 1)
    have hadd := add_gate layer1 decIn_layer1 r0 i
    conv => { lhs; arg 2; unfold tsRunTrap }
    by_cases e : r = r0 + i
    · simp [nock_exec, listNoun, isRun, hR, add.arm_at, add_arm, hadd, e, ih]
    · simp [nock_exec, listNoun, isRun, hR, add.arm_at, add_arm, hadd, e, ih, loob]

/-- `layer1` in the rest of the subject of `run`. -/
theorem tsn_r_layer1 {ctx : Noun} (hc : CompIn ctx) (B Bo D G : Noun) (o : Nat) (NED : Noun) :
    slot? 0x3ffffff (C (A 1) (C (C tsUnBat (C (A 0) (C Bo (tsS0N D G ctx o NED)))) (C B (tsS0N D G ctx o NED))))
      = some layer1 := by
  have hl1 := ts_layer1 hc
  simp only [tsS0N]
  generalize tsBat = T
  simp [nock_exec, hl1]

/-- **Pushes 6 to 8**: `n-in` is the length of `ins` (`+lent`), the trap
`run` gives `isRun ins r0 0`, the gate `ren` is built. -/
theorem tsn_pre2 {ctx : Noun} (hc : CompIn ctx) (D G BN : Noun) (o : Nat) (NED : Noun) (r0 : Nat)
    (l : List Nat) :
    nock (tsS5N BN BN (tsS0N D G ctx o NED) r0 (listNoun A l)) tsR6
      = nock (C (C tsRenBat (C (A 0) (tsS7N BN BN (tsS0N D G ctx o NED) r0 (listNoun A l) l.length
            (loob (isRun l r0 0)))))
          (tsS7N BN BN (tsS0N D G ctx o NED) r0 (listNoun A l) l.length (loob (isRun l r0 0)))) tsR9 := by
  have hl := lent_gate layer2 (l.map A)
  have hR := tsn_r_layer1 hc BN BN D G o NED
  have hrun := tsn_run l.length r0 _ hR l 0
  rw [← listNoun_map_listN] at hl
  simp only [List.length_map] at hl
  unfold tsR6 tsR7 tsR8
  simp only [tsS5N, tsS7N, tsS0N] at hrun ⊢
  generalize tsBat = T at hrun ⊢
  generalize tsRunTrap = RT at hrun ⊢
  simp [nock_exec, hc, lent.arm_at, lent_arm, hl, hrun]

/-! ## `ren` -/

/-- **The gate `ren`** on the state of the core: `renReg r0 n`. -/
theorem tsn_ren {ctx : Noun} (hc : CompIn ctx) (B Bo D G : Noun) (o : Nat) (NED : Noun) (r0 : Nat)
    (INS : Noun) (n : Nat) (RUN : Noun) (r : Nat) :
    nock (C tsRenBat (C (A r) (tsS7N B Bo (tsS0N D G ctx o NED) r0 INS n RUN))) tsRenBat
      = some (A (renReg r0 n r)) := by
  have hl1 := ts_layer1 hc
  have hadd := add_gate layer1 decIn_layer1
  have hsub := sub_gate layer1 decIn_layer1
  have hlth := lth_gate layer1 decIn_layer1
  unfold renReg
  simp only [tsS0N, tsS7N, tsS5N]
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
theorem tsn_pre3 {ctx : Noun} (hc : CompIn ctx) (D G BN SB BN1 BN2 REN : Noun) (o : Nat) (NED : Noun)
    (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun)
    (hget : getF mugF (A o) BN = some (C (A 0) SB)) (hdel : delF mugF (A o) BN = some BN1)
    (hput : putF mugF (A 0) SB BN1 = some BN2) :
    nock (C REN (tsS7N BN BN (tsS0N D G ctx o NED) r0 INS n RUN)) tsR9
      = nock (tsCoreStN SB REN BN2 BN (tsS0N D G ctx o NED) r0 INS n RUN)
          (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgot := got_gate layer2 hgc (A o) BN SB hget
  have hd := del_gate layer2 gorIn_morIn_layer2 (A o) BN BN1 hdel
  have hp := put_gate layer2 gorIn_morIn_layer2 (A 0) SB BN1 BN2 hput
  unfold tsR9 tsR10 tsR11 tsR12 tsR13
  simp only [tsCoreStN, tsS0N, tsS5N, tsS7N, tsSampleN]
  generalize tsBat = T
  generalize tsCoreBat = K
  simp [nock_exec, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, by.del.arm_at, del_arm, hd,
    by.put.arm_at, put_arm, hp]

/-- `+got:by` crashes when `then.nex` is not a block. -/
theorem tsn_pre3_nil {ctx : Noun} (hc : CompIn ctx) (D G BN REN : Noun) (o : Nat) (NED : Noun)
    (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun)
    (hget : getF mugF (A o) BN = some (A 0)) :
    nock (C REN (tsS7N BN BN (tsS0N D G ctx o NED) r0 INS n RUN)) tsR9 = none := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgot := got_gate_nil layer2 hgc (A o) BN hget
  unfold tsR9
  simp only [tsS0N, tsS5N, tsS7N, tsSampleN]
  generalize tsBat = T
  generalize tsR10 = R
  simp [nock_exec, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot]

/-- The gate `ren` as the gate of `+to-straight` pushed it. -/
noncomputable def tsRenGN (BN D G ctx : Noun) (o : Nat) (NED : Noun) (l : List Nat) : Noun :=
  C tsRenBat (C (A 0) (tsS7N BN BN (tsS0N D G ctx o NED) (l.headD 0) (listNoun A l) l.length
    (loob (isRun l (l.headD 0) 0))))

/-- The state of the `|^` core, with the blocks of the context of `ren`
named apart (`BN`) from the edited blocks (`B`). -/
noncomputable def tsStN (SB B Bo BN D G ctx : Noun) (o : Nat) (NED : Noun) (l : List Nat) : Noun :=
  tsCoreStN SB (tsRenGN BN D G ctx o NED l) B Bo (tsS0N D G ctx o NED) (l.headD 0) (listNoun A l)
    l.length (loob (isRun l (l.headD 0) 0))

/-- **The pushes of `+to-straight`** on any input need with `cond` empty. -/
theorem tsn_pre {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (ned : Need)
    (hcond : ∀ k, HoonMap.get g.cond k = Option.none) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (HoonMap.get g.blocks o).bind fun start =>
          nock (tsStN (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
            (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x)
            ctx o ned.toNoun (flattenNeed ned))
            (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  have hb := genNoun_blocks g x
  have hcd : slot? 254 (genNoun g x) = some (A 0) := by
    simp only [genNoun, nock_exec, ts_map_nil condValNoun g.cond hcond]
  have h1 := tsn_pre1 hc (genNoun g x) _ o ned hb hcd
  have h2 := tsn_pre2 hc comp.door (genNoun g x) (HoonMap.toNoun Blob.toNoun g.blocks) o ned.toNoun
    ((flattenNeed ned).headD 0) (flattenNeed ned)
  have hget := getF_hoonMap Blob.toNoun g.blocks o
  simp only [compCore]
  change nock (tsS0N comp.door (genNoun g x) ctx o ned.toNoun) tsBat = _
  rw [h1, h2]
  cases e : HoonMap.get g.blocks o with
  | none =>
    rw [e] at hget
    exact tsn_pre3_nil hc _ _ _ _ o _ _ _ _ _ hget
  | some start =>
    rw [e] at hget
    exact tsn_pre3 hc _ _ _ _ _ _ _ o _ _ _ _ _ hget (delF_hoonMap Blob.toNoun g.blocks o)
      (putF_hoonMap Blob.toNoun (HoonMap.del g.blocks o) 0 start)

/-! ## `rer` and `+rewrite-input` -/

/-- **`rer`** with `proxies` `|` and `run` `&`: `[(ren r) gen]`. -/
theorem tsn_rer {ctx : Noun} (hc : CompIn ctx) (SB B Bo BN D G : Noun) (o : Nat) (NED : Noun) (l : List Nat)
    (hrun : isRun l (l.headD 0) 0 = true) (r : Nat) :
    nock (C tsRerBody (C (A r) (tsStN SB B Bo BN D G ctx o NED l))) tsRerBody
      = some (C (A (renReg (l.headD 0) l.length r)) (C (A 0) (A 0))) := by
  have hr := tsn_ren hc BN BN D G o NED (l.headD 0) (listNoun A l) l.length (loob (isRun l (l.headD 0) 0)) r
  unfold tsStN tsRenGN
  unfold tsRenGN at hr
  simp only [tsCoreStN]
  rw [hrun] at hr ⊢
  generalize tsS7N BN BN (tsS0N D G ctx o NED) (l.headD 0) (listNoun A l) l.length (loob true) = X at hr ⊢
  simp only [tsS7N, tsS5N, loob, if_true]
  generalize tsS0N D G ctx o NED = S0
  generalize tsCoreBat = K
  unfold tsRerBody
  generalize tsRerMap = M
  simp [nock_exec, hr]

/-- The cases `^` and `%both` of the trap of `rewrite-input`, written out. -/
def tsRiRestN : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 28))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 61))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 254))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 28))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 20) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (A 0) (A 3))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 118))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 247))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 254))))))))))))))))))))))))))

theorem tsn_rirest_at : slot? 122239 tsRiArm = some tsRiRestN := by kernel_rfl

theorem tsn_rirest_eq : tsRiRest = tsRiRestN := by
  unfold tsRiRest; rw [tsn_rirest_at]; rfl

/-- **The trap of `rewrite-input`** on any need, in a core whose `rer` is a
renaming that leaves `gen`: the need without its registers, `gen`
unchanged. -/
theorem tsn_ri_trap (B GEN REST : Noun) (ren : Nat → Nat)
    (hrer : ∀ r, nock (C tsRerBody (C (A r) (C tsCoreBat (C GEN REST)))) tsRerBody = some (C (A (ren r)) GEN)) :
    ∀ ned : Need, nock (C tsRiTrap (C B (C ned.toNoun (C tsCoreBat (C GEN REST))))) tsRiTrap
      = some (C (needToOrd ned).toNoun GEN)
  | Need.none => by
    conv => { lhs; arg 2; unfold tsRiTrap }
    simp [nock_exec, Need.toNoun, needToOrd, NeedOrd.toNoun, Tag.none]
  | Need.this r => by
    have hra := ts_rer_at
    have hr := hrer r
    conv => { lhs; arg 2; unfold tsRiTrap }
    generalize tsCoreBat = K at hra hr ⊢
    generalize tsRerBody = RB at hra hr ⊢
    simp [nock_exec, Need.toNoun, needToOrd, NeedOrd.toNoun, Tag.none, Tag.this, hra, hr]
  | Need.pair p q => by
    have ihp := tsn_ri_trap B GEN REST ren hrer p
    have ihq := tsn_ri_trap B GEN REST ren hrer q
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    rw [hp] at ihp
    conv => { lhs; arg 2; unfold tsRiTrap; rw [tsn_rirest_eq]; unfold tsRiRestN }
    simp [nock_exec, Need.toNoun, hp, needToOrd, NeedOrd.toNoun, ihp, ihq]
  | Need.both r h t => by
    have hra := ts_rer_at
    have hr := hrer r
    have ihh := tsn_ri_trap B GEN REST ren hrer h
    have iht := tsn_ri_trap B GEN REST ren hrer t
    conv => { lhs; arg 2; unfold tsRiTrap; rw [tsn_rirest_eq]; unfold tsRiRestN }
    generalize tsCoreBat = K at hra hr ihh iht ⊢
    generalize tsRerBody = RB at hra hr ⊢
    simp [nock_exec, Need.toNoun, needToOrd, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, hra, hr, ihh, iht]

/-- **The gate `rewrite-input`** from `gen = [0 0]`. -/
theorem tsn_ri (REST : Noun) (ren : Nat → Nat)
    (hrer : ∀ r, nock (C tsRerBody (C (A r) (C tsCoreBat (C (C (A 0) (A 0)) REST)))) tsRerBody
      = some (C (A (ren r)) (C (A 0) (A 0)))) (ned : Need) :
    nock (C tsRiBody (C ned.toNoun (C tsCoreBat (C (C (A 0) (A 0)) REST)))) tsRiBody
      = some (C (needToOrd ned).toNoun (C (A 0) (A 0))) := by
  have ht := tsn_ri_trap tsRiBody (C (A 0) (A 0)) REST ren hrer ned
  conv => { lhs; arg 2; unfold tsRiBody }
  generalize tsRiTrap = RT at ht ⊢
  simp [nock_exec, ht]

/-- **The arm `$` up to its branches** on any need whose registers are a
run: `rewrite-input` gives `needToOrd ned` and leaves the core, the test
`&(run !proxies)` is `&`, so `$` is the renaming branch on `[(needToOrd ned)
core]`. -/
theorem tsn_dol {ctx : Noun} (hc : CompIn ctx) (SB B Bo BN D G : Noun) (o : Nat) (ned : Need)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    nock (tsStN SB B Bo BN D G ctx o ned.toNoun (flattenNeed ned)) (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = nock (C (needToOrd ned).toNoun (tsStN SB B Bo BN D G ctx o ned.toNoun (flattenNeed ned)))
          tsRenameBr := by
  have hrer := tsn_rer hc SB B Bo BN D G o ned.toNoun (flattenNeed ned) hrun
  unfold tsStN at hrer ⊢
  simp only [tsCoreStN] at hrer ⊢
  have hri := tsn_ri _ _ hrer ned
  have hdol := ts_dol_at
  have hria := ts_ri_at
  generalize tsRenGN BN D G ctx o ned.toNoun (flattenNeed ned) = RG at hri ⊢
  rw [hrun] at hri ⊢
  simp only [tsS7N, tsS5N, tsS0N, tsSampleN, loob, if_true] at hri ⊢
  generalize tsBat = T at hri ⊢
  generalize tsCoreBat = K at hri hdol hria ⊢
  generalize tsRiBody = RIB at hri hria ⊢
  generalize tsRenameBr = RNB at hdol ⊢
  generalize tsMapBr = MB at hdol ⊢
  generalize (needToOrd ned).toNoun = ORD at hri ⊢
  generalize ned.toNoun = NED at hri ⊢
  generalize (flattenNeed ned).headD 0 = r0 at hri ⊢
  generalize (flattenNeed ned).length = n at hri ⊢
  generalize listNoun A (flattenNeed ned) = INS at hri ⊢
  simp [nock_exec, hdol, hria, hri]

/-! ## `+count-args` -/

/-- The cases `^` and `%both` of `+count-args`, written out. -/
def caRestN : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 8) (C (C (A 9) (C (A 36) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12))))) (C (A 4) (C (A 8) (C (C (A 9) (C (A 36) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2))))))))))))))

theorem ca_rest_at : slot? 1919 caArm = some caRestN := by kernel_rfl

theorem ca_rest_eq : caRest = caRestN := by
  unfold caRest; rw [ca_rest_at]; rfl

/-- `layer1` in `K`. -/
theorem compK_layer1 : slot? 0x1ffff compK = some layer1 := by
  have h : slot? 65535 compK = slot? 1 layer2 := compK_layer2
  have := slot_spine (by omega) (by omega) h 1
  simp only [show 2 ^ 1 * (65535 + 1) - 1 = 0x1ffff from rfl,
    show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  rw [this]; exact layer2_layer1

/-- **The gate of `+count-args`** is `countArgs`. -/
theorem ca_gate (KC : Noun) (hK : slot? 0x1ffff KC = some layer1) : ∀ ord : NeedOrd,
    nock (C caBody (C ord.toNoun KC)) caBody = some (A (countArgs ord))
  | NeedOrd.none => by
    conv => { lhs; arg 2; unfold caBody }
    simp [nock_exec, NeedOrd.toNoun, countArgs, Tag.none]
  | NeedOrd.this => by
    conv => { lhs; arg 2; unfold caBody }
    simp [nock_exec, NeedOrd.toNoun, countArgs, Tag.none, Tag.this]
  | NeedOrd.pair p q => by
    have ihp := ca_gate KC hK p
    have ihq := ca_gate KC hK q
    have hadd := add_gate layer1 decIn_layer1 (countArgs p) (countArgs q)
    obtain ⟨a, b, hp⟩ := nord_cell p
    rw [hp] at ihp
    conv => { lhs; arg 2; unfold caBody; rw [ca_rest_eq]; unfold caRestN }
    simp [nock_exec, NeedOrd.toNoun, hp, countArgs, ihp, ihq, hK, add.arm_at, add_arm, hadd]
  | NeedOrd.both h t => by
    have ihh := ca_gate KC hK h
    have iht := ca_gate KC hK t
    have hadd := add_gate layer1 decIn_layer1 (countArgs h) (countArgs t)
    conv => { lhs; arg 2; unfold caBody; rw [ca_rest_eq]; unfold caRestN }
    simp [nock_exec, NeedOrd.toNoun, countArgs, ihh, iht, hK, add.arm_at, add_arm, hadd, Tag.none, Tag.this,
      Tag.both]

/-! ## The renaming branch and the gate of its fold -/

/-- The subject of the `+rep:by` gate: `rename`, then `[input core]`. -/
noncomputable def tsYN (SB B Bo BN D G ctx : Noun) (o : Nat) (NED : Noun) (l : List Nat) (ORD : Noun) : Noun :=
  C (tsRenameG (tsRenGN BN D G ctx o NED l)) (C ORD (tsStN SB B Bo BN D G ctx o NED l))

/-- **The renaming branch** on `[ord core]`: `[ord (countArgs ord) r]` with
`r` the `+rep:by` of the gate `tsGBody` over the blocks `B` from `~`. -/
theorem tsn_rename {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK)
    (SB B Bo BN D G : Noun) (o : Nat) (NED : Noun) (l : List Nat) (ord : NeedOrd) :
    nock (C ord.toNoun (tsStN SB B Bo BN D G ctx o NED l)) tsRenameBr
      = (nock (C by.rep.battery (C (C tsGBody (C (C tsGE (A 0)) (tsYN SB B Bo BN D G ctx o NED l ord.toNoun)))
            (C by.battery (C B layer2)))) by.rep.battery).bind
          fun r => some (C ord.toNoun (C (A (countArgs ord)) r)) := by
  have h15 := ts_types h7
  have hmr := mr_at
  have hca := ca_at
  have hcg := ca_gate compK compK_layer1 ord
  rw [ts_rb_eq]
  unfold tsYN tsRenameG tsStN
  have hms := mr_slam (tsRenGN BN D G ctx o NED l)
  unfold tsRenameG at hms
  generalize tsRenGN BN D G ctx o NED l = RG at hms ⊢
  simp only [tsCoreStN, tsS7N, tsS5N, tsS0N, tsSampleN]
  generalize tsBat = T
  generalize tsCoreBat = K
  generalize caBody = CB at hca hcg
  generalize mrBody = MB at hmr hms ⊢
  generalize tsGBody = GB
  generalize ord.toNoun = ORD at hcg ⊢
  simp [nock_exec, hc, h7, h15, hmr, hms, hca, hcg, by_arm, by.arm_at, by.rep.arm_at, rep_arm, Option.bind_assoc]

/-- **The gate of the `+rep:by` of the renaming branch** in any core that
meets `CfCore` with `+chase-fin` at `382`, with any input at `30`:
`renameStep`. -/
theorem tsn_step_gen (S INP RB RS RC : Noun) (ren : Nat → Nat) (bs new : TreapMap mugF Blob) (k : Nat)
    (b : Blob) (hcf : CfCore bs ren S)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (h382 : slot? 382 S
      = some (C (A 8) (C (C (A 1) (C (A 0x6d6f62) (A 0))) (C (C (A 1) cfBody) (C (A 0) (A 1)))))) :
    nock (C tsGBody (C (C (Tr.pairNoun Blob.toNoun (k, b)) (HoonMap.toNoun Blob.toNoun new))
        (C (tsRenameG (C RB (C RS RC))) (C INP S)))) tsGBody
      = (renameStep bs ren new (k, b)).map (HoonMap.toNoun Blob.toNoun) := by
  obtain ⟨par, body, fin⟩ := b
  have hmr := mr_inner_bom mrInner mrBody RB RS RC compTypes ren hren mr_types_layer2 par body
  simp only [Blob.toNoun, Termin.toNoun, unitNoun, Tag.bom] at hmr
  have hcfg := cf_gate hcf cfBody fin
  have hbyp := ts_byp S ⟨par, body, fin⟩
  have hput := fun (f' : Termin) => put_gate layer2 gorIn_morIn_layer2 (A k)
    (Blob.toNoun ⟨par.map ren, body.map (renPole ren), f'⟩)
    (HoonMap.toNoun Blob.toNoun new) _
    (putF_hoonMap Blob.toNoun new k ⟨par.map ren, body.map (renPole ren), f'⟩)
  simp only [Blob.toNoun] at hput hbyp
  have hL := hcf.hL
  have hY := hcf.hY
  unfold tsRenameG
  unfold renameStep keepBlock
  conv => { lhs; arg 2; unfold tsGBody }
  by_cases hk : k = 0
  · subst hk
    simp only [Tr.pairNoun, ne_eq, not_true_eq_false, false_and, if_false]
    cases e : chaseFin bs ren fin <;> rw [e] at hcfg <;>
      simp [nock_exec, hmr, h382, hcfg, hL, by_arm, by.arm_at, by.put.arm_at, put_arm, hput]
  · have hk' : ¬ (0 = k) := fun h => hk h.symm
    cases hb : bypassable true ⟨par, body, fin⟩
    · rw [hb] at hbyp
      simp only [Tr.pairNoun, hb, Bool.false_eq_true, and_false, if_false]
      cases e : chaseFin bs ren fin <;> rw [e] at hcfg <;>
        simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, hmr, h382, hcfg, hL, by_arm, by.arm_at,
          by.put.arm_at, put_arm, hput]
    · rw [hb] at hbyp
      simp only [Tr.pairNoun, hb, ne_eq, hk, not_false_eq_true, and_self, if_true]
      simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp]

/-- The core of the renaming branch meets `CfCore` with `renReg r0 n-in`. -/
theorem tsn_st_cf {ctx : Noun} (hc : CompIn ctx) (SB Bo BN D G : Noun) (o : Nat) (NED : Noun) (l : List Nat)
    (bs : TreapMap mugF Blob) :
    CfCore bs (renReg (l.headD 0) l.length) (tsStN SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o NED l) := by
  have hy := ts_byp_at
  have hch := ts_chase_at
  have hL : slot? 0x1ffffffff (tsStN SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o NED l) = some layer2 := by
    simp [tsStN, tsCoreStN, tsS7N, tsS5N, tsS0N, nock_exec, hc]
  have hR : ∃ RB RS RC, slot? 30 (tsStN SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o NED l)
      = some (C RB (C RS RC)) ∧ ∀ r, nock (C RB (C (A r) RC)) RB = some (A (renReg (l.headD 0) l.length r)) :=
    ⟨tsRenBat, A 0, tsS7N BN BN (tsS0N D G ctx o NED) (l.headD 0) (listNoun A l) l.length
      (loob (isRun l (l.headD 0) 0)), by simp [tsStN, tsCoreStN, tsRenGN, nock_exec],
      fun r => tsn_ren hc BN BN D G o NED _ _ _ _ r⟩
  refine ⟨?_, hL, ?_, ?_, hR, lf_rj _ _ hL hR⟩
  · simp [tsStN, tsCoreStN, tsS7N, tsS5N, nock_exec]
  · simp only [tsStN, tsCoreStN, nock_exec]; exact hy
  · simp only [tsStN, tsCoreStN, nock_exec]; exact hch

/-- **The gate of the fold** in the core of the renaming branch. -/
theorem tsn_step {ctx : Noun} (hc : CompIn ctx) (SB Bo BN D G : Noun) (o : Nat) (NED : Noun) (l : List Nat)
    (bs new : TreapMap mugF Blob) (ORD : Noun) (p : Nat × Blob) :
    nock (C tsGBody (C (C (Tr.pairNoun Blob.toNoun p) (HoonMap.toNoun Blob.toNoun new))
        (tsYN SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o NED l ORD))) tsGBody
      = (renameStep bs (renReg (l.headD 0) l.length) new p).map (HoonMap.toNoun Blob.toNoun) := by
  obtain ⟨k, b⟩ := p
  have hcf := tsn_st_cf hc SB Bo BN D G o NED l bs
  have h382 : slot? 382 (tsStN SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o NED l)
      = some (C (A 8) (C (C (A 1) (C (A 0x6d6f62) (A 0))) (C (C (A 1) cfBody) (C (A 0) (A 1))))) := by
    simp only [tsStN, tsCoreStN, nock_exec]; exact ts_cf_at
  unfold tsYN tsRenGN
  exact tsn_step_gen _ ORD tsRenBat (A 0) _ _ bs new k b hcf (fun r => tsn_ren hc BN BN D G o NED _ _ _ _ r) h382

/-! ## The core and the gate -/

/-- **The `|^` core of `+to-straight`** on any need whose registers are a
run: the renaming path of the model with `renReg r0 n-in`. -/
theorem tsn_core {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF))
    (x : GenRest) (o : Nat) (ned : Need) (start : Blob)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    nock (tsStN (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
        (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x)
        ctx o ned.toNoun (flattenNeed ned)) (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = (renameBlocks (HoonMap.put (HoonMap.del g.blocks o) 0 start)
          (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length)).map
          fun new => Straight.toNoun (⟨needToOrd ned, countArgs (needToOrd ned), new⟩ : Straight (TreapMap mugF)) := by
  generalize HoonMap.put (HoonMap.del g.blocks o) 0 start = bs
  rw [tsn_dol hc _ _ _ _ _ _ o ned hrun, tsn_rename hc h7]
  have ha : Tree (HoonMap.toNoun Blob.toNoun bs) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bs.2 Blob.toNoun)
  have hL : preorder (HoonMap.toNoun Blob.toNoun bs) = (TreapMap.rap bs).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bs
  have hrep := rep_gate_list (Tr.pairNoun Blob.toNoun) (HoonMap.toNoun Blob.toNoun)
    (fun p s => renameStep bs (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length) s p) by.battery
    layer2 tsGBody tsGE
    (tsYN (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun bs) (HoonMap.toNoun Blob.toNoun g.blocks)
      (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x) ctx o ned.toNoun (flattenNeed ned)
      (needToOrd ned).toNoun)
    _ ha _ hL HoonMap.empty (fun p _ s => tsn_step hc _ _ _ _ _ o _ _ bs s _ p)
  rw [HoonMap.toNoun_empty] at hrep
  rw [hrep, renameBlocks_rap]
  cases (TreapMap.rap bs).foldlM
    (fun s p => renameStep bs (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length) s p)
    HoonMap.empty <;> rfl

/-- **`+to-straight` on any input need** whose registers are a run, with
`cond` empty: the gate on `[%next [[ned ~] ~ ~] ~ o]` returns the noun of
`toStraightF`. -/
theorem tsn_at {ctx : Noun} (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF)) (x : GenRest)
    (o : Nat) (ned : Need) (hcond : ∀ k, HoonMap.get g.cond k = Option.none)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  rw [tsn_pre hc g x o ned hcond, toStraightF_eq hcond hrun]
  unfold toStraight
  simp only [hrun, Bool.true_eq_false, if_false]
  cases e : HoonMap.get g.blocks o with
  | none => rfl
  | some start =>
    simp only [Option.bind_some]
    rw [tsn_core hc h7 g x o ned start hrun, Option.map_map]
    rfl
