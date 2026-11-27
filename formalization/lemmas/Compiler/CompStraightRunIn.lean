import lemmas.Compiler.CompStraightRunBlk
import lemmas.Compiler.CompStraightMapAt

/-!
# `+to-straight` with `run` `|`: `rewrite-input`, the arm `$`, the gate

README Gaps 20.  With the state `[re-gen m]`:

* `tsr_ri_trap`, `tsr_ri`: the trap of `rewrite-input` and the gate from
  `gen = [0 ~]` (its `?>  =(0 re-gen.gen)` holds), the model's
  `rewriteInput rr ned (0, ∅)`;
* `tsr_dol`: the arm `$` with `run` `|`: `rewrite-input`, then the test
  `&(run !proxies)` is `|` whatever `proxies` is, so the map branch on
  `[input core]` with the state `rewrite-input` left;
* the two bunts with the state free (`tsr_rep_bunt_sp`, `tsr_arg_bunt_sp`);
* `tsr_core`: the `|^` core with `run` `|`, `rewrite-input` then
  `mapBlocks`;
* `tsrp_core`, **`tsr_at`**: the gate on every input need whose registers
  are not a run, with or without proxies: the noun of `toStraightF`;
* **`ts_at_any`**: `+to-straight` on every input need and every `cond`
  (`ts_at_all` without `isRun`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `rewrite-input` -/

/-- **The trap of `rewrite-input` with the state**: the model's
`rewriteInputGo rr`. -/
theorem tsr_ri_trap {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R) (B : Noun) :
    ∀ (ned : Need) (st : Nat × TreapMap mugF Nat),
      nock (C tsRiTrap (C B (C ned.toNoun (C tsCoreBat (C (rmN st) R))))) tsRiTrap
        = (rewriteInputGo rr ned st).map fun p => C p.1.toNoun (rmN p.2)
  | Need.none, st => by
    conv => { lhs; arg 2; unfold tsRiTrap }
    simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, pure, StateT.pure]
  | Need.this r, st => by
    have hra := ts_rer_at
    have hr := hrer r st
    conv => { lhs; arg 2; unfold tsRiTrap }
    generalize tsCoreBat = K at hra hr ⊢
    generalize tsRerBody = RB at hra hr ⊢
    cases e1 : rr r st with
    | none =>
      rw [e1] at hr
      simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, Tag.this, hra, hr, bind, StateT.bind,
        e1]
    | some p1 =>
      obtain ⟨r1, st1⟩ := p1
      rw [e1] at hr
      simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, Tag.this, hra, hr, bind, StateT.bind,
        pure, StateT.pure, e1]
  | Need.pair p q, st => by
    have ihp := tsr_ri_trap hrer B p
    have ihq := tsr_ri_trap hrer B q
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    simp only [hp] at ihp
    conv => { lhs; arg 2; unfold tsRiTrap; rw [tsn_rirest_eq]; unfold tsRiRestN }
    cases e1 : rewriteInputGo rr p st with
    | none =>
      have h1 := ihp st
      rw [e1] at h1
      simp [nock_exec, Need.toNoun, hp, rewriteInputGo, NeedOrd.toNoun, h1, bind, StateT.bind, e1]
    | some p1 =>
      obtain ⟨l, st1⟩ := p1
      have h1 := ihp st
      rw [e1] at h1
      cases e2 : rewriteInputGo rr q st1 with
      | none =>
        have h2 := ihq st1
        rw [e2] at h2
        simp [nock_exec, Need.toNoun, hp, rewriteInputGo, NeedOrd.toNoun, h1, h2, bind, StateT.bind, e1, e2]
      | some p2 =>
        obtain ⟨r2, st2⟩ := p2
        have h2 := ihq st1
        rw [e2] at h2
        simp [nock_exec, Need.toNoun, hp, rewriteInputGo, NeedOrd.toNoun, h1, h2, bind, StateT.bind, pure,
          StateT.pure, e1, e2]
  | Need.both r h t, st => by
    have hra := ts_rer_at
    have hr := hrer r st
    have ihh := tsr_ri_trap hrer B h
    have iht := tsr_ri_trap hrer B t
    conv => { lhs; arg 2; unfold tsRiTrap; rw [tsn_rirest_eq]; unfold tsRiRestN }
    generalize tsCoreBat = K at hra hr ihh iht ⊢
    generalize tsRerBody = RB at hra hr ⊢
    cases e1 : rr r st with
    | none =>
      rw [e1] at hr
      simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, hra, hr, bind,
        StateT.bind, e1]
    | some p1 =>
      obtain ⟨r1, st1⟩ := p1
      rw [e1] at hr
      cases e2 : rewriteInputGo rr h st1 with
      | none =>
        have h2 := ihh st1
        rw [e2] at h2
        simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, hra, hr, h2,
          bind, StateT.bind, e1, e2]
      | some p2 =>
        obtain ⟨h1, st2⟩ := p2
        have h2 := ihh st1
        rw [e2] at h2
        cases e3 : rewriteInputGo rr t st2 with
        | none =>
          have h3 := iht st2
          rw [e3] at h3
          simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, hra, hr, h2,
            h3, bind, StateT.bind, e1, e2, e3]
        | some p3 =>
          obtain ⟨t1, st3⟩ := p3
          have h3 := iht st2
          rw [e3] at h3
          simp [nock_exec, Need.toNoun, rewriteInputGo, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, hra, hr, h2,
            h3, bind, StateT.bind, pure, StateT.pure, e1, e2, e3]

theorem rmN_zero : rmN (0, (HoonMap.empty : TreapMap mugF Nat)) = C (A 0) (A 0) := rfl

/-- **The gate `rewrite-input` with the state** from `gen = [0 ~]`: the
model's `rewriteInput rr ned (0, ∅)`. -/
theorem tsr_ri {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R) (ned : Need) :
    nock (C tsRiBody (C ned.toNoun (C tsCoreBat (C (C (A 0) (A 0)) R)))) tsRiBody
      = (rewriteInput rr ned (0, HoonMap.empty)).map fun p => C p.1.toNoun (rmN p.2) := by
  have ht := tsr_ri_trap hrer tsRiBody ned (0, HoonMap.empty)
  rw [rmN_zero] at ht
  unfold rewriteInput
  simp only [if_true]
  conv => { lhs; arg 2; unfold tsRiBody }
  generalize tsRiTrap = RT at ht ⊢
  simp [nock_exec, ht]

/-! ## The arm `$` with `run` `|` -/

/-- **The arm `$` with `run` `|`**: `rewrite-input` from `[0 ~]`, then the
map branch on `[input core]` with the state it left, whatever `proxies`
(`PX`) is. -/
theorem tsr_dol {rr : Nat → RM (TreapMap mugF) Nat} (SB REN N R0 INS PX REST : Noun) (ned : Need)
    (hrer : RerM rr (C SB (C REN (C (A 1) (C N (C R0 (C INS (C PX REST))))))))
    (hN : slot? 488 REST = some ned.toNoun) :
    nock (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (C (A 1) (C N (C R0 (C INS (C PX REST)))))))))
        (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = (rewriteInput rr ned (0, HoonMap.empty)).bind fun p =>
          nock (C p.1.toNoun (C tsCoreBat (C (rmN p.2) (C SB (C REN (C (A 1) (C N (C R0 (C INS (C PX REST)))))))))) tsMapBr := by
  have hri := tsr_ri hrer ned
  have hdol := ts_dol_at
  have hria := ts_ri_at
  generalize tsCoreBat = K at hri hdol hria ⊢
  generalize tsRiBody = RIB at hri hria ⊢
  generalize tsRenameBr = RNB at hdol ⊢
  generalize tsMapBr = MB at hdol ⊢
  generalize ned.toNoun = NED at hri hN ⊢
  cases e : rewriteInput rr ned (0, HoonMap.empty) with
  | none =>
    rw [e] at hri
    simp [nock_exec, hdol, hria, hri, hN]
  | some p =>
    obtain ⟨ord, st⟩ := p
    rw [e] at hri
    simp [nock_exec, hdol, hria, hri, hN]

/-! ## The bunts with the state free -/

/-- The bunt of the sample of `tsmGate` with the state a free cell
`[X Y]` (a free noun returned whole does not reduce in the kernel, a free
cell does): `[[0 *blob] [~ [X Y]]]`. -/
theorem tsr_rep_bunt_sp (ord X Y SB REN RUN N R0 INS PX UNG B T SAM D G' c2 c6 : Noun) :
    nock (C ord (C tsCoreBat (C (C X Y) (C SB (C REN (C RUN (C N (C R0 (C INS (C PX (C UNG (C B (C T (C SAM (C D (C G' (C c2 (C c6 compK)))))))))))))))))) tsmRepBuntF
      = some (C (C (A 0) tsmBlobBunt) (C (A 0) (C X Y))) :=
  nock_of_evalFuel (fuel := 5000) (by kernel_rfl)

/-- The bunt of the sample of the `+spin` gate of `rewrite-args` with the
state a free cell `[X Y]`: `[~ [X Y]]`. -/
theorem tsr_arg_bunt_sp (J X Y SB REN RUN N R0 INS PX UNG B T SAM D G' c2 c6 : Noun) :
    nock (C tsmArgBody (C J (C tsCoreBat (C (C X Y) (C SB (C REN (C RUN (C N (C R0 (C INS (C PX (C UNG (C B (C T (C SAM (C D (C G' (C c2 (C c6 compK))))))))))))))))))) tsmArgBuntF1
      = some (C (A 0) (C X Y)) :=
  nock_of_evalFuel (fuel := 5000) (by kernel_rfl)


/-! ## The core, the gate, every input -/

/-- The rest of the `|^` core with `run` `|`: `rer`'s shape of `tsr_rer`. -/
def tsrR (SB REN N R0 INS PX UB US UC REST : Noun) : Noun :=
  C SB (C REN (C (A 1) (C N (C R0 (C INS (C PX (C (C UB (C US UC)) REST)))))))

/-- **The `|^` core of `+to-straight` with `run` `|`**, with or without
proxies: `rewrite-input` from `[0 ~]`, then the map path `mapBlocks` from
the state it left, the model's map path with `run` false. -/
theorem tsr_core {bs : TreapMap mugF Blob} (cond : TreapMap mugF (Nat × List Nat)) (proxies : Bool)
    (ren : Nat → Nat) (UB US UC SB REN N R0 INS REST : Noun) (ned : Need)
    (hu : ∀ r, nock (C UB (C (A r) UC)) UB = some (A (unproxy cond r)))
    (hN : slot? 488 (C (C UB (C US UC)) REST) = some ned.toNoun)
    (hL : slot? 0x7fffffff (tsrR SB REN N R0 INS (loob proxies) UB US UC REST) = some layer2)
    (hU : ∀ J (st : Nat × TreapMap mugF Nat), nock (C tsmArgBody (C J (C tsCoreBat (C (rmN st)
      (tsrR SB REN N R0 INS (loob proxies) UB US UC REST))))) tsmArgBuntF1 = some (C (A 0) (rmN st)))
    (hB : ∀ G, slot? 4094 (C tsCoreBat (C G (tsrR SB REN N R0 INS (loob proxies) UB US UC REST)))
      = some (HoonMap.toNoun Blob.toNoun bs))
    (hT : slot? 0x1ffff (tsrR SB REN N R0 INS (loob proxies) UB US UC REST) = some compTypes)
    (hK : slot? 0xffff (tsrR SB REN N R0 INS (loob proxies) UB US UC REST) = some compK)
    (hRB : ∀ (ord : NeedOrd) (st : Nat × TreapMap mugF Nat), nock (C ord.toNoun (C tsCoreBat (C (rmN st)
      (tsrR SB REN N R0 INS (loob proxies) UB US UC REST)))) tsmRepBuntF
      = some (C (C (A 0) tsmBlobBunt) (C (A 0) (rmN st)))) :
    nock (C tsCoreBat (C (C (A 0) (A 0)) (tsrR SB REN N R0 INS (loob proxies) UB US UC REST)))
        (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = (rewriteInput (rer cond proxies false ren) ned (0, HoonMap.empty)).bind fun p =>
          (mapBlocks (rer cond proxies false ren) bs p.2).map fun new =>
            Straight.toNoun (⟨p.1, countArgs p.1, new⟩ : Straight (TreapMap mugF)) := by
  have hrer := tsr_rer cond proxies ren UB US UC SB REN N R0 INS REST hu hL
  have hc : MapCoreM bs (rer cond proxies false ren) (tsrR SB REN N R0 INS (loob proxies) UB US UC REST) :=
    ⟨hrer, hL, hU, hB⟩
  unfold tsrR at hrer ⊢
  rw [tsr_dol SB REN N R0 INS (loob proxies) (C (C UB (C US UC)) REST) ned hrer hN]
  cases e : rewriteInput (rer cond proxies false ren) ned (0, HoonMap.empty) with
  | none => rfl
  | some p =>
    obtain ⟨ord, st⟩ := p
    simp only [Option.bind_some]
    have hb := tsr_branch hc hT hK ord st (hRB ord st)
    unfold tsrR at hb
    rw [hb]
    rfl

/-- **The `|^` core of the real gate with `run` `|`**, `proxies` being
`hasProxies cond`. -/
theorem tsrp_core {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF))
    (x : GenRest) (o : Nat) (ned : Need) (start : Blob)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = false) :
    nock (tsStP (loob (hasProxies g.cond)) (Blob.toNoun start)
        (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
        (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x)
        ctx o ned.toNoun (flattenNeed ned)) (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = (rewriteInput (rer g.cond (hasProxies g.cond) false
            (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length)) ned (0, HoonMap.empty)).bind fun p =>
          (mapBlocks (rer g.cond (hasProxies g.cond) false
              (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length))
            (HoonMap.put (HoonMap.del g.blocks o) 0 start) p.2).map fun new =>
            Straight.toNoun (⟨p.1, countArgs p.1, new⟩ : Straight (TreapMap mugF)) := by
  have h15 := ts_types h7
  unfold tsStP tsRenGP tsCoreStP tsS7P tsS5P
  rw [hrun, loob_false]
  obtain ⟨c2, c6, rfl⟩ := ctx_of_slot7 h7
  exact tsr_core g.cond (hasProxies g.cond) _ _ _ _ _ _ _ _ _ _ ned
    (fun r => tsm_unproxy hc g x _ comp.door o _ r)
    (by simp [tsS0N, tsSampleN, nock_exec])
    (by simp [tsrR, tsS0N, nock_exec, hc])
    (fun J st => tsr_arg_bunt_sp J (A st.1) (HoonMap.toNoun A st.2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (fun G => by simp [tsrR, nock_exec])
    (by simp [tsrR, tsS0N, nock_exec, h15])
    (by simp [tsrR, tsS0N, nock_exec, h7])
    (fun ord st => tsr_rep_bunt_sp ord.toNoun (A st.1) (HoonMap.toNoun A st.2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- The pushes on any `cond`: `tsn_pre` without proxies, `tsnp_pre` with. -/
theorem ts_pre_any {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (ned : Need) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (HoonMap.get g.blocks o).bind fun start =>
          nock (tsStP (loob (hasProxies g.cond)) (Blob.toNoun start)
            (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
            (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x)
            ctx o ned.toNoun (flattenNeed ned))
            (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  cases hp : hasProxies g.cond with
  | false => rw [tsn_pre hc g x o ned (hasProxies_none hp)]; rfl
  | true => rw [tsnp_pre hc g x o ned hp]; rfl

/-- **`+to-straight` on every input need whose registers are not a run**,
with or without proxies: the gate returns the noun of `toStraightF`, the
map path through the state `[re-gen m]`. -/
theorem tsr_at {ctx : Noun} (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF)) (x : GenRest)
    (o : Nat) (ned : Need) (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = false) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  rw [ts_pre_any hc g x o ned]
  unfold toStraightF
  simp only [hrun, Bool.false_and, Bool.false_eq_true, if_false]
  cases e : HoonMap.get g.blocks o with
  | none => rfl
  | some start =>
    simp only [Option.bind_some]
    rw [tsrp_core hc h7 g x o ned start hrun]
    cases e2 : rewriteInput (rer g.cond (hasProxies g.cond) false
        (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length)) ned (0, HoonMap.empty) with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, Option.map_map]
      rfl

/-- **`+to-straight` on every input need and every `cond`**: `ts_at_all`
without `isRun` (`tsr_at` when the inputs are not a run). -/
theorem ts_at_any {ctx : Noun} (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF)) (x : GenRest)
    (o : Nat) (ned : Need) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun := by
  cases hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 with
  | true => exact ts_at_all h7 g x o ned hrun
  | false => exact tsr_at h7 g x o ned hrun

/-- **`+to-straight` on every sample `[%next [[ned ~] ~ ~] ~ o]` of a final
pass**, every state, no condition on the registers. -/
def TsAny : Prop :=
  ∀ (ctx : Noun), slot? 7 ctx = some compK → ∀ (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (ned : Need),
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun

theorem tsAny_holds : TsAny := fun _ h7 g x o ned => ts_at_any h7 g x o ned

end Compiler
end Formalization
