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

end Compiler
end Formalization
