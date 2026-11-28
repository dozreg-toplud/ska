import lemmas.Compiler.CompRunDirectRing

/-!
# `+callee-need` on every case through a ring with no hot driver (track K, README Gaps 19 (h))

`cne_step` (`CompCalleeComp.lean`) asks the callee's `call.cole` entry to be `~`.  With a ring
`u` the arm reads `(biff rin ~(get by jets-hot))` (line 4608), which is `~` when `jets-hot` has
no entry at `u` (`RinAt`, `CompRunDirectRing.lean`): then the arm goes on as with no ring, on
the read-only cases (`NeedRead`, as `cne_readR` of `CompRingNeed.lean`) and on a miss in
`nary.cache` (the compile `CccMiss`).

* **`cne_stepR`**: `+callee-need` on every case of `NeedStep`, `rin` any unit with no hot driver.
* **`callNounMTG_of`**: `CallNounMTG` from `RinAt`, the need step, `SureNoun` at the new rest and
  the push of `sof` on the subject with `rin`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **`+callee-need` through a ring on every case**: `nb` and the rest `x'` of `NeedStep`, the
callee's entry `rin` with no `jets-hot` entry (`RinAt`). -/
theorem cne_stepR (h7 : slot? 7 ctx = some compK) (b : Bell) (nb : NeedOrd) (x x' : GenRest)
    (rin : Option Noun) (hra : RinAt ctx b rin) (hs : NeedStep ctx x b nb x') (g : Gen (TreapMap mugF)) :
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x')) := by
  obtain ⟨cole, jh, hcl, hjh, hgc, hw⟩ := hra
  cases rin with
  | none => exact cne_step h7 b nb x x' ⟨cole, hcl, hgc⟩ ⟨jh, hjh⟩ hs g
  | some w =>
  have hgw := hw w rfl
  simp only [unitNoun, id] at hgc
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole _ hgc
  have hgj := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ w jh _ hgw
  cases hs with
  | read hr =>
    cases hr with
    | @loc S ML u' hS hh hML hg hu =>
      have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S true hh
      have hgl := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun ML _ hg
      conv => lhs; rw [cne_bat]
      simp [nock_exec, compCore, genNoun, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
        biff.arm_at, biff_gate_some, hgj, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hML, hgl, hu]
    | @top S ML TP hS hh hML hg hTP hgt' =>
      have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S true hh
      have hgl := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun ML _ hg
      have hgut : nock (C by.gut.battery (C (C b.toNoun (C (A 0x656e6f6e) (A 0))) (C by.battery (C TP layer2))))
          by.gut.battery = some nb.toNoun := by
        rcases hgt' with h | ⟨h, hn⟩
        · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun
            (C (A 0x656e6f6e) (A 0)) TP _ h (Or.inr ⟨_, rfl⟩)
          simpa using this
        · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun
            (C (A 0x656e6f6e) (A 0)) TP _ h (Or.inl rfl)
          rw [hn]
          simpa [NeedOrd.toNoun, Tag.none] using this
      conv => lhs; rw [cne_bat]
      simp [nock_exec, compCore, genNoun, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
        biff.arm_at, biff_gate_some, hgj, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hML, hgl, hTP,
        by.gut.arm_at, gut_arm, hgut]
    | @nary S N u' hS hh hN hg hu =>
      have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S false hh
      have hcc := ccc_nary hc b x hN hg hu g
      have hD := ccc_at
      simp only [compCore] at hcc
      conv => lhs; rw [cne_bat]
      generalize cccBat = CB at hcc hD
      simp only [compCore]
      generalize comp.door = Dr at hcc hD ⊢
      simp [nock_exec, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
        biff.arm_at, biff_gate_some, hgj, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hD, hcc]
  | @miss S NR MO SC RS CA' hS hh hx hmiss hm =>
    obtain ⟨NS, SC', M, u, hscc, hcsi, hg, hu⟩ := hm
    have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S false hh
    obtain ⟨xc, xs, xf⟩ := x
    simp only at hx
    subst hx
    have hcc := ccc_miss hc b g hmiss (hscc g) (hcsi g) hg hu
    have hD := ccc_at
    simp only [compCore, ccRest] at hcc
    conv => lhs; rw [cne_bat]
    generalize cccBat = CB at hcc hD
    simp only [compCore]
    generalize comp.door = Dr at hcc hD ⊢
    simp [nock_exec, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
      biff.arm_at, biff_gate_some, hgj, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hD, hcc]

/-- **`CallNounMTG` from the facts**: the entry `rin` with no hot driver, `NeedStep` to `x'`,
`SureNoun` at `x'`, and the push of `sof` at `x'` on the subject with `rin`. -/
theorem callNounMTG_of (h7 : slot? 7 ctx = some compK) {env : CallEnv} {msup : Option Nomm} {p q : Nomm}
    {b : Bell} {nb : NeedOrd} {x x' : GenRest} {mono SOF : Noun} {rin : Option Noun}
    (hra : RinAt ctx b rin) (hs : NeedStep ctx x b nb x') (hsu : SureNoun env b x')
    (hsof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
      nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (unitNoun id rin) (C PV (crSubj mono (crdN p q b)
        goalN regionN (unitNoun Nomm.toNoun msup) (compCore g x' ctx)))))))) crDKc6 = some SOF) :
    CallNounMTG msup ctx p q b nb (env.sure b).toNoun x x' mono SOF rin :=
  ⟨hra, cne_stepR h7 b nb x x' rin hra hs, csu_gate (comp_ctx_pill ctx h7).1 env b x' hsu, hsof⟩

end Compiler
end Formalization
