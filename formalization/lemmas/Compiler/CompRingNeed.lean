import lemmas.Compiler.CompRunDirectS
import lemmas.Compiler.CompMonoLinkRing
import lemmas.Ska.CompRingContract

/-!
# `+callee-need` of a callee with a ring and no hot driver (track K, README Gaps 19 (h))

The pill link of `+callee-need` (door arm `221180`, `cne_read` of `CompRunDirectS.lean`) asked
the callee's `call.cole` entry to be `~`.  With a ring `u` (`getF b cole = [~ u]`) the arm reads
`(biff rin ~(get by jets-hot))`, which is `~` when `jets-hot` has no entry at `u`: the arm then
goes on as with no ring.

* `ColeAt ctx JH b`: the `call.cole` entry of `b` in the context is `~`, or a ring `u` with no
  `jets-hot` entry (`JH` at axis `54`).  With `JH` the empty map (`jets-hot = ~` at every reached
  state, owner P: the coordinator's clause `PGood9`) the second case holds of every ring
  (`coleAt_of_empty`).
* **`cne_readR`**: `+callee-need` in its read-only cases, ring or not, given `ColeAt`.
* `ringOf_cole`: the model's `envOf … COLE …` reads `ringOf COLE`, the ring `u` of the entry.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ctx : Noun}

/-- **The callee's `call.cole` entry** (axis `6846`) is `~`, or a ring with no entry in
`jets-hot` (axis `54`). -/
def ColeAt (ctx : Noun) (b : Bell) : Prop :=
  ∃ cole jh, slot? 6846 ctx = some cole ∧ slot? 54 ctx = some jh ∧
    (getF mugF b.toNoun cole = some (A 0) ∨ ∃ u, getF mugF b.toNoun cole = some (C (A 0) u) ∧ getF mugF u jh = some (A 0))

/-- With `jets-hot` the empty map, every entry of `call.cole` is `~` or a ring with no driver. -/
theorem coleAt_of_empty {b : Bell} {cole : Noun} (hc : slot? 6846 ctx = some cole) (hj : slot? 54 ctx = some (A 0))
    (hg : getF mugF b.toNoun cole = some (A 0) ∨ ∃ u, getF mugF b.toNoun cole = some (C (A 0) u)) : ColeAt ctx b := by
  refine ⟨cole, A 0, hc, hj, ?_⟩
  rcases hg with h | ⟨u, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, h, rfl⟩

/-- The old hypothesis (no ring) is the first case. -/
theorem coleAt_of_none {b : Bell} (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) : ColeAt ctx b := by
  obtain ⟨cole, h1, h2⟩ := hcole
  obtain ⟨jh, h3⟩ := hhot
  exact ⟨cole, jh, h1, h3, Or.inl h2⟩

/-- **`+callee-need` in its read-only cases, ring or not** (no hot driver): `nb` and the state
unchanged. -/
theorem cne_readR (h7 : slot? 7 ctx = some compK) (b : Bell) (nb : NeedOrd) (x : GenRest)
    (hcole : ColeAt ctx b) (hr : NeedRead ctx x b nb) (g : Gen (TreapMap mugF)) :
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x)) := by
  obtain ⟨cole, jh, hcl, hjh, hgc | ⟨u, hgc, hgu⟩⟩ := hcole
  · exact cne_read h7 b nb x ⟨cole, hcl, hgc⟩ ⟨jh, hjh⟩ hr g
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole _ hgc
  have hgj := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ u jh _ hgu
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

/-- **The model's ring is the noun's**: `envOf CODE COLE …` reads `ringOf COLE`, which is the
ring `u` of a `[~ u]` entry and `none` for a `~` entry. -/
theorem ringOf_cole {COLE : Noun} {b : Bell} {u : Noun} (h : getF mugF b.toNoun COLE = some (C (A 0) u)) :
    ringOf COLE b = some u := by
  simp [ringOf, h]

theorem ringOf_cole_none {COLE : Noun} {b : Bell} (h : getF mugF b.toNoun COLE = some (A 0)) :
    ringOf COLE b = Option.none := by
  simp [ringOf, h]

end Compiler
end Formalization
