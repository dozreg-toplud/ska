import lemmas.Compiler.OptLinkMiddle

/-!
# `+remove-empty-middle`: the gate of the `+rep:by` and the gate

The arm `$` of the `|^` core (`remBat` axis `6`, core axis `10`) rolls the
gate `remMainG` over the blocks with `+rep:by` from `[| ~]`.  The gate's `?+`
rewrites the two jumps of a `%clq`, `%eqq`, `%brn` or `%brz` with
`rewrite-jump` (core axis `11`) and the jump of a `%hop` with `rewrite-hop`
(core axis `4`), and puts the block with its new terminator.

* `rem_step`: where `middleFin` returns, the gate returns the model's step
  (`rj_gate`, `rhop_gate`, given `RdOK` of `readers`).
* `rem_gate_of`: **where `removeEmptyMiddle fuel` returns `(changed, new)`,
  the gate of `+remove-empty-middle` returns `[changed new]`**, given that
  the computation of `readers` returns a noun with `RdOK`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of the accumulator `[changed new]`. -/
def remN (s : Bool × TreapMap mugF Blob) : Noun := C (flag s.1) (HoonMap.toNoun Blob.toNoun s.2)

/-- The step of the model's fold on a pair of `rap`. -/
def remG (bl : TreapMap mugF Blob) (fuel : Nat) (s : Bool × TreapMap mugF Blob) (p : Nat × Blob) :
    Option (Bool × TreapMap mugF Blob) :=
  (Opt.middleFin bl (Opt.readersOf bl) fuel p.2.fin).map fun f' =>
    (s.1 || decide (f' ≠ p.2.fin), HoonMap.put s.2 p.1 { p.2 with fin := f' })

/-- The arm `rewrite-jump` of the core. -/
def remJumpArm : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) remJumpBody) (C (A 0) (A 1))))
/-- The arm `rewrite-hop` of the core. -/
def remHopArm : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) remHopBody) (C (A 0) (A 1))))

theorem rem_core_jump (RD BL : Noun) : slot? 11 (remCore RD BL) = some remJumpArm := by rfl
theorem rem_core_hop (RD BL : Noun) : slot? 4 (remCore RD BL) = some remHopArm := by rfl
theorem rem_core_layer2 (RD BL : Noun) : slot? 0x1fffff (remCore RD BL) = some layer2 := by
  have h : slot? 31 (remCore RD BL) = slot? 1 optC := rfl
  have := slot_spine (by omega) (by omega) h 16
  simp only [show 2 ^ 16 * (31 + 1) - 1 = 0x1fffff from rfl,
    show 2 ^ 16 * (1 + 1) - 1 = 0x1ffff from rfl] at this
  rw [this]
  exact optC_layer2

@[nock_exec] theorem rem_jump_arm (d : Noun) : nock d remJumpArm = some (C remJumpBody (C (C (A 0) (A 0)) d)) := by
  unfold remJumpArm; generalize remJumpBody = B; simp [nock_exec]
@[nock_exec] theorem rem_hop_arm (d : Noun) : nock d remHopArm = some (C remHopBody (C (C (A 0) (A 0)) d)) := by
  unfold remHopArm; generalize remHopBody = B; simp [nock_exec]

/-- The subject of the gate: `[remMainG [[[o b] acc] CORE]]`. -/
def remGS (o : Nat) (b : Blob) (ACC CORE : Noun) : Noun := C remMainG (C (C (C (A o) b.toNoun) ACC) CORE)

/-- **The `?+` over the terminator**: where `middleFin` returns `f'`, the
noun of `f'`. -/
theorem rem_sw (bl : TreapMap mugF Blob) (RD : Noun) (hR : RdOK bl RD) (fuel o : Nat) (b : Blob) (ACC : Noun)
    (f' : Termin) (hf : Opt.middleFin bl (Opt.readersOf bl) fuel b.fin = some f') :
    nock (remGS o b ACC (remCore RD (HoonMap.toNoun Blob.toNoun bl))) remSw = some f'.toNoun := by
  have hj := rj_gate bl RD fuel
  have hh := rhop_gate bl RD hR fuel
  have hcj := rem_core_jump RD (HoonMap.toNoun Blob.toNoun bl)
  have hch := rem_core_hop RD (HoonMap.toNoun Blob.toNoun bl)
  obtain ⟨par, body, fin⟩ := b
  unfold remGS
  generalize remCore RD (HoonMap.toNoun Blob.toNoun bl) = CORE at hj hh hcj hch
  cases fin with
  | clq s z o' =>
    simp only [Opt.middleFin] at hf
    obtain ⟨z', hz, h2⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨o'', ho, rfl⟩ := Option.map_eq_some_iff.mp h2
    simp [nock_exec, remSw, Blob.toNoun, Termin.toNoun, Tag.clq, hcj, rem_jump_arm, hj _ _ hz, hj _ _ ho]
  | eqq l r z o' =>
    simp only [Opt.middleFin] at hf
    obtain ⟨z', hz, h2⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨o'', ho, rfl⟩ := Option.map_eq_some_iff.mp h2
    simp [nock_exec, remSw, Blob.toNoun, Termin.toNoun, Tag.clq, Tag.eqq, hcj, rem_jump_arm, hj _ _ hz,
      hj _ _ ho]
  | brn s z o' =>
    simp only [Opt.middleFin] at hf
    obtain ⟨z', hz, h2⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨o'', ho, rfl⟩ := Option.map_eq_some_iff.mp h2
    simp [nock_exec, remSw, Blob.toNoun, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, hcj, rem_jump_arm,
      hj _ _ hz, hj _ _ ho]
  | brz s z o' =>
    simp only [Opt.middleFin] at hf
    obtain ⟨z', hz, h2⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨o'', ho, rfl⟩ := Option.map_eq_some_iff.mp h2
    simp [nock_exec, remSw, Blob.toNoun, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, hcj, rem_jump_arm,
      hj _ _ hz, hj _ _ ho]
  | hop t =>
    simp only [Opt.middleFin] at hf
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp hf
    simp [nock_exec, remSw, Blob.toNoun, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, hch,
      rem_hop_arm, hh _ _ ht]
  | _ =>
    simp only [Opt.middleFin, Option.some.injEq] at hf
    subst hf
    simp [nock_exec, remSw, Blob.toNoun, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp,
      Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-- **The rest of the gate**: the flag and the `+put:by`. -/
theorem rem_rest (o : Nat) (b : Blob) (ch : Bool) (new : TreapMap mugF Blob) (RD BL : Noun) (f' : Termin) :
    nock (C f'.toNoun (remGS o b (remN (ch, new)) (remCore RD BL))) remRest
      = some (remN (ch || decide (f' ≠ b.fin), HoonMap.put new o { b with fin := f' })) := by
  have hL := rem_core_layer2 RD BL
  have hp := putF_hoonMap Blob.toNoun new o { b with fin := f' }
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A o) _ _ _ hp
  obtain ⟨par, body, fin⟩ := b
  simp only [Blob.toNoun] at hput ⊢
  unfold remGS remN
  generalize remCore RD BL = CORE at hL
  by_cases h : f' = fin
  · subst h
    cases ch <;> simp [nock_exec, remRest, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hput, flag]
  · cases ch <;> simp [nock_exec, remRest, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hput, flag,
      termin_toNoun_inj, h]

/-- **The gate of the `+rep:by` of `$`**: where the model's step returns. -/
theorem rem_step (bl : TreapMap mugF Blob) (RD : Noun) (hR : RdOK bl RD) (fuel : Nat) (p : Nat × Blob)
    (s s' : Bool × TreapMap mugF Blob) (h : remG bl fuel s p = some s') :
    nock (C remMainG (C (C (Tr.pairNoun Blob.toNoun p) (remN s)) (remCore RD (HoonMap.toNoun Blob.toNoun bl))))
      remMainG = some (remN s') := by
  obtain ⟨o, b⟩ := p
  obtain ⟨ch, new⟩ := s
  unfold remG at h
  obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp h
  have hsw := rem_sw bl RD hR fuel o b (remN (ch, new)) f' hf'
  have hr := rem_rest o b ch new RD (HoonMap.toNoun Blob.toNoun bl) f'
  unfold remGS at hsw hr
  simp only [Tr.pairNoun]
  conv => lhs; arg 2; unfold remMainG
  rw [nock_op8, hsw]
  exact hr

/-! ## The gate, given `readers` -/

/-- The arm `$` of the core. -/
def remMainArm : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 767) (C (A 10)
    (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7)
    (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) remMainB) (C (C (A 1) remMainG) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))

theorem rem_core_main (RD BL : Noun) : slot? 10 (remCore RD BL) = some remMainArm := by rfl

/-- The model's fold in the order of `rap`. -/
theorem rem_fold (bl : TreapMap mugF Blob) (fuel : Nat) :
    Opt.removeEmptyMiddle fuel bl = (TreapMap.rap bl).foldlM (fun s p => remG bl fuel s p) (false, HoonMap.empty) := by
  unfold Opt.removeEmptyMiddle
  rw [optKeys_eq]
  exact foldl_keys_rap bl (fun s k v => remG bl fuel s (k, v)) _ (rap_get bl) (some _)

/-- **`+remove-empty-middle`, given `readers`**: where `removeEmptyMiddle
fuel` returns `(changed, new)` and the computation of `readers` returns a
noun with `RdOK`, the gate returns `[changed new]`. -/
theorem rem_gate_of (bl : TreapMap mugF Blob) (fuel : Nat) (r : Bool × TreapMap mugF Blob)
    (h : Opt.removeEmptyMiddle fuel bl = some r) (RD : Noun)
    (hRD : nock (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) remReaders = some RD) (hR : RdOK bl RD) :
    nock (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) remBody = some (remN r) := by
  rw [rem_fold] at h
  have ha : Tree (HoonMap.toNoun Blob.toNoun bl) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bl.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bl) = (TreapMap.rap bl).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bl
  have hrep := rep_gate_fwd (Tr.pairNoun Blob.toNoun) remN (fun p s => remG bl fuel s p) by.battery layer2
    remMainG (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (remCore RD (HoonMap.toNoun Blob.toNoun bl))
    _ ha _ hP (false, HoonMap.empty) r h (fun p _ s s' hs => rem_step bl RD hR fuel p s s' hs)
  have hb : C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (remN (false, HoonMap.empty)) = remMainB := by
    simp [remMainB, remAnyB, remN, flag, HoonMap.toNoun_empty]
  rw [hb] at hrep
  have hL := rem_core_layer2 RD (HoonMap.toNoun Blob.toNoun bl)
  have hm := rem_core_main RD (HoonMap.toNoun Blob.toNoun bl)
  conv => lhs; arg 2; unfold remBody
  rw [nock_op8, hRD]
  simp only [Option.bind_some]
  have e : C remBat (C RD (C remBody (C (HoonMap.toNoun Blob.toNoun bl) optC)))
      = remCore RD (HoonMap.toNoun Blob.toNoun bl) := rfl
  simp only [nock_exec, e, hm, Option.bind_some]
  exact hrep

end Compiler
end Formalization
