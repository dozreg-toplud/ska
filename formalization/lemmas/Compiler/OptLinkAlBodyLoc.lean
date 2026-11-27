import lemmas.Compiler.OptLinkAlBody
import lemmas.Hoon.JabBy

/-!
# `+alias`: the body of a block, the cases that read and edit `info-local` (phase 13, README Gaps 13)

The maps of facts `info-local.gen` (`InfoMapRel`): `+got:by` of a register the
model knows (`loc_got`), `+jab:by` with a lens that maps the noun there to a
noun related to the new fact (`loc_jab`, through `jab_gate_v`, a copy of
`jab_gate_at` of `CompSect.lean`, and `jab_arm_node`, the arm on a map that is
a node).

* `opOK_cel`: `%cel` is dropped when `is-cell` is known, else `is-cell` is set.
* `opOK_lob`: `%lob` is dropped when `is-loob` or a loobean `has-imm` is
  known (`InfoRel` fixes `is-loob ∨ loobImm`, which is all the test reads),
  else `is-loob` is set.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `+got:by` and `+jab:by` on `info-local` -/

/-- `(~(got by info-local.gen) r)` of a register the model knows. -/
theorem loc_got {LOC : Noun} {m : Opt.AInfo} (h : InfoMapRel LOC m) {r : Nat} {x : Opt.InfoReg}
    (hx : m r = some x) :
    ∃ N, Get LOC (A r) N ∧ InfoRel N x ∧
      nock (C by.got.battery (C (A r) (C by.battery (C LOC layer2)))) by.got.battery = some N := by
  obtain ⟨N, hN⟩ := h.2.2 r x hx
  obtain ⟨r', x', e, hx', hrel⟩ := h.2.1 _ _ hN
  have e' : r = r' := Noun.atom.inj e
  subst e'
  rw [hx] at hx'
  cases hx'
  exact ⟨N, hN, hrel, got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _
    (getF_some h.1 hN)⟩

/-- `+jab:by` with a gate that need only work on the value `v` at the key
(`jab_gate_at` of `CompSect.lean`). -/
theorem jab_gate_v {mug : Noun → Nat} (c : Noun) (hc : GorIn mug c) (B key fp fs fc : Noun)
    (g : Noun → Noun) (v : Noun) (hg : nock (C fp (C v fc)) fp = some (g v)) :
    ∀ (a out : Noun), getF mug key a = some (C (A 0) v) → jabF mug key g a = some out →
      nock (C by.jab.battery (C (C key (C fp (C fs fc))) (C B (C a c)))) by.jab.battery = some out := by
  intro a
  have hgor := gor_gate (mug := mug) c hc.2
  have hgo := hc.1
  fun_induction jabF mug key g a
  all_goals intro out hv h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals simp [getF, *] at hv
  all_goals first
    | (cases h
       subst hv
       nock_open by.jab.battery
       simp [nock_exec, *]
       done)
    | (nock_open by.jab.battery
       simp_all [nock_exec])

/-- The arm `jab` of the door on a map that is a node: its gate. -/
theorem jab_arm_node (B c p q l r : Noun) :
    nock (C B (C (C (C p q) (C l r)) c)) by.jab.arm
      = some (C by.jab.battery (C (C p (C (C (A 0) (A 15)) (C q (C q q)))) (C B (C (C (C p q) (C l r)) c)))) := by
  nock_open by.jab.arm; simp [nock_exec]

/-- The map of a key that the model knows is a node. -/
theorem loc_node {LOC k v : Noun} (h : Get LOC k v) : ∃ p q l r, LOC = C (C p q) (C l r) := by
  cases h <;> exact ⟨_, _, _, _, rfl⟩

/-- `(~(jab by info-local.gen) r lens)`, the lens mapping the noun `N` at `r`
to `N'`, related to `y`. -/
theorem loc_jab {LOC : Noun} {m : Opt.AInfo} (h : InfoMapRel LOC m) {r : Nat} {N : Noun}
    (hN : Get LOC (A r) N) (N' : Noun) {y : Opt.InfoReg} (hy : InfoRel N' y) :
    ∃ LOC', (∀ fp fs fc, nock (C fp (C N fc)) fp = some N' →
      nock (C by.jab.battery (C (C (A r) (C fp (C fs fc))) (C by.battery (C LOC layer2)))) by.jab.battery
        = some LOC') ∧ InfoMapRel LOC' (Opt.updA m r (some y)) := by
  obtain ⟨out, hj, ho, hg⟩ := jabF_spec (mug := mugF) (A r) (fun _ => N') h.1 hN
  refine ⟨out, fun fp fs fc hl => jab_gate_v layer2 gorIn_morIn_layer2.1 by.battery (A r) fp fs fc
    (fun _ => N') N hl LOC out (getF_some h.1 hN) hj, ho, ?_, ?_⟩
  · intro k v hv
    rcases (hg k v).1 hv with ⟨rfl, rfl⟩ | ⟨ne, hv'⟩
    · exact ⟨r, y, rfl, by simp [Opt.updA], hy⟩
    · obtain ⟨r', y', rfl, hy', hr⟩ := h.2.1 _ _ hv'
      have : r' ≠ r := fun e => ne (by rw [e])
      exact ⟨r', y', rfl, by simp [Opt.updA, this, hy'], hr⟩
  · intro r' y' hy'
    by_cases e : r' = r
    · subst e; exact ⟨N', (hg _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · simp only [Opt.updA, e, if_false] at hy'
      obtain ⟨w, hw⟩ := h.2.2 r' y' hy'
      exact ⟨w, (hg _ _).2 (Or.inr ⟨fun h' => e (Noun.atom.inj h'), hw⟩)⟩

/-! ## `%cel` and `%lob` -/

theorem opOK_cel (pick : List Nat → Nat) (p : Nat) : OpOK pick alOpCel (Pole.cel p) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp] at hm
  obtain ⟨ai, hai, hm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨N, hN, hrel, hgot⟩ := loc_got hR.2.1 hai
  obtain ⟨p0, q0, l0, r0, hLOC⟩ := loc_node hN
  have hja := jab_arm_node by.battery layer2 p0 q0 l0 r0
  rw [← hLOC] at hja
  obtain ⟨lb, hs, ts, rfl, hhs, hts, hlb⟩ := hrel
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  cases hc : ai.isCell
  · rw [hc] at hm
    simp only [Bool.false_eq_true, if_false, Opt.jabA, hai, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨LOC', hj, hr⟩ := loc_jab hR.2.1 hN (infoN { ai with isCell := true } lb hs ts)
      (y := { ai with isCell := true }) ⟨lb, hs, ts, rfl, hhs, hts, hlb⟩
    refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
    have hj' := fun fs fc => hj (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 6)))) fs fc
      (by simp [nock_exec, infoN, flag])
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    simp [nock_exec, alOpCel, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm,
      by.jab.arm_at, hja, hrn, hgot, hj', optCons, Tag.cel, infoN, hc, flag]
  · rw [hc] at hm
    simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨OLD, LOC, IML, ?_, hR⟩
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    simp [nock_exec, alOpCel, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm,
      hrn, hgot, optCons, infoN, hc, flag]

theorem opOK_lob (pick : List Nat → Nat) (p : Nat) : OpOK pick alOpLob (Pole.lob p) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp] at hm
  obtain ⟨ai, hai, hm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨N, hN, hrel, hgot⟩ := loc_got hR.2.1 hai
  obtain ⟨p0, q0, l0, r0, hLOC⟩ := loc_node hN
  have hja := jab_arm_node by.battery layer2 p0 q0 l0 r0
  rw [← hLOC] at hja
  obtain ⟨lb, hs, ts, rfl, hhs, hts, hlb⟩ := hrel
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  by_cases hc : (ai.isLoob || ai.loobImm) = true
  · rw [if_pos hc] at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨OLD, LOC, IML, ?_, hR⟩
    have ht : (lb || ai.loobImm) = true := by rw [hlb]; exact hc
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    generalize ai.isLoob = il at hgot ht
    rcases ai with ⟨c, l, h, t, hh, ht', dd, im⟩
    cases lb <;> rcases im with _ | ⟨_ | _ | n⟩ | ⟨p', q'⟩ <;>
      simp [Opt.InfoReg.loobImm] at ht <;>
      simp [nock_exec, alOpLob, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm,
        hrn, hgot, optCons, infoN, flag, unitNoun, ht]
  · rw [if_neg hc] at hm
    simp only [Opt.jabA, hai, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    have ht : (lb || ai.loobImm) = false := by rw [hlb]; simpa using hc
    obtain ⟨LOC', hj, hr⟩ := loc_jab hR.2.1 hN (infoN { ai with isLoob := true } true hs ts)
      (y := { ai with isLoob := true }) ⟨true, hs, ts, rfl, hhs, hts, by simp⟩
    refine ⟨OLD, LOC', IML, ?_, hR.1, hr, hR.2.2⟩
    have hj' := fun fs fc => hj (C (A 10) (C (C (A 6) (C (A 1) (A 0))) (C (A 0) (A 6)))) fs fc
      (by simp [nock_exec, infoN, flag])
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    rcases ai with ⟨c, l, h, t, hh, ht', dd, im⟩
    cases lb <;> rcases im with _ | ⟨_ | _ | n⟩ | ⟨p', q'⟩ <;>
      simp [Opt.InfoReg.loobImm] at ht <;>
      simp [nock_exec, alOpLob, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm,
        by.jab.arm_at, hja, hrn, hgot, hj', optCons, Tag.lob, infoN, flag, unitNoun, ht]

end Compiler
end Formalization
