import lemmas.Compiler.OptLinkAlBodyLoc

/-!
# `+alias`: the body of a block, `%imm` and `%con` (phase 13, README Gaps 13)

The two cases that pick a member of a set (`n.res`, `n.intersect`): the root
of the set's treap, which is `Ana.pickR FinMap` of the model's list
(`sawRel_root`), so they link for `pick = Ana.pickR FinMap`.

* `iml_get`, `iml_put`: `+get:ju` and `+put:ju` on `imms-local.gen`
  (`ImmsRel`).
* `opOK_imm`: `%imm` renames `d` to a register known to hold the noun, or
  keeps the op, puts `has-imm` at `d` and `d` in the set of the noun.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local instance] SkaModel.Ana.tkeyNat

theorem mem_insN {x d : Nat} {l : List Nat} : x ∈ Opt.insN l d ↔ x = d ∨ x ∈ l := by
  unfold Opt.insN
  split
  · rename_i h
    constructor
    · exact Or.inr
    · rintro (rfl | h') <;> assumption
  · simp

/-- `(~(get ju imms-local.gen) n)`: the set of the registers of `n`. -/
theorem iml_get {IML : Noun} {m : Opt.AImms} (h : ImmsRel IML m) (n : Noun) :
    ∃ S, nock (C ju.get.battery (C n (C ju.battery (C IML layer2)))) ju.get.battery = some S ∧
      SawRel S (m n) := by
  by_cases hx : ∃ s, Get IML n s
  · obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_, (h.2.1 _ _ hs).1⟩
    have := ju_get_gate layer2 juIn_layer2' ju.battery n IML _ (getF_some h.1 hs)
    simpa [unUnit] using this
  · refine ⟨A 0, ?_, ?_⟩
    · have := ju_get_gate layer2 juIn_layer2' ju.battery n IML _ (getF_none h.1 (fun v hv => hx ⟨v, hv⟩))
      simpa [unUnit] using this
    · have : m n = [] := Classical.byContradiction fun hne => by
        obtain ⟨v, hv⟩ := h.2.2 n hne
        exact hx ⟨v, hv⟩
      rw [this]; exact sawRel_nil

/-- `(~(put ju imms-local.gen) n d)`: `d` joins the set of `n`. -/
theorem iml_put {IML : Noun} {m : Opt.AImms} (h : ImmsRel IML m) (n : Noun) (d : Nat) :
    ∃ IML', nock (C ju.put.battery (C (C n (A d)) (C ju.battery (C IML layer2)))) ju.put.battery = some IML' ∧
      ImmsRel IML' (fun k => if k = n then Opt.insN (m k) d else m k) := by
  obtain ⟨out, e, hev, hm, he, hhe, hg⟩ :=
    ju_put layer2 juIn_layer2' IML n (A d) h.1 (fun s hs => (h.2.1 _ _ hs).1.1)
  have hS : SawRel e (Opt.insN (m n) d) := by
    refine ⟨he, fun k => ?_⟩
    rw [hhe]
    constructor
    · rintro (rfl | ⟨s, hs, hk⟩)
      · exact ⟨d, mem_insN.2 (Or.inl rfl), rfl⟩
      · obtain ⟨x, hx, rfl⟩ := ((h.2.1 _ _ hs).1.2 k).1 hk
        exact ⟨x, mem_insN.2 (Or.inr hx), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rcases mem_insN.1 hx with rfl | hx
      · exact Or.inl rfl
      · obtain ⟨s, hs⟩ := h.2.2 n (List.ne_nil_of_mem hx)
        exact Or.inr ⟨s, hs, ((h.2.1 _ _ hs).1.2 _).2 ⟨x, hx, rfl⟩⟩
  refine ⟨out, nock_eq_some_iff.2 hev, hm, ?_, ?_⟩
  · intro k v hv
    rcases (hg k v).1 hv with ⟨rfl, rfl⟩ | ⟨ne, hv'⟩
    · refine ⟨by simpa using hS, ?_⟩
      intro e0
      have := (hS.2 (A d)).2 ⟨d, mem_insN.2 (Or.inl rfl), rfl⟩
      rw [e0] at this
      exact not_has_atom this
    · simpa [ne] using h.2.1 _ _ hv'
  · intro k hk
    by_cases e' : k = n
    · subst e'; exact ⟨e, (hg _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · simp only [e', if_false] at hk
      obtain ⟨w, hw⟩ := h.2.2 k hk
      exact ⟨w, (hg _ _).2 (Or.inr ⟨e', hw⟩)⟩

/-- **`%imm`**. -/
theorem opOK_imm (n : Noun) (d : Nat) : OpOK (Ana.pickR FinMap) alOpImm (Pole.imm n d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  obtain ⟨S, hget, hS⟩ := iml_get hR.2.2 n
  have hL := optC_layer2
  by_cases hne : st.imml n ≠ []
  · simp only [Opt.aliasOp, hne, ne_eq, not_false_eq_true, if_true, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨Lr, Rr, rfl⟩ := sawRel_root hS hne
    obtain ⟨OLD', hp, hr⟩ := old_put hR.1 d (Ana.pickR FinMap (st.imml n))
    refine ⟨OLD', LOC, IML, ?_, hr, hR.2.1, hR.2.2⟩
    unfold alOS alGenB
    generalize optC = OC at hL
    simp [nock_exec, alOpImm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, ju.arm_at, ju_arm,
      ju.get.arm_at, ju_get_arm, hget, hp, optCons]
  · have hne' : st.imml n = [] := by simpa using hne
    simp only [Opt.aliasOp, hne, if_false, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    have hS0 : S = A 0 := hS.eq_nil.2 hne'
    subst hS0
    have hx0 : InfoRel (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) n))))))))
        { hasImm := some n } := ⟨false, A 0, A 0, rfl, sawRel_nil, sawRel_nil, rfl⟩
    obtain ⟨LOC', hp, hr⟩ := loc_put hR.2.1 d hx0
    obtain ⟨IML', hq, hq'⟩ := iml_put hR.2.2 n d
    refine ⟨OLD, LOC', IML', ?_, hR.1, hr, hq'⟩
    unfold alOS alGenB
    generalize optC = OC at hL
    simp [nock_exec, alOpImm, Pole.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, ju.arm_at, ju_arm,
      ju.get.arm_at, ju_get_arm, ju.put.arm_at, ju_put_arm, hget, hp, hq, optCons, Tag.imm]

end Compiler
end Formalization
