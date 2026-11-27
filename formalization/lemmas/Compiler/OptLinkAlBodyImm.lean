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

/-! ## `%con` -/

/-- The lens `|=(info-reg +<(hed-of (~(put in hed-of) new)))` of `%con`. -/
def alLensHed : Noun := C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))

/-- The lens `|=(info-reg +<(tel-of (~(put in tel-of) new)))` of `%con`. -/
def alLensTel : Noun := C (A 10) (C (C (A 30) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))

theorem al_lens_hed (x : Opt.InfoReg) (lb : Bool) (hs ts hs' : Noun) (d : Nat)
    (hp : putInF mugF (A d) hs = some hs') (fc : Noun) (hc : slot? 0x7ffffffff fc = some layer2)
    (hd : slot? 6 fc = some (A d)) :
    nock (C alLensHed (C (infoN x lb hs ts) fc)) alLensHed
      = some (infoN { x with hedOf := Opt.insN x.hedOf d } lb hs' ts) := by
  have hpi := put_in_gate layer2 gorIn_morIn_layer2 (A d) hs hs' hp
  unfold alLensHed
  simp [nock_exec, infoN, hc, hd, in.arm_at, in_arm, in.put.arm_at, put_in_arm, hpi]

theorem al_lens_tel (x : Opt.InfoReg) (lb : Bool) (hs ts ts' : Noun) (d : Nat)
    (hp : putInF mugF (A d) ts = some ts') (fc : Noun) (hc : slot? 0x7ffffffff fc = some layer2)
    (hd : slot? 6 fc = some (A d)) :
    nock (C alLensTel (C (infoN x lb hs ts) fc)) alLensTel
      = some (infoN { x with telOf := Opt.insN x.telOf d } lb hs ts') := by
  have hpi := put_in_gate layer2 gorIn_morIn_layer2 (A d) ts ts' hp
  unfold alLensTel
  simp [nock_exec, infoN, hc, hd, in.arm_at, in_arm, in.put.arm_at, put_in_arm, hpi]

/-- `+put:in` of `d` on a set related to `l`: related to `insN l d`. -/
theorem saw_insN {S : Noun} {l : List Nat} (h : SawRel S l) (d : Nat) :
    ∃ S', putInF mugF (A d) S = some S' ∧ SawRel S' (Opt.insN l d) := by
  obtain ⟨out, hp, hs, hh⟩ := putInF_spec mugF S (A d) h.1
  refine ⟨out, hp, hs, fun k => ?_⟩
  rw [hh, h.2 k]
  constructor
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨d, mem_insN.2 (Or.inl rfl), rfl⟩
    · exact ⟨n, mem_insN.2 (Or.inr hn), rfl⟩
  · rintro ⟨n, hn, rfl⟩
    rcases mem_insN.1 hn with rfl | hn
    · exact Or.inl rfl
    · exact Or.inr ⟨n, hn, rfl⟩

/-- **`%con`**. -/
theorem opOK_con (h t d : Nat) : OpOK (Ana.pickR FinMap) alOpCon (Pole.con h t d) := by
  intro K BN GI P1 P2 P3 P4 P5 NEW INFO IMMS REST Y Z OLD LOC IML st hR res st' hm
  simp only [Opt.aliasOp] at hm
  obtain ⟨hi, hhi, hm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨ti, hti, hm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨Nh, hNh, hrh, hgh⟩ := loc_got hR.2.1 hhi
  obtain ⟨Nt, hNt, hrt, hgt⟩ := loc_got hR.2.1 hti
  obtain ⟨lbh, hsh, tsh, rfl, hhsh, htsh, hlbh⟩ := hrh
  obtain ⟨lbt, hst, tst, rfl, hhst, htst, hlbt⟩ := hrt
  obtain ⟨H, hH, hHs, hHk⟩ := int_in (mug := mugF) layer2 gorIn_morIn_layer2 hsh tst hhsh.1 htst.1
  have hHr := sawRel_int hhsh htst hHs hHk
  obtain ⟨X, R, hX⟩ := alBat_rn
  have hrn := al_rn' X R NEW OLD (C INFO (C IMMS (C LOC (C IML REST)))) Y Z st.old hR.1
  have hL := optC_layer2
  by_cases hne : hi.hedOf.filter (· ∈ ti.telOf) ≠ []
  · rw [if_pos hne] at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨Lr, Rr, rfl⟩ := sawRel_root hHr hne
    obtain ⟨OLD', hp, hr⟩ := old_put hR.1 d (Ana.pickR FinMap (hi.hedOf.filter (· ∈ ti.telOf)))
    refine ⟨OLD', LOC, IML, ?_, hr, hR.2.1, hR.2.2⟩
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    simp [nock_exec, alOpCon, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm,
      by.put.arm_at, put_arm, in.arm_at, in_arm, in.int.arm_at, int_in_arm, hrn, hgh, hgt, hH, hp, optCons,
      infoN]
  · rw [if_neg hne] at hm
    have hH0 : H = A 0 := hHr.eq_nil.2 (by simpa using hne)
    subst hH0
    have hx0 : InfoRel (C (A 0) (C (A 1) (C (A 0) (C (A 0) (C (C (A 0) (A (st.old h)))
        (C (C (A 0) (A (st.old t))) (C (A 0) (A 0))))))))
        { hasHed := some (st.old h), hasTel := some (st.old t), isCell := true } :=
      ⟨false, A 0, A 0, rfl, sawRel_nil, sawRel_nil, rfl⟩
    obtain ⟨LOC1, hp1, hr1⟩ := loc_put hR.2.1 d hx0
    obtain ⟨l1, hl1, hm⟩ := Option.bind_eq_some_iff.1 hm
    obtain ⟨x1, hx1, rfl⟩ := Option.map_eq_some_iff.1 hl1
    obtain ⟨N1, hN1, hrel1, hg1⟩ := loc_got hr1 hx1
    obtain ⟨p1, q1, a1, b1, hLOC1⟩ := loc_node hN1
    have hja1 := jab_arm_node by.battery layer2 p1 q1 a1 b1
    rw [← hLOC1] at hja1
    obtain ⟨lb1, hs1, ts1, rfl, hhs1, hts1, hlb1⟩ := hrel1
    obtain ⟨hs1', hq1, hS1'⟩ := saw_insN hhs1 d
    obtain ⟨LOC2, hj1, hr2⟩ := loc_jab hr1 hN1 (infoN { x1 with hedOf := Opt.insN x1.hedOf d } lb1 hs1' ts1)
      (y := { x1 with hedOf := Opt.insN x1.hedOf d }) ⟨lb1, hs1', ts1, rfl, hS1', hts1, hlb1⟩
    obtain ⟨l2, hl2, hm⟩ := Option.map_eq_some_iff.1 hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨x2, hx2, rfl⟩ := Option.map_eq_some_iff.1 hl2
    obtain ⟨N2, hN2, hrel2, hg2⟩ := loc_got hr2 hx2
    obtain ⟨p2, q2, a2, b2, hLOC2⟩ := loc_node hN2
    have hja2 := jab_arm_node by.battery layer2 p2 q2 a2 b2
    rw [← hLOC2] at hja2
    obtain ⟨lb2, hs2, ts2, rfl, hhs2, hts2, hlb2⟩ := hrel2
    obtain ⟨ts2', hq2, hT2'⟩ := saw_insN hts2 d
    obtain ⟨LOC3, hj2, hr3⟩ := loc_jab hr2 hN2 (infoN { x2 with telOf := Opt.insN x2.telOf d } lb2 hs2 ts2')
      (y := { x2 with telOf := Opt.insN x2.telOf d }) ⟨lb2, hs2, ts2', rfl, hhs2, hT2', hlb2⟩
    refine ⟨OLD, LOC3, IML, ?_, hR.1, hr3, hR.2.2⟩
    have hj1' := fun fs fc (hc : slot? 0x7ffffffff fc = some layer2) (hd : slot? 6 fc = some (A d)) =>
      hj1 alLensHed fs fc (al_lens_hed x1 lb1 hs1 ts1 hs1' d hq1 fc hc hd)
    have hj2' := fun fs fc (hc : slot? 0x7ffffffff fc = some layer2) (hd : slot? 6 fc = some (A d)) =>
      hj2 alLensTel fs fc (al_lens_tel x2 lb2 hs2 ts2 ts2' d hq2 fc hc hd)
    unfold alLensHed at hj1'
    unfold alLensTel at hj2'
    unfold alOS alGenB
    rw [hX]
    generalize optC = OC at hL hrn
    unfold alRnArm at hrn
    simp [nock_exec, alOpCon, alRnArm, Pole.toNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm,
      by.put.arm_at, put_arm, by.jab.arm_at, in.arm_at, in_arm, in.int.arm_at, int_in_arm, hrn, hgh, hgt, hH,
      hp1, hg1, hg2, hja1, hja2, hj1', hj2', optCons, Tag.con, infoN]

end Compiler
end Formalization
