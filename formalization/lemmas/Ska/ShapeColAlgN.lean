import lemmas.Ska.ShapeColAlg
import lemmas.Ska.SccLoopMsg

/-!
# `+uni-need-ord` is a semilattice join on normal shapes (the fuel of `fixLoop`, part 1)

`Ska/ShapeColAlg.lean` found by enumeration that `uniOrd` is commutative on
every shape and associative on `normal` ones (no `[%pair [%none ~] [%none ~]]`
anywhere).  Proved here:

* **`uniOrd_comm`**: `uniOrd` is commutative on every shape (induction);
* the reading of a shape as a register bit and an optional split, with the
  union `uniN` (a register where either has one, the splits united by
  halves): `uniN` is idempotent, commutative and associative on every shape
  (`uniN_idem`, `uniN_comm`, `uniN_assoc`), and `none` only from two `none`s
  (`uniN_eq_none`);
* **`uniOrd_eq_uniN`**: on normal shapes `uniOrd` is `uniN` (the only places
  where they differ need a `pair none none`: `uniBoth` of two `none` halves
  gives `[%this ~]`, `+cons-need` of two `none` halves gives `[%none ~]`);
* so **`uniOrd_assoc`** on normal shapes;
* `normal` shapes are kept by `uniOrd` (`ordNormal_uniOrd`), `msgOrd`
  (`ordNormal_msgOrd`), `msgFix` (`ordNormal_msgFix`), and none of `uniOrd`,
  `msgOrd` deepens a shape (`ordDepth_uniOrd`, `ordDepth_msgOrd`);
* the weight `ordW` (a register counts `1`, a split `1`): `uniN` never lowers
  it and raises it when it changes the shape (`ordW_uniN`), it is at most
  `wB d` at depth `d` (`ordW_le_wB`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

/-! ## Commutativity on every shape -/

theorem uniOrd_pp (p q p' q' : NeedOrd) :
    uniOrd (NeedOrd.pair p q) (NeedOrd.pair p' q') =
      if NeedOrd.pair p q = NeedOrd.pair p' q' then NeedOrd.pair p q
      else consOrd (uniOrd p p') (uniOrd q q') := by
  rw [uniOrd]

theorem uniOrd_pb (p q h t : NeedOrd) :
    uniOrd (NeedOrd.pair p q) (NeedOrd.both h t) = uniBoth (uniOrd p h) (uniOrd q t) := by
  rw [uniOrd]; simp

theorem uniOrd_bp (p q h t : NeedOrd) :
    uniOrd (NeedOrd.both h t) (NeedOrd.pair p q) = uniBoth (uniOrd h p) (uniOrd t q) := by
  rw [uniOrd]; simp

theorem uniOrd_bb (h t h' t' : NeedOrd) :
    uniOrd (NeedOrd.both h t) (NeedOrd.both h' t') =
      if NeedOrd.both h t = NeedOrd.both h' t' then NeedOrd.both h t
      else uniBoth (uniOrd h h') (uniOrd t t') := by
  rw [uniOrd]

theorem uniOrd_none_right (a : NeedOrd) : uniOrd a NeedOrd.none = a := by
  cases a <;> rw [uniOrd] <;> simp

theorem uniOrd_self (a : NeedOrd) : uniOrd a a = a := by
  unfold uniOrd; simp

/-- **`+uni-need-ord` is commutative** on every shape. -/
theorem uniOrd_comm (a b : NeedOrd) : uniOrd a b = uniOrd b a := by
  induction a generalizing b with
  | pair p q ihp ihq =>
    cases b with
    | pair p' q' =>
      rw [uniOrd_pp, uniOrd_pp, ihp p', ihq q']
      by_cases h : NeedOrd.pair p q = NeedOrd.pair p' q'
      · rw [if_pos h, if_pos h.symm, h]
      · rw [if_neg h, if_neg (Ne.symm h)]
    | both h t => rw [uniOrd_pb, uniOrd_bp, ihp h, ihq t]
    | this => rw [uniOrd, uniOrd]; simp
    | none => rw [uniOrd_none_right, uniOrd_none_left]
  | both h t ihh iht =>
    cases b with
    | pair p q => rw [uniOrd_pb, uniOrd_bp, ihh p, iht q]
    | both h' t' =>
      rw [uniOrd_bb, uniOrd_bb, ihh h', iht t']
      by_cases e : NeedOrd.both h t = NeedOrd.both h' t'
      · rw [if_pos e, if_pos e.symm, e]
      · rw [if_neg e, if_neg (Ne.symm e)]
    | this => rw [uniOrd, uniOrd]; simp
    | none => rw [uniOrd_none_right, uniOrd_none_left]
  | this =>
    cases b with
    | none => rw [uniOrd_none_right, uniOrd_none_left]
    | this => rfl
    | _ => unfold uniOrd; simp
  | none => rw [uniOrd_none_right, uniOrd_none_left]

/-! ## The reading: a register bit and an optional split -/

/-- The union on the reading of a shape as a register bit and an optional
split. -/
def uniN : NeedOrd → NeedOrd → NeedOrd
  | NeedOrd.none, b => b
  | NeedOrd.this, NeedOrd.none => NeedOrd.this
  | NeedOrd.this, NeedOrd.this => NeedOrd.this
  | NeedOrd.this, NeedOrd.both h t => NeedOrd.both h t
  | NeedOrd.this, NeedOrd.pair p q => NeedOrd.both p q
  | NeedOrd.both h t, NeedOrd.none => NeedOrd.both h t
  | NeedOrd.both h t, NeedOrd.this => NeedOrd.both h t
  | NeedOrd.both h t, NeedOrd.both h' t' => NeedOrd.both (uniN h h') (uniN t t')
  | NeedOrd.both h t, NeedOrd.pair p q => NeedOrd.both (uniN h p) (uniN t q)
  | NeedOrd.pair p q, NeedOrd.none => NeedOrd.pair p q
  | NeedOrd.pair p q, NeedOrd.this => NeedOrd.both p q
  | NeedOrd.pair p q, NeedOrd.both h t => NeedOrd.both (uniN p h) (uniN q t)
  | NeedOrd.pair p q, NeedOrd.pair p' q' => NeedOrd.pair (uniN p p') (uniN q q')

theorem uniN_none_right (a : NeedOrd) : uniN a NeedOrd.none = a := by
  cases a <;> rfl

theorem uniN_idem (a : NeedOrd) : uniN a a = a := by
  induction a with
  | pair p q ihp ihq => simp [uniN, ihp, ihq]
  | both h t ihh iht => simp [uniN, ihh, iht]
  | this => rfl
  | none => rfl

theorem uniN_comm (a b : NeedOrd) : uniN a b = uniN b a := by
  induction a generalizing b with
  | pair p q ihp ihq => cases b <;> simp [uniN, ihp, ihq]
  | both h t ihh iht => cases b <;> simp [uniN, ihh, iht]
  | this => cases b <;> rfl
  | none => cases b <;> rfl

theorem uniN_assoc (a b c : NeedOrd) : uniN (uniN a b) c = uniN a (uniN b c) := by
  induction a generalizing b c with
  | pair p q ihp ihq => cases b <;> cases c <;> simp [uniN, ihp, ihq]
  | both h t ihh iht => cases b <;> cases c <;> simp [uniN, ihh, iht]
  | this => cases b <;> cases c <;> rfl
  | none => rfl

theorem uniN_eq_none (a b : NeedOrd) : uniN a b = NeedOrd.none ↔ a = NeedOrd.none ∧ b = NeedOrd.none := by
  cases a <;> cases b <;> simp [uniN]

/-! ## Normal shapes -/

theorem ordNormal_pair (p q : NeedOrd) :
    ordNormal (NeedOrd.pair p q) = true ↔
      ¬ (p = NeedOrd.none ∧ q = NeedOrd.none) ∧ ordNormal p = true ∧ ordNormal q = true := by
  cases p <;> cases q <;> simp [ordNormal]

theorem ordNormal_both (h t : NeedOrd) :
    ordNormal (NeedOrd.both h t) = true ↔ ordNormal h = true ∧ ordNormal t = true := by
  simp [ordNormal]

theorem ordNormal_consOrd {a b : NeedOrd} (ha : ordNormal a = true) (hb : ordNormal b = true) :
    ordNormal (consOrd a b) = true := by
  unfold consOrd
  split
  · rfl
  · rename_i h; exact (ordNormal_pair a b).2 ⟨h, ha, hb⟩

theorem ordNormal_uniN : ∀ {a b : NeedOrd}, ordNormal a = true → ordNormal b = true → ordNormal (uniN a b) = true
  | NeedOrd.none, _, _, hb => hb
  | NeedOrd.this, NeedOrd.none, _, _ => rfl
  | NeedOrd.this, NeedOrd.this, _, _ => rfl
  | NeedOrd.this, NeedOrd.both _ _, _, hb => hb
  | NeedOrd.this, NeedOrd.pair _ _, _, hb => by
    rw [ordNormal_pair] at hb; rw [uniN, ordNormal_both]; exact hb.2
  | NeedOrd.both _ _, NeedOrd.none, ha, _ => ha
  | NeedOrd.both _ _, NeedOrd.this, ha, _ => ha
  | NeedOrd.both h t, NeedOrd.both h' t', ha, hb => by
    rw [ordNormal_both] at ha hb; rw [uniN, ordNormal_both]
    exact ⟨ordNormal_uniN ha.1 hb.1, ordNormal_uniN ha.2 hb.2⟩
  | NeedOrd.both h t, NeedOrd.pair p q, ha, hb => by
    rw [ordNormal_both] at ha; rw [ordNormal_pair] at hb; rw [uniN, ordNormal_both]
    exact ⟨ordNormal_uniN ha.1 hb.2.1, ordNormal_uniN ha.2 hb.2.2⟩
  | NeedOrd.pair _ _, NeedOrd.none, ha, _ => ha
  | NeedOrd.pair _ _, NeedOrd.this, ha, _ => by
    rw [ordNormal_pair] at ha; rw [uniN, ordNormal_both]; exact ha.2
  | NeedOrd.pair p q, NeedOrd.both h t, ha, hb => by
    rw [ordNormal_pair] at ha; rw [ordNormal_both] at hb; rw [uniN, ordNormal_both]
    exact ⟨ordNormal_uniN ha.2.1 hb.1, ordNormal_uniN ha.2.2 hb.2⟩
  | NeedOrd.pair p q, NeedOrd.pair p' q', ha, hb => by
    rw [ordNormal_pair] at ha hb; rw [uniN, ordNormal_pair]
    refine ⟨?_, ordNormal_uniN ha.2.1 hb.2.1, ordNormal_uniN ha.2.2 hb.2.2⟩
    rintro ⟨e1, e2⟩
    rw [uniN_eq_none] at e1 e2
    exact ha.1 ⟨e1.1, e2.1⟩

theorem consOrd_of_ne {a b : NeedOrd} (h : ¬ (a = NeedOrd.none ∧ b = NeedOrd.none)) :
    consOrd a b = NeedOrd.pair a b := by
  unfold consOrd; rw [if_neg h]

theorem uniBoth_of_ne {a b : NeedOrd} (h : ¬ (a = NeedOrd.none ∧ b = NeedOrd.none)) :
    uniBoth a b = NeedOrd.both a b := by
  unfold uniBoth; rw [consOrd_of_ne h]

/-- **On normal shapes `+uni-need-ord` is the union `uniN`.** -/
theorem uniOrd_eq_uniN : ∀ {a b : NeedOrd}, ordNormal a = true → ordNormal b = true → uniOrd a b = uniN a b
  | NeedOrd.none, b, _, _ => by rw [uniOrd_none_left]; rfl
  | NeedOrd.this, NeedOrd.none, _, _ => rfl
  | NeedOrd.this, NeedOrd.this, _, _ => rfl
  | NeedOrd.this, NeedOrd.both _ _, _, _ => by rw [uniOrd]; simp [uniN]
  | NeedOrd.this, NeedOrd.pair _ _, _, _ => by rw [uniOrd]; simp [uniN]
  | NeedOrd.both _ _, NeedOrd.none, _, _ => by rw [uniOrd_none_right]; rfl
  | NeedOrd.both _ _, NeedOrd.this, _, _ => by rw [uniOrd]; simp [uniN]
  | NeedOrd.both h t, NeedOrd.both h' t', ha, hb => by
    rw [ordNormal_both] at ha hb
    rw [uniOrd_bb, uniOrd_eq_uniN ha.1 hb.1, uniOrd_eq_uniN ha.2 hb.2]
    by_cases e : NeedOrd.both h t = NeedOrd.both h' t'
    · rw [if_pos e]; injection e with e1 e2; subst e1; subst e2; simp [uniN, uniN_idem]
    · rw [if_neg e, uniN]
      refine uniBoth_of_ne ?_
      rintro ⟨e1, e2⟩
      rw [uniN_eq_none] at e1 e2
      exact e (by rw [e1.1, e1.2, e2.1, e2.2])
  | NeedOrd.both h t, NeedOrd.pair p q, ha, hb => by
    rw [ordNormal_both] at ha; rw [ordNormal_pair] at hb
    rw [uniOrd_bp, uniOrd_eq_uniN ha.1 hb.2.1, uniOrd_eq_uniN ha.2 hb.2.2, uniN]
    refine uniBoth_of_ne ?_
    rintro ⟨e1, e2⟩
    rw [uniN_eq_none] at e1 e2
    exact hb.1 ⟨e1.2, e2.2⟩
  | NeedOrd.pair _ _, NeedOrd.none, _, _ => by rw [uniOrd_none_right]; rfl
  | NeedOrd.pair _ _, NeedOrd.this, _, _ => by rw [uniOrd]; simp [uniN]
  | NeedOrd.pair p q, NeedOrd.both h t, ha, hb => by
    rw [ordNormal_pair] at ha; rw [ordNormal_both] at hb
    rw [uniOrd_pb, uniOrd_eq_uniN ha.2.1 hb.1, uniOrd_eq_uniN ha.2.2 hb.2, uniN]
    refine uniBoth_of_ne ?_
    rintro ⟨e1, e2⟩
    rw [uniN_eq_none] at e1 e2
    exact ha.1 ⟨e1.1, e2.1⟩
  | NeedOrd.pair p q, NeedOrd.pair p' q', ha, hb => by
    rw [ordNormal_pair] at ha hb
    rw [uniOrd_pp, uniOrd_eq_uniN ha.2.1 hb.2.1, uniOrd_eq_uniN ha.2.2 hb.2.2]
    by_cases e : NeedOrd.pair p q = NeedOrd.pair p' q'
    · rw [if_pos e]; injection e with e1 e2; subst e1; subst e2; simp [uniN, uniN_idem]
    · rw [if_neg e, uniN]
      refine consOrd_of_ne ?_
      rintro ⟨e1, e2⟩
      rw [uniN_eq_none] at e1 e2
      exact ha.1 ⟨e1.1, e2.1⟩

theorem ordNormal_uniOrd {a b : NeedOrd} (ha : ordNormal a = true) (hb : ordNormal b = true) :
    ordNormal (uniOrd a b) = true := by
  rw [uniOrd_eq_uniN ha hb]; exact ordNormal_uniN ha hb

/-- **`+uni-need-ord` is associative on normal shapes.** -/
theorem uniOrd_assoc {a b c : NeedOrd} (ha : ordNormal a = true) (hb : ordNormal b = true)
    (hc : ordNormal c = true) : uniOrd (uniOrd a b) c = uniOrd a (uniOrd b c) := by
  rw [uniOrd_eq_uniN ha hb, uniOrd_eq_uniN hb hc, uniOrd_eq_uniN (ordNormal_uniN ha hb) hc,
    uniOrd_eq_uniN ha (ordNormal_uniN hb hc), uniN_assoc]

/-! ## Depth -/

theorem ordDepth_uniN : ∀ a b : NeedOrd, ordDepth (uniN a b) ≤ max (ordDepth a) (ordDepth b)
  | NeedOrd.none, b => by simp [uniN, ordDepth]
  | NeedOrd.this, NeedOrd.none => by simp [uniN, ordDepth]
  | NeedOrd.this, NeedOrd.this => by simp [uniN, ordDepth]
  | NeedOrd.this, NeedOrd.both _ _ => by simp [uniN, ordDepth]
  | NeedOrd.this, NeedOrd.pair _ _ => by simp [uniN, ordDepth]
  | NeedOrd.both _ _, NeedOrd.none => by simp [uniN, ordDepth]
  | NeedOrd.both _ _, NeedOrd.this => by simp [uniN, ordDepth]
  | NeedOrd.both h t, NeedOrd.both h' t' => by
    have := ordDepth_uniN h h'; have := ordDepth_uniN t t'; simp only [uniN, ordDepth]; omega
  | NeedOrd.both h t, NeedOrd.pair p q => by
    have := ordDepth_uniN h p; have := ordDepth_uniN t q; simp only [uniN, ordDepth]; omega
  | NeedOrd.pair _ _, NeedOrd.none => by simp [uniN, ordDepth]
  | NeedOrd.pair _ _, NeedOrd.this => by simp [uniN, ordDepth]
  | NeedOrd.pair p q, NeedOrd.both h t => by
    have := ordDepth_uniN p h; have := ordDepth_uniN q t; simp only [uniN, ordDepth]; omega
  | NeedOrd.pair p q, NeedOrd.pair p' q' => by
    have := ordDepth_uniN p p'; have := ordDepth_uniN q q'; simp only [uniN, ordDepth]; omega

theorem ordDepth_uniOrd {a b : NeedOrd} (ha : ordNormal a = true) (hb : ordNormal b = true) :
    ordDepth (uniOrd a b) ≤ max (ordDepth a) (ordDepth b) := by
  rw [uniOrd_eq_uniN ha hb]; exact ordDepth_uniN a b

/-! ## `msgOrd` and `msgFix` keep normal shapes normal, `msgOrd` does not deepen -/

theorem ordNormal_hed {a : NeedOrd} (h : ordNormal a = true) : ordNormal (ordHed a) = true := by
  cases a with
  | pair p q => exact ((ordNormal_pair p q).1 h).2.1
  | both x y => exact ((ordNormal_both x y).1 h).1
  | _ => rfl

theorem ordNormal_tel {a : NeedOrd} (h : ordNormal a = true) : ordNormal (ordTel a) = true := by
  cases a with
  | pair p q => exact ((ordNormal_pair p q).1 h).2.2
  | both x y => exact ((ordNormal_both x y).1 h).2
  | _ => rfl

theorem ordNormal_mkB (b : Bool) {x y : NeedOrd} (hx : ordNormal x = true) (hy : ordNormal y = true) :
    ordNormal (mkB b x y) = true := by
  cases b
  · exact ordNormal_consOrd hx hy
  · exact (ordNormal_both x y).2 ⟨hx, hy⟩

theorem msgCap_cases (x : NeedOrd) : msgCap x = NeedOrd.this ∨ msgCap x = x := by
  unfold msgCap; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ordNormal_msgCap {x : NeedOrd} (h : ordNormal x = true) : ordNormal (msgCap x) = true := by
  rcases msgCap_cases x with e | e <;> rw [e]
  · rfl
  · exact h

theorem ordDepth_consOrd (x y : NeedOrd) : ordDepth (consOrd x y) ≤ max (ordDepth x) (ordDepth y) + 1 := by
  unfold consOrd; split <;> simp [ordDepth]

theorem ordDepth_mkB (b : Bool) (x y : NeedOrd) : ordDepth (mkB b x y) ≤ max (ordDepth x) (ordDepth y) + 1 := by
  cases b
  · exact ordDepth_consOrd x y
  · simp [mkB, ordDepth]

theorem ordDepth_msgCap (x : NeedOrd) : ordDepth (msgCap x) ≤ ordDepth x := by
  rcases msgCap_cases x with e | e <;> rw [e]
  · simp [ordDepth]
  · exact Nat.le_refl _

/-- `(msg-need-ord [%none ~] d less)` is always normal, never deeper. -/
theorem msgNone_normal_depth : ∀ (d : NeedOrd) (c : Cape),
    ordNormal (msgNone d c) = true ∧ ordDepth (msgNone d c) ≤ ordDepth d
  | NeedOrd.none, _ => by simp [msgNone, ordNormal, ordDepth]
  | NeedOrd.this, _ => by simp [msgNone, ordNormal, ordDepth]
  | NeedOrd.pair p q, Cape.cell lh lt => by
    have hp := msgNone_normal_depth p lh; have hq := msgNone_normal_depth q lt
    rw [msgNone]
    refine ⟨ordNormal_msgCap (ordNormal_consOrd hp.1 hq.1), ?_⟩
    have := ordDepth_msgCap (consOrd (msgNone p lh) (msgNone q lt))
    have := ordDepth_consOrd (msgNone p lh) (msgNone q lt)
    simp only [ordDepth]; omega
  | NeedOrd.both h t, Cape.cell lh lt => by
    have hh := msgNone_normal_depth h lh; have ht := msgNone_normal_depth t lt
    rw [msgNone]
    refine ⟨ordNormal_msgCap ((ordNormal_both _ _).2 ⟨hh.1, ht.1⟩), ?_⟩
    have := ordDepth_msgCap (NeedOrd.both (msgNone h lh) (msgNone t lt))
    simp only [ordDepth] at this ⊢; omega
  | NeedOrd.pair _ _, Cape.yes => by simp [msgNone, ordNormal, ordDepth]
  | NeedOrd.pair _ _, Cape.no => by simp [msgNone, ordNormal, ordDepth]
  | NeedOrd.both _ _, Cape.yes => by simp [msgNone, ordNormal, ordDepth]
  | NeedOrd.both _ _, Cape.no => by simp [msgNone, ordNormal, ordDepth]

theorem ordDepth_hed_tel {d : NeedOrd} (hd : isLeaf d = false) :
    max (ordDepth (ordHed d)) (ordDepth (ordTel d)) + 1 = ordDepth d := by
  cases d <;> simp_all [isLeaf, ordHed, ordTel, ordDepth]

theorem msgOne_normal_depth (s d : NeedOrd) (c : Cape) (hd : isLeaf d = false) :
    ordNormal (msgOne s d c) = true ∧ ordDepth (msgOne s d c) ≤ ordDepth d := by
  cases c with
  | cell lh lt =>
    rw [msgOne_cell s d lh lt hd]
    have h1 := msgNone_normal_depth (ordHed d) lh
    have h2 := msgNone_normal_depth (ordTel d) lt
    refine ⟨ordNormal_msgCap (ordNormal_mkB _ h1.1 h2.1), ?_⟩
    have := ordDepth_msgCap (mkB (s == NeedOrd.this || isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt))
    have := ordDepth_mkB (s == NeedOrd.this || isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt)
    have := ordDepth_hed_tel hd
    omega
  | yes => simp [msgOne, ordNormal, ordDepth]
  | no => simp [msgOne, ordNormal, ordDepth]

/-- **`+msg-need-ord` keeps normal shapes normal and does not deepen them.** -/
theorem msgOrd_normal_depth : ∀ (a b : NeedOrd) (c : Cape), ordNormal a = true → ordNormal b = true →
    ordNormal (msgOrd a b c) = true ∧ ordDepth (msgOrd a b c) ≤ max (ordDepth a) (ordDepth b) := by
  refine ord_induct (Q := fun a => ∀ b c, ordNormal a = true → ordNormal b = true →
    ordNormal (msgOrd a b c) = true ∧ ordDepth (msgOrd a b c) ≤ max (ordDepth a) (ordDepth b)) ?_ ?_
  · intro a ha b c hna hnb
    by_cases hab : a = b
    · rw [hab, msgOrd_self]; exact ⟨hnb, Nat.le_max_right _ _⟩
    cases hb : isLeaf b
    · rw [msgOrd_left _ _ _ ha hb]
      have := msgOne_normal_depth a b c hb
      exact ⟨this.1, Nat.le_trans this.2 (Nat.le_max_right _ _)⟩
    · rw [msgOrd_leaf _ _ _ ha hb hab]; simp [ordNormal, ordDepth]
  · intro a ha ih1 ih2 b c hna hnb
    by_cases hab : a = b
    · rw [hab, msgOrd_self]; exact ⟨hnb, Nat.le_max_right _ _⟩
    cases hb : isLeaf b
    · rw [msgOrd_inner _ _ _ ha hb hab]
      have h1 := ih1 (ordHed b) (capeHed c) (ordNormal_hed hna) (ordNormal_hed hnb)
      have h2 := ih2 (ordTel b) (capeTel c) (ordNormal_tel hna) (ordNormal_tel hnb)
      refine ⟨ordNormal_mkB _ h1.1 h2.1, ?_⟩
      have := ordDepth_mkB (isB a || isB b) (msgOrd (ordHed a) (ordHed b) (capeHed c))
        (msgOrd (ordTel a) (ordTel b) (capeTel c))
      have := ordDepth_hed_tel ha; have := ordDepth_hed_tel hb
      omega
    · rw [msgOrd_right _ _ _ hb ha]
      have := msgOne_normal_depth b a c ha
      exact ⟨this.1, Nat.le_trans this.2 (Nat.le_max_left _ _)⟩

theorem ordNormal_msgOrd {a b : NeedOrd} (c : Cape) (ha : ordNormal a = true) (hb : ordNormal b = true) :
    ordNormal (msgOrd a b c) = true := (msgOrd_normal_depth a b c ha hb).1

theorem ordDepth_msgOrd {a b : NeedOrd} (c : Cape) (ha : ordNormal a = true) (hb : ordNormal b = true) :
    ordDepth (msgOrd a b c) ≤ max (ordDepth a) (ordDepth b) := (msgOrd_normal_depth a b c ha hb).2

theorem ordNormal_fixEnd (here : Bool) {x : NeedOrd} (h : ordNormal x = true) : ordNormal (fixEnd here x) = true := by
  cases x with
  | pair p q =>
    have := (ordNormal_pair p q).1 h
    cases here
    · exact h
    · exact (ordNormal_both p q).2 ⟨this.2.1, this.2.2⟩
  | _ => cases here <;> rfl

/-- **`+msg-need-ord-fix-aware` keeps normal shapes normal.** -/
theorem ordNormal_msgFix (fix : NeedOrd) : ∀ (a b : NeedOrd) (c : Cape), ordNormal a = true → ordNormal b = true →
    ordNormal (msgFix a b fix c) = true := by
  induction fix with
  | this => intro a b c ha hb; unfold msgFix; split
            · exact ha
            · exact ordNormal_msgOrd c ha hb
  | none => intro a b c ha hb; unfold msgFix; split
            · exact ha
            · exact ordNormal_msgOrd c ha hb
  | pair fh ft ih1 ih2 =>
    intro a b c ha hb; unfold msgFix
    by_cases e0 : a = b
    · rw [if_pos e0]; exact ha
    rw [if_neg e0]
    dsimp only
    split
    · exact hb
    split
    · exact ha
    exact ordNormal_fixEnd _ (ordNormal_consOrd (ih1 _ _ _ (ordNormal_hed ha) (ordNormal_hed hb))
      (ih2 _ _ _ (ordNormal_tel ha) (ordNormal_tel hb)))
  | both fh ft ih1 ih2 =>
    intro a b c ha hb; unfold msgFix
    by_cases e0 : a = b
    · rw [if_pos e0]; exact ha
    rw [if_neg e0]
    dsimp only
    split
    · exact hb
    split
    · exact ha
    exact ordNormal_fixEnd _ (ordNormal_consOrd (ih1 _ _ _ (ordNormal_hed ha) (ordNormal_hed hb))
      (ih2 _ _ _ (ordNormal_tel ha) (ordNormal_tel hb)))

/-! ## The weight: a bounded measure that `uniN` raises when it changes a shape -/

/-- A register counts `1`, a split `1`. -/
def ordW : NeedOrd → Nat
  | NeedOrd.none => 0
  | NeedOrd.this => 1
  | NeedOrd.both h t => 2 + ordW h + ordW t
  | NeedOrd.pair p q => 1 + ordW p + ordW q

/-- The most weight at depth `d`. -/
def wB : Nat → Nat
  | 0 => 1
  | d + 1 => 2 + 2 * wB d

theorem wB_mono : ∀ {d e : Nat}, d ≤ e → wB d ≤ wB e
  | 0, 0, _ => Nat.le_refl _
  | 0, e + 1, _ => by have := @wB_mono 0 e (Nat.zero_le _); simp only [wB] at this ⊢; omega
  | d + 1, 0, h => absurd h (by omega)
  | d + 1, e + 1, h => by have := @wB_mono d e (by omega); simp only [wB]; omega

theorem ordW_le_wB : ∀ a : NeedOrd, ordW a ≤ wB (ordDepth a)
  | NeedOrd.none => by simp [ordW, wB, ordDepth]
  | NeedOrd.this => by simp [ordW, wB, ordDepth]
  | NeedOrd.both h t => by
    have h1 := ordW_le_wB h; have h2 := ordW_le_wB t
    have := wB_mono (Nat.le_max_left (ordDepth h) (ordDepth t))
    have := wB_mono (Nat.le_max_right (ordDepth h) (ordDepth t))
    simp only [ordW, ordDepth, wB]; omega
  | NeedOrd.pair p q => by
    have h1 := ordW_le_wB p; have h2 := ordW_le_wB q
    have := wB_mono (Nat.le_max_left (ordDepth p) (ordDepth q))
    have := wB_mono (Nat.le_max_right (ordDepth p) (ordDepth q))
    simp only [ordW, ordDepth, wB]; omega

theorem ordW_eq_zero {a : NeedOrd} (h : ordW a = 0) : a = NeedOrd.none := by
  cases a <;> simp_all [ordW] <;> omega

/-- **`uniN` never lowers the weight, and raises it when it changes the shape.** -/
theorem ordW_uniN : ∀ a b : NeedOrd, ordW a ≤ ordW (uniN a b) ∧ (uniN a b ≠ a → ordW a < ordW (uniN a b))
  | NeedOrd.none, b => by
    refine ⟨Nat.zero_le _, fun h => ?_⟩
    simp only [uniN] at h ⊢
    exact Nat.pos_of_ne_zero (fun e => h (ordW_eq_zero e))
  | NeedOrd.this, NeedOrd.none => by simp [uniN]
  | NeedOrd.this, NeedOrd.this => by simp [uniN]
  | NeedOrd.this, NeedOrd.both _ _ => by simp [uniN, ordW]; omega
  | NeedOrd.this, NeedOrd.pair _ _ => by simp [uniN, ordW]; omega
  | NeedOrd.both _ _, NeedOrd.none => by simp [uniN]
  | NeedOrd.both _ _, NeedOrd.this => by simp [uniN]
  | NeedOrd.both h t, NeedOrd.both h' t' => by
    have e1 := ordW_uniN h h'; have e2 := ordW_uniN t t'
    simp only [uniN, ordW, ne_eq, NeedOrd.both.injEq]
    refine ⟨by omega, fun hne => ?_⟩
    by_cases h1 : uniN h h' = h
    · have := e2.2 (fun h2 => hne ⟨h1, h2⟩); omega
    · have := e1.2 h1; omega
  | NeedOrd.both h t, NeedOrd.pair p q => by
    have e1 := ordW_uniN h p; have e2 := ordW_uniN t q
    simp only [uniN, ordW, ne_eq, NeedOrd.both.injEq]
    refine ⟨by omega, fun hne => ?_⟩
    by_cases h1 : uniN h p = h
    · have := e2.2 (fun h2 => hne ⟨h1, h2⟩); omega
    · have := e1.2 h1; omega
  | NeedOrd.pair _ _, NeedOrd.none => by simp [uniN]
  | NeedOrd.pair p q, NeedOrd.this => by simp [uniN, ordW]
  | NeedOrd.pair p q, NeedOrd.both h t => by
    have e1 := ordW_uniN p h; have e2 := ordW_uniN q t
    simp only [uniN, ordW, ne_eq, reduceCtorEq, not_false_eq_true, true_implies]
    omega
  | NeedOrd.pair p q, NeedOrd.pair p' q' => by
    have e1 := ordW_uniN p p'; have e2 := ordW_uniN q q'
    simp only [uniN, ordW, ne_eq, NeedOrd.pair.injEq]
    refine ⟨by omega, fun hne => ?_⟩
    by_cases h1 : uniN p p' = p
    · have := e2.2 (fun h2 => hne ⟨h1, h2⟩); omega
    · have := e1.2 h1; omega

/-! ## The order whose join is `uniN` -/

/-- `a ≤ b` for the join `uniN`. -/
def oLe (a b : NeedOrd) : Prop := uniN a b = b

theorem oLe_refl (a : NeedOrd) : oLe a a := uniN_idem a

theorem oLe_trans {a b c : NeedOrd} (h1 : oLe a b) (h2 : oLe b c) : oLe a c := by
  unfold oLe at *; rw [← h2, ← uniN_assoc, h1]

theorem oLe_uniN_left (a x : NeedOrd) : oLe a (uniN a x) := by
  unfold oLe; rw [← uniN_assoc, uniN_idem]

theorem oLe_uniN_right (a x : NeedOrd) : oLe a (uniN x a) := by
  rw [uniN_comm]; exact oLe_uniN_left a x

theorem ordW_oLe {a b : NeedOrd} (h : oLe a b) : ordW a ≤ ordW b ∧ (a ≠ b → ordW a < ordW b) := by
  have := ordW_uniN a b
  unfold oLe at h; rw [h] at this
  exact ⟨this.1, fun hne => this.2 (Ne.symm hne)⟩

end Comp
end SkaModel
end Formalization
