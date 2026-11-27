import lemmas.Ska.ShapeCol

/-! # The algebra of `+msg-need-ord` (`msgOrd`), for the loop of `+compile-scc-in` (Gaps 21)

Facts about `msgOrd` of `Ska/ShapeCol.lean` that the sweep loop of `+compile-scc-in` rests on.

* `msgOrd_self` (idempotent, `+msg-need-ord`'s first test), `msgOrd_comm` (commutative), and
  `msgOrd_abs`: `msg a (msg a b) = msg a b`, the hypothesis `msgAbs` of `Hyp` in
  `Ska/SccLoop.lean`, for every cape.  With `msgOrd_comm` it also gives
  `msg (msg a b) b = msg a b` (`msgOrd_abs'`).
* `msgOrd_not_assoc`: `msgOrd` is not associative (a witness without the cap, and one where
  only `split-max` breaks it).
* `msgOrd_cycle`: iterating `e ↦ msg n e` (what the loop does to an entry, `need-pessimized =
  (msg-need-ord need-new prev cape)`) can return to its start: under the cape
  `[[| |] [| |]]`, from `this` the needs `[%both this this]`, `[%both [%both this this]
  [%both this this]]`, `this` give the entries `[%both this this]`, the big split, `this`.  The
  big split has seven registers: the `%both` case of `+msg-need-ord` keeps it (no cap there),
  and the case of one side `%this` turns it into `this` (`msgCap`).  So no order on shapes makes
  every step of `+msg-need-ord` go up, and the termination of the loop needs a property of the
  member compile (README Gaps 21.8).

The proofs go through the uncut register count `regsU` (`ordRegs_min`: `+need-ord-regs` is it,
cut above `max`), `msgNone_idem`, `msgOrd_none_self` (`msg d (msg none d) = msg none d`) and
`msgOrd_eq_none` (an atom cape: only `none` and `none` give `none`). -/

namespace Formalization.SkaModel.Comp

open Nock Compiler

/-! ## Registers -/

/-- The registers of a shape, uncut. -/
def regsU : NeedOrd → Nat
  | NeedOrd.none => 0
  | NeedOrd.this => 1
  | NeedOrd.both h t => regsU h + regsU t + 1
  | NeedOrd.pair p q => regsU p + regsU q

theorem ordRegs_min (m : Nat) (n : NeedOrd) (acc : Nat) :
    min (ordRegs m n acc) (m + 1) = min (acc + regsU n) (m + 1) := by
  induction n generalizing acc with
  | none => unfold ordRegs; split <;> simp [regsU]
  | this => unfold ordRegs; split <;> simp [regsU] <;> omega
  | both h t ih1 ih2 =>
    unfold ordRegs; split
    · simp [regsU]; omega
    · have := ih1 (acc + 1); have := ih2 (ordRegs m h (acc + 1)); simp only [regsU]; omega
  | pair p q ih1 ih2 =>
    unfold ordRegs; split
    · simp [regsU]; omega
    · have := ih1 acc; have := ih2 (ordRegs m p acc); simp only [regsU]; omega

theorem msgCap_eq (r : NeedOrd) : msgCap r = if regsU r > splitMax then NeedOrd.this else r := by
  have := ordRegs_min splitMax r 0
  unfold msgCap
  by_cases h : regsU r > splitMax
  · have : ordRegs splitMax r 0 > splitMax := by simp [splitMax] at *; omega
    simp [*]
  · have : ¬ ordRegs splitMax r 0 > splitMax := by simp [splitMax] at *; omega
    simp [*]

/-! ## The cases of `msgOrd` -/

def isLeaf : NeedOrd → Bool
  | NeedOrd.this => true
  | NeedOrd.none => true
  | _ => false

def isB : NeedOrd → Bool
  | NeedOrd.both _ _ => true
  | _ => false

/-- A `%both` or a `+cons-need`. -/
def mkB (b : Bool) (x y : NeedOrd) : NeedOrd := if b then NeedOrd.both x y else consOrd x y

theorem msgOrd_self (a : NeedOrd) (c : Cape) : msgOrd a a c = a := by
  unfold msgOrd; simp

theorem msgOrd_leaf (a b : NeedOrd) (c : Cape) (ha : isLeaf a) (hb : isLeaf b) (h : a ≠ b) :
    msgOrd a b c = NeedOrd.this := by
  cases a <;> cases b <;> simp_all [isLeaf, msgOrd]

theorem msgOrd_left (s d : NeedOrd) (c : Cape) (hs : isLeaf s) (hd : isLeaf d = false) :
    msgOrd s d c = msgOne s d c := by
  cases s <;> cases d <;> simp_all [isLeaf, msgOrd]

theorem msgOrd_right (s d : NeedOrd) (c : Cape) (hs : isLeaf s) (hd : isLeaf d = false) :
    msgOrd d s c = msgOne s d c := by
  cases s <;> cases d <;> simp_all [isLeaf, msgOrd]

theorem msgOrd_inner (a b : NeedOrd) (c : Cape) (ha : isLeaf a = false) (hb : isLeaf b = false)
    (h : a ≠ b) :
    msgOrd a b c = mkB (isB a || isB b) (msgOrd (ordHed a) (ordHed b) (capeHed c))
      (msgOrd (ordTel a) (ordTel b) (capeTel c)) := by
  cases a <;> cases b <;> simp_all [isLeaf, isB, msgOrd, mkB, ordHed, ordTel]

theorem msgOne_cell (s d : NeedOrd) (lh lt : Cape) (hd : isLeaf d = false) :
    msgOne s d (Cape.cell lh lt) =
      msgCap (mkB (s == NeedOrd.this || isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt)) := by
  cases d <;> simp_all [isLeaf, isB, msgOne, mkB] <;> cases s <;> simp

theorem msgOne_atom (s d : NeedOrd) (c : Cape) (hc : ∀ x y, c ≠ Cape.cell x y) :
    msgOne s d c = NeedOrd.this := by
  cases c <;> simp_all [msgOne]

theorem msgNone_cell (d : NeedOrd) (lh lt : Cape) (hd : isLeaf d = false) :
    msgNone d (Cape.cell lh lt) =
      msgCap (mkB (isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt)) := by
  cases d <;> simp_all [isLeaf, isB, msgNone, mkB, ordHed, ordTel]

theorem msgOne_yes (s d : NeedOrd) : msgOne s d Cape.yes = NeedOrd.this := rfl
theorem msgOne_no (s d : NeedOrd) : msgOne s d Cape.no = NeedOrd.this := rfl
theorem msgNone_yes (d : NeedOrd) (hd : isLeaf d = false) : msgNone d Cape.yes = NeedOrd.this := by
  cases d <;> simp_all [isLeaf, msgNone]
theorem msgNone_no (d : NeedOrd) (hd : isLeaf d = false) : msgNone d Cape.no = NeedOrd.this := by
  cases d <;> simp_all [isLeaf, msgNone]

theorem msgNone_atom (d : NeedOrd) (c : Cape) (hd : isLeaf d = false)
    (hc : ∀ x y, c ≠ Cape.cell x y) : msgNone d c = NeedOrd.this := by
  cases d <;> cases c <;> simp_all [isLeaf, msgNone]

/-! ## `msg none` -/

theorem regsU_mkB (b : Bool) (x y : NeedOrd) : regsU (mkB b x y) ≤ regsU (NeedOrd.both x y) := by
  cases b <;> simp [mkB, consOrd, regsU] <;> split <;> simp [regsU] <;> omega

theorem mkB_ne_none_of_ne (b : Bool) (x y : NeedOrd) (h : mkB b x y ≠ NeedOrd.none) :
    isLeaf (mkB b x y) = false := by
  cases b
  · simp only [mkB, consOrd] at h ⊢
    by_cases hx : x = NeedOrd.none ∧ y = NeedOrd.none
    · simp [hx] at h
    · simp [hx, isLeaf]
  · rfl

theorem msgCap_this_or (r : NeedOrd) : msgCap r = NeedOrd.this ∨ (msgCap r = r ∧ regsU r ≤ splitMax) := by
  rw [msgCap_eq]; split <;> simp_all <;> omega

/-- `msg none` of a `mkB` of fixed points, under the cap, is that `mkB`. -/
theorem msgNone_mkB (b : Bool) (x y : NeedOrd) (lh lt : Cape) (hx : msgNone x lh = x)
    (hy : msgNone y lt = y) (hr : regsU (mkB b x y) ≤ splitMax) :
    msgNone (mkB b x y) (Cape.cell lh lt) = mkB b x y := by
  cases b
  · simp only [mkB, consOrd, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    by_cases h : x = NeedOrd.none ∧ y = NeedOrd.none
    · rw [if_pos h]; simp [msgNone]
    · rw [if_neg h] at hr ⊢
      rw [msgNone_cell (NeedOrd.pair x y) lh lt rfl]
      simp only [mkB, isB, ordHed, ordTel, hx, hy, consOrd, if_neg h, Bool.false_eq_true,
        if_false]
      rw [msgCap_eq]; simp_all
  · simp only [mkB, ↓reduceIte] at hr ⊢
    rw [msgNone_cell (NeedOrd.both x y) lh lt rfl]
    simp only [mkB, isB, ordHed, ordTel, hx, hy, if_true]
    rw [msgCap_eq]; simp_all

theorem msgNone_idem (d : NeedOrd) (c : Cape) : msgNone (msgNone d c) c = msgNone d c := by
  induction d generalizing c with
  | none => simp [msgNone]
  | this => simp [msgNone]
  | pair p q ih1 ih2 =>
    cases c with
    | cell lh lt =>
      rw [msgNone_cell (NeedOrd.pair p q) lh lt rfl]
      rcases msgCap_this_or (mkB (isB (NeedOrd.pair p q)) (msgNone (ordHed (NeedOrd.pair p q)) lh)
        (msgNone (ordTel (NeedOrd.pair p q)) lt)) with h | ⟨h, hr⟩
      · rw [h]; simp [msgNone]
      · rw [h]; exact msgNone_mkB _ _ _ _ _ (ih1 lh) (ih2 lt) hr
    | _ => simp [msgNone]
  | both p q ih1 ih2 =>
    cases c with
    | cell lh lt =>
      rw [msgNone_cell (NeedOrd.both p q) lh lt rfl]
      rcases msgCap_this_or (mkB (isB (NeedOrd.both p q)) (msgNone (ordHed (NeedOrd.both p q)) lh)
        (msgNone (ordTel (NeedOrd.both p q)) lt)) with h | ⟨h, hr⟩
      · rw [h]; simp [msgNone]
      · rw [h]; exact msgNone_mkB _ _ _ _ _ (ih1 lh) (ih2 lt) hr
    | _ => simp [msgNone]

/-! ## Helpers on shapes -/

theorem ord_induct {Q : NeedOrd → Prop} (hl : ∀ a, isLeaf a = true → Q a)
    (hi : ∀ a, isLeaf a = false → Q (ordHed a) → Q (ordTel a) → Q a) : ∀ a, Q a := by
  intro a
  induction a with
  | pair p q ih1 ih2 => exact hi _ rfl ih1 ih2
  | both p q ih1 ih2 => exact hi _ rfl ih1 ih2
  | this => exact hl _ rfl
  | none => exact hl _ rfl

theorem leaf_cases {a : NeedOrd} (h : isLeaf a = true) : a = NeedOrd.this ∨ a = NeedOrd.none := by
  cases a <;> simp_all [isLeaf]

theorem pair_of {a : NeedOrd} (h : isLeaf a = false) (hb : isB a = false) :
    a = NeedOrd.pair (ordHed a) (ordTel a) := by
  cases a <;> simp_all [isLeaf, isB, ordHed, ordTel]

theorem mkB_none {b : Bool} {x y : NeedOrd} (h : mkB b x y = NeedOrd.none) :
    b = false ∧ x = NeedOrd.none ∧ y = NeedOrd.none := by
  cases b <;> simp only [mkB, consOrd, Bool.false_eq_true, ↓reduceIte] at h
  · by_cases hx : x = NeedOrd.none ∧ y = NeedOrd.none
    · exact ⟨rfl, hx⟩
    · rw [if_neg hx] at h; cases h
  · cases h

theorem mkB_parts {b : Bool} {x y : NeedOrd} (h : isLeaf (mkB b x y) = false) :
    ordHed (mkB b x y) = x ∧ ordTel (mkB b x y) = y ∧ isB (mkB b x y) = b := by
  cases b <;> simp only [mkB, consOrd, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · by_cases hx : x = NeedOrd.none ∧ y = NeedOrd.none
    · rw [if_pos hx] at h; cases h
    · rw [if_neg hx]; simp [ordHed, ordTel, isB]
  · simp [ordHed, ordTel, isB]

theorem mkB_leaf {b : Bool} {x y : NeedOrd} (h : isLeaf (mkB b x y) = true) :
    mkB b x y = NeedOrd.none := by
  rcases leaf_cases h with h' | h'
  · cases b <;> simp only [mkB, consOrd, Bool.false_eq_true, ↓reduceIte] at h'
    · by_cases hx : x = NeedOrd.none ∧ y = NeedOrd.none
      · rw [if_pos hx] at h'; cases h'
      · rw [if_neg hx] at h'; cases h'
    · cases h'
  · exact h'

theorem msgCap_none : msgCap NeedOrd.none = NeedOrd.none := by
  rw [msgCap_eq]; simp [regsU, splitMax]

theorem msgCap_eq_none {x : NeedOrd} (h : msgCap x = NeedOrd.none) : x = NeedOrd.none := by
  rw [msgCap_eq] at h; split at h
  · cases h
  · exact h

theorem msgCap_mkB_this {b : Bool} {x y : NeedOrd} (h : msgCap (mkB b x y) = NeedOrd.this) :
    msgCap (NeedOrd.both x y) = NeedOrd.this := by
  have hle := regsU_mkB b x y
  rw [msgCap_eq] at h ⊢
  split at h
  · next hg => rw [if_pos (by omega)]
  · cases b <;> simp only [mkB, consOrd, Bool.false_eq_true, ↓reduceIte] at h
    · by_cases hx : x = NeedOrd.none ∧ y = NeedOrd.none
      · rw [if_pos hx] at h; cases h
      · rw [if_neg hx] at h; cases h
    · cases h

theorem msgOne_none (d : NeedOrd) (c : Cape) (hd : isLeaf d = false) :
    msgOne NeedOrd.none d c = msgNone d c := by
  cases c with
  | cell lh lt => rw [msgOne_cell _ _ _ _ hd, msgNone_cell _ _ _ hd]; rfl
  | yes => rw [msgOne_yes, msgNone_yes _ hd]
  | no => rw [msgOne_no, msgNone_no _ hd]

/-! ## `none` from `msgOrd` -/

/-- Under an atom cape only `none` and `none` give `none`. -/
theorem msgOrd_eq_none_atom (c : Cape) (hc : ∀ x y, c ≠ Cape.cell x y) :
    ∀ a b, msgOrd a b c = NeedOrd.none → a = NeedOrd.none ∧ b = NeedOrd.none := by
  have hh : capeHed c = c := by cases c <;> simp_all [capeHed]
  have ht : capeTel c = c := by cases c <;> simp_all [capeTel]
  refine ord_induct (Q := fun a => ∀ b, msgOrd a b c = NeedOrd.none →
    a = NeedOrd.none ∧ b = NeedOrd.none) ?_ ?_
  · intro a ha b h
    by_cases hab : a = b
    · subst hab; rw [msgOrd_self] at h; exact ⟨h, h⟩
    cases hb : isLeaf b
    · rw [msgOrd_left _ _ _ ha hb, msgOne_atom _ _ _ hc] at h; cases h
    · rw [msgOrd_leaf _ _ _ ha hb hab] at h; cases h
  · intro a ha ih1 ih2 b h
    by_cases hab : a = b
    · subst hab; rw [msgOrd_self] at h; exact ⟨h, h⟩
    cases hb : isLeaf b
    · rw [msgOrd_inner _ _ _ ha hb hab, hh, ht] at h
      obtain ⟨hf, hx, hy⟩ := mkB_none h
      obtain ⟨h1, h2⟩ := ih1 _ hx
      obtain ⟨h3, h4⟩ := ih2 _ hy
      simp only [Bool.or_eq_false_iff] at hf
      exact absurd (by rw [pair_of ha hf.1, pair_of hb hf.2, h1, h2, h3, h4]) hab
    · rw [msgOrd_right _ _ _ hb ha, msgOne_atom _ _ _ hc] at h; cases h

theorem atom_pair_eq {a b : NeedOrd} {c : Cape} (hc : ∀ x y, c ≠ Cape.cell x y)
    (ha : isLeaf a = false) (hb : isLeaf b = false) (hf : isB a = false ∧ isB b = false)
    (hx : msgOrd (ordHed a) (ordHed b) (capeHed c) = NeedOrd.none)
    (hy : msgOrd (ordTel a) (ordTel b) (capeTel c) = NeedOrd.none) : a = b := by
  have hh : capeHed c = c := by cases c <;> simp_all [capeHed]
  have ht : capeTel c = c := by cases c <;> simp_all [capeTel]
  rw [hh] at hx; rw [ht] at hy
  obtain ⟨h1, h2⟩ := msgOrd_eq_none_atom c hc _ _ hx
  obtain ⟨h3, h4⟩ := msgOrd_eq_none_atom c hc _ _ hy
  rw [pair_of ha hf.1, pair_of hb hf.2, h1, h2, h3, h4]

theorem msgOrd_eq_none : ∀ a b c, msgOrd a b c = NeedOrd.none → msgNone a c = NeedOrd.none := by
  refine ord_induct (Q := fun a => ∀ b c, msgOrd a b c = NeedOrd.none →
    msgNone a c = NeedOrd.none) ?_ ?_
  · intro a ha b c h
    by_cases hab : a = b
    · subst hab; rw [msgOrd_self] at h; subst h; rfl
    rcases leaf_cases ha with rfl | rfl
    · exfalso
      cases hb : isLeaf b
      · rw [msgOrd_left _ _ _ rfl hb] at h
        cases c with
        | cell lh lt =>
          rw [msgOne_cell _ _ _ _ hb] at h
          have := mkB_none (msgCap_eq_none h); simp at this
        | _ => simp [msgOne] at h
      · rw [msgOrd_leaf _ _ _ rfl hb hab] at h; cases h
    · rfl
  · intro a ha ih1 ih2 b c h
    by_cases hab : a = b
    · subst hab; rw [msgOrd_self] at h; subst h; rfl
    cases hb : isLeaf b
    · rw [msgOrd_inner _ _ _ ha hb hab] at h
      obtain ⟨hf, hx, hy⟩ := mkB_none h
      simp only [Bool.or_eq_false_iff] at hf
      cases c with
      | cell lh lt =>
        simp only [capeHed, capeTel] at hx hy
        rw [msgNone_cell _ _ _ ha, ih1 _ _ hx, ih2 _ _ hy, hf.1]
        simp [mkB, consOrd, msgCap_none]
      | _ => exact absurd (atom_pair_eq (by simp) ha hb hf hx hy) hab
    · rw [msgOrd_right _ _ _ hb ha] at h
      cases c with
      | cell lh lt =>
        rw [msgOne_cell _ _ _ _ ha] at h
        obtain ⟨hf, hx, hy⟩ := mkB_none (msgCap_eq_none h)
        simp only [Bool.or_eq_false_iff] at hf
        rw [msgNone_cell _ _ _ ha, hx, hy, hf.2]
        simp [mkB, consOrd, msgCap_none]
      | _ => simp [msgOne] at h

/-! ## `msg d (msg none d) = msg none d` -/

theorem msgOrd_none_self : ∀ d c, msgOrd d (msgNone d c) c = msgNone d c := by
  refine ord_induct (Q := fun d => ∀ c, msgOrd d (msgNone d c) c = msgNone d c) ?_ ?_
  · intro d hd c
    rcases leaf_cases hd with rfl | rfl <;> simp [msgNone, msgOrd_self]
  · intro d hd ih1 ih2 c
    cases c with
    | cell lh lt =>
      rw [msgNone_cell _ _ _ hd]
      rcases msgCap_this_or (mkB (isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt))
        with h | ⟨h, _⟩
      · rw [h, msgOrd_right _ _ _ rfl hd, msgOne_cell _ _ _ _ hd]
        simpa [mkB] using msgCap_mkB_this h
      · rw [h]
        cases hR : isLeaf (mkB (isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt))
        · by_cases hdR : d = mkB (isB d) (msgNone (ordHed d) lh) (msgNone (ordTel d) lt)
          · rw [← hdR, msgOrd_self]
          rw [msgOrd_inner _ _ _ hd hR hdR]
          obtain ⟨e1, e2, e3⟩ := mkB_parts hR
          rw [e1, e2, e3]; simp only [capeHed, capeTel, Bool.or_self]
          rw [ih1, ih2]
        · rw [mkB_leaf hR, msgOrd_right _ _ _ rfl hd, msgOne_none _ _ hd,
            msgNone_cell _ _ _ hd, ← mkB_leaf hR, h]
    | _ =>
      simp only [msgNone_yes _ hd, msgNone_no _ hd]
      rw [msgOrd_right NeedOrd.this d _ rfl hd]; simp only [msgOne_yes, msgOne_no]

/-! ## `msgAbs` and commutativity -/

theorem msgOrd_this_of (a : NeedOrd) (c : Cape) (ha : isLeaf a = true) :
    msgOrd a NeedOrd.this c = NeedOrd.this := by
  rcases leaf_cases ha with rfl | rfl
  · exact msgOrd_self _ _
  · exact msgOrd_leaf _ _ _ rfl rfl (by simp)

/-- **`msgAbs`**: `msg a (msg a b) = msg a b`, for every cape. -/
theorem msgOrd_abs : ∀ a b c, msgOrd a (msgOrd a b c) c = msgOrd a b c := by
  refine ord_induct (Q := fun a => ∀ b c, msgOrd a (msgOrd a b c) c = msgOrd a b c) ?_ ?_
  · intro a ha b c
    by_cases hab : a = b
    · subst hab; rw [msgOrd_self, msgOrd_self]
    cases hb : isLeaf b
    · rw [msgOrd_left _ _ _ ha hb]
      cases c with
      | cell lh lt =>
        rw [msgOne_cell _ _ _ _ hb]
        rcases msgCap_this_or (mkB (a == NeedOrd.this || isB b) (msgNone (ordHed b) lh)
          (msgNone (ordTel b) lt)) with h | ⟨h, hr⟩
        · rw [h, msgOrd_this_of _ _ ha]
        · rw [h]
          cases hR : isLeaf (mkB (a == NeedOrd.this || isB b) (msgNone (ordHed b) lh)
              (msgNone (ordTel b) lt))
          · rw [msgOrd_left _ _ _ ha hR, msgOne_cell _ _ _ _ hR]
            obtain ⟨e1, e2, e3⟩ := mkB_parts hR
            rw [e1, e2, e3, msgNone_idem, msgNone_idem]
            have : (a == NeedOrd.this || (a == NeedOrd.this || isB b)) =
              (a == NeedOrd.this || isB b) := by cases (a == NeedOrd.this) <;> simp
            rw [this, h]
          · have hn := mkB_leaf hR
            obtain ⟨hf, _, _⟩ := mkB_none hn
            rw [hn]
            rcases leaf_cases ha with rfl | rfl
            · simp at hf
            · exact msgOrd_self _ _
      | _ => simp only [msgOne_yes, msgOne_no]; rw [msgOrd_this_of _ _ ha]
    · rw [msgOrd_leaf _ _ _ ha hb hab, msgOrd_this_of _ _ ha]
  · intro a ha ih1 ih2 b c
    by_cases hab : a = b
    · subst hab; rw [msgOrd_self, msgOrd_self]
    cases hb : isLeaf b
    · rw [msgOrd_inner _ _ _ ha hb hab]
      cases hR : isLeaf (mkB (isB a || isB b) (msgOrd (ordHed a) (ordHed b) (capeHed c))
          (msgOrd (ordTel a) (ordTel b) (capeTel c)))
      · by_cases haR : a = mkB (isB a || isB b) (msgOrd (ordHed a) (ordHed b) (capeHed c))
            (msgOrd (ordTel a) (ordTel b) (capeTel c))
        · rw [← haR, msgOrd_self]
        rw [msgOrd_inner _ _ _ ha hR haR]
        obtain ⟨e1, e2, e3⟩ := mkB_parts hR
        rw [e1, e2, e3, ih1, ih2]
        cases (isB a) <;> simp
      · have hn := mkB_leaf hR
        obtain ⟨hf, hx, hy⟩ := mkB_none hn
        simp only [Bool.or_eq_false_iff] at hf
        rw [hn, msgOrd_right _ _ _ rfl ha, msgOne_none _ _ ha]
        cases c with
        | cell lh lt =>
          simp only [capeHed, capeTel] at hx hy
          rw [msgNone_cell _ _ _ ha, msgOrd_eq_none _ _ _ hx, msgOrd_eq_none _ _ _ hy, hf.1]
          simp [mkB, consOrd, msgCap_none]
        | _ => exact absurd (atom_pair_eq (by simp) ha hb hf hx hy) hab
    · rw [msgOrd_right _ _ _ hb ha]
      cases c with
      | cell lh lt =>
        rw [msgOne_cell _ _ _ _ ha]
        rcases msgCap_this_or (mkB (b == NeedOrd.this || isB a) (msgNone (ordHed a) lh)
          (msgNone (ordTel a) lt)) with h | ⟨h, hr⟩
        · rw [h, msgOrd_right _ _ _ rfl ha, msgOne_cell _ _ _ _ ha]
          simpa [mkB] using msgCap_mkB_this h
        · rw [h]
          cases hR : isLeaf (mkB (b == NeedOrd.this || isB a) (msgNone (ordHed a) lh)
              (msgNone (ordTel a) lt))
          · by_cases haR : a = mkB (b == NeedOrd.this || isB a) (msgNone (ordHed a) lh)
                (msgNone (ordTel a) lt)
            · rw [← haR, msgOrd_self]
            rw [msgOrd_inner _ _ _ ha hR haR]
            obtain ⟨e1, e2, e3⟩ := mkB_parts hR
            rw [e1, e2, e3]; simp only [capeHed, capeTel]
            rw [msgOrd_none_self, msgOrd_none_self]
            have : (isB a || (b == NeedOrd.this || isB a)) = (b == NeedOrd.this || isB a) := by
              cases (isB a) <;> simp
            rw [this]
          · have hn := mkB_leaf hR
            obtain ⟨hf, hx, hy⟩ := mkB_none hn
            simp only [Bool.or_eq_false_iff] at hf
            rw [hn, msgOrd_right _ _ _ rfl ha, msgOne_none _ _ ha, msgNone_cell _ _ _ ha, hx, hy,
              hf.2]
            simp [mkB, consOrd, msgCap_none]
      | _ =>
        simp only [msgOne_yes, msgOne_no]
        rw [msgOrd_right NeedOrd.this a _ rfl ha]; simp only [msgOne_yes, msgOne_no]

theorem msgOrd_comm : ∀ a b c, msgOrd a b c = msgOrd b a c := by
  refine ord_induct (Q := fun a => ∀ b c, msgOrd a b c = msgOrd b a c) ?_ ?_
  · intro a ha b c
    by_cases hab : a = b
    · rw [hab]
    cases hb : isLeaf b
    · rw [msgOrd_left _ _ _ ha hb, msgOrd_right _ _ _ ha hb]
    · rw [msgOrd_leaf _ _ _ ha hb hab, msgOrd_leaf _ _ _ hb ha (Ne.symm hab)]
  · intro a ha ih1 ih2 b c
    by_cases hab : a = b
    · rw [hab]
    cases hb : isLeaf b
    · rw [msgOrd_inner _ _ _ ha hb hab, msgOrd_inner _ _ _ hb ha (Ne.symm hab), ih1, ih2,
        Bool.or_comm]
    · rw [msgOrd_right _ _ _ hb ha, msgOrd_left _ _ _ hb ha]

/-- `msg (msg a b) b = msg a b`. -/
theorem msgOrd_abs' (a b : NeedOrd) (c : Cape) : msgOrd (msgOrd a b c) b c = msgOrd a b c := by
  rw [msgOrd_comm _ b, msgOrd_comm a b, msgOrd_abs]

/-! ## Witnesses: no associativity, a cycle

Both checked on the real `+msg-need-ord` too (README Gaps 21.8). -/

/-- The cape `[[| |] [| |]]`. -/
def cape22 : Cape := Cape.cell (Cape.cell Cape.no Cape.no) (Cape.cell Cape.no Cape.no)

def bTT : NeedOrd := NeedOrd.both NeedOrd.this NeedOrd.this

/-- Seven registers: over `split-max`. -/
def bBig : NeedOrd := NeedOrd.both bTT bTT

/-- `msgOrd` is not associative, and only `split-max` breaks it here: `(a b) d` keeps a split
of seven registers through the `%both` case, `a (b d)` meets the cap in the case of one side
`%this`.  (Without the cap no triple of shapes free of `[none none]` up to two inner nodes, all
of them, and none of 1.5 million random ones up to three, breaks associativity.) -/
theorem msgOrd_not_assoc :
    msgOrd (msgOrd NeedOrd.this (NeedOrd.both NeedOrd.none
        (NeedOrd.both (NeedOrd.pair NeedOrd.none NeedOrd.this) NeedOrd.this)) cape22)
      (NeedOrd.both bTT NeedOrd.this) cape22 = bBig ∧
    msgOrd NeedOrd.this (msgOrd (NeedOrd.both NeedOrd.none
        (NeedOrd.both (NeedOrd.pair NeedOrd.none NeedOrd.this) NeedOrd.this))
      (NeedOrd.both bTT NeedOrd.this) cape22) cape22 = NeedOrd.this := by decide

/-- **A cycle of `e ↦ msg n e`**: from `this`, the needs `bTT`, `bBig`, `this` give the
entries `bTT`, `bBig`, `this`, each step a change.  So no order on shapes makes every step of
`+msg-need-ord` go up (it would need `this < bTT < bBig < this`). -/
theorem msgOrd_cycle :
    msgOrd bTT NeedOrd.this cape22 = bTT ∧ msgOrd bBig bTT cape22 = bBig ∧
    msgOrd NeedOrd.this bBig cape22 = NeedOrd.this := by decide

/-- The "reads more" order is not kept (the `%deep` SCC of `SccLoopData.lean`). -/
theorem msgOrd_deep :
    msgOrd (NeedOrd.pair NeedOrd.this NeedOrd.this) (NeedOrd.pair NeedOrd.this bTT) Cape.no =
      NeedOrd.pair NeedOrd.this NeedOrd.this := by decide

end Formalization.SkaModel.Comp
