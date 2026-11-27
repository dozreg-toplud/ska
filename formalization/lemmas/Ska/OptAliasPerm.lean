import lemmas.Ska.OptAliasModel

/-!
# The order of `pre` in `+alias`

The Hoon walks the predecessors of a block in the order of `~(tap in ...)` of
a set, the model (`Ska/OptAliasModel.lean`) in the order of the list
`g.rev o`.  Both lists hold the same labels without duplicates, so one is a
permutation of the other.  The results of the phases that read `pre` are not
equal under a permutation: `joinReg a b` keeps the order of `a.hedOf`, so
`joinReg a b` and `joinReg b a` differ in the order of `hedOf` (witness
`joinReg_not_comm` below), and `joinRegE` keeps an equal value as it is,
which `joinReg` changes in `isLoob` where `hasImm` is a loobean.  They are
equal up to **`InfoEq`**: the units and `isCell` equal, `hedOf` and `telOf`
with the same members, and `isLoob ∨ loobImm` equal.  This is exactly what
the link's `InfoRel` (`Compiler/OptLinkAlJReg.lean`) fixes of an `info-reg`
noun, so `InfoRel N x` and `InfoEq x y` give `InfoRel N y`.

* `loobC_joinReg`: the class `isLoob ∨ loobImm` of a join is the meet of the
  classes.  With it `joinReg` is congruent (`joinReg_congr`), commutative
  (`joinReg_comm`), associative (`joinReg_assoc`) and idempotent
  (`joinReg_idem`) up to `InfoEq`, and `joinRegE` is `joinReg`
  (`joinRegE_eq`).  The same for the pointwise maps (`AInfoEq`:
  `joinInfoA_congr`, `joinInfoA_comm`, `joinInfoA_assoc`) and the
  immediates (`ImmsEq`, the same members at each noun: `joinImmsA_*`).
* `foldl_perm_rel`, `fold1_perm`: a fold of a commutative and associative
  operation, up to an equivalence, over two permutations.
* **`aliasStart_perm`**, **`aliasStartImms_perm`**, **`aliasEdges_perm`**,
  **`aliasPars_perm`**, **`paramInfo_perm`**: the phases under a permutation of
  `pre` (and of the edges), related by `OptR AInfoEq`, `OptR ImmsEq`,
  `OptR List.Perm` (both `none`, or both `some` and related).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-! ## Relations on options -/

/-- Both `none`, or both `some` and related. -/
def OptR {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

@[simp] theorem optR_none_none {α β : Type} (R : α → β → Prop) : OptR R none none := trivial
@[simp] theorem optR_some_some {α β : Type} (R : α → β → Prop) (a : α) (b : β) :
    OptR R (some a) (some b) ↔ R a b := Iff.rfl
@[simp] theorem optR_none_some {α β : Type} (R : α → β → Prop) (b : β) : OptR R none (some b) ↔ False :=
  Iff.rfl
@[simp] theorem optR_some_none {α β : Type} (R : α → β → Prop) (a : α) : OptR R (some a) none ↔ False :=
  Iff.rfl

theorem optR_refl {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) : ∀ x : Option α, OptR R x x
  | none => trivial
  | some a => hR a

theorem optR_symm {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {x y : Option α}, OptR R x y → OptR R y x
  | none, none, _ => trivial
  | some _, some _, h => hR _ _ h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem optR_trans {α : Type} {R : α → α → Prop} (hR : ∀ a b c, R a b → R b c → R a c) :
    ∀ {x y z : Option α}, OptR R x y → OptR R y z → OptR R x z
  | none, none, none, _, _ => trivial
  | some _, some _, some _, h1, h2 => hR _ _ _ h1 h2
  | none, some _, _, h, _ => h.elim
  | some _, none, _, h, _ => h.elim
  | none, none, some _, _, h => h.elim
  | some _, some _, none, _, h => h.elim

theorem optR_equiv {α : Type} {R : α → α → Prop} (hE : Equivalence R) : Equivalence (OptR R) :=
  ⟨optR_refl hE.refl, optR_symm (R := R) (fun _ _ => hE.symm), optR_trans (R := R) (fun _ _ _ => hE.trans)⟩

/-! ## The meet of two units -/

/-- `?:(=(a b) a ~)`. -/
def meetO {α : Type} [DecidableEq α] (x y : Option α) : Option α := if x = y then x else none

theorem meetO_comm {α : Type} [DecidableEq α] (x y : Option α) : meetO x y = meetO y x := by
  unfold meetO
  by_cases h : x = y
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem meetO_idem {α : Type} [DecidableEq α] (x : Option α) : meetO x x = x := by
  unfold meetO; simp

theorem meetO_assoc {α : Type} [DecidableEq α] (x y z : Option α) :
    meetO (meetO x y) z = meetO x (meetO y z) := by
  unfold meetO
  by_cases h1 : x = y
  · subst h1
    by_cases h2 : x = z
    · subst h2; simp
    · simp [h2]; exact fun h => h.symm
  · by_cases h2 : y = z
    · subst h2; simp [h1]
    · rw [if_neg h1, if_neg h2]
      by_cases h3 : x = none
      · subst h3; simp
      · simp [h3]

/-! ## Facts up to what the link reads -/

/-- The class of `isLoob` that `InfoRel` fixes: `isLoob ∨ ?=([~ ?] has-imm)`. -/
def InfoReg.loobC (a : InfoReg) : Bool := a.isLoob || a.loobImm

/-- **Two facts the link cannot tell apart**: the units and `isCell` equal,
`hedOf` and `telOf` with the same members, `isLoob ∨ loobImm` equal. -/
structure InfoEq (a b : InfoReg) : Prop where
  cell : a.isCell = b.isCell
  loob : a.loobC = b.loobC
  hed : ∀ k, k ∈ a.hedOf ↔ k ∈ b.hedOf
  tel : ∀ k, k ∈ a.telOf ↔ k ∈ b.telOf
  hasHed : a.hasHed = b.hasHed
  hasTel : a.hasTel = b.hasTel
  decOf : a.decOf = b.decOf
  hasImm : a.hasImm = b.hasImm

theorem InfoEq.refl (a : InfoReg) : InfoEq a a :=
  ⟨rfl, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, rfl, rfl, rfl⟩

theorem InfoEq.symm {a b : InfoReg} (h : InfoEq a b) : InfoEq b a :=
  ⟨h.cell.symm, h.loob.symm, fun k => (h.hed k).symm, fun k => (h.tel k).symm, h.hasHed.symm,
    h.hasTel.symm, h.decOf.symm, h.hasImm.symm⟩

theorem InfoEq.trans {a b c : InfoReg} (h1 : InfoEq a b) (h2 : InfoEq b c) : InfoEq a c :=
  ⟨h1.cell.trans h2.cell, h1.loob.trans h2.loob, fun k => (h1.hed k).trans (h2.hed k),
    fun k => (h1.tel k).trans (h2.tel k), h1.hasHed.trans h2.hasHed, h1.hasTel.trans h2.hasTel,
    h1.decOf.trans h2.decOf, h1.hasImm.trans h2.hasImm⟩

theorem infoEq_equiv : Equivalence InfoEq := ⟨InfoEq.refl, InfoEq.symm, InfoEq.trans⟩

/-- `loobImm` reads only `hasImm`. -/
theorem loobImm_congr {a b : InfoReg} (h : a.hasImm = b.hasImm) : a.loobImm = b.loobImm := by
  unfold InfoReg.loobImm; rw [h]

theorem InfoEq.loobImm {a b : InfoReg} (h : InfoEq a b) : a.loobImm = b.loobImm := loobImm_congr h.hasImm

/-- `isLoob` is fixed where `hasImm` is not a loobean. -/
theorem InfoEq.isLoob {a b : InfoReg} (h : InfoEq a b) (hl : a.loobImm = false) : a.isLoob = b.isLoob := by
  have e := h.loob
  have hb : b.loobImm = false := h.loobImm ▸ hl
  unfold InfoReg.loobC at e
  rw [hl, hb] at e
  simpa using e

theorem joinReg_isCell (a b : InfoReg) : (joinReg a b).isCell = (a.isCell && b.isCell) := rfl
theorem joinReg_hasHed (a b : InfoReg) : (joinReg a b).hasHed = meetO a.hasHed b.hasHed := rfl
theorem joinReg_hasTel (a b : InfoReg) : (joinReg a b).hasTel = meetO a.hasTel b.hasTel := rfl
theorem joinReg_decOf (a b : InfoReg) : (joinReg a b).decOf = meetO a.decOf b.decOf := rfl
theorem joinReg_hasImm (a b : InfoReg) : (joinReg a b).hasImm = meetO a.hasImm b.hasImm := rfl

theorem mem_joinReg_hed (a b : InfoReg) (k : Nat) : k ∈ (joinReg a b).hedOf ↔ k ∈ a.hedOf ∧ k ∈ b.hedOf := by
  simp [joinReg, List.mem_filter]

theorem mem_joinReg_tel (a b : InfoReg) (k : Nat) : k ∈ (joinReg a b).telOf ↔ k ∈ a.telOf ∧ k ∈ b.telOf := by
  simp [joinReg, List.mem_filter]

/-- **The class of `isLoob` of a join is the meet of the classes.** -/
theorem loobC_joinReg (a b : InfoReg) : (joinReg a b).loobC = (a.loobC && b.loobC) := by
  have e1 : (joinReg a b).isLoob = (a.loobC && b.loobC) := rfl
  unfold InfoReg.loobC at e1 ⊢
  rw [e1]
  by_cases h : a.hasImm = b.hasImm
  · have e2 : (joinReg a b).loobImm = a.loobImm :=
      loobImm_congr (by rw [joinReg_hasImm]; unfold meetO; rw [if_pos h])
    have e3 := loobImm_congr h
    rw [e2, ← e3]
    cases a.loobImm <;> simp
  · have e2 : (joinReg a b).loobImm = false := by
      unfold InfoReg.loobImm; rw [joinReg_hasImm]; unfold meetO; rw [if_neg h]
    rw [e2]; simp

theorem joinReg_congr {a a' b b' : InfoReg} (ha : InfoEq a a') (hb : InfoEq b b') :
    InfoEq (joinReg a b) (joinReg a' b') where
  cell := by rw [joinReg_isCell, joinReg_isCell, ha.cell, hb.cell]
  loob := by rw [loobC_joinReg, loobC_joinReg, ha.loob, hb.loob]
  hed k := by rw [mem_joinReg_hed, mem_joinReg_hed, ha.hed, hb.hed]
  tel k := by rw [mem_joinReg_tel, mem_joinReg_tel, ha.tel, hb.tel]
  hasHed := by rw [joinReg_hasHed, joinReg_hasHed, ha.hasHed, hb.hasHed]
  hasTel := by rw [joinReg_hasTel, joinReg_hasTel, ha.hasTel, hb.hasTel]
  decOf := by rw [joinReg_decOf, joinReg_decOf, ha.decOf, hb.decOf]
  hasImm := by rw [joinReg_hasImm, joinReg_hasImm, ha.hasImm, hb.hasImm]

theorem joinReg_comm (a b : InfoReg) : InfoEq (joinReg a b) (joinReg b a) where
  cell := by rw [joinReg_isCell, joinReg_isCell, Bool.and_comm]
  loob := by rw [loobC_joinReg, loobC_joinReg, Bool.and_comm]
  hed k := by rw [mem_joinReg_hed, mem_joinReg_hed, And.comm]
  tel k := by rw [mem_joinReg_tel, mem_joinReg_tel, And.comm]
  hasHed := by rw [joinReg_hasHed, joinReg_hasHed, meetO_comm]
  hasTel := by rw [joinReg_hasTel, joinReg_hasTel, meetO_comm]
  decOf := by rw [joinReg_decOf, joinReg_decOf, meetO_comm]
  hasImm := by rw [joinReg_hasImm, joinReg_hasImm, meetO_comm]

theorem joinReg_assoc (a b c : InfoReg) : InfoEq (joinReg (joinReg a b) c) (joinReg a (joinReg b c)) where
  cell := by simp only [joinReg_isCell, Bool.and_assoc]
  loob := by simp only [loobC_joinReg, Bool.and_assoc]
  hed k := by simp only [mem_joinReg_hed, and_assoc]
  tel k := by simp only [mem_joinReg_tel, and_assoc]
  hasHed := by simp only [joinReg_hasHed, meetO_assoc]
  hasTel := by simp only [joinReg_hasTel, meetO_assoc]
  decOf := by simp only [joinReg_decOf, meetO_assoc]
  hasImm := by simp only [joinReg_hasImm, meetO_assoc]

theorem joinReg_idem (a : InfoReg) : InfoEq (joinReg a a) a where
  cell := by rw [joinReg_isCell, Bool.and_self]
  loob := by rw [loobC_joinReg, Bool.and_self]
  hed k := by rw [mem_joinReg_hed, and_self]
  tel k := by rw [mem_joinReg_tel, and_self]
  hasHed := by rw [joinReg_hasHed, meetO_idem]
  hasTel := by rw [joinReg_hasTel, meetO_idem]
  decOf := by rw [joinReg_decOf, meetO_idem]
  hasImm := by rw [joinReg_hasImm, meetO_idem]

/-- `joinRegE` is `joinReg` up to `InfoEq`. -/
theorem joinRegE_eq (a b : InfoReg) : InfoEq (joinRegE a b) (joinReg a b) := by
  unfold joinRegE
  by_cases h : a = b
  · subst h; rw [if_pos rfl]; exact (joinReg_idem a).symm
  · rw [if_neg h]; exact InfoEq.refl _

theorem joinRegE_congr {a a' b b' : InfoReg} (ha : InfoEq a a') (hb : InfoEq b b') :
    InfoEq (joinRegE a b) (joinRegE a' b') :=
  (joinRegE_eq a b).trans ((joinReg_congr ha hb).trans (joinRegE_eq a' b').symm)

/-- `joinReg` of the same facts with the lists in another order is not equal:
`InfoEq` is the most that holds. -/
theorem joinReg_not_comm :
    joinReg { hedOf := [1, 2] } { hedOf := [2, 1] } ≠ joinReg { hedOf := [2, 1] } { hedOf := [1, 2] } := by
  decide

/-! ## Maps of facts and immediates -/

/-- Register maps of facts up to `InfoEq` at each register. -/
def AInfoEq (a b : AInfo) : Prop := ∀ k, OptR InfoEq (a k) (b k)

theorem aInfoEq_equiv : Equivalence AInfoEq :=
  ⟨fun a k => optR_refl InfoEq.refl (a k), fun h k => optR_symm (R := InfoEq) (fun _ _ => InfoEq.symm) (h k),
    fun h1 h2 k => optR_trans (R := InfoEq) (fun _ _ _ => InfoEq.trans) (h1 k) (h2 k)⟩

theorem joinInfoA_congr {a a' b b' : AInfo} (ha : AInfoEq a a') (hb : AInfoEq b b') :
    AInfoEq (joinInfoA a b) (joinInfoA a' b') := by
  intro k
  have h1 := ha k
  have h2 := hb k
  unfold joinInfoA
  revert h1 h2
  cases a k <;> cases a' k <;> cases b k <;> cases b' k <;> simp
  exact joinRegE_congr

theorem joinInfoA_comm (a b : AInfo) : AInfoEq (joinInfoA a b) (joinInfoA b a) := by
  intro k
  unfold joinInfoA
  cases a k <;> cases b k <;> simp
  rename_i x y
  exact (joinRegE_eq x y).trans ((joinReg_comm x y).trans (joinRegE_eq y x).symm)

theorem joinInfoA_assoc (a b c : AInfo) :
    AInfoEq (joinInfoA (joinInfoA a b) c) (joinInfoA a (joinInfoA b c)) := by
  intro k
  unfold joinInfoA
  cases a k <;> cases b k <;> cases c k <;> simp
  rename_i x y z
  exact (joinRegE_eq _ _).trans ((joinReg_congr (joinRegE_eq x y) (InfoEq.refl z)).trans
    ((joinReg_assoc x y z).trans ((joinReg_congr (InfoEq.refl x) (joinRegE_eq y z)).symm.trans
      (joinRegE_eq _ _).symm)))

/-- Immediates with the same members at each noun. -/
def ImmsEq (a b : AImms) : Prop := ∀ n x, x ∈ a n ↔ x ∈ b n

theorem immsEq_equiv : Equivalence ImmsEq :=
  ⟨fun _ _ _ => Iff.rfl, fun h n x => (h n x).symm, fun h1 h2 n x => (h1 n x).trans (h2 n x)⟩

theorem mem_joinImmsA (a b : AImms) (n : Noun) (x : Nat) : x ∈ joinImmsA a b n ↔ x ∈ a n ∧ x ∈ b n := by
  simp [joinImmsA, List.mem_filter]

theorem joinImmsA_congr {a a' b b' : AImms} (ha : ImmsEq a a') (hb : ImmsEq b b') :
    ImmsEq (joinImmsA a b) (joinImmsA a' b') := fun n x => by
  rw [mem_joinImmsA, mem_joinImmsA, ha n x, hb n x]

theorem joinImmsA_comm (a b : AImms) : ImmsEq (joinImmsA a b) (joinImmsA b a) := fun n x => by
  rw [mem_joinImmsA, mem_joinImmsA, And.comm]

theorem joinImmsA_assoc (a b c : AImms) :
    ImmsEq (joinImmsA (joinImmsA a b) c) (joinImmsA a (joinImmsA b c)) := fun n x => by
  simp only [mem_joinImmsA, and_assoc]

/-! ## Folds over permutations -/

section Fold

variable {α β : Type} {E : α → α → Prop}

theorem foldl_rel (hE : Equivalence E) (f : α → β → α) (hc : ∀ a a' x, E a a' → E (f a x) (f a' x)) :
    ∀ (l : List β) {a a' : α}, E a a' → E (l.foldl f a) (l.foldl f a')
  | [], _, _, h => h
  | x :: l, _, _, h => foldl_rel hE f hc l (hc _ _ x h)

/-- A fold whose step commutes on the right, over two permutations. -/
theorem foldl_perm_rel (hE : Equivalence E) (f : α → β → α) (hc : ∀ a a' x, E a a' → E (f a x) (f a' x))
    (hrc : ∀ a x y, E (f (f a x) y) (f (f a y) x)) {l l' : List β} (hp : l.Perm l') :
    ∀ {a a' : α}, E a a' → E (l.foldl f a) (l'.foldl f a') := by
  induction hp with
  | nil => intro a a' h; exact h
  | cons x _ ih => intro a a' h; exact ih (hc _ _ _ h)
  | swap x y l =>
    intro a a' h
    simp only [List.foldl_cons]
    exact foldl_rel hE f hc l (hE.trans (hrc a y x) (hc _ _ _ (hc _ _ _ h)))
  | trans _ _ ih1 ih2 => intro a a' h; exact hE.trans (ih1 h) (ih2 (hE.refl _))

/-- The right commutation from commutation and associativity. -/
theorem rc_of (hE : Equivalence E) (f : α → α → α)
    (hcg : ∀ a a' b b', E a a' → E b b' → E (f a b) (f a' b')) (hcm : ∀ a b, E (f a b) (f b a))
    (has : ∀ a b c, E (f (f a b) c) (f a (f b c))) (a x y : α) : E (f (f a x) y) (f (f a y) x) :=
  hE.trans (has a x y) (hE.trans (hcg _ _ _ _ (hE.refl a) (hcm x y)) (hE.symm (has a y x)))

/-- A fold of the first element with the rest. -/
def fold1 (f : α → α → α) : List α → Option α
  | [] => none
  | x :: l => some (l.foldl f x)

/-- **A fold of a commutative, associative step over two permutations.** -/
theorem fold1_perm (hE : Equivalence E) (f : α → α → α)
    (hcg : ∀ a a' b b', E a a' → E b b' → E (f a b) (f a' b')) (hcm : ∀ a b, E (f a b) (f b a))
    (has : ∀ a b c, E (f (f a b) c) (f a (f b c))) {l l' : List α} (hp : l.Perm l') :
    OptR E (fold1 f l) (fold1 f l') := by
  have hc : ∀ a a' x, E a a' → E (f a x) (f a' x) := fun a a' x h => hcg _ _ _ _ h (hE.refl x)
  have hrc := rc_of hE f hcg hcm has
  cases l with
  | nil => rw [hp.nil_eq.symm]; trivial
  | cons h t =>
    cases l' with
    | nil => exact absurd hp.symm.nil_eq (List.cons_ne_nil h t).symm
    | cons h' t' =>
      show E (t.foldl f h) (t'.foldl f h')
      by_cases e : h = h'
      · subst e
        exact foldl_perm_rel hE f hc hrc hp.cons_inv (hE.refl _)
      · have hm : h ∈ t' := by
          rcases List.mem_cons.mp (hp.mem_iff.mp List.mem_cons_self) with e' | hm
          · exact absurd e' e
          · exact hm
        obtain ⟨s1, s2, rfl⟩ := List.append_of_mem hm
        have p1 : (s1 ++ h :: s2).Perm (h :: (s1 ++ s2)) := List.perm_middle
        have p2 : (h :: t).Perm (h :: h' :: (s1 ++ s2)) :=
          hp.trans ((p1.cons h').trans (List.Perm.swap h h' (s1 ++ s2)))
        have q1 := foldl_perm_rel hE f hc hrc p2.cons_inv (hE.refl h)
        have q2 := foldl_perm_rel hE f hc hrc p1 (hE.refl h')
        simp only [List.foldl_cons] at q1 q2
        exact hE.trans q1 (hE.trans (foldl_rel hE f hc _ (hcm h h')) (hE.symm q2))

end Fold

/-! ## `mapM` over two permutations -/

theorem optR_perm_trans {β : Type} {x y z : Option (List β)} (h1 : OptR List.Perm x y)
    (h2 : OptR List.Perm y z) : OptR List.Perm x z :=
  optR_trans (R := List.Perm) (fun _ _ _ a b => List.Perm.trans a b) h1 h2

theorem mapM_perm {α β : Type} (v : α → Option β) {l l' : List α} (hp : l.Perm l') :
    OptR List.Perm (l.mapM v) (l'.mapM v) := by
  induction hp with
  | nil => simp [List.mapM_nil]
  | cons x _ ih =>
    simp only [List.mapM_cons]
    revert ih
    cases v x <;> cases List.mapM v _ <;> cases List.mapM v _ <;> simp
  | swap x y l =>
    simp only [List.mapM_cons]
    cases v x <;> cases v y <;> cases List.mapM v l <;> simp
    exact List.Perm.swap _ _ _
  | trans _ _ ih1 ih2 => exact optR_perm_trans ih1 ih2

/-- `foldlM` of a step that reads a value per element is `mapM`, then `foldl`. -/
theorem foldlM_map_eq {α β γ : Type} (v : β → Option γ) (f : α → γ → α) :
    ∀ (t : List β) (a : α), t.foldlM (fun acc o1 => (v o1).map fun i1 => f acc i1) a =
      (t.mapM v).map fun xs => xs.foldl f a
  | [], a => by simp [List.mapM_nil]
  | x :: t, a => by
    simp only [List.foldlM_cons, List.mapM_cons]
    cases v x with
    | none => simp
    | some b =>
      have ih := foldlM_map_eq v f t (f a b)
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at ih ⊢
      rw [ih]
      cases List.mapM v t <;> simp

/-- The bind of `fold1` over two related lists. -/
theorem optR_bind_fold1 {α : Type} {E : α → α → Prop} (hE : Equivalence E) (f : α → α → α)
    (hcg : ∀ a a' b b', E a a' → E b b' → E (f a b) (f a' b')) (hcm : ∀ a b, E (f a b) (f b a))
    (has : ∀ a b c, E (f (f a b) c) (f a (f b c))) {x y : Option (List α)} (h : OptR List.Perm x y) :
    OptR E (x.bind (fold1 f)) (y.bind (fold1 f)) := by
  revert h
  cases x <;> cases y <;> simp
  exact fold1_perm hE f hcg hcm has

/-! ## The phases under a permutation of `pre` -/

theorem mapM_cons_fold1 {α β : Type} (v : α → Option β) (f : β → β → β) (p : α) (t : List α) :
    ((p :: t).mapM v).bind (fold1 f) = (v p).bind fun x => (t.mapM v).map fun r => r.foldl f x := by
  simp only [List.mapM_cons]
  cases v p <;> simp
  cases List.mapM v t <;> simp [fold1]

/-- `aliasStart` on two or more predecessors is the join of their facts. -/
theorem aliasStart_many (g : AGen Map) (o p : Nat) {t : List Nat} (ht : t ≠ []) :
    aliasStart g o (p :: t) = ((p :: t).mapM g.info).bind (fold1 joinInfoA) := by
  rw [mapM_cons_fold1]
  simp only [aliasStart]
  simp only [foldlM_map_eq g.info joinInfoA t]
  cases g.info p with
  | none => rfl
  | some i0 =>
    simp only [Option.bind_some]
    cases List.mapM g.info t with
    | none => rfl
    | some r => simp [ht]

/-- **`aliasStart` under a permutation of `pre`**: related by `AInfoEq`. -/
theorem aliasStart_perm (g : AGen Map) (o : Nat) {pre pre' : List Nat} (hp : pre.Perm pre') :
    OptR AInfoEq (aliasStart g o pre) (aliasStart g o pre') := by
  match pre, pre', hp with
  | [], _, hp => rw [← hp.nil_eq]; trivial
  | [p], _, hp => rw [List.perm_singleton.mp hp.symm]; exact optR_refl (aInfoEq_equiv.refl) _
  | p :: q :: t, [], hp => exact absurd hp.symm.nil_eq (List.cons_ne_nil _ _).symm
  | p :: q :: t, [p'], hp =>
    have := hp.length_eq; simp at this
  | p :: q :: t, p' :: q' :: t', hp =>
    rw [aliasStart_many g o p (List.cons_ne_nil q t), aliasStart_many g o p' (List.cons_ne_nil q' t')]
    exact optR_bind_fold1 aInfoEq_equiv joinInfoA (fun _ _ _ _ => joinInfoA_congr) joinInfoA_comm
      joinInfoA_assoc (mapM_perm g.info hp)

theorem aliasStartImms_cons (g : AGen Map) (p : Nat) (t : List Nat) :
    aliasStartImms g (p :: t) = ((p :: t).mapM g.imms).bind (fold1 joinImmsA) := by
  rw [mapM_cons_fold1]
  simp only [aliasStartImms]
  simp only [foldlM_map_eq g.imms joinImmsA t]

/-- **`aliasStartImms` under a permutation of `pre`**: related by `ImmsEq`. -/
theorem aliasStartImms_perm (g : AGen Map) {pre pre' : List Nat} (hp : pre.Perm pre') :
    OptR ImmsEq (aliasStartImms g pre) (aliasStartImms g pre') := by
  match pre, pre', hp with
  | [], _, hp => rw [← hp.nil_eq]; exact optR_refl immsEq_equiv.refl _
  | p :: t, [], hp => exact absurd hp.symm.nil_eq (List.cons_ne_nil _ _).symm
  | p :: t, p' :: t', hp =>
    rw [aliasStartImms_cons, aliasStartImms_cons]
    exact optR_bind_fold1 immsEq_equiv joinImmsA (fun _ _ _ _ => joinImmsA_congr) joinImmsA_comm
      joinImmsA_assoc (mapM_perm g.imms hp)

theorem optR_map_flatten {β : Type} {x y : Option (List (List β))} (h : OptR List.Perm x y) :
    OptR List.Perm (x.map List.flatten) (y.map List.flatten) := by
  revert h
  cases x <;> cases y <;> simp
  exact List.Perm.flatten

/-- **`aliasEdges` under a permutation of `pre`**: the edges permuted. -/
theorem aliasEdges_perm (g : AGen Map) (o : Nat) {pre pre' : List Nat} (hp : pre.Perm pre') :
    OptR List.Perm (aliasEdges g o pre) (aliasEdges g o pre') :=
  optR_map_flatten (mapM_perm _ hp)

/-! ## `param-info` and the parameter loop -/

/-- Clearing the facts that name other registers keeps `InfoEq`. -/
theorem InfoEq.clear {a b : InfoReg} (h : InfoEq a b) :
    InfoEq { a with hedOf := [], telOf := [], hasHed := none, hasTel := none, decOf := none }
      { b with hedOf := [], telOf := [], hasHed := none, hasTel := none, decOf := none } where
  cell := h.cell
  loob := h.loob
  hed _ := Iff.rfl
  tel _ := Iff.rfl
  hasHed := rfl
  hasTel := rfl
  decOf := rfl
  hasImm := h.hasImm

/-- **`param-info` of a permutation of its inputs** is the same up to `InfoEq`. -/
theorem paramInfo_perm {ins ins' : List (Option InfoReg)} (hp : ins.Perm ins') :
    InfoEq (paramInfo ins) (paramInfo ins') := by
  have hf := hp.filterMap id
  have hl := hp.length_eq
  have hfl := hf.length_eq
  unfold paramInfo
  rw [hl] at *
  generalize ins.filterMap id = F at hf hfl ⊢
  generalize ins'.filterMap id = F' at hf hfl ⊢
  cases F with
  | nil => rw [← hf.nil_eq]; exact InfoEq.refl _
  | cons h t =>
    cases F' with
    | nil => exact absurd hf.symm.nil_eq (List.cons_ne_nil h t).symm
    | cons h' t' =>
      have hj : InfoEq (t.foldl (fun b a => joinReg a b) h) (t'.foldl (fun b a => joinReg a b) h') :=
        fold1_perm (f := fun b a => joinReg a b) infoEq_equiv (fun _ _ _ _ ha hb => joinReg_congr hb ha)
          (fun a b => joinReg_comm b a) (fun a b c => (joinReg_assoc c b a).symm) hf
      dsimp only
      rw [hfl]
      split
      · exact hj
      · exact hj.clear

theorem updA_eq {a a' : AInfo} (h : AInfoEq a a') (x : Nat) {v v' : InfoReg} (hv : InfoEq v v') :
    AInfoEq (updA a x (some v)) (updA a' x (some v')) := fun k => by
  unfold updA
  by_cases e : k = x
  · rw [if_pos e, if_pos e]; exact hv
  · rw [if_neg e, if_neg e]; exact h k

/-- **The parameter loop under a permutation of the edges** and related facts. -/
theorem aliasPars_perm (g : AGen Map) :
    ∀ (ps : List Nat) {edges edges' : List (Nat × List (Option Nat))} {loc loc' : AInfo},
      edges.Perm edges' → AInfoEq loc loc' →
      OptR AInfoEq (aliasPars g ps edges loc) (aliasPars g ps edges' loc')
  | [], _, _, _, _, _, hl => hl
  | x :: ps, edges, edges', loc, loc', he, hl => by
    simp only [aliasPars]
    have h := mapM_perm (aliasIn g) he
    revert h
    cases List.mapM (aliasIn g) edges <;> cases List.mapM (aliasIn g) edges' <;> simp
    intro hi
    exact aliasPars_perm g ps (he.map _) (updA_eq hl x (paramInfo_perm hi))

/-- **The parameters of a block under a permutation of `pre`**: the edges of
the two orders, then the loop. -/
theorem aliasPars_edges_perm (g : AGen Map) (o : Nat) (ps : List Nat) {pre pre' : List Nat}
    (hp : pre.Perm pre') {loc loc' : AInfo} (hl : AInfoEq loc loc') :
    OptR AInfoEq ((aliasEdges g o pre).bind fun e => aliasPars g ps e loc)
      ((aliasEdges g o pre').bind fun e => aliasPars g ps e loc') := by
  have h := aliasEdges_perm g o hp
  revert h
  cases aliasEdges g o pre <;> cases aliasEdges g o pre' <;> simp
  intro he
  exact aliasPars_perm g ps he hl

/-- Two lists without duplicates and with the same members are permutations
(the Hoon's `pre` and the model's `g.rev o`). -/
theorem perm_of_nodup {l l' : List Nat} (h : l.Nodup) (h' : l'.Nodup) (hm : ∀ x, x ∈ l ↔ x ∈ l') :
    l.Perm l' := (List.perm_ext_iff_of_nodup h h').mpr hm

/-! ## Equality fails: a witness -/

/-- The facts of the witness: two predecessors whose `hedOf` of register `0`
hold the same members in two orders. -/
def wInfo : Nat → Option AInfo
  | 1 => some fun r => if r = 0 then some { hedOf := [1, 2] } else none
  | 2 => some fun r => if r = 0 then some { hedOf := [2, 1] } else none
  | _ => none

/-- **`aliasStart` is not a function of the members of `pre`**: the two orders
of `[1, 2]` give `hedOf` of register `0` in two orders (`InfoEq`, not equal). -/
theorem aliasStart_order (new : Map Blob) :
    let g : AGen Map := { new := new, old := id, info := wInfo, imms := fun _ => none, rev := fun _ => [],
                          folded := false }
    (aliasStart g 5 [1, 2]).map (· 0) = some (some { hedOf := [1, 2] }) ∧
    (aliasStart g 5 [2, 1]).map (· 0) = some (some { hedOf := [2, 1] }) := by
  simp [aliasStart, wInfo, joinInfoA, joinRegE, joinReg, InfoReg.loobImm]

end Opt
end SkaModel
end Formalization
