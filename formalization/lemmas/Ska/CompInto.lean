import lemmas.Ska.CompIntoLook

/-!
# What `+into-need` does

`+into-need` walks the need of the edited noun down the edited axis: at
each step the half off the path is kept for the recipient (on a tack), and
a register that names the whole is rebuilt from the two halves by a `%con`;
at the axis the rest of the need is the donor's, and the tack, rolled up
with `+cons-need`, is the recipient's.  The ops are put in front of the
block `o` that `+into` emitted, deepest first.

`intoLoop_rec`: the loop is `intoRec`, the same walk as a recursion that
returns its ops, followed by one `+add-ops`.  `intoRec_ok`: the need of the
edited noun holds after the ops when the donor's and the recipient's do, and
the edited noun has its shape exactly when the donor and the recipient have
theirs.  The recipient's need can lose the requirement that the recipient
has the edited axis (the dropped halves are rebuilt with `+cons-need`); that
requirement is the look `axe` that `+into-sure` adds (`intoLok_looks`,
`slot_edit`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- The loop of `+into-need` as a recursion: the donor's need, the
recipient's need below this step, and the `%con` ops, deepest first. -/
def intoRec (axe : Nat) (ned : Need) : CM Map (Need × Need × List Pole) :=
  if _h : axe ≤ 1 then pure (ned, Need.none, []) else
  let h := decide (cap axe = 2)
  match ned with
  | Need.none => do
      let x ← intoRec (mas axe) Need.none
      pure (x.1, side h x.2.1 Need.none, x.2.2)
  | Need.this r => do
      let l ← re
      let r' ← re
      let x ← intoRec (mas axe) (Need.this (if h then l else r'))
      pure (x.1, side h x.2.1 (Need.this (if h then r' else l)), x.2.2 ++ [Pole.con l r' r])
  | Need.pair p q => do
      let x ← intoRec (mas axe) (if h then p else q)
      pure (x.1, side h x.2.1 (if h then q else p), x.2.2)
  | Need.both r hh t => do
      let l ← must hh
      let r' ← must t
      let x ← intoRec (mas axe) (if h then l.2 else r'.2)
      pure (x.1, side h x.2.1 (if h then r'.2 else l.2), x.2.2 ++ [Pole.con l.1 r'.1 r])
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- **The loop is the recursion and one `+add-ops`.** -/
theorem intoLoop_rec {o : Nat} : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole)
    (g g' : Gen Map) (x : Need × Need), intoLoop o axe ned tack ops g = some (x, g') →
    ∃ d r ops' g1, intoRec axe ned g = some ((d, r, ops'), g1) ∧ addOps o (ops' ++ ops) g1 = some ((), g') ∧
      x = (d, tack.foldl (fun acc e => side e.1 acc e.2) r) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned tack ops g g' x h
  rw [intoLoop] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    obtain ⟨u, g1, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ned, Need.none, [], g, by rw [intoRec, dif_pos h1]; rfl, by rw [List.nil_append]; exact h2, rfl⟩
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  cases ned with
  | none =>
    obtain ⟨d, r, ops', g1, e1, e2, rfl⟩ := ih _ lt _ _ _ _ _ _ h
    refine ⟨d, _, ops', g1, ?_, e2, rfl⟩
    rw [intoRec, dif_neg h1]; simp only [bind_apply, e1, Option.bind_some, pure_apply]
  | this r0 =>
    simp only [bind_apply, re_apply, Option.bind_some] at h
    obtain ⟨d, r, ops', g1, e1, e2, rfl⟩ := ih _ lt _ _ _ _ _ _ h
    refine ⟨d, _, ops' ++ [_], g1, ?_, by rw [List.append_assoc]; exact e2, rfl⟩
    rw [intoRec, dif_neg h1]; simp only [bind_apply, re_apply, e1, Option.bind_some, pure_apply]
  | pair p q =>
    obtain ⟨d, r, ops', g1, e1, e2, rfl⟩ := ih _ lt _ _ _ _ _ _ h
    refine ⟨d, _, ops', g1, ?_, e2, rfl⟩
    rw [intoRec, dif_neg h1]; simp only [bind_apply, e1, Option.bind_some, pure_apply]
  | both r0 hh t =>
    simp only at h
    obtain ⟨l, g2, h2, h⟩ := bind_some h
    obtain ⟨l', g3, h3, h⟩ := bind_some h
    obtain ⟨d, r, ops', g1, e1, e2, rfl⟩ := ih _ lt _ _ _ _ _ _ h
    refine ⟨d, _, ops' ++ [_], g1, ?_, by rw [List.append_assoc]; exact e2, rfl⟩
    rw [intoRec, dif_neg h1]; simp only [bind_apply, h2, h3, e1, Option.bind_some, pure_apply]

/-! ## Cells with a side -/

/-- The cell whose half on the side `h` (the head when `h`) is `u`. -/
def cellOn (h : Bool) (u v : Noun) : Noun := if h then C u v else C v u

theorem edit_step {axe : Nat} (ha : 2 ≤ axe) {x t n : Noun} (he : edit? axe x t = some n) :
    ∃ u v w, t = cellOn (decide (cap axe = 2)) u v ∧ edit? (mas axe) x u = some w ∧
      n = cellOn (decide (cap axe = 2)) w v := by
  rw [edit?_cap ha] at he
  cases t with
  | atom => simp at he
  | cell a b =>
    simp only at he
    by_cases hc : cap axe = 2
    · rw [if_pos hc] at he
      obtain ⟨w, e1, rfl⟩ := Option.map_eq_some_iff.mp he
      exact ⟨a, b, w, by simp [cellOn, hc], e1, by simp [cellOn, hc]⟩
    · rw [if_neg hc] at he
      obtain ⟨w, e1, rfl⟩ := Option.map_eq_some_iff.mp he
      exact ⟨b, a, w, by simp [cellOn, hc], e1, by simp [cellOn, hc]⟩

theorem nmem_side (h : Bool) (a b : Need) (y : Nat) : NMem (side h a b) y ↔ NMem a y ∨ NMem b y := by
  cases h <;> simp only [side, consNeed, Bool.false_eq_true, if_true, if_false] <;> split <;>
    rename_i e <;> (try obtain ⟨rfl, rfl⟩ := e) <;> simp [NMem, or_comm]

theorem distinct_side (h : Bool) {a b : Need} (da : Distinct a) (db : Distinct b)
    (dab : ∀ y, NMem a y → ¬ NMem b y) : Distinct (side h a b) := by
  cases h <;> simp only [side, consNeed, Bool.false_eq_true, if_true, if_false] <;> split
  · trivial
  · exact ⟨db, da, fun y hb ha => dab y ha hb⟩
  · trivial
  · exact ⟨da, db, dab⟩

theorem fits_side (h : Bool) (a b : Need) (u v : Noun) :
    Fits (side h a b) (cellOn h u v) ↔ Fits a u ∧ Fits b v := by
  cases h <;> simp only [side, consNeed, cellOn, Bool.false_eq_true, if_true, if_false] <;> split <;>
    rename_i e <;> (try obtain ⟨rfl, rfl⟩ := e) <;> simp [Fits, and_comm]

theorem holds_side (h : Bool) (a b : Need) (R : Map (Option Noun)) (u v : Noun) :
    HoldsN (side h a b) R (cellOn h u v) ↔ HoldsN a R u ∧ HoldsN b R v := by
  cases h <;> simp only [side, consNeed, cellOn, Bool.false_eq_true, if_true, if_false] <;> split <;>
    rename_i e <;> (try obtain ⟨rfl, rfl⟩ := e) <;> simp [HoldsN, and_comm]

theorem fits_pair_on (h : Bool) (p q : Need) (u v : Noun) :
    Fits (Need.pair p q) (cellOn h u v) ↔ Fits (if h then p else q) u ∧ Fits (if h then q else p) v := by
  cases h <;> simp [cellOn, Fits, and_comm]

theorem holds_pair_on (h : Bool) (p q : Need) (R : Map (Option Noun)) (u v : Noun) :
    HoldsN (Need.pair p q) R (cellOn h u v) ↔
      HoldsN (if h then p else q) R u ∧ HoldsN (if h then q else p) R v := by
  cases h <;> simp [cellOn, HoldsN, and_comm]

theorem fits_both_on (h : Bool) (x : Nat) (p q : Need) (u v : Noun) :
    Fits (Need.both x p q) (cellOn h u v) ↔ Fits (if h then p else q) u ∧ Fits (if h then q else p) v := by
  cases h <;> simp [cellOn, Fits, and_comm]

theorem holds_both_on (h : Bool) (x : Nat) (p q : Need) (R : Map (Option Noun)) (u v : Noun) :
    HoldsN (Need.both x p q) R (cellOn h u v) ↔ SkaModel.read x R = some (cellOn h u v) ∧
      HoldsN (if h then p else q) R u ∧ HoldsN (if h then q else p) R v := by
  cases h <;> simp [cellOn, HoldsN, and_comm]

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {tr : Trace}

theorem runs_con_on (h : Bool) {l r' x0 : Nat} {R : Map (Option Noun)} {w v : Noun}
    (hn : SkaModel.read (if h then l else r') R = some w) (ho : SkaModel.read (if h then r' else l) R = some v) :
    Runs lib O c gul st tr [Pole.con l r' x0] R (store x0 (cellOn h w v) R) := by
  cases h
  · simp only [Bool.false_eq_true, if_false] at hn ho; exact runs_con ho hn
  · simp only [if_true] at hn ho; exact runs_con hn ho

end

/-! ## The recursion -/

/-- What one run of `intoRec` does. -/
structure IntoOK (axe : Nat) (ned d r : Need) (ops : List Pole) (g g' : Gen Map) : Prop where
  gen : g' = { g with re := g'.re }
  le : g.re ≤ g'.re
  md : ∀ y, NMem d y → NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)
  mr : ∀ y, NMem r y → NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)
  sem : Distinct ned → (∀ y, NMem ned y → y < g.re) →
    Distinct d ∧ Distinct r ∧ (∀ y, NMem d y → ¬ NMem r y) ∧
    (∀ x t n, edit? axe x t = some n → (Fits ned n ↔ Fits d x ∧ Fits r t)) ∧
    (∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (tr : Trace)
      (R : Map (Option Noun)) (x t n : Noun), edit? axe x t = some n → HoldsN d R x → HoldsN r R t →
      ∃ R', Runs lib O c gul st tr ops R R' ∧ HoldsN ned R' n ∧
        ∀ y, ¬ NMem ned y → (y < g.re ∨ g'.re ≤ y) → SkaModel.read y R' = SkaModel.read y R)

theorem intoRec_ok : ∀ (axe : Nat) (ned : Need) (g g' : Gen Map) (d r : Need) (ops : List Pole),
    1 ≤ axe → intoRec axe ned g = some ((d, r, ops), g') → IntoOK axe ned d r ops g g' := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned g g' d r ops ha h
  rw [intoRec] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have a1 : axe = 1 := by omega
    subst a1
    refine ⟨rfl, Nat.le_refl _, fun y hy => Or.inl hy, fun y hy => hy.elim, fun dn _ =>
      ⟨dn, trivial, fun _ _ h => h.elim, fun x t n he => ?_, fun lib σ O c gul st tr R x t n he hd _ => ?_⟩⟩
    · simp only [edit?_one, Option.some.injEq] at he; subst he; simp [Fits]
    · simp only [edit?_one, Option.some.injEq] at he; subst he
      exact ⟨R, Runs.nil R, hd, fun _ _ _ => rfl⟩
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  have m1 : 1 ≤ mas axe := mas_pos axe (by omega)
  have es : ∀ {x t n : Noun}, edit? axe x t = some n →
      ∃ u v w, t = cellOn (decide (cap axe = 2)) u v ∧ edit? (mas axe) x u = some w ∧
        n = cellOn (decide (cap axe = 2)) w v := fun he => edit_step (by omega) he
  generalize decide (cap axe = 2) = b at h es
  cases ned with
  | none =>
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have I := ih _ lt _ _ _ _ _ _ m1 e1
    refine ⟨I.gen, I.le, I.md, fun y hy => ?_, fun _ _ => ?_⟩
    · rcases (nmem_side b _ _ y).mp hy with a | a
      · exact I.mr y a
      · exact a.elim
    obtain ⟨Dd, Dr, Ddr, F, H⟩ := I.sem trivial (fun y hy => hy.elim)
    refine ⟨Dd, distinct_side b Dr trivial (fun _ _ h => h), fun y a b' => ?_, fun x t n he => ?_,
      fun lib σ O c gul st tr R x t n he hd hr => ?_⟩
    · rcases (nmem_side _ _ _ y).mp b' with e | e
      · exact Ddr y a e
      · exact e
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      rw [fits_side, ← and_assoc, ← F x u w e2]; simp [Fits]
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      obtain ⟨R', r1, _, fr⟩ := H lib σ O c gul st tr R x u w e2 hd ((holds_side _ _ _ _ _ _).mp hr).1
      exact ⟨R', r1, trivial, fr⟩
  | this x0 =>
    obtain ⟨l, gl, hl, h⟩ := bind_some h
    rw [re_apply] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨l', gl', hl', h⟩ := bind_some h
    rw [re_apply] at hl'; simp only [Option.some.injEq, Prod.mk.injEq] at hl'; obtain ⟨rfl, rfl⟩ := hl'
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have I := ih _ lt _ _ _ _ _ _ m1 e1
    have L : g.re + 2 ≤ g1.re := I.le
    have md : ∀ y, NMem d0 y → y = (if b then g.re else g.re + 1) ∨ (g.re + 2 ≤ y ∧ y < g1.re) := I.md
    have mr : ∀ y, NMem r0 y → y = (if b then g.re else g.re + 1) ∨ (g.re + 2 ≤ y ∧ y < g1.re) := I.mr
    have nn : ∀ y, NMem (Need.this (if b then g.re + 1 else g.re)) y ↔ y = (if b then g.re + 1 else g.re) :=
      fun y => Iff.rfl
    refine ⟨I.gen.trans rfl, by omega, fun y hy => ?_, fun y hy => ?_, fun _ _ => ?_⟩
    · rcases md y hy with e | ⟨e1, e2⟩
      · exact Or.inr ⟨by cases b <;> simp at e <;> omega, by cases b <;> simp at e <;> omega⟩
      · exact Or.inr ⟨by omega, e2⟩
    · rcases (nmem_side b _ _ y).mp hy with a | a
      · rcases mr y a with e | ⟨e1, e2⟩
        · exact Or.inr ⟨by cases b <;> simp at e <;> omega, by cases b <;> simp at e <;> omega⟩
        · exact Or.inr ⟨by omega, e2⟩
      · rw [nn] at a
        exact Or.inr ⟨by cases b <;> simp at a <;> omega, by cases b <;> simp at a <;> omega⟩
    obtain ⟨Dd, Dr, Ddr, F, H⟩ := I.sem trivial (fun y hy => by
      have : y = if b then g.re else g.re + 1 := hy
      show y < g.re + 1 + 1
      cases b <;> simp at this <;> omega)
    refine ⟨Dd, distinct_side b Dr trivial (fun y a c => ?_), fun y a c => ?_, fun x t n he => ?_,
      fun lib σ O c gul st tr R x t n he hd hr => ?_⟩
    · rw [nn] at c
      rcases mr y a with e | e <;> cases b <;> simp at e c <;> omega
    · rcases (nmem_side _ _ _ y).mp c with e | e
      · exact Ddr y a e
      · rw [nn] at e
        rcases md y a with e' | e' <;> cases b <;> simp at e e' <;> omega
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      rw [fits_side, ← and_assoc, ← F x u w e2]; simp [Fits]
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      obtain ⟨hr0, hold⟩ := (holds_side _ _ _ _ _ _).mp hr
      obtain ⟨R1, r1, hn1, fr1⟩ := H lib σ O c gul st tr R x u w e2 hd hr0
      have hold' : SkaModel.read (if b then g.re + 1 else g.re) R = some v := hold
      have ho1 : SkaModel.read (if b then g.re + 1 else g.re) R1 = some v :=
        (fr1 _ (fun e => by
          have : (if b then g.re + 1 else g.re) = (if b then g.re else g.re + 1) := e
          cases b <;> simp at this) (Or.inl (by show (if b then g.re + 1 else g.re) < g.re + 1 + 1; split <;> omega))).trans hold'
      refine ⟨store x0 (cellOn b w v) R1, Runs.append r1 (runs_con_on b hn1 ho1), read_store_eq _ _ _,
        fun y hy hlt => ?_⟩
      rw [read_store_ne (fun e => hy e)]
      exact fr1 y (fun e => by
        have : y = if b then g.re else g.re + 1 := e
        cases b <;> simp at this <;> omega) (by simp only at hlt ⊢; omega)
  | pair p q =>
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have I := ih _ lt _ _ _ _ _ _ m1 e1
    have sub_new : ∀ y, NMem (if b then p else q) y → NMem (Need.pair p q) y := fun y hy => by
      cases b <;> simp at hy <;> simp [NMem, hy]
    have sub_old : ∀ y, NMem (if b then q else p) y → NMem (Need.pair p q) y := fun y hy => by
      cases b <;> simp at hy <;> simp [NMem, hy]
    refine ⟨I.gen, I.le, fun y hy => ?_, fun y hy => ?_, fun dn lo => ?_⟩
    · rcases I.md y hy with e | e
      · exact Or.inl (sub_new y e)
      · exact Or.inr e
    · rcases (nmem_side _ _ _ y).mp hy with e | e
      · rcases I.mr y e with e | e
        · exact Or.inl (sub_new y e)
        · exact Or.inr e
      · exact Or.inl (sub_old y e)
    have dno : Distinct (if b then p else q) ∧ Distinct (if b then q else p) ∧
        ∀ y, NMem (if b then p else q) y → ¬ NMem (if b then q else p) y := by
      obtain ⟨d1, d2, d3⟩ := dn
      cases b
      · exact ⟨d2, d1, fun y a c => d3 y c a⟩
      · exact ⟨d1, d2, d3⟩
    obtain ⟨Dd, Dr, Ddr, F, H⟩ := I.sem dno.1 (fun y hy => lo y (sub_new y hy))
    refine ⟨Dd, distinct_side b Dr dno.2.1 (fun y a c => ?_), fun y a c => ?_, fun x t n he => ?_,
      fun lib σ O c gul st tr R x t n he hd hr => ?_⟩
    · rcases I.mr y a with e | ⟨e, _⟩
      · exact dno.2.2 y e c
      · have := lo y (sub_old y c); omega
    · rcases (nmem_side _ _ _ y).mp c with e | e
      · exact Ddr y a e
      · rcases I.md y a with e' | ⟨e', _⟩
        · exact dno.2.2 y e' e
        · have := lo y (sub_old y e); omega
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      rw [fits_pair_on, fits_side, F x u w e2, and_assoc]
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      obtain ⟨hr0, hold⟩ := (holds_side _ _ _ _ _ _).mp hr
      obtain ⟨R1, r1, hn1, fr1⟩ := H lib σ O c gul st tr R x u w e2 hd hr0
      refine ⟨R1, r1, (holds_pair_on _ _ _ _ _ _).mpr ⟨hn1, HoldsN.agree _ (fun y hy =>
        fr1 y (fun e => dno.2.2 y e hy) (Or.inl (lo y (sub_old y hy)))) hold⟩, fun y hy hlt =>
        fr1 y (fun e => hy (sub_new y e)) hlt⟩
  | both x0 hh tt =>
    obtain ⟨⟨rl, nl⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rt, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨d0, r0, ops0⟩, g3, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    obtain ⟨G1, L1, M1, Q1, F1, H1, D1⟩ := must_spec h1
    obtain ⟨G2, L2, M2, Q2, F2, H2, D2⟩ := must_spec h2
    have I := ih _ lt _ _ _ _ _ _ m1 e1
    simp only at I
    have sub_new : ∀ y, NMem (if b then nl else nt) y → NMem (Need.both x0 hh tt) y ∨ (g.re ≤ y ∧ y < g2.re) :=
      fun y hy => by
        cases b
        · simp only [Bool.false_eq_true, if_false] at hy
          rcases M2 y hy with e | e
          · exact Or.inl (Or.inr (Or.inr e))
          · exact Or.inr ⟨by omega, e.2⟩
        · simp only [if_true] at hy
          rcases M1 y hy with e | e
          · exact Or.inl (Or.inr (Or.inl e))
          · exact Or.inr ⟨e.1, by omega⟩
    have sub_old : ∀ y, NMem (if b then nt else nl) y → NMem (Need.both x0 hh tt) y ∨ (g.re ≤ y ∧ y < g2.re) :=
      fun y hy => by
        cases b
        · simp only [Bool.false_eq_true, if_false] at hy
          rcases M1 y hy with e | e
          · exact Or.inl (Or.inr (Or.inl e))
          · exact Or.inr ⟨e.1, by omega⟩
        · simp only [if_true] at hy
          rcases M2 y hy with e | e
          · exact Or.inl (Or.inr (Or.inr e))
          · exact Or.inr ⟨by omega, e.2⟩
    refine ⟨I.gen.trans (by rw [G2, G1]), by have := I.le; omega, fun y hy => ?_, fun y hy => ?_,
      fun dn lo => ?_⟩
    · rcases I.md y hy with e | e
      · rcases sub_new y e with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e.1, by have := I.le; omega⟩
      · exact Or.inr ⟨by omega, e.2⟩
    · rcases (nmem_side _ _ _ y).mp hy with e | e
      · rcases I.mr y e with e | e
        · rcases sub_new y e with e | e
          · exact Or.inl e
          · exact Or.inr ⟨e.1, by have := I.le; omega⟩
        · exact Or.inr ⟨by omega, e.2⟩
      · rcases sub_old y e with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e.1, by have := I.le; omega⟩
    obtain ⟨dh, dt, dht, nh, nt'⟩ := dn
    have loh : ∀ y, NMem hh y → y < g.re := fun y hy => lo y (Or.inr (Or.inl hy))
    have lot : ∀ y, NMem tt y → y < g.re := fun y hy => lo y (Or.inr (Or.inr hy))
    have Dl := D1 dh loh
    have Dt := D2 dt (fun y hy => Nat.lt_of_lt_of_le (lot y hy) L1)
    -- the halves on and off the path share no register
    have dno : ∀ y, NMem (if b then nl else nt) y → ¬ NMem (if b then nt else nl) y := by
      have k : ∀ y, NMem nl y → ¬ NMem nt y := fun y a c => by
        rcases M1 y a with e | e <;> rcases M2 y c with e' | e'
        · exact dht y e e'
        · have := loh y e; omega
        · have := lot y e'; omega
        · omega
      cases b
      · exact fun y a c => k y c a
      · exact k
    have dnew : Distinct (if b then nl else nt) := by cases b <;> assumption
    have dold : Distinct (if b then nt else nl) := by cases b <;> assumption
    have lonew : ∀ y, NMem (if b then nl else nt) y → y < g2.re := fun y hy => by
      rcases sub_new y hy with e | e
      · have := lo y e; omega
      · exact e.2
    have loold : ∀ y, NMem (if b then nt else nl) y → y < g2.re := fun y hy => by
      rcases sub_old y hy with e | e
      · have := lo y e; omega
      · exact e.2
    obtain ⟨Dd, Dr, Ddr, F, H⟩ := I.sem dnew lonew
    refine ⟨Dd, distinct_side b Dr dold (fun y a c => ?_), fun y a c => ?_, fun x t n he => ?_,
      fun lib σ O c gul st tr R x t n he hd hr => ?_⟩
    · rcases I.mr y a with e | ⟨e, _⟩
      · exact dno y e c
      · have := loold y c; omega
    · rcases (nmem_side _ _ _ y).mp c with e | e
      · exact Ddr y a e
      · rcases I.md y a with e' | ⟨e', _⟩
        · exact dno y e' e
        · have := loold y e; omega
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      have fn : Fits (if b then nl else nt) w ↔ Fits (if b then hh else tt) w := by
        cases b
        · exact F2 w
        · exact F1 w
      have fo : Fits (if b then nt else nl) v ↔ Fits (if b then tt else hh) v := by
        cases b
        · exact F1 v
        · exact F2 v
      rw [fits_both_on, fits_side, ← fn, ← fo, F x u w e2, and_assoc]
    · obtain ⟨u, v, w, rfl, e2, rfl⟩ := es he
      obtain ⟨hr0, hold⟩ := (holds_side _ _ _ _ _ _).mp hr
      obtain ⟨R1, r1, hn1, fr1⟩ := H lib σ O c gul st tr R x u w e2 hd hr0
      have ho1 : HoldsN (if b then nt else nl) R1 v :=
        HoldsN.agree _ (fun y hy => fr1 y (fun e => dno y e hy) (Or.inl (loold y hy))) hold
      have hn : SkaModel.read (if b then rl else rt) R1 = some w ∧ HoldsN (if b then hh else tt) R1 w := by
        cases b
        · exact H2 R1 w hn1
        · exact H1 R1 w hn1
      have ho : SkaModel.read (if b then rt else rl) R1 = some v ∧ HoldsN (if b then tt else hh) R1 v := by
        cases b
        · exact H1 R1 v ho1
        · exact H2 R1 v ho1
      have x0h : ∀ y, NMem (if b then hh else tt) y → y ≠ x0 := fun y hy e => by
        subst e; cases b
        · exact nt' hy
        · exact nh hy
      have x0t : ∀ y, NMem (if b then tt else hh) y → y ≠ x0 := fun y hy e => by
        subst e; cases b
        · exact nh hy
        · exact nt' hy
      refine ⟨store x0 (cellOn b w v) R1, Runs.append r1 (runs_con_on b hn.1 ho.1),
        (holds_both_on _ _ _ _ _ _ _).mpr ⟨read_store_eq _ _ _,
          HoldsN.agree _ (fun y hy => read_store_ne (x0h y hy) _ _) hn.2,
          HoldsN.agree _ (fun y hy => read_store_ne (x0t y hy) _ _) ho.2⟩, fun y hy hlt => ?_⟩
      rw [read_store_ne (fun e => hy (Or.inl e))]
      refine fr1 y (fun e => ?_) (by omega)
      rcases sub_new y e with e | e
      · exact hy e
      · have := I.le; omega

/-! ## `+into` -/

theorem looks_put {lok : S} {a : Nat} {t : Noun} :
    Looks (HoonSet.put lok a) t ↔ Looks lok t ∧ (slot? a t).isSome := by
  constructor
  · intro h
    exact ⟨fun y hy => h y ((HoonSet.mem_put _ _ _).mpr (Or.inr hy)),
      h a ((HoonSet.mem_put _ _ _).mpr (Or.inl rfl))⟩
  · intro ⟨h1, h2⟩ y hy
    rcases (HoonSet.mem_put _ _ _).mp hy with rfl | hy
    · exact h2
    · exact h1 y hy

/-- `+into-need` from the state after the emit: the recursion's run, and
the one `+add-ops`. -/
theorem intoNeed_rec {axe : Nat} {ned : Need} {o : Nat} {g0 g2 : Gen Map} {x : Need × Need}
    (h : intoNeed axe ned o g0 = some (x, g2)) :
    1 ≤ axe ∧ ∃ ops g1, IntoOK axe ned x.1 x.2 ops g0 g1 ∧ g2.re = g1.re ∧ g2.bo = g1.bo ∧ g2.drop = g1.drop ∧
      (∀ o', o' ≠ o → HoonMap.get g2.blocks o' = HoonMap.get g1.blocks o') ∧
      (g1.drop = false → Front o g1 g2 ops) := by
  simp only [intoNeed] at h
  by_cases a0 : axe = 0
  · simp [a0] at h
  rw [if_neg a0] at h
  refine ⟨by omega, ?_⟩
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst a1
    have I := intoRec_ok 1 ned g0 g0 ned Need.none [] (Nat.le_refl _) (by rw [intoRec]; rfl)
    exact ⟨[], g0, I, rfl, rfl, rfl, fun _ _ => rfl, fun _ => front_nil o g0⟩
  rw [if_neg a1] at h
  obtain ⟨d, r, ops', g1, e1, e2, rfl⟩ := intoLoop_rec _ _ _ _ _ _ _ h
  have I := intoRec_ok axe ned g0 g1 d r ops' (by omega) e1
  obtain ⟨q1, q2, q3, q4⟩ := addOps_gen e2
  rw [List.append_nil] at e2
  exact ⟨ops', g1, I, q1, q2, q3, q4, fun hd => front_addOps e2 hd⟩

/-- **`+into`.**  The block `o` that it emits puts together, from the needs
of the donor and the recipient it returns, the need `laz` of the edited
noun, and goes on to `th`.  When the edit succeeds, the edited noun has the
shape and the looks of `laz` exactly when the donor and the recipient have
theirs; a recipient with its looks has the edited axis. -/
theorem into_ok {laz : Sure S} {th : Jmp} {axe : Nat} {g g' : Gen Map} {don rec : Sure S} {o : Nat}
    (h : into ⟨laz, th⟩ axe g = some ((don, rec, o), g')) :
    1 ≤ axe ∧ o = g.bo ∧ Ext g g' ∧ g'.bo = g.bo + 1 ∧
    (∀ y, NMem don.ned y → NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (∀ y, NMem rec.ned y → NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (∀ x t, FitsS rec t → (edit? axe x t).isSome) ∧
    (Distinct laz.ned → (∀ y, NMem laz.ned y → y < g.re) →
      Distinct don.ned ∧ Distinct rec.ned ∧ (∀ y, NMem don.ned y → ¬ NMem rec.ned y) ∧
      (∀ x t n, edit? axe x t = some n → (FitsS laz n ↔ FitsS don x ∧ FitsS rec t)) ∧
      (g.drop = false → ∀ (c : Straight Map), Agree c g g' → ∀ (lib : Lib) (σ : Type) (O : Oracle σ) st tr
        (R : Map (Option Noun)) x t n gul, edit? axe x t = some n → HoldsN don.ned R x → HoldsN rec.ned R t →
        ∃ R', HoldsN laz.ned R' n ∧
          (∀ y, ¬ NMem laz.ned y → (y < g.re ∨ g'.re ≤ y) → SkaModel.read y R' = SkaModel.read y R) ∧
          goJ lib O c gul st R tr (jmp0 o) = goJ lib O c gul st R' tr th)) := by
  simp only [into] at h
  obtain ⟨o', g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨a1, ops, g3, I, q1, q2, q3, q4, Fr⟩ := intoNeed_rec h3
  simp only at I
  have E0 := ext_emit g ⟨[], [], Termin.hop th⟩
  have b3 : g3.bo = g.bo + 1 := by rw [I.gen]; rfl
  have d3 : g3.drop = g.drop := by rw [I.gen]; rfl
  have k3 : g3.blocks = (g.emitted ⟨[], [], Termin.hop th⟩).blocks := by rw [I.gen]
  have r3 : g.re ≤ g3.re := I.le
  have E : Ext g g2 := ⟨by omega, by omega, by rw [q3, d3], fun o' ho' => by
    rw [q4 o' (by omega), k3]; exact E0.2.2.2 o' ho'⟩
  -- the recipient's looks, with the edited axis
  have lk : ∀ t, Looks (if axe = 1 then lr else HoonSet.put lr axe) t ↔ Looks lr t ∧ (slot? axe t).isSome := by
    intro t
    by_cases e : axe = 1
    · subst e; simp
    · rw [if_neg e]; exact looks_put
  refine ⟨a1, rfl, E, by omega, fun y hy => ?_, fun y hy => ?_, fun x t ht => ?_, fun dn lo => ?_⟩
  · rcases I.md y hy with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e.1, by omega⟩
  · rcases I.mr y hy with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e.1, by omega⟩
  · exact edit_isSome ((lk t).mp ht.2).2
  obtain ⟨Dd, Dr, Ddr, F, H⟩ := I.sem dn lo
  refine ⟨Dd, Dr, Ddr, fun x t n he => ?_, fun hd c hc lib σ O st' tr R x t n gul he hdx hrt => ?_⟩
  · simp only [FitsS]
    rw [F x t n he, intoLok_looks hl he, lk t]
    have := (slot_edit he).2
    simp only [this, and_true]
    exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
  · obtain ⟨R', r1, hl', u⟩ := H lib σ O c gul st' tr R x t n he hdx hrt
    have F0 : Front g.bo (g.emitted ⟨[], [], Termin.hop th⟩) g3 [] :=
      ⟨fun B fin hb => by rw [k3]; simpa using hb, fun o' _ => by rw [k3], b3.trans (emitted_bo g _).symm, by rw [d3]; rfl, r3⟩
    have Fr' := F0.trans (Fr (by rw [d3]; exact hd))
    have hb0 : HoonMap.get c.blocks g.bo = some ⟨[], ops ++ [], Termin.hop th⟩ := by
      rw [hc g.bo (Nat.le_refl _) (by omega)]
      have := Fr'.blk _ _ (emitted_get g _ hd)
      simpa using this
    refine ⟨R', hl', fun y hy hlt => u y hy (by simp only [emitted_re]; omega), ?_⟩
    rw [goJ_jmp0 _ _ _ _ hb0, r1, execBlob_hop]

end Comp
end SkaModel
end Formalization
