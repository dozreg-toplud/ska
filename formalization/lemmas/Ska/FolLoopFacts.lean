import lemmas.Ska.FolLoop
import lemmas.Ska.NommAgree

/-!
# Facts that the soundness of `fol-loop` rests on

* `Annot.mono`: the invariant of nomm holds on fewer subjects.
* `shape_fol`, `shape_other_crash`: a case of `fol-loop`'s `?+` is its
  pattern, and on the default case `+mink` crashes at once.
* What `+mink` returns on each kind of formula, taken apart (`mink_inv_*`)
  and put together (`mink_mk_*`), for products (`%0` tones) from the empty
  trace.
* `pull_yes`: a sock pulled to a fully known `&` determines the subject's
  part at the axis, which exists.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## The invariant on fewer subjects -/

theorem Img_mono {lib : Lib} {P Q : Noun → Prop} {b : Noun} (h : ∀ x, Q x → P x) :
    ∀ y, Img lib Q b y → Img lib P b y :=
  fun _ ⟨x, gul, hx, hm⟩ => ⟨x, gul, h x hx, hm⟩

theorem Img8_mono {lib : Lib} {P Q : Noun → Prop} {b : Noun} (h : ∀ x, Q x → P x) :
    ∀ z, Img8 lib Q b z → Img8 lib P b z :=
  fun _ ⟨x, y, gul, hx, hm, hz⟩ => ⟨x, y, gul, h x hx, hm, hz⟩

/-- **`Annot` holds on fewer subjects.** -/
theorem Annot.mono {lib : Lib} {code : Bell → Option Nomm} :
    ∀ {P f n}, Annot lib code P f n → ∀ {Q : Noun → Prop}, (∀ x, Q x → P x) → Annot lib code Q f n := by
  intro P f n h
  induction h with
  | cons _ _ ih1 ih2 => intro Q hQ; exact Annot.cons (ih1 hQ) (ih2 hQ)
  | n0 => intro Q _; exact Annot.n0
  | n1 => intro Q _; exact Annot.n1
  | indirect _ _ ih1 ih2 => intro Q hQ; exact Annot.indirect (ih1 hQ) (ih2 hQ)
  | direct _ _ hc hy hg ih1 ih2 =>
    intro Q hQ
    exact Annot.direct (ih1 hQ) (ih2 hQ) hc (fun x gul y hx => hy x gul y (hQ x hx))
      (fun x gul g hx => hg x gul g (hQ x hx))
  | inline _ htot _ ih1 ih2 =>
    intro Q hQ
    exact Annot.inline (ih1 hQ) (fun x gul hx => htot x gul (hQ x hx)) (ih2 (Img_mono hQ))
  | n3 _ ih => intro Q hQ; exact Annot.n3 (ih hQ)
  | n4 _ ih => intro Q hQ; exact Annot.n4 (ih hQ)
  | n5 _ _ ih1 ih2 => intro Q hQ; exact Annot.n5 (ih1 hQ) (ih2 hQ)
  | n6 _ _ _ ih1 ih2 ih3 => intro Q hQ; exact Annot.n6 (ih1 hQ) (ih2 hQ) (ih3 hQ)
  | n7 _ _ ih1 ih2 => intro Q hQ; exact Annot.n7 (ih1 hQ) (ih2 (Img_mono hQ))
  | n8 _ _ ih1 ih2 => intro Q hQ; exact Annot.n8 (ih1 hQ) (ih2 (Img8_mono hQ))
  | n9 _ _ ih1 ih2 => intro Q hQ; exact Annot.n9 (ih1 hQ) (ih2 (Img_mono hQ))
  | n10 hax _ _ ih1 ih2 => intro Q hQ; exact Annot.n10 hax (ih1 hQ) (ih2 hQ)
  | n11s _ ih => intro Q hQ; exact Annot.n11s (ih hQ)
  | n11d _ _ ih1 ih2 => intro Q hQ; exact Annot.n11d (ih1 hQ) (ih2 hQ)
  | mean _ _ ih1 ih2 => intro Q hQ; exact Annot.mean (ih1 hQ) (ih2 hQ)
  | n12 _ _ ih1 ih2 => intro Q hQ; exact Annot.n12 (ih1 hQ) (ih2 hQ)
  | bare hb => intro Q _; exact Annot.bare hb
  | memo hh _ ih =>
    intro Q hQ
    exact Annot.memo (fun x gul hx => hh x gul (hQ x hx)) (ih hQ)
  | crash hc => intro Q _; exact Annot.crash hc

/-! ## The cases of the `?+` -/

/-- A case of the `?+` is its pattern. -/
theorem shape_fol (f : Noun) : shape f = Shape.other ∨ (shape f).fol = f := by
  unfold shape
  split <;> first | (left; rfl) | (right; rfl)

/-- On the default case of the `?+`, `+mink` crashes at once: the formula is
an atom, has no case in `+mink`, or has an operand that is an atom, which
`+mink` runs first. -/
theorem shape_other_crash {f : Noun} (h : shape f = Shape.other) (lib : Lib) (gul : Noun)
    (t : Trace) (s : Noun) : minkF lib gul 2 t s f = some (Tone.two t) := by
  match f, h with
  | Noun.atom _, _ => rfl
  | Noun.cell (Noun.cell _ _) _, h => simp [shape] at h
  | Noun.cell (Noun.atom 0) (Noun.atom _), h => simp [shape] at h
  | Noun.cell (Noun.atom 0) (Noun.cell _ _), _ => rfl
  | Noun.cell (Noun.atom 1) _, h => simp [shape] at h
  | Noun.cell (Noun.atom 2) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 2) (Noun.cell (Noun.atom _) _), _ => rfl
  | Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell _ _) _), h => simp [shape] at h
  | Noun.cell (Noun.atom 3) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 3) (Noun.cell _ _), h => simp [shape] at h
  | Noun.cell (Noun.atom 4) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 4) (Noun.cell _ _), h => simp [shape] at h
  | Noun.cell (Noun.atom 5) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 5) (Noun.cell (Noun.atom _) _), _ => rfl
  | Noun.cell (Noun.atom 5) (Noun.cell (Noun.cell _ _) _), h => simp [shape] at h
  | Noun.cell (Noun.atom 6) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 6) (Noun.cell _ (Noun.atom _)), _ => rfl
  | Noun.cell (Noun.atom 6) (Noun.cell (Noun.atom _) (Noun.cell _ _)), _ => rfl
  | Noun.cell (Noun.atom 6) (Noun.cell (Noun.cell _ _) (Noun.cell _ _)), h => simp [shape] at h
  | Noun.cell (Noun.atom 7) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 7) (Noun.cell (Noun.atom _) _), _ => rfl
  | Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell _ _) _), h => simp [shape] at h
  | Noun.cell (Noun.atom 8) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 8) (Noun.cell (Noun.atom _) _), _ => rfl
  | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell _ _) _), h => simp [shape] at h
  | Noun.cell (Noun.atom 9) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.cell _ _) _), _ => rfl
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom _) (Noun.atom _)), _ => rfl
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom _) (Noun.cell _ _)), h => simp [shape] at h
  | Noun.cell (Noun.atom 10) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.atom _) _), _ => rfl
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.cell _ _) _) _), _ => rfl
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a) _) (Noun.atom _)), _ =>
    by_cases ha : a = 0
    · subst ha; rfl
    · simp [minkF, minkStep, ha]
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom _) _) (Noun.cell _ _)), h =>
    simp [shape] at h
  | Noun.cell (Noun.atom 11) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) (Noun.atom _)), _ => rfl
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) (Noun.cell _ _)), h => simp [shape] at h
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.cell _ _) _) _), _ => rfl
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) (Noun.atom _)) _), _ => rfl
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) (Noun.cell _ _)) _), h =>
    simp [shape] at h
  | Noun.cell (Noun.atom 12) (Noun.atom _), _ => rfl
  | Noun.cell (Noun.atom 12) (Noun.cell (Noun.atom _) _), _ => rfl
  | Noun.cell (Noun.atom 12) (Noun.cell (Noun.cell _ _) _), h => simp [shape] at h
  | Noun.cell (Noun.atom (_ + 13)) _, _ => rfl

theorem shape_other_crashes {f : Noun} (h : shape f = Shape.other) (lib : Lib) :
    CrashesAtOnce lib f :=
  fun gul t s => ⟨2, shape_other_crash h lib gul t s⟩

/-! ## What `+mink` returns, taken apart -/

section MinkParts

variable {lib : Lib} {gul : Noun}

theorem mink_succ {x f : Noun} {r : Tone} (h : Mink lib gul [] x f r) :
    ∃ n, minkStep lib gul (minkF lib gul n) [] x f = some r := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [minkF] at hn
  | succ n => exact ⟨n, hn⟩

/-- A run that returns from a trace returns the same from the empty one. -/
theorem Mink.nil {t : Trace} {x f p : Noun} (h : minkF lib gul n t x f = some (Tone.zero p)) :
    Mink lib gul [] x f (Tone.zero p) := ⟨n, mink_nil_of_zero h⟩

theorem tbind_zero_inv {x : Option Tone} {k : Noun → Option Tone} {p : Noun}
    (h : tbind x k = some (Tone.zero p)) : ∃ y, x = some (Tone.zero y) ∧ k y = some (Tone.zero p) := by
  rcases tbind_eq_some h with h | ⟨_, hnz⟩
  · exact h
  · exact absurd rfl (hnz p)

theorem mink_inv_cons {x a b q p : Noun} (h : Mink lib gul [] x (C (C a b) q) (Tone.zero p)) :
    ∃ p1 p2, p = C p1 p2 ∧ Mink lib gul [] x (C a b) (Tone.zero p1) ∧
      Mink lib gul [] x q (Tone.zero p2) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨p1, h1, hn⟩ := tbind_zero_inv hn
  obtain ⟨p2, h2, hn⟩ := tbind_zero_inv hn
  cases hn
  exact ⟨p1, p2, rfl, ⟨n, h1⟩, ⟨n, h2⟩⟩

theorem mink_inv_n0 {x p : Noun} {ax : Nat} (h : Mink lib gul [] x (C (A 0) (A ax)) (Tone.zero p)) :
    slot? ax x = some p := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  revert hn
  cases slot? ax x <;> simp

theorem mink_inv_n1 {x k p : Noun} (h : Mink lib gul [] x (C (A 1) k) (Tone.zero p)) : p = k := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep, Option.some.injEq, Tone.zero.injEq] at hn
  exact hn.symm

theorem mink_inv_n2 {x b c p : Noun} (h : Mink lib gul [] x (n3 (A 2) b c) (Tone.zero p)) :
    ∃ y g, Mink lib gul [] x b (Tone.zero y) ∧ Mink lib gul [] x c (Tone.zero g) ∧
      Mink lib gul [] y g (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨y, h1, hn⟩ := tbind_zero_inv hn
  obtain ⟨g, h2, hn⟩ := tbind_zero_inv hn
  exact ⟨y, g, ⟨n, h1⟩, ⟨n, h2⟩, ⟨n, hn⟩⟩

theorem mink_inv_n6 {x b c d p : Noun} (h : Mink lib gul [] x (n4 (A 6) b c d) (Tone.zero p)) :
    Mink lib gul [] x c (Tone.zero p) ∨ Mink lib gul [] x d (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨t, _, hn⟩ := tbind_zero_inv hn
  match t, hn with
  | Noun.atom 0, hn => exact Or.inl ⟨n, hn⟩
  | Noun.atom 1, hn => exact Or.inr ⟨n, hn⟩
  | Noun.atom (_ + 2), hn => simp at hn
  | Noun.cell _ _, hn => simp at hn

theorem mink_inv_n7 {x b c p : Noun} (h : Mink lib gul [] x (n3 (A 7) b c) (Tone.zero p)) :
    ∃ y, Mink lib gul [] x b (Tone.zero y) ∧ Mink lib gul [] y c (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨y, h1, hn⟩ := tbind_zero_inv hn
  exact ⟨y, ⟨n, h1⟩, ⟨n, hn⟩⟩

theorem mink_inv_n8 {x b c p : Noun} (h : Mink lib gul [] x (n3 (A 8) b c) (Tone.zero p)) :
    ∃ y, Mink lib gul [] x b (Tone.zero y) ∧ Mink lib gul [] (C y x) c (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨y, h1, hn⟩ := tbind_zero_inv hn
  exact ⟨y, ⟨n, h1⟩, ⟨n, hn⟩⟩

theorem mink_inv_n9 {x c p : Noun} {ax : Nat}
    (h : Mink lib gul [] x (n3 (A 9) (A ax) c) (Tone.zero p)) :
    ∃ core arm, Mink lib gul [] x c (Tone.zero core) ∧ slot? ax core = some arm ∧
      Mink lib gul [] core arm (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨core, h1, hn⟩ := tbind_zero_inv hn
  revert hn
  cases hs : slot? ax core with
  | none => simp
  | some arm => intro hn; exact ⟨core, arm, ⟨n, h1⟩, hs, ⟨n, hn⟩⟩

theorem mink_inv_n10 {x v t p : Noun} {ax : Nat}
    (h : Mink lib gul [] x (n3 (A 10) (n2 (A ax) v) t) (Tone.zero p)) :
    ∃ tg vv, Mink lib gul [] x t (Tone.zero tg) ∧ Mink lib gul [] x v (Tone.zero vv) ∧
      edit? ax vv tg = some p := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  split at hn
  · simp at hn
  · obtain ⟨tg, h1, hn⟩ := tbind_zero_inv hn
    obtain ⟨vv, h2, hn⟩ := tbind_zero_inv hn
    revert hn
    cases he : edit? ax vv tg with
    | none => simp
    | some r => simp only [Option.some.injEq, Tone.zero.injEq]; intro hr; subst hr
                exact ⟨tg, vv, ⟨n, h1⟩, ⟨n, h2⟩, he⟩

theorem mink_inv_n11s {x q p : Noun} {tag : Nat}
    (h : Mink lib gul [] x (n3 (A 11) (A tag) q) (Tone.zero p)) : Mink lib gul [] x q (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ h
  simp only [minkStep] at hn
  obtain ⟨y, h1, hn⟩ := tbind_zero_inv hn
  cases hn
  exact ⟨n, h1⟩

theorem mink_inv_n11d {x h f p : Noun} {tag : Nat}
    (hm : Mink lib gul [] x (n3 (A 11) (C (A tag) h) f) (Tone.zero p)) :
    (∃ c, Mink lib gul [] x h (Tone.zero c)) ∧ Mink lib gul [] x f (Tone.zero p) := by
  obtain ⟨n, hn⟩ := mink_succ hm
  simp only [minkStep] at hn
  obtain ⟨c, h1, hn⟩ := tbind_zero_inv hn
  obtain ⟨y, h2, hn⟩ := tbind_zero_inv hn
  cases hn
  exact ⟨⟨c, n, h1⟩, Mink.nil h2⟩

/-! ## What `+mink` returns, put together -/

theorem minkF_lift {n m : Nat} {t : Trace} {x f : Noun} {r : Tone} (hle : n ≤ m)
    (h : minkF lib gul n t x f = some r) : minkF lib gul m t x f = some r :=
  minkF_le lib gul hle t x f r h

theorem mink_mk_cons {x a b q p1 p2 : Noun} (h1 : Mink lib gul [] x (C a b) (Tone.zero p1))
    (h2 : Mink lib gul [] x q (Tone.zero p2)) : Mink lib gul [] x (C (C a b) q) (Tone.zero (C p1 p2)) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero, minkF_lift (Nat.le_max_right _ _) e2, tbind_zero]

theorem mink_mk_n2 {x b c y g p : Noun} (h1 : Mink lib gul [] x b (Tone.zero y))
    (h2 : Mink lib gul [] x c (Tone.zero g)) (h3 : Mink lib gul [] y g (Tone.zero p)) :
    Mink lib gul [] x (n3 (A 2) b c) (Tone.zero p) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  obtain ⟨n3, e3⟩ := h3
  refine ⟨max n1 (max n2 n3) + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (by omega) e1, tbind_zero, minkF_lift (by omega) e2, tbind_zero]
  exact minkF_lift (by omega) e3

theorem mink_mk_n1 (x k : Noun) : Mink lib gul [] x (C (A 1) k) (Tone.zero k) := ⟨1, rfl⟩

theorem mink_mk_n0 {x p : Noun} {ax : Nat} (h : slot? ax x = some p) :
    Mink lib gul [] x (C (A 0) (A ax)) (Tone.zero p) :=
  ⟨1, by rw [minkF_succ_eq]; simp only [minkStep, h]⟩

theorem mink_mk_n11s {x q p : Noun} (tag : Nat) (h : Mink lib gul [] x q (Tone.zero p)) :
    Mink lib gul [] x (n3 (A 11) (A tag) q) (Tone.zero p) := by
  obtain ⟨n, e⟩ := h
  exact ⟨n + 1, by rw [minkF_succ_eq]; simp only [minkStep, e, tbind_zero]⟩

theorem mink_mk_n11d {x h f c p : Noun} (tag : Nat) (h1 : Mink lib gul [] x h (Tone.zero c))
    (h2 : Mink lib gul [] x f (Tone.zero p)) :
    Mink lib gul [] x (n3 (A 11) (C (A tag) h) f) (Tone.zero p) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_lift (Nat.le_max_left _ _) e1, tbind_zero,
    mink_t_of_nil_zero _ (minkF_lift (Nat.le_max_right _ _) e2), tbind_zero]

/-- `[2 [0 1] 1 f]` returns what `f` returns on the same subject. -/
theorem mink_self_call {x f p : Noun} :
    Mink lib gul [] x (n3 (A 2) (slot 1) (quote f)) (Tone.zero p) ↔ Mink lib gul [] x f (Tone.zero p) := by
  constructor
  · intro h
    obtain ⟨y, g, h1, h2, h3⟩ := mink_inv_n2 h
    have hy := mink_inv_n0 h1
    have hg := mink_inv_n1 h2
    simp only [slot?_one, Option.some.injEq] at hy
    subst hy; subst hg
    exact h3
  · intro ⟨n, e⟩
    refine ⟨n + 2, ?_⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [show minkF lib gul (n + 1) [] x (slot 1) = some (Tone.zero x) by
          rw [minkF_succ_eq]; simp [minkStep],
        tbind_zero, show minkF lib gul (n + 1) [] x (quote f) = some (Tone.zero f) from rfl, tbind_zero]
    exact minkF_lift (Nat.le_succ n) e

/-- `[11 [%memo h] f]`, where `h` returns: what `f` returns. -/
theorem mink_memo_iff {x h f p : Noun} (hh : ∃ c, Mink lib gul [] x h (Tone.zero c)) :
    Mink lib gul [] x (n3 (A 11) (C (A Tag.memo) h) f) (Tone.zero p) ↔
      Mink lib gul [] x (n3 (A 2) (slot 1) (quote f)) (Tone.zero p) := by
  rw [mink_self_call]
  constructor
  · intro hm; exact (mink_inv_n11d hm).2
  · intro hf; obtain ⟨c, hc⟩ := hh; exact mink_mk_n11d _ hc hf

end MinkParts

/-! ## Socks that know all -/

/-- A cape that knows nothing never pulls to `&`. -/
theorem pullLoop_isNo_ne : ∀ (axe : Nat) (c : Cape) (d m : Noun), c.isNo = true →
    So.pullLoop c d axe ≠ Sock.mk Cape.yes m := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d m hc
  rw [So.pullLoop.eq_def]
  split
  · intro h; cases h; simp [Cape.isNo] at hc
  · rename_i hax
    have hlt := mas_lt axe (by omega)
    by_cases hcn : c = Cape.no
    · simp only [hcn, if_true]; intro h; cases h
    · simp only [hcn, if_false]
      cases d with
      | atom _ => intro h; cases h
      | cell dh dt =>
        cases c with
        | yes => simp [Cape.isNo] at hc
        | no => exact absurd rfl hcn
        | cell ch ct =>
          simp only [Cape.isNo, Bool.and_eq_true] at hc
          simp only
          split
          · exact ih _ hlt ch dh m hc.1
          · exact ih _ hlt ct dt m hc.2

/-- A sock pulled to a fully known `&` at an axis: the axis is in every noun
of the sock, and holds the data there. -/
theorem pullLoop_yes : ∀ (axe : Nat) (c : Cape) (d n m : Noun), 1 ≤ axe →
    FitsCape c d n → So.pullLoop c d axe = Sock.mk Cape.yes m → slot? axe n = some m := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d n m h1 hf hp
  rw [So.pullLoop.eq_def] at hp
  split at hp
  · have : axe = 1 := by omega
    subst this
    cases hp
    simp only [FitsCape] at hf
    subst hf
    simp
  · rename_i hax
    have h2 : 2 ≤ axe := by omega
    have hlt := mas_lt axe h2
    have hpos := mas_pos axe h2
    split at hp
    · cases hp
    · rename_i hcno
      split at hp
      · cases hp
      · rename_i dh dt
        rw [slot?_cap h2]
        split at hp
        · rename_i ch ct
          simp only [FitsCape] at hf
          rcases hf with hno | ⟨dh', dt', nh, nt, hd, hn, hh, ht⟩
          · simp only [Bool.and_eq_true] at hno
            split at hp
            · exact absurd hp (pullLoop_isNo_ne _ _ _ _ hno.1)
            · exact absurd hp (pullLoop_isNo_ne _ _ _ _ hno.2)
          · cases hd; subst hn
            simp only
            split at hp
            · rename_i hc; simp only [hc, if_true]; exact ih _ hlt _ _ _ _ hpos hh hp
            · rename_i hc; simp only [hc, if_false]; exact ih _ hlt _ _ _ _ hpos ht hp
        · rename_i hcc
          cases c with
          | no => exact absurd rfl hcno
          | cell ch ct => exact absurd rfl (hcc ch ct)
          | yes =>
            simp only [FitsCape] at hf
            subst hf
            simp only
            split at hp
            · rename_i hc; simp only [hc, if_true]; exact ih _ hlt Cape.yes dh dh m hpos rfl hp
            · rename_i hc; simp only [hc, if_false]; exact ih _ hlt Cape.yes dt dt m hpos rfl hp

theorem pull_yes {s : Sock} {axe : Nat} {n m : Noun} (hf : Fits s n)
    (hp : So.pull s axe = some (Sock.mk Cape.yes m)) : slot? axe n = some m := by
  unfold So.pull at hp
  split at hp
  · simp at hp
  · rename_i hax
    cases s with
    | void => exact absurd hf id
    | mk c d =>
      simp only [Option.some.injEq] at hp
      exact pullLoop_yes axe c d n m (by omega) hf hp

/-- A knit never knows a cell as `&`: the cons of two capes is a cell. -/
theorem knit_ne_yes (one two : Sock) (d : Noun) : So.knit one two ≠ Sock.mk Cape.yes d := by
  cases one with
  | void => cases two <;> simp [So.knit]
  | mk l d1 =>
    cases two with
    | void => simp [So.knit]
    | mk r d2 =>
      simp only [So.knit]
      split
      · intro h; cases h
      · intro h
        injection h with h1 _
        unfold Ca.con at h1
        split at h1 <;> cases h1

theorem fits_yes {d n : Noun} (h : Fits (Sock.mk Cape.yes d) n) : n = d := h

end SkaModel
end Formalization
