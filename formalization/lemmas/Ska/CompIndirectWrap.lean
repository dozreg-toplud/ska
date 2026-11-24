import lemmas.Ska.CompIndirectBwd

/-!
# The indirect call under `%memo` and constant `%6`

README Gaps 12.12 (sixteenth session).  The first call theorem
(`indirectTop_contract`) is stated on the formula `[2 b c]` with `Annot` of
`b` and `c`, not on every `Annot` of the nomm `[2 p q]` with no callee.  The
constructors of `Annot` that give a nomm `Nomm.n2 p q none` are:

* `Annot.indirect`, on the formula `[2 b c]`;
* `Annot.bare` and `Annot.bareLit`, on a `%bare` formula `f`, with `q` the
  literal `[1 f]` (`bareLitQ q`);
* the wrappers `Annot.memo` (`[11 [%memo h] f]` with the nomm of
  `[2 [0 1] [1 f]]`), `Annot.six0` and `Annot.six1` (`[6 b c d]` with the
  nomm of `c` or `d`), whose nomm is the nomm of their premise.

Every other constructor gives a nomm whose head is not `%2` (`cons`, `n0`,
`n1`, `n3` to `n7`, `n8`, `n8g`, `n8l`, `n9`, `n10`, `n11s`, `n11d`,
`mean`, `n12`, `crash`, `fold`, `inline`) or a `%2` with a callee
(`direct`): the proof of `minkN2_of_annot` checks this case by case
(`cases` on the equation of the nomms).

`MinkN2 lib P f p q` is what the proofs of the first call theorem use of
the formula: `+mink` on `f` runs the product formula of `q` on the product
subject of `p` with less fuel (forward), any run of it is one of `f`
(backward), and where `p` or `q` has no product `+mink` crashes with the
trace as it is.  `minkN2_of_annot` proves it for every `Annot` of
`[2 p q]` with pure parts and `bareLitQ q = false`, through the wrappers:
`%memo` and `%6` spend one step of fuel before the call, so the oracle's
bound `j < n` still covers it.  For example the formula
`[11 [%memo [1 0]] [2 [0 3] [0 2]]]` has the nomm `[2 [0 1] [1 [2 [0 3] [0 2]]]]`
through `Annot.memo`, and `[6 [1 0] [2 [0 3] [0 2]] [0 0]]` has the nomm of
`[2 [0 3] [0 2]]` through `Annot.six0`.

A `%bare` formula `f = [11 %bare g]` is excluded: its nomm `[2 [0 1] [1 f]]`
makes one `nok` of `f` itself, which `+mink` runs with all of its fuel.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The nomm `[1 f]` of a `%bare` formula `f`: the `q` of `Annot.bare` and
`Annot.bareLit`. -/
def bareLitQ : Nomm → Bool
  | Nomm.n1 f => isBare f
  | _ => false

/-- **What the first call theorem uses of the formula `f` whose nomm is
`[2 p q]`** (pure parts): forward, `+mink` on `f` with fuel `n` runs the
product of `q` on the product of `p` with fuel below `n`, or crashes with
the trace as it is where one of them has no product; backward, a run of
`+mink` on the two products is one on `f`, and the crash is one too. -/
structure MinkN2 (lib : Lib) (P : Noun → Prop) (f : Noun) (p q : Nomm) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    (∃ n' x y, n' < n ∧ pureEval p s = some x ∧ pureEval q s = some y ∧ minkF lib gul n' tm x y = some r) ∨
      (((pureEval p s).bind fun x => (pureEval q s).bind fun y => some (C x y)) = Option.none ∧ r = Tone.two tm)
  bwd : ∀ {s gul : Noun} {tm : Trace} {x y : Noun} {r : Tone}, P s → pureEval p s = some x →
    pureEval q s = some y → Mink lib gul tm x y r → Mink lib gul tm s f r
  crash : ∀ {s gul : Noun} {tm : Trace}, P s →
    ((pureEval p s).bind fun x => (pureEval q s).bind fun y => some (C x y)) = Option.none →
    Mink lib gul tm s f (Tone.two tm)

/-- `[2 b c]` itself (`Annot.indirect`). -/
theorem minkN2_indirect {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {b c : Noun} {p q : Nomm} (hp : p.pure = true) (hq : q.pure = true) (hAp : Annot lib code P b p)
    (hAq : Annot lib code P c q) : MinkN2 lib P (n3 (A 2) b c) p q where
  fwd := fun hs h => by
    rcases minkF_n2_pure hok hp hq hAp hAq hs h with ⟨n', x, y, rfl, ex, ey, hm⟩ | e
    · exact Or.inl ⟨n', x, y, Nat.lt_succ_self n', ex, ey, hm⟩
    · exact Or.inr e
  bwd := fun {s gul tm x y r} hs ex ey h => by
    have mp : Mink lib gul tm s b (pureTone tm p s) := (mink_pure hok hp hAp hs gul tm _).mpr rfl
    have mq : Mink lib gul tm s c (pureTone tm q s) := (mink_pure hok hq hAq hs gul tm _).mpr rfl
    rw [pureTone, ex] at mp
    rw [pureTone, ey] at mq
    exact mink_n2_of mp mq h
  crash := fun {s gul tm} hs e => by
    have mp : Mink lib gul tm s b (pureTone tm p s) := (mink_pure hok hp hAp hs gul tm _).mpr rfl
    have mq : Mink lib gul tm s c (pureTone tm q s) := (mink_pure hok hq hAq hs gul tm _).mpr rfl
    cases ex : pureEval p s with
    | none => rw [pureTone, ex] at mp; exact mink_n2_crash1 mp
    | some x =>
      rw [ex] at e
      rw [pureTone, ex] at mp
      cases ey : pureEval q s with
      | none => rw [pureTone, ey] at mq; exact mink_n2_crash2 mp mq
      | some y => rw [ey] at e; simp at e

/-! ## `%memo` -/

theorem minkF_call1 (lib : Lib) (gul : Noun) (k : Nat) (t : Trace) (s f : Noun) :
    minkF lib gul (k + 2) t s (n3 (A 2) (slot 1) (quote f)) = minkF lib gul (k + 1) t s f := by
  rw [minkF_succ_eq]; simp only [minkStep]
  rw [minkF_slot1', tbind_zero, show minkF lib gul (k + 1) t s (quote f) = some (Tone.zero f) from rfl,
    tbind_zero]

/-- `+mink` on `[2 [0 1] [1 f]]` is `+mink` on `f`. -/
theorem mink_call1 {lib : Lib} {gul : Noun} {t : Trace} {s f : Noun} {r : Tone} :
    Mink lib gul t s (n3 (A 2) (slot 1) (quote f)) r ↔ Mink lib gul t s f r := by
  constructor
  · rintro ⟨k, h⟩
    cases k with
    | zero => simp [minkF] at h
    | succ k =>
      cases k with
      | zero => simp [minkStep, minkF, tbind] at h
      | succ k => rw [minkF_call1] at h; exact ⟨_, h⟩
  · rintro ⟨k, h⟩
    cases k with
    | zero => simp [minkF] at h
    | succ k => exact ⟨k + 2, by rw [minkF_call1]; exact h⟩

theorem mink_memo_of {lib : Lib} {P : Noun → Prop} {h f : Noun}
    (hh : ∀ x gul, P x → ∃ c, Mink lib gul [] x h (Tone.zero c)) {s gul : Noun} {tm : Trace} {r : Tone}
    (hs : P s) (hf : Mink lib gul tm s f r) : Mink lib gul tm s (n3 (A 11) (C (A Tag.memo) h) f) r := by
  have hst : stopTag Tag.memo = false := by decide
  obtain ⟨c0, k0, e0⟩ := hh s gul hs
  obtain ⟨k1, e1⟩ := hf
  refine ⟨max k0 k1 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep, hst, Bool.false_eq_true, if_false]
  rw [minkF_le lib gul (Nat.le_max_left k0 k1) tm s h _ (mink_t_of_nil_zero tm e0), tbind_zero,
    minkF_le lib gul (Nat.le_max_right k0 k1) tm s f _ e1, tbind_zero_id]

/-- **Under `%memo`** (`Annot.memo`): the clue returns, and the body is the
call `[2 [0 1] [1 f]]`. -/
theorem minkN2_memo {lib : Lib} {P : Noun → Prop} {h f : Noun} {p q : Nomm}
    (hh : ∀ x gul, P x → ∃ c, Mink lib gul [] x h (Tone.zero c))
    (M : MinkN2 lib P (n3 (A 2) (slot 1) (quote f)) p q) :
    MinkN2 lib P (n3 (A 11) (C (A Tag.memo) h) f) p q where
  fwd := fun {s gul n tm r} hs hm => by
    have hst : stopTag Tag.memo = false := by decide
    cases n with
    | zero => simp [minkF] at hm
    | succ n0 =>
      rw [minkF_succ_eq] at hm
      simp only [minkStep, hst, Bool.false_eq_true, if_false] at hm
      have hf : minkF lib gul n0 tm s f = some r := by
        rcases tbind_eq_some hm with ⟨_, _, h1⟩ | ⟨hh', hnz⟩
        · rw [tbind_zero_id] at h1; exact h1
        · obtain ⟨c0, hc0⟩ := hh s gul hs
          exact absurd (mink_det_zero hc0 hh') (hnz c0)
      obtain ⟨n1, rfl⟩ : ∃ n1, n0 = n1 + 1 := by
        cases n0 with
        | zero => simp [minkF] at hf
        | succ n1 => exact ⟨n1, rfl⟩
      have hrun : minkF lib gul (n1 + 2) tm s (n3 (A 2) (slot 1) (quote f)) = some r := by
        rw [minkF_call1]; exact hf
      rcases M.fwd hs hrun with ⟨n', x, y, hlt, ex, ey, h'⟩ | e
      · exact Or.inl ⟨n', x, y, by omega, ex, ey, h'⟩
      · exact Or.inr e
  bwd := fun hs ex ey hm => mink_memo_of hh hs (mink_call1.mp (M.bwd hs ex ey hm))
  crash := fun hs e => mink_memo_of hh hs (mink_call1.mp (M.crash hs e))

/-! ## Constant `%6` -/

theorem mink_six_of {lib : Lib} {P : Noun → Prop} {b c d e : Noun} {v : Nat}
    (hb : ∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A v)))
    (hce : (v = 0 ∧ e = c) ∨ (v = 1 ∧ e = d)) {s gul : Noun} {tm : Trace} {r : Tone}
    (hs : P s) (he : Mink lib gul tm s e r) : Mink lib gul tm s (n4 (A 6) b c d) r := by
  obtain ⟨k0, e0⟩ := hb s gul hs
  obtain ⟨k1, e1⟩ := he
  refine ⟨max k0 k1 + 1, ?_⟩
  rw [minkF_succ_eq]; simp only [minkStep]
  rw [minkF_le lib gul (Nat.le_max_left k0 k1) tm s b _ (mink_t_of_nil_zero tm e0), tbind_zero]
  have e1' := minkF_le lib gul (Nat.le_max_right k0 k1) tm s e _ e1
  rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact e1'
  · exact e1'

theorem minkN2_six {lib : Lib} {P : Noun → Prop} {b c d e : Noun} {v : Nat} {p q : Nomm}
    (hb : ∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A v)))
    (hce : (v = 0 ∧ e = c) ∨ (v = 1 ∧ e = d)) (M : MinkN2 lib P e p q) :
    MinkN2 lib P (n4 (A 6) b c d) p q where
  fwd := fun {s gul n tm r} hs hm => by
    cases n with
    | zero => simp [minkF] at hm
    | succ n0 =>
      rw [minkF_succ_eq] at hm
      simp only [minkStep] at hm
      rcases tbind_eq_some hm with ⟨w, hw, h1⟩ | ⟨hw, hnz⟩
      · cases mink_det_zero (hb s gul hs) hw
        have h1' : minkF lib gul n0 tm s e = some r := by
          rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1
          · exact h1
        rcases M.fwd hs h1' with ⟨n', x, y, hlt, ex, ey, h'⟩ | e
        · exact Or.inl ⟨n', x, y, by omega, ex, ey, h'⟩
        · exact Or.inr e
      · exact absurd (mink_det_zero (hb s gul hs) hw) (hnz _)
  bwd := fun hs ex ey hm => mink_six_of hb hce hs (M.bwd hs ex ey hm)
  crash := fun hs e => mink_six_of hb hce hs (M.crash hs e)

/-! ## Every `Annot` of `[2 p q]` but the bare ones -/

/-- **The inversion of `Annot` on the indirect call**: every `Annot` of the
nomm `[2 p q]` with no callee, pure parts and `q` not the literal of a
`%bare` formula meets `MinkN2` (through `Annot.indirect` under the wrappers
`Annot.memo`, `Annot.six0`, `Annot.six1`; no other constructor gives this
nomm). -/
theorem minkN2_of_annot {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    ∀ {p q : Nomm}, nm = Nomm.n2 p q Option.none → p.pure = true → q.pure = true → bareLitQ q = false →
      MinkN2 lib P f p q := by
  induction hA with
  | indirect hb hc _ _ =>
    intro p q e hp hq _
    cases e
    exact minkN2_indirect hok hp hq hb hc
  | bare hf =>
    intro p q e _ _ hb
    cases e
    simp [bareLitQ, hf] at hb
  | bareLit hf _ =>
    intro p q e _ _ hb
    cases e
    simp [bareLitQ, hf] at hb
  | memo hh _ ih =>
    intro p q e hp hq hb
    exact minkN2_memo hh (ih e hp hq hb)
  | six0 hb _ ih =>
    intro p q e hp hq hq'
    exact minkN2_six hb (Or.inl ⟨rfl, rfl⟩) (ih e hp hq hq')
  | six1 hb _ ih =>
    intro p q e hp hq hq'
    exact minkN2_six hb (Or.inr ⟨rfl, rfl⟩) (ih e hp hq hq')
  | cons => intro _ _ e; cases e
  | n0 => intro _ _ e; cases e
  | n1 => intro _ _ e; cases e
  | direct => intro _ _ e; cases e
  | inline => intro _ _ e; cases e
  | n3 => intro _ _ e; cases e
  | n4 => intro _ _ e; cases e
  | n5 => intro _ _ e; cases e
  | n6 => intro _ _ e; cases e
  | n7 => intro _ _ e; cases e
  | n8 => intro _ _ e; cases e
  | n9 => intro _ _ e; cases e
  | n10 => intro _ _ e; cases e
  | n11s => intro _ _ e; cases e
  | n11d => intro _ _ e; cases e
  | mean => intro _ _ e; cases e
  | n12 => intro _ _ e; cases e
  | crash => intro _ _ e; cases e
  | fold => intro _ _ e; cases e
  | n8g => intro _ _ e; cases e
  | n8l => intro _ _ e; cases e

end Comp
end SkaModel
end Formalization
