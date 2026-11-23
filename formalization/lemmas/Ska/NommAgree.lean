import lemmas.Ska.NommSem
import lemmas.Ska.MinkTrace

/-!
# A nomm that satisfies the invariant runs as `+mink` runs its formula

`nomm_fwd`: if `Annot lib code P f n`, the table satisfies `CodeOK`, and `x`
is in `P`, then whatever `+mink` returns on `[x f]`, `nommF` returns on `n`
once its fuel is large enough.  `nomm_bwd` is the converse.  Both go by
induction on the fuel and by cases on `Annot`; a direct call is the induction
hypothesis on the callee's nomm, whose annotation `CodeOK` gives.

`Ev F r`: the family `F` of fuelled runs returns `r` from some fuel on.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Eventually -/

def Ev (F : Nat → Option Tone) (r : Tone) : Prop := ∃ m0, ∀ m, m0 ≤ m → F m = some r

theorem Ev.const (r : Tone) : Ev (fun _ => some r) r := ⟨0, fun _ _ => rfl⟩

theorem Ev.succ {F : Nat → Option Tone} {r : Tone} (h : Ev (fun m => F (m + 1)) r) : Ev F r := by
  obtain ⟨m0, h⟩ := h
  refine ⟨m0 + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact h k (by omega)

theorem Ev.exists {F : Nat → Option Tone} {r : Tone} (h : Ev F r) : ∃ m, F m = some r := by
  obtain ⟨m0, h⟩ := h
  exact ⟨m0, h m0 (Nat.le_refl _)⟩

theorem ev_tbind {x : Option Tone} {k : Noun → Option Tone} {F : Nat → Option Tone}
    {K : Noun → Nat → Option Tone} {r : Tone}
    (hx : ∀ r', x = some r' → Ev F r')
    (hk : ∀ p r', x = some (Tone.zero p) → k p = some r' → Ev (K p) r')
    (h : tbind x k = some r) : Ev (fun m => tbind (F m) (fun p => K p m)) r := by
  rcases tbind_eq_some h with ⟨p, hp, hkp⟩ | ⟨hx', hnz⟩
  · obtain ⟨m1, h1⟩ := hx _ hp
    obtain ⟨m2, h2⟩ := hk p r hp hkp
    exact ⟨max m1 m2, fun m hm => by show tbind (F m) _ = _; rw [h1 m (by omega)]; exact h2 m (by omega)⟩
  · obtain ⟨m1, h1⟩ := hx _ hx'
    refine ⟨m1, fun m hm => ?_⟩
    show tbind (F m) _ = _
    rw [h1 m hm]
    cases r with
    | zero p => exact absurd rfl (hnz p)
    | one _ => rfl
    | two _ => rfl

theorem Ev.minkF {lib : Lib} {gul : Noun} {n : Nat} {t : Trace} {s f : Noun} {r : Tone}
    (h : minkF lib gul n t s f = some r) : Ev (fun m => minkF lib gul m t s f) r :=
  ⟨n, fun _ hm => minkF_le lib gul hm _ _ _ _ h⟩

theorem mink_nil_of_zero {lib : Lib} {gul : Noun} {n : Nat} {t : Trace} {s f y : Noun}
    (h : minkF lib gul n t s f = some (Tone.zero y)) : minkF lib gul n [] s f = some (Tone.zero y) := by
  rw [minkF_trace] at h
  obtain ⟨r0, h0, he⟩ := Option.map_eq_some_iff.mp h
  cases r0 <;> simp [Tone.app] at he
  subst he; exact h0

theorem mink_t_of_nil_zero {lib : Lib} {gul : Noun} {n : Nat} (t : Trace) {s f y : Noun}
    (h : minkF lib gul n [] s f = some (Tone.zero y)) : minkF lib gul n t s f = some (Tone.zero y) := by
  rw [minkF_trace, h]; rfl

/-! ## Fuel for nomm -/

theorem nommStep_mono (lib : Lib) (gul : Noun) (code : Bell → Option Nomm)
    {go go' : Trace → Noun → Nomm → Option Tone} {mk mk' : Trace → Noun → Noun → Option Tone}
    (hg : ∀ t s n, OptLe (go t s n) (go' t s n)) (hm : ∀ t s f, OptLe (mk t s f) (mk' t s f))
    (t : Trace) (s : Noun) (nm : Nomm) :
    OptLe (nommStep lib gul code go mk t s nm) (nommStep lib gul code go' mk' t s nm) := by
  cases nm with
  | cons p q => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n0 _ => exact OptLe.refl _
  | n1 _ => exact OptLe.refl _
  | n2 p q info =>
    cases info with
    | none => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => hm _ _ _
    | some i =>
      exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ =>
        OptLe.bind (OptLe.refl _) fun _ => hg _ _ _
  | n3 p => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n4 p => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n5 p q => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n6 p q r =>
    refine OptLe.tbind (hg _ _ _) fun v => ?_
    split
    · exact hg _ _ _
    · exact hg _ _ _
    · exact OptLe.refl _
  | n7 p q => exact OptLe.tbind (hg _ _ _) fun _ => hg _ _ _
  | n10 a v q =>
    simp only [nommStep]
    split
    · exact OptLe.refl _
    · exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n11s _ q _ => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n11d _ h q _ => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | n12 p q => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _
  | mean p _ q _ _ => exact OptLe.tbind (hg _ _ _) fun _ => OptLe.tbind (hg _ _ _) fun _ => OptLe.refl _

theorem nommF_succ_le (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) :
    ∀ (n : Nat) (t : Trace) (s : Noun) (nm : Nomm),
      OptLe (nommF lib gul code n t s nm) (nommF lib gul code (n + 1) t s nm)
  | 0, _, _, _ => fun _ h => by simp [nommF] at h
  | n + 1, t, s, nm => nommStep_mono lib gul code (fun t s nm => nommF_succ_le lib gul code n t s nm)
      (fun t s f => minkF_succ lib gul n t s f) t s nm

theorem nommF_le (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) {n m : Nat} (hle : n ≤ m)
    (t : Trace) (s : Noun) (nm : Nomm) :
    OptLe (nommF lib gul code n t s nm) (nommF lib gul code m t s nm) := by
  induction hle with
  | refl => exact OptLe.refl _
  | step _ ih => exact fun r h => nommF_succ_le lib gul code _ t s nm r (ih r h)

theorem Ev.nommF {lib : Lib} {gul : Noun} {code : Bell → Option Nomm} {n : Nat} {t : Trace}
    {s : Noun} {nm : Nomm} {r : Tone} (h : nommF lib gul code n t s nm = some r) :
    Ev (fun m => nommF lib gul code m t s nm) r :=
  ⟨n, fun _ hm => nommF_le lib gul code hm _ _ _ _ h⟩

theorem nommF_succ (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) (n : Nat) :
    nommF lib gul code (n + 1) = nommStep lib gul code (nommF lib gul code n) (minkF lib gul n) :=
  rfl

/-! ## Helpers -/

theorem minkF_slot1' (lib : Lib) (gul : Noun) (k : Nat) (t : Trace) (s : Noun) :
    minkF lib gul (k + 1) t s (slot 1) = some (Tone.zero s) := by
  simp [minkF_succ_eq, minkStep]

theorem minkF_slot (lib : Lib) (gul : Noun) (k : Nat) (t : Trace) (s : Noun) (axis : Nat) :
    minkF lib gul (k + 1) t s (slot axis) =
      (match slot? axis s with | none => some (Tone.two t) | some p => some (Tone.zero p)) := by
  rw [minkF_succ_eq]; simp only [minkStep]; cases slot? axis s <;> rfl

theorem minkF_invoke (lib : Lib) (gul : Noun) (k : Nat) (t : Trace) (core : Noun) (axis : Nat) :
    minkF lib gul (k + 2) t core (n3 (A 2) (slot 1) (slot axis)) =
      (match slot? axis core with
        | none => some (Tone.two t)
        | some arm => minkF lib gul (k + 1) t core arm) := by
  rw [minkF_succ_eq]; simp only [minkStep]
  rw [minkF_slot1', tbind_zero, minkF_slot]
  cases slot? axis core <;> rfl

theorem nommF_n0 (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) (m : Nat) (t : Trace)
    (s : Noun) (axis : Nat) :
    nommF lib gul code (m + 1) t s (Nomm.n0 axis) =
      (match slot? axis s with | none => some (Tone.two t) | some p => some (Tone.zero p)) := by
  simp only [nommF_succ, nommStep]; cases slot? axis s <;> rfl

theorem img_of {lib : Lib} {P : Noun → Prop} {x b y gul : Noun} {n : Nat} {t : Trace}
    (hP : P x) (h : minkF lib gul n t x b = some (Tone.zero y)) : Img lib P b y :=
  ⟨x, gul, hP, n, mink_nil_of_zero h⟩

theorem mink_det_zero {lib : Lib} {gul : Noun} {n : Nat} {t : Trace} {x c g : Noun} {r : Tone}
    (htot : Mink lib gul [] x c (Tone.zero g)) (h : minkF lib gul n t x c = some r) :
    r = Tone.zero g := by
  obtain ⟨n0, h0⟩ := htot
  exact minkF_det lib gul h (mink_t_of_nil_zero t h0)

theorem tbind_nonzero' {x : Tone} (h : ∀ p, x ≠ Tone.zero p) (k : Noun → Option Tone) :
    tbind (some x) k = some x := by
  cases x with
  | zero p => exact absurd rfl (h p)
  | one _ => rfl
  | two _ => rfl

theorem nommF_cons_n0 (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) (k : Nat) (t : Trace)
    (x : Noun) (p : Nomm) :
    nommF lib gul code (k + 2) t x (Nomm.cons p (Nomm.n0 1)) =
      tbind (nommF lib gul code (k + 1) t x p) (fun a => some (Tone.zero (C a x))) := by
  rw [nommF_succ]
  simp only [nommStep]
  rw [nommF_n0]
  simp

/-! ## The forward direction -/

/-- **What `+mink` returns on a formula, its nomm returns.** -/
theorem nomm_fwd (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) (hc : CodeOK lib code) :
    ∀ n P f nm t x r, Annot lib code P f nm → P x → minkF lib gul n t x f = some r →
      Ev (fun m => nommF lib gul code m t x nm) r := by
  intro n
  induction n with
  | zero => intro P f nm t x r _ _ h; simp [minkF] at h
  | succ n ih =>
  intro P f nm t x r hA hP h
  have IH : ∀ {P f nm t x r}, Annot lib code P f nm → P x → minkF lib gul n t x f = some r →
      Ev (fun m => nommF lib gul code m t x nm) r := fun hA hP h => ih _ _ _ _ _ _ hA hP h
  have h0 := h
  rw [minkF_succ_eq] at h
  apply Ev.succ
  simp only [nommF_succ]
  cases hA with
  | cons hA1 hA2 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun _ _ _ h3 => by cases h3; exact Ev.const _) h1) h
  | @n0 _ axis =>
    simp only [minkStep] at h
    refine ⟨0, fun _ _ => ?_⟩
    simp only [nommStep]
    cases hs : slot? axis x <;> simp only [hs] at h ⊢ <;> exact h
  | n1 =>
    simp only [minkStep] at h
    exact ⟨0, fun _ _ => h⟩
  | indirect hA1 hA2 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun _ _ _ h3 => Ev.minkF h3) h1) h
  | direct hA1 hA2 hcode hy hg =>
    rename_i b c p q bl k nb
    simp only [minkStep] at h
    simp only [nommStep]
    refine ev_tbind (fun _ h1 => IH hA1 hP h1) (fun y _ hxy h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun g r2 hxg h2 => ?_) h1) h
    have hgf := hg x gul g hP ⟨n, mink_nil_of_zero hxg⟩
    have hfit := hy x gul y hP ⟨n, mink_nil_of_zero hxy⟩
    subst hgf
    simp only [hcode, Option.bind_some]
    exact IH (hc bl nb hcode) hfit h2
  | inline hA1 htot hA2 =>
    rename_i b c g p q
    simp only [minkStep] at h
    simp only [nommStep]
    refine ev_tbind (fun _ h1 => IH hA1 hP h1) (fun y r1 hxy h1 => ?_) h
    rcases tbind_eq_some h1 with ⟨g', hg', h2⟩ | ⟨hrc, hnz⟩
    · have := mink_det_zero (htot x gul hP) hg'
      cases this
      exact IH hA2 (img_of hP hxy) h2
    · exact absurd (mink_det_zero (htot x gul hP) hrc) (hnz g)
  | n3 hA1 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => by cases h1; exact Ev.const _) h
  | n4 hA1 =>
    simp only [minkStep] at h
    simp only [nommStep]
    refine ev_tbind (fun _ h1 => IH hA1 hP h1) (fun v _ _ h1 => ⟨0, fun _ _ => ?_⟩) h
    cases v <;> exact h1
  | n5 hA1 hA2 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun _ _ _ h3 => by cases h3; exact Ev.const _) h1) h
  | n6 hA1 hA2 hA3 =>
    simp only [minkStep] at h
    simp only [nommStep]
    refine ev_tbind (fun _ h1 => IH hA1 hP h1) (fun v _ _ h1 => ?_) h
    match v, h1 with
    | Noun.cell _ _, h1 => exact ⟨0, fun _ _ => h1⟩
    | Noun.atom 0, h1 => exact IH hA2 hP h1
    | Noun.atom 1, h1 => exact IH hA3 hP h1
    | Noun.atom (k + 2), h1 => exact ⟨0, fun _ _ => h1⟩
  | n7 hA1 hA2 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ hxy h1 => IH hA2 (img_of hP hxy) h1) h
  | n8 hA1 hA2 =>
    rename_i b c p q
    simp only [minkStep] at h
    simp only [nommStep]
    rcases tbind_eq_some h with ⟨y, hy, h1⟩ | ⟨hb, hnz⟩
    · obtain ⟨m1, e1⟩ := IH hA1 hP hy
      obtain ⟨m2, e2⟩ := IH hA2 ⟨x, y, gul, hP, ⟨n, mink_nil_of_zero hy⟩, rfl⟩ h1
      refine ⟨m1 + m2 + 2, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      show tbind _ _ = _
      have e1' : nommF lib gul code (k + 1) t x p = some (Tone.zero y) := e1 (k + 1) (by omega)
      rw [nommF_cons_n0, e1', tbind_zero, tbind_zero]
      exact e2 (k + 2) (by omega)
    · obtain ⟨m1, e1⟩ := IH hA1 hP hb
      refine ⟨m1 + 2, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      show tbind _ _ = _
      have e1' : nommF lib gul code (k + 1) t x p = some r := e1 (k + 1) (by omega)
      rw [nommF_cons_n0, e1', tbind_nonzero' hnz, tbind_nonzero' hnz]
  | n9 hA1 hA2 =>
    rename_i axis c q rr
    simp only [minkStep] at h
    simp only [nommStep]
    refine ev_tbind (fun _ h1 => IH hA1 hP h1) (fun core r1 hxc h1 => ?_) h
    have hQ : Img lib P c core := img_of hP hxc
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
      cases n with
      | zero => simp [minkF] at hxc
      | succ n' => exact ⟨n', rfl⟩
    have hrun : minkF lib gul (n' + 2) t core (n3 (A 2) (slot 1) (slot axis)) = some r1 := by
      rw [minkF_invoke]
      cases hs : slot? axis core <;> simp only [hs] at h1 ⊢ <;> exact h1
    have hrun' := hrun
    rw [minkF_succ_eq] at hrun'
    simp only [minkStep] at hrun'
    apply Ev.succ
    simp only [nommF_succ]
    cases hA2 with
    | indirect hp hq =>
      simp only [nommStep]
      exact ev_tbind (fun _ e1 => IH hp hQ e1) (fun _ _ _ e1 => ev_tbind (fun _ e2 => IH hq hQ e2)
        (fun _ _ _ e3 => Ev.minkF e3) e1) hrun'
    | direct hp hq hcode hy hg =>
      rename_i p' q' bl k nb
      simp only [nommStep]
      refine ev_tbind (fun _ e1 => IH hp hQ e1) (fun y _ hxy e1 => ev_tbind (fun _ e2 => IH hq hQ e2)
        (fun g r2 hxg e2 => ?_) e1) hrun'
      have hgf := hg core gul g hQ ⟨_, mink_nil_of_zero hxg⟩
      have hfit := hy core gul y hQ ⟨_, mink_nil_of_zero hxy⟩
      subst hgf
      simp only [hcode, Option.bind_some]
      exact IH (hc bl nb hcode) hfit e2
    | inline hp htot hq =>
      rename_i g p' q'
      simp only [nommStep]
      refine ev_tbind (fun _ e1 => IH hp hQ e1) (fun y r2 hxy e1 => ?_) hrun'
      rcases tbind_eq_some e1 with ⟨g', hg', e2⟩ | ⟨hrc, hnz⟩
      · have := mink_det_zero (htot core gul hQ) hg'
        cases this
        exact IH hq (img_of hQ hxy) e2
      · exact absurd (mink_det_zero (htot core gul hQ) hrc) (hnz g)
    | crash hcr =>
      obtain ⟨k, hk⟩ := hcr gul t core
      have := minkF_det lib gul hrun hk
      subst this
      refine ⟨0, fun _ _ => ?_⟩
      simp only [nommStep]
      rfl
  | n10 hax hA1 hA2 =>
    simp only [minkStep, hax, if_false] at h
    simp only [nommStep, hax, if_false]
    refine ev_tbind (fun _ h1 => IH hA2 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA1 hP h2)
      (fun _ _ _ h3 => ⟨0, fun _ _ => ?_⟩) h1) h
    split at h3 <;> simp_all
  | n11s hA1 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => by cases h1; exact Ev.const _) h
  | n11d hA1 hA2 =>
    simp only [minkStep] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun _ _ _ h3 => by cases h3; exact Ev.const _) h1) h
  | mean hA1 hA2 =>
    have hst : stopTag Tag.mean = true := by decide
    simp only [minkStep, hst, if_true] at h
    simp only [nommStep]
    exact ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun _ _ _ h3 => by cases h3; exact Ev.const _) h1) h
  | n12 hA1 hA2 =>
    simp only [minkStep] at h
    simp only [nommStep]
    refine ev_tbind (fun _ h1 => IH hA1 hP h1) (fun _ _ _ h1 => ev_tbind (fun _ h2 => IH hA2 hP h2)
      (fun _ _ _ h3 => ⟨0, fun _ _ => ?_⟩) h1) h
    split at h3
    · simp_all
    · rw [if_neg (by assumption)]
      cases hsl : lib.slam gul _ <;> simp only [hsl, Option.bind_none, Option.bind_some] at h3 ⊢
      · exact h3
      · rename_i res
        cases hd : scryDecode res <;> simp only [hd, Option.bind_none, Option.bind_some] at h3 ⊢
        · exact h3
        · rename_i d; cases d <;> exact h3
  | crash hcr =>
    obtain ⟨k, hk⟩ := hcr gul t x
    have := minkF_det lib gul h0 hk
    subst this
    refine ⟨0, fun _ _ => ?_⟩
    simp only [nommStep]
    rfl

end SkaModel
end Formalization
