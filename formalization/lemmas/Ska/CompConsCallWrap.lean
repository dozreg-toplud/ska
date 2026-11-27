import lemmas.Ska.CompConsCallTopB

/-!
# The cons with the call in its head on every `Annot`

README Gaps 12.16 (nineteenth session).  `RawMono` quantifies over every
`Annot` of the bell's formula by the nomm.  The constructors that give the
nomm `[[2 b c] d]` are `Annot.cons` and the wrappers `Annot.memo`,
`Annot.six0`, `Annot.six1` (whose nomm is their premise's).  Both halves of
the contract go through a wrapper whose `+mink` runs the inner formula with
no more fuel and returns what it returns (`WrapRel`).

* `WrapRel`, `wrapRel_six`, `wrapRel_memo`, `contract_wrap`.
* `consCH_contractP`: both halves of `[[2 b c] d]` for any `P` and the cell
  formula `[fh ft]` (`finishLUC_fwdC`, `finishLUC_bwdC`).
* `consCH_contract_of_annot`: both halves on every `Annot` of the nomm
  `[[2 b c] d]` with `b`, `c`, `d` in `FragU`, at most 255 `%6`, and `c` not
  the literal of a `%bare` formula.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `+mink` on `f'` runs `f` with no more fuel and returns what it returns,
on the subjects of `P`. -/
structure WrapRel (lib : Lib) (P : Noun → Prop) (f f' : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f' = some r →
    ∃ n', n' ≤ n ∧ minkF lib gul n' tm s f = some r
  bwd : ∀ {s gul : Noun} {tm : Trace} {r : Tone}, P s → Mink lib gul tm s f r → Mink lib gul tm s f' r

theorem wrapRel_six {lib : Lib} {P : Noun → Prop} {b c d e : Noun} {v : Nat}
    (hb : ∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A v)))
    (hce : (v = 0 ∧ e = c) ∨ (v = 1 ∧ e = d)) : WrapRel lib P e (n4 (A 6) b c d) where
  fwd := fun {s gul n tm r} hs hm => by
    cases n with
    | zero => simp [minkF] at hm
    | succ n0 =>
      rw [minkF_succ_eq] at hm
      simp only [minkStep] at hm
      rcases tbind_eq_some hm with ⟨w, hw, h1⟩ | ⟨hw, hnz⟩
      · cases mink_det_zero (hb s gul hs) hw
        refine ⟨n0, Nat.le_succ n0, ?_⟩
        rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h1
        · exact h1
      · exact absurd (mink_det_zero (hb s gul hs) hw) (hnz _)
  bwd := fun hs h => mink_six_of hb hce hs h

theorem wrapRel_memo {lib : Lib} {P : Noun → Prop} {h f : Noun}
    (hh : ∀ x gul, P x → ∃ c, Mink lib gul [] x h (Tone.zero c)) :
    WrapRel lib P (n3 (A 2) (slot 1) (quote f)) (n3 (A 11) (C (A Tag.memo) h) f) where
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
      exact ⟨n1 + 2, Nat.le_refl _, by rw [minkF_call1]; exact hf⟩
  bwd := fun hs hm => mink_memo_of hh hs (mink_call1.mp hm)

/-- **Both halves go through a wrapper.** -/
theorem contract_wrap {lib : Lib} {P : Noun → Prop} {f f' : Noun} (W : WrapRel lib P f f') {N : Needs}
    {c : Straight Map} (H : ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c) :
    ∀ s, P s → ContractFwd lib N s f' [s] c ∧ ContractBwd lib N s f' [s] c := by
  intro s hs
  refine ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩
  · obtain ⟨n', hle, hm'⟩ := W.fwd hs hm
    exact (H s hs).1 σ Inv ν O n' gul ti tm r hN hS (oracleFwd_le hF hle) hm' st hI htr
  · obtain ⟨r, hm, hrel⟩ := (H s hs).2 σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx
    exact ⟨r, W.bwd hs hm, hrel⟩

/-- **Both halves of `[[2 b c] d]` for any `P`**, the formula `[fh ft]`. -/
theorem consCH_contractP {lib : Lib} {b c d : Nomm} (ub : UOK (S := S) (Map := Map) lib b)
    (uc : UOK (S := S) (Map := Map) lib c) (ud : UOK (S := S) (Map := Map) lib d) {P : Noun → Prop}
    {fh ft : Noun} (M : MinkN2 lib P fh b c) (hfh : ∃ x y, fh = C x y)
    (Mq : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s →
      minkF lib gul n tm s ft = some r → r = toneOf tm (pureEval d s))
    (MqB : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s ft (toneOf tm (pureEval d s)))
    (hcount : sixCount b + sixCount c + sixCount d ≤ 255) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.n2 b c Option.none) d) = some cd) (N : Needs) :
    ∀ s, P s → ContractFwd lib N s (C fh ft) [s] cd ∧ ContractBwd lib N s (C fh ft) [s] cd := by
  have F := finishLUC_fwdC lib (pq := Nomm.cons b c)
    (fun hr => consCH_runD lib ub uc ud M hfh Mq hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0
      condBelow_gen0 hr) (fun {s gul n tm r} hs e hm => by
        obtain ⟨n', rh, _, hmh, hr⟩ := minkF_consC hfh Mq hs hm
        rcases M.fwd hs hmh with ⟨n'', x, y, _, ex, ey, _⟩ | ⟨_, er⟩
        · rw [pureEval_cons, ex, ey] at e; simp at e
        · rcases hr with ⟨_, rfl⟩ | ⟨x, ex, _⟩
          · exact er
          · rw [er] at ex; cases ex) h N
  have B := finishLUC_bwdC lib (pq := Nomm.cons b c)
    (fun hr => ⟨(consCH_runD lib ub uc ud M hfh Mq hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0
        condBelow_gen0 hr).1,
      (consCH_runD lib ub uc ud M hfh Mq hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0
        condBelow_gen0 hr).2,
      consCH_runDB lib ub uc ud M hfh Mq MqB hcount (by simp [gen0]) rfl upBelow_gen0 clear_gen0
        condBelow_gen0 hr⟩)
    (fun {s gul tm} hs e => mink_consC_crash hfh (M.crash hs (by rw [pureEval_cons] at e; exact e))) h N
  exact fun s hs => ⟨F.2 s hs, B.2 s hs⟩

/-- **Both halves on every `Annot` of `[[2 b c] d]`** with the parts in
`FragU`, at most 255 `%6`, and `c` not the literal of a `%bare` formula:
`Annot.cons` (`consCH_contractP`, the head through `minkN2_of_annot`, the
tail through `mink_pure`) under the wrappers (`contract_wrap`). -/
theorem consCH_contract_of_annot {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    ∀ {b c d : Nomm}, nm = Nomm.cons (Nomm.n2 b c Option.none) d → FragU (S := S) b → FragU (S := S) c →
      FragU (S := S) d → sixCount b + sixCount c + sixCount d ≤ 255 → bareLitQ c = false →
      ∀ (env : CallEnv) (cd : Straight Map), finishLUC (S := S) env nm = some cd → ∀ N : Needs,
      ∀ s, P s → ContractFwd lib N s f [s] cd ∧ ContractBwd lib N s f [s] cd := by
  induction hA with
  | cons hA1 hA2 _ _ =>
    intro b c d e hb hc hd hcount hbl env cd h N
    cases e
    exact consCH_contractP (runU_uok lib hb) (runU_uok lib hc) (runU_uok lib hd)
      (minkN2_of_annot hok hA1 rfl (fragU_pure hb) (fragU_pure hc) hbl) ⟨_, _, rfl⟩
      (fun {s gul n tm r} hs hm => (mink_pure hok (fragU_pure hd) hA2 hs gul tm r).mp ⟨n, hm⟩)
      (fun {s gul tm} hs => (mink_pure hok (fragU_pure hd) hA2 hs gul tm _).mpr rfl) hcount h N
  | memo hh _ ih =>
    intro b c d e hb hc hd hcount hbl env cd h N
    exact contract_wrap (wrapRel_memo hh) (ih e hb hc hd hcount hbl env cd h N)
  | six0 hb' _ ih =>
    intro b c d e hb hc hd hcount hbl env cd h N
    exact contract_wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih e hb hc hd hcount hbl env cd h N)
  | six1 hb' _ ih =>
    intro b c d e hb hc hd hcount hbl env cd h N
    exact contract_wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih e hb hc hd hcount hbl env cd h N)
  | n0 => intro _ _ _ e; cases e
  | n1 => intro _ _ _ e; cases e
  | indirect => intro _ _ _ e; cases e
  | direct => intro _ _ _ e; cases e
  | inline => intro _ _ _ e; cases e
  | n3 => intro _ _ _ e; cases e
  | n4 => intro _ _ _ e; cases e
  | n5 => intro _ _ _ e; cases e
  | n6 => intro _ _ _ e; cases e
  | n7 => intro _ _ _ e; cases e
  | n8 => intro _ _ _ e; cases e
  | n9 => intro _ _ _ e; cases e
  | n10 => intro _ _ _ e; cases e
  | n11s => intro _ _ _ e; cases e
  | n11d => intro _ _ _ e; cases e
  | n11c => intro _ _ _ e; cases e
  | mean => intro _ _ _ e; cases e
  | n12 => intro _ _ _ e; cases e
  | bare => intro _ _ _ e; cases e
  | crash => intro _ _ _ e; cases e
  | fold => intro _ _ _ e; cases e
  | n8g => intro _ _ _ e; cases e
  | n8l => intro _ _ _ e; cases e
  | bareLit => intro _ _ _ e; cases e

end Comp
end SkaModel
end Formalization
