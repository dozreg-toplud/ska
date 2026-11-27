import lemmas.Ska.AnnotSBase
import lemmas.Ska.FolRel
import lemmas.Ska.ConvergeRel

/-!
# `InvBSR`, the analysis half: the cases of `fol-loop` give `RGoodK`

The case lemmas of `FolLoopRel.lean` again, for what the analysis adds to
`RGood` for the bake (`RGoodK`, `AnnotSBase.lean`).  Each `rgoodK_X` takes
the hypotheses of `rgood_X`, the old `RGood` of the recursion (`IH`, for the
products, `sff` and `saf` facts the `AnnotK` premises use) and `RGoodK` of
the recursion (`IHK`), and gives `RGoodK`:

* `annot`: the `Annot` proof with `AnnotK` constructors; at a direct call
  (memo key `mk`) the extra premise is `detK` of the formula part, whose
  product sock is `&` with the formula and whose provenance `want` covers;
* `detK`: a read from `sff` (the product is `&` and covered, so the read
  returns, so its axis is there); a cons is `&` only in the safe branch of
  `consProd` (a knit is never `&`, `knit_ne_yes`), then both parts are
  `saf`; a `%6`'s product is `+double-int` of its branches', which is `&`
  only if each branch is the result or `%void` (`doubleInt_yes`), and a
  `%void` branch keeps a call (`kc`) or the subject is `%void` (no noun is
  reached, `detK_empty`); hints: the body; reruns: the rerun;
* `safK`: a safe result is a literal, a cons of safe results or a safe hint;
* `kc`: a `%void` product on a subject that is not `%void` comes from a
  call: `+double-int`, `+knit` and `+darn` are `%void` only when a part is
  (`doubleInt_void`, `knit_void`, `darn_void`), a read of a sock that is not
  `%void` is not `%void`.
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock

/-! ## Helpers -/

theorem annotK_ctag {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {a b h f : Noun}
    {nm : Nomm} (hA : AnnotK lib code P (n3 (A 11) (C (A 0) h) f) nm) :
    AnnotK lib code P (n3 (A 11) (C (C a b) h) f) nm := by
  generalize hF : n3 (A 11) (C (A 0) h) f = F at hA
  cases hA with
  | n11d hh hf =>
    simp only [n3, C, A, Noun.cell.injEq, Noun.atom.injEq] at hF
    obtain ⟨-, ⟨rfl, rfl⟩, rfl⟩ := hF
    exact AnnotK.n11c hh hf
  | crash hcr => subst hF; exact AnnotK.crash fun gul t s => (mink_ctag_iff).mpr (hcr gul t s)
  | fold hv => subst hF; exact AnnotK.fold fun x gul hx => (mink_ctag_iff).mpr (hv x gul hx)
  | bare hb => subst hF; simp [isBare] at hb
  | bareLit hb => subst hF; simp [isBare] at hb
  | memo => simp [n3, C, A, Tag.memo] at hF
  | mean => simp [n3, C, A, Tag.mean] at hF
  | _ => simp [n3, n2, n4, C, A, slot, quote] at hF

theorem RGoodK.of_dunno {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape} {fol : Noun}
    {sub : Anno} {out : FolOut} (ha : AnnotK lib code (RSub bus W sub) fol out.nomm)
    (hd : out.prod = Anno.dunno) (hsaf : out.saf = false) : RGoodK lib code bus W fol sub out where
  annot := ha
  detK := fun _ he _ => by rw [hd] at he; simp [Anno.dunno, Sock.dunno] at he
  safK := fun h => by rw [hsaf] at h; cases h
  kc := fun _ hv => by rw [hd] at hv; simp [Anno.dunno, Sock.dunno] at hv

/-- **`+double-int` is `&` only where each side is the join or `%void`.** -/
theorem doubleInt_yes {a b : Anno} {d : Noun} (h : (doubleInt a b).sock = Sock.mk Cape.yes d) :
    (a.sock = Sock.void ∨ a = doubleInt a b) ∧ (b.sock = Sock.void ∨ b = doubleInt a b) := by
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact ⟨Or.inr rfl, Or.inr rfl⟩
  by_cases ha : a.sock = Sock.void
  · rw [doubleInt_void_left ha hab]; exact ⟨Or.inl ha, Or.inr rfl⟩
  by_cases hb : b.sock = Sock.void
  · rw [doubleInt_void_right hb ha hab]; exact ⟨Or.inr rfl, Or.inl hb⟩
  exfalso
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => exact ha rfl
  | mk ca da =>
  cases sb with
  | void => exact hb rfl
  | mk cb db =>
  revert h
  exact doubleInt_cases (fun r => r.sock = Sock.mk Cape.yes d → False) hab
    (fun e => by simp [Anno.dunno, Sock.dunno] at e) (fun _ e => knit_ne_yes _ _ _ e)

/-- **`+double-int` is `%void` only if both sides are.** -/
theorem doubleInt_void {a b : Anno} (h : (doubleInt a b).sock = Sock.void) :
    a.sock = Sock.void ∧ b.sock = Sock.void := by
  have ha : a.sock = Sock.void := by
    by_cases ha : a.sock = Sock.void
    · exact ha
    · exact absurd h (doubleInt_ne_void' _ a b (Nat.lt_succ_self _) ha)
  refine ⟨ha, ?_⟩
  by_cases hab : a = b
  · subst hab; exact ha
  · rw [doubleInt_void_left ha hab] at h; exact h

theorem knit_void {u v : Sock} (h : So.knit u v = Sock.void) : u = Sock.void ∨ v = Sock.void := by
  by_cases hu : u = Sock.void
  · exact Or.inl hu
  · by_cases hv : v = Sock.void
    · exact Or.inr hv
    · exact absurd h (knit_ne_void hu hv)

theorem darnUp_ne_void : ∀ (acc : List (Nat × Sock)) (two : Sock), two ≠ Sock.void →
    (∀ p ∈ acc, p.2 ≠ Sock.void) → So.darnUp two acc ≠ Sock.void
  | [], _, h, _ => h
  | (n, s) :: acc, two, h, ha => by
    have hs : s ≠ Sock.void := ha (n, s) (by simp)
    have ht : ∀ p ∈ acc, p.2 ≠ Sock.void := fun p hp => ha p (by simp [hp])
    rw [darnUp_eq]
    split
    · exact darnUp_ne_void _ _ (knit_ne_void h hs) ht
    · exact darnUp_ne_void _ _ (knit_ne_void hs h) ht

theorem darnDown_ne_void : ∀ (ax : Nat) (one two : Sock) (acc : List (Nat × Sock)) (s : Sock),
    one ≠ Sock.void → two ≠ Sock.void → (∀ p ∈ acc, p.2 ≠ Sock.void) →
    So.darnDown one ax two acc = some s → s ≠ Sock.void := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro one two acc s h1 h2 ha hd
  rw [So.darnDown] at hd
  split at hd
  · cases hd; exact darnUp_ne_void acc two h2 ha
  · split at hd
    · cases hd
    · split at hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (hed_ne_void h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact tel_ne_void h1
            · exact ha p hp) hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (tel_ne_void h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact hed_ne_void h1
            · exact ha p hp) hd

/-- **`+darn:so` is `%void` only if a side is.** -/
theorem darn_void {one two : Sock} {ax : Nat} (h : So.darn one ax two = some Sock.void) :
    one = Sock.void ∨ two = Sock.void := by
  unfold So.darn at h
  split at h
  · cases h; exact Or.inr rfl
  · split at h
    · rename_i hv; exact hv
    · split at h
      · simp [Sock.dunno] at h
      · rename_i hv _
        simp only [not_or] at hv
        exact absurd rfl (darnDown_ne_void ax one two [] _ hv.1 hv.2 (by simp) h)

/-- A branch of a `%6` whose join is `&` and covered: `DetK` or `KC`. -/
theorem branch_detK {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape} {fol : Noun}
    {sub : Anno} {o : FolOut} {u : Anno} (G : RGoodK lib code bus W fol sub o)
    (hu : o.prod.sock = Sock.void ∨ o.prod = u) (d : Noun) (he : u.sock = Sock.mk Cape.yes d)
    (hW : ∀ q, (distribute Cape.yes u.src).Has q → W.Has q) :
    DetK (RSub bus W sub) o.nomm ∨ KC o.nomm := by
  rcases hu with hv | rfl
  · by_cases hs : sub.sock = Sock.void
    · exact Or.inl (detK_empty (rsub_void hs) _)
    · exact Or.inr (G.kc hs hv)
  · exact Or.inl (G.detK d he hW)

section Cases

variable {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {go : FolGo} {bus : Sock} {W : Cape}
  {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

/-! ## The cases without calls -/

theorem rgoodK_other (hs : shape fol = Shape.other)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RGoodK lib code bus W fol sub out := by
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact RGoodK.of_dunno (AnnotK.crash (shape_other_crashes hs lib)) rfl rfl

theorem rgoodK_op1 {p : Noun} (hs : shape fol = Shape.op1 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨AnnotK.n1, fun _ _ _ => trivial, fun _ _ => trivial, fun _ hv => by cases hv⟩

theorem rgoodK_op0 {p : Nat} (hs : shape fol = Shape.op0 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RGoodK lib code bus W fol sub out := by
  have G : RGood lib code bus W fol sub out := rgood_op0 hs h
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨pr, hpr, rfl, rfl⟩ := h
  refine ⟨AnnotK.n0, ?_, fun h => (by cases h), ?_⟩
  · intro d he hW
    show AxisIn _ _
    intro x hx
    exact ⟨d, mink_inv_n0 (G.sff rfl d he hW x (A 0) hx)⟩
  · intro hv hpv
    exfalso
    split at hpr
    · cases hpr; simp [Anno.dunno, Sock.dunno] at hpv
    · split at hpr
      · cases hpr; exact hv hpv
      · rename_i h0 h1
        obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hpr
        obtain ⟨q, hq⟩ := axisPath_pos p (by omega)
        rw [pull_eq_sockAt (by omega) hq] at hs'
        cases hs'
        exact sockAt_ne_void q hv hpv

theorem rgoodK_op3 (IHK : GoRGoodK lib code bus W go) {a b : Noun}
    (hs : shape fol = Shape.op3 a b) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, rfl, rfl⟩ := h
  exact RGoodK.of_dunno (AnnotK.n3 (IHK _ _ _ _ _ _ _ _ h1 hW).annot) rfl rfl

theorem rgoodK_op4 (IHK : GoRGoodK lib code bus W go) {a b : Noun}
    (hs : shape fol = Shape.op4 a b) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, rfl, rfl⟩ := h
  exact RGoodK.of_dunno (AnnotK.n4 (IHK _ _ _ _ _ _ _ _ h1 hW).annot) rfl rfl

theorem rgoodK_op5 (IHK : GoRGoodK lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.op5 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  exact RGoodK.of_dunno (AnnotK.n5 (IHK _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))).annot
    (IHK _ _ _ _ _ _ _ _ h2 hW).annot) rfl rfl

theorem rgoodK_op12 (IHK : GoRGoodK lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.op12 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  exact RGoodK.of_dunno (AnnotK.n12 (IHK _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))).annot
    (IHK _ _ _ _ _ _ _ _ h2 hW).annot) rfl rfl

theorem rgoodK_op6 (IHK : GoRGoodK lib code bus W go) (hM : GoMono go) {a b q r : Noun}
    (hs : shape fol = Shape.op6 a b q r) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, ⟨r', g3⟩, h3, rfl, rfl⟩ := h
  have W3 : WCov W g3 := hW
  have W2 : WCov W g2 := hW.of_le (hM _ _ _ _ _ _ _ _ h3)
  have W1 : WCov W g1 := W2.of_le (hM _ _ _ _ _ _ _ _ h2)
  have Gp := IHK _ _ _ _ _ _ _ _ h1 W1
  have Gq := IHK _ _ _ _ _ _ _ _ h2 W2
  have Gr := IHK _ _ _ _ _ _ _ _ h3 W3
  refine ⟨AnnotK.n6 Gp.annot Gq.annot Gr.annot, ?_, fun h => (by cases h), ?_⟩
  · intro d he hWd
    obtain ⟨hq, hr⟩ := doubleInt_yes he
    exact ⟨branch_detK Gq hq d he hWd, branch_detK Gr hr d he hWd⟩
  · intro hv hpv
    obtain ⟨hq, hr⟩ := doubleInt_void hpv
    exact Or.inr ⟨Gq.kc hv hq, Gr.kc hv hr⟩

theorem rgoodK_op7 (IH : GoRGood lib code bus W go) (IHK : GoRGoodK lib code bus W go) (hM : GoMono go)
    {a b q : Noun}
    (hs : shape fol = Shape.op7 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  have Gp := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Kp := IHK _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Kq := IHK _ _ _ _ _ _ _ _ h2 hW
  refine ⟨AnnotK.n7 Kp.annot (Kq.annot.mono (rsub_img Gp.prod)), fun _ _ _ => trivial,
    fun h => (by cases h), ?_⟩
  intro hv hpv
  by_cases hp : p.prod.sock = Sock.void
  · exact Or.inl (Kp.kc hv hp)
  · exact Or.inr (Kq.kc hp hpv)

theorem rgoodK_cons (IHK : GoRGoodK lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.cons a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
  have Gl := IHK _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Gr := IHK _ _ _ _ _ _ _ _ h2 hW
  have hsafe : (consProd l r).2 = true → l.saf = true ∧ r.saf = true := by
    unfold consProd
    split
    · rename_i hc; intro _; exact ⟨hc.1, hc.2.1⟩
    · intro h; cases h
  refine ⟨AnnotK.cons Gl.annot Gr.annot, ?_, ?_, ?_⟩
  · intro d he _
    have hc : (consProd l r).2 = true := by
      revert he
      show (consProd l r).1.sock = Sock.mk Cape.yes d → (consProd l r).2 = true
      unfold consProd
      split
      · intro _; rfl
      · intro he; exact absurd he (knit_ne_yes _ _ _)
    obtain ⟨s1, s2⟩ := hsafe hc
    exact ⟨Gl.safK s1 _, Gr.safK s2 _⟩
  · intro hc P
    obtain ⟨s1, s2⟩ := hsafe hc
    exact ⟨Gl.safK s1 P, Gr.safK s2 P⟩
  · intro hv hpv
    revert hpv
    show (consProd l r).1.sock = Sock.void → KC l.nomm ∨ KC r.nomm
    unfold consProd
    split
    · intro e; cases e
    · intro e
      rcases knit_void e with e | e
      · exact Or.inl (Gl.kc hv e)
      · exact Or.inr (Gr.kc hv e)

/-! ## Calls -/

theorem rgoodK_call (hT : RTab lib code tab) (hwf : WellFormed bus) (IHK : GoRGoodK lib code bus W go)
    (hM : GoMono go) {b c : Noun} {s f : FolOut}
    (Gs : RGood lib code bus W b sub s) (Gf : RGood lib code bus W c sub f)
    (Ks : RGoodK lib code bus W b sub s) (Kf : RGoodK lib code bus W c sub f) {g2 : Gen}
    (h : callStep tab go mk bc df s f g2 = some (out, gen')) (hW : WCov W gen') :
    RGoodK lib code bus W (n3 (A 2) b c) sub out := by
  unfold callStep at h
  split at h
  · -- a void subject or formula
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨AnnotK.indirect Ks.annot Kf.annot, fun _ _ _ => trivial, fun h => (by cases h),
      fun _ _ => trivial⟩
  · rename_i hv
    simp only [not_or] at hv
    split at h
    · rename_i fa fb hfp
      have hg : (∀ q, (distribute Cape.yes f.prod.src).Has q → W.Has q) →
          ∀ X' x gul g, RP bus W sub X' x → Mink lib gul [] x c (Tone.zero g) → g = C fa fb := by
        intro hWf X' x gul g hx hm
        have R := Gf.prod X' x gul g hx hm
        have := known_at (provO_iff.mpr R.prov) R.stat R.req [] (by simpa [springAt] using hWf)
          (by rw [hfp]; rfl)
        simpa [slotO, slotAtPath] using this
      split at h
      · -- inlined
        rename_i hin
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨i, g3⟩, hi, rfl, rfl⟩ := h
        have hWf : ∀ q, (distribute Cape.yes f.prod.src).Has q → W.Has q := fun q hq =>
          hW q (hM _ _ _ _ _ _ _ _ hi q (by show (Ca.uni _ _).Has q; rw [uni_has]; exact Or.inr hq))
        have Ki := IHK _ _ _ _ _ _ _ _ hi hW
        refine ⟨AnnotK.inline Ks.annot ?_ (Ki.annot.mono (rsub_img Gs.prod)), fun _ _ _ => trivial,
          fun h => (by cases h), ?_⟩
        · exact fun x gul hx => Gf.sff hin.2.2.2 _ hfp hWf x gul hx
        · intro _ hpv; exact Or.inr (Ki.kc hv.1 hpv)
      · -- a direct call
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨d, hd, h⟩ := h
        split at h
        · cases h
        · rename_i lc dl hdl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hWf : ∀ q, (distribute Cape.yes f.prod.src).Has q → W.Has q := fun q hq =>
            hW q (by show (Ca.uni _ (Ca.uni _ _)).Has q; rw [uni_has, uni_has]; exact Or.inr (Or.inl hq))
          have hWs : ∀ q, (distribute lc s.prod.src).Has q → W.Has q := fun q hq =>
            hW q (by show (Ca.uni _ (Ca.uni _ _)).Has q; rw [uni_has, uni_has]; exact Or.inr (Or.inr hq))
          obtain ⟨nb, hnb⟩ := hT.code _ _ d hd
          have hless : ∀ X' x gul y, RP bus W sub X' x → Mink lib gul [] x b (Tone.zero y) →
              Fits d.less y := fun X' x gul y hx hm => by
            have R := Gs.prod X' x gul y hx hm
            exact hT.less _ _ d lc dl hd hv.1 hdl y (call_sub_fits (provO_iff.mpr R.prov) R.stat hwf R.req hWs)
          refine ⟨AnnotK.direct (bl := ⟨d.less, C fa fb⟩) Ks.annot Kf.annot hnb ?_ ?_
            (fun _ => Kf.detK _ hfp hWf), fun _ _ _ => trivial, fun h => (by cases h), fun _ _ => trivial⟩
          · intro x gul y ⟨X', hx⟩ hm; exact hless X' x gul y hx hm
          · intro x gul g ⟨X', hx⟩ hm; exact hg hWf X' x gul g hx hm
    · -- an indirect call
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact RGoodK.of_dunno (AnnotK.indirect Ks.annot Kf.annot) rfl rfl

theorem rgoodK_op2 (hT : RTab lib code tab) (hwf : WellFormed bus) (IH : GoRGood lib code bus W go)
    (IHK : GoRGoodK lib code bus W go) (hM : GoMono go) {a b q : Noun} (hs : shape fol = Shape.op2 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s', g1⟩, h1, ⟨f', g2⟩, h2, h⟩ := h
  have W2 : WCov W g2 := hW.of_le (callStep_mono hM h)
  have W1 : WCov W g1 := W2.of_le (hM _ _ _ _ _ _ _ _ h2)
  exact rgoodK_call hT hwf IHK hM (IH _ _ _ _ _ _ _ _ h1 W1) (IH _ _ _ _ _ _ _ _ h2 W2)
    (IHK _ _ _ _ _ _ _ _ h1 W1) (IHK _ _ _ _ _ _ _ _ h2 W2) h hW

/-! ## Edits and hints -/

theorem rgoodK_op10 (IHK : GoRGoodK lib code bus W go) (hM : GoMono go) {ax : Nat} {don r1 r2 : Noun}
    (hs : shape fol = Shape.op10 ax don r1 r2)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  split at h
  · rename_i hax
    subst hax
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact RGoodK.of_dunno (AnnotK.crash fun gul t s => ⟨1, by simp [minkF, minkStep]⟩) rfl rfl
  · rename_i hax
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, sk, hd, rfl, rfl⟩ := h
    have Gd := IHK _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
    have Gr := IHK _ _ _ _ _ _ _ _ h2 hW
    refine ⟨AnnotK.n10 hax Gd.annot Gr.annot, fun _ _ _ => trivial, fun h => (by cases h), ?_⟩
    intro hv hpv
    have e : sk = Sock.void := hpv
    subst e
    rcases darn_void hd with e | e
    · exact Or.inr (Gr.kc hv e)
    · exact Or.inl (Gd.kc hv e)

theorem rgoodK_op11s_plain (IHK : GoRGoodK lib code bus W go) {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p ≠ Tag.bare)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, hp, if_false, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨q, g1⟩, h1, rfl, rfl⟩ := h
  have Gq := IHK _ _ _ _ _ _ _ _ h1 hW
  exact ⟨AnnotK.n11s Gq.annot, fun d he hW' => Gq.detK d he hW', fun h => (by cases h),
    fun hv hpv => Gq.kc hv hpv⟩

theorem rgoodK_op11d (IH : GoRGood lib code bus W go) (IHK : GoRGoodK lib code bus W go) (hM : GoMono go)
    {tag : Nat} {h1 h2 f : Noun}
    (hs : shape fol = Shape.op11d tag h1 h2 f)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨hh, g1⟩, hh1, h⟩ := h
  split at h
  · -- a safe %memo: the call [2 [0 1] 1 f], memoized
    rename_i hm
    obtain ⟨htag, hsaf, _⟩ := hm
    subst htag
    have K' := IHK _ _ _ _ _ _ _ _ h hW
    have Gh := IH _ _ _ _ _ _ _ _ hh1 (hW.of_le (hM _ _ _ _ _ _ _ _ h))
    obtain ⟨dh, _, mh⟩ := Gh.saf hsaf
    have hret : ∀ x gul, ∃ c, Mink lib gul [] x (C h1 h2) (Tone.zero c) := fun x gul => ⟨dh, mh x gul⟩
    exact ⟨AnnotK.memo (fun x gul _ => hret x gul) K'.annot, K'.detK, K'.safK, K'.kc⟩
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨arm, g2⟩, ha, ⟨fr, g3⟩, hf1, rfl, rfl⟩ := h
    have Kf := IHK _ _ _ _ _ _ _ _ hf1 hW
    have Kh := IHK _ _ _ _ _ _ _ _ hh1
      ((hW.of_le (hM _ _ _ _ _ _ _ _ hf1)).of_le (meanArm_mono hM ha))
    have hsaf : decide ((tag = Tag.spot ∨ tag = Tag.mean) ∧ hh.saf = true ∧ fr.saf = true) = true →
        fr.saf = true := by
      intro hd
      simp only [decide_eq_true_eq] at hd
      exact hd.2.2
    cases harm : arm with
    | none =>
      subst harm
      exact ⟨AnnotK.n11d Kh.annot Kf.annot, fun d he hW' => Kf.detK d he hW',
        fun hs P => Kf.safK (hsaf hs) P, fun hv hpv => Or.inr (Kf.kc hv hpv)⟩
    | some bk =>
      obtain ⟨bl, k⟩ := bk
      have htag := meanArm_tag ha (by rw [harm]; simp)
      subst htag
      subst harm
      exact ⟨AnnotK.mean Kh.annot Kf.annot, fun d he hW' => Kf.detK d he hW',
        fun hs P => Kf.safK (hsaf hs) P, fun hv hpv => Or.inr (Kf.kc hv hpv)⟩

/-! ## A hint whose tag is a cell, analysed as under `%$` -/

theorem rgoodK_op11c (IHK : GoRGoodK lib code bus W go) {x y h1 h2 f : Noun}
    (hs : shape fol = Shape.op11c x y h1 h2 f)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGoodK lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  have K' := IHK _ _ _ _ _ _ _ _ h hW
  exact ⟨annotK_ctag K'.annot, K'.detK, K'.safK, K'.kc⟩

end Cases

end AnnotSF
end SkaModel
end Formalization
