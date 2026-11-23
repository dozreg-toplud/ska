import lemmas.Ska.FolLoopFacts

/-!
# `fol-loop` is sound, given its table of callees

`folLoop_good`: whatever the model of `fol-loop` returns for a formula on a
subject sock `sub` (`folLoopF tab n fol sub ...  = some (out, gen')`) is
`Good`:

* `annot`: the nomm satisfies `Annot` on every subject that fits the sock, so
  that, with `CodeOK` of the code table, it returns what `+mink` returns on
  the formula (`nomm_agree`);
* `prod`: on every subject that fits the sock, every product of the formula
  fits the product sock;
* `saf`: if the analysis says the formula is safe, its product sock is a
  fully known constant, which the formula returns on every subject;
* `safe`: if `+safe-nomm` holds of the nomm, the formula returns on every
  subject that fits the sock;
* `sff`: if `+safe-fol-fol` holds of the nomm and the product sock is fully
  known (`&`), the formula returns that constant on every subject that fits
  the sock.  This is what makes the side condition of `Annot.inline` hold.

The table is assumed to be right about the calls it answers (`TabOK`): the
code requirement of an answer holds of the call's subjects, the callee's
bell has code, and the product sock holds of the callee's products.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- **What the proofs assume of the table of callees.**  For an answer `d` to
a call of the formula `f` on the subject sock `s`:

* `less`: every subject of `s` fits the code requirement `d.less`;
* `code`: the bell `[d.less f]` has a nomm in the code table;
* `prod`: every product of `f` on a subject of `s` fits `d.prod`. -/
structure TabOK (lib : Lib) (code : Bell → Option Nomm) (tab : Tab) : Prop where
  less : ∀ s f d, tab s f = some d → ∀ y, Fits s y → Fits d.less y
  code : ∀ s f d, tab s f = some d → ∃ nb, code ⟨d.less, f⟩ = some nb
  prod : ∀ s f d, tab s f = some d →
    ∀ y gul p, Fits s y → Mink lib gul [] y f (Tone.zero p) → Fits d.prod p

/-- What holds of a result `out` of `fol-loop` on the formula `fol` and the
subject `sub`. -/
structure Good (lib : Lib) (code : Bell → Option Nomm) (fol : Noun) (sub : Anno) (out : FolOut) :
    Prop where
  annot : Annot lib code (Fits sub.sock) fol out.nomm
  prod : ∀ x gul p, Fits sub.sock x → Mink lib gul [] x fol (Tone.zero p) → Fits out.prod.sock p
  saf : out.saf = true →
    ∃ d, out.prod.sock = Sock.mk Cape.yes d ∧ ∀ x gul, Mink lib gul [] x fol (Tone.zero d)
  safe : safeNomm out.nomm = true →
    ∀ x gul, Fits sub.sock x → ∃ c, Mink lib gul [] x fol (Tone.zero c)
  sff : safeFolFol out.nomm = true → ∀ d, out.prod.sock = Sock.mk Cape.yes d →
    ∀ x gul, Fits sub.sock x → Mink lib gul [] x fol (Tone.zero d)

/-- Every result of the recursion is `Good`. -/
def GoGood (lib : Lib) (code : Bell → Option Nomm) (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') →
    Good lib code fol sub out

theorem shape_eq {fol : Noun} {s : Shape} (hs : shape fol = s) (hne : s ≠ Shape.other) :
    fol = s.fol := by
  rcases shape_fol fol with h | h
  · rw [hs] at h; exact absurd h hne
  · rw [hs] at h; exact h.symm

/-- A result whose nomm is neither safe nor `+safe-fol-fol`, and that is not
safe, from its `annot` and `prod`. -/
theorem Good.of_plain {lib : Lib} {code : Bell → Option Nomm} {fol : Noun} {sub : Anno}
    {out : FolOut} (ha : Annot lib code (Fits sub.sock) fol out.nomm)
    (hp : ∀ x gul p, Fits sub.sock x → Mink lib gul [] x fol (Tone.zero p) → Fits out.prod.sock p)
    (hsaf : out.saf = false) (hs : safeNomm out.nomm = false) (hf : safeFolFol out.nomm = false) :
    Good lib code fol sub out where
  annot := ha
  prod := hp
  saf := fun h => by rw [hsaf] at h; cases h
  safe := fun h => by rw [hs] at h; cases h
  sff := fun h => by rw [hf] at h; cases h

/-- A result whose product is unknown, from its `annot`. -/
theorem Good.of_dunno {lib : Lib} {code : Bell → Option Nomm} {fol : Noun} {sub : Anno}
    {out : FolOut} (ha : Annot lib code (Fits sub.sock) fol out.nomm)
    (hd : out.prod.sock = Sock.dunno) (hsaf : out.saf = false) (hs : safeNomm out.nomm = false) :
    Good lib code fol sub out where
  annot := ha
  prod := fun _ _ _ _ _ => by rw [hd]; exact fits_dunno _
  saf := fun h => by rw [hsaf] at h; cases h
  safe := fun h => by rw [hs] at h; cases h
  sff := fun _ d he _ _ _ => by rw [hd] at he; cases he

section Cases

variable {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {go : FolGo}
  {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

/-! ## The cases without calls -/

theorem good_other (hs : shape fol = Shape.other)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact Good.of_dunno (Annot.crash (shape_other_crashes hs lib)) rfl rfl rfl

theorem good_op1 {p : Noun} (hs : shape fol = Shape.op1 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact {
    annot := Annot.n1
    prod := fun _ _ _ _ hm => by rw [mink_inv_n1 hm]; rfl
    saf := fun _ => ⟨p, rfl, fun x _ => mink_mk_n1 x p⟩
    safe := fun _ x _ _ => ⟨p, mink_mk_n1 x p⟩
    sff := fun _ d he x _ _ => by cases he; exact mink_mk_n1 x _ }

theorem good_op0 {p : Nat} (hs : shape fol = Shape.op0 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨pr, hpr, rfl, rfl⟩ := h
  refine ⟨Annot.n0, ?_, fun h => (by cases h), fun h => (by cases h), ?_⟩
  · intro x gul y hx hm
    have hy := mink_inv_n0 hm
    split at hpr
    · cases hpr; exact fits_dunno _
    · split at hpr
      · rename_i h1; subst h1; cases hpr
        simp only [slot?_one, Option.some.injEq] at hy
        subst hy; exact hx
      · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hpr
        exact pull_fits hx hy hs'
  · intro _ d he x gul hx
    split at hpr
    · cases hpr; cases he
    · split at hpr
      · rename_i h1; subst h1; cases hpr
        simp only at he
        rw [he] at hx
        rw [fits_yes hx]
        exact mink_mk_n0 (slot?_one _)
      · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hpr
        simp only at he
        subst he
        exact mink_mk_n0 (pull_yes hx hs')

theorem good_op3 (IH : GoGood lib code go) {a b : Noun} (hs : shape fol = Shape.op3 a b)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, rfl, rfl⟩ := h
  exact Good.of_dunno (Annot.n3 (IH _ _ _ _ _ _ _ _ h1).annot) rfl rfl rfl

theorem good_op4 (IH : GoGood lib code go) {a b : Noun} (hs : shape fol = Shape.op4 a b)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, rfl, rfl⟩ := h
  exact Good.of_dunno (Annot.n4 (IH _ _ _ _ _ _ _ _ h1).annot) rfl rfl rfl

theorem good_op5 (IH : GoGood lib code go) {a b q : Noun} (hs : shape fol = Shape.op5 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  exact Good.of_dunno (Annot.n5 (IH _ _ _ _ _ _ _ _ h1).annot (IH _ _ _ _ _ _ _ _ h2).annot)
    rfl rfl rfl

theorem good_op12 (IH : GoGood lib code go) {a b q : Noun} (hs : shape fol = Shape.op12 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  exact Good.of_dunno (Annot.n12 (IH _ _ _ _ _ _ _ _ h1).annot (IH _ _ _ _ _ _ _ _ h2).annot)
    rfl rfl rfl

theorem good_op6 (IH : GoGood lib code go) {a b q r : Noun} (hs : shape fol = Shape.op6 a b q r)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, ⟨r', g3⟩, h3, rfl, rfl⟩ := h
  have Gq := IH _ _ _ _ _ _ _ _ h2
  have Gr := IH _ _ _ _ _ _ _ _ h3
  refine Good.of_plain (Annot.n6 (IH _ _ _ _ _ _ _ _ h1).annot Gq.annot Gr.annot) ?_ rfl rfl rfl
  intro x gul y hx hm
  rcases mink_inv_n6 hm with hc | hd
  · exact doubleInt_fits_left _ _ (Gq.prod x gul y hx hc)
  · exact doubleInt_fits_right _ _ (Gr.prod x gul y hx hd)

theorem good_op7 (IH : GoGood lib code go) {a b q : Noun} (hs : shape fol = Shape.op7 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  have Gp := IH _ _ _ _ _ _ _ _ h1
  have Gq := IH _ _ _ _ _ _ _ _ h2
  refine Good.of_plain (Annot.n7 Gp.annot (Gq.annot.mono ?_)) ?_ rfl rfl rfl
  · intro y ⟨x, gul, hx, hm⟩
    exact Gp.prod x gul y hx hm
  · intro x gul y hx hm
    obtain ⟨z, h1, h2⟩ := mink_inv_n7 hm
    exact Gq.prod z gul y (Gp.prod x gul z hx h1) h2

theorem good_cons (IH : GoGood lib code go) {a b q : Noun} (hs : shape fol = Shape.cons a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
  have Gl := IH _ _ _ _ _ _ _ _ h1
  have Gr := IH _ _ _ _ _ _ _ _ h2
  -- the safe case: both sides are constants
  have hsafe : (consProd l r).2 = true → ∃ dl dr, (consProd l r).1.sock = Sock.mk Cape.yes (C dl dr) ∧
      (∀ x gul, Mink lib gul [] x (C a b) (Tone.zero dl)) ∧ (∀ x gul, Mink lib gul [] x q (Tone.zero dr)) := by
    unfold consProd
    split
    · rename_i hc
      intro _
      obtain ⟨dl, hl, ml⟩ := Gl.saf hc.1
      obtain ⟨dr, hr, mr⟩ := Gr.saf hc.2.1
      refine ⟨dl, dr, ?_, ml, mr⟩
      simp only [hl, hr, Sock.data]
    · intro h; cases h
  refine ⟨Annot.cons Gl.annot Gr.annot, ?_, ?_, ?_, ?_⟩
  · intro x gul p hx hm
    obtain ⟨p1, p2, rfl, m1, m2⟩ := mink_inv_cons hm
    unfold consProd
    split
    · rename_i hc
      obtain ⟨dl, hl, _⟩ := Gl.saf hc.1
      obtain ⟨dr, hr, _⟩ := Gr.saf hc.2.1
      have f1 := Gl.prod x gul p1 hx m1
      have f2 := Gr.prod x gul p2 hx m2
      rw [hl] at f1; rw [hr] at f2
      simp only [hl, hr, Sock.data, fits_yes f1, fits_yes f2]
      rfl
    · exact knit_fits (Gl.prod x gul p1 hx m1) (Gr.prod x gul p2 hx m2)
  · intro hc
    obtain ⟨dl, dr, he, ml, mr⟩ := hsafe hc
    exact ⟨C dl dr, he, fun x gul => mink_mk_cons (ml x gul) (mr x gul)⟩
  · intro hn x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hn
    obtain ⟨c1, m1⟩ := Gl.safe hn.1 x gul hx
    obtain ⟨c2, m2⟩ := Gr.safe hn.2 x gul hx
    exact ⟨C c1 c2, mink_mk_cons m1 m2⟩
  · intro _ d he x gul _
    have hc : (consProd l r).2 = true := by
      revert he
      unfold consProd
      split
      · intro _; rfl
      · intro he; exact absurd he (knit_ne_yes _ _ _)
    obtain ⟨dl, dr, he', ml, mr⟩ := hsafe hc
    rw [he] at he'
    cases he'
    exact mink_mk_cons (ml x gul) (mr x gul)

/-! ## Calls -/

theorem good_call (hT : TabOK lib code tab) (IH : GoGood lib code go) {b c : Noun} {s f : FolOut}
    (Gs : Good lib code b sub s) (Gf : Good lib code c sub f) {g2 : Gen}
    (h : callStep tab go mk bc df s f g2 = some (out, gen')) :
    Good lib code (n3 (A 2) b c) sub out := by
  unfold callStep at h
  split at h
  · -- a void subject or formula: no run reaches the call
    rename_i hv
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Good.of_plain (Annot.indirect Gs.annot Gf.annot) ?_ rfl rfl rfl
    intro x gul p hx hm
    obtain ⟨y, g, m1, m2, _⟩ := mink_inv_n2 hm
    have f1 := Gs.prod x gul y hx m1
    have f2 := Gf.prod x gul g hx m2
    rcases hv with hv | hv
    · rw [hv] at f1; exact absurd f1 id
    · rw [hv] at f2; exact absurd f2 id
  · split at h
    · rename_i fa fb hfp
      split at h
      · -- inlined
        rename_i hin
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨i, g3⟩, hi, rfl, rfl⟩ := h
        have Gi := IH _ _ _ _ _ _ _ _ hi
        have hg : ∀ x gul g, Fits sub.sock x → Mink lib gul [] x c (Tone.zero g) → g = C fa fb :=
          fun x gul g hx hm => by have := Gf.prod x gul g hx hm; rw [hfp] at this; exact this
        refine Good.of_plain (Annot.inline Gs.annot ?_ (Gi.annot.mono ?_)) ?_ rfl rfl rfl
        · exact fun x gul hx => Gf.sff hin.2.2.2 _ hfp x gul hx
        · intro y ⟨x, gul, hx, hm⟩
          exact Gs.prod x gul y hx hm
        · intro x gul p hx hm
          obtain ⟨y, g, m1, m2, m3⟩ := mink_inv_n2 hm
          rw [hg x gul g hx m2] at m3
          exact Gi.prod y gul p (Gs.prod x gul y hx m1) m3
      · -- a direct call
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨d, hd, h⟩ := h
        split at h
        · cases h
        · rename_i lc _ _
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨nb, hnb⟩ := hT.code _ _ d hd
          have hg : ∀ x gul g, Fits sub.sock x → Mink lib gul [] x c (Tone.zero g) → g = C fa fb :=
            fun x gul g hx hm => by have := Gf.prod x gul g hx hm; rw [hfp] at this; exact this
          refine Good.of_plain (Annot.direct (bl := ⟨d.less, C fa fb⟩) Gs.annot Gf.annot hnb ?_ hg)
            ?_ rfl rfl rfl
          · exact fun x gul y hx hm => hT.less _ _ d hd y (Gs.prod x gul y hx hm)
          · intro x gul p hx hm
            obtain ⟨y, g, m1, m2, m3⟩ := mink_inv_n2 hm
            rw [hg x gul g hx m2] at m3
            exact hT.prod _ _ d hd y gul p (Gs.prod x gul y hx m1) m3
    · -- an indirect call
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Good.of_dunno (Annot.indirect Gs.annot Gf.annot) rfl rfl rfl

theorem good_op2 (hT : TabOK lib code tab) (IH : GoGood lib code go) {a b q : Noun}
    (hs : shape fol = Shape.op2 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s', g1⟩, h1, ⟨f', g2⟩, h2, h⟩ := h
  exact good_call hT IH (IH _ _ _ _ _ _ _ _ h1) (IH _ _ _ _ _ _ _ _ h2) h

/-! ## Edits and hints -/

theorem good_op10 (IH : GoGood lib code go) {ax : Nat} {don r1 r2 : Noun}
    (hs : shape fol = Shape.op10 ax don r1 r2)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  split at h
  · rename_i hax
    subst hax
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Good.of_dunno (Annot.crash fun gul t s => ⟨1, by simp [minkF, minkStep]⟩) rfl rfl rfl
  · rename_i hax
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, sk, hd, rfl, rfl⟩ := h
    have Gd := IH _ _ _ _ _ _ _ _ h1
    have Gr := IH _ _ _ _ _ _ _ _ h2
    refine Good.of_plain (Annot.n10 hax Gd.annot Gr.annot) ?_ rfl rfl rfl
    intro x gul p hx hm
    obtain ⟨tg, vv, m1, m2, he⟩ := mink_inv_n10 hm
    exact darn_fits (Gr.prod x gul tg hx m1) (Gd.prod x gul vv hx m2) he hd

theorem good_op11s_plain (IH : GoGood lib code go) {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p ≠ Tag.bare)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, hp, if_false, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨q, g1⟩, h1, rfl, rfl⟩ := h
  have Gq := IH _ _ _ _ _ _ _ _ h1
  refine ⟨Annot.n11s Gq.annot, ?_, fun h => (by cases h), ?_, ?_⟩
  · exact fun x gul y hx hm => Gq.prod x gul y hx (mink_inv_n11s hm)
  · intro hn x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hn
    obtain ⟨c, mc⟩ := Gq.safe hn.2 x gul hx
    exact ⟨c, mink_mk_n11s _ mc⟩
  · intro hn d he x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hn
    exact mink_mk_n11s _ (Gq.sff hn.2 d he x gul hx)

/-- The arm of a `%mean` hint is found only under `%mean`. -/
theorem meanArm_tag {tag : Nat} {h : FolOut} {g : Gen} {arm : Option (Bell × Option Noun)}
    {g' : Gen} (ha : meanArm go tag h mk bc g = some (arm, g')) (hs : arm ≠ none) :
    tag = Tag.mean := by
  unfold meanArm at ha
  split at ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    exact absurd ha.1.symm hs
  · rename_i hc
    exact (Classical.not_not.mp hc).1

theorem good_op11d (IH : GoGood lib code go) {tag : Nat} {h1 h2 f : Noun}
    (hs : shape fol = Shape.op11d tag h1 h2 f)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨hh, g1⟩, hh1, h⟩ := h
  have Gh := IH _ _ _ _ _ _ _ _ hh1
  split at h
  · -- a safe %memo: the call [2 [0 1] 1 f], memoized
    rename_i hm
    obtain ⟨htag, hsaf, _⟩ := hm
    subst htag
    have G' := IH _ _ _ _ _ _ _ _ h
    obtain ⟨dh, _, mh⟩ := Gh.saf hsaf
    have hret : ∀ x gul, ∃ c, Mink lib gul [] x (C h1 h2) (Tone.zero c) := fun x gul => ⟨dh, mh x gul⟩
    have heq : ∀ x gul p, Mink lib gul [] x (n3 (A 11) (C (A Tag.memo) (C h1 h2)) f) (Tone.zero p) ↔
        Mink lib gul [] x (n3 (A 2) (slot 1) (quote f)) (Tone.zero p) :=
      fun x gul p => mink_memo_iff (hret x gul)
    refine ⟨Annot.memo (fun x gul _ => hret x gul) G'.annot, ?_, ?_, ?_, ?_⟩
    · exact fun x gul p hx hm => G'.prod x gul p hx ((heq x gul p).mp hm)
    · intro hs'
      obtain ⟨d, hd, md⟩ := G'.saf hs'
      exact ⟨d, hd, fun x gul => (heq x gul d).mpr (md x gul)⟩
    · intro hn x gul hx
      obtain ⟨c, mc⟩ := G'.safe hn x gul hx
      exact ⟨c, (heq x gul c).mpr mc⟩
    · exact fun hn d hd x gul hx => (heq x gul d).mpr (G'.sff hn d hd x gul hx)
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨arm, g2⟩, ha, ⟨fr, g3⟩, hf1, rfl, rfl⟩ := h
    have Gf := IH _ _ _ _ _ _ _ _ hf1
    have hprod : ∀ x gul p, Fits sub.sock x →
        Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero p) → Fits fr.prod.sock p :=
      fun x gul p hx hm => Gf.prod x gul p hx (mink_inv_n11d hm).2
    -- what both nomms need of the clue and the body
    have hsafe : ∀ x gul, Fits sub.sock x → safeNomm hh.nomm = true → safeNomm fr.nomm = true →
        ∃ c, Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero c) := by
      intro x gul hx s1 s2
      obtain ⟨c1, m1⟩ := Gh.safe s1 x gul hx
      obtain ⟨c2, m2⟩ := Gf.safe s2 x gul hx
      exact ⟨c2, mink_mk_n11d _ m1 m2⟩
    have hsff : ∀ x gul d, Fits sub.sock x → safeNomm hh.nomm = true → safeFolFol fr.nomm = true →
        fr.prod.sock = Sock.mk Cape.yes d →
        Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero d) := by
      intro x gul d hx s1 s2 hd
      obtain ⟨c1, m1⟩ := Gh.safe s1 x gul hx
      exact mink_mk_n11d _ m1 (Gf.sff s2 d hd x gul hx)
    have hsaf : decide ((tag = Tag.spot ∨ tag = Tag.mean) ∧ hh.saf = true ∧ fr.saf = true) = true →
        ∃ d, fr.prod.sock = Sock.mk Cape.yes d ∧
          ∀ x gul, Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero d) := by
      intro hd
      simp only [decide_eq_true_eq] at hd
      obtain ⟨d1, _, m1⟩ := Gh.saf hd.2.1
      obtain ⟨d2, e2, m2⟩ := Gf.saf hd.2.2
      exact ⟨d2, e2, fun x gul => mink_mk_n11d _ (m1 x gul) (m2 x gul)⟩
    cases harm : arm with
    | none =>
      subst harm
      refine ⟨Annot.n11d Gh.annot Gf.annot, hprod, hsaf, ?_, ?_⟩
      · intro hn x gul hx
        simp only [safeNomm, Bool.and_eq_true] at hn
        exact hsafe x gul hx hn.1.2 hn.2
      · intro hn d hd x gul hx
        simp only [safeFolFol, Bool.and_eq_true] at hn
        exact hsff x gul d hx hn.1.2 hn.2 hd
    | some bk =>
      obtain ⟨bl, k⟩ := bk
      have htag := meanArm_tag ha (by rw [harm]; simp)
      subst htag
      subst harm
      refine ⟨Annot.mean Gh.annot Gf.annot, hprod, hsaf, ?_, ?_⟩
      · intro hn x gul hx
        simp only [safeNomm, Bool.and_eq_true] at hn
        exact hsafe x gul hx hn.1 hn.2
      · intro hn d hd x gul hx
        simp only [safeFolFol, Bool.and_eq_true] at hn
        exact hsff x gul d hx hn.1 hn.2 hd

/-! ## The rewritten cases: `%8`, `%9`, `%bare` -/

theorem shape_op7_eq (a b q : Noun) : shape (n3 (A 7) (C a b) q) = Shape.op7 a b q := rfl
theorem shape_cons_eq (a b q : Noun) : shape (C (C a b) q) = Shape.cons a b q := rfl
theorem shape_slot1 : shape (slot 1) = Shape.op0 1 := rfl
theorem shape_self_call (g : Noun) :
    shape (n3 (A 2) (slot 1) (quote g)) = Shape.op2 (A 0) (A 1) (quote g) := rfl
theorem shape_quote (g : Noun) : shape (quote g) = Shape.op1 g := rfl

theorem consProd_unsafe {l r : FolOut} (hr : r.saf = false) :
    consProd l r = (⟨So.knit l.prod.sock r.prod.sock, Pi.cons l.prod.src r.prod.src⟩, false) := by
  unfold consProd
  simp [hr]

/-- `fol-loop` on `[0 1]`. -/
theorem folLoop_slot1 {m : Nat} (h : folLoopF tab m (slot 1) sub mk bc df gen = some (out, gen')) :
    out = ⟨Nomm.n0 1, sub, false⟩ ∧ gen' = gen := by
  cases m with
  | zero => simp [folLoopF] at h
  | succ m =>
    rw [folLoopF_succ] at h
    simp only [folStep, shape_slot1, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    simp at hpr
    subst hpr
    exact ⟨rfl, rfl⟩

/-- A call under `%bare` is indirect. -/
theorem callStep_bare {s f : FolOut} {g : Gen}
    (h : callStep tab go mk true df s f g = some (out, gen')) :
    out.nomm = Nomm.n2 s.nomm f.nomm none := by
  unfold callStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  · split at h
    · rename_i hb; cases hb
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]

theorem Good.transfer {fol fol' : Noun} (G : Good lib code fol' sub out)
    (heq : ∀ x gul p, Mink lib gul [] x fol (Tone.zero p) ↔ Mink lib gul [] x fol' (Tone.zero p))
    (ha : Annot lib code (Fits sub.sock) fol out.nomm) : Good lib code fol sub out where
  annot := ha
  prod := fun x gul p hx hm => G.prod x gul p hx ((heq x gul p).mp hm)
  saf := fun hs => by
    obtain ⟨d, hd, md⟩ := G.saf hs
    exact ⟨d, hd, fun x gul => (heq x gul d).mpr (md x gul)⟩
  safe := fun hn x gul hx => by
    obtain ⟨c, mc⟩ := G.safe hn x gul hx
    exact ⟨c, (heq x gul c).mpr mc⟩
  sff := fun hn d hd x gul hx => (heq x gul d).mpr (G.sff hn d hd x gul hx)

theorem good_bare {m : Nat} (IH : GoGood lib code (folLoopF tab m)) {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p = Tag.bare)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) :
    Good lib code fol sub out := by
  subst hp
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, if_true] at h
  have G' := IH _ _ _ _ _ _ _ _ h
  refine G'.transfer (fun x gul p => mink_self_call.symm) ?_
  have hn : out.nomm = Nomm.n2 (Nomm.n0 1) (Nomm.n1 (C (A 11) (C (A Tag.bare) (C a b)))) none := by
    cases m with
    | zero => simp [folLoopF] at h
    | succ m =>
      rw [folLoopF_succ] at h
      simp only [folStep, shape_self_call, Option.bind_eq_some_iff] at h
      obtain ⟨⟨s', g1⟩, h1, ⟨f', g2⟩, h2, h⟩ := h
      obtain ⟨rfl, rfl⟩ := folLoop_slot1 h1
      cases m with
      | zero => simp [folLoopF] at h2
      | succ m =>
        rw [folLoopF_succ] at h2
        simp only [folStep, shape_quote, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact callStep_bare h
  rw [hn]
  exact Annot.bare (by simp [isBare])

theorem good_op9 {m : Nat} (IH : GoGood lib code (folLoopF tab m)) (IH' : ∀ k, k + 1 = m → GoGood lib code (folLoopF tab k))
    {p : Nat} {a b : Noun} (hs : shape fol = Shape.op9 p a b)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) :
    Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  cases m with
  | zero => simp [folLoopF] at h
  | succ k =>
  rw [folLoopF_succ] at h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨o1, g1⟩, h1, ⟨o2, g2⟩, h2, rfl, rfl⟩ := h
  have G1 := IH' k rfl _ _ _ _ _ _ _ _ h1
  have G2 := IH' k rfl _ _ _ _ _ _ _ _ h2
  refine Good.of_plain (Annot.n9 G1.annot (G2.annot.mono ?_)) ?_ rfl rfl rfl
  · intro y ⟨x, gul, hx, hm⟩
    exact G1.prod x gul y hx hm
  · intro x gul y hx hm
    obtain ⟨core, arm, m1, hsl, m2⟩ := mink_inv_n9 hm
    exact G2.prod core gul y (G1.prod x gul core hx m1)
      (mink_mk_n2 (mink_mk_n0 (slot?_one core)) (mink_mk_n0 hsl) m2)

theorem good_op8 {m : Nat} (IH' : ∀ k, k < m → GoGood lib code (folLoopF tab k))
    {a b q : Noun} (hs : shape fol = Shape.op8 a b q)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) :
    Good lib code fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  cases m with
  | zero => simp [folLoopF] at h
  | succ k =>
  rw [folLoopF_succ] at h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨o1, g1⟩, h1, ⟨o2, g2⟩, h2, rfl, rfl⟩ := h
  have G2 := IH' k (by omega) _ _ _ _ _ _ _ _ h2
  cases k with
  | zero => simp [folLoopF] at h1
  | succ j =>
  rw [folLoopF_succ] at h1
  simp only [folStep, shape_cons_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨ob, gb⟩, hb, ⟨oz, gz⟩, hz, rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := folLoop_slot1 hz
  have Gb := IH' j (by omega) _ _ _ _ _ _ _ _ hb
  rw [consProd_unsafe rfl] at G2
  refine Good.of_plain (Annot.n8 Gb.annot (G2.annot.mono ?_)) ?_ rfl rfl rfl
  · intro z ⟨x, y, gul, hx, hm, hz⟩
    subst hz
    exact knit_fits (Gb.prod x gul y hx hm) hx
  · intro x gul p hx hm
    obtain ⟨y, m1, m2⟩ := mink_inv_n8 hm
    exact G2.prod (C y x) gul p (knit_fits (Gb.prod x gul y hx m1) hx) m2

end Cases

/-! ## The main theorem -/

/-- **`fol-loop` is sound, given its table.**  Every result of the model of
`fol-loop` with a table that is right about its answers is `Good`: its nomm
satisfies `Annot` on the subjects of the subject sock, its product sock holds
of every product, and what it says is safe is. -/
theorem folLoop_good {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} (hT : TabOK lib code tab) :
    ∀ n, GoGood lib code (folLoopF tab n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro fol sub mk bc df gen out gen' h
  cases n with
  | zero => simp [folLoopF] at h
  | succ m =>
  rw [folLoopF_succ] at h
  have IH : GoGood lib code (folLoopF tab m) := ih m (by omega)
  cases hs : shape fol with
  | cons a b q => exact good_cons IH hs h
  | op0 p => exact good_op0 hs h
  | op1 p => exact good_op1 hs h
  | op2 a b q => exact good_op2 hT IH hs h
  | op3 a b => exact good_op3 IH hs h
  | op4 a b => exact good_op4 IH hs h
  | op5 a b q => exact good_op5 IH hs h
  | op6 a b q r => exact good_op6 IH hs h
  | op7 a b q => exact good_op7 IH hs h
  | op8 a b q => exact good_op8 (fun k hk => ih k (by omega)) hs h
  | op9 p a b => exact good_op9 IH (fun k hk => ih k (by omega)) hs h
  | op10 ax don r1 r2 => exact good_op10 IH hs h
  | op11s p a b =>
    by_cases hp : p = Tag.bare
    · exact good_bare IH hs hp h
    · exact good_op11s_plain IH hs hp h
  | op11d tag h1 h2 f => exact good_op11d IH hs h
  | op12 a b q => exact good_op12 IH hs h
  | other => exact good_other hs h

/-! ## Consequences -/

/-- **Product soundness of `fol-loop`.**  On every subject that fits the
subject sock, every product of the formula fits the product sock. -/
theorem folLoop_prod {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} (hT : TabOK lib code tab)
    {n : Nat} {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
    {out : FolOut} (h : folLoopF tab n fol sub mk bc df gen = some (out, gen'))
    {x : Noun} (hx : Fits sub.sock x) {gul p : Noun} (hm : Mink lib gul [] x fol (Tone.zero p)) :
    Fits out.prod.sock p :=
  (folLoop_good hT n _ _ _ _ _ _ _ _ h).prod x gul p hx hm

/-- **The nomm of `fol-loop` satisfies the invariant.** -/
theorem folLoop_annot {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} (hT : TabOK lib code tab)
    {n : Nat} {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
    {out : FolOut} (h : folLoopF tab n fol sub mk bc df gen = some (out, gen')) :
    Annot lib code (Fits sub.sock) fol out.nomm :=
  (folLoop_good hT n _ _ _ _ _ _ _ _ h).annot

/-- **Step 2, inlining: `+safe-fol-fol` with a product cape of exactly `&`
implies the side condition of `Annot.inline`.**  If `fol-loop` analyses the
formula of a formula `c` to a nomm on which `+safe-fol-fol` holds, with the
product sock `&+g`, then `c` returns `g` on every subject of the subject
sock, from any scry gate. -/
theorem safeFolFol_inline {lib : Lib} {code : Bell → Option Nomm} {tab : Tab}
    (hT : TabOK lib code tab) {n : Nat} {c : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool}
    {gen gen' : Gen} {f : FolOut} (h : folLoopF tab n c sub mk bc df gen = some (f, gen'))
    (hs : safeFolFol f.nomm = true) {g : Noun} (hp : f.prod.sock = Sock.mk Cape.yes g) :
    ∀ x gul, Fits sub.sock x → Mink lib gul [] x c (Tone.zero g) :=
  (folLoop_good hT n _ _ _ _ _ _ _ _ h).sff hs g hp

/-- **Step 2, memoization: `saf` implies the side condition of
`Annot.memo`.**  A clue that `fol-loop` calls safe returns, on every subject. -/
theorem saf_memo {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} (hT : TabOK lib code tab)
    {n : Nat} {h : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
    {o : FolOut} (hr : folLoopF tab n h sub mk bc df gen = some (o, gen')) (hs : o.saf = true) :
    ∀ x gul, ∃ c, Mink lib gul [] x h (Tone.zero c) := by
  obtain ⟨d, _, md⟩ := (folLoop_good hT n _ _ _ _ _ _ _ _ hr).saf hs
  exact fun x gul => ⟨d, md x gul⟩

/-- **The analysis of one function agrees with `+mink`**, given a table that
is right about its answers and a code table whose nomms satisfy the
invariant: on every subject of the identity's sock, the nomm that `fol-loop`
returns, run with the code table, returns exactly the tones that `+mink`
returns on the formula. -/
theorem folLoop_agree {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} (hT : TabOK lib code tab)
    (hc : CodeOK lib code) {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (h : folLoopTop tab n bus fol = some (out, gen')) {x : Noun} (hx : Fits bus x) (gul : Noun)
    (t : Trace) (r : Tone) :
    Mink lib gul t x fol r ↔ ∃ m, nommF lib gul code m t x out.nomm = some r :=
  nomm_agree lib gul code hc (folLoop_annot hT h) hx t r

end SkaModel
end Formalization
