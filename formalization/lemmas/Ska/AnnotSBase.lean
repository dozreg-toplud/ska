import lemmas.Ska.AnnotSDet

/-!
# `InvBSR`: the shared definitions of the copies (track Q, README Gaps 27)

`AnnotK` is `Annot` with, at a direct call whose memo key is `~`, `DetK` of
the formula part's nomm on the call's subjects (`AnnotSDet.lean`): what the
analysis knows of the formula part and the bake keeps.  It gives `AnnotS`
(`AnnotK.toAnnotS`, by `ret_of_detK`), so `CodeOKK` gives `CodeOKS`.

`RGoodK` is what the analysis adds to `RGood` (`FolLoopRel.lean`) for it:
the nomm satisfies `AnnotK` on the nouns reached; if the product sock is `&`
and `W` covers its provenance, the nomm satisfies `DetK` there; a safe result
(`saf`) satisfies `DetK` everywhere (it reads nothing); and on a subject that
is not `%void`, a `%void` product comes with `KC` (a void product comes only
from a call).

Also here: `KC.not_safe` (`KC` fails `+safe-nomm` and `+safe-fol-fol`),
`detK_empty`, `AnnotK.mono`, `AnnotK.mono_code`.
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock

/-- **`Annot` with `DetK` of the formula part at a direct call with no memo
key.**  Every other constructor is `Annot`'s. -/
inductive AnnotK (lib : Lib) (code : Bell → Option Nomm) : (Noun → Prop) → Noun → Nomm → Prop where
  | cons {P a1 a2 b p q} : AnnotK lib code P (C a1 a2) p → AnnotK lib code P b q →
      AnnotK lib code P (C (C a1 a2) b) (Nomm.cons p q)
  | n0 {P axis} : AnnotK lib code P (slot axis) (Nomm.n0 axis)
  | n1 {P k} : AnnotK lib code P (quote k) (Nomm.n1 k)
  | indirect {P b c p q} : AnnotK lib code P b p → AnnotK lib code P c q →
      AnnotK lib code P (n3 (A 2) b c) (Nomm.n2 p q none)
  | direct {P b c p q bl k nb} : AnnotK lib code P b p → AnnotK lib code P c q →
      code bl = some nb →
      (∀ x gul y, P x → Mink lib gul [] x b (Tone.zero y) → Fits bl.less y) →
      (∀ x gul g, P x → Mink lib gul [] x c (Tone.zero g) → g = bl.fol) →
      (k = none → DetK P q) →
      AnnotK lib code P (n3 (A 2) b c) (Nomm.n2 p q (some (bl, k)))
  | inline {P b c g p q} : AnnotK lib code P b p →
      (∀ x gul, P x → Mink lib gul [] x c (Tone.zero g)) →
      AnnotK lib code (Img lib P b) g q →
      AnnotK lib code P (n3 (A 2) b c) (Nomm.n7 p q)
  | n3 {P b p} : AnnotK lib code P b p → AnnotK lib code P (n2 (A 3) b) (Nomm.n3 p)
  | n4 {P b p} : AnnotK lib code P b p → AnnotK lib code P (n2 (A 4) b) (Nomm.n4 p)
  | n5 {P b c p q} : AnnotK lib code P b p → AnnotK lib code P c q →
      AnnotK lib code P (n3 (A 5) b c) (Nomm.n5 p q)
  | n6 {P b c d p q r} : AnnotK lib code P b p → AnnotK lib code P c q → AnnotK lib code P d r →
      AnnotK lib code P (n4 (A 6) b c d) (Nomm.n6 p q r)
  | n7 {P b c p q} : AnnotK lib code P b p → AnnotK lib code (Img lib P b) c q →
      AnnotK lib code P (n3 (A 7) b c) (Nomm.n7 p q)
  | n8 {P b c p q} : AnnotK lib code P b p → AnnotK lib code (Img8 lib P b) c q →
      AnnotK lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p (Nomm.n0 1)) q)
  | n9 {P axis c q r} : AnnotK lib code P c q →
      AnnotK lib code (Img lib P c) (n3 (A 2) (slot 1) (slot axis)) r →
      AnnotK lib code P (n3 (A 9) (A axis) c) (Nomm.n7 q r)
  | n10 {P axis v t p q} : axis ≠ 0 → AnnotK lib code P v p → AnnotK lib code P t q →
      AnnotK lib code P (n3 (A 10) (n2 (A axis) v) t) (Nomm.n10 axis p q)
  | n11s {P tag q f} : AnnotK lib code P f q →
      AnnotK lib code P (n3 (A 11) (A tag) f) (Nomm.n11s tag q f)
  | n11d {P tag h f p q} : AnnotK lib code P h p → AnnotK lib code P f q →
      AnnotK lib code P (n3 (A 11) (C (A tag) h) f) (Nomm.n11d tag p q f)
  | n11c {P x y h f p q} : AnnotK lib code P h p → AnnotK lib code P f q →
      AnnotK lib code P (n3 (A 11) (C (C x y) h) f) (Nomm.n11d 0 p q f)
  | mean {P h f p q b k} : AnnotK lib code P h p → AnnotK lib code P f q →
      AnnotK lib code P (n3 (A 11) (C (A Tag.mean) h) f) (Nomm.mean p b q f k)
  | n12 {P b c p q} : AnnotK lib code P b p → AnnotK lib code P c q →
      AnnotK lib code P (n3 (A 12) b c) (Nomm.n12 p q)
  | bare {P f} : isBare f = true → AnnotK lib code P f (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) none)
  | memo {P h f nm} : (∀ x gul, P x → ∃ c, Mink lib gul [] x h (Tone.zero c)) →
      AnnotK lib code P (n3 (A 2) (slot 1) (quote f)) nm →
      AnnotK lib code P (n3 (A 11) (C (A Tag.memo) h) f) nm
  | crash {P f} : CrashesAtOnce lib f → AnnotK lib code P f (Nomm.n0 0)
  | fold {P f v} : (∀ x gul, P x → Mink lib gul [] x f (Tone.zero v)) → AnnotK lib code P f (Nomm.n1 v)
  | six0 {P b c d q} : (∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A 0))) → AnnotK lib code P c q →
      AnnotK lib code P (n4 (A 6) b c d) q
  | six1 {P b c d r} : (∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A 1))) → AnnotK lib code P d r →
      AnnotK lib code P (n4 (A 6) b c d) r
  | n8g {P b c p r q} : AnnotK lib code P b p → AnnotK lib code P (slot 1) r →
      AnnotK lib code (Img8 lib P b) c q →
      AnnotK lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p r) q)
  | n8l {P b c y d q} : (∀ x gul, P x → Mink lib gul [] x b (Tone.zero y) ∧ x = d) →
      AnnotK lib code (Img8 lib P b) c q →
      AnnotK lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.n1 (C y d)) q)
  | bareLit {P f d} : isBare f = true → (∀ x, P x → x = d) →
      AnnotK lib code P f (Nomm.n2 (Nomm.n1 d) (Nomm.n1 f) none)


theorem AnnotK.toAnnot {lib : Lib} {code : Bell → Option Nomm} {P f nm}
    (h : AnnotK lib code P f nm) : Annot lib code P f nm := by
  induction h with
  | cons _ _ i1 i2 => exact Annot.cons i1 i2
  | n0 => exact Annot.n0
  | n1 => exact Annot.n1
  | indirect _ _ i1 i2 => exact Annot.indirect i1 i2
  | direct _ _ hc hy hg _ i1 i2 => exact Annot.direct i1 i2 hc hy hg
  | inline _ ht _ i1 i2 => exact Annot.inline i1 ht i2
  | n3 _ i => exact Annot.n3 i
  | n4 _ i => exact Annot.n4 i
  | n5 _ _ i1 i2 => exact Annot.n5 i1 i2
  | n6 _ _ _ i1 i2 i3 => exact Annot.n6 i1 i2 i3
  | n7 _ _ i1 i2 => exact Annot.n7 i1 i2
  | n8 _ _ i1 i2 => exact Annot.n8 i1 i2
  | n9 _ _ i1 i2 => exact Annot.n9 i1 i2
  | n10 ha _ _ i1 i2 => exact Annot.n10 ha i1 i2
  | n11s _ i => exact Annot.n11s i
  | n11d _ _ i1 i2 => exact Annot.n11d i1 i2
  | n11c _ _ i1 i2 => exact Annot.n11c i1 i2
  | mean _ _ i1 i2 => exact Annot.mean i1 i2
  | n12 _ _ i1 i2 => exact Annot.n12 i1 i2
  | bare hb => exact Annot.bare hb
  | memo hh _ i => exact Annot.memo hh i
  | crash hc => exact Annot.crash hc
  | fold hf => exact Annot.fold hf
  | six0 hb _ i => exact Annot.six0 hb i
  | six1 hb _ i => exact Annot.six1 hb i
  | n8g _ _ _ i1 i2 i3 => exact Annot.n8g i1 i2 i3
  | n8l hb _ i => exact Annot.n8l hb i
  | bareLit hb hd => exact Annot.bareLit hb hd

/-- **`AnnotK` holds on fewer subjects.** -/
theorem AnnotK.mono {lib : Lib} {code : Bell → Option Nomm} :
    ∀ {P f n}, AnnotK lib code P f n → ∀ {Q : Noun → Prop}, (∀ x, Q x → P x) → AnnotK lib code Q f n := by
  intro P f n h
  induction h with
  | cons _ _ ih1 ih2 => intro Q hQ; exact AnnotK.cons (ih1 hQ) (ih2 hQ)
  | n0 => intro Q _; exact AnnotK.n0
  | n1 => intro Q _; exact AnnotK.n1
  | indirect _ _ ih1 ih2 => intro Q hQ; exact AnnotK.indirect (ih1 hQ) (ih2 hQ)
  | direct _ _ hc hy hg hd ih1 ih2 =>
    intro Q hQ
    exact AnnotK.direct (ih1 hQ) (ih2 hQ) hc (fun x gul y hx => hy x gul y (hQ x hx))
      (fun x gul g hx => hg x gul g (hQ x hx)) (fun hk => DetK.mono hQ _ (hd hk))
  | inline _ htot _ ih1 ih2 =>
    intro Q hQ
    exact AnnotK.inline (ih1 hQ) (fun x gul hx => htot x gul (hQ x hx)) (ih2 (Img_mono hQ))
  | n3 _ ih => intro Q hQ; exact AnnotK.n3 (ih hQ)
  | n4 _ ih => intro Q hQ; exact AnnotK.n4 (ih hQ)
  | n5 _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n5 (ih1 hQ) (ih2 hQ)
  | n6 _ _ _ ih1 ih2 ih3 => intro Q hQ; exact AnnotK.n6 (ih1 hQ) (ih2 hQ) (ih3 hQ)
  | n7 _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n7 (ih1 hQ) (ih2 (Img_mono hQ))
  | n8 _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n8 (ih1 hQ) (ih2 (Img8_mono hQ))
  | n9 _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n9 (ih1 hQ) (ih2 (Img_mono hQ))
  | n10 hax _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n10 hax (ih1 hQ) (ih2 hQ)
  | n11s _ ih => intro Q hQ; exact AnnotK.n11s (ih hQ)
  | n11d _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n11d (ih1 hQ) (ih2 hQ)
  | n11c _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n11c (ih1 hQ) (ih2 hQ)
  | mean _ _ ih1 ih2 => intro Q hQ; exact AnnotK.mean (ih1 hQ) (ih2 hQ)
  | n12 _ _ ih1 ih2 => intro Q hQ; exact AnnotK.n12 (ih1 hQ) (ih2 hQ)
  | bare hb => intro Q _; exact AnnotK.bare hb
  | memo hh _ ih =>
    intro Q hQ
    exact AnnotK.memo (fun x gul hx => hh x gul (hQ x hx)) (ih hQ)
  | crash hc => intro Q _; exact AnnotK.crash hc
  | fold hv => intro Q hQ; exact AnnotK.fold (fun x gul hx => hv x gul (hQ x hx))
  | six0 hb _ ih => intro Q hQ; exact AnnotK.six0 (fun x gul hx => hb x gul (hQ x hx)) (ih hQ)
  | six1 hb _ ih => intro Q hQ; exact AnnotK.six1 (fun x gul hx => hb x gul (hQ x hx)) (ih hQ)
  | n8g _ _ _ ih1 ih2 ih3 => intro Q hQ; exact AnnotK.n8g (ih1 hQ) (ih2 hQ) (ih3 (Img8_mono hQ))
  | n8l hb _ ih => intro Q hQ; exact AnnotK.n8l (fun x gul hx => hb x gul (hQ x hx)) (ih (Img8_mono hQ))
  | bareLit hb hd => intro Q hQ; exact AnnotK.bareLit hb (fun x hx => hd x (hQ x hx))

/-- `AnnotK` needs of the code table only that the bells it calls have a
nomm: a table with more bells keeps it. -/
theorem AnnotK.mono_code {lib : Lib} {code code' : Bell → Option Nomm}
    (hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb')
    {P : Noun → Prop} {f : Noun} {n : Nomm} (h : AnnotK lib code P f n) : AnnotK lib code' P f n := by
  induction h with
  | cons _ _ ih1 ih2 => exact AnnotK.cons ih1 ih2
  | n0 => exact AnnotK.n0
  | n1 => exact AnnotK.n1
  | indirect _ _ ih1 ih2 => exact AnnotK.indirect ih1 ih2
  | direct _ _ hb hl hf hd ih1 ih2 =>
    obtain ⟨nb', hb'⟩ := hcc _ _ hb
    exact AnnotK.direct ih1 ih2 hb' hl hf hd
  | inline _ hc _ ih1 ih2 => exact AnnotK.inline ih1 hc ih2
  | n3 _ ih => exact AnnotK.n3 ih
  | n4 _ ih => exact AnnotK.n4 ih
  | n5 _ _ ih1 ih2 => exact AnnotK.n5 ih1 ih2
  | n6 _ _ _ ih1 ih2 ih3 => exact AnnotK.n6 ih1 ih2 ih3
  | n7 _ _ ih1 ih2 => exact AnnotK.n7 ih1 ih2
  | n8 _ _ ih1 ih2 => exact AnnotK.n8 ih1 ih2
  | n9 _ _ ih1 ih2 => exact AnnotK.n9 ih1 ih2
  | n10 hx _ _ ih1 ih2 => exact AnnotK.n10 hx ih1 ih2
  | n11s _ ih => exact AnnotK.n11s ih
  | n11d _ _ ih1 ih2 => exact AnnotK.n11d ih1 ih2
  | n11c _ _ ih1 ih2 => exact AnnotK.n11c ih1 ih2
  | mean _ _ ih1 ih2 => exact AnnotK.mean ih1 ih2
  | n12 _ _ ih1 ih2 => exact AnnotK.n12 ih1 ih2
  | bare hb => exact AnnotK.bare hb
  | memo hs _ ih => exact AnnotK.memo hs ih
  | crash hc => exact AnnotK.crash hc
  | fold hv => exact AnnotK.fold hv
  | six0 hb _ ih => exact AnnotK.six0 hb ih
  | six1 hb _ ih => exact AnnotK.six1 hb ih
  | n8g _ _ _ ih1 ih2 ih3 => exact AnnotK.n8g ih1 ih2 ih3
  | n8l hb _ ih => exact AnnotK.n8l hb ih
  | bareLit hb hd => exact AnnotK.bareLit hb hd


/-- **`AnnotK` gives `AnnotS`**: at a direct call with no memo key, a formula
part that passes `+safe-fol-fol` returns (`ret_of_detK`). -/
theorem AnnotK.toAnnotS {lib : Lib} {code : Bell → Option Nomm} {P f nm}
    (h : AnnotK lib code P f nm) : Glue.AnnotS lib code P f nm := by
  induction h with
  | cons _ _ i1 i2 => exact Glue.AnnotS.cons i1 i2
  | n0 => exact Glue.AnnotS.n0
  | n1 => exact Glue.AnnotS.n1
  | indirect _ _ i1 i2 => exact Glue.AnnotS.indirect i1 i2
  | direct _ _ hc hy hg hd i1 i2 =>
    exact Glue.AnnotS.direct i1 i2 hc hy hg (fun hk hs => ret_of_detK i2.toAnnot hs (hd hk))
  | inline _ ht _ i1 i2 => exact Glue.AnnotS.inline i1 ht i2
  | n3 _ i => exact Glue.AnnotS.n3 i
  | n4 _ i => exact Glue.AnnotS.n4 i
  | n5 _ _ i1 i2 => exact Glue.AnnotS.n5 i1 i2
  | n6 _ _ _ i1 i2 i3 => exact Glue.AnnotS.n6 i1 i2 i3
  | n7 _ _ i1 i2 => exact Glue.AnnotS.n7 i1 i2
  | n8 _ _ i1 i2 => exact Glue.AnnotS.n8 i1 i2
  | n9 _ _ i1 i2 => exact Glue.AnnotS.n9 i1 i2
  | n10 ha _ _ i1 i2 => exact Glue.AnnotS.n10 ha i1 i2
  | n11s _ i => exact Glue.AnnotS.n11s i
  | n11d _ _ i1 i2 => exact Glue.AnnotS.n11d i1 i2
  | n11c _ _ i1 i2 => exact Glue.AnnotS.n11c i1 i2
  | mean _ _ i1 i2 => exact Glue.AnnotS.mean i1 i2
  | n12 _ _ i1 i2 => exact Glue.AnnotS.n12 i1 i2
  | bare hb => exact Glue.AnnotS.bare hb
  | memo hh _ i => exact Glue.AnnotS.memo hh i
  | crash hc => exact Glue.AnnotS.crash hc
  | fold hf => exact Glue.AnnotS.fold hf
  | six0 hb _ i => exact Glue.AnnotS.six0 hb i
  | six1 hb _ i => exact Glue.AnnotS.six1 hb i
  | n8g _ _ _ i1 i2 i3 => exact Glue.AnnotS.n8g i1 i2 i3
  | n8l hb _ i => exact Glue.AnnotS.n8l hb i
  | bareLit hb hd => exact Glue.AnnotS.bareLit hb hd

/-- The table invariant with `AnnotK`. -/
def CodeOKK (lib : Lib) (code : Bell → Option Nomm) : Prop :=
  ∀ bl nb, code bl = some nb → AnnotK lib code (Fits bl.less) bl.fol nb

theorem CodeOKK.toCodeOKS {lib : Lib} {code : Bell → Option Nomm} (h : CodeOKK lib code) :
    Glue.CodeOKS lib code := fun bl nb hb => (h bl nb hb).toAnnotS

theorem CodeOKK.toCodeOK {lib : Lib} {code : Bell → Option Nomm} (h : CodeOKK lib code) :
    CodeOK lib code := fun bl nb hb => (h bl nb hb).toAnnot

/-! ## `KC` and `DetK` -/

/-- **A nomm that keeps a call fails `+safe-nomm` and `+safe-fol-fol`.** -/
theorem KC.not_safe : ∀ {n : Nomm}, KC n → safeNomm n = false ∧ safeFolFol n = false
  | Nomm.n0 _, h | Nomm.n1 _, h => h.elim
  | Nomm.n2 _ _ _, _ | Nomm.n3 _, _ | Nomm.n4 _, _ | Nomm.n5 _ _, _ | Nomm.n6 _ _ _, _
  | Nomm.n7 _ _, _ | Nomm.n10 _ _ _, _ | Nomm.n12 _ _, _ => ⟨rfl, rfl⟩
  | Nomm.cons p q, h => by
    rcases h with h | h
    · have := KC.not_safe h; simp [safeNomm, safeFolFol, this.1, this.2]
    · have := KC.not_safe h; simp [safeNomm, safeFolFol, this.1, this.2]
  | Nomm.n11s _ q _, h => by
    have := KC.not_safe (n := q) h; simp [safeNomm, safeFolFol, this.1, this.2]
  | Nomm.n11d _ p q _, h => by
    rcases h with h | h
    · have := KC.not_safe h; simp [safeNomm, safeFolFol, this.1]
    · have := KC.not_safe h; simp [safeNomm, safeFolFol, this.1, this.2]
  | Nomm.mean p _ q _ _, h => by
    rcases h with h | h
    · have := KC.not_safe h; simp [safeNomm, safeFolFol, this.1]
    · have := KC.not_safe h; simp [safeNomm, safeFolFol, this.1, this.2]

/-- **`DetK` holds of every nomm on a set with no subject.** -/
theorem detK_empty {P : Noun → Prop} (hP : ∀ x, ¬ P x) : ∀ n : Nomm, DetK P n
  | Nomm.n0 _ => fun x hx => (hP x hx).elim
  | Nomm.n1 _ => trivial
  | Nomm.cons p q => ⟨detK_empty hP p, detK_empty hP q⟩
  | Nomm.n11s _ q _ => detK_empty hP q
  | Nomm.n11d _ _ q _ => detK_empty hP q
  | Nomm.mean _ _ q _ _ => detK_empty hP q
  | Nomm.n6 _ q r => ⟨Or.inl (detK_empty hP q), Or.inl (detK_empty hP r)⟩
  | Nomm.n2 _ _ _ | Nomm.n3 _ | Nomm.n4 _ | Nomm.n5 _ _ | Nomm.n7 _ _ | Nomm.n10 _ _ _
  | Nomm.n12 _ _ => trivial

/-! ## What the analysis adds to `RGood` -/

/-- **What the analysis adds to `RGood`** for `InvBSR`, of a result `out`
of `fol-loop` on `fol` and `sub`. -/
structure RGoodK (lib : Lib) (code : Bell → Option Nomm) (bus : Sock) (W : Cape) (fol : Noun)
    (sub : Anno) (out : FolOut) : Prop where
  annot : AnnotK lib code (RSub bus W sub) fol out.nomm
  detK : ∀ d, out.prod.sock = Sock.mk Cape.yes d →
    (∀ q, (distribute Cape.yes out.prod.src).Has q → W.Has q) → DetK (RSub bus W sub) out.nomm
  safK : out.saf = true → ∀ P, DetK P out.nomm
  kc : sub.sock ≠ Sock.void → out.prod.sock = Sock.void → KC out.nomm

/-- Every result of the recursion whose `want` `W` covers is `RGoodK`. -/
def GoRGoodK (lib : Lib) (code : Bell → Option Nomm) (bus : Sock) (W : Cape) (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') → WCov W gen' →
    RGoodK lib code bus W fol sub out

/-- No noun is reached from a `%void` subject. -/
theorem rsub_void {bus : Sock} {W : Cape} {sub : Anno} (h : sub.sock = Sock.void) :
    ∀ x, ¬ RSub bus W sub x := fun _ ⟨_, hz⟩ => hz.prov.nonvoid h

end AnnotSF
end SkaModel
end Formalization
