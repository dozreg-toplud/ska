import lemmas.Glue.Inline
import lemmas.Ska.FolLoopFacts
import lemmas.Ska.CompHypOf

/-!
# The model half of `inlAnnot` (LEDGER 2.e)

`inlAnnot` asks that the nomm of `+inlined` stand for the bell's formula:
`Annot lib (realOf code) (Fits b.less) b.fol nm`.  With the model
`inlinedM` (`Glue/Inline.lean`, checked against the real `+inlined`), the
field splits into a pill half (`D.inl` is `inlinedM`) and a model half,
proved here.

FINDING (a hypothesis `Annot` does not carry).  An inlined call drops the
call's formula part `q`, so `Annot.inline` asks that `q` RETURN on every
subject of `P`.  `Annot.direct` only says that `q`, when it returns, returns
the callee's formula.  `+safe-fol-fol q` does not give the return: it admits
`[%0 a]`, which crashes on a subject without the axis `a` (the Hoon's comment:
"all executable code is required to be present in the subject", a fact of the
analysis's sock, not of `Annot`).  So the model half is NOT provable from
`CodeOK`: on a table whose entry has a direct call with `q = [0 a]` and
subjects in `P` without the axis, the inlined nomm returns where the formula
crashes.  Witness (argued, not written in Lean): `c` with `fol = [1 0]`,
nomm `[%1 0]`; `b` knowing nothing, `fol = [7 b' [2 [0 1] [0 7]]]` with
`b' = [6 [3 0 1] [1 0 0 1 0] [1 5]]`, nomm `[%7 p [%2 [%0 1] [%0 7] [~ c ~]]]`.
`CodeOK` holds (`Annot.n7`, then `Annot.direct` on `Img = {[0 0 1 0], 5}`:
`[0 7]` returns `[1 0]` or crashes), `inlinedM` gives `[%7 p [%7 [%0 1]
[%1 0]]]`, which returns `0` on an atom subject where the formula crashes, so
no `Annot` of it can hold (`nomm_agree`).  The real analysis does not make
this call direct (the sock of `b'`'s product is the join, which does not
know axis `7`), which is what `AnnotS` records.  It is provable from `CodeOKS`, the same table invariant with
`AnnotS`: `Annot` whose `direct` case also carries, when the memo key is
`none` and `+safe-fol-fol q` holds, that `q` returns on every subject of
`P` (the analysis knows the formula from the sock, so the axes `q` reads are
in every subject the sock admits).  `AnnotS.toAnnot` forgets it.

PROVED:
* `inlWalk_annot`: the walk of `+inlined` over a nomm with `AnnotS` gives a
  nomm with `Annot`, when every callee nomm `go` returns has `Annot` at the
  callee's sock (one induction on the `AnnotS` derivation; the copy is
  structural, so every constructor is rebuilt from the copied children, and a
  direct call that becomes `[%7 p' m]` is `Annot.inline`, with `m`'s `Annot`
  restricted by `Annot.mono` along `Img lib P b ⊆ Fits c.less`);
* `inlinedM_annot`: `CodeOKS` gives `Annot` of every result of `inlinedM`, at
  every fuel (induction on the fuel: the callee chain), whatever `calls`,
  `hot`, `single` are (the tests of line 3339 to 3345 are not needed for
  soundness, only `k = none` and `+safe-fol-fol`, through `CodeOKS`);
* `inlAnnot_of`: the field `inlAnnot` of `CompRest` from the pill half
  `InlPill` and the analysis half `InvBS` (the table of every `InvB` state
  meets `CodeOKS`).
-/

namespace Formalization
namespace SkaModel
namespace Glue

open Nock

/-- **`Annot` with the return of the formula part at a direct call** that
`+inlined` may drop (memo key `none`, `+safe-fol-fol q`).  Every other
constructor is `Annot`'s. -/
inductive AnnotS (lib : Lib) (code : Bell → Option Nomm) : (Noun → Prop) → Noun → Nomm → Prop where
  | cons {P a1 a2 b p q} : AnnotS lib code P (C a1 a2) p → AnnotS lib code P b q →
      AnnotS lib code P (C (C a1 a2) b) (Nomm.cons p q)
  | n0 {P axis} : AnnotS lib code P (slot axis) (Nomm.n0 axis)
  | n1 {P k} : AnnotS lib code P (quote k) (Nomm.n1 k)
  | indirect {P b c p q} : AnnotS lib code P b p → AnnotS lib code P c q →
      AnnotS lib code P (n3 (A 2) b c) (Nomm.n2 p q none)
  | direct {P b c p q bl k nb} : AnnotS lib code P b p → AnnotS lib code P c q →
      code bl = some nb →
      (∀ x gul y, P x → Mink lib gul [] x b (Tone.zero y) → Fits bl.less y) →
      (∀ x gul g, P x → Mink lib gul [] x c (Tone.zero g) → g = bl.fol) →
      (k = none → safeFolFol q = true → ∀ x gul, P x → ∃ g, Mink lib gul [] x c (Tone.zero g)) →
      AnnotS lib code P (n3 (A 2) b c) (Nomm.n2 p q (some (bl, k)))
  | inline {P b c g p q} : AnnotS lib code P b p →
      (∀ x gul, P x → Mink lib gul [] x c (Tone.zero g)) →
      AnnotS lib code (Img lib P b) g q →
      AnnotS lib code P (n3 (A 2) b c) (Nomm.n7 p q)
  | n3 {P b p} : AnnotS lib code P b p → AnnotS lib code P (n2 (A 3) b) (Nomm.n3 p)
  | n4 {P b p} : AnnotS lib code P b p → AnnotS lib code P (n2 (A 4) b) (Nomm.n4 p)
  | n5 {P b c p q} : AnnotS lib code P b p → AnnotS lib code P c q →
      AnnotS lib code P (n3 (A 5) b c) (Nomm.n5 p q)
  | n6 {P b c d p q r} : AnnotS lib code P b p → AnnotS lib code P c q → AnnotS lib code P d r →
      AnnotS lib code P (n4 (A 6) b c d) (Nomm.n6 p q r)
  | n7 {P b c p q} : AnnotS lib code P b p → AnnotS lib code (Img lib P b) c q →
      AnnotS lib code P (n3 (A 7) b c) (Nomm.n7 p q)
  | n8 {P b c p q} : AnnotS lib code P b p → AnnotS lib code (Img8 lib P b) c q →
      AnnotS lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p (Nomm.n0 1)) q)
  | n9 {P axis c q r} : AnnotS lib code P c q →
      AnnotS lib code (Img lib P c) (n3 (A 2) (slot 1) (slot axis)) r →
      AnnotS lib code P (n3 (A 9) (A axis) c) (Nomm.n7 q r)
  | n10 {P axis v t p q} : axis ≠ 0 → AnnotS lib code P v p → AnnotS lib code P t q →
      AnnotS lib code P (n3 (A 10) (n2 (A axis) v) t) (Nomm.n10 axis p q)
  | n11s {P tag q f} : AnnotS lib code P f q →
      AnnotS lib code P (n3 (A 11) (A tag) f) (Nomm.n11s tag q f)
  | n11d {P tag h f p q} : AnnotS lib code P h p → AnnotS lib code P f q →
      AnnotS lib code P (n3 (A 11) (C (A tag) h) f) (Nomm.n11d tag p q f)
  | n11c {P x y h f p q} : AnnotS lib code P h p → AnnotS lib code P f q →
      AnnotS lib code P (n3 (A 11) (C (C x y) h) f) (Nomm.n11d 0 p q f)
  | mean {P h f p q b k} : AnnotS lib code P h p → AnnotS lib code P f q →
      AnnotS lib code P (n3 (A 11) (C (A Tag.mean) h) f) (Nomm.mean p b q f k)
  | n12 {P b c p q} : AnnotS lib code P b p → AnnotS lib code P c q →
      AnnotS lib code P (n3 (A 12) b c) (Nomm.n12 p q)
  | bare {P f} : isBare f = true → AnnotS lib code P f (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) none)
  | memo {P h f nm} : (∀ x gul, P x → ∃ c, Mink lib gul [] x h (Tone.zero c)) →
      AnnotS lib code P (n3 (A 2) (slot 1) (quote f)) nm →
      AnnotS lib code P (n3 (A 11) (C (A Tag.memo) h) f) nm
  | crash {P f} : CrashesAtOnce lib f → AnnotS lib code P f (Nomm.n0 0)
  | fold {P f v} : (∀ x gul, P x → Mink lib gul [] x f (Tone.zero v)) → AnnotS lib code P f (Nomm.n1 v)
  | six0 {P b c d q} : (∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A 0))) → AnnotS lib code P c q →
      AnnotS lib code P (n4 (A 6) b c d) q
  | six1 {P b c d r} : (∀ x gul, P x → Mink lib gul [] x b (Tone.zero (A 1))) → AnnotS lib code P d r →
      AnnotS lib code P (n4 (A 6) b c d) r
  | n8g {P b c p r q} : AnnotS lib code P b p → AnnotS lib code P (slot 1) r →
      AnnotS lib code (Img8 lib P b) c q →
      AnnotS lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p r) q)
  | n8l {P b c y d q} : (∀ x gul, P x → Mink lib gul [] x b (Tone.zero y) ∧ x = d) →
      AnnotS lib code (Img8 lib P b) c q →
      AnnotS lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.n1 (C y d)) q)
  | bareLit {P f d} : isBare f = true → (∀ x, P x → x = d) →
      AnnotS lib code P f (Nomm.n2 (Nomm.n1 d) (Nomm.n1 f) none)

/-- The table invariant with `AnnotS`. -/
def CodeOKS (lib : Lib) (code : Bell → Option Nomm) : Prop :=
  ∀ bl nb, code bl = some nb → AnnotS lib code (Fits bl.less) bl.fol nb

/-- `AnnotS` forgets to `Annot`. -/
theorem AnnotS.toAnnot {lib : Lib} {code : Bell → Option Nomm} {P f nm}
    (h : AnnotS lib code P f nm) : Annot lib code P f nm := by
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

theorem CodeOKS.toCodeOK {lib : Lib} {code : Bell → Option Nomm} (h : CodeOKS lib code) :
    CodeOK lib code := fun bl nb hb => (h bl nb hb).toAnnot

section walk
variable {lib : Lib} {code : Bell → Option Nomm} {calls : Bell → Bell → Bool} {hot single : Bell → Bool}
  {go : Bell → Option Nomm}

/-- What the callee recursion `go` must give: `Annot` at the callee's sock. -/
def GoOK (lib : Lib) (code : Bell → Option Nomm) (go : Bell → Option Nomm) : Prop :=
  ∀ c m, go c = some m → Annot lib code (Fits c.less) c.fol m

/-- **The walk of `+inlined` keeps the annotation.** -/
theorem inlWalk_annot (hgo : GoOK lib code go) {P f nm} (h : AnnotS lib code P f nm) :
    ∀ {nm'}, inlWalk calls hot single go nm = some nm' → Annot lib code P f nm' := by
  induction h with
  | cons _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.cons (i1 ha) (i2 hd)
  | n0 => intro nm' e; simp only [inlWalk, Option.some.injEq] at e; subst e; exact Annot.n0
  | n1 => intro nm' e; simp only [inlWalk, Option.some.injEq] at e; subst e; exact Annot.n1
  | indirect _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.indirect (i1 ha) (i2 hd)
  | @direct P b c p q bl k nb _ _ hc hy hg hret i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff] at e
    obtain ⟨a, ha, d, hd, e⟩ := e
    have keep : Annot lib code P (n3 (A 2) b c) (Nomm.n2 a d (some (bl, k))) :=
      Annot.direct (i1 ha) (i2 hd) hc hy hg
    by_cases hok : inlOK calls hot single bl k q = true
    · rw [if_pos hok, Option.bind_eq_some_iff] at e
      obtain ⟨m, hm, e⟩ := e
      simp only [Option.some.injEq] at e
      subst e
      by_cases hs : inlineMax < nommSize 0 m
      · rw [if_pos hs]; exact keep
      · rw [if_neg hs]
        simp only [inlOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
        obtain ⟨⟨⟨⟨hk, hq⟩, -⟩, -⟩, -⟩ := hok
        have hk' : k = none := Option.isNone_iff_eq_none.mp hk
        refine Annot.inline (g := bl.fol) (i1 ha) (fun x gul hx => ?_) ?_
        · obtain ⟨g, hmg⟩ := hret hk' hq x gul hx
          have := hg x gul g hx hmg
          subst this
          exact hmg
        · exact (hgo bl m hm).mono (fun y ⟨x, gul, hx, hmy⟩ => hy x gul y hx hmy)
    · rw [if_neg hok, Option.some.injEq] at e
      subst e; exact keep
  | inline _ ht _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.inline (i1 ha) ht (i2 hd)
  | n3 _ i =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, rfl⟩ := e
    exact Annot.n3 (i ha)
  | n4 _ i =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, rfl⟩ := e
    exact Annot.n4 (i ha)
  | n5 _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n5 (i1 ha) (i2 hd)
  | n6 _ _ _ i1 i2 i3 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, r, hr, rfl⟩ := e
    exact Annot.n6 (i1 ha) (i2 hd) (i3 hr)
  | n7 _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n7 (i1 ha) (i2 hd)
  | n8 _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ⟨a1, ha1, a2, ha2, rfl⟩, d, hd, rfl⟩ := e
    cases ha2
    exact Annot.n8 (i1 ha1) (i2 hd)
  | n9 _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n9 (i1 ha) (i2 hd)
  | n10 hax _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n10 hax (i1 ha) (i2 hd)
  | n11s _ i =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, rfl⟩ := e
    exact Annot.n11s (i ha)
  | n11d _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n11d (i1 ha) (i2 hd)
  | n11c _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n11c (i1 ha) (i2 hd)
  | mean _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.mean (i1 ha) (i2 hd)
  | n12 _ _ i1 i2 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ha, d, hd, rfl⟩ := e
    exact Annot.n12 (i1 ha) (i2 hd)
  | bare hb =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, rfl, d, rfl, rfl⟩ := e
    exact Annot.bare hb
  | memo hh _ i => intro nm' e; exact Annot.memo hh (i e)
  | crash hc => intro nm' e; simp only [inlWalk, Option.some.injEq] at e; subst e; exact Annot.crash hc
  | fold hf => intro nm' e; simp only [inlWalk, Option.some.injEq] at e; subst e; exact Annot.fold hf
  | six0 hb _ i => intro nm' e; exact Annot.six0 hb (i e)
  | six1 hb _ i => intro nm' e; exact Annot.six1 hb (i e)
  | n8g _ _ _ i1 i2 i3 =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, ⟨a1, ha1, a2, ha2, rfl⟩, d, hd, rfl⟩ := e
    exact Annot.n8g (i1 ha1) (i2 ha2) (i3 hd)
  | n8l hb _ i =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, rfl, d, hd, rfl⟩ := e
    exact Annot.n8l hb (i hd)
  | bareLit hb hd =>
    intro nm' e
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨a, rfl, d, rfl, rfl⟩ := e
    exact Annot.bareLit hb hd

end walk

/-- **The model half of `inlAnnot`** (`InlAnnotM`, LEDGER 2.e): on a table
with `CodeOKS`, every result of `inlinedM` stands for its bell's formula on
the bell's sock, at every fuel and for every `calls`, `hot`, `single`. -/
theorem inlinedM_annot {lib : Lib} {code : Bell → Option Nomm} (hS : CodeOKS lib code)
    (calls : Bell → Bell → Bool) (hot single : Bell → Bool) :
    ∀ fuel, GoOK lib code (inlinedM code calls hot single fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c m h; simp [inlinedM] at h
  | succ f ih =>
    intro c m h
    simp only [inlinedM, Option.bind_eq_some_iff] at h
    obtain ⟨nb, hnb, hw⟩ := h
    exact inlWalk_annot ih (hS c nb hnb) hw

/-! ## The field `inlAnnot` from its two halves -/

open Ana Bake PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H : Type}

/-- **The pill half** (no owner): the nomm `D.inl` of `+inlined` is
`inlinedM` on the code table, for some fuel, `calls`, `hot`, `single` (the
Hoon's: `calls.long-ska`, the rings with a driver in `jets-hot`, the
singleton test of `+scc-of`), on every `InvB` state. -/
def InlPill (lib : Lib) (D : CompData M Map J H) : Prop :=
  ∀ long jets hot b nm, InvB lib long → D.inl long jets hot b = some nm →
    ∃ fuel calls hotf single, inlinedM (realOf long.code) calls hotf single fuel b = some nm

/-- **The analysis half** (a leaf of the analysis): the code table of every
`InvB` state meets `CodeOKS` (`InvB.codeOK` with `AnnotS`: at every direct
call with no memo key and a `+safe-fol-fol` formula part, that part returns
on every subject). -/
def InvBS (M : Type → Type → Type) [Treap M] (lib : Lib) : Prop :=
  ∀ long : LongB M, InvB lib long → CodeOKS lib (realOf long.code)

/-- **`inlAnnot` from the two halves.** -/
theorem inlAnnot_of {lib : Lib} {D : CompData M Map J H} (hP : InlPill lib D) (hS : InvBS M lib) :
    ∀ long jets hot b nm, InvB lib long → D.inl long jets hot b = some nm →
      Annot lib (realOf long.code) (Fits b.less) b.fol nm := by
  intro long jets hot b nm hI hinl
  obtain ⟨fuel, calls, hotf, single, h⟩ := hP long jets hot b nm hI hinl
  exact inlinedM_annot (hS long hI) calls hotf single fuel b nm h

end Glue
end SkaModel
end Formalization
