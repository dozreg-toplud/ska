import lemmas.Ska.AnnotS

/-!
# `InvBSR`: what the analysis must carry for the bake (track Q, README Gaps 27)

FINDING of step 1 (`tools/hoon/annots2.hoon`, real `%full` pokes): the bake
DOES leave droppable formula parts that are not literals.  The analysis joins
the branches of a `%6` by `+double-int` with provenance; the bake's `+know`
folds a read of a known part to a literal with NO provenance, so the same
join in the bake loses a part the analysis knew, and a call whose subject is
that join's product keeps the read `[%0 2]` as its formula part, which
passes `+safe-fol-fol`.  Case `%j2` is the shape of the brief: the analysis's
formula part is `[%6 [%5 [%1 0] [%1 0]] [%0 2] [%0 2]]` (fails
`+safe-fol-fol`), the bake folds the test and leaves `[%0 2]` (passes it).
`+inlined` drops it in both cases (the `inl.cache` entries).  The read never
fails: on 12 subjects that fit the root's code bell `+eval-top` equals
`+mink`.  Why it cannot fail: the analysis knew the read's product whole,
with its provenance in `want` (`RGood.sff` of the read, a `+safe-fol-fol`
nomm already in the analysis), and that fact is about every subject of
`RSub`, not only the bake's sock.

So `KnowOK` cannot give `AnnotS` from `Annot` alone (the code table's nomm
does not record the analysis's socks; with `Annot` only, the witness of
`invBS_false` is a counterexample).  The analysis must hand the bake, at
each direct call with no memo key, `DetK` of the formula part's nomm: every
read the bake could keep has its axis on every subject, through the
branches of `%6` (each branch on the whole set: the analysis does not refine
the subject by the test), a branch that never returns being one that keeps
a call (`KC`), which no bake turns into a `+safe-fol-fol` nomm.  Then the
bake's droppable parts have `SffOn` (`sffOn_of_detK` on the folded nomm,
`DetK.mono` for the smaller set) and `annot_sff_returns` gives `AnnotS`.

PROVED here: `DetK.mono`, `sffOn_of_detK`, `ret_of_detK`.
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock

/-- The nomm keeps a call under every bake: no `+know` output of it passes
`+safe-fol-fol` or `+safe-nomm`.  A `%6` keeps one if its test does (then it
is not folded) or both branches do. -/
def KC : Nomm → Prop
  | Nomm.n0 _ => False
  | Nomm.n1 _ => False
  | Nomm.n2 _ _ _ => True
  | Nomm.cons p q => KC p ∨ KC q
  | Nomm.n3 p => KC p
  | Nomm.n4 p => KC p
  | Nomm.n5 p q => KC p ∨ KC q
  | Nomm.n6 p q r => KC p ∨ (KC q ∧ KC r)
  | Nomm.n7 p q => KC p ∨ KC q
  | Nomm.n10 _ p q => KC p ∨ KC q
  | Nomm.n11s _ q _ => KC q
  | Nomm.n11d _ p q _ => KC p ∨ KC q
  | Nomm.mean p _ q _ _ => KC p ∨ KC q
  | Nomm.n12 p q => KC p ∨ KC q

/-- What the analysis knows of a formula part, as the bake needs it: each
read the bake may keep (through conses, hints and either branch of a `%6`)
has its axis on every subject of `P`.  A branch may instead keep a call.
Other forms either fold to a literal (sound by the fold) or stay and fail
`+safe-fol-fol`: nothing is asked of them. -/
def DetK (P : Noun → Prop) : Nomm → Prop
  | Nomm.n0 a => AxisIn P a
  | Nomm.n1 _ => True
  | Nomm.cons p q => DetK P p ∧ DetK P q
  | Nomm.n11s _ q _ => DetK P q
  | Nomm.n11d _ _ q _ => DetK P q
  | Nomm.mean _ _ q _ _ => DetK P q
  | Nomm.n6 _ q r => (DetK P q ∨ KC q) ∧ (DetK P r ∨ KC r)
  | Nomm.n2 _ _ _ => True
  | Nomm.n3 _ => True
  | Nomm.n4 _ => True
  | Nomm.n5 _ _ => True
  | Nomm.n7 _ _ => True
  | Nomm.n10 _ _ _ => True
  | Nomm.n12 _ _ => True

theorem AxisIn.mono {P Q : Noun → Prop} {a : Nat} (h : AxisIn P a) (hQ : ∀ x, Q x → P x) :
    AxisIn Q a := fun x hx => h x (hQ x hx)

/-- `DetK` holds on every smaller set (the bake's subjects are among the
analysis's). -/
theorem DetK.mono {P Q : Noun → Prop} (hQ : ∀ x, Q x → P x) : ∀ (n : Nomm), DetK P n → DetK Q n
  | Nomm.n0 _, h => AxisIn.mono h hQ
  | Nomm.n1 _, _ => trivial
  | Nomm.cons p q, h => ⟨DetK.mono hQ p h.1, DetK.mono hQ q h.2⟩
  | Nomm.n11s _ q _, h => DetK.mono hQ q h
  | Nomm.n11d _ _ q _, h => DetK.mono hQ q h
  | Nomm.mean _ _ q _ _, h => DetK.mono hQ q h
  | Nomm.n6 _ q r, h =>
    ⟨match h.1 with
      | Or.inl d => Or.inl (DetK.mono hQ q d)
      | Or.inr k => Or.inr k,
     match h.2 with
      | Or.inl d => Or.inl (DetK.mono hQ r d)
      | Or.inr k => Or.inr k⟩
  | Nomm.n2 _ _ _, _ | Nomm.n3 _, _ | Nomm.n4 _, _ | Nomm.n5 _ _, _ | Nomm.n7 _ _, _
  | Nomm.n10 _ _ _, _ | Nomm.n12 _ _, _ => trivial

/-- On a `+safe-fol-fol` nomm `DetK` is `SffOn` (the dynamic clue and the
trap of `%mean` pass `+safe-nomm`, which needs nothing). -/
theorem sffOn_of_detK {P : Noun → Prop} : ∀ {n : Nomm}, safeFolFol n = true → DetK P n → SffOn P n
  | Nomm.n0 _, _, h => h
  | Nomm.n1 _, _, _ => trivial
  | Nomm.cons p q, hs, h => by
    simp only [safeFolFol, Bool.and_eq_true] at hs
    exact ⟨sffOn_of_detK hs.1 h.1, sffOn_of_detK hs.2 h.2⟩
  | Nomm.n11s _ q _, hs, h => by
    simp only [safeFolFol, Bool.and_eq_true] at hs
    exact sffOn_of_detK (n := q) hs.2 h
  | Nomm.n11d _ _ q _, hs, h => by
    simp only [safeFolFol, Bool.and_eq_true] at hs
    exact sffOn_of_detK (n := q) hs.2 h
  | Nomm.mean _ _ q _ _, hs, h => by
    simp only [safeFolFol, Bool.and_eq_true] at hs
    exact sffOn_of_detK (n := q) hs.2 h
  | Nomm.n2 _ _ _, hs, _ | Nomm.n3 _, hs, _ | Nomm.n4 _, hs, _ | Nomm.n5 _ _, hs, _
  | Nomm.n6 _ _ _, hs, _ | Nomm.n7 _ _, hs, _ | Nomm.n10 _ _ _, hs, _ | Nomm.n12 _ _, hs, _ => by
    simp [safeFolFol] at hs

/-- The return the extra premise of `AnnotS.direct` asks for, from `DetK`
of the (folded) formula part on the call's set. -/
theorem ret_of_detK {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {f : Noun} {q : Nomm}
    (h : Annot lib code P f q) (hs : safeFolFol q = true) (hd : DetK P q) :
    ∀ x gul, P x → ∃ g, Mink lib gul [] x f (Tone.zero g) :=
  annot_sff_returns h hs (sffOn_of_detK hs hd)

end AnnotSF
end SkaModel
end Formalization
