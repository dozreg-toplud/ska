import lemmas.Ska.CompHintTree

/-!
# The kind of a part under hints not kept (README Gaps 24.13)

The composition lemmas take of each part its `kind`: call-free with `MinkEq`,
or hinted.  A pure formula under a hint that is not kept (`[11 %foo [4 [0
3]]]`) is neither: it is not `Nomm.pure`, and `+hinted` of it is `|`.  What
the lemmas read of the first branch is only that `+past` returns its need
(`pastL_pure`) and `TotalC` (`totalC_of_minkEq`); both hold for any nomm
whose `+hinted` is `|` and whose formula never pushes a frame and returns
or crashes with the trace as it is.  So:

* `pastL_unhinted`: `+past` returns its need when `+hinted` is `|`.
* `KindU`: `(hinted = some false ∧ TotalC) ∨ hinted = some true`; it follows
  from the old kind (`KindU.of_kind`) and from `MinkEq` against any nomm, the
  one with the hints erased included (`KindU.of_minkEq`).
* `TotalC` of `[11 tag f]` (`totalC_minkAs`), of `[11 [tag h] f]` with a safe
  clue (`totalC_minkAsP`), of a cons, `[7 p q]`, `[4 p]`, `[3 p]`, `[5 p q]`
  from their parts.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+past` returns its need behind a nomm that is not hinted**, pure or not. -/
theorem pastL_unhinted (cod : Bell → Option Bool) (nex : NextL S) {nom : Nomm} (h : hinted cod nom = some false)
    (region : List Nat) : (pastL cod nex nom region : CM Map (NextL S)) = pure nex := by
  unfold pastL
  simp only [h]
  split <;> rfl

/-- **The kind of a part** for the class with hints around pure formulas. -/
abbrev KindU (lib : Lib) (cod : Bell → Option Bool) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  (hinted cod nm = some false ∧ TotalC lib P f) ∨ hinted cod nm = some true

theorem KindU.of_kind {lib : Lib} {cod : Bell → Option Bool} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : (nm.pure = true ∧ MinkEq lib P f nm) ∨ hinted cod nm = some true) : KindU lib cod P f nm :=
  h.elim (fun ⟨hp, M⟩ => Or.inl ⟨hinted_pure cod nm hp, totalC_of_minkEq M⟩) Or.inr

/-- `MinkEq` against any nomm `e` (the nomm with the hints not kept erased)
gives the first branch. -/
theorem KindU.of_minkEq {lib : Lib} {cod : Bell → Option Bool} {P : Noun → Prop} {f : Noun} {nm e : Nomm}
    (hh : hinted cod nm = some false) (M : MinkEq lib P f e) : KindU lib cod P f nm :=
  Or.inl ⟨hh, totalC_of_minkEq M⟩

/-! ## `TotalC` of the composites -/

section
variable {lib : Lib}

theorem two_of_total {r : Tone} {tm : Trace} (h : r = Tone.two tm ∨ ∃ y, r = Tone.zero y)
    (hn : ∀ q, r ≠ Tone.zero q) : r = Tone.two tm :=
  h.elim id fun ⟨y, e⟩ => absurd e (hn y)

theorem two_ne_zero' (tm : Trace) : ∀ q, Tone.two tm ≠ Tone.zero q := fun _ h => by cases h

theorem totalC_minkAs {P : Noun → Prop} {f' f : Noun} (M : MinkAs lib f' f) (T : TotalC lib P f) :
    TotalC lib P f' :=
  ⟨fun s gul n tm r hP h => by obtain ⟨n', -, h'⟩ := M.fwd h; exact T.1 s gul n' tm r hP h',
   fun s gul tm hP => by obtain ⟨r, hm, hr⟩ := T.2 s gul tm hP; exact ⟨r, M.bwd hm, hr⟩⟩

theorem totalC_minkAsP {P : Noun → Prop} {f' f : Noun} (M : MinkAsP lib P f' f) (T : TotalC lib P f) :
    TotalC lib P f' :=
  ⟨fun s gul n tm r hP h => by obtain ⟨n', -, h'⟩ := M.fwd hP h; exact T.1 s gul n' tm r hP h',
   fun s gul tm hP => by obtain ⟨r, hm, hr⟩ := T.2 s gul tm hP; exact ⟨r, M.bwd hP hm, hr⟩⟩

theorem totalC_cons {P : Noun → Prop} {fh ft : Noun} (hfh : ∃ a b, fh = C a b) (Th : TotalC lib P fh)
    (Tt : TotalC lib P ft) : TotalC lib P (C fh ft) := by
  refine ⟨fun s gul n tm r hP h => ?_, fun s gul tm hP => ?_⟩
  · obtain ⟨n', -, rh, e1, h1⟩ := minkF_consG hfh h
    rcases h1 with ⟨hn, rfl⟩ | ⟨x, rfl, rt, e2, h2⟩
    · exact Or.inl (two_of_total (Th.1 s gul n' tm _ hP e1) hn)
    · rcases h2 with ⟨hn, rfl⟩ | ⟨y, rfl, rfl⟩
      · exact Or.inl (two_of_total (Tt.1 s gul n' tm _ hP e2) hn)
      · exact Or.inr ⟨_, rfl⟩
  · obtain ⟨rh, Mh, hh⟩ := Th.2 s gul tm hP
    have B := mink_consG_bwd (ft := ft) hfh Mh
    rcases hh with rfl | ⟨x, rfl⟩
    · exact ⟨_, B.1 (two_ne_zero' tm), Or.inl rfl⟩
    · obtain ⟨rt, Mt, ht⟩ := Tt.2 s gul tm hP
      rcases ht with rfl | ⟨y, rfl⟩
      · exact ⟨_, (B.2 x _ rfl Mt).1 (two_ne_zero' tm), Or.inl rfl⟩
      · exact ⟨_, (B.2 x _ rfl Mt).2 y _ rfl rfl, Or.inr ⟨_, rfl⟩⟩

theorem totalC_seven {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc) (Tb : TotalC lib P fb)
    (Tc : TotalC lib (Img lib P fb) fc) : TotalC lib P f := by
  refine ⟨fun s gul n tm r hP h => ?_, fun s gul tm hP => ?_⟩
  · obtain ⟨n1, -, rb, e1, h1⟩ := M.fwd hP h
    rcases h1 with ⟨hn, rfl⟩ | ⟨u, rfl, n2, -, e2⟩
    · exact Or.inl (two_of_total (Tb.1 s gul n1 tm _ hP e1) hn)
    · exact Tc.1 u gul n2 tm r (img_of hP e1) e2
  · obtain ⟨rb, Mb, hb⟩ := Tb.2 s gul tm hP
    have B := M.bwd hP Mb
    rcases hb with rfl | ⟨u, rfl⟩
    · exact ⟨_, B.1 (two_ne_zero' tm), Or.inl rfl⟩
    · obtain ⟨n1, e1⟩ := Mb
      obtain ⟨r, Mc, hc⟩ := Tc.2 u gul tm (img_of hP e1)
      exact ⟨r, B.2 u r rfl Mc, hc⟩

theorem totalC_four {P : Noun → Prop} {f fb : Noun} (M : MinkC4 lib P f fb) (Tb : TotalC lib P fb) :
    TotalC lib P f := by
  have K : ∀ {tm : Trace} {rb : Tone}, (rb = Tone.two tm ∨ ∃ y, rb = Tone.zero y) →
      (incTone tm rb = Tone.two tm ∨ ∃ y, incTone tm rb = Tone.zero y) := fun {tm rb} h => by
    rcases h with rfl | ⟨y, rfl⟩
    · exact Or.inl rfl
    · cases y with
      | atom a => exact Or.inr ⟨_, rfl⟩
      | cell _ _ => exact Or.inl rfl
  refine ⟨fun s gul n tm r hP h => ?_, fun s gul tm hP => ?_⟩
  · obtain ⟨n', -, rb, e1, rfl⟩ := M.fwd hP h
    exact K (Tb.1 s gul n' tm _ hP e1)
  · obtain ⟨rb, Mb, hb⟩ := Tb.2 s gul tm hP
    exact ⟨_, M.bwd hP Mb, K hb⟩

theorem totalC_three {P : Noun → Prop} {f fb : Noun} (M : MinkC3 lib P f fb) (Tb : TotalC lib P fb) :
    TotalC lib P f := by
  have K : ∀ {tm : Trace} {rb : Tone}, (rb = Tone.two tm ∨ ∃ y, rb = Tone.zero y) →
      (wutTone rb = Tone.two tm ∨ ∃ y, wutTone rb = Tone.zero y) := fun {tm rb} h => by
    rcases h with rfl | ⟨y, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  refine ⟨fun s gul n tm r hP h => ?_, fun s gul tm hP => ?_⟩
  · obtain ⟨n', -, rb, e1, rfl⟩ := M.fwd hP h
    exact K (Tb.1 s gul n' tm _ hP e1)
  · obtain ⟨rb, Mb, hb⟩ := Tb.2 s gul tm hP
    exact ⟨_, M.bwd hP Mb, K hb⟩

theorem totalC_five {P : Noun → Prop} {f fb fc : Noun} (M : MinkC5 lib P f fb fc) (Tb : TotalC lib P fb)
    (Tc : TotalC lib P fc) : TotalC lib P f := by
  refine ⟨fun s gul n tm r hP h => ?_, fun s gul tm hP => ?_⟩
  · obtain ⟨n', -, rb, e1, h1⟩ := M.fwd hP h
    rcases h1 with ⟨hn, rfl⟩ | ⟨x, rfl, rc, e2, h2⟩
    · exact Or.inl (two_of_total (Tb.1 s gul n' tm _ hP e1) hn)
    · rcases h2 with ⟨hn, rfl⟩ | ⟨y, rfl, rfl⟩
      · exact Or.inl (two_of_total (Tc.1 s gul n' tm _ hP e2) hn)
      · exact Or.inr ⟨_, rfl⟩
  · obtain ⟨rb, Mb, hb⟩ := Tb.2 s gul tm hP
    have B := M.bwd hP Mb
    rcases hb with rfl | ⟨x, rfl⟩
    · exact ⟨_, B.1 (two_ne_zero' tm), Or.inl rfl⟩
    · obtain ⟨rc, Mc, hc⟩ := Tc.2 s gul tm hP
      rcases hc with rfl | ⟨y, rfl⟩
      · exact ⟨_, (B.2 x _ rfl Mc).1 (two_ne_zero' tm), Or.inl rfl⟩
      · exact ⟨_, (B.2 x _ rfl Mc).2 y rfl, Or.inr ⟨_, rfl⟩⟩

end

end Comp
end SkaModel
end Formalization
