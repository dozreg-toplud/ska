import lemmas.Ska.AnnotSBase

/-!
# `+know` keeps `KC` and `DetK`, and gives `AnnotS` (track Q, README Gaps 27)

`knowGo_kc`: a nomm that keeps a call keeps it under `+know` (every fold
needs a literal or a `+safe-nomm` part, which `KC` fails: `KC.not_safe`).
`knowGo_detKC`: `DetK ∨ KC` is kept (`DetK` alone is NOT: a `%6` whose test
folds takes its branch, and a branch may be `KC` without `DetK`, e.g.
`[[2 ..] [0 5]]` with an axis `5` that is missing).

FINDING: so `+know` cannot give `AnnotK` of its output (the extra premise of
`AnnotK.direct` is `DetK` of the folded formula part, which may be `KC`
instead), and the copy of `knowGo_sound` gives `AnnotS` (`KnowOKK`): at a
direct call with no memo key whose folded formula part passes
`+safe-fol-fol`, that part is `DetK` (it is not `KC`, by `KC.not_safe`), and
`ret_of_detK` gives its return.  The input is `AnnotK`.
-/

namespace Formalization
namespace SkaModel

open Nock AnnotSF

namespace Bake

theorem kc_lit {n : Nomm} (h : KC n) : lit n = none := by
  cases n <;> first | rfl | exact h.elim

theorem kc_safe {n : Nomm} (h : KC n) : safeNomm n = false := (KC.not_safe h).1

section Pure

variable {fold : Bool} {dat : Bell → Option Datum} {res : Bell → Sock → Option Bell}

theorem kc_go {fold : Bool} {dat : Bell → Option Datum} {res : Bell → Sock → Option Bell} :
    ∀ {nm : Nomm} {sub : Anno} {st : List Site} {r : (Nomm × Anno) × List Site},
    knowGo fold dat res nm sub st = some r → KC nm → KC r.1.1
  | Nomm.n0 _, _, _, _, _, hk => hk.elim
  | Nomm.n1 _, _, _, _, _, hk => hk.elim
  | Nomm.cons p q, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r', hr, h⟩ := h
    split at h
    · rename_i x y hx hy
      rcases hk with hk | hk
      · rw [kc_lit (kc_go hl hk)] at hx; cases hx
      · rw [kc_lit (kc_go hr hk)] at hy; cases hy
    · cases h
      rcases hk with hk | hk
      · exact Or.inl (kc_go hl hk)
      · exact Or.inr (kc_go hr hk)
  | Nomm.n2 p q info, sub, st, r, h, _ => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, f, hf, h⟩ := h
    split at h
    · cases h; trivial
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, rfl⟩ := h
      trivial
  | Nomm.n3 p, sub, st, r, h, hk => by
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have k1 := kc_go hp hk
    split at h
    · rename_i hs; rw [kc_safe k1] at hs; cases hs
    · subst h; exact k1
  | Nomm.n4 p, sub, st, r, h, hk => by
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have k1 := kc_go hp hk
    split at h
    · rename_i hs; rw [kc_safe k1] at hs; cases hs
    · subst h; exact k1
  | Nomm.n5 p q, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, h⟩ := h
    split at h
    · rename_i hs1 _ hs2
      rcases hk with hk | hk
      · rw [kc_safe (kc_go hp hk)] at hs1; cases hs1
      · rw [kc_safe (kc_go hq hk)] at hs2; cases hs2
    · subst h
      rcases hk with hk | hk
      · exact Or.inl (kc_go hp hk)
      · exact Or.inr (kc_go hq hk)
  | Nomm.n6 p q r0, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    split at h
    · rename_i hs
      rcases hk with hk | hk
      · rw [kc_safe (kc_go hp hk)] at hs; cases hs
      · exact kc_go h hk.1
    · rename_i hs
      rcases hk with hk | hk
      · rw [kc_safe (kc_go hp hk)] at hs; cases hs
      · exact kc_go h hk.2
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨qq, hq, rr, hr, rfl⟩ := h
      rcases hk with hk | hk
      · exact Or.inl (kc_go hp hk)
      · exact Or.inr ⟨kc_go hq hk.1, kc_go hr hk.2⟩
  | Nomm.n7 p q, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, h⟩ := h
    split at h
    · rename_i hl hs
      rcases hk with hk | hk
      · rw [kc_safe (kc_go hp hk)] at hs; cases hs
      · rw [kc_lit (kc_go hq hk)] at hl; cases hl
    · subst h
      rcases hk with hk | hk
      · exact Or.inl (kc_go hp hk)
      · exact Or.inr (kc_go hq hk)
  | Nomm.n10 ax don rec, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨dn, hdn, rc, hrc, h⟩ := h
    have hn : ∀ x y, lit dn.1.1 = some x → lit rc.1.1 = some y → False := by
      intro x y h1 h2
      rcases hk with hk | hk
      · rw [kc_lit (kc_go hdn hk)] at h1; cases h1
      · rw [kc_lit (kc_go hrc hk)] at h2; cases h2
    split at h
    · rename_i u hu
      split at hu
      · rename_i x y h1 h2; exact (hn x y h1 h2).elim
      · cases hu
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s, _, rfl⟩ := h
      rcases hk with hk | hk
      · exact Or.inl (kc_go hdn hk)
      · exact Or.inr (kc_go hrc hk)
  | Nomm.n11s tag q body, sub, st, r, h, hk => by
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨qq, hq, h⟩ := h
    have k1 := kc_go hq hk
    split at h
    · rename_i hl; rw [kc_lit k1] at hl; cases hl
    · subst h; exact k1
  | Nomm.n11d tag hn q body, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨hh, hhh, qq, hq, h⟩ := h
    split at h
    · rename_i hs hl
      rcases hk with hk | hk
      · rw [kc_safe (kc_go hhh hk)] at hs; cases hs
      · rw [kc_lit (kc_go hq hk)] at hl; cases hl
    · subst h
      rcases hk with hk | hk
      · exact Or.inl (kc_go hhh hk)
      · exact Or.inr (kc_go hq hk)
  | Nomm.n12 p q, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, rfl⟩ := h
    rcases hk with hk | hk
    · exact Or.inl (kc_go hp hk)
    · exact Or.inr (kc_go hq hk)
  | Nomm.mean p b q body k, sub, st, r, h, hk => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, v, _, qq, hq, rfl⟩ := h
    rcases hk with hk | hk
    · exact Or.inl (kc_go hp hk)
    · exact Or.inr (kc_go hq hk)

/-- **`+know` keeps a call.** -/
theorem knowGo_kc {fold : Bool} {dat : Bell → Option Datum} {res : Bell → Sock → Option Bell}
    {nm : Nomm} {sub : Anno} {st : List Site} {r : (Nomm × Anno) × List Site}
    (hk : KC nm) (h : knowGo fold dat res nm sub st = some r) : KC r.1.1 := kc_go h hk

/-- `DetK` of a literal. -/
theorem detK_lit {P : Noun → Prop} {n : Nomm} {v : Noun} (h : lit n = some v) : DetK P n := by
  cases n <;> simp [lit] at h
  trivial

/-- **`+know` keeps `DetK` or a call** (`DetK` alone is not kept: a folded
`%6` takes a branch, which may keep a call instead). -/
theorem detK_go {fold : Bool} {dat : Bell → Option Datum} {res : Bell → Sock → Option Bell}
    {P : Noun → Prop} : ∀ {nm : Nomm} {sub : Anno} {st : List Site}
    {r : (Nomm × Anno) × List Site},
    knowGo fold dat res nm sub st = some r → DetK P nm → DetK P r.1.1 ∨ KC r.1.1
  | Nomm.n0 a, sub, st, r, h, hd => by
    simp only [knowGo] at h
    split at h
    · cases h; exact Or.inl hd
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨prod, _, h⟩ := h
      split at h
      · cases h; exact Or.inl trivial
      · cases h; exact Or.inl hd
  | Nomm.n1 _, sub, st, r, h, _ => by
    simp only [knowGo, Option.some.injEq] at h
    subst h; exact Or.inl trivial
  | Nomm.cons p q, sub, st, r, h, hd => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r', hr, h⟩ := h
    split at h
    · cases h; exact Or.inl trivial
    · cases h
      rcases detK_go hl hd.1 with d1 | k1
      · rcases detK_go hr hd.2 with d2 | k2
        · exact Or.inl ⟨d1, d2⟩
        · exact Or.inr (Or.inr k2)
      · exact Or.inr (Or.inl k1)
  | Nomm.n2 p q info, sub, st, r, h, _ => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, f, hf, h⟩ := h
    split at h
    · cases h; exact Or.inl trivial
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, rfl⟩ := h
      exact Or.inl trivial
  | Nomm.n3 p, sub, st, r, h, _ => by
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    split at h <;> (subst h; exact Or.inl trivial)
  | Nomm.n4 p, sub, st, r, h, _ => by
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    split at h <;> (subst h; exact Or.inl trivial)
  | Nomm.n5 p q, sub, st, r, h, _ => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, h⟩ := h
    split at h <;> (subst h; exact Or.inl trivial)
  | Nomm.n6 p q r0, sub, st, r, h, hd => by
    have comb : ∀ {n : Nomm} {sub : Anno} {st : List Site} {r : (Nomm × Anno) × List Site},
        (∀ {sub st r}, DetK P n → knowGo fold dat res n sub st = some r → DetK P r.1.1 ∨ KC r.1.1) →
        (DetK P n ∨ KC n) → knowGo fold dat res n sub st = some r → DetK P r.1.1 ∨ KC r.1.1 :=
      fun ih hdk h => hdk.elim (fun d => ih d h) (fun k => Or.inr (knowGo_kc k h))
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    split at h
    · exact comb (fun d h => detK_go h d) hd.1 h
    · exact comb (fun d h => detK_go h d) hd.2 h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨qq, hq, rr, hr, rfl⟩ := h
      exact Or.inl ⟨comb (fun d h => detK_go h d) hd.1 hq, comb (fun d h => detK_go h d) hd.2 hr⟩
  | Nomm.n7 p q, sub, st, r, h, _ => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, h⟩ := h
    split at h
    · rename_i hl _; subst h; exact Or.inl (detK_lit hl)
    · subst h; exact Or.inl trivial
  | Nomm.n10 ax don rec, sub, st, r, h, _ => by
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨dn, hdn, rc, hrc, h⟩ := h
    split at h
    · cases h; exact Or.inl trivial
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s, _, rfl⟩ := h
      exact Or.inl trivial
  | Nomm.n11s tag q body, sub, st, r, h, hd => by
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨qq, hq, h⟩ := h
    split at h
    · rename_i hl; subst h; exact Or.inl (detK_lit hl)
    · subst h; have := detK_go hq hd; exact this
  | Nomm.n11d tag hn q body, sub, st, r, h, hd => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨hh, hhh, qq, hq, h⟩ := h
    split at h
    · rename_i hl; subst h; exact Or.inl (detK_lit hl)
    · subst h
      rcases detK_go hq hd with d | k
      · exact Or.inl d
      · exact Or.inr (Or.inr k)
  | Nomm.n12 p q, sub, st, r, h, _ => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, rfl⟩ := h
    exact Or.inl trivial
  | Nomm.mean p b q body k, sub, st, r, h, hd => by
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, v, _, qq, hq, rfl⟩ := h
    rcases detK_go hq hd with d | k
    · exact Or.inl d
    · exact Or.inr (Or.inr k)

theorem knowGo_detK {fold : Bool} {dat : Bell → Option Datum} {res : Bell → Sock → Option Bell}
    {P : Noun → Prop} {nm : Nomm} {sub : Anno} {st : List Site} {r : (Nomm × Anno) × List Site}
    (hd : DetK P nm) (h : knowGo fold dat res nm sub st = some r) : DetK P r.1.1 ∨ KC r.1.1 :=
  detK_go h hd

/-- `DetK ∨ KC` is kept. -/
theorem knowGo_detKC {P : Noun → Prop} {nm : Nomm} {sub : Anno} {st : List Site}
    {r : (Nomm × Anno) × List Site} (hd : DetK P nm ∨ KC nm)
    (h : knowGo fold dat res nm sub st = some r) : DetK P r.1.1 ∨ KC r.1.1 :=
  hd.elim (fun d => knowGo_detK d h) (fun k => Or.inr (knowGo_kc k h))

/-- At a folded formula part that passes `+safe-fol-fol`: `DetK`. -/
theorem knowGo_detK_safe {P : Noun → Prop} {nm : Nomm} {sub : Anno} {st : List Site}
    {r : (Nomm × Anno) × List Site} (hd : DetK P nm)
    (h : knowGo fold dat res nm sub st = some r) (hs : safeFolFol r.1.1 = true) : DetK P r.1.1 := by
  rcases knowGo_detK hd h with d | k
  · exact d
  · rw [(KC.not_safe k).2] at hs; cases hs

end Pure

/-! ## `knowGo_sound` with `AnnotK` in and `AnnotS` out -/

section SoundK

variable {lib : Lib} {code code' : Bell → Option Nomm} {fold : Bool} {dat : Bell → Option Datum}
  {res : Bell → Sock → Option Bell} {stF : List Site}

/-- **What `+know` gives, with `AnnotS`**: the folded nomm stands for the
formula on `Q` with the table `code'`, with the return of each droppable
formula part, and the product sock fits every product of the original nomm. -/
def KnowOKK (lib : Lib) (code code' : Bell → Option Nomm) (Q : Noun → Prop) (f : Noun) (nm : Nomm)
    (out : Nomm × Anno) : Prop :=
  Glue.AnnotS lib code' Q f out.1 ∧
    ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x nm = some (Tone.zero y) → Fits out.2.sock y

theorem KnowOKK.toKnowOK {Q : Noun → Prop} {f : Noun} {nm : Nomm} {out : Nomm × Anno}
    (h : KnowOKK lib code code' Q f nm out) : KnowOK lib code code' Q f nm out := ⟨h.1.toAnnot, h.2⟩

theorem annot_safe_totalS {Q : Noun → Prop} {f : Noun} {n : Nomm} (h : Glue.AnnotS lib code Q f n) :
    safeNomm n = true → ∀ x gul, Q x → ∃ y, Mink lib gul [] x f (Tone.zero y) :=
  annot_safe_total h.toAnnot

theorem annot_litS {Q : Noun → Prop} {f : Noun} {n : Nomm} (h : Glue.AnnotS lib code Q f n) :
    ∀ v, n = Nomm.n1 v → ∀ x gul, Q x → Mink lib gul [] x f (Tone.zero v) :=
  annot_lit h.toAnnot

theorem nomm_minkK (hc : CodeOK lib code) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hA : AnnotK lib code P f nm) {x : Noun} (hx : P x) {gul : Noun} {t : Trace} {m : Nat} {y : Noun}
    (h : nommF lib gul code m t x nm = some (Tone.zero y)) : Mink lib gul [] x f (Tone.zero y) :=
  nomm_mink hc hA.toAnnot hx h

theorem mink_nommK (hc : CodeOK lib code) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hA : AnnotK lib code P f nm) {x : Noun} (hx : P x) {gul y : Noun}
    (h : Mink lib gul [] x f (Tone.zero y)) : ∃ m, nommF lib gul code m [] x nm = some (Tone.zero y) :=
  mink_nomm hc hA.toAnnot hx h

theorem lit_valK (hc : CodeOK lib code) {P Q : Noun → Prop} {f : Noun} {p : Nomm} {v : Noun}
    (hA : AnnotK lib code P f p) (hQP : ∀ x, Q x → P x) (hl : Glue.AnnotS lib code' Q f (Nomm.n1 v))
    {x gul : Noun} {t : Trace} {m : Nat} {y : Noun} (hx : Q x)
    (h : nommF lib gul code m t x p = some (Tone.zero y)) : y = v :=
  lit_val (code' := code') hc hA.toAnnot hQP hl.toAnnot hx h

theorem safe_knownK (hc : CodeOK lib code) {P Q : Noun → Prop} {b : Noun} {p : Nomm} {out : Nomm × Anno}
    {d : Noun} (hA : AnnotK lib code P b p) (hQP : ∀ x, Q x → P x) (hk : KnowOKK lib code code' Q b p out)
    (hs : safeNomm out.1 = true) (hkn : known out.2.sock = some d) :
    ∀ x gul, Q x → Mink lib gul [] x b (Tone.zero d) :=
  safe_known hc hA.toAnnot hQP hk.toKnowOK hs hkn

theorem knowGo_n0K {sub : Anno} {st : List Site} {axis : Nat} {r : (Nomm × Anno) × List Site}
    (h : knowGo fold dat res (Nomm.n0 axis) sub st = some r) {Q : Noun → Prop}
    (hQ : ∀ x, Q x → Fits sub.sock x) :
    r.2 = st ∧ KnowOKK lib code code' Q (slot axis) (Nomm.n0 axis) r.1 ∧
      (r.1.1 = Nomm.n0 axis ∨ ∃ d, r.1.1 = Nomm.n1 d ∧ ∀ x, Q x → slot? axis x = some d) := by
  obtain ⟨h1, K, h3⟩ := knowGo_n0 (lib := lib) (code := code) (code' := code') h hQ
  refine ⟨h1, ⟨?_, K.2⟩, h3⟩
  rcases h3 with e | ⟨d, e, hd⟩
  · rw [e]; exact Glue.AnnotS.n0
  · rw [e]; exact Glue.AnnotS.fold fun x gul hx => mink_mk_n0 (hd x hx)

-- BEGIN annots_know.py (tools/gen/annots_know.py)
/-- **`AnnotS` holds on fewer subjects.** -/
theorem _root_.Formalization.SkaModel.Glue.AnnotS.mono {lib : Lib} {code : Bell → Option Nomm} :
    ∀ {P f n}, Glue.AnnotS lib code P f n → ∀ {Q : Noun → Prop}, (∀ x, Q x → P x) → Glue.AnnotS lib code Q f n := by
  intro P f n h
  induction h with
  | cons _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.cons (ih1 hQ) (ih2 hQ)
  | n0 => intro Q _; exact Glue.AnnotS.n0
  | n1 => intro Q _; exact Glue.AnnotS.n1
  | indirect _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.indirect (ih1 hQ) (ih2 hQ)
  | direct _ _ hc hy hg hr ih1 ih2 =>
    intro Q hQ
    exact Glue.AnnotS.direct (ih1 hQ) (ih2 hQ) hc (fun x gul y hx => hy x gul y (hQ x hx))
      (fun x gul g hx => hg x gul g (hQ x hx)) (fun hk hs x gul hx => hr hk hs x gul (hQ x hx))
  | inline _ htot _ ih1 ih2 =>
    intro Q hQ
    exact Glue.AnnotS.inline (ih1 hQ) (fun x gul hx => htot x gul (hQ x hx)) (ih2 (Img_mono hQ))
  | n3 _ ih => intro Q hQ; exact Glue.AnnotS.n3 (ih hQ)
  | n4 _ ih => intro Q hQ; exact Glue.AnnotS.n4 (ih hQ)
  | n5 _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n5 (ih1 hQ) (ih2 hQ)
  | n6 _ _ _ ih1 ih2 ih3 => intro Q hQ; exact Glue.AnnotS.n6 (ih1 hQ) (ih2 hQ) (ih3 hQ)
  | n7 _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n7 (ih1 hQ) (ih2 (Img_mono hQ))
  | n8 _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n8 (ih1 hQ) (ih2 (Img8_mono hQ))
  | n9 _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n9 (ih1 hQ) (ih2 (Img_mono hQ))
  | n10 hax _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n10 hax (ih1 hQ) (ih2 hQ)
  | n11s _ ih => intro Q hQ; exact Glue.AnnotS.n11s (ih hQ)
  | n11d _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n11d (ih1 hQ) (ih2 hQ)
  | n11c _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n11c (ih1 hQ) (ih2 hQ)
  | mean _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.mean (ih1 hQ) (ih2 hQ)
  | n12 _ _ ih1 ih2 => intro Q hQ; exact Glue.AnnotS.n12 (ih1 hQ) (ih2 hQ)
  | bare hb => intro Q _; exact Glue.AnnotS.bare hb
  | memo hh _ ih =>
    intro Q hQ
    exact Glue.AnnotS.memo (fun x gul hx => hh x gul (hQ x hx)) (ih hQ)
  | crash hc => intro Q _; exact Glue.AnnotS.crash hc
  | fold hv => intro Q hQ; exact Glue.AnnotS.fold (fun x gul hx => hv x gul (hQ x hx))
  | six0 hb _ ih => intro Q hQ; exact Glue.AnnotS.six0 (fun x gul hx => hb x gul (hQ x hx)) (ih hQ)
  | six1 hb _ ih => intro Q hQ; exact Glue.AnnotS.six1 (fun x gul hx => hb x gul (hQ x hx)) (ih hQ)
  | n8g _ _ _ ih1 ih2 ih3 => intro Q hQ; exact Glue.AnnotS.n8g (ih1 hQ) (ih2 hQ) (ih3 (Img8_mono hQ))
  | n8l hb _ ih => intro Q hQ; exact Glue.AnnotS.n8l (fun x gul hx => hb x gul (hQ x hx)) (ih (Img8_mono hQ))
  | bareLit hb hd => intro Q hQ; exact Glue.AnnotS.bareLit hb (fun x hx => hd x (hQ x hx))

/-- `AnnotS` needs of the code table only that the bells it calls have a
nomm. -/
theorem _root_.Formalization.SkaModel.Glue.AnnotS.mono_code {lib : Lib} {code code' : Bell → Option Nomm}
    (hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb')
    {P : Noun → Prop} {f : Noun} {n : Nomm} (h : Glue.AnnotS lib code P f n) : Glue.AnnotS lib code' P f n := by
  induction h with
  | cons _ _ ih1 ih2 => exact Glue.AnnotS.cons ih1 ih2
  | n0 => exact Glue.AnnotS.n0
  | n1 => exact Glue.AnnotS.n1
  | indirect _ _ ih1 ih2 => exact Glue.AnnotS.indirect ih1 ih2
  | direct _ _ hb hl hf hr ih1 ih2 =>
    obtain ⟨nb', hb'⟩ := hcc _ _ hb
    exact Glue.AnnotS.direct ih1 ih2 hb' hl hf hr
  | inline _ hc _ ih1 ih2 => exact Glue.AnnotS.inline ih1 hc ih2
  | n3 _ ih => exact Glue.AnnotS.n3 ih
  | n4 _ ih => exact Glue.AnnotS.n4 ih
  | n5 _ _ ih1 ih2 => exact Glue.AnnotS.n5 ih1 ih2
  | n6 _ _ _ ih1 ih2 ih3 => exact Glue.AnnotS.n6 ih1 ih2 ih3
  | n7 _ _ ih1 ih2 => exact Glue.AnnotS.n7 ih1 ih2
  | n8 _ _ ih1 ih2 => exact Glue.AnnotS.n8 ih1 ih2
  | n9 _ _ ih1 ih2 => exact Glue.AnnotS.n9 ih1 ih2
  | n10 hx _ _ ih1 ih2 => exact Glue.AnnotS.n10 hx ih1 ih2
  | n11s _ ih => exact Glue.AnnotS.n11s ih
  | n11d _ _ ih1 ih2 => exact Glue.AnnotS.n11d ih1 ih2
  | n11c _ _ ih1 ih2 => exact Glue.AnnotS.n11c ih1 ih2
  | mean _ _ ih1 ih2 => exact Glue.AnnotS.mean ih1 ih2
  | n12 _ _ ih1 ih2 => exact Glue.AnnotS.n12 ih1 ih2
  | bare hb => exact Glue.AnnotS.bare hb
  | memo hs _ ih => exact Glue.AnnotS.memo hs ih
  | crash hc => exact Glue.AnnotS.crash hc
  | fold hv => exact Glue.AnnotS.fold hv
  | six0 hb _ ih => exact Glue.AnnotS.six0 hb ih
  | six1 hb _ ih => exact Glue.AnnotS.six1 hb ih
  | n8g _ _ _ ih1 ih2 ih3 => exact Glue.AnnotS.n8g ih1 ih2 ih3
  | n8l hb _ ih => exact Glue.AnnotS.n8l hb ih
  | bareLit hb hd => exact Glue.AnnotS.bareLit hb hd

/-- The statement of `knowGo_soundK` for one annotation, as an induction
motive. -/
def IHKK (lib : Lib) (code code' : Bell → Option Nomm) (fold : Bool) (dat : Bell → Option Datum)
    (res : Bell → Sock → Option Bell) (stF : List Site) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ sub st r, knowGo fold dat res nm sub st = some r → r.2 <:+ stF →
    ∀ Q : Noun → Prop, (∀ x, Q x → P x ∧ Fits sub.sock x) → KnowOKK lib code code' Q f nm r.1

/-- The Nock 7 family (`%7`, an inlined `%2`, `%9`): the first nomm gives
the subject of the second. -/
theorem seven_coreK (hc : CodeOK lib code) {P : Noun → Prop} {f b g : Noun} {p q : Nomm}
    (hA1 : AnnotK lib code P b p) (hA2 : AnnotK lib code (Img lib P b) g q)
    (ih1 : IHKK lib code code' fold dat res stF P b p)
    (ih2 : IHKK lib code code' fold dat res stF (Img lib P b) g q)
    (hmk : ∀ {Q : Noun → Prop} {p' q' : Nomm}, (∀ x, Q x → P x) → Glue.AnnotS lib code' Q b p' →
      Glue.AnnotS lib code' (Img lib Q b) g q' → Glue.AnnotS lib code' Q f (Nomm.n7 p' q'))
    (hfold : ∀ {Q : Noun → Prop}, (∀ x, Q x → P x) → ∀ v x gul z, Q x → Mink lib gul [] x b (Tone.zero z) →
      Mink lib gul [] z g (Tone.zero v) → Mink lib gul [] x f (Tone.zero v)) :
    IHKK lib code code' fold dat res stF P f (Nomm.n7 p q) := by
  intro sub st r h hsuf Q hQ
  simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨pp, hp, qq, hq, h⟩ := h
  have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
  have hp2 : pp.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
  have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
  have K1 := ih1 sub st pp hp hp2 Q hQ
  have hQ2 : ∀ z, Img lib Q b z → Img lib P b z ∧ Fits pp.1.2.sock z := by
    rintro z ⟨x, gul, hx, hm⟩
    refine ⟨⟨x, gul, hQP x hx, hm⟩, ?_⟩
    obtain ⟨m, hm'⟩ := mink_nommK hc hA1 (hQP x hx) hm
    exact K1.2 x hx gul [] m z hm'
  have K2 := ih2 pp.1.2 pp.2 qq hq hq2 (Img lib Q b) hQ2
  have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n7 p q) = some (Tone.zero y) →
      ∃ z m', Img lib Q b z ∧ nommF lib gul code m' t z q = some (Tone.zero y) := by
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    obtain ⟨z, hz, hzq⟩ := tbind_zero_inv hm'
    exact ⟨z, m', ⟨x, gul, hx, nomm_minkK hc hA1 (hQP x hx) hz⟩, hzq⟩
  split at h
  · rename_i v hv hs
    cases h
    have hl := lit_eq hv
    have K21 := K2.1
    rw [hl] at K21
    refine ⟨?_, ?_⟩
    · show Glue.AnnotS lib code' Q f qq.1.1
      rw [hl]
      refine Glue.AnnotS.fold fun x gul hx => ?_
      obtain ⟨z, hz⟩ := annot_safe_totalS K1.1 hs x gul hx
      exact hfold hQP v x gul z hx hz (annot_litS K21 v rfl z gul ⟨x, gul, hx, hz⟩)
    · intro x hx gul t m y hm
      obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
      exact fits_litAnno (lit_valK hc hA2 (fun z hz => (hQ2 z hz).1) K21 hz hzq)
  · cases h
    refine ⟨hmk hQP K1.1 K2.1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
    exact K2.2 z hz gul t m' y hzq

/-- `%8` and the forms `+know` gives it: the pushed pair `[b 0 1]`, as a
cons of two nomms or folded whole. -/
theorem n8_coreK (hc : CodeOK lib code) {P : Noun → Prop} {b c : Noun} {p r' q : Nomm}
    (hA1 : AnnotK lib code P b p) (hA2 : AnnotK lib code P (slot 1) r')
    (hA3 : AnnotK lib code (Img8 lib P b) c q)
    (ih1 : IHKK lib code code' fold dat res stF P b p)
    (ih2 : IHKK lib code code' fold dat res stF P (slot 1) r')
    (ih3 : IHKK lib code code' fold dat res stF (Img8 lib P b) c q) :
    IHKK lib code code' fold dat res stF P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p r') q) := by
  intro sub st r h hsuf Q hQ
  simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨pp, ⟨l, hl, r0, hr0, hcons⟩, qq, hq, h⟩ := h
  have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
  have hcases : (∃ x1 x2, lit l.1.1 = some x1 ∧ lit r0.1.1 = some x2 ∧
      pp = ((Nomm.n1 (C x1 x2), litAnno (C x1 x2)), r0.2)) ∨
      pp = ((Nomm.cons l.1.1 r0.1.1, ⟨So.knit l.1.2.sock r0.1.2.sock, Pi.cons l.1.2.src r0.1.2.src⟩), r0.2) := by
    split at hcons
    · rename_i x1 x2 h1 h2
      exact Or.inl ⟨_, _, h1, h2, (Option.some.inj hcons).symm⟩
    · exact Or.inr (Option.some.inj hcons).symm
  have hpp : pp.2 = r0.2 := by rcases hcases with ⟨_, _, _, _, rfl⟩ | rfl <;> rfl
  have hpq : pp.2 <:+ qq.2 := knowGo_suffix fold dat res q _ _ _ hq
  have hr02 : r0.2 <:+ stF := hpp ▸ hpq.trans hq2
  have hl2 : l.2 <:+ stF := (knowGo_suffix fold dat res r' _ _ _ hr0).trans hr02
  have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
  have K1 := ih1 sub st l hl hl2 Q hQ
  have K0 := ih2 sub l.2 r0 hr0 hr02 Q hQ
  have hself : ∀ x, Q x → ∀ gul t m w, nommF lib gul code m t x r' = some (Tone.zero w) → w = x :=
    fun x hx gul t m w hm => slot1_eq (nomm_minkK hc hA2 (hQP x hx) hm)
  have hself' : ∀ x, Q x → ∀ gul, ∃ m, nommF lib gul code m [] x r' = some (Tone.zero x) :=
    fun x hx gul => mink_nommK hc hA2 (hQP x hx) (mink_mk_n0 (slot?_one x))
  have hQ2 : ∀ z, Img8 lib Q b z → Img8 lib P b z ∧ Fits pp.1.2.sock z := by
    rintro z ⟨x, y, gul, hx, hy, rfl⟩
    refine ⟨⟨x, y, gul, hQP x hx, hy, rfl⟩, ?_⟩
    rcases hcases with ⟨x1, x2, h1, h2, rfl⟩ | rfl
    · have e1 := Mink.det hy (annot_litS K1.1 x1 (lit_eq h1) x gul hx)
      cases e1
      have e2 := slot1_eq (annot_litS K0.1 x2 (lit_eq h2) x gul hx)
      exact fits_litAnno (by rw [e2])
    · obtain ⟨m, hm⟩ := mink_nommK hc hA1 (hQP x hx) hy
      obtain ⟨m', hm'⟩ := hself' x hx gul
      exact knit_fits (K1.2 x hx gul [] m y hm) (K0.2 x hx gul [] m' x hm')
  have K3 := ih3 pp.1.2 pp.2 qq hq hq2 (Img8 lib Q b) hQ2
  have hsem : ∀ x, Q x → ∀ gul t m y,
      nommF lib gul code m t x (Nomm.n7 (Nomm.cons p r') q) = some (Tone.zero y) →
      ∃ z m', Img8 lib Q b z ∧ nommF lib gul code m' t z q = some (Tone.zero y) := by
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    obtain ⟨z, hz, hzq⟩ := tbind_zero_inv hm'
    obtain ⟨m'', rfl, hz'⟩ := nommF_succ_inv hz
    simp only [nommStep] at hz'
    obtain ⟨u, hu, hz'⟩ := tbind_zero_inv hz'
    obtain ⟨w, hw, hz'⟩ := tbind_zero_inv hz'
    cases hz'
    have hwx := hself x hx gul t m'' w hw
    subst hwx
    exact ⟨_, m'' + 1, ⟨_, u, gul, hx, nomm_minkK hc hA1 (hQP _ hx) hu, rfl⟩, hzq⟩
  split at h
  · rename_i v hv hs
    cases h
    have K31 := K3.1
    rw [lit_eq hv] at K31
    refine ⟨?_, ?_⟩
    · show Glue.AnnotS lib code' Q (n3 (A 8) b c) qq.1.1
      rw [lit_eq hv]
      refine Glue.AnnotS.fold fun x gul hx => ?_
      have hb : ∃ z, Mink lib gul [] x b (Tone.zero z) := by
        rcases hcases with ⟨x1, x2, h1, h2, rfl⟩ | rfl
        · exact ⟨x1, annot_litS K1.1 x1 (lit_eq h1) x gul hx⟩
        · simp only [safeNomm, Bool.and_eq_true] at hs
          exact annot_safe_totalS K1.1 hs.1 x gul hx
      obtain ⟨z, hz⟩ := hb
      exact mink_mk_n8 hz (annot_litS K31 v rfl _ gul ⟨x, z, gul, hx, hz, rfl⟩)
    · intro x hx gul t m y hm
      obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
      exact fits_litAnno (lit_valK hc hA3 (fun z hz => (hQ2 z hz).1) K31 hz hzq)
  · cases h
    refine ⟨?_, ?_⟩
    · show Glue.AnnotS lib code' Q (n3 (A 8) b c) (Nomm.n7 pp.1.1 qq.1.1)
      rcases hcases with ⟨x1, x2, h1, h2, rfl⟩ | rfl
      · refine Glue.AnnotS.n8l (fun x gul hx => ⟨annot_litS K1.1 x1 (lit_eq h1) x gul hx, ?_⟩) K3.1
        exact (slot1_eq (annot_litS K0.1 x2 (lit_eq h2) x gul hx)).symm
      · exact Glue.AnnotS.n8g K1.1 K0.1 K3.1
    · intro x hx gul t m y hm
      obtain ⟨z, m', hz, hzq⟩ := hsem x hx gul t m y hm
      exact K3.2 z hz gul t m' y hzq

/-- **`+know` is sound.**  If a nomm stands for a formula on the subjects of
`P` with the analysis' table `code`, then on every set `Q` of subjects in
`P` that fit the sock `+know` starts from, the nomm `knowGo` folds stands for
the same formula with the variants' table `code'`, and its product sock fits
every product of the original nomm (`KnowOKK`). -/
theorem knowGo_soundK (hc : CodeOK lib code) (hdat : DatOK lib dat) (hres : ResOK code' res stF) :
    ∀ {P f nm}, AnnotK lib code P f nm → IHKK lib code code' fold dat res stF P f nm := by
  intro P f nm hA
  induction hA with
  | cons hA1 hA2 ih1 ih2 =>
    rename_i P a1 a2 b p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r', hr, h⟩ := h
    have hr2 : r'.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hl2 : l.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hr).trans hr2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st l hl hl2 Q hQ
    have K2 := ih2 sub l.2 r' hr hr2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.cons p q) = some (Tone.zero y) →
        ∃ m' u w, nommF lib gul code m' t x p = some (Tone.zero u) ∧
          nommF lib gul code m' t x q = some (Tone.zero w) ∧ y = C u w := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨u, hu, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨w, hw, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', u, w, hu, hw, rfl⟩
    split at h
    · rename_i x1 x2 h1 h2
      cases h
      have K11 := K1.1
      rw [lit_eq h1] at K11
      have K21 := K2.1
      rw [lit_eq h2] at K21
      refine ⟨Glue.AnnotS.fold fun x gul hx =>
        mink_mk_cons (annot_litS K11 x1 rfl x gul hx) (annot_litS K21 x2 rfl x gul hx), ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', u, w, hu, hw, rfl⟩ := hsem x hx gul t m y hm
      exact fits_litAnno (by rw [lit_valK hc hA1 hQP K11 hx hu, lit_valK hc hA2 hQP K21 hx hw])
    · cases h
      refine ⟨Glue.AnnotS.cons K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', u, w, hu, hw, rfl⟩ := hsem x hx gul t m y hm
      exact knit_fits (K1.2 x hx gul t m' u hu) (K2.2 x hx gul t m' w hw)
  | n0 =>
    intro sub st r h hsuf Q hQ
    exact (knowGo_n0K h (fun x hx => (hQ x hx).2)).2.1
  | n1 =>
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.some.injEq] at h
    cases h
    refine ⟨Glue.AnnotS.n1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep, Option.some.injEq, Tone.zero.injEq] at hm'
    exact fits_litAnno hm'.symm
  | indirect hA1 hA2 ih1 ih2 =>
    rename_i P b c p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨s, hs, fq, hf, rfl⟩ := h
    have hs2 : s.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hf).trans hsuf
    exact ⟨Glue.AnnotS.indirect (ih1 sub st s hs hs2 Q hQ).1 (ih2 sub s.2 fq hf hsuf Q hQ).1,
      fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | direct hA1 hA2 hcode hy hg hdk ih1 ih2 =>
    rename_i P b c p q bl k nb
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, fq, hf, v, hv, rfl⟩ := h
    have hmem : (bl, s.1.2.sock) ∈ stF := hsuf.subset List.mem_cons_self
    obtain ⟨hvf, ⟨nb', hnb'⟩, hvfit⟩ := hres bl s.1.2.sock v hmem hv
    have hf2 : fq.2 <:+ stF := (List.suffix_cons _ _).trans hsuf
    have hs2 : s.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hf).trans hf2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st s hs hs2 Q hQ
    have K2 := ih2 sub s.2 fq hf hf2 Q hQ
    refine ⟨Glue.AnnotS.direct K1.1 K2.1 hnb' (fun x gul y hx hm => hvfit y (hy x gul y (hQP x hx) hm) ?_)
      (fun x gul g hx hm => (hg x gul g (hQP x hx) hm).trans hvf.symm)
      (fun hk hsf => ret_of_detK K2.1.toAnnot hsf (DetK.mono hQP _ (knowGo_detK_safe (hdk hk) hf hsf))), ?_⟩
    · obtain ⟨m, hm'⟩ := mink_nommK hc hA1 (hQP x hx) hm
      exact K1.2 x hx gul [] m y hm'
    · intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨s', hs', hm'⟩ := tbind_zero_inv hm'
      obtain ⟨g, hg', hm'⟩ := tbind_zero_inv hm'
      rw [hcode, Option.bind_some] at hm'
      dsimp only
      split
      · exact fits_dunno _
      · rename_i d hd
        have hsfit : Fits bl.less s' := hy x gul s' (hQP x hx) (nomm_minkK hc hA1 (hQP x hx) hs')
        have hk : Fits s.1.2.sock s' := K1.2 x hx gul t m' s' hs'
        exact hdat bl d hd s.1.2.sock s' y gul hsfit hk (nomm_mink hc (hc bl nb hcode) hsfit hm')
  | inline hA1 htot hA2 ih1 ih2 =>
    exact seven_coreK hc hA1 hA2 ih1 ih2
      (fun hQP a1 a2 => Glue.AnnotS.inline a1 (fun x gul hx => htot x gul (hQP x hx)) a2)
      (fun hQP _ x gul _ hx hz hzv => mink_mk_n2 hz (htot x gul (hQP x hx)) hzv)
  | n3 hA1 ih1 =>
    rename_i P b p
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have hp2 : pp.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n3 p) = some (Tone.zero y) →
        ∃ m' z, nommF lib gul code m' t x p = some (Tone.zero z) ∧ y = wut z := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', z, hz, rfl⟩
    split at h
    · rename_i d hd hs
      cases h
      refine ⟨Glue.AnnotS.fold fun x gul hx => ?_, ?_⟩
      · rw [← wut_eq]; exact mink_mk_n3 (safe_knownK hc hA1 hQP K1 hs hd x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', z, hz, rfl⟩ := hsem x hx gul t m y hm
        rw [known_fits hd (K1.2 x hx gul t m' z hz)]
        exact fits_litAnno (wut_eq d)
    · cases h
      exact ⟨Glue.AnnotS.n3 K1.1, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | n4 hA1 ih1 =>
    rename_i P b p
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have hp2 : pp.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n4 p) = some (Tone.zero y) →
        ∃ m' a, nommF lib gul code m' t x p = some (Tone.zero (A a)) ∧ y = A (a + 1) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases z with
      | cell _ _ => cases hm'
      | atom a => cases hm'; exact ⟨m', a, hz, rfl⟩
    split at h
    · rename_i a hd hs
      cases h
      refine ⟨Glue.AnnotS.fold fun x gul hx => mink_mk_n4 (safe_knownK hc hA1 hQP K1 hs hd x gul hx), ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', a', hz, rfl⟩ := hsem x hx gul t m y hm
      have e := known_fits hd (K1.2 x hx gul t m' _ hz)
      cases e
      exact fits_litAnno rfl
    · cases h
      exact ⟨Glue.AnnotS.n4 K1.1, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | n5 hA1 hA2 ih1 ih2 =>
    rename_i P b c p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hp2 : pp.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have K2 := ih2 sub pp.2 qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n5 p q) = some (Tone.zero y) →
        ∃ m' u w, nommF lib gul code m' t x p = some (Tone.zero u) ∧
          nommF lib gul code m' t x q = some (Tone.zero w) ∧ y = eqCode u w := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨u, hu, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨w, hw, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', u, w, hu, hw, rfl⟩
    split at h
    · rename_i dp dq hdp hsp hdq hsq
      cases h
      refine ⟨Glue.AnnotS.fold fun x gul hx => ?_, ?_⟩
      · rw [← eqCode_eq]
        exact mink_mk_n5 (safe_knownK hc hA1 hQP K1 hsp hdp x gul hx) (safe_knownK hc hA2 hQP K2 hsq hdq x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', u, w, hu, hw, rfl⟩ := hsem x hx gul t m y hm
        rw [known_fits hdp (K1.2 x hx gul t m' u hu), known_fits hdq (K2.2 x hx gul t m' w hw)]
        exact fits_litAnno (eqCode_eq dp dq)
    · cases h
      exact ⟨Glue.AnnotS.n5 K1.1 K2.1, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | n6 hA1 hA2 hA3 ih1 ih2 ih3 =>
    rename_i P b c d p q r0
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨pp, hp, h⟩ := h
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n6 p q r0) = some (Tone.zero y) →
        ∃ m' z, nommF lib gul code m' t x p = some (Tone.zero z) ∧
          ((z = A 0 ∧ nommF lib gul code m' t x q = some (Tone.zero y)) ∨
            (z = A 1 ∧ nommF lib gul code m' t x r0 = some (Tone.zero y))) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      refine ⟨m', z, hz, ?_⟩
      match z, hm' with
      | Noun.atom 0, hm' => exact Or.inl ⟨rfl, hm'⟩
      | Noun.atom 1, hm' => exact Or.inr ⟨rfl, hm'⟩
      | Noun.atom (k + 2), hm' => cases hm'
      | Noun.cell _ _, hm' => cases hm'
    split at h
    · rename_i hd hs
      have hq2 := h
      have hp2 : pp.2 <:+ stF := (knowGo_suffix _ dat res q _ _ _ h).trans hsuf
      have K1 := ih1 sub st pp hp hp2 Q hQ
      have K2 := ih2 sub pp.2 r h hsuf Q hQ
      refine ⟨Glue.AnnotS.six0 (safe_knownK hc hA1 hQP K1 hs hd) K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', z, hz, ⟨rfl, hzq⟩ | ⟨rfl, _⟩⟩ := hsem x hx gul t m y hm
      · exact K2.2 x hx gul t m' y hzq
      · cases known_fits hd (K1.2 x hx gul t m' _ hz)
    · rename_i hd hs
      have hp2 : pp.2 <:+ stF := (knowGo_suffix _ dat res r0 _ _ _ h).trans hsuf
      have K1 := ih1 sub st pp hp hp2 Q hQ
      have K3 := ih3 sub pp.2 r h hsuf Q hQ
      refine ⟨Glue.AnnotS.six1 (safe_knownK hc hA1 hQP K1 hs hd) K3.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', z, hz, ⟨rfl, _⟩ | ⟨rfl, hzr⟩⟩ := hsem x hx gul t m y hm
      · cases known_fits hd (K1.2 x hx gul t m' _ hz)
      · exact K3.2 x hx gul t m' y hzr
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨qq, hq, rr, hr, rfl⟩ := h
      have hr2 : rr.2 <:+ stF := hsuf
      have hq2 : qq.2 <:+ stF := (knowGo_suffix _ dat res r0 _ _ _ hr).trans hr2
      have hp2 : pp.2 <:+ stF := (knowGo_suffix _ dat res q _ _ _ hq).trans hq2
      have K1 := ih1 sub st pp hp hp2 Q hQ
      have K2 := ih2 sub pp.2 qq hq hq2 Q hQ
      have K3 := ih3 sub qq.2 rr hr hr2 Q hQ
      refine ⟨Glue.AnnotS.n6 K1.1 K2.1 K3.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', z, hz, ⟨_, hzq⟩ | ⟨_, hzr⟩⟩ := hsem x hx gul t m y hm
      · exact doubleInt_fits_left _ _ (K2.2 x hx gul t m' y hzq)
      · exact doubleInt_fits_right _ _ (K3.2 x hx gul t m' y hzr)
  | n7 hA1 hA2 ih1 ih2 =>
    exact seven_coreK hc hA1 hA2 ih1 ih2 (fun _ a1 a2 => Glue.AnnotS.n7 a1 a2)
      (fun _ _ _ _ _ _ hz hzv => mink_mk_n7 hz hzv)
  | n8 hA1 hA2 ih1 ih2 =>
    refine n8_coreK hc hA1 AnnotK.n0 hA2 ih1 ?_ ih2
    intro sub st r h hsuf Q hQ
    exact (knowGo_n0K h (fun x hx => (hQ x hx).2)).2.1
  | n9 hA1 hA2 ih1 ih2 =>
    exact seven_coreK hc hA1 hA2 ih1 ih2 (fun _ a1 a2 => Glue.AnnotS.n9 a1 a2)
      (fun _ _ _ _ _ _ hz hzv => mink_mk_n9 hz hzv)
  | n10 hax hA1 hA2 ih1 ih2 =>
    rename_i P axis v t0 p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨dn, hdn, rc, hrc, h⟩ := h
    have hrc2 : rc.2 <:+ stF := by
      split at h
      · cases h; exact hsuf
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        exact hsuf
    have hdn2 : dn.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hrc).trans hrc2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st dn hdn hdn2 Q hQ
    have K2 := ih2 sub dn.2 rc hrc hrc2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n10 axis p q) = some (Tone.zero y) →
        ∃ m' a b, nommF lib gul code m' t x p = some (Tone.zero a) ∧
          nommF lib gul code m' t x q = some (Tone.zero b) ∧ edit? axis a b = some y := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep, hax, if_false] at hm'
      obtain ⟨b, hb, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨a, ha, hm'⟩ := tbind_zero_inv hm'
      split at hm'
      · cases hm'
      · rename_i u hu
        cases hm'
        exact ⟨m', a, b, ha, hb, hu⟩
    split at h
    · rename_i u hu
      cases h
      -- the literal: both parts are literals and the edit succeeds
      revert hu
      split
      · rename_i x1 x2 h1 h2
        intro hu
        have K11 := K1.1
        rw [lit_eq h1] at K11
        have K21 := K2.1
        rw [lit_eq h2] at K21
        refine ⟨Glue.AnnotS.fold fun x gul hx =>
          mink_mk_n10 hax (annot_litS K11 x1 rfl x gul hx) (annot_litS K21 x2 rfl x gul hx) hu, ?_⟩
        intro x hx gul t m y hm
        obtain ⟨m', a, b, ha, hb, he⟩ := hsem x hx gul t m y hm
        rw [lit_valK hc hA1 hQP K11 hx ha, lit_valK hc hA2 hQP K21 hx hb, hu] at he
        exact fits_litAnno (Option.some.inj he).symm
      · intro hu; cases hu
    · rename_i hl
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨s', hs', rfl⟩ := h
      refine ⟨Glue.AnnotS.n10 hax K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', a, b, ha, hb, he⟩ := hsem x hx gul t m y hm
      exact darn_fits (K2.2 x hx gul t m' b hb) (K1.2 x hx gul t m' a ha) he hs'
  | n11s hA1 ih1 =>
    rename_i P tag q f0
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n11s tag q f0) = some (Tone.zero y) →
        ∃ m', nommF lib gul code m' t x q = some (Tone.zero y) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', hz⟩
    split at h
    · rename_i v hfree hv
      cases h
      have K11 := K1.1
      rw [lit_eq hv] at K11
      refine ⟨?_, ?_⟩
      · show Glue.AnnotS lib code' Q _ qq.1.1
        rw [lit_eq hv]
        exact Glue.AnnotS.fold fun x gul hx => mink_mk_n11s tag (annot_litS K11 v rfl x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', hm'⟩ := hsem x hx gul t m y hm
        exact fits_litAnno (lit_valK hc hA1 hQP K11 hx hm')
    · cases h
      refine ⟨Glue.AnnotS.n11s K1.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', hm'⟩ := hsem x hx gul t m y hm
      exact K1.2 x hx gul t m' y hm'
  | n11d hA1 hA2 ih1 ih2 =>
    rename_i P tag h0 f0 p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨hh, hhh, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hh2 : hh.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st hh hhh hh2 Q hQ
    have K2 := ih2 sub hh.2 qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n11d tag p q f0) = some (Tone.zero y) →
        ∃ m' t', nommF lib gul code m' t' x q = some (Tone.zero y) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨c0, _, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', _, hz⟩
    split at h
    · rename_i v hfree hs hv
      cases h
      have K21 := K2.1
      rw [lit_eq hv] at K21
      refine ⟨?_, ?_⟩
      · show Glue.AnnotS lib code' Q _ qq.1.1
        rw [lit_eq hv]
        refine Glue.AnnotS.fold fun x gul hx => ?_
        obtain ⟨c0, hc0⟩ := annot_safe_totalS K1.1 hs x gul hx
        exact mink_mk_n11d tag hc0 (annot_litS K21 v rfl x gul hx)
      · intro x hx gul t m y hm
        obtain ⟨m', t', hm'⟩ := hsem x hx gul t m y hm
        exact fits_litAnno (lit_valK hc hA2 hQP K21 hx hm')
    · cases h
      refine ⟨Glue.AnnotS.n11d K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', t', hm'⟩ := hsem x hx gul t m y hm
      exact K2.2 x hx gul t' m' y hm'
  | n11c hA1 hA2 ih1 ih2 =>
    rename_i P x0 y0 h0 f0 p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨hh, hhh, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hh2 : hh.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hq2
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st hh hhh hh2 Q hQ
    have K2 := ih2 sub hh.2 qq hq hq2 Q hQ
    have hsem : ∀ x, Q x → ∀ gul t m y, nommF lib gul code m t x (Nomm.n11d 0 p q f0) = some (Tone.zero y) →
        ∃ m' t', nommF lib gul code m' t' x q = some (Tone.zero y) := by
      intro x hx gul t m y hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨c0, _, hm'⟩ := tbind_zero_inv hm'
      obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
      cases hm'
      exact ⟨m', _, hz⟩
    split at h
    · rename_i v hfree hs hv
      cases h
      have K21 := K2.1
      rw [lit_eq hv] at K21
      refine ⟨?_, ?_⟩
      · show Glue.AnnotS lib code' Q _ qq.1.1
        rw [lit_eq hv]
        refine Glue.AnnotS.fold fun x gul hx => ?_
        obtain ⟨c0, hc0⟩ := annot_safe_totalS K1.1 hs x gul hx
        exact mink_ctag_iff.mpr (mink_mk_n11d 0 hc0 (annot_litS K21 v rfl x gul hx))
      · intro x hx gul t m y hm
        obtain ⟨m', t', hm'⟩ := hsem x hx gul t m y hm
        exact fits_litAnno (lit_valK hc hA2 hQP K21 hx hm')
    · cases h
      refine ⟨Glue.AnnotS.n11c K1.1 K2.1, ?_⟩
      intro x hx gul t m y hm
      obtain ⟨m', t', hm'⟩ := hsem x hx gul t m y hm
      exact K2.2 x hx gul t' m' y hm'
  | mean hA1 hA2 ih1 ih2 =>
    rename_i P h0 f0 p q b k
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, v, hv, qq, hq, rfl⟩ := h
    have hp2 : pp.2 <:+ stF :=
      (List.suffix_cons _ _).trans ((knowGo_suffix fold dat res q _ _ _ hq).trans hsuf)
    have K1 := ih1 sub st pp hp hp2 Q hQ
    have K2 := ih2 sub _ qq hq hsuf Q hQ
    refine ⟨Glue.AnnotS.mean K1.1 K2.1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep] at hm'
    obtain ⟨c0, _, hm'⟩ := tbind_zero_inv hm'
    obtain ⟨z, hz, hm'⟩ := tbind_zero_inv hm'
    cases hm'
    exact K2.2 x hx gul _ m' _ hz
  | n12 hA1 hA2 ih1 ih2 =>
    rename_i P b c p q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨pp, hp, qq, hq, rfl⟩ := h
    have hp2 : pp.2 <:+ stF := (knowGo_suffix fold dat res q _ _ _ hq).trans hsuf
    exact ⟨Glue.AnnotS.n12 (ih1 sub st pp hp hp2 Q hQ).1 (ih2 sub pp.2 qq hq hsuf Q hQ).1,
      fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | bare hb =>
    rename_i P f0
    intro sub st r h hsuf Q hQ
    have e2 : knowGo fold dat res (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f0) none) sub st =
        (knowGo fold dat res (Nomm.n0 1) sub st).bind fun s =>
          (knowGo fold dat res (Nomm.n1 f0) sub s.2).bind fun fq =>
            some ((Nomm.n2 s.1.1 fq.1.1 none, Anno.dunno), fq.2) := rfl
    rw [e2] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨s, hs, fq, hf, rfl⟩ := h
    obtain ⟨_, _, hshape⟩ := knowGo_n0K (lib := lib) (code := code) (code' := code') hs (Q := Q) (fun x hx => (hQ x hx).2)
    simp only [knowGo, Option.some.injEq] at hf
    cases hf
    refine ⟨?_, fun _ _ _ _ _ _ _ => fits_dunno _⟩
    rcases hshape with e | ⟨d, e, hd⟩
    · show Glue.AnnotS lib code' Q f0 (Nomm.n2 s.1.1 (Nomm.n1 f0) none)
      rw [e]; exact Glue.AnnotS.bare hb
    · show Glue.AnnotS lib code' Q f0 (Nomm.n2 s.1.1 (Nomm.n1 f0) none)
      rw [e]
      exact Glue.AnnotS.bareLit hb fun x hx => by
        have := hd x hx
        simp only [slot?_one, Option.some.injEq] at this
        exact this
  | memo hh hA1 ih1 =>
    intro sub st r h hsuf Q hQ
    have hQP : ∀ x, Q x → _ := fun x hx => (hQ x hx).1
    have K1 := ih1 sub st r h hsuf Q hQ
    exact ⟨Glue.AnnotS.memo (fun x gul hx => hh x gul (hQP x hx)) K1.1, K1.2⟩
  | crash hcr =>
    intro sub st r h hsuf Q hQ
    simp only [knowGo, if_true, Option.some.injEq] at h
    cases h
    exact ⟨Glue.AnnotS.crash hcr, fun _ _ _ _ _ _ _ => fits_dunno _⟩
  | fold hv =>
    rename_i P f0 v
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.some.injEq] at h
    cases h
    refine ⟨Glue.AnnotS.fold fun x gul hx => hv x gul (hQ x hx).1, ?_⟩
    intro x hx gul t m y hm
    obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
    simp only [nommStep, Option.some.injEq, Tone.zero.injEq] at hm'
    exact fits_litAnno hm'.symm
  | six0 hb hA1 ih1 =>
    intro sub st r h hsuf Q hQ
    have K1 := ih1 sub st r h hsuf Q hQ
    exact ⟨Glue.AnnotS.six0 (fun x gul hx => hb x gul (hQ x hx).1) K1.1, K1.2⟩
  | six1 hb hA1 ih1 =>
    intro sub st r h hsuf Q hQ
    have K1 := ih1 sub st r h hsuf Q hQ
    exact ⟨Glue.AnnotS.six1 (fun x gul hx => hb x gul (hQ x hx).1) K1.1, K1.2⟩
  | n8g hA1 hA2 hA3 ih1 ih2 ih3 => exact n8_coreK hc hA1 hA2 hA3 ih1 ih2 ih3
  | n8l hb hA1 ih1 =>
    rename_i P b c y d q
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    obtain ⟨pp, rfl, qq, hq, h⟩ := h
    have hq2 : qq.2 <:+ stF := by split at h <;> (cases h; exact hsuf)
    have hQP : ∀ x, Q x → P x := fun x hx => (hQ x hx).1
    have hQ2 : ∀ z, Img8 lib Q b z → Img8 lib P b z ∧ Fits (litAnno (C y d)).sock z := by
      rintro z ⟨x, y', gul, hx, hy, rfl⟩
      refine ⟨⟨x, y', gul, hQP x hx, hy, rfl⟩, ?_⟩
      obtain ⟨hby, hxd⟩ := hb x gul (hQP x hx)
      cases Mink.det hy hby
      exact fits_litAnno (by rw [hxd])
    have K1 := ih1 _ _ qq hq hq2 (Img8 lib Q b) hQ2
    have hsem : ∀ x, Q x → ∀ gul t m v, nommF lib gul code m t x (Nomm.n7 (Nomm.n1 (C y d)) q) =
        some (Tone.zero v) → ∃ m', Img8 lib Q b (C y d) ∧ nommF lib gul code m' t (C y d) q = some (Tone.zero v) := by
      intro x hx gul t m v hm
      obtain ⟨m', rfl, hm'⟩ := nommF_succ_inv hm
      simp only [nommStep] at hm'
      obtain ⟨z, hz, hzq⟩ := tbind_zero_inv hm'
      obtain ⟨m'', rfl, hz'⟩ := nommF_succ_inv hz
      simp only [nommStep, Option.some.injEq, Tone.zero.injEq] at hz'
      subst hz'
      obtain ⟨hby, hxd⟩ := hb x gul (hQP x hx)
      exact ⟨_, ⟨x, y, gul, hx, hby, by rw [hxd]⟩, hzq⟩
    split at h
    · rename_i v hv hs
      cases h
      have K11 := K1.1
      rw [lit_eq hv] at K11
      refine ⟨?_, ?_⟩
      · show Glue.AnnotS lib code' Q _ qq.1.1
        rw [lit_eq hv]
        refine Glue.AnnotS.fold fun x gul hx => ?_
        obtain ⟨hby, hxd⟩ := hb x gul (hQP x hx)
        exact mink_mk_n8 hby (annot_litS K11 v rfl _ gul ⟨x, y, gul, hx, hby, rfl⟩)
      · intro x hx gul t m w hm
        obtain ⟨m', hz, hzq⟩ := hsem x hx gul t m w hm
        exact fits_litAnno (lit_valK hc hA1 (fun z hz => (hQ2 z hz).1) K11 hz hzq)
    · cases h
      refine ⟨Glue.AnnotS.n8l (fun x gul hx => hb x gul (hQP x hx)) K1.1, ?_⟩
      intro x hx gul t m w hm
      obtain ⟨m', hz, hzq⟩ := hsem x hx gul t m w hm
      exact K1.2 _ hz gul t m' w hzq
  | bareLit hb hd =>
    intro sub st r h hsuf Q hQ
    simp only [knowGo, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨s, rfl, fq, rfl, rfl⟩ := h
    exact ⟨Glue.AnnotS.bareLit hb fun x hx => hd x (hQ x hx).1, fun _ _ _ _ _ _ _ => fits_dunno _⟩

/-- **A variant's nomm**: `+know` of a code bell's nomm under a bake stands
for the code bell's formula on the subjects that fit both the code
requirement and the bake. -/
theorem know_annotK (hc : CodeOK lib code) (hdat : DatOK lib dat) {c : Bell} {nm : Nomm}
    (hA : AnnotK lib code (Fits c.less) c.fol nm) {s : Sock} {n' : Nomm} {sites : List Site}
    (h : know fold nm s dat res = some (n', sites)) (hres : ResOK code' res sites) :
    Glue.AnnotS lib code' (fun x => Fits c.less x ∧ Fits s x) c.fol n' := by
  simp only [know, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, e⟩ := h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact (knowGo_soundK (stF := r.2) hc hdat hres hA ⟨s, A 1⟩ [] r hr (List.suffix_refl _) _
    (fun x hx => hx)).1

/-- With a bake that implies the code requirement, the variant's nomm stands
for the formula on every subject of the bake. -/
theorem know_annot_of_impliesK (hc : CodeOK lib code) (hdat : DatOK lib dat) {c : Bell} {nm : Nomm}
    (hA : AnnotK lib code (Fits c.less) c.fol nm) {s : Sock} {n' : Nomm} {sites : List Site}
    (h : know fold nm s dat res = some (n', sites)) (hres : ResOK code' res sites)
    (himp : ∀ x, Fits s x → Fits c.less x) : Glue.AnnotS lib code' (Fits s) c.fol n' :=
  (know_annotK hc hdat hA h hres).mono fun x hx => ⟨himp x hx, hx⟩

-- END annots_know.py

end SoundK

end Bake

end SkaModel
end Formalization
