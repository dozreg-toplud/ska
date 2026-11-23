import lemmas.Ska.AppMask
import lemmas.Ska.FolLoopSound
import lemmas.Ska.WantMono

/-!
# `fol-loop` is sound on the subjects of its code requirement

`folLoop_rgood` redoes the induction of `FolLoopSound.lean` relative to the
code requirement.  A run of `fol-loop` in a function on the subject sock
`bus` reaches a noun `z` from a subject `X'` of `app:ca W bus`, where `W`
covers the final `want` of the function; what holds of `z` is `RP`: the
provenance invariant on `X'` and the static condition of the subject sock
(`StatOK`).  The result is `RGood`:

* `annot`: the nomm satisfies `Annot` on the nouns reached so (`RSub`);
* `prod`: every product, from a noun reached so, is reached so with the
  product sock and provenance;
* `saf`, `safe`, `sff` as in `Good`, the last two on the nouns reached so,
  and `sff` given that `W` covers the provenance of the product.

The table is assumed to be right relative to the call site (`RTab`): the
callee's code requirement holds of every noun that fits it cut down to what
it uses of the call's subject sock, the bell has code, and on every subject
of its code requirement the callee's product satisfies the provenance
invariant and the static condition on the call's subject sock.  The
function's subject sock is assumed well formed (`WellFormed`).

`folLoop_wantSound` is `WantSound` for one run under these assumptions, and
`folLoop_relProd` the product half that `hit_prod` and the table of a caller
need.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- **What holds of a noun `z` that a run reaches** from the subject `X'`
of the code requirement `app:ca W bus`, with the sock-annotated noun `a`. -/
structure RP (bus : Sock) (W : Cape) (a : Anno) (X' z : Noun) : Prop where
  req : Fits (Ca.app W bus) X'
  prov : ProvR X' a.sock a.src z
  stat : StatOK bus a.sock a.src

/-- The nouns that a run reaches with the sock-annotated noun `a`. -/
def RSub (bus : Sock) (W : Cape) (a : Anno) : Noun → Prop := fun z => ∃ X', RP bus W a X' z

/-- **What the relative proofs assume of the table of callees**, for an
answer `d` to a call of `f` on the subject sock `s`. -/
structure RTab (lib : Lib) (code : Bell → Option Nomm) (tab : Tab) : Prop where
  less : ∀ s f d lc dl, tab s f = some d → s ≠ Sock.void → d.less = Sock.mk lc dl →
    ∀ y, Fits (Ca.app lc s) y → Fits d.less y
  code : ∀ s f d, tab s f = some d → ∃ nb, code ⟨d.less, f⟩ = some nb
  prod : ∀ s f d, tab s f = some d → s ≠ Sock.void → ∀ y gul p, Fits d.less y →
    Mink lib gul [] y f (Tone.zero p) → ProvR y d.prod d.map p ∧ StatOK s d.prod d.map

/-- What holds of a result `out` of `fol-loop` on `fol` and `sub`, relative
to the code requirement. -/
structure RGood (lib : Lib) (code : Bell → Option Nomm) (bus : Sock) (W : Cape) (fol : Noun)
    (sub : Anno) (out : FolOut) : Prop where
  annot : Annot lib code (RSub bus W sub) fol out.nomm
  prod : ∀ X' z gul p, RP bus W sub X' z → Mink lib gul [] z fol (Tone.zero p) →
    RP bus W out.prod X' p
  saf : out.saf = true →
    ∃ d, out.prod.sock = Sock.mk Cape.yes d ∧ ∀ x gul, Mink lib gul [] x fol (Tone.zero d)
  safe : safeNomm out.nomm = true →
    ∀ x gul, RSub bus W sub x → ∃ c, Mink lib gul [] x fol (Tone.zero c)
  sff : safeFolFol out.nomm = true → ∀ d, out.prod.sock = Sock.mk Cape.yes d →
    (∀ q, (distribute Cape.yes out.prod.src).Has q → W.Has q) →
    ∀ x gul, RSub bus W sub x → Mink lib gul [] x fol (Tone.zero d)

/-- `W` covers the `want` of `g`. -/
def WCov (W : Cape) (g : Gen) : Prop := ∀ q, g.want.Has q → W.Has q

theorem WCov.of_le {W : Cape} {g g' : Gen} (h : WCov W g') (hl : WantLe g g') : WCov W g :=
  fun q hq => h q (hl q hq)

/-- Every result of the recursion whose `want` `W` covers is `RGood`. -/
def GoRGood (lib : Lib) (code : Bell → Option Nomm) (bus : Sock) (W : Cape) (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') → WCov W gen' →
    RGood lib code bus W fol sub out

/-! ## Helpers -/

theorem provO_yes (y n : Noun) : ProvO y (Sock.mk Cape.yes n) (A 0) (some n) where
  nonvoid := by simp
  exact := exactAt_zero _ _
  const := fun π _ => fitsOpt_sockAt π (show Fits (Sock.mk Cape.yes n) n from rfl)

theorem RP.dunno {bus : Sock} {W : Cape} {X' z p : Noun} (h : RP bus W ⟨S, σ⟩ X' z) :
    RP bus W Anno.dunno X' p :=
  ⟨h.req, provO_iff.mp (provO_dunno X' _), statOK_dunno _ _⟩

theorem RGood.of_plain {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape} {fol : Noun}
    {sub : Anno} {out : FolOut} (ha : Annot lib code (RSub bus W sub) fol out.nomm)
    (hp : ∀ X' z gul p, RP bus W sub X' z → Mink lib gul [] z fol (Tone.zero p) → RP bus W out.prod X' p)
    (hsaf : out.saf = false) (hs : safeNomm out.nomm = false) (hf : safeFolFol out.nomm = false) :
    RGood lib code bus W fol sub out where
  annot := ha
  prod := hp
  saf := fun h => by rw [hsaf] at h; cases h
  safe := fun h => by rw [hs] at h; cases h
  sff := fun h => by rw [hf] at h; cases h

theorem RGood.of_dunno {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape} {fol : Noun}
    {sub : Anno} {out : FolOut} (ha : Annot lib code (RSub bus W sub) fol out.nomm)
    (hd : out.prod = Anno.dunno) (hsaf : out.saf = false) (hs : safeNomm out.nomm = false) :
    RGood lib code bus W fol sub out where
  annot := ha
  prod := fun X' z _ _ hz _ => by
    rw [hd]; exact ⟨hz.req, provO_iff.mp (provO_dunno X' _), statOK_dunno _ _⟩
  saf := fun h => by rw [hsaf] at h; cases h
  safe := fun h => by rw [hs] at h; cases h
  sff := fun _ d he _ _ _ => by rw [hd] at he; cases he

theorem RGood.transfer {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape} {fol fol' : Noun}
    {sub : Anno} {out : FolOut} (G : RGood lib code bus W fol' sub out)
    (heq : ∀ x gul p, Mink lib gul [] x fol (Tone.zero p) ↔ Mink lib gul [] x fol' (Tone.zero p))
    (ha : Annot lib code (RSub bus W sub) fol out.nomm) : RGood lib code bus W fol sub out where
  annot := ha
  prod := fun X' z gul p hz hm => G.prod X' z gul p hz ((heq z gul p).mp hm)
  saf := fun hs => by
    obtain ⟨d, hd, md⟩ := G.saf hs
    exact ⟨d, hd, fun x gul => (heq x gul d).mpr (md x gul)⟩
  safe := fun hn x gul hx => by
    obtain ⟨c, mc⟩ := G.safe hn x gul hx
    exact ⟨c, (heq x gul c).mpr mc⟩
  sff := fun hn d hd hW x gul hx => (heq x gul d).mpr (G.sff hn d hd hW x gul hx)

theorem rsub_img {lib : Lib} {bus : Sock} {W : Cape} {sub a : Anno} {b : Noun}
    (h : ∀ X' z gul y, RP bus W sub X' z → Mink lib gul [] z b (Tone.zero y) → RP bus W a X' y) :
    ∀ y, Img lib (RSub bus W sub) b y → RSub bus W a y := by
  intro y ⟨x, gul, ⟨X', hx⟩, hm⟩
  exact ⟨X', h X' x gul y hx hm⟩

theorem slot_of_slotO {a : Nat} {q : List Bool} {x d : Noun} (hq : axisPath a = some q)
    (h : slotO (some x) q = some d) : slot? a x = some d := by
  simpa [slot?, hq, slotO] using h

section Cases

variable {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {go : FolGo} {bus : Sock} {W : Cape}
  {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

/-! ## The cases without calls -/

theorem rgood_other (hs : shape fol = Shape.other)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RGood lib code bus W fol sub out := by
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact RGood.of_dunno (Annot.crash (shape_other_crashes hs lib)) rfl rfl rfl

theorem rgood_op1 {p : Noun} (hs : shape fol = Shape.op1 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact {
    annot := Annot.n1
    prod := fun X' _ _ _ hz hm => by
      rw [mink_inv_n1 hm]; exact ⟨hz.req, provO_iff.mp (provO_yes X' p), statOK_zero _ _⟩
    saf := fun _ => ⟨p, rfl, fun x _ => mink_mk_n1 x p⟩
    safe := fun _ x _ _ => ⟨p, mink_mk_n1 x p⟩
    sff := fun _ d he _ x _ _ => by cases he; exact mink_mk_n1 x _ }

theorem rgood_op0 {p : Nat} (hs : shape fol = Shape.op0 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨pr, hpr, rfl, rfl⟩ := h
  refine ⟨Annot.n0, ?_, fun h => (by cases h), fun h => (by cases h), ?_⟩
  · intro X' z gul y hz hm
    have hy := mink_inv_n0 hm
    split at hpr
    · cases hpr; exact ⟨hz.req, provO_iff.mp (provO_dunno X' _), statOK_dunno _ _⟩
    · split at hpr
      · rename_i h1; subst h1; cases hpr
        simp only [slot?_one, Option.some.injEq] at hy
        subst hy; exact hz
      · rename_i h0 h1
        obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hpr
        obtain ⟨q, hq⟩ := axisPath_pos p (by omega)
        rw [pull_eq_sockAt (by omega) hq] at hs'
        cases hs'
        refine ⟨hz.req, ?_, statOK_slot hz.stat (by omega) hq⟩
        have := provO_slot (provO_iff.mpr hz.prov) (by omega) hq
        have e : slotO (some z) q = some y := by simpa [slot?, hq, slotO] using hy
        rw [e] at this
        exact provO_iff.mp this
  · intro _ d he hW x gul ⟨X', hz⟩
    split at hpr
    · cases hpr; cases he
    · split at hpr
      · rename_i h1; subst h1; cases hpr
        have := known_at (provO_iff.mpr hz.prov) hz.stat hz.req [] (by simpa [springAt] using hW) he
        simp only [slotO_nil, Option.some.injEq] at this
        subst this
        exact mink_mk_n0 (slot?_one _)
      · rename_i h0 h1
        obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hpr
        obtain ⟨q, hq⟩ := axisPath_pos p (by omega)
        rw [pull_eq_sockAt (by omega) hq] at hs'
        cases hs'
        have hsl : springAt sub.src q = Pi.slot sub.src p := by
          have := springAt_slot p sub.src q [] (by omega) hq
          simpa [springAt] using this.symm
        have := known_at (provO_iff.mpr hz.prov) hz.stat hz.req q (by rw [hsl]; exact hW) he
        exact mink_mk_n0 (slot_of_slotO hq this)

theorem rgood_op3 (IH : GoRGood lib code bus W go) (hM : GoMono go) {a b : Noun}
    (hs : shape fol = Shape.op3 a b) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, rfl, rfl⟩ := h
  exact RGood.of_dunno (Annot.n3 (IH _ _ _ _ _ _ _ _ h1 hW).annot) rfl rfl rfl

theorem rgood_op4 (IH : GoRGood lib code bus W go) {a b : Noun}
    (hs : shape fol = Shape.op4 a b) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, rfl, rfl⟩ := h
  exact RGood.of_dunno (Annot.n4 (IH _ _ _ _ _ _ _ _ h1 hW).annot) rfl rfl rfl

theorem rgood_op5 (IH : GoRGood lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.op5 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  exact RGood.of_dunno (Annot.n5 (IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))).annot
    (IH _ _ _ _ _ _ _ _ h2 hW).annot) rfl rfl rfl

theorem rgood_op12 (IH : GoRGood lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.op12 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  exact RGood.of_dunno (Annot.n12 (IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))).annot
    (IH _ _ _ _ _ _ _ _ h2 hW).annot) rfl rfl rfl

theorem rgood_op6 (IH : GoRGood lib code bus W go) (hM : GoMono go) {a b q r : Noun}
    (hs : shape fol = Shape.op6 a b q r) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, ⟨r', g3⟩, h3, rfl, rfl⟩ := h
  have W3 : WCov W g3 := hW
  have W2 : WCov W g2 := hW.of_le (hM _ _ _ _ _ _ _ _ h3)
  have W1 : WCov W g1 := W2.of_le (hM _ _ _ _ _ _ _ _ h2)
  have Gq := IH _ _ _ _ _ _ _ _ h2 W2
  have Gr := IH _ _ _ _ _ _ _ _ h3 W3
  refine RGood.of_plain (Annot.n6 (IH _ _ _ _ _ _ _ _ h1 W1).annot Gq.annot Gr.annot) ?_ rfl rfl rfl
  intro X' x gul y hx hm
  rcases mink_inv_n6 hm with hc | hd
  · have R := Gq.prod X' x gul y hx hc
    exact ⟨R.req, provO_iff.mp (provO_doubleInt_left _ _ (provO_iff.mpr R.prov)),
      statOK_doubleInt_left _ _ R.prov.nonvoid R.stat⟩
  · have R := Gr.prod X' x gul y hx hd
    exact ⟨R.req, provO_iff.mp (provO_doubleInt_right _ _ (provO_iff.mpr R.prov)),
      statOK_doubleInt_right _ _ R.prov.nonvoid R.stat⟩

theorem rgood_op7 (IH : GoRGood lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.op7 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  have Gp := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Gq := IH _ _ _ _ _ _ _ _ h2 hW
  refine RGood.of_plain (Annot.n7 Gp.annot (Gq.annot.mono (rsub_img Gp.prod))) ?_ rfl rfl rfl
  intro X' x gul y hx hm
  obtain ⟨z, m1, m2⟩ := mink_inv_n7 hm
  exact Gq.prod X' z gul y (Gp.prod X' x gul z hx m1) m2

theorem rgood_cons (IH : GoRGood lib code bus W go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.cons a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
  have Gl := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Gr := IH _ _ _ _ _ _ _ _ h2 hW
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
  · intro X' x gul p hx hm
    obtain ⟨p1, p2, rfl, m1, m2⟩ := mink_inv_cons hm
    have R1 := Gl.prod X' x gul p1 hx m1
    have R2 := Gr.prod X' x gul p2 hx m2
    unfold consProd
    split
    · rename_i hc
      obtain ⟨dl, hl, ml⟩ := Gl.saf hc.1
      obtain ⟨dr, hr, mr⟩ := Gr.saf hc.2.1
      have e1 := Mink.det m1 (ml x gul)
      have e2 := Mink.det m2 (mr x gul)
      cases e1; cases e2
      simp only [hl, hr, Sock.data]
      exact ⟨hx.req, provO_iff.mp (provO_yes X' _), statOK_zero _ _⟩
    · refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R1.stat R2.stat⟩
      · rw [slotO_some_cell_false]; exact provO_iff.mpr R1.prov
      · rw [slotO_some_cell_true]; exact provO_iff.mpr R2.prov
  · intro hc
    obtain ⟨dl, dr, he, ml, mr⟩ := hsafe hc
    exact ⟨C dl dr, he, fun x gul => mink_mk_cons (ml x gul) (mr x gul)⟩
  · intro hn x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hn
    obtain ⟨c1, m1⟩ := Gl.safe hn.1 x gul hx
    obtain ⟨c2, m2⟩ := Gr.safe hn.2 x gul hx
    exact ⟨C c1 c2, mink_mk_cons m1 m2⟩
  · intro _ d he _ x gul _
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

theorem rgood_call (hT : RTab lib code tab) (hwf : WellFormed bus) (IH : GoRGood lib code bus W go)
    (hM : GoMono go) {b c : Noun} {s f : FolOut}
    (Gs : RGood lib code bus W b sub s) (Gf : RGood lib code bus W c sub f) {g2 : Gen}
    (h : callStep tab go mk bc df s f g2 = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W (n3 (A 2) b c) sub out := by
  unfold callStep at h
  split at h
  · -- a void subject or formula: no run reaches the call
    rename_i hv
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine RGood.of_plain (Annot.indirect Gs.annot Gf.annot) ?_ rfl rfl rfl
    intro X' x gul p hx hm
    obtain ⟨y, g, m1, m2, _⟩ := mink_inv_n2 hm
    have f1 := (Gs.prod X' x gul y hx m1).prov.nonvoid
    have f2 := (Gf.prod X' x gul g hx m2).prov.nonvoid
    rcases hv with hv | hv
    · exact absurd hv f1
    · exact absurd hv f2
  · rename_i hv
    simp only [not_or] at hv
    split at h
    · rename_i fa fb hfp
      -- the formula of the call is known
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
        have Gi := IH _ _ _ _ _ _ _ _ hi hW
        refine RGood.of_plain (Annot.inline Gs.annot ?_ (Gi.annot.mono (rsub_img Gs.prod))) ?_ rfl rfl rfl
        · exact fun x gul hx => Gf.sff hin.2.2.2 _ hfp hWf x gul hx
        · intro X' x gul p hx hm
          obtain ⟨y, g, m1, m2, m3⟩ := mink_inv_n2 hm
          rw [hg hWf X' x gul g hx m2] at m3
          exact Gi.prod X' y gul p (Gs.prod X' x gul y hx m1) m3
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
          refine RGood.of_plain (Annot.direct (bl := ⟨d.less, C fa fb⟩) Gs.annot Gf.annot hnb ?_ ?_)
            ?_ rfl rfl rfl
          · intro x gul y ⟨X', hx⟩ hm; exact hless X' x gul y hx hm
          · intro x gul g ⟨X', hx⟩ hm; exact hg hWf X' x gul g hx hm
          · intro X' x gul p hx hm
            obtain ⟨y, g, m1, m2, m3⟩ := mink_inv_n2 hm
            rw [hg hWf X' x gul g hx m2] at m3
            have R := Gs.prod X' x gul y hx m1
            obtain ⟨hpR, hpS⟩ := hT.prod _ _ d hd hv.1 y gul p (hless X' x gul y hx m1) m3
            refine ⟨R.req, ?_, statOK_compose hv.1 R.stat hpS⟩
            exact provO_iff.mp (provO_compose (provO_iff.mpr R.prov) (provO_iff.mpr hpR)
              (hpS.toStatS hpR.nonvoid) (hpS.toShapeOK hpR.nonvoid))
    · -- an indirect call
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact RGood.of_dunno (Annot.indirect Gs.annot Gf.annot) rfl rfl rfl

theorem rgood_op2 (hT : RTab lib code tab) (hwf : WellFormed bus) (IH : GoRGood lib code bus W go)
    (hM : GoMono go) {a b q : Noun} (hs : shape fol = Shape.op2 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s', g1⟩, h1, ⟨f', g2⟩, h2, h⟩ := h
  have W2 : WCov W g2 := hW.of_le (callStep_mono hM h)
  have W1 : WCov W g1 := W2.of_le (hM _ _ _ _ _ _ _ _ h2)
  exact rgood_call hT hwf IH hM (IH _ _ _ _ _ _ _ _ h1 W1) (IH _ _ _ _ _ _ _ _ h2 W2) h hW

/-! ## Edits and hints -/

theorem rgood_op10 (IH : GoRGood lib code bus W go) (hM : GoMono go) {ax : Nat} {don r1 r2 : Noun}
    (hs : shape fol = Shape.op10 ax don r1 r2)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  split at h
  · rename_i hax
    subst hax
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact RGood.of_dunno (Annot.crash fun gul t s => ⟨1, by simp [minkF, minkStep]⟩) rfl rfl rfl
  · rename_i hax
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, sk, hd, rfl, rfl⟩ := h
    have Gd := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
    have Gr := IH _ _ _ _ _ _ _ _ h2 hW
    refine RGood.of_plain (Annot.n10 hax Gd.annot Gr.annot) ?_ rfl rfl rfl
    intro X' x gul p hx hm
    obtain ⟨tg, vv, m1, m2, he⟩ := mink_inv_n10 hm
    have R1 := Gr.prod X' x gul tg hx m1
    have R2 := Gd.prod X' x gul vv hx m2
    exact ⟨hx.req, provO_iff.mp (provO_darn (provO_iff.mpr R1.prov) (provO_iff.mpr R2.prov) he hd),
      statOK_darn R1.stat R2.stat hd⟩

theorem rgood_op11s_plain (IH : GoRGood lib code bus W go) {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p ≠ Tag.bare)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, hp, if_false, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨q, g1⟩, h1, rfl, rfl⟩ := h
  have Gq := IH _ _ _ _ _ _ _ _ h1 hW
  refine ⟨Annot.n11s Gq.annot, ?_, fun h => (by cases h), ?_, ?_⟩
  · exact fun X' x gul y hx hm => Gq.prod X' x gul y hx (mink_inv_n11s hm)
  · intro hn x gul hx
    simp only [safeNomm, Bool.and_eq_true] at hn
    obtain ⟨c, mc⟩ := Gq.safe hn.2 x gul hx
    exact ⟨c, mink_mk_n11s _ mc⟩
  · intro hn d he hW' x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hn
    exact mink_mk_n11s _ (Gq.sff hn.2 d he hW' x gul hx)

theorem rgood_op11d (IH : GoRGood lib code bus W go) (hM : GoMono go) {tag : Nat} {h1 h2 f : Noun}
    (hs : shape fol = Shape.op11d tag h1 h2 f)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
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
    have G' := IH _ _ _ _ _ _ _ _ h hW
    have Gh := IH _ _ _ _ _ _ _ _ hh1 (hW.of_le (hM _ _ _ _ _ _ _ _ h))
    obtain ⟨dh, _, mh⟩ := Gh.saf hsaf
    have hret : ∀ x gul, ∃ c, Mink lib gul [] x (C h1 h2) (Tone.zero c) := fun x gul => ⟨dh, mh x gul⟩
    exact G'.transfer (fun x gul p => mink_memo_iff (hret x gul))
      (Annot.memo (fun x gul _ => hret x gul) G'.annot)
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨arm, g2⟩, ha, ⟨fr, g3⟩, hf1, rfl, rfl⟩ := h
    have Gf := IH _ _ _ _ _ _ _ _ hf1 hW
    have Gh := IH _ _ _ _ _ _ _ _ hh1
      ((hW.of_le (hM _ _ _ _ _ _ _ _ hf1)).of_le (meanArm_mono hM ha))
    have hprod : ∀ X' x gul p, RP bus W sub X' x →
        Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero p) → RP bus W fr.prod X' p :=
      fun X' x gul p hx hm => Gf.prod X' x gul p hx (mink_inv_n11d hm).2
    have hsafe : ∀ x gul, RSub bus W sub x → safeNomm hh.nomm = true → safeNomm fr.nomm = true →
        ∃ c, Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero c) := by
      intro x gul hx s1 s2
      obtain ⟨c1, m1⟩ := Gh.safe s1 x gul hx
      obtain ⟨c2, m2⟩ := Gf.safe s2 x gul hx
      exact ⟨c2, mink_mk_n11d _ m1 m2⟩
    have hsff : ∀ x gul d, RSub bus W sub x → safeNomm hh.nomm = true → safeFolFol fr.nomm = true →
        fr.prod.sock = Sock.mk Cape.yes d → (∀ q, (distribute Cape.yes fr.prod.src).Has q → W.Has q) →
        Mink lib gul [] x (n3 (A 11) (C (A tag) (C h1 h2)) f) (Tone.zero d) := by
      intro x gul d hx s1 s2 hd hW'
      obtain ⟨c1, m1⟩ := Gh.safe s1 x gul hx
      exact mink_mk_n11d _ m1 (Gf.sff s2 d hd hW' x gul hx)
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
      · intro hn d hd hW' x gul hx
        simp only [safeFolFol, Bool.and_eq_true] at hn
        exact hsff x gul d hx hn.1.2 hn.2 hd hW'
    | some bk =>
      obtain ⟨bl, k⟩ := bk
      have htag := meanArm_tag ha (by rw [harm]; simp)
      subst htag
      subst harm
      refine ⟨Annot.mean Gh.annot Gf.annot, hprod, hsaf, ?_, ?_⟩
      · intro hn x gul hx
        simp only [safeNomm, Bool.and_eq_true] at hn
        exact hsafe x gul hx hn.1 hn.2
      · intro hn d hd hW' x gul hx
        simp only [safeFolFol, Bool.and_eq_true] at hn
        exact hsff x gul d hx hn.1 hn.2 hd hW'

/-! ## The rewritten cases: `%8`, `%9`, `%bare` -/

theorem rgood_bare {m : Nat} (IH : GoRGood lib code bus W (folLoopF tab m)) {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p = Tag.bare)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
  subst hp
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, if_true] at h
  have G' := IH _ _ _ _ _ _ _ _ h hW
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

theorem rgood_op9 {m : Nat} (IH' : ∀ k, k + 1 = m → GoRGood lib code bus W (folLoopF tab k))
    {p : Nat} {a b : Noun} (hs : shape fol = Shape.op9 p a b)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
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
  have G2 := IH' k rfl _ _ _ _ _ _ _ _ h2 hW
  have G1 := IH' k rfl _ _ _ _ _ _ _ _ h1 (hW.of_le (folLoopF_want_mono tab k _ _ _ _ _ _ _ _ h2))
  refine RGood.of_plain (Annot.n9 G1.annot (G2.annot.mono (rsub_img G1.prod))) ?_ rfl rfl rfl
  intro X' x gul y hx hm
  obtain ⟨core, arm, m1, hsl, m2⟩ := mink_inv_n9 hm
  exact G2.prod X' core gul y (G1.prod X' x gul core hx m1)
    (mink_mk_n2 (mink_mk_n0 (slot?_one core)) (mink_mk_n0 hsl) m2)

theorem rgood_op8 {m : Nat} (IH' : ∀ k, k < m → GoRGood lib code bus W (folLoopF tab k))
    {a b q : Noun} (hs : shape fol = Shape.op8 a b q)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RGood lib code bus W fol sub out := by
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
  have G2 := IH' k (by omega) _ _ _ _ _ _ _ _ h2 hW
  have W1 : WCov W g1 := hW.of_le (folLoopF_want_mono tab k _ _ _ _ _ _ _ _ h2)
  cases k with
  | zero => simp [folLoopF] at h1
  | succ j =>
  rw [folLoopF_succ] at h1
  simp only [folStep, shape_cons_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨ob, gb⟩, hb, ⟨oz, gz⟩, hz, rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := folLoop_slot1 hz
  have Gb := IH' j (by omega) _ _ _ _ _ _ _ _ hb W1
  rw [consProd_unsafe rfl] at G2
  have hsub : ∀ X' x gul y, RP bus W sub X' x → Mink lib gul [] x (C a b) (Tone.zero y) →
      RP bus W ⟨So.knit ob.prod.sock sub.sock, Pi.cons ob.prod.src sub.src⟩ X' (C y x) := by
    intro X' x gul y hx hm
    have R := Gb.prod X' x gul y hx hm
    refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R.stat hx.stat⟩
    · rw [slotO_some_cell_false]; exact provO_iff.mpr R.prov
    · rw [slotO_some_cell_true]; exact provO_iff.mpr hx.prov
  refine RGood.of_plain (Annot.n8 Gb.annot (G2.annot.mono ?_)) ?_ rfl rfl rfl
  · intro z ⟨x, y, gul, ⟨X', hx⟩, hm, hz⟩
    subst hz
    exact ⟨X', hsub X' x gul y hx hm⟩
  · intro X' x gul p hx hm
    obtain ⟨y, m1, m2⟩ := mink_inv_n8 hm
    exact G2.prod X' (C y x) gul p (hsub X' x gul y hx m1) m2

end Cases

/-! ## The main theorem -/

/-- **`fol-loop` is sound on the subjects of its code requirement**, given
a table that is right relative to its call sites and a well-formed subject
sock: every result whose `want` `W` covers is `RGood`. -/
theorem folLoop_rgood {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {bus : Sock} {W : Cape}
    (hT : RTab lib code tab) (hwf : WellFormed bus) : ∀ n, GoRGood lib code bus W (folLoopF tab n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro fol sub mk bc df gen out gen' h hW
  cases n with
  | zero => simp [folLoopF] at h
  | succ m =>
  rw [folLoopF_succ] at h
  have IH : GoRGood lib code bus W (folLoopF tab m) := ih m (by omega)
  have hM : GoMono (folLoopF tab m) := folLoopF_want_mono tab m
  cases hs : shape fol with
  | cons a b q => exact rgood_cons IH hM hs h hW
  | op0 p => exact rgood_op0 hs h
  | op1 p => exact rgood_op1 hs h
  | op2 a b q => exact rgood_op2 hT hwf IH hM hs h hW
  | op3 a b => exact rgood_op3 IH hM hs h hW
  | op4 a b => exact rgood_op4 IH hs h hW
  | op5 a b q => exact rgood_op5 IH hM hs h hW
  | op6 a b q r => exact rgood_op6 IH hM hs h hW
  | op7 a b q => exact rgood_op7 IH hM hs h hW
  | op8 a b q => exact rgood_op8 (fun k hk => ih k (by omega)) hs h hW
  | op9 p a b => exact rgood_op9 (fun k hk => ih k (by omega)) hs h hW
  | op10 ax don r1 r2 => exact rgood_op10 IH hM hs h hW
  | op11s p a b =>
    by_cases hp : p = Tag.bare
    · exact rgood_bare IH hs hp h hW
    · exact rgood_op11s_plain IH hs hp h hW
  | op11d tag h1 h2 f => exact rgood_op11d IH hM hs h hW
  | op12 a b q => exact rgood_op12 IH hM hs h hW
  | other => exact rgood_other hs h

/-! ## Consequences for a function -/

/-- A subject of the code requirement is reached at the start, with the
subject `[bus 1]`. -/
theorem provR_top {S : Sock} (hS : S ≠ Sock.void) (x : Noun) : ProvR x S (A 1) x where
  nonvoid := hS
  exact := fun π a e _ => by
    rw [springAt_atom 1 π (by omega)] at e
    cases e
    have := axisPath_pegPath 1 π [] (by omega) rfl
    simp [slot?, this]
  const := fun π e => by
    rw [springAt_atom 1 π (by omega)] at e
    injection e with e'
    exact absurd e' (pegPath_ne_zero 1 π (by omega))

theorem rp_top {bus : Sock} {W : Cape} {x : Noun} (hx : Fits (Ca.app W bus) x) :
    RP bus W ⟨bus, A 1⟩ x x := by
  have hb : bus ≠ Sock.void := by
    intro e; subst e; rw [app_void] at hx; exact hx
  exact ⟨hx, provR_top hb x, statOK_top bus⟩

/-- **`WantSound` for one run**: the nomm of a run of `fol-loop` on the
identity `[bus fol]` satisfies `Annot` on every subject of its code
requirement `app:ca want bus`, given a table that is right relative to its
call sites and a well-formed subject sock. -/
theorem folLoop_wantSound {lib : Lib} {code : Bell → Option Nomm} {tab : Tab}
    (hT : RTab lib code tab) {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (hwf : WellFormed bus) (h : folLoopTop tab n bus fol = some (out, gen')) :
    Annot lib code (Fits (Ca.app gen'.want bus)) fol out.nomm :=
  ((folLoop_rgood (W := gen'.want) hT hwf n _ _ _ _ _ _ _ _ h (fun _ h => h)).annot).mono
    fun x hx => ⟨x, rp_top hx⟩

/-- **The product half**: on every subject of the code requirement, every
product of the function satisfies the provenance invariant with the
product sock and provenance of the run, and the static condition on `bus`.
This is what `hit_prod` assumes (`hR`) and what the table of a caller
asks of an `exact` answer. -/
theorem folLoop_relProd {lib : Lib} {code : Bell → Option Nomm} {tab : Tab}
    (hT : RTab lib code tab) {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (hwf : WellFormed bus) (h : folLoopTop tab n bus fol = some (out, gen'))
    {x : Noun} (hx : Fits (Ca.app gen'.want bus) x) {gul p : Noun}
    (hm : Mink lib gul [] x fol (Tone.zero p)) :
    ProvR x out.prod.sock out.prod.src p ∧ StatOK bus out.prod.sock out.prod.src := by
  have R := (folLoop_rgood (W := gen'.want) hT hwf n _ _ _ _ _ _ _ _ h (fun _ h => h)).prod
    x x gul p (rp_top hx) hm
  exact ⟨R.prov, R.stat⟩

end SkaModel
end Formalization
