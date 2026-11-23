import lemmas.Ska.FolLoopRel
import lemmas.Ska.MinkFuel

/-!
# The product half of `folLoop_rgood`, with the fuel of `+mink`

`folLoop_rprod` is the `prod` field of `folLoop_rgood` for the runs of
`+mink` with fuel `K + 1`, from a table whose answers are right on products
only for the runs of their callees with fuel `K` (`RTabP`).  Nock 2 with
fuel `K + 1` runs its callee with fuel `K` (`minkF_inv_n2`), and every other
case runs its parts with fuel `K` too, which a run with fuel `K + 1` covers
(`minkF_up`).  At convergence the table is made of the entries themselves,
so this is the step of the induction on the fuel in `ConvergeProd.lean`.

The `saf` field of `RGood` goes along, because the cons case needs it, and
it is fuel-free.  The fields `annot`, `safe` and `sff` are not needed: the
inlined call uses only that the formula is known on every product of the
formula-formula, which the `prod` field of that formula-formula gives.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The `less` field of `RTab`: what a callee's code requirement holds of. -/
def RTabL (tab : Tab) : Prop :=
  ∀ s f d lc dl, tab s f = some d → s ≠ Sock.void → d.less = Sock.mk lc dl →
    ∀ y, Fits (Ca.app lc s) y → Fits d.less y

/-- The `prod` field of `RTab`, for the runs of the callee with fuel `K`. -/
def RTabP (lib : Lib) (tab : Tab) (K : Nat) : Prop :=
  ∀ s f d, tab s f = some d → s ≠ Sock.void → ∀ y gul p, Fits d.less y →
    minkF lib gul K [] y f = some (Tone.zero p) → ProvR y d.prod d.map p ∧ StatOK s d.prod d.map

theorem RTab.toL {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} (h : RTab lib code tab) :
    RTabL tab := h.less

/-- The `prod` and `saf` fields of `RGood`, the first for runs with fuel `K + 1`. -/
structure RProd (lib : Lib) (bus : Sock) (W : Cape) (K : Nat) (fol : Noun) (sub : Anno)
    (out : FolOut) : Prop where
  prod : ∀ X' z gul p, RP bus W sub X' z → minkF lib gul (K + 1) [] z fol = some (Tone.zero p) →
    RP bus W out.prod X' p
  saf : out.saf = true →
    ∃ d, out.prod.sock = Sock.mk Cape.yes d ∧ ∀ x gul, Mink lib gul [] x fol (Tone.zero d)

/-- Every result of the recursion whose `want` `W` covers is `RProd`. -/
def GoRProd (lib : Lib) (bus : Sock) (W : Cape) (K : Nat) (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') → WCov W gen' →
    RProd lib bus W K fol sub out

theorem RProd.of_plain {lib : Lib} {bus : Sock} {W : Cape} {K : Nat} {fol : Noun} {sub : Anno}
    {out : FolOut}
    (hp : ∀ X' z gul p, RP bus W sub X' z → minkF lib gul (K + 1) [] z fol = some (Tone.zero p) →
      RP bus W out.prod X' p)
    (hsaf : out.saf = false) : RProd lib bus W K fol sub out where
  prod := hp
  saf := fun h => by rw [hsaf] at h; cases h

theorem RProd.of_dunno {lib : Lib} {bus : Sock} {W : Cape} {K : Nat} {fol : Noun} {sub : Anno}
    {out : FolOut} (hd : out.prod = Anno.dunno) (hsaf : out.saf = false) :
    RProd lib bus W K fol sub out :=
  RProd.of_plain (fun X' _ _ _ hz _ => by
    rw [hd]; exact ⟨hz.req, provO_iff.mp (provO_dunno X' _), statOK_dunno _ _⟩) hsaf

/-- A `%bare` call, the call with `bc` set: its product is not known, or a
side is `%void`, and it is not safe. -/
theorem callStep_bare_prod {tab : Tab} {go : FolGo} {mk : Option Noun} {df : Bool}
    {s f out : FolOut} {g gen' : Gen} (h : callStep tab go mk true df s f g = some (out, gen')) :
    out.saf = false ∧ (out.prod = Anno.dunno ∨ s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void) := by
  unfold callStep at h
  split at h
  · rename_i hv
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact ⟨rfl, Or.inr hv⟩
  · split at h
    · rename_i hb; cases hb
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨rfl, Or.inl rfl⟩

section Cases

variable {lib : Lib} {tab : Tab} {go : FolGo} {bus : Sock} {W : Cape} {K : Nat}
  {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

/-! ## The cases without calls -/

theorem rprod_other (hs : shape fol = Shape.other)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact RProd.of_dunno rfl rfl

theorem rprod_op1 {p : Noun} (hs : shape fol = Shape.op1 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact {
    prod := fun X' _ _ _ hz hm => by
      rw [minkF_inv_n1 hm]; exact ⟨hz.req, provO_iff.mp (provO_yes X' p), statOK_zero _ _⟩
    saf := fun _ => ⟨p, rfl, fun x _ => mink_mk_n1 x p⟩ }

theorem rprod_op0 {p : Nat} (hs : shape fol = Shape.op0 p)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨pr, hpr, rfl, rfl⟩ := h
  refine RProd.of_plain ?_ rfl
  intro X' z gul y hz hm
  have hy := minkF_inv_n0 hm
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

/-- The cases whose product is not known: `%3`, `%4`, `%5`, `%12`. -/
theorem rprod_op3 {a b : Noun} (hs : shape fol = Shape.op3 a b)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl, rfl⟩ := h
  exact RProd.of_dunno rfl rfl

theorem rprod_op4 {a b : Noun} (hs : shape fol = Shape.op4 a b)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl, rfl⟩ := h
  exact RProd.of_dunno rfl rfl

theorem rprod_op5 {a b q : Noun} (hs : shape fol = Shape.op5 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, rfl, rfl⟩ := h
  exact RProd.of_dunno rfl rfl

theorem rprod_op12 {a b q : Noun} (hs : shape fol = Shape.op12 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) : RProd lib bus W K fol sub out := by
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, rfl, rfl⟩ := h
  exact RProd.of_dunno rfl rfl

theorem rprod_op6 (IH : GoRProd lib bus W K go) (hM : GoMono go) {a b q r : Noun}
    (hs : shape fol = Shape.op6 a b q r) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, ⟨r', g3⟩, h3, rfl, rfl⟩ := h
  have W3 : WCov W g3 := hW
  have W2 : WCov W g2 := hW.of_le (hM _ _ _ _ _ _ _ _ h3)
  have Gq := IH _ _ _ _ _ _ _ _ h2 W2
  have Gr := IH _ _ _ _ _ _ _ _ h3 W3
  refine RProd.of_plain ?_ rfl
  intro X' x gul y hx hm
  rcases minkF_inv_n6 hm with hc | hd
  · have R := Gq.prod X' x gul y hx (minkF_up hc)
    exact ⟨R.req, provO_iff.mp (provO_doubleInt_left _ _ (provO_iff.mpr R.prov)),
      statOK_doubleInt_left _ _ R.prov.nonvoid R.stat⟩
  · have R := Gr.prod X' x gul y hx (minkF_up hd)
    exact ⟨R.req, provO_iff.mp (provO_doubleInt_right _ _ (provO_iff.mpr R.prov)),
      statOK_doubleInt_right _ _ R.prov.nonvoid R.stat⟩

theorem rprod_op7 (IH : GoRProd lib bus W K go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.op7 a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨p, g1⟩, h1, ⟨q', g2⟩, h2, rfl, rfl⟩ := h
  have Gp := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Gq := IH _ _ _ _ _ _ _ _ h2 hW
  refine RProd.of_plain ?_ rfl
  intro X' x gul y hx hm
  obtain ⟨z, m1, m2⟩ := minkF_inv_n7 hm
  exact Gq.prod X' z gul y (Gp.prod X' x gul z hx (minkF_up m1)) (minkF_up m2)

theorem rprod_cons (IH : GoRProd lib bus W K go) (hM : GoMono go) {a b q : Noun}
    (hs : shape fol = Shape.cons a b q) (h : folStep tab go fol sub mk bc df gen = some (out, gen'))
    (hW : WCov W gen') : RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
  have Gl := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
  have Gr := IH _ _ _ _ _ _ _ _ h2 hW
  refine ⟨?_, ?_⟩
  · intro X' x gul p hx hm
    obtain ⟨p1, p2, rfl, m1, m2⟩ := minkF_inv_cons hm
    have R1 := Gl.prod X' x gul p1 hx (minkF_up m1)
    have R2 := Gr.prod X' x gul p2 hx (minkF_up m2)
    unfold consProd
    split
    · rename_i hc
      obtain ⟨dl, hl, ml⟩ := Gl.saf hc.1
      obtain ⟨dr, hr, mr⟩ := Gr.saf hc.2.1
      have e1 := Mink.det ⟨_, m1⟩ (ml x gul)
      have e2 := Mink.det ⟨_, m2⟩ (mr x gul)
      cases e1; cases e2
      simp only [hl, hr, Sock.data]
      exact ⟨hx.req, provO_iff.mp (provO_yes X' _), statOK_zero _ _⟩
    · refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R1.stat R2.stat⟩
      · rw [slotO_some_cell_false]; exact provO_iff.mpr R1.prov
      · rw [slotO_some_cell_true]; exact provO_iff.mpr R2.prov
  · unfold consProd
    split
    · rename_i hc
      intro _
      obtain ⟨dl, hl, ml⟩ := Gl.saf hc.1
      obtain ⟨dr, hr, mr⟩ := Gr.saf hc.2.1
      refine ⟨C dl dr, ?_, fun x gul => mink_mk_cons (ml x gul) (mr x gul)⟩
      simp only [hl, hr, Sock.data]
    · intro h; cases h

/-! ## Calls -/

theorem rprod_call (hL : RTabL tab) (hP : RTabP lib tab K) (hwf : WellFormed bus)
    (IH : GoRProd lib bus W K go) (hM : GoMono go) {b c : Noun} {s f : FolOut}
    (Gs : RProd lib bus W K b sub s) (Gf : RProd lib bus W K c sub f) {g2 : Gen}
    (h : callStep tab go mk bc df s f g2 = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K (n3 (A 2) b c) sub out := by
  unfold callStep at h
  split at h
  · -- a void subject or formula: no run reaches the call
    rename_i hv
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine RProd.of_plain ?_ rfl
    intro X' x gul p hx hm
    obtain ⟨y, g, m1, m2, _⟩ := minkF_inv_n2 hm
    have f1 := (Gs.prod X' x gul y hx (minkF_up m1)).prov.nonvoid
    have f2 := (Gf.prod X' x gul g hx (minkF_up m2)).prov.nonvoid
    rcases hv with hv | hv
    · exact absurd hv f1
    · exact absurd hv f2
  · rename_i hv
    simp only [not_or] at hv
    split at h
    · rename_i fa fb hfp
      -- the formula of the call is known
      have hg : (∀ q, (distribute Cape.yes f.prod.src).Has q → W.Has q) →
          ∀ X' x gul g, RP bus W sub X' x → minkF lib gul (K + 1) [] x c = some (Tone.zero g) →
            g = C fa fb := by
        intro hWf X' x gul g hx hm
        have R := Gf.prod X' x gul g hx hm
        have := known_at (provO_iff.mpr R.prov) R.stat R.req [] (by simpa [springAt] using hWf)
          (by rw [hfp]; rfl)
        simpa [slotO, slotAtPath] using this
      split at h
      · -- inlined
        simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨i, g3⟩, hi, rfl, rfl⟩ := h
        have hWf : ∀ q, (distribute Cape.yes f.prod.src).Has q → W.Has q := fun q hq =>
          hW q (hM _ _ _ _ _ _ _ _ hi q (by show (Ca.uni _ _).Has q; rw [uni_has]; exact Or.inr hq))
        have Gi := IH _ _ _ _ _ _ _ _ hi hW
        refine RProd.of_plain ?_ rfl
        intro X' x gul p hx hm
        obtain ⟨y, g, m1, m2, m3⟩ := minkF_inv_n2 hm
        rw [hg hWf X' x gul g hx (minkF_up m2)] at m3
        exact Gi.prod X' y gul p (Gs.prod X' x gul y hx (minkF_up m1)) (minkF_up m3)
      · -- a direct call: the callee runs with fuel `K`
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
          refine RProd.of_plain ?_ rfl
          intro X' x gul p hx hm
          obtain ⟨y, g, m1, m2, m3⟩ := minkF_inv_n2 hm
          rw [hg hWf X' x gul g hx (minkF_up m2)] at m3
          have R := Gs.prod X' x gul y hx (minkF_up m1)
          have hless : Fits d.less y :=
            hL _ _ d lc dl hd hv.1 hdl y (call_sub_fits (provO_iff.mpr R.prov) R.stat hwf R.req hWs)
          obtain ⟨hpR, hpS⟩ := hP _ _ d hd hv.1 y gul p hless m3
          refine ⟨R.req, ?_, statOK_compose hv.1 R.stat hpS⟩
          exact provO_iff.mp (provO_compose (provO_iff.mpr R.prov) (provO_iff.mpr hpR)
            (hpS.toStatS hpR.nonvoid) (hpS.toShapeOK hpR.nonvoid))
    · -- an indirect call
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact RProd.of_dunno rfl rfl

theorem rprod_op2 (hL : RTabL tab) (hP : RTabP lib tab K) (hwf : WellFormed bus)
    (IH : GoRProd lib bus W K go) (hM : GoMono go) {a b q : Noun} (hs : shape fol = Shape.op2 a b q)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, Option.bind_eq_some_iff] at h
  obtain ⟨⟨s', g1⟩, h1, ⟨f', g2⟩, h2, h⟩ := h
  have W2 : WCov W g2 := hW.of_le (callStep_mono hM h)
  have W1 : WCov W g1 := W2.of_le (hM _ _ _ _ _ _ _ _ h2)
  exact rprod_call hL hP hwf IH hM (IH _ _ _ _ _ _ _ _ h1 W1) (IH _ _ _ _ _ _ _ _ h2 W2) h hW

/-! ## Edits and hints -/

theorem rprod_op10 (IH : GoRProd lib bus W K go) (hM : GoMono go) {ax : Nat} {don r1 r2 : Noun}
    (hs : shape fol = Shape.op10 ax don r1 r2)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact RProd.of_dunno rfl rfl
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, sk, hd, rfl, rfl⟩ := h
    have Gd := IH _ _ _ _ _ _ _ _ h1 (hW.of_le (hM _ _ _ _ _ _ _ _ h2))
    have Gr := IH _ _ _ _ _ _ _ _ h2 hW
    refine RProd.of_plain ?_ rfl
    intro X' x gul p hx hm
    obtain ⟨tg, vv, m1, m2, he⟩ := minkF_inv_n10 hm
    have R1 := Gr.prod X' x gul tg hx (minkF_up m1)
    have R2 := Gd.prod X' x gul vv hx (minkF_up m2)
    exact ⟨hx.req, provO_iff.mp (provO_darn (provO_iff.mpr R1.prov) (provO_iff.mpr R2.prov) he hd),
      statOK_darn R1.stat R2.stat hd⟩

theorem rprod_op11s_plain (IH : GoRProd lib bus W K go) {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p ≠ Tag.bare)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K fol sub out := by
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, hp, if_false, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨q, g1⟩, h1, rfl, rfl⟩ := h
  have Gq := IH _ _ _ _ _ _ _ _ h1 hW
  exact RProd.of_plain (fun X' x gul y hx hm => Gq.prod X' x gul y hx (minkF_up (minkF_inv_n11s hm))) rfl

theorem rprod_op11d (IH : GoRProd lib bus W K go) (hM : GoMono go) {tag : Nat} {h1 h2 f : Noun}
    (hs : shape fol = Shape.op11d tag h1 h2 f)
    (h : folStep tab go fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K fol sub out := by
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
    refine ⟨fun X' x gul p hx hm => G'.prod X' x gul p hx (minkF_mk_self (minkF_inv_n11d hm).2), ?_⟩
    intro hs'
    obtain ⟨d, hd, md⟩ := G'.saf hs'
    exact ⟨d, hd, fun x gul => (mink_memo_iff ⟨dh, mh x gul⟩).mpr (md x gul)⟩
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨arm, g2⟩, ha, ⟨fr, g3⟩, hf1, rfl, rfl⟩ := h
    have Gf := IH _ _ _ _ _ _ _ _ hf1 hW
    have Gh := IH _ _ _ _ _ _ _ _ hh1
      ((hW.of_le (hM _ _ _ _ _ _ _ _ hf1)).of_le (meanArm_mono hM ha))
    refine ⟨fun X' x gul p hx hm => Gf.prod X' x gul p hx (minkF_up (minkF_inv_n11d hm).2), ?_⟩
    intro hd
    simp only [decide_eq_true_eq] at hd
    obtain ⟨d1, _, m1⟩ := Gh.saf hd.2.1
    obtain ⟨d2, e2, m2⟩ := Gf.saf hd.2.2
    exact ⟨d2, e2, fun x gul => mink_mk_n11d _ (m1 x gul) (m2 x gul)⟩

/-! ## The rewritten cases: `%8`, `%9`, `%bare` -/

/-- `%bare` is the call `[2 [0 1] 1 fol]` with `bc` set, whose product is
not known: so nothing about the fuel is needed. -/
theorem rprod_bare {m : Nat} {p : Nat} {a b : Noun}
    (hs : shape fol = Shape.op11s p a b) (hp : p = Tag.bare)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) :
    RProd lib bus W K fol sub out := by
  subst hp
  have hf := shape_eq hs (by simp)
  simp only [Shape.fol] at hf
  subst hf
  simp only [folStep, hs, if_true] at h
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
  obtain ⟨hsaf, hd⟩ := callStep_bare_prod h
  rcases hd with hd | hd | hd
  · exact RProd.of_dunno hd hsaf
  · refine RProd.of_plain (fun X' z gul y hz _ => absurd hd hz.prov.nonvoid) hsaf
  · exact absurd hd (by simp)

theorem rprod_op9 {m : Nat} (IH' : ∀ k, k + 1 = m → GoRProd lib bus W K (folLoopF tab k))
    {p : Nat} {a b : Noun} (hs : shape fol = Shape.op9 p a b)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K fol sub out := by
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
  refine RProd.of_plain ?_ rfl
  intro X' x gul y hx hm
  obtain ⟨core, arm, m1, hsl, m2⟩ := minkF_inv_n9 hm
  exact G2.prod X' core gul y (G1.prod X' x gul core hx (minkF_up m1)) (minkF_mk_arm hsl m2)

theorem rprod_op8 {m : Nat} (IH' : ∀ k, k < m → GoRProd lib bus W K (folLoopF tab k))
    {a b q : Noun} (hs : shape fol = Shape.op8 a b q)
    (h : folStep tab (folLoopF tab m) fol sub mk bc df gen = some (out, gen')) (hW : WCov W gen') :
    RProd lib bus W K fol sub out := by
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
  refine RProd.of_plain ?_ rfl
  intro X' x gul p hx hm
  obtain ⟨y, m1, m2⟩ := minkF_inv_n8 hm
  have R := Gb.prod X' x gul y hx (minkF_up m1)
  have hsub : RP bus W ⟨So.knit ob.prod.sock sub.sock, Pi.cons ob.prod.src sub.src⟩ X' (C y x) := by
    refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R.stat hx.stat⟩
    · rw [slotO_some_cell_false]; exact provO_iff.mpr R.prov
    · rw [slotO_some_cell_true]; exact provO_iff.mpr hx.prov
  exact G2.prod X' (C y x) gul p hsub (minkF_up m2)

end Cases

/-! ## The main theorem -/

/-- **The product half of `fol-loop`'s soundness, with the fuel of
`+mink`**: given that the table's answers are right on products for the
runs of their callees with fuel `K` (`hP`), every result whose `want` `W`
covers is right on products for the runs with fuel `K + 1`. -/
theorem folLoop_rprod {lib : Lib} {tab : Tab} {bus : Sock} {W : Cape} {K : Nat}
    (hL : RTabL tab) (hP : RTabP lib tab K) (hwf : WellFormed bus) :
    ∀ n, GoRProd lib bus W K (folLoopF tab n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro fol sub mk bc df gen out gen' h hW
  cases n with
  | zero => simp [folLoopF] at h
  | succ m =>
  rw [folLoopF_succ] at h
  have IH : GoRProd lib bus W K (folLoopF tab m) := ih m (by omega)
  have hM : GoMono (folLoopF tab m) := folLoopF_want_mono tab m
  cases hs : shape fol with
  | cons a b q => exact rprod_cons IH hM hs h hW
  | op0 p => exact rprod_op0 hs h
  | op1 p => exact rprod_op1 hs h
  | op2 a b q => exact rprod_op2 hL hP hwf IH hM hs h hW
  | op3 a b => exact rprod_op3 hs h
  | op4 a b => exact rprod_op4 hs h
  | op5 a b q => exact rprod_op5 hs h
  | op6 a b q r => exact rprod_op6 IH hM hs h hW
  | op7 a b q => exact rprod_op7 IH hM hs h hW
  | op8 a b q => exact rprod_op8 (fun k hk => ih k (by omega)) hs h hW
  | op9 p a b => exact rprod_op9 (fun k hk => ih k (by omega)) hs h hW
  | op10 ax don r1 r2 => exact rprod_op10 IH hM hs h hW
  | op11s p a b =>
    by_cases hp : p = Tag.bare
    · exact rprod_bare hs hp h
    · exact rprod_op11s_plain IH hs hp h hW
  | op11d tag h1 h2 f => exact rprod_op11d IH hM hs h hW
  | op12 a b q => exact rprod_op12 hs h
  | other => exact rprod_other hs h

/-- **The product half for a function, with fuel**: on every subject of
the code requirement, every product of a run of `+mink` with fuel `K + 1`
satisfies the provenance invariant with the product sock and provenance of
the run of `fol-loop`, and the static condition on `bus`. -/
theorem folLoop_relProdN {lib : Lib} {tab : Tab} {K : Nat} (hL : RTabL tab) (hP : RTabP lib tab K)
    {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (hwf : WellFormed bus) (h : folLoopTop tab n bus fol = some (out, gen'))
    {x : Noun} (hx : Fits (Ca.app gen'.want bus) x) {gul p : Noun}
    (hm : minkF lib gul (K + 1) [] x fol = some (Tone.zero p)) :
    ProvR x out.prod.sock out.prod.src p ∧ StatOK bus out.prod.sock out.prod.src := by
  have R := (folLoop_rprod (W := gen'.want) hL hP hwf n _ _ _ _ _ _ _ _ h (fun _ h => h)).prod
    x x gul p (rp_top hx) hm
  exact ⟨R.prov, R.stat⟩

end SkaModel
end Formalization
