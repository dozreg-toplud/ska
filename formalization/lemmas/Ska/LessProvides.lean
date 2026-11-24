import lemmas.Ska.KnowMeets

/-!
# `LessProvidesNF` split into named pieces

`LessProvidesNF` (`SitesMeetNF.lean`): under `less.cur` and without folding,
every site `[c k]` of `+know` provides its callee's code requirement
(`Sub k c.less`).  The argument compares `+know`'s walk with the analysis'
walk of the same nomm, site by site:

1. The analysis' site sock `ka` provides `c.less`: a `+git:mi` hit is checked
   by `+huge:so`, a new identity's requirement is `+app:ca` of the site sock,
   and `%rec` is checked against the frozen final entries.
2. `+know`'s site sock `k` knows, on the cape of `c.less`, whatever `ka`
   knows there (`Sub k (Ca.app cl ka)`).

The two give `Sub k c.less` by `sub_app_cape`: a sock with a noun under
`L = [cl dl]`, masked by `cl`, is still under `L`.  For example
`ka = &+[5 7]` under `L = [[& |] [5 0]]` masks to `[[& |] [5 7]]`, which is
under `L`.

The pieces, each a `def … : Prop`:

1. `SiteCover`: every site of `+know` without folding has such a `ka`.
   `lessProvidesNF_of_cover` gives `LessProvidesNF` from it.
2. `AnaReplay`: the analysis' walk of the nomm is a walk of `+know` without
   folding under the identity's subject sock `more` (under `less.cur`), with
   the products of the identities that the analysis resolved (`datA`), and
   every one of its sites provides its callee's code requirement.  A call that
   the analysis inlined is a `%7` of the nomm (`callStep`), which `+know`
   walks as a `%7`, so inlining needs no case of its own.
3. `WalkAgree`: the two walks of one nomm, under `less.cur` with `dat` and
   under `more` with `datA`, list the same callees in the same order, and the
   first walk's site knows on the callee's cape what the second's knows.
   This is where provenance (`ProvO`, `StatOK`) and the residue `ProdSame`
   enter: a part of a site that `c.less` knows comes from the subject through
   provenance (then `less.cur` knows it, since the analysis put it into
   `want`), from a constant, or from a callee's product, where `dat` and
   `datA` must agree.

`siteCover_of_parts`: `SiteCover` from `AnaReplay` and `WalkAgree`.
Neither is proved.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-! ## A masked sock under its mask's sock -/

theorem sub_blank {a : Sock} {c : Cape} {d : Noun} (hc : c.isNo = true) : Sub a (Sock.mk c d) :=
  fun x _ => FitsCape_isNo hc d x

/-- A sock under `[[h t] [dh dt]]` that is not blank: its head is under
`[h dh]`, and has a noun when the sock has one. -/
theorem sub_hed_of_cell {ka : Sock} {h t : Cape} {dh dt : Noun} (hy : ∃ y, Fits ka y)
    (hs : Sub ka (Sock.mk (Cape.cell h t) (C dh dt))) (hnb : (h.isNo && t.isNo) = false) :
    (Sub (So.hed ka) (Sock.mk h dh) ∧ ∃ y, Fits (So.hed ka) y) ∧
    (Sub (So.tel ka) (Sock.mk t dt) ∧ ∃ y, Fits (So.tel ka) y) := by
  obtain ⟨y, hy⟩ := hy
  have hys := hs y hy
  simp only [Fits, FitsCape] at hys
  rcases hys with hno | ⟨dh', dt', y1, y2, hd, rfl, _, _⟩
  · rw [hno] at hnb; cases hnb
  · cases hd
    refine ⟨⟨fun x1 hx1 => ?_, ⟨y1, hed_fits hy⟩⟩, ⟨fun x2 hx2 => ?_, ⟨y2, tel_fits hy⟩⟩⟩
    · have hc := hs _ (fits_join_of_cell hy hx1 (tel_fits hy))
      simp only [Fits, FitsCape] at hc
      rcases hc with hno | ⟨_, _, _, _, hd, he, h1, _⟩
      · rw [hno] at hnb; cases hnb
      · cases hd; cases he; exact h1
    · have hc := hs _ (fits_join_of_cell hy (hed_fits hy) hx2)
      simp only [Fits, FitsCape] at hc
      rcases hc with hno | ⟨_, _, _, _, hd, he, _, h2⟩
      · rw [hno] at hnb; cases hnb
      · cases hd; cases he; exact h2

/-- **A sock with a noun under `[cs ds]`, masked by `cs`, is still under
`[cs ds]`.** -/
theorem sub_app_cape : ∀ (cs : Cape) (ds : Noun) (ka : Sock), (∃ y, Fits ka y) →
    Sub ka (Sock.mk cs ds) → Sub (Ca.app cs ka) (Sock.mk cs ds)
  | Cape.no, _, _, _, _ => sub_blank rfl
  | Cape.yes, ds, ka, hy, hs => by
    cases ka with
    | void => obtain ⟨_, h⟩ := hy; exact absurd h id
    | mk ck dk =>
      by_cases h2 : ck = Cape.no
      · subst h2
        exfalso
        have h1 := hs (A 0) trivial
        have h2 := hs (C (A 0) (A 0)) trivial
        simp only [Fits, FitsCape] at h1 h2
        rw [← h1] at h2
        cases h2
      · have happ : Ca.app Cape.yes (Sock.mk ck dk) = Sock.mk ck dk := by
          unfold Ca.app
          by_cases h1 : Cape.yes = ck
          · rw [if_pos h1]
          · rw [if_neg h1, if_neg (by simp [h2])]
        rw [happ]
        exact hs
  | Cape.cell h t, ds, ka, hy, hs => by
    by_cases hb : (h.isNo && t.isNo) = true
    · exact sub_blank hb
    have hnb : (h.isNo && t.isNo) = false := by simpa using hb
    cases ka with
    | void => obtain ⟨_, h⟩ := hy; exact absurd h id
    | mk ck dk =>
    -- `ds` is a cell: a noun of `ka` fits `[[h t] ds]`, which is not blank
    obtain ⟨y, hy'⟩ := hy
    have hys := hs y hy'
    simp only [Fits, FitsCape] at hys
    rcases hys with hno | ⟨dh, dt, _, _, rfl, _, _, _⟩
    · rw [hno] at hnb; cases hnb
    have hparts := sub_hed_of_cell ⟨y, hy'⟩ hs hnb
    have ih1 := sub_app_cape h dh _ hparts.1.2 hparts.1.1
    have ih2 := sub_app_cape t dt _ hparts.2.2 hparts.2.1
    by_cases h2 : ck = Cape.no
    · subst h2
      intro x _
      exact hs x trivial
    by_cases h1 : Cape.cell h t = ck
    · have happ : Ca.app (Cape.cell h t) (Sock.mk ck dk) = Sock.mk ck dk := by
        unfold Ca.app
        rw [if_pos h1]
      rw [happ]
      exact hs
    have happ : Ca.app (Cape.cell h t) (Sock.mk ck dk) =
        So.knit (Ca.app h (So.hed (Sock.mk ck dk))) (Ca.app t (So.tel (Sock.mk ck dk))) := by
      rw [Ca.app.eq_def]
      dsimp only
      rw [if_neg h1, if_neg (by simp [h2])]
    rw [happ]
    intro x hx
    rcases knit_fits_inv hx with ⟨b1, b2⟩ | ⟨x1, x2, rfl, h1, h2⟩
    · -- both masks know nothing, so neither do `h` and `t`
      have e1 := isNo_of_all (c := h) (d := dh) fun z => ih1 z (b1.fits z)
      have e2 := isNo_of_all (c := t) (d := dt) fun z => ih2 z (b2.fits z)
      rw [e1, e2] at hnb; cases hnb
    · exact Or.inr ⟨dh, dt, x1, x2, rfl, rfl, ih1 x1 h1, ih2 x2 h2⟩

/-- **The site argument**: a site sock that knows, on the cape of the
callee's code requirement, what a sock with a noun under it knows, is under
it. -/
theorem sub_of_cover {k ka L : Sock} (hy : ∃ y, Fits ka y) (hs : Sub ka L)
    (hk : ∀ cl dl, L = Sock.mk cl dl → Sub k (Ca.app cl ka)) : Sub k L := by
  cases L with
  | void => obtain ⟨y, hy⟩ := hy; exact absurd (hs y hy) id
  | mk cl dl => exact fun x hx => sub_app_cape cl dl ka hy hs x (hk cl dl rfl x hx)

/-! ## The pieces -/

variable {M : Type → Type → Type} [Treap M]

/-- **Every site of `+know` without folding has a sock with a noun that
provides its callee's code requirement and knows, on that requirement's
cape, no more than the site.** -/
def SiteCover (E : BEnv M) : Prop :=
  ∀ cur d out sites, E.dat cur = some d → know false d.nomm cur.less E.dat idc = some (out, sites) →
    ∀ c k, (c, k) ∈ sites → c ≠ E.root →
      ∃ ka, (∃ y, Fits ka y) ∧ Sub ka c.less ∧ ∀ cl dl, c.less = Sock.mk cl dl → Sub k (Ca.app cl ka)

omit [Treap M] in
/-- **`LessProvidesNF` from `SiteCover`.** -/
theorem lessProvidesNF_of_cover {E : BEnv M} (h : SiteCover E) : LessProvidesNF E := by
  intro cur d out sites hd hk c k hck hc
  obtain ⟨ka, hy, hs, hcov⟩ := h cur d out sites hd hk c k hck hc
  exact sub_of_cover hy hs hcov

/-- **The analysis' walk as a walk of `+know`**: for every datum of `dat`
there are the identity's subject sock `more` (with a noun, under
`less.cur`) and the products `datA` of the identities the analysis
resolved, such that `+know` without folding under `more` with `datA` returns
on the nomm, and every one of its sites (but the root's) has a noun and
provides its callee's code requirement. -/
def AnaReplay (E : BEnv M) : Prop :=
  ∀ cur d, E.dat cur = some d →
    ∃ (more : Sock) (datA : Bell → Option Datum) (outA : Nomm) (sitesA : List Site),
      (∃ y, Fits more y) ∧ Sub more cur.less ∧
      know false d.nomm more datA idc = some (outA, sitesA) ∧
      ∀ c ka, (c, ka) ∈ sitesA → c ≠ E.root → (∃ y, Fits ka y) ∧ Sub ka c.less

/-- **The two walks of one nomm agree on the callees' capes**: under
`less.cur` with `dat` and under the analysis' `more` with its `datA`, every
site of the first (but the root's) has a site of the same callee in the
second that knows, on the callee's cape, no more than it. -/
def WalkAgree (E : BEnv M) : Prop :=
  ∀ cur d more datA outA sitesA out sites, E.dat cur = some d →
    (∃ y, Fits more y) → Sub more cur.less →
    know false d.nomm more datA idc = some (outA, sitesA) →
    know false d.nomm cur.less E.dat idc = some (out, sites) →
    ∀ c k, (c, k) ∈ sites → c ≠ E.root →
      ∃ ka, (c, ka) ∈ sitesA ∧ ∀ cl dl, c.less = Sock.mk cl dl → Sub k (Ca.app cl ka)

omit [Treap M] in
/-- **`SiteCover` from `AnaReplay` and `WalkAgree`.** -/
theorem siteCover_of_parts {E : BEnv M} (ha : AnaReplay E) (hw : WalkAgree E) : SiteCover E := by
  intro cur d out sites hd hk c k hck hc
  obtain ⟨more, datA, outA, sitesA, hmy, hms, hka, hok⟩ := ha cur d hd
  obtain ⟨ka, hkam, hcov⟩ := hw cur d more datA outA sitesA out sites hd hmy hms hka hk c k hck hc
  obtain ⟨hy, hs⟩ := hok c ka hkam hc
  exact ⟨ka, hy, hs, hcov⟩

omit [Treap M] in
/-- **`LessProvidesNF` from `AnaReplay` and `WalkAgree`.** -/
theorem lessProvidesNF_of_parts {E : BEnv M} (ha : AnaReplay E) (hw : WalkAgree E) : LessProvidesNF E :=
  lessProvidesNF_of_cover (siteCover_of_parts ha hw)

end Bake

namespace PokeM

open Bake

variable {M : Type → Type → Type} [Treap M] {J H R : Type}

/-- **`AnaReplay` and `WalkAgree` of every poke** from a state that
satisfies `InvB`. -/
def PokeLessParts (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    let E := anaEnv jet fold frozen s f L j hot dats memo' rd reg'
    AnaReplay E ∧ WalkAgree E

/-- **`PokeLessNF` from the two pieces.** -/
theorem pokeLessNF_of_parts {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : PokeLessParts lib env jet fold frozen fuel regOf) : PokeLessNF lib env jet fold frozen fuel regOf :=
  fun s f L j hot pr dats memo' rd reg' hI hs =>
    let ⟨ha, hw⟩ := h s f L j hot pr dats memo' rd reg' hI hs
    lessProvidesNF_of_parts ha hw

/-- **`PokeSites` from the two pieces.** -/
theorem pokeSites_of_lessParts {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : PokeLessParts lib env jet fold frozen fuel regOf) : PokeSites lib env jet fold frozen fuel regOf :=
  pokeSites_of_lessNF (pokeLessNF_of_parts h)

end PokeM

end SkaModel
end Formalization
