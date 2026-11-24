import lemmas.Ska.KnowMeets

/-!
# `LessProvidesNF` from a cover of its sites

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
`L = [cl dl]`, masked by `cl`, is still under `L` (`sub_of_cover`).  For
example `ka = &+[5 7]` under `L = [[& |] [5 0]]` masks to `[[& |] [5 7]]`,
which is under `L`.  `SiteCover` states that such a `ka` exists for every
site, and `lessProvidesNF_of_cover` gives `LessProvidesNF` from it;
`pokeSites_of_cover` gives `PokeSites` from `SiteCover` of every poke.

## What is left: `SiteCover`, and why it is not split further here

A first split, tried and dropped, replayed the analysis' walk as a walk of
`+know` without folding under the identity's subject sock `more` with a
table `datA` of the products of the identities the analysis resolved, and
compared it with the walk under `less.cur` with `dat`.  Two things are wrong
with it:

1. `datA` cannot be a function of the bell.  One nomm can call two
   identities of one code bell at two sites, with different products: that
   is the `.indi` miss of `tools/hoon/prodsame.hoon`, where
   `[(f (add 2 3)) (f 5)]` calls two identities of the code bell of `f`.  A
   replay needs `+know` with a table indexed by the site (bell and site
   sock), that is a second model of the walk.
2. The comparison of the two walks is false for an arbitrary `datA`: a
   table whose products know more than `dat`'s makes the analysis' sites
   know more than `+know`'s.  It needs, as hypotheses, the residue
   (`ProdSame` between the identity used and `dat`'s, for every site sock
   that occurs, not only `less.c`) and the provenance fact that the analysis
   put into `want` every part of the subject that a callee's code
   requirement reads (`distribute lc s.prod.src` in `callStep`), so that
   masking `more` by `want` changes nothing that a site's callee needs.

Checked on the real compiler (runhoon.sh, 2026-11-24) where a `%he`
generalization ends a chain of identities of one code bell:
`tools/hoon/he2.hoon` (a gate `|=([n=@ a=*] ?:(=(0 n) .*(a a) $(n (dec n),
a [a 5]))))` and two variants, each grows `a`, a part used as a formula, so
the `.indi` test misses at every level) gives in each pruned graph one group
of 32 or 33 identities of one code bell, 992 or 1,056 ordered pairs, with no
failure of `ProdMeet` and no pair whose patched products under `less.c`
differ; with `he-threshold` raised the first poke did not end in 90 s, so
the `%he` step is what ends the chain.  `tools/hoon/he24.hoon` found after
the last poke 20 pairs of a code bell and a bake (7 strict) and 38 sites,
with no failure of `LessProvidesNF`, `KnowMeetsNF` or `SitesMeet`.

Inlining needs no case: an inlined call is the `%7` of the nomm that
`callStep` makes, and `+know` walks it as a `%7`, with the product of the
formula's subject as the inlined body's subject, as the analysis did.
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

/-! ## Monotone sock operations, for the comparison of two walks -/

/-- The cons of two blank socks is blank. -/
theorem knit_blank {A B : Sock} (hA : A.Blank) (hB : B.Blank) : (So.knit A B).Blank := by
  obtain ⟨l, d1, rfl, hl⟩ := hA
  obtain ⟨r, d2, rfl, hr⟩ := hB
  simp only [So.knit]
  split
  · exact dunno_blank
  · refine ⟨_, _, rfl, ?_⟩
    unfold Ca.con
    split
    · rfl
    · simp [Cape.isNo, hl, hr]

/-- **`+knit:so` is monotone**: a cons of socks that know more knows more. -/
theorem sub_knit {a a' b b' : Sock} (ha : Sub a a') (hb : Sub b b') : Sub (So.knit a b) (So.knit a' b') := by
  intro x hx
  rcases knit_fits_inv hx with ⟨b1, b2⟩ | ⟨x1, x2, rfl, h1, h2⟩
  · have e1 := blank_of_all fun z => ha z (b1.fits z)
    have e2 := blank_of_all fun z => hb z (b2.fits z)
    exact (knit_blank e1 e2).fits x
  · exact knit_fits (ha _ h1) (hb _ h2)

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

end Bake

namespace PokeM

open Bake

variable {M : Type → Type → Type} [Treap M] {J H R : Type}

/-- **`SiteCover` of every poke** from a state that satisfies `InvB`. -/
def PokeSiteCover (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    SiteCover (anaEnv jet fold frozen s f L j hot dats memo' rd reg')

/-- **`PokeLessNF` from `SiteCover` of every poke.** -/
theorem pokeLessNF_of_cover {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : PokeSiteCover lib env jet fold frozen fuel regOf) : PokeLessNF lib env jet fold frozen fuel regOf :=
  fun s f L j hot pr dats memo' rd reg' hI hs => lessProvidesNF_of_cover (h s f L j hot pr dats memo' rd reg' hI hs)

/-- **`PokeSites` from `SiteCover` of every poke.** -/
theorem pokeSites_of_cover {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : PokeSiteCover lib env jet fold frozen fuel regOf) : PokeSites lib env jet fold frozen fuel regOf :=
  pokeSites_of_lessNF (pokeLessNF_of_cover h)

end PokeM

end SkaModel
end Formalization
