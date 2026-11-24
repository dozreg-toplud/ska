import lemmas.Ska.SiteCover

/-!
# `SitesMeet` is false on the real compiler, and so is `BakesImply`

`tools/hoon/bakedrop.hoon` (runhoon.sh, 2026-11-24) pokes `bakeDropWitness`
below on `&+lib` and finds a site of `+know` under a bake (with the default
`fold`, for the strict bake and for the pair at `less.c`) whose sock shares
no noun with its callee's code requirement, so `SitesMeet` fails, and a
variant whose bake is not under its code bell's code requirement, so
`BakesImply` (`bakes_ok_of_meet`, `PokeBakes`) fails too.  `KnowMeetsNF`
holds there (0 failures) and `LessProvidesNF` fails, as for
`voidSccWitness`.

The core is `C = [[armR armF] 0]`, and the root kicks `armR` on it.  `armR`
is `[2 [6 [1 0] [[1 [[3 0] 5]] [9 5 0 1]] [1 [[[1 7] 5] 9]]] [1 H]]` with
`H = [2 [0 1] [0 4]]`: if `0 = 0` then `[[[3 0] 5] (armF C)]`, else
`[[[1 7] 5] 9]`, and then `H` on the product.  `armF` is
`[8 [9 4 0 1] [9 5 0 3]]`, which calls `armR`, then itself, so it never
returns, and the two are one SCC.

1. The analysis never folds a `%6`.  `armR`'s last run reads `armF`'s
   product `%void` (in progress), so the first branch is `%void`
   (`+knit:so` with `%void`), `+double-int` keeps the second, and `H` is
   called at `&+[[[1 7] 5] 9]`.  `H` reads axis `4` as a formula, so its code
   bell requires `[[[& |] |] [[[1 7] 0] 0]]` (axis `4` is `[1 7]`).
2. `+know` under `armR`'s bake folds the literal test `[1 0]` to the first
   branch, where `armF`'s product is the `|+~` of `+pop`, so the site of `H`
   knows `[[& |] [[[3 0] 5] 0]]` (axis `4` is `[3 0]`).  The two share no
   noun (`witness_no_meet`).
3. `+uni-sock` of the code requirement and that site keeps the fully known
   side, so `H`'s variant has the bake `[[& |] [[[3 0] 5] 0]]`
   (`bakeok.hoon`'s check: 1 bad pair).

Within this poke the compiled code is not wrong (a later poke makes it
wrong, `VariantCollision.lean`): the site lies after a call that never
returns, and a live site naming `H`'s code bell knows axis `4` is `[1 7]`, so
it never provides that bake and `+pick` never sends it to the variant.  What
fails is the invariant: a variant's code is right on the subjects that fit
both its bake and its code bell's code requirement (`variant_annot`), which
for this variant are none.  So no route can prove `SitesMeet` or
`PokeSites`, and the routes through `LessProvidesNF`, `SiteCover`,
`Compare`, `PokeLessNF`, `PokeSiteCover` (refuted by `voidSccWitness`) and
through a reference walk with the analysis' `%void` products kept are all
closed.  The theorems that assume `SitesMeet` or `PokeSites`
(`bakes_ok_of_meet`, `skaPokeB_sound`, `anaHyp_of_meet`, `gap_of_meet`,
`sitesMeet_of_parts`, `sitesMeet_of_nf`, `sitesMeet_of_lessNF`) stay true
but cannot be used: their hypothesis is false for this poke.

The same poke with the test `[5 [1 0] [1 0]]` fails the same way.
`voidSccWitness` did not fail `SitesMeet` only because its test
`[5 [1 0] [4 [1 0]]]` folds to the branch the analysis kept.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-- The root formula of `tools/hoon/bakedrop.hoon`, poked on `&+lib`: a
witness against `SitesMeet` and `BakesImply` on the real compiler. -/
def bakeDropWitness : Noun :=
  let armR : Noun :=
    C (A 2) (C (C (A 6) (C (C (A 1) (A 0))
      (C (C (C (A 1) (C (C (A 3) (A 0)) (A 5))) (C (A 9) (C (A 5) (C (A 0) (A 1)))))
        (C (A 1) (C (C (C (A 1) (A 7)) (A 5)) (A 9))))))
      (C (A 1) (C (A 2) (C (C (A 0) (A 1)) (C (A 0) (A 4))))))
  let armF : Noun := C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 1)))) (C (A 9) (C (A 5) (C (A 0) (A 3)))))
  C (A 7) (C (C (A 1) (C (C armR armF) (A 0))) (C (A 9) (C (A 4) (C (A 0) (A 1)))))

/-- The code requirement of `H`'s code bell on the real compiler. -/
def witnessLessH : Sock :=
  Sock.mk (Cape.cell (Cape.cell Cape.yes Cape.no) Cape.no) (C (C (C (A 1) (A 7)) (A 0)) (A 0))

/-- The sock of `H`'s site under `armR`'s bake, and the bake of `H`'s
variant, on the real compiler. -/
def witnessSiteH : Sock :=
  Sock.mk (Cape.cell Cape.yes Cape.no) (C (C (C (A 3) (A 0)) (A 5)) (A 0))

/-- **The site and the code requirement share no noun**: one says axis `4`
is `[1 7]`, the other that it is `[3 0]`. -/
theorem witness_no_meet : ¬ ∃ y, Fits witnessLessH y ∧ Fits witnessSiteH y := by
  rintro ⟨y, h1, h2⟩
  simp only [witnessLessH, witnessSiteH, Fits, FitsCape, Cape.isNo] at h1 h2
  rcases h2 with h2 | ⟨dh, dt, nh, nt, hd, hn, hh, -⟩
  · simp at h2
  · rcases h1 with h1 | ⟨dh', dt', nh', nt', hd', hn', hh', -⟩
    · simp at h1
    · subst hn
      cases hd; cases hd'
      simp only [C, Noun.cell.injEq] at hn'
      obtain ⟨rfl, rfl⟩ := hn'
      subst hh
      rcases hh' with h | ⟨a, b, c, e, hda, hnc, hf, -⟩
      · simp at h
      · simp only [C, Noun.cell.injEq] at hda hnc
        obtain ⟨rfl, rfl⟩ := hda
        obtain ⟨rfl, rfl⟩ := hnc
        simp_all

end Bake

end SkaModel
end Formalization
