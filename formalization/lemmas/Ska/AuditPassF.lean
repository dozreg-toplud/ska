import lemmas.Ska.PassMeasureK

/-! The axioms of the theorems of track F (`Ska/PassMeasure.lean`,
`Ska/PassMeasureK.lean`, README Gaps 16), and checks of the measure of
`PassMeasureK.lean` on the runs that broke the first guess of it.  `lake build` prints them; each should be `propext`,
`Classical.choice` and `Quot.sound` at most. -/

open Formalization.SkaModel

#print axioms capeLe_refl
#print axioms capeLe_no_inv
#print axioms capeLe_uni_right
#print axioms uni_denorm_example
#print axioms doubleInt_dunno_old
#print axioms msgAnno_dunno_old
#print axioms mergeProd_dunno_old
#print axioms runDatum_dunno_prod
#print axioms genZ_k
#print axioms app_mono
#print axioms app_idem
#print axioms less_genZ
#print axioms mergeProd_genZ
#print axioms runDatum_prod_step
#print axioms runDatum_less_step
#print axioms less_untidy_example
#print axioms doubleInt_map
#print axioms msgAnno_map
#print axioms runDatum_map_step
#print axioms capeLe_msgCa
#print axioms runDatum_indi_seek
#print axioms runDatum_measure

open Formalization.Nock

/- The six runs where `less-code` went from `[[& &] |]` to `[& |]` over the
same nouns: the weight rises. -/
#guard kS (Sock.mk (Cape.cell (Cape.cell Cape.yes Cape.yes) Cape.no) (C (C (A 1) (A 2)) (A 0))) <
  kS (Sock.mk (Cape.cell Cape.yes Cape.no) (C (C (A 1) (A 2)) (A 0)))

/- The 51 map-only runs with a product that knows a cell: provenance lost
under a `|` leaf (`1` to `[2 0]`, `[2 [6 7]]` to `[2 [0 7]]`) lowers `mapL`;
the map spelled out along the cells (`1` to `[2 [6 7]]`) keeps `mapL` and
lowers `mapA`. -/
#guard mapL (Cape.cell Cape.yes Cape.no) (C (A 2) (A 0)) < mapL (Cape.cell Cape.yes Cape.no) (A 1)
#guard mapL (Cape.cell Cape.yes (Cape.cell Cape.no Cape.yes)) (C (A 2) (C (A 0) (A 7))) <
  mapL (Cape.cell Cape.yes (Cape.cell Cape.no Cape.yes)) (C (A 2) (C (A 6) (A 7)))
#guard mapL (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (C (A 2) (C (A 6) (A 7))) =
  mapL (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (A 1)
#guard mapA (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (C (A 2) (C (A 6) (A 7))) <
  mapA (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (A 1)

/- And `+double-int` makes that last move itself: the same product with the
maps `[2 [6 7]]` (new) and `1` (old) keeps the product and spells the map
out. -/
#guard
  let T := Sock.mk (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (C (A 5) (C (A 6) (A 7)))
  doubleInt ⟨T, C (A 2) (C (A 6) (A 7))⟩ ⟨T, A 1⟩ == ⟨T, C (A 2) (C (A 6) (A 7))⟩
