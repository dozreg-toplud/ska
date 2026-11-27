The switch to the pill of dab8478
=================================

One Hoon commit: dab8478 (the pass loop of `+analyze` culls only when it is
stable: no `+cull` after each pass, and the loop ends only when no entry
changed, no function was found and every member that `.id` reaches is
clean).  The pill changes from sha256 75012450..., 793,354 bytes (Hoon at
f7e95af) to sha256 03d6233e..., 793,550 bytes.  It is made as before
(`U3NC_STEEL_GEN`, `U3NC_STEEL_SYS`, `U3NC_STEEL_LIB` with the harness of
`nocw/o-steel3`); the comments of the commit do not change it (the same
sha256 with and without them).

Arms whose Nock changed:

1. The `$` of `+analyze`'s pass loop (`ska_analyze.loop1`): new code, 369
   leaves before, 463 after.
2. Five arms whose source is the same, but whose `?=` over a set of hint tags
   tests the tags in another order (the same leaves, as a multiset, and the
   same size): `+know` (arm `13814` of the battery of `ana`), the arm `14302`
   of the battery of `ana` (no `%fast` label; the test of `hint-safe`), the
   arm `+hinted` (battery axis `63348` of `K`, arm `96116` of `K`: `hdBat` of
   `Compiler/CompPastLink.lean`), and the arms `comp-run-shape` (`27630`)
   and `comp-run` (`2047`) of the door of `+comp`.  The order of such a test
   follows the order of the forks of the tag type, a set ordered by the mugs
   of type nouns, and these hold the type of the library core, whose arms
   (as Hoon) include `+analyze`.
   The hand-written nouns that changed with them: `hdBat` of
   `Compiler/CompPastLink.lean` and `cr11TD` of `Compiler/CompRunHintS.lean`
   (the `?=(hint-dynamic ..)` of `comp-run`'s case `%11`, written by
   `tools/gen/runhint.py`); both regenerated from the pill, proofs unchanged.

Every other changed noun is a battery, a quoted core or a type noun that
holds one of them: `ska_analyze.battery` and `.arm`, `ska_cg.k_bat`,
`.battery` and `.arm`, the battery of `ana`, the battery of `K` (with the
arm `+comp` at `3542`, which quotes the door), `comp.door`, the battery of
the optimizer's core (its arm `get-idom` at `28` quotes the cores above),
`ana`, `cor`, `interp`, `core`, `trap`, `root`, and the Hoon of `+analyze`
in the core types that `cor` and `trap` hold.  Checked by hash-consing the
nouns of `lemmas/Pill` before and after: of the 1,090 new subterms, 15 are
minimal (new, with both children old); 7 lie in the loop, 6 are the reordered
tests (an old test chain paired with other old branches), and 2 are pieces
of the Hoon of the loop in the types (`(cull id st)` moved, and the gate
`|=(m=identity ..)`).

Hash names that changed, among those the hand-written files use
---------------------------------------------------------------

One pair per line, old name then new name: the battery of the optimizer's
core (`optC`, slot 62 of `cor`) and the battery of `K` (`compK`, slot 126).

nhd6b9320ed1b6 nh0494996e5568
nhe0b859c3d8aa nh5592f9d7750f
