The switch to the pill of 2a5b618
=================================

One Hoon commit: 2a5b618 (the sweep loop of `+compile-scc-in` joins a
member's new shape with its entry by `+msg-need-ord-kept`, a new arm of the
core `K` after `+msg-need-ord`: what the entry takes whole stays whole; the
fork joins still call `+msg-need-ord`).  The pill changes from sha256
03d6233e..., 793,550 bytes (Hoon at dab8478) to sha256 8bc108f4...,
794,095 bytes, made as before (`U3NC_STEEL_GEN`, `U3NC_STEEL_SYS`,
`U3NC_STEEL_LIB` with the harness of `nocw/o-steel3`; built twice, the
same sha256).

Arms whose Nock changed:

1. The new arm `+msg-need-ord-kept` (387 leaves), at battery axis `113398`
   of `K` (arm `178934` of `K`).  `K` is the core of `+comp`, the core of
   lines 3244 to 8180 of the library (`compK`, slot 63 of `cor`, battery at
   126).
2. The new arm goes into the battery tree of `K` where `+this-only` was,
   and pushes four arms one level down.  Their Nock is the same, their axes
   are new (battery axis, then arm of `K`):
   - `+this-only` (182 leaves): `113398` / `178934` becomes `226798` / `357870`;
   - an arm of 279 leaves: `226798` / `357870` becomes `453598` / `715742`;
   - `+pass-bomb` (50 leaves): `453598` / `715742` becomes `907198` / `1431486`;
   - an arm of 171 leaves: `453599` / `715743` becomes `907199` / `1431487`.
3. The arm `+compile-scc-in` (battery axis `1708`, arm `2732` of `K`): the
   join of `member` calls arm `178934` (the new arm) instead of arm `20`
   (`+msg-need-ord`), one atom.
4. Seven arms of `K` whose source is the same and whose calls of the moved
   arms take the new axes (atoms only, the same size): battery axes `14`
   (arm `22`), `62` (`94`), `214` (`342`), `892` (`1404`), `894` (`1406`),
   `3542` (`5590`, `+comp`, which quotes the door) and `3550` (`5598`).
   No `?=` over a tag set changed its order this time.

Every other changed noun is a battery, a quoted core or a type noun that
holds one of them: the battery of `K` (`compK`, slot 126 of `cor`), the
battery of the optimizer's core (`optC`, slot 62 of `cor`: its arm
`get-idom` at `28` quotes the cores above), `comp.door`, `cor`, `core`,
`interp`, `trap`, `root`, and the Hoon of the two arms in the core types
that `cor` and `trap` hold.  Checked by hash-consing the nouns of
`lemmas/Pill` before and after (the named defs: only these six changed, no
named def came or went): of the 997 new subterms, 24 are minimal (new, with
both children old): the call atoms of 3. and 4., the new arm, and pieces of
the Hoon of the two arms in the types.  The arm files of `lemmas/Pill/Arm`:
only `Comp.lean` changed.

Hash names that changed, among those the hand-written files use
---------------------------------------------------------------

One pair per line, old name then new name: the battery of `K` (`compK`,
slot 126 of `cor`) and the battery of the optimizer's core (`optC`, slot 62).

nh5592f9d7750f nh290d8f32435a
nh0494996e5568 nhdc32b3a7a533

The hand-written files that the switch changed
----------------------------------------------

The axes of the moved arms (`tools/gen` tables and the kernel facts; the
nouns are the same, so the proofs are unchanged).  Hex atoms are written
`0x...` when over 9999, and the new axis of `+this-only` is the old one of
`+laze` (`0x575ee`), so these were replaced arm by arm, not by a blind
substitution:

- `+this-only` `178934` -> `357870`: `Compiler/CompSixKerf.lean` (`tho_at`),
  `tools/gen/sixhelp.py`;
- `+pass-bomb` `715742` -> `1431486`: `Compiler/CompLeapN.lean` (`pbo_at`,
  rewritten by `tools/gen/leap.py`, which also gives the new `pbtArm`:
  `+pass-both` calls `+pass-bomb`), `Compiler/CompLeapPass.lean` (`PassIn`),
  `tools/gen/leap.py`;
- `+laze` `0x575ee` -> `0xaebde` (its bunt is called in the nouns):
  `Compiler/CompRunShapeBranch.lean`, `CompRunShapeBranchCut.lean`,
  `CompRunShapeColl.lean`, `CompRunShapeCollCut.lean`,
  `tools/gen/runshapecoll.py`;
- `+inter2-fix-round` `0xaebdf` -> `0x15d7bf`: `Compiler/CompShapeCol.lean`
  (`fr_at` and the noun of `+inter2-collapse`), `CompShapeColFix.lean`,
  `tools/gen/shapecol.py`, `tools/gen/shapecolcells.py`.

Regenerated nouns: `cr6*` of `Compiler/CompRunSixN.lean` (`tools/gen/runsix.py`:
the case `%6` of `+run` calls `+this-only`), `memOld` of
`Compiler/CompMember.lean` (`tools/gen/member.py`: the join of `member` calls
the new arm).
