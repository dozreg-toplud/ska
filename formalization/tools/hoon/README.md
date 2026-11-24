Tests that run Hoon on the real compiler, without a ship.

`runhoon.sh TEST.hoon [seconds]` builds hoon.hoon and nock-compilation.hoon of this worktree
from text and evaluates the expression in TEST.hoon against the library's core, with the jet
of `+mink` off (the reference).  `RUNHOON_LIB=path` takes another nock-compilation.hoon.  It
needs the harness `~/work/ska-scratch/nocw/nct` and `samx5.hoon` beside it.

* `fix.hoon`        22 formulas, `+eval-top` against `+mock`
* `stale.hoon`      the stale entry of `+analyze` (fixed in fefb95d)
* `sect.hoon`       the threading cases of `+sect` through `+eval-top`
* `sect2.hoon`      the same on the code before `+optimize`
* `thread-a/b/c`    162 threading cases: before `+optimize`, after it, and with passes left out
* `sitesmeet2.hoon` `SitesMeet` on every site after fifteen pokes
* `sitesmeet3.hoon` the three invariants of `lemmas/Ska/SitesMeet.lean` on the same sites
* `sitesmeet4.hoon` `LessProvidesNF` and `KnowMeetsNF` of `lemmas/Ska/SitesMeetNF.lean` (a copy of `+know` with `fold` as a sample)
* `sitesmeet5.hoon` the residue `ProdMeet` of `lemmas/Ska/KnowMeets.lean` on the pruned graphs, and `DatInhab`, `LessInhab`, `NoAx0Dat`
* `prodsame.hoon`   the checks of `sitesmeet5.hoon` on seven pokes that each make two identities of one code bell (an `.indi` miss: a gate whose sample is an indirect call's formula, called with an unknown sample, then with a known atom)
* `prodsame4.hoon`  the checks of `sitesmeet4.hoon` on the same pokes
* `bakeok.hoon`     every variant's bake is under its code requirement
* `he.hoon`, `he4.hoon`   the checks of `prodsame.hoon` and `prodsame4.hoon` on four pokes that recurse more than `he-threshold` deep with growing subjects (a gate built on the previous one, a formula built on the previous one)
* `he2.hoon`, `he24.hoon` the same on three pokes whose recursion grows a part of the subject used as a formula (an `.indi` chain): the `%he` generalization stops the chain at 32 or 33 identities of one code bell (with `he-threshold` raised the first poke did not end in 90 s), and `ProdMeet`, `ProdSame` under `less.c`, `LessProvidesNF`, `KnowMeetsNF` and `SitesMeet` held
* `prodsites.hoon`  `ProdSame` at the site socks that occur, on the pokes of `prodsame.hoon` and `he2.hoon`: for every entry of the pruned graph, the sites of `+know` without folding under its code requirement and its callees' subject socks; every identity of the callee's code bell, patched for the site sock, against `dat`'s (`+huge:so` both ways)
* `prodmaps.hoon`   the maps at the site socks of `prodsites.hoon`: every two identities of one code bell, patched for the site sock, have equal maps (and so equal on the parts the product knows); at each callee identity, the product the analysis used (not patched) against itself and `dat`'s patched for its subject sock (nouns and maps)
* `voidcall.hoon`   five formulas with a call that never returns in one branch of a `%6`
                    whose product is the subject of a later call: the checks of
                    `prodsame4.hoon` find no failure (2026-11-24)
