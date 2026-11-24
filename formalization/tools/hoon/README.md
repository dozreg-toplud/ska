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
* `proxy-dump.hoon` the raw blocks of two proxy cases for a subject sock that knows nothing (`lemmas/Ska/ExecPath.lean`)
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
                    `prodsame4.hoon` find no failure (2026-11-24).  None of the five
                    makes a `%void`: `+pull:so` of a known atom is `|+~`, `[0 0]` is
                    `|+~`, the branch's call is inlined, the `%6` gives `|+~`, and the
                    later call's callee then requires `|+~`
* `voidscc.hoon`    the witness against `LessProvidesNF`: a never-returning member of the
                    root's SCC, whose pre-pop `%void` product the root's last run used, while
                    `dat` has the `|+~` of `+pop`.  One site of `+know` without folding fails
                    (for the pair at `less.c` and for the strict one); `KnowMeetsNF` and
                    `SitesMeet` hold (2026-11-24)
* `bakedrop.hoon`   the witness against `SitesMeet` and `BakesImply` (`lemmas/Ska/SitesMeetFalse.lean`): the
                    test of `voidscc.hoon` made to fold to the branch with the never-returning call, which
                    the analysis saw as `%void`.  Under the bake (default `fold`) `H`'s site knows axis `4`
                    is `[3 0]`, its code requirement says `[1 7]`: SitesMeet fails at 1 site per pair (strict
                    and at `less.c`), and `H`'s variant has a bake not under its code requirement (2026-11-24)
* `collide.hoon`    a miscompile (`lemmas/Ska/VariantCollision.lean`): the poke of `bakedrop.hoon`'s first
                    formula, then `[7 [[1 [[3 0] 5]] (dec 40)] [2 [0 1] [1 H]]]`, whose `H` gets a second code
                    bell with the same bake, so the live call runs the dead variant's code: `+eval-top` gives
                    `[%0 7]`, `+mock` `[%2 ~]` (2026-11-24).  `collide0.hoon`: the second formula alone agrees.
                    `collide-vars.hoon`: after each poke, `H`'s code bells, their variants' bakes and nomms
                    (two code bells list the one variant, whose nomm is `[7 [0 1] [1 7]]`)
