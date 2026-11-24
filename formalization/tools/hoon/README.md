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
* `selfkeep.py OUTDIR` writes an instrumented copy of the library and a driver for the register facts of `lemmas/Ska/CompUnproxyRegs.lean`: over the 74 formulas of `thread-a.hoon` and the two of `proxy-dump.hoon`, 2930 runs of `run` in `%run` mode (352 make a proxy), no failure (2026-11-24); with check i5 (every register a new or changed block of a run mentions is below the run's end) the output has 5860 lines (each case's sequence twice), 704 with a proxy, no failure (2026-11-24)
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
* `swaploop.hoon`   the pass loop of `+analyze` does not end (`lemmas/Ska/PassLoop.lean`): one member whose
                    `less-code` alternates between `[& [& |]]` and `[& [| &]]`; `+poke` gave no answer in 300 s, the same
                    poke with the sample not swapped answers at once (2026-11-24)
* `collide.hoon`    a miscompile (`lemmas/Ska/VariantCollision.lean`): the poke of `bakedrop.hoon`'s first
                    formula, then `[7 [[1 [[3 0] 5]] (dec 40)] [2 [0 1] [1 H]]]`, whose `H` gets a second code
                    bell with the same bake, so the live call runs the dead variant's code: `+eval-top` gives
                    `[%0 7]`, `+mock` `[%2 ~]` (2026-11-24).  `collide0.hoon`: the second formula alone agrees.
                    `collide-vars.hoon`: after each poke, `H`'s code bells, their variants' bakes and nomms
                    (two code bells list the one variant, whose nomm is `[7 [0 1] [1 7]]`)
* `closed.hoon`     `GraphClosed` of `lemmas/Ska/AnaEnds.lean` on the graph `+ska-callgraph` returns, over the 26 pokes of
                    `sitesmeet4.hoon`, `he2.hoon`, `voidscc.hoon`, `prodsame.hoon` with the memo threaded: 1760 entries,
                    4052 callee edges, no callee missing, every root an entry (2026-11-24)
* `closedsteps.py OUTDIR` writes an instrumented copy of the library whose `+cull` and `+pop` check the two clauses of
                    `CInv.clo` (`lemmas/Ska/GraphClose.lean`) at every state they see, and `closed.hoon` as the driver:
                    at 3680 culls no callee edge from outside the component points into it (2,195,392 edges) and no
                    callee is missing; at 4472 pops no callee edge of a finalized entry points into `order` (2,354,100
                    edges) and no callee is missing (2026-11-24)
* `optcheck.hoon`   over the 74 formulas of `thread-a.hoon`, the raw blocks against what the models of
                    `lemmas/Ska/Opt*.lean` predict: `+remove-useless-branching` as `rubFin`, `+remove-hops` keeps
                    block `0`, the parameters and only labels of `topo`; on raw code `topo` is ordered and the
                    parameters are distinct; every jump passes the check of `+eval-pass` (`PassOK`) on raw code
                    and after `+remove-hops`: no failure (2026-11-24).  Also over the other formulas here
                    (`fix.hoon`'s 22, `deadcrash.hoon`'s 9, `proxy-dump.hoon`'s 2; the 28 small ones with
                    the subject unknown and known, 135 cases in all): `PassOK` and `ParNodup` after
                    `+remove-empty-middle` alone on raw code (5 cases changed) and after every pass of every
                    round of `+optimize` replayed pass by pass (194 rounds, 2229 checks, 507 hops with
                    arguments redirected by `rewrite-hop`), and on the output after `+switch-chains`, which
                    equals that of `+optimize` on all 135: no failure (2026-11-24).  `DownPar` of
                    `lemmas/Ska/OptDownPar.lean` (no argument register of a jump is a parameter of a
                    block reachable from its target) on the raw code, after every pass of every round
                    and on the output, on the same 135 cases: no failure, printed as `%downpar-raw`,
                    `%downpar-fail`, `%downpar-out` when it fails (2026-11-24).  The shape of `trimRun` (`lemmas/Ska/OptTrim.lean`) at every call of `+trim-trace-hints`:
                    the same labels, parameters and ends, each body the one before with only trace hint ops
                    dropped (`%trim-shape-fail`), over 143 cases (the 135 and 8 with `%spot`/`%mean` hints
                    around formulas that cannot crash, subject known and unknown): no failure
                    (2026-11-24), but the pass dropped no op on any of them (`%trim-drop` never printed), so
                    which hints it drops is not yet tested.  `TrimBr` of `lemmas/Ska/OptTrim.lean` on the raw code
                    and at every call of `+trim-trace-hints`, on the 143 cases: no failure (`br=0`, 202 rounds, 2026-11-24).
* `trimcheck.hoon`  51 formulas where `+trim-trace-hints` drops hints (constants, conses, known-cell slots, nested
                    hints, hints in branches and across joins, `%lose`/`%hunk`/`%hand`, constant and deferred `%mean`),
                    subject unknown and known (7 subjects): at every call the pass against the model of
                    `lemmas/Ska/OptTrim.lean` written again with lists, `TrimBr` on the raw code and at the input
                    of the pass, and 714 runs of the optimized code (`+eval-blob` subject unknown, `+eval-top`
                    subject known, both through `+eval-mook`) against `+mook` of `+mink`: 408 compiles, 168 with
                    drops, 416 ops dropped, model equal to the pass everywhere; 4 runs differ, all `%same-clue-subj`,
                    whose trim input breaks `TrimBr` (2026-11-24)
* `trimbug.hoon`    the witness: `[11 [%spot 0 1] [11 [%spot 0 1] 1 5] 0 0]` on `0`, `+mock` `[%2 ~[leaf+"mook.spot"]]`,
                    `+eval-top` `[%2 ~]`; the same with `%mean` twice, with an axis of a known cell, with an
                    increment; agreement when the hints differ in tag or the clue is a constant (2026-11-24)
* `deadcrash.hoon`  nine formulas whose crashing operand has a dead product (`[7 [0 2] [1 5]]`
                    on an atom and the like): `+eval-top` agrees with `+mock` on all
                    (2026-11-24), so `+remove-dead-code` drops no check there
