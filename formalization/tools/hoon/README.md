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
* `copymeet.sh [seconds]` the `cnMeet` test of `lemmas/Compiler/CompCopyLink.lean`: runs the control `copyprobe.hoon` (a `~?` that prints, 2 lines: the harness evaluates twice) and `thread-a/b/c.hoon` and `proxy-dump.hoon` (162 + 2 formulas through `+comp`) and counts the lines of the `~?` prints of `+copy-need-make-ops` (`%copy-this-l-a`, `%copy-this-l-b`, `%copy-this-r`, `%copy-both`, printed when a `%mov` of the walk would join a register to itself): 0 in all four (2026-11-24)
* `proxy-dump.hoon` the raw blocks of two proxy cases for a subject sock that knows nothing (`lemmas/Ska/ExecPath.lean`)
* `calldump.hoon`  the raw blocks of calls (`lemmas/Ska/CompCall.lean`): an indirect call, and a direct call of the recursive `R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]` as a tail call, under `%next`, in the head of a cons, in a branch of a `%6`, as a test, with its product unused, two calls in sequence (`%dseq`), two calls in a cons (`%dtwo`); the top function's nomm, its whole-subject blocks and the n-ary blocks and nomm of every function compiled (2026-11-24; the n-ary blocks of whole functions are the `#guard` checks of `lemmas/Ska/CompRunLCEq.lean`)
* `selfkeep.py OUTDIR` writes an instrumented copy of the library and a driver for the register facts of `lemmas/Ska/CompUnproxyRegs.lean`: over the 74 formulas of `thread-a.hoon` and the two of `proxy-dump.hoon`, 2930 runs of `run` in `%run` mode (352 make a proxy), no failure (2026-11-24); with check i5 (every register a new or changed block of a run mentions is below the run's end) the output has 5860 lines (each case's sequence twice), 704 with a proxy, no failure (2026-11-24)
* `tagkeep.py OUTDIR [a|b|c|x|all]` writes an instrumented copy of the library and a driver for the tag invariant of
                    `lemmas/Ska/CompTagX.lean` and `lemmas/Ska/CompTagU.lean`: at the end of every run of `run` in `%run` mode, with region `rb` and goal `gol`,
                    with G(t) = "`rb` is a suffix of `t`, or `t` is the tag (at the start) of a lazy block of `gol`", every key
                    the run added to `cond` has a tag satisfying G, every entry of `tags` it set satisfies G, every lazy block of
                    the returned `next` has a tag satisfying G, and every old key of `cond` keeps its tag.  Run it as
                    `RUNHOON_LIB=OUTDIR/lib.hoon runhoon.sh OUTDIR/ck.hoon 1500 > out.txt`, then `tagkeep.py --sum out.txt`.
                    Over the 162 formulas of `thread-a/b/c`, the two of `proxy-dump.hoon` and 17 nestings of
                    `[7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]]` (inside two `%6`, inside a cons inside a `%6`, in a test, in both
                    branches, under a goal with forks, under `%10` and `%5`): 181 cases, 9584 runs, 1582 with a proxy,
                    13844 keys added, no failure (2026-11-24).  The stronger form without the goal's tags ("every key added
                    has a tag with `rb` as a suffix") fails in 758 runs, all under goals whose lazy blocks have tags from
                    outside the run's region (the forking branch of `%6`, for example the case `%c` of
                    `proxy-dump.hoon`, `[7 [6 [0 2] [1 0] [6 [0 6] [0 7] [0 1]]] [6 [0 2] [0 3] [0 1]]]`); in every run whose goal's lazy blocks
                    all have tags with `rb` as a suffix (a fork-free goal among them) every key added has one
* `sitesmeet2.hoon` `SitesMeet` on every site after fifteen pokes
* `sitesmeet3.hoon` the three invariants of `lemmas/Ska/SitesMeet.lean` on the same sites
* `sitesmeet4.hoon` `LessProvidesNF` and `KnowMeetsNF` of `lemmas/Ska/SitesMeetNF.lean` (a copy of `+know` with `fold` as a sample)
* `sitesmeet5.hoon` the residue `ProdMeet` of `lemmas/Ska/KnowMeets.lean` on the pruned graphs, and `DatInhab`, `LessInhab`, `NoAx0Dat`
* `prodsame.hoon`   the checks of `sitesmeet5.hoon` on seven pokes that each make two identities of one code bell (an `.indi` miss: a gate whose sample is an indirect call's formula, called with an unknown sample, then with a known atom)
* `prodsame4.hoon`  the checks of `sitesmeet4.hoon` on the same pokes
* `bakeok.hoon`     every variant's bake is under its code requirement (with the guard: 10 pokes, 375 variants, `bad=0`, 2026-11-24)
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
                    and at `less.c`), and `H`'s variant has a bake not under its code requirement (2026-11-24).  On the compiler with the guard
                    of commit 8f2162e SitesMeet still fails at that site, but `[%bakeok 1 variants=7 bad=0]` (2026-11-24)
* `swaploop.hoon`   the pass loop of `+analyze` did not end before 1813f09 (`lemmas/Ska/PassLoop.lean`): one member
                    whose `less-code` alternated between `[& [& |]]` and `[& [| &]]`; `+poke` gave no answer in 300 s,
                    the same poke with the sample not swapped answers at once (2026-11-24).  On the compiler of 1813f09,
                    where `+run` unites `less-code` with the old cape, it prints `[%poke-returned %.y]` (2026-11-24)
* `collide.hoon`    a miscompile (`lemmas/Ska/VariantCollision.lean`): the poke of `bakedrop.hoon`'s first
                    formula, then `[7 [[1 [[3 0] 5]] (dec 40)] [2 [0 1] [1 H]]]`, whose `H` gets a second code
                    bell with the same bake, so the live call runs the dead variant's code: `+eval-top` gives
                    `[%0 7]`, `+mock` `[%2 ~]` (2026-11-24).  `collide0.hoon`: the second formula alone agrees.
                    `collide-vars.hoon`: after each poke, `H`'s code bells, their variants' bakes and nomms
                    (two code bells list the one variant, whose nomm is `[7 [0 1] [1 7]]`).  Fixed by commit 8f2162e: on the
                    changed compiler `collide.hoon` prints `[%after-witness %same]` twice (2026-11-24)
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
                    and at every call of `+trim-trace-hints`, on the 143 cases: no failure (`br=0`, 202 rounds, 2026-11-24).  Without the
                    distinct-key clause (the counted pass of commit 753abe9): `[%summary n=143 bad=0 cyc=0 dup=0 rubch=7
                    hopch=143 pas=0 pas2=0 br=0]` (2026-11-24).
* `trimcheck.hoon`  51 formulas where `+trim-trace-hints` drops hints (constants, conses, known-cell slots, nested
                    hints, hints in branches and across joins, `%lose`/`%hunk`/`%hand`, constant and deferred `%mean`),
                    subject unknown and known (7 subjects): at every call the pass against the model of
                    `lemmas/Ska/OptTrim.lean` written again with lists, `TrimBr` on the raw code and at the input
                    of the pass, and 714 runs of the optimized code (`+eval-blob` subject unknown, `+eval-top`
                    subject known, both through `+eval-mook`) against `+mook` of `+mink`: 408 compiles, 168 with
                    drops, 416 ops dropped, model equal to the pass everywhere; 4 runs differ, all `%same-clue-subj`,
                    whose trim input breaks `TrimBr` (2026-11-24).  After commit 753abe9 (counts per key), with the
                    model counted (maps, a hand-folded `max`) and `TrimBr` without its distinct-key clause:
                    `[%summary cases=408 drop-cases=160 ops=384 mis=0 runs=714 bad=0 same=0]`, and no `TrimBr`
                    failure on raw code or at any call of the pass (2026-11-24)
* `trimbug.hoon`    the witness: `[11 [%spot 0 1] [11 [%spot 0 1] 1 5] 0 0]` on `0`, `+mock` `[%2 ~[leaf+"mook.spot"]]`,
                    `+eval-top` `[%2 ~]`; the same with `%mean` twice, with an axis of a known cell, with an
                    increment; agreement when the hints differ in tag or the clue is a constant (2026-11-24).  Fixed by
                    commit 753abe9: `%same`, both `[%2 ~[leaf+"mook.spot"]]` (2026-11-24)
* `switchcheck.hoon` 26 formulas made to have chains of tests of one register (tagged tests `?=([%c *] x)` and
                    plain ones `=(c x)`, both operand orders, four to nine tests, duplicated constants, a constant of
                    `2^31`, hits that read the head, chains mixed with other tests, a chain in a hit of another), compiled
                    with the subject unknown and known on each subject (208 compiles): `+switch-chains` fired on 153 and
                    made 572 `%lti`, its output equals the model of `lemmas/Ska/OptSwitch.lean` written again in Hoon on
                    every compile, and 364 runs (`+eval-blob` and `+eval-top` through `+eval-mook`) agree with `+mock`
                    (2026-11-24).  It does not fire with three tests, a constant of `2^31` cutting the chain, a hit
                    that reads the head register (`uses` is then 3), or another test in the chain
* `switchcheck2.hoon` the same model against `+switch-chains` on the 143 cases of `optcheck.hoon`, after the rounds
                    of `+optimize`: the pass fires on none of them and the model agrees on all (2026-11-24)
* `aliascheck.hoon` 28 formulas made to have `+alias` act (moves, a test of a register against itself, a cell test
                    twice, a loobean test inside a branch of the same test, a pushed loobean, joins, heads twice, trace
                    hints around folded branches), 101 compiles, 164 calls of `+alias`, 116 of which changed
                    something: 315 `%mov` eliminated, 77 other ops dropped, 44 two-way ends folded to a `%hop`, 19
                    `%brn` made `%brz`, 44 blocks dropped, no `%brn` made `[%bom ~]`; 146 runs agree with `+mock`,
                    traces included (2026-11-24).  The library's list types do not fuse with a test's own in a `?=`
                    (`fuse-loop`): the check and the model of `switchcheck.hoon` clam the blocks to nouns first.
                    Extended (2026-11-24) with 13 formulas: facts reaching a join block from two predecessors that
                    agree (a cell test, a loobean, a head, an immediate, before the split), that disagree (`&` on
                    one side, `|` on the other: joined to `is-loob`, so the next `%brn` becomes `%brz`), from one
                    side only (dropped, no fold), parameters joined, and three aimed at `[%bom ~]`.  The counter
                    `jfold` counts the ends folded (to `%hop`, `%brz` or `[%bom ~]`) in a block with two distinct
                    predecessors or more whose test register no op of the block defines, so a fact from the
                    block's start.  Totals: 160 compiles, 270 calls, 202 changed, 761 moves, 303 other ops, 69
                    folds, 28 `%brz`, 3 `[%bom ~]`, 75 blocks dropped, `jfold=52` (the new `j-agree-cell`,
                    `-cell3`, `-loob`, `j-two-cell`, `j-disagree-loob`, `j-par-loob` among them; `j-one-cell` and
                    `j-par-agree` do not fold), 238 runs, `bad=0`.  `[%bom ~]` fires on `bom-c`,
                    `[8 [6 [3 0 1] [1 7] [0 0]] [6 [0 2] [1 4] [1 5]]]`: the no side crashes, so the join block
                    has one predecessor and its parameter gets `has-imm 7` from `param-info` where the analysis
                    did not fold the `%6`; `+mock` agrees on subjects `0` and `[1 2]`
* `aliascheck2.hoon` the model of `+alias` (`lemmas/Ska/OptAliasModel.lean`, `aliasM`) written again on nouns, against
                    the pass at every call over the 143 cases of `optcheck.hoon` (with the 74 of `thread-a.hoon`)
                    and the 41 formulas of `aliascheck.hoon` (subject unknown, and known for each subject): 303
                    compiles, 472 calls, 336 of which changed something, `mis=0` (2026-11-24).  A mutation of the
                    model (a `%cel` on a known cell kept) is caught
* `aliasssa.hoon`   two blocks with `DInvT` that read register `0v1` by a `%mov` and then write it: `+alias` renames
                    the later read of the moved register to `0v1`, and `+eval-blob` gives `7` before, `5` after;
                    `+alias` needs single assignment (`AliasSSA` of `lemmas/Ska/OptAliasField.lean`)
* `ssacheck.hoon`   `AliasSSA` of `lemmas/Ska/OptAliasField.lean` on the real compiler: on raw `+comp` output and
                    after every pass of every round of `+optimize` replayed as `+optimize-once` does (so at every
                    call of `+alias`), over the cases of `aliascheck2.hoon` (the 143 of `optcheck.hoon`, the 41
                    formulas of `aliascheck.hoon`), `thread-a.hoon` with the subject known and `thread-b.hoon`,
                    `thread-c.hoon` with it unknown and known: 553 compiles, 955 calls of `+alias`.  `DefFirst`
                    (a forward must-analysis over `bb-topo`, the start of a block the intersection of its
                    predecessors' ends and its parameters, every read of a register that has a definition
                    checked: 56085 reads on raw code, 72162 at the calls) holds everywhere.  `DefOnce` fails on 32
                    raw compiles and at 26 calls (24 after `+alias`, none after `+remove-dead-code`), always on
                    the fill of `+crash-need`: `[%cel a] [%imm 0 x] .. [%bom ~]`, where `x` is `a` itself (a
                    parameter of the block before, or an `%inc` destination) and is defined twice.  Smallest:
                    `[10 [6 0 1] 5 [0 6] 0 1]` and `[7 [5 [0 14] 1 5] 10 [2 0 3] 0 1]` (subject unknown), where
                    `+eval-blob` agrees with `+mock` on every subject tried (both crash).  The weaker `DefOnceB`
                    holds everywhere (raw, every pass, every call): on the blocks reachable from `0`, a register
                    has at most one definition that is not a dead fill, a dead fill of `x` being an `%imm` into
                    `x` in a block ending in `%bom`, followed there by `%imm` ops only, with every read of `x` in
                    that block before it.  Without reachability it fails (unreachable raw blocks read the
                    register), and without "followed by `%imm` ops only" it fails after `+remove-hops` merges the
                    `%inc` into the fill's block.  With the arguments `0 .. n-args - 1` defined at the entry and
                    every read checked, 10 raw compiles read a register that nothing defines, in blocks reachable
                    in the graph (in thread-a case 48 a jump argument on the nonzero side of a `%brz`: a run
                    taking that edge would crash in `+move`, which the runs of `thread-a.hoon` do not show, but
                    it is not shown for every subject); none after any `+alias` (2026-11-24)
* `deadcrash.hoon`  nine formulas whose crashing operand has a dead product (`[7 [0 2] [1 5]]`
                    on an atom and the like): `+eval-top` agrees with `+mock` on all
                    (2026-11-24), so `+remove-dead-code` drops no check there
