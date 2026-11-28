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
* `flagsdump.hoon` the flags `[pure total]` of every `code` entry after each of 10 `%full` pokes in a row (track P, README Gaps 23, P1): `[| |]`, `[| &]`, `[& &]` occur, old entries keep their flags, no SCC of more than one bell in these runs (2026-11-27)
* `jetsdump.hoon` the jets noun and `jets-hot` before and after each of 8 `%full` pokes (two of a `~%` root core): the five jugs, `call`, `back` and `jets-hot` are treaps, the jets noun has seven parts, `jets-hot` stays `~`; output `jetsdump.txt` (track P, README Gaps 23, `PGood`, 2026-11-27)
* `sprestdump.hoon` the baking half of `+ska-poke` against the model over 21 `%full` pokes in a row (fresh state, `~%` roots, repeats, two 2-bell SCCs): root bell, memo, `vars`, the keys and entries of `code`/`calls`/`seek` (`newCode`, `addCode`), closure of the table, the flags equal to the replay of the SCC loop over the whole table, the jets equal to `+ska-cole-update` of the edited jets; output `sprestdump.txt`, no difference (track P, README Gaps 23, 2026-11-27)
* `invdump.hoon` the clauses of `PGood2` (`lemmas/Compiler/PokeLinkGood2.lean`) after each of the 21 `%full` pokes of `sprestdump.hoon`: `calls` and `%2` info bells are keys of `code`, `sure`/`inl` are treaps, keys of `sure` = keys of `nary`, `inl` keys in `code` and each `inl` entry `+inlined` of its bell with `inl` emptied, `sccs` `SccsGood`, `nary` closed under SCCs; output `invdump.txt`, all hold (track P, README Gaps 23, 2026-11-27)
* `inldump.hoon` `+inlined` against the model `inlinedM` (track G, `lemmas/Glue/Inline.lean`, LEDGER 2.e): 20 pokes in a row (16 through the `%full` branch by hand with an unknown subject `[| ~]`, 4 real `%full`), then one jam of the entries of `inl.cache` and, per bell of `code`, `[bell nomm single self]`; `inlcheck.py --sum OUT` (calls inlined per entry) or `--lean OUT` (writes `lemmas/Glue/InlineData.lean`, the `#guard`s of `lemmas/Glue/InlineCheck.lean`): the 29 entries equal `inlinedM`, 11 with calls inlined, `jets-hot` `~` (2026-11-27)
* `invdump2.hoon` the clauses of `PGood2` and `%vars`, `%ckey`, `%mono`, `%scck`, `%gone`, `%flag` after each of 32 pokes mixing `%full`, `%jets` (real drops), `%fast` (with and without `reset`) and `%dire`; output `invdump2.txt`, all hold (track P, README Gaps 23, 2026-11-27); ninth session: `%sset` (every `sccs.cache` entry is its bell's SCC over `calls`) and `%ccoh` (`call.cole` and `back.cole` agree), all hold
* `jetsmodel.hoon` `invdump2.hoon` with `%jmod` and `%nnew` after every `%full`: the jets after the poke equal the model `jetsOfP` of `lemmas/Compiler/PokeLinkJetsP.lean` (computed from the old state, the regs of `+ska-callgraph` rerun, the new `code` and `seek`), and the poke's list is `(flop new.regs)`; both hold at all 16 `%full` pokes, `call.cole` grows at four (track P, README Gaps 23, twelfth session, 2026-11-28); with `%bset`, `%pset` (`back.cole` and `pend.jets` jugs of sets), `%jpth` (the keys of `core.jets` are paths) and, at each `%full`, `%rmap` (the regs of `+ska-callgraph` have four maps and paths as `core` keys): all hold at the 32 pokes (thirteenth session)
* `hotempty.hoon` (track P, README Gaps 23, fifteenth session, 2026-11-28) the clauses of `jetsmodel.hoon` and `%hot0` (`jets-hot` is `~`), `%same` (`[%jets ~]` at `pend = ~` returns `[%drop ~]`, state unchanged), `%drop0` (every `[%jets ~]` drops nothing), `%long` (no poke but `%full` changes `memo`, `code`, `calls`, `vars`, `seek`) after each of 42 pokes that `Reach` admits (every `%jets` is `[%jets ~]`): all hold
* `hotatom.hoon` `+validate-ovum` on `[%jets ~]` returns it and on `[%jets 5]` crashes (exit 1 after the first print)
* `ten0dump.hoon` four `%full` pokes with a `%10` at axis `0` (at the top, in either branch of a `%6`) and one at axis `1`, then the nomm and flags of every `code` entry: axis `0` is analysed to `[%0 0]` with `[| |]` (track P, README Gaps 23, ninth session, 2026-11-27)
* `flagsck.hoon` after each of the 53 pokes of `invdump2.hoon` and `sprestdump.hoon`: the SCCs of the whole table callees first in `~(rep in scc)` order, each new entry's bell and nomm, every key's flags; `tools/gen/flagscheck.py OUT > lemmas/Ska/PokeFlagsCheck.lean` (53 `#guard`s on `sccLoop`, all pass), `--trim OUT > flagsck.txt` (track P, README Gaps 23, 2026-11-27)
* `optempty.hoon` `+optimize` on a straight with no blocks crashes (`+bb-topo` reads block `0` with `+got:by`), on one `%don` block it returns: `OptLink` for every straight is false (track P, README Gaps 23, 2026-11-27)
* `proxy-dump.hoon` the raw blocks of two proxy cases for a subject sock that knows nothing (`lemmas/Ska/ExecPath.lean`)
* `calldump.hoon`  the raw blocks of calls (`lemmas/Ska/CompCall.lean`): an indirect call, and a direct call of the recursive `R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]` as a tail call, under `%next`, in the head of a cons, in a branch of a `%6`, as a test, with its product unused, two calls in sequence (`%dseq`), two calls in a cons (`%dtwo`); the top function's nomm, its whole-subject blocks and the n-ary blocks and nomm of every function compiled (2026-11-24; the n-ary blocks of whole functions are the `#guard` checks of `lemmas/Ska/CompRunLCEq.lean`)
* `calldump2.hoon` the raw blocks of the whole-subject version of 16 formulas with indirect calls in several parts (calls in both halves of a cons, a call under `%7` on either side, a call in a part of a call, a call under `%4`, a cons whose tail is a cons whose head calls), with the nomm after the analysis; eleven of them are the `#guard`s of `lemmas/Ska/CompRunOKLC.lean`, all equal to `finishLUC` (2026-11-24)
* `calldump3.hoon` the raw blocks of the whole-subject version of 13 formulas whose nomm is `[7 p q]` with indirect calls in its parts, in the forms the analysis gives `%7` (`[7 b c]`, `[8 b c]` with the call in the pushed pair or in the body, `[9 a c]` with the arm's call and a calling core formula, a nested `%7`, a `%7` as the tail of a cons, `%7` whose `q`'s need has a bond, the gate call `[8 [9 2 [0 2]] [9 2 [10 [6 [0 7]] [0 2]]]]`, an `[8 b c]` outside the fragment (`%lim`), an inlined `%2`, which the analysis turns into a direct call), with the nomm after the analysis; nine are the `#guard`s of `lemmas/Ska/CompFragF.lean` and two (`%s7a`, `%s7b`) those of `lemmas/Ska/CompRunOKLC.lean`, all equal to `finishLUC` (2026-11-24)
* `calldump4.hoon` the raw blocks of the whole-subject version of 13 formulas for the induction over `NC` (`lemmas/Ska/CompNC.lean`, README Gaps 12.22): a cons under a goal with entries (`%lim`, no op at the bond block; `%bc1`, `+split`'s `con` there; `%bc2`, `+copy`'s `mov` there), `[4 p]` under a goal with a bond whose sure part is a register `d` (`%s4t`: the bond block reads `d`), `%10` at a bond (`%s10`), `[4 p]` and `[3 p]` with a call (`%i4`, `%i3`), heads under the bond goal (`%h4c`, `%h1`, `%h3`, `%h3c`, `%h5`) and `[[0 1] [8 [0 3] [2 [0 2] [0 6]]]]` (`%c8t`) (2026-11-24)
* `directdump.hoon` the raw blocks of the whole-subject version of three direct calls of the recursive `R` (`lemmas/Ska/CompDirect.lean`, README Gaps 18): a tail call, a call under `%4`, a call in the head of a cons; `+mono-try-call` (`%clq`, `%hed`, `%tal`, the optimistic `%jmp`/`%cal`, the pessimistic `%jsp`/`%csl`), which the model does not have
* `directdump2.hoon` the cases of `directdump.hoon` and four more (a call in the tail of a cons, the test of a `%6`, and a callee `R2` whose need `[~ [this this]]` splits two levels deep, as a tail call and under `%4`), with the top's need and argument count and each callee's bell and need: the seven `#guard`s of `lemmas/Ska/CompDirectMCheck.lean` (`finishLUCM`) are equal to its blocks (2026-11-27)
* `sccloop.py OUTDIR` writes an instrumented copy of the library (prints in `+compile-scc-in` and `member`: the SCC, `order`, `top`, each compile's views of the kids, `need-new`, `sur`, `was`, `moved`, cape, previous entry and `need-pessimized`, each sweep's `any`, the final entries) and a driver of 18 recursive formulas.  Run `RUNHOON_LIB=OUTDIR/lib.hoon runhoon.sh OUTDIR/ck.hoon 900 > out.txt`, then `sccloop.py --lean out.txt > lemmas/Ska/SccLoopData.lean`.  On 2026-11-27: 23 SCCs went through the loop, each in three sweeps, at most two `%must` compiles per member, `need-new` of every `%done` compile equal to that member's last sweep and `need-pessimized` equal to the entry (`lemmas/Ska/SccLoopCheck.lean`)
* `sccreal.py OUTDIR [--tally-lib]` writes the instrumented library (prints in `member` on the `%done` path: `less.b`, nomm, `laz`, `ord`, `ned-final`, `need-new`, `sur`, `o`, the soft calls, the views, the outside callees, the entry; inside `finish` the soft map after `+coerce-lazy`, the blocks' mug before and after `+soft-done`, and the straight of `(finish ~)`; with `--tally-lib` also each entry of `+run-shape` with its nomm case and goal) and the driver of `sccloop.py`'s 18 cases; run `RUNHOON_LIB=OUTDIR/lib.hoon runhoon.sh OUTDIR/ck.hoon 900 > out.txt`, then `sccreal.py --lean out.txt > lemmas/Ska/SccLoopRealData.lean`, or `sccreal.py --tally out.txt [must|may]` for the table of `+run-shape` cases (README Gaps 21.14, 21.16); with `--shape-lib` also each `%must` / `%may` compile of `member` (the `laze` of `+run-shape`, `collapsed`, `shape`, `sur`, `id-gen`, `sofs`, the views with `jet` as `+run-shape` reads it, the outside callees; at the product `keep`, `was`, `sur`, `moved`, the entry, `np`, `chg`) and the code table after each case, then `sccreal.py --shape-lean out.txt > lemmas/Ska/SccLoopShapeData.lean` (109 compiles, 28 s, README Gaps 21.18)
* `softmink.hoon` the 6 soft compiles at run time (README Gaps 21.16): `+eval-top` against `+mink` (with `+mook`) of the formula `[8 [1 gat] 9 2 10 [6 0 7] 0 2]` of `%swap`, `%fld`, `%rot3` (the gates of `sccloop.py`) on 9 subjects `[0 sample]` (`%swap`, `%fld` only where they return or crash at once, `%rot3` on 5 samples that recurse through the soft call); all the same, about 8 minutes (2026-11-27)
* `medesoft.hoon` the `+mede` question of track K (README Gaps 21.19, 2026-11-28): soft tail calls that pass the constant `5` where the callee, entered with that part unknown, splits it on every path but not first thing (`w14`, `w15`, `w17`, `w18`, `w19`); run on the library of `sccreal.py OUT --shape-lib` (`RUNHOON_LIB=OUT/lib.hoon`, 15 s): the first `%done` run of each records `req` `[2 [[%this 1] %none 0]]` in its soft call (the `[%ds ..]` dump), a cell need, so `+mede` asked through `+crash-need`
* `medemink2.hoon` (README Gaps 21.20, 2026-11-28): `+eval-top` against `+mink` on 30 subjects of `w20`, `w21`, `w22` (the atom at the soft call made by `%4`, `%5`, `%3`: `+collapse-lazy-atom` asks through `+crash-need`); `runhoon.sh medemink2.hoon 300`: all the same (`[%done %bad 0]`).  The `%done` compiles of these and of the five `medesoft` cases: `sccreal.py OUT --extra`, then `--lean out.txt --extra > lemmas/Ska/SccLoopMedeData.lean` (about 60 s).
* `ringcall.hoon` (track K, README Gaps 19 (g), 2026-11-28): a core registered by `%fast` (`/mm`) before the first `%full`, whose arm `ma` the root `[9 4 0 1]` calls directly; after each of 6 pokes the rings of `call.cole` (formula, ring, has a `nary.cache` entry), `jets-hot`, and the ops of the root's blocks.  With `jets-hot` empty the callee gets the ring `[/mm 4]` AND compiles normally, and the root's call is `%jsf` / `%jmf` (through the ring, not `%jmp`); after a `%jets` making the rings hot, the same `%full` compiles only the root (`+callee-need` takes the driver's need), one block ending in `%jmf`.  `CodeNoRing` is not an invariant; the model `callL` has no ring case (`lemmas/Compiler/CompMonoLinkRing.lean`)
* `ringdump.hoon` (track K, README Gaps 19 (h), 2026-11-28): the raw blocks of direct calls through rings (no hot driver): a three-arm core registered by `%fast` before any compile, 8 roots (tail, `%4`, cons head/tail, `%6` test/branch, `mb`, `mc`) with their nomm, inlined nomm, `+compiled-mono`, `+compiled-nary` and every `nary.cache` entry; part B a callee registered after its caller was compiled (`%fast`, `%jets ~`: the cached caller keeps `%jmp`, a fresh compile emits `%jmf`); `tools/gen/ringcheck.py OUT > lemmas/Ska/CompRingCheck.lean`
* `sccstress.py OUTDIR [SEED] [N]` the instrumented library of `sccloop.py` and a driver of 9 fixed and N generated SCCs (one to three gates on the sample `[[a b] [c d]]`, capes cells at the sample); run `RUNHOON_LIB=OUTDIR/lib.hoon runhoon.sh OUTDIR/ck.hoon 1700 > out.txt`, then `sccstress.py --sum out.txt` (per SCC: size, sweeps, most `%must` compiles of a member, `keep`, each member's entries; the cases are in `OUTDIR/cases.txt`; parser in `sccloop_parse.py`).  2026-11-27, seeds 1 (56, with the first 4 fixed cases) and 2 (70): 145 SCCs, at most 5 sweeps, `keep` never set; the summaries and cases are in `sccstress/` (README Gaps 21.8)
* `bakedump.hoon` baking in the final pass (README Gaps 9, MAP of 2026-11-27): part A, 34 bells `[[cape data] formula]` of call-free code through the real arms of `member`'s final pass (`+run`, `+shape-collapse`, `+collapse-shape`, `+bake-need`, `+bake-need-ord`, `+coerce-lazy`, `+add-ops` of the `%imm` ops, `+to-straight`); part B, 11 `%full` pokes (gates, recursive gates whose variants know a sample's tail) with each n-ary entry's bell, `ned-final`, `bak` and whether its need is `need-to-ordered ned.bak` (always; `imm` is `~` in every entry: reads of known parts fold first).  Output `bakedump.txt`; `tools/gen/bakecheck.py bakedump.txt > lemmas/Ska/BakeNeedCheck.lean`, 34 `#guard`s, all equal (2026-11-27)
* `sccfall.py OUTDIR CASEFILE` the instrumented library of `sccloop.py` plus a probe in `member`: at every `%must` compile it recompiles the member with its own entry of `map-local` set to each of the 130 shapes within the cape `[[| |] [| |]]` (the table `F` of `need-new` against the view of itself); `sccfall.py --gen SEED N [SIZES]` writes generated cases; run `RUNHOON_LIB=OUTDIR/lib.hoon runhoon.sh OUTDIR/ck.hoon 1700 > out.txt`, then `sccfall.py --sum out.txt` (per SCC: sweeps, `need-new` and entries per `%must` compile, `FALL` when an entry went from a split to `this`, the outputs of `F`, the orbit `e' = msg (F e) e` from the real start and from every probe, and the check of `Ranked` of `lemmas/Ska/SccLoopTotal.lean` on the table).  2026-11-27: 305 SCCs (cases and summaries in `sccfall/`), no fall, no cycle, `Ranked` on all 261 tables with chains of at most 2 (README Gaps 21.8.5).  A case list over about 40 cases can fail as a whole on a generated `mint-vain`: run it in chunks of 33
* `splitmax.py OUT.hoon [--fix none|nocut|loop|sticky|late] [--trace [--small]] [--in LIB]` (track S, README Gaps 30)
                    a COPY of the library (each textual patch asserts its text occurs once) with a candidate
                    change of `+split-max` in the sweep loop of `+compile-scc-in`: `nocut` the cut line of
                    `+msg-need-ord` removed (forks too), `loop` the join of line 3601 without the cut (a copy
                    `+msg-need-ord-uncut`; `+laze-collapse` keeps it), `sticky` the join cuts as now but a member
                    whose join cut is frozen at that entry (flag: `n-args` 1 of the placeholder), `late` the
                    uncut join until stable, then a sweep of every member with the cut join, members it changes
                    frozen, the loop goes on, and ends at a cut sweep that changes nothing.  `--trace` prints the
                    loop (`%sc` `%sw` `%se`), each member's first entry (`%s0`) and every join (`%sm`), and the mug
                    of each final pass's map of straights (`%fz`); `--small` (for `mint`, `ream`) prints registers,
                    mugs and the flags fired/reach computed in the copy, and the shapes only where the cut fires or
                    an entry shrinks.  Real target: `pill.sh TAG` of the copy, then one `bench.sh KIND 1 TAG` in
                    `~/work/ska-scratch/splitmax/` (the trace is in the log; the traced `ream` runs out of loom
                    after 224 SCCs: partial)
* `splitmax-sum.py OUT.txt [--show N] [--quiet] [--codes OUT.json]` the summary of a traced run: SCCs, sweeps,
                    joins, how many reach the cut line, how many it fires in (`msgpy.py` of `tools/msgord`, checked
                    against the printed result), sweep and entry kind of each, shrinks of an entry, entries that
                    return to an earlier one, the code mugs per SCC (`--codes`, compared by fix)
* `splitmax-order.py OUT.txt` (full trace) the order of `need-new` across a member's sweeps (axes split, axes in
                    a register: equal, loses, gains, neither) and the entry steps that climb in the order of
                    the uncut join
* `splitmax-climb.py K KC [--cut]` the measure of the uncut join by enumeration: for all entries and new needs
                    with at most K inner nodes and capes with at most KC, the join climbs node by node (cell
                    cape: kind none < this, split < both, never this <-> split; atom cape: the split only
                    shrinks, both stays).  2026-11-28, `3 3`: 2,359,296 triples, 0 fail; with `--cut` 15 fail
* `splitmax-cores.py OUT.hoon SEED N [DEEP] [--targeted]` a driver of generated SCCs for the search (the form of
                    `sccstress.py`'s driver): one to three gates on a sample of four or eight leaves where every
                    other leaf is the same known gate, called by the members, so that the capes are cells;
                    `--targeted` the pattern of the real cuts (a callee whose fork cuts, read at `top` first)
* `shapecoldump.hoon` the input (`laz.nex`, the cape) and the product of `+shape-collapse` in the one-bell final pass of 34 formulas whose final pass forks (a `%6` under `%done`, known parts of the subject, nested `%6`, `%6` in a cons, `+sect` under `%next`, a split over `split-max`, a bond), the sets as lists in the order of `+rep:in`; its output is `shapecoldump.txt`, the `#guard`s of `lemmas/Ska/ShapeColCheck.lean` (`tools/gen/shapecolcheck.py`), all equal (2026-11-27).  The test's own `?=`, `;;` and `+turn` on the library's types fail with `fuse-loop`: the driver walks the lazy need as a raw noun
* `leaptwice.py OUTDIR` writes an instrumented copy of the library and a driver for the fuel `3` of `sixNextLC` (`lemmas/Ska/CompRunLC.lean`): in the case `%6` of `+run`, whenever `+leap` returns a rest, it runs `+leap` on that rest and prints `[%lp2-bad ..]` if it is not `~`.  Run `RUNHOON_LIB=OUTDIR/lib.hoon runhoon.sh OUTDIR/ck.hoon 1700 > out.txt`, then `leaptwice.py --sum out.txt`.  Over 726 formulas (the 162 of `thread-a/b/c`, 364 with a `%6` in the first part of a `%7` whose second part forks, in the head of a cons, nested, two in a row, and 200 random ones): `+leap` returned a rest 708 times (174 of them a rest that still forks or bonds, so the second `+leap` ran its loop), never a second time; `+kerf` ran 242 times, phase F 1208 (2026-11-27)
* `sofcheck.hoon` (written by `tools/gen/sofcheck.py hoon`) slams `+sound-far`, `+need-soft` and `+need-ord-edit` on 190 raw nouns (`.*` of each gate core with its sample replaced, no library type in the test): nomms with cons, `%6`, `%7`, `%10`, `%11`, `%mean`, direct `%2` into a table of four bells (one calling itself past depth `3`), needs with `%both`, cells, `%this`, `%none`, socks with cell capes; its output `sofcheck.txt` (each line twice: the harness evaluates twice) is the 190 `#guard`s of `lemmas/Ska/SofModelCheck.lean` (`sofcheck.py lean`), all equal to the models of `lemmas/Ska/SofModel.lean` (2026-11-27)
* `runshape.hoon` (written by `tools/gen/runshapecheck.py hoon`) slams the library's gate `~(run-shape cmp gen)` with the gate's sample `[nomm goal sup]`, the door's sample `[scc long-ska jets-hot map-local top b]` and `gen` replaced by raw nouns (five bells, four in the SCC, one with an n-ary entry), on 683 cases; output `runshape.txt` (each line twice), the 683 `#guard`s of `lemmas/Ska/RunShapeCheck.lean` (`runshapecheck.py lean`), all equal to `runShape` (2026-11-27, 18 s)
* `calleecomp.py OUT` (README Gaps 19 (g)) writes an instrumented library (every `+callee-need` with its case, the brackets of each compile a miss in `nary.cache` starts, the member runs, the replacements of `+inlined`, the whole-subject run of `+compile-unary`) and a driver of 37 `%full` pokes; run it with `RUNHOON_LIB=OUT/lib.hoon runhoon.sh OUT/ck.hoon 600` (13 s), then `calleecomp.py --sum out.txt` (the table `calleecomp.txt`) or `--trace out.txt CASE`.
* `sccofhit.py OUT` (README Gaps 19 (g)) the library and driver of `calleecomp.py` with two more prints: in the miss branch of `+callee-compiled` before its `+scc-of`, whether `sccs.cache` holds the callee, the size of its stored SCC and how many of its callees `sccs.cache` lacks; before the poke's own `+scc-of`, whether `sccs.cache` holds `func`.  Run `RUNHOON_LIB=OUT/lib.hoon runhoon.sh OUT/ck.hoon 900` (the prints are raw nouns: tag `7.299.955` is `%sco`, `7.368.564` `%top`).  2026-11-27: 107 of 107 misses take the cache hit of `+scc-of` (SCC sizes 1, 2, 3, 4: 91, 8, 7, 1), 0 callees outside `sccs.cache`; the poke's own `+scc-of` misses 37 of 37
* `wholedump.hoon` the raw blocks of the whole-subject version (`+compiled-mono`, what `%full` and `%dire` with `mono` `&` run) and of the n-ary version of `[4 [0 3]]`, `[6 [3 0 1] [0 2] [1 0]]`, `[[0 2] [0 3]]`, `[7 [0 2] [4 [0 3]]]` and the indirect call `[2 [0 3] [0 2]]`, with each version's need and argument count (`lemmas/Ska/CompWhole.lean`, 2026-11-24)
* `crashdump.hoon` the raw blocks of the whole-subject and the n-ary version of `[10 [6 0 1] 5 [0 6] 0 1]`, whose crash block fills through `+crash-need` on a register: on the compiler of af5cc39 `0w3 cel v9, imm 0 va` (before it also `imm 0 v9`), equal to `finishLU` and `finishLF` (its two `#guard`s in `lemmas/Ska/CompWhole.lean`, 2026-11-24).  The other guards of `CompWhole.lean`, `CompRunLCEq.lean`, `CompRunOKLC.lean`, `CompFragF.lean`, `CompFragUC.lean`, `CompConsT.lean`, `CompNCExamples.lean`, `CompCallParent.lean`, `CompCall.lean` hold unchanged on the model of af5cc39, so none of their dumps had a fill of `+crash-need` into the atom's register and the dumps of the old compiler stand
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
* `passmeasure.py OUTDIR [seed]` writes an instrumented copy of the library and drivers for the measure of the pass loop
                    of `+analyze` (`lemmas/Ska/PassMeasure.lean`, README Gaps 16): per run, how `less-code`, the product, the
                    map, `indi` and `seek` changed; per pass loop, its passes; the members `+cull` drops and whether one is
                    analysed again (also `%pm-rec caller kid target`, `%pm-ex caller kid` at every %rec and exact
                    resolution, and `%st`, a mug of the members with their entries, at every pass; and `%pm-ent`, at
                    every pass start each member with its DFS number, how its entry changed since the previous start, its
                    callees and whether it is `+dirty`, read by `passmeasure-stab.py`; and `%pm-tik`, at the same start
                    the run counter and `[ran chg]` of every function in progress, read by `passmeasure-freeze.py`).  `passmeasure-lib.hoon` is its driver over 21 library calls.  Over 2,269 calls (2026-11-27):
                    no run against the lexicographic measure (with `less-code` in the order `CapeLe`), 151 runs that changed
                    only the map (open point (a)), 21 culled members and none found again (open point (b)), no pass loop that
                    did not end.  It also checks `Tidy` and `PiNorm` (`lemmas/Ska/PassMeasureT.lean`) at every run: over
                    13,297 runs no untidy subject sock, product, `less-code` or callee subject, and no map with `[~ ~]`
                    (2026-11-27).  And `RunW` (`lemmas/Ska/PassMeasureE.lean`) of the old entry at every run after
                    the first: `less-code` always a mask of `bus`, `indi` always fixed by `+lack:ca` of `dark` and the
                    new `indi` normal; 680 runs with an old product `%void` (2026-11-27).  `--passes OUT...` checks the
                    measure of the whole component (`lemmas/Ska/PassMeasureP.lean`) per pass: of 5,058 passes that
                    ended with `%pm-end`, 2,446 went on, 947 with a push and 1,499 with every run kept or lowered,
                    one lowered and no more members next pass; none against it (`--passes-v` prints each pass)
* `repush.hoon`     point (b) of README Gaps 16 is false: three `%full` pokes on which an identity that `+cull`
                    dropped is pushed again in a later pass of the same component (with the library of
                    `passmeasure.py`: a `%pm-new` for a mug an earlier `%pm-cull` printed).  Poke 1: two sites of one
                    formula `f` whose subjects (built from two shift registers in the product of a recursive `R`)
                    pass through `[[a x x |] K]` at passes 2 and 5; poke 2: four sites, one identity pushed four times;
                    poke 3: one site pushes two identities twice each, its subject going back up when a callee
                    upstream is replaced by a fresh entry.  8, 14, 12 passes; all three return on the plain library
                    (2026-11-27)
* `passmeasure-repush.py OUT.hoon w|m|s|c|r SEED N` the drivers of the search for `repush.hoon` (`w` one re-push, `m` 2 to
                    5 sites, `s` one site, `c` a chain of two restarting callees before one site: one identity pushed 4
                    times, 31 passes, `r` random cores whose shared `f` is a restarting shift register), run with
                    the library of `passmeasure.py`; `--sum OUT.txt...` counts pushes per identity, re-pushes after a
                    cull, passes, and cases that did not finish.  Over 363 random cores (seeds 1, 11 to 16): 13
                    re-pushes, at most 2 pushes of one identity, at most 9 passes, all returned (2026-11-27)
                    `c D N M_0,..,M_{D-1}`: a chain of D restarting callees (`chain`), R's register N slots, g_i's
                    M_i (decreasing, M_{D-1} >= 3); chain(2, 14, [6, 3]) is the old c14 (2026-11-27, track F step 1:
                    D = 1..8, passes = the register slots within 5 %, see README Gaps 16)
* `passmeasure-tab.py OUT.txt...` per case: passes of the root's loop, all passes, pushes of the most pushed identity,
                    total pushes, identities, re-pushes after a cull, runs, returned; `--take OUT.txt...`: per (caller,
                    kid) the identities it resolved to (`%pm-rec`, `%pm-ex`), takeovers and returns A..B..A
* `passmeasure-q.py SEED N OUT.hoon` random cores with two shared formulas (a self-shifting `f`, a restarting `g`),
                    sites from registers, earlier products, constants, and feedback of site products into R's register;
                    960 cores (seeds 101..116): all returned, 50 re-pushes, at most 18 passes, 2 pushes of one identity
* `passmeasure-u.py SEED N OUT.hoon` random self-calls of ONE formula at many subjects (exact, %rec, %he or a push);
                    1280 cores (seeds 201..216): all returned, 3690 takeovers (69 back to an earlier target), 4 re-pushes,
                    at most 11 passes (2026-11-27)
* `passmeasure-stab.py [-v] OUT.txt...` reads `%pm-ent` and checks per pass that goes on `passOn_old` of
                    `lemmas/Ska/PassStab.lean` (no member present at two starts rises) and the candidate measures A, B, C, D,
                    DB of `lemmas/Ska/PassStabM.lean`.  Over the 2,632 cores of q, u, the chains, the re-push drivers and
                    cyc (2026-11-27): 18,682 passes, 50,915 pairs, no rise; A fails at 407, B at 415, C never, D at 43
                    (all in u, an older member goes dirty through a back edge), DB at 49 (README Gaps 16)
* `passmeasure-freeze.py [-v] OUT.txt...` the tests of the freezing argument (`lemmas/Ska/PassFreeze.lean`, README
                    Gaps 16) on `%pm-ent` and `%pm-tik`: T0 `+dirty` is "a callee's chg >= the member's ran"; T1 a member
                    that does not run keeps callees and entry, and one clean at the start runs only if a callee changed in
                    the pass (`+dirty` is tested at the member's turn); T2 a callee of a member kept by `+cull` that was a
                    member is kept; T3 what each dirty member owes its dirt to; T4 runs of starts at which a member is
                    dirty with entry and callees the same, and whether it owes that only to transient callees; T5 a
                    dirty member at every start of a pass that goes on; T6 every member reached from the root; T7
                    callee changes at a constant entry; candidates E (dirt charged to the newest callee owed), Et (E on
                    the transient members after the persistent ones froze), P2A, P2D; N, NP (C of `PassMoves.lean`: a pass
                    with nothing falling, or with a visible push, gave a start member a callee new to the graph)
                    (passes p and p+2).  Over the 2,632 cores of passmeasure-stab.py with `%pm-tik` (2026-11-27):
                    T0 to T6 never fail (69,069 starts, 118,678 kept callees, 18,682 passes), 12,462 stuck starts, none
                    owed only to transient callees, at most 49 callee changes of one member at a constant entry
                    (`fib6`); E 0 fails, P2A 97, P2D 5
* `passmeasure-run.sh LIB OUTDIR DRIVER...` runs drivers with the library of `passmeasure.py`, six at a time, 900 s
                    each; `passmeasure-show.py OUT.txt CASETAG ROOTMUG` prints one pass loop pass by pass;
                    `passmeasure-inter.py OUTDIR` matches the D failures of the u cores with their `%rec` takeovers
* `passmeasure-cyc.py OUT.hoon` a period-3 %rec takeover designed as a true cycle; it returns in 2 passes, because
                    `fol-loop` analyses both branches of a %6 whatever its test (no dispatch on a known tag) and a
                    `%rec` target's product, patched by `+patch-prod`, depends on the target only through its precision
* `passmeasure-take.py OUT.hoon x|q|r|s ARGS`, `batch DIR`, `batch2 DIR`, `--sum[-v] OUT.txt...` cores
                    designed to make a persistent member (the root, constant subject) take a fresh callee
                    forever by the `%rec` takeover at a site of constant subject (README Gaps 16): family X
                    (32 cores, `batch`: two ages feed incomparable partial patterns of a formula slot) and A (34
                    cores, `batch2`: complementary patterns fed across two tags); `--sum` per case: root passes,
                    `%st` recurrence, pushes, re-pushes, takeovers, changes of the root's callee set (`-v`: the
                    set per pass).  2026-11-27: all 66 returned, at most 10 passes, no `%st` recurrence, no
                    re-push (a cons `[v v]` has the cape `[& &]`, so its member covers every subject of its tag;
                    every pattern appears at the first read, when the registers are fresh)
                    `batch3 DIR`: family D (22 cores: relays take a formula slot whole, a direct call; chains of
                    relays delay a source); 21 return, `de3-24-44-111` does not (`takecycle.hoon`)
* `takecycle.hoon`  the pass loop of `+analyze` does not end (README Gaps 16): one `%full` poke whose root, with a
                    constant entry, changes its callee set forever by a `%rec` takeover cycle of period 18 at a
                    constant-subject site (two chains of direct relays of lengths 2 and 4 restart the members
                    `[V |]`, `[| V]` of one formula in turn).  With the library of
                    `passmeasure.py` the `%st` hash is periodic (33,135 passes in 300 s, 24 values); on the plain
                    library no answer in 600 s (2026-11-27)
* `passfix.py OUT.hoon --fix none|keep|endcull|late [--n N] [--cap N] [--in LIB]` (track F, README Gaps 16)
                    writes a PATCHED COPY of the library with a candidate fix of the pass loop (each textual
                    patch asserts its text occurs once): `keep` (a) `+cull` keeps the dropped datum and a re-push
                    starts from it, `endcull` (b) no `+cull` inside the loop, only when stable, which also needs
                    every reached member clean (`+dirty`), `late` (c) the original for N passes (64), then (b);
                    `--cap N` (measurement only) stops a loop at pass N+1 with `[%pm-capped ..]`.
                    `PASSMEASURE_IN=OUT.hoon passmeasure.py DIR` instruments such a copy
* `passmeasure-quiet.py --instrument LIB.hoon OUT.hoon`, `passmeasure-quiet.py [-v] OUT.txt...` (track F, README
                    Gaps 16) the measure of the pass loop after dab8478 on traces.  `--instrument` adds to a library of
                    `passmeasure.py` (run with `PASSMEASURE_IN` on the fixed library) at every pass start `%pq-s` (next,
                    the size of `g`, whether every identity in `g` at the previous start is still there) and `%pq-m`
                    (every member above the root: `+dirty`, swept, the mug of its callee set), and at the end of
                    `+run` `%pq-cal` (a run after the first with no `changed` whose callee set changed).  The check: A
                    nothing leaves `g` inside a loop, B a pass that goes on with a change and no push lowers one run
                    and raises none, C a quiet pass that goes on (no change, no push) keeps the five fields, and the
                    dirty members at the next start are within those at its start minus the reached ones, D the
                    triple falls.  2026-11-27, on takecycle, takemin, the 346 cores of `passfix-cores.py`, repush,
                    `passmeasure-lib.hoon`, takesame and the 15 `ck-*` drivers (2,612 cases, 11,537 pass starts, 5,241
                    passes that go on: 1,990 with a push, 3,251 with a change that lowers a run): no violation, NO quiet
                    pass that goes on (the clean test never fired), although 1,553 starts had an unreached dirty member
                    and 936 runs changed their callee set with no `changed`.  The control (the library before dab8478
                    on `repush.hoon`) fails A at 12 starts.  Largest pass number 62 (`ck-rnd1`, `%rnd1` case 49)
* `passmeasure-branch.py --instrument LIB.hoon OUT.hoon`, `passmeasure-branch.py OUT.txt...` (track F, README Gaps 16)
                    `FinBranch` on traces.  `--instrument` adds to a library of `passmeasure-quiet.py` a print at the
                    start of every `+run`: `%pb-beg` (mug, the `%2` and `%9` nodes of the formula along the grammar, the
                    formula's mug); the check pairs it with `%pm-run`, takes the innermost open run as the parent of
                    each `%pm-new`, and counts per case and parent the distinct kids, their formulas and the re-pushes.
                    2026-11-28 on the corpus of `passmeasure-quiet.py` (10,532 cases, 68,750 runs, 24,460 pushes): 0
                    re-pushes, at most 64 distinct kids of one parent (514 sites), 572 parents with more kids than
                    `%2`/`%9` nodes (at most twice as many); on the generated cores (no hints) the kid formulas never
                    exceed the sites, so the extra kids are one formula reached with other subject socks.
* `passmeasure-forms.py --instrument LIB.hoon OUT.hoon`, `passmeasure-forms.py OUT.txt...` (track F, README Gaps 16)
                    the pushed formulas against the poke's nouns.  `--instrument` adds to a library of `passmeasure.py`
                    an arm `+pf-subs` (the mugs of every subnoun, memoized) and after the push of `+analyze` a print
                    `%pf-new` (mug, formula mug, whether the formula is a subnoun of the formula and subject data of the
                    bottom of the stack, the subject sock and the formula when small); the check counts the distinct pushed
                    formulas per case and lists the pushes outside.  2026-11-28, 10,532 cases, 24,460 pushes: 4 outside
                    (2 cases of `ck-rnd2`, the value of a safe cons of constants), at most 1,009 formulas in one case.
* `passmeasure-width.py OUT.txt...` (track F, README Gaps 16) the width of each pass loop on the traces of `passmeasure.py`:
                    pushes between its first and last pass start, minus the growth of the stack (new members), an
                    upper bound on what `WidthFin` bounds.  2026-11-28, 12,592 loops: 1,950 with such a push, at most 127
                    (library), 33 on the generated cores.
* `passmeasure-git.py --instrument LIB.hoon OUT.hoon`, `passmeasure-git.py OUT.txt...` (track F, README Gaps 16)
                    the `done` answers of `+git:mi` per pass.  `--instrument` adds to a library of `passmeasure-forms.py`
                    an arm `+pw-all` and at the `done` hit of `resolve` a print `%pw-hit` (formula, caller sock, the
                    entry, the patched `[prod map]`, its `less-code`, and: entries stored, entries that pass, distinct
                    patched products).  2026-11-28, the corpus of `passmeasure-width.py` (12,574 loops, 21,088 hits):
                    one passing entry at every hit, 2,524 calls repeated across passes of a loop, none answered
                    otherwise; per pass of the 127 loop and of the 62-pass loop (`ck-rnd1`) its pushes and hits
* `width-dark.hoon` (track F, README Gaps 16 (c)) two `done` entries of `F = [2 [0 3] [0 2]]` pass the hit test
                    at `[[1 c] 6]`: the direct one (from `[[1 c] 5]`, answer `c`) and the dark one (from `[7 5]`, an
                    atom where a formula is expected, `indi` empty: answer unknown); 12 values of `c`; with the
                    library of `passmeasure-git.py` 38 hits with two passing entries, for `c = 101, 102` the answer
                    changes from `c` to unknown once the dark entry is in `done`; every loop ends in 2 passes
                    `--depth OUT.txt...` (the instrumented library also prints `%pw-dep`, the depth of the cape tree
                    of each pushed subject): per loop the deepest push of the first run against each pass; 2026-11-28:
                    12,440 of 12,574 loops never deeper after pass 1, 132 once, one case 30 times (`width-he.hoon`)
* `width-he.hoon`   (track F, README Gaps 16) case 49 of `ck-rnd1` alone: 62 passes, the stack grows by one member
                    every two passes at a subject one level deeper; with `he-threshold` 8, 16, 48 in a copy of the
                    library 14, 30, 94 passes
* `passfix-cores.py all|grid|grid2|ablate|ablate2|one OUT.hoon [..]`, `--tab OUT.txt..` one driver of the 88
                    cores of `passmeasure-take.py` (`all`), or of `core3` cases (two relay chains from `k`'s
                    target into `a`, `b`) for the smallest witness; `--tab` per case: root passes, capped, `%st`
                    period, pushes, re-pushes, takeovers.  2026-11-27, unpatched with `--cap 400`: 88 return but
                    2 capped; grids (348 cases) 22 capped, the smallest `e2-12-44-020` (`takemin.hoon`)
* `takemin.hoon`    the smallest witness found (R's register 2, 6 sites, relay chains of 1 and 2, registers 4):
                    plain library no answer in 240 s; period 9 from pass 6 with `--cap`; returns with each fix
* `takesame.hoon`, `takesame-thread.hoon` identical output of a fix: the 21 pokes of `sprestdump.hoon` and the
                    21 library calls of `passmeasure-lib.hoon` (on the core of hoon.hoon), and the 324 calls of
                    thread-a/b/c; mugs of product, state, graph.  2026-11-27: `keep`, `endcull`, `late` equal to
                    the unpatched library on these, on the 1,921 cores of passmeasure.py and on `repush.hoon`
* `untidyin.hoon`   the pokes that could plant an untidy sock: `%fast` with data under a `|` and with a cape `[| |]`
                    returns and keeps both templates normalized (`[[& |] [bat 0]]`), `%fast` with a cell cape over an atom
                    and `%dire` with an untidy bell crash, and a `%full` poke then returns with tidy memo subjects (2026-11-27)
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
* `aliasrev.hoon`   `+alias` with a `rev` that lists a predecessor no jump has (`rev-cfg` plus `0w0` for the
                    unreachable `0w1`, `TopoInv` holds): the walked `0w1` renames `0v2` to `0v5` in `old`, the end of
                    `0w2` becomes `[%don 0v5]`, and `+eval-blob` gives `5` before, `7` after; with `rev-cfg` alone
                    `0w1` is dropped and the code kept (`RevSound` of `lemmas/Ska/OptAliasRev.lean`, 2026-11-24)
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
                    it is not shown for every subject); none after any `+alias` (2026-11-24).  On the compiler of
                    af5cc39, where `+crash-need` does not fill the register it tests, `DefOnce` holds on all 553 raw
                    compiles and at all 955 calls of `+alias`, after every pass; the other counts are as above
                    (2026-11-24)
* `deadcrash.hoon`  nine formulas whose crashing operand has a dead product (`[7 [0 2] [1 5]]`
                    on an atom and the like): `+eval-top` agrees with `+mock` on all
                    (2026-11-24), so `+remove-dead-code` drops no check there
* `undefarg.hoon`   the raw blocks of `[7 [6 [0 1] [0 0] [1 0]] [6 [0 1] [0 2] [1 0]]]`: block `0wa` hops passing `0v7`, which nothing
                    defines (a kid register of `+fork-need` whose branch went to `+bomb`); the edge is dead, the first
                    `+alias` removes it, and raw and optimized code agree with `+mock` (2026-11-24)
* `xbcheck.hoon`     the block map `[%lob 1]` then `[%brn 1 1 2]` (two arguments): the first `+alias` reports a change
                    and turns the `%brn` into a `%brz` with the same blocks and targets, a second reports none,
                    and `+optimize` returns after two rounds (2026-11-27; the witness `xbBlocks` of
                    `Compiler/AuditOptTotal.lean`, for the weight of `%brn` in the measure)
* `hintdump.hoon`   hints through `+comp` (README Gaps 24): 39 formulas with `%11` (static, dynamic, cell tags), `%mean`, `%12`, alone and inside cons, `%4`, `%5`, `%6`, `%7`, `%10`, calls; per case a jam of the nomm, the whole-subject and n-ary raw blocks and the formula, then the raw code under `+eval-blob` against `+mink` on five subjects with and without a scry gate.  Its output is `hintdump.txt`; `tools/gen/hintcheck.py --sum hintdump.txt` compares the runs (390, all agree, 2026-11-27), `--lean` writes `lemmas/Ska/CompHintData.lean` (the `#guard`s of `lemmas/Ska/CompHintCheck.lean`)
* `hintdump2.hoon`  the same 39 formulas through the whole pipeline: `(mook (mink ..))` against `(eval-mook (eval-top ..))`, with `+optimize` and `+trim-trace-hints`, toons with rendered traces: 390 runs, all equal (2026-11-27)
* `hintmean.hoon`  `%mean` through `+comp` (README Gaps 25): 31 formulas and the arms of 5 real gates with `~_`; per new code entry with a `%mean` a jam of the nomm, the whole-subject and n-ary raw blocks, the formula, the subjects and a table `[bell pure nomm need]` of the bells it names, then the raw code against `+mink` (output `hintmean.txt`; `tools/gen/runhintmean.py --sum`: 360 runs agree, `--lean` writes `lemmas/Compiler/CompRunHintMeanData.lean`, the `#guard`s of `CompRunHintMeanCheck.lean`, 2026-11-27)
* `annots.hoon` (track F, README Gaps 26, `lemmas/Ska/AnnotS.lean`) every direct call of the code table with no memo key and a `+safe-fol-fol` formula part, after the 20 pokes of `inldump.hoon` and 8 more, tested on the sock at its point (`[%0 a]`: axis `a` in every noun of the sock): 33 direct calls, 31 tested, 0 failures, all 31 formula parts literals; the M19 witness's call is indirect (2026-11-27)
* `tarjandump.hoon` (written by `tools/gen/tarjancheck.py hoon`) `+tarjan` of the library on 222 graphs on atoms below 100 (the empty graph, 3 single vertices, 3 self loops, 33 chains (kids in the key set, the last vertex outside it, reversed), 24 cycles of 1 to 12, 14 pairs of cycles sharing a vertex, 24 DAGs of cycles, 96 random of six densities with and without self loops, 24 with kids outside the key set; up to 12 vertices, seed 20261127): per case `[%tj N (jam [ord out])]`, `ord` the graph in the order of `+rep` (the pre-order of the raw treap: the test's own `~(rep by g)` with a typed gate, and a `?-` on the `+mule` of the wet gate, fail to compile with `fuse-loop`), `out` the components in `rep in` order (on the empty graph only whether it crashes: it does, the bunt of `vertex = _p.n.-.g`).  12 s.  `tarjancheck.py trim OUT > tarjandump.txt`, then `tarjancheck.py lean tarjandump.txt` writes `lemmas/Ska/TarjanData.lean`; the `#guard`s of `lemmas/Ska/TarjanCheck.lean`: `tarjanM` equals every product, the flopped products meet the spec (callers first they do not on 115 graphs), the invariant clauses hold on all 8398 states of a traced copy (track Q, 2026-11-27)
* `annots2.hoon` (track Q, README Gaps 27.5, `lemmas/Ska/AnnotSDet.lean`) four `%full` pokes whose bake loses a `%6` join the analysis kept: prints every droppable call (no memo key, `+safe-fol-fol` formula part) whose formula part is not a literal, with the callee and the sock of `annots.hoon`'s walk, the totals, `+eval-top` against `+mink` on 12 subjects that fit the root's code bell, and `inl.cache`.  2026-11-28: 5 droppable, 2 not literal (`[%0 2]`, both dropped by `+inlined`), 0 failures, all 12 runs the same (about 30 s)
* `annots3.hoon` (track Q, README Gaps 27.6, `lemmas/Ska/AnnotSCheck.lean`) the pokes of `annots.hoon`, `annots2.hoon` and `hinttab.hoon` (48) in one state; walks the ANALYSIS's nomm of each datum of `memo.long-ska` (63) from its `less-code` with `+fol-loop`'s product rules and tests `DetK` of the formula part at every direct call with no memo key (47, all pass) and `KC` of every `%6` branch and nomm with a `%void` product on a non-void subject (none with the memo's products; with every direct call void, 10 branches and 95 nomms, all `KC`) (2026-11-28).
* `bakehalt-lib.hoon`, `bakehalt-adv.hoon` (track Q, README Gaps 31, 2026-11-28) the worklist of `+bake-graph` on 21 library calls and 14 stress pokes, run against the copy of `tools/gen/bakehalt_lib.py OUT --cap 20000` (`RUNHOON_LIB=OUT runhoon.sh bakehalt-lib.hoon 2400`): evaluations, bells, changes per bell, ties, changes back to `less.c`; every worklist ended, no tie
