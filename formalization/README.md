# SKA formalization

Lean 4 (v4.33.1, no dependencies).  The aim: the SKA compiler and its IR
interpreter, as the Nock inside a steel pill, agree with Nock.  The compiler
is not ported to Lean and no port is trusted.

## Layout

| Directory | Content |
| --- | --- |
| `core/` | The trusted part, with no proofs: the Nock specification, `cue`, the pill as an atom, and the statements. It imports nothing from `lemmas/`. |
| `lemmas/` | Everything else: executable Nock, tactics, the pill's nouns as Lean definitions, models and proofs. |
| `pill/steel.pill` | The pill that `core/Pill.lean` and `lemmas/Pill/` are generated from. |
| `tools/` | The generators and the memory cap. |

## Build

```sh
cd formalization
tools/capped.sh -m 3G lake build core              # 3 s
tools/capped.sh -m 3G lake build                   # about 63 s from scratch, 2.5 GB peak
tools/capped.sh -m 3G lake env lean lemmas/Audit.lean  # axioms of the main theorems
```

`tools/capped.sh` runs a command under a memory cap (8 GB unless `-m SIZE`).
Use it for anything that makes the kernel evaluate: an uncapped check of `cue`
on the whole pill took the machine down.

## core

| File | Content |
| --- | --- |
| `Nock.lean` | Nouns, `Slot`, `Edit` and the big-step relation `Eval`: Nock 4K. |
| `Cue.lean` | `cue : Nat → Option Noun`, after `+cue` of hoon.hoon. Written to be read, not run. |
| `Pill.lean` | Generated: the pill file as an atom, in 1024-byte chunks. |
| `Statement.lean` | `Loads`, `Meek`, `Weak`, `Converse`, `Halts`, `Full`, and the few definitions they need. Start here. |

The statements quantify over every core that the pill's core can become by
pokes and by runs of the interpreter, except through a `%jets` poke that names
a jet.  Nothing in `core/` is proved, and nothing in `lemmas/` connects to
`Statement.lean` yet.

What a reader of `core/` has to take on trust beyond the Lean kernel:

1. `Eval` is Nock, and `cue` is `+cue`.
2. `Pill.lean` is the pill file (`tools/pill2core.py --check`).
3. The axes in `Statement.lean` are those of the arms they are named after.
   Each is the formula Hoon compiles the arm's name to against the library.

## lemmas

| File | Content |
| --- | --- |
| `Fuel.lean` | `slot?`, `edit?` and the fuelled `evalFuel`. |
| `Sound.lean` | `slot?_iff`, `edit?_iff`, and `evalFuel_sound`: a fuelled run is a derivation of `Eval`. |
| `Run.lean` | `nock`, the evaluator as a partial function, with one rewrite rule per opcode and `nock_eq_some_iff : nock s f = some p ↔ Eval s f p`. |
| `Exec.lean` | Symbolic execution with `simp only [nock_exec]`, and simprocs that compute `slot?` and `edit?` at a literal axis.  An axis whose path runs through a variable `v` becomes `slot? rest v`, so a hypothesis about `v` applies. |
| `CueSpec.lean` | `cue` of `core/` checked by the kernel on jams made by `tools/nouns.py`. |
| `CueWords.lean`, `CueExample.lean` | An earlier `cue` on 32-bit words, built for the kernel, checked on a 150-cell jam. |
| `Pill/Arm/<Family>.lean` | Generated: the named nouns of one arm family (`dec.arm`, `dec.battery`, `dec.loop`, ..., and the axis constant `dec.axis`), as a Lean module whose nouns are public but whose bodies are not exposed. |
| `Pill/Nouns/P000.lean`, ... | Generated: the rest of the pill's noun and of the SKA core (definitions named by a hash of their content), as a chain of modules.  A few named nouns live here too: the library core `lib`, the batteries `ca.battery` and `so.battery`, and the arms `dif` of `+ca` and `huge` of `+so`, which quote a noun holding the hoon core. |
| `Pill/Facts.lean` | Generated, kernel-checked: the pill's formula on its trap evaluates to the core, and the arms sit at their axes (`x.arm_at`). |
| `Hoon/Basic.lean` | Flags (`loob`), lists as nouns (`listN`, `appendN`), and `Below`, the predicate on the context of a second-layer arm that reads the first layer. |
| `Hoon/Dec.lean` | `+dec`: `dec_gate (c) (n) (h : 0 < n) : nock [dec.battery n c] dec.battery = some (n - 1)`, and `(dec 0)` crashes. |
| `Hoon/Arith.lean` | `+add`, `+sub`, `+mul`, `+lth`, `+lte`, `+gte`, `+gth`, `+max`, `+min`, `+dvr`, `+div`, `+mod` compute their `Nat` operations; `+sub` crashes below zero and `+dvr`, `+div`, `+mod` on a zero divisor. |
| `Hoon/MugSpec.lean` | `MugSpec`, what the arms that hash need from `+mug`. |
| `Hoon/Order.lean` | `+dor`, `+gor`, `+mor` compute `dorF`, `gorF`, `morF`, given `MugSpec`. |
| `Hoon/MapModel.lean` | The Lean models `dorF`, `gorF`, `morF`, `putF`, and the map invariant `IsMap`. |
| `Hoon/Treap.lean` | Pure Lean: the three orders are total orders, and `putF` inserts into an `IsMap`. |
| `Hoon/PutBy.lean` | `put_by`: `+put:by` ends on an `IsMap`, keeps the invariant, and holds the new pair and the old pairs under other keys. |
| `Hoon/Lists.lean` | `+lent`, `+weld`, `+flop`, `+snag`, `+scag`, `+slag` against `List Noun`; `+turn`, `+roll`, `+levy`, `+lien` given what their gate argument computes on the elements. |
| `Hoon/Units.lean` | `+need`, `+fall` and `+biff` on units. |
| `Hoon/Maps.lean` | `+get:by`, `+has:by`, `+got:by`, `+gut:by` on an `IsMap`. |
| `Hoon/Apt.lean` | `apt_by`: the pill's `+apt:by` says yes exactly on `IsMap` nouns and on the lone nodes `[x ~ ~]` with an atom `x`. |
| `Hoon/TapBy.lean`, `Hoon/TapIn.lean` | `+tap:by` and `+tap:in` (the same noun): the list of the pairs of a map, of the keys of a set. |
| `Hoon/DelBy.lean`, `Hoon/GasBy.lean`, `Hoon/JabBy.lean` | `+del:by` (with the merge of two treaps), `+gas:by`, `+jab:by` on maps. |
| `Hoon/RepBy.lean` | `+rep:by` and `+rep:in` (one noun): a fold over the nodes in pre-order. |
| `Hoon/MapFolds.lean`, `Hoon/SetFolds.lean` | `+key:by`, `+run:by`, `+any:by`, `+wyt` of `+by` and `+in` (one noun); `+gas:in`, `+any:in`, `+run:in`, `+del:in`. |
| `Hoon/Ju.lean` | The doors `+ju` (get, put, has, del, gas) and `+ja` (get, add). |
| `Hoon/ListsMore.lean` | `+skim`, `+skip`, `+murn`, `+rear`, `+snip`. |
| `Hoon/ListsSort.lean` | `+welp`, `+zing`, `+snoc`, `+skid`, `+spin`, and `+sort` against the quicksort `qsort`, which permutes its list. |
| `Hoon/Axis.lean` | `+cap`, `+mas`, `+peg`, and what they mean for `slot?` (`slot_pegF`, `slot_cap_mas`). |
| `Hoon/Sets.lean` | `+put:in` and `+has:in`, with a set read as the map of its keys to `~`. |
| `Hoon/Rip.lean` | `+rip` on a bite of step at least 1: the blocks of an atom, least significant first (`ripF`). |
| `Hoon/Bits.lean` | `+bex`, `+lsh`, `+rsh`, `+end`, `+met`, `+cut`, `+cat`, `+can`, and `+mix`, `+dis`, `+con` as `^^^`, `&&&`, `|||`. |
| `Hoon/Muk.lean` | The arms `sit`, `sum`, `rol` of the door `+fe`, and `+muk` against the model `mukF`. |
| `Hoon/Mug.lean` | `mug_spec`: `+mug` computes `mugF` on every noun, which proves `MugSpec mugF`. |
| `Hoon/Layer1.lean`, `Hoon/Layer2.lean` | The pill's layers satisfy the predicates of their arms, and `+gor`, `+mor` and the map and set theorems hold on `layer2` with no assumption.  The only theorem files that import `Facts.lean` and the bulk. |
| `Compiler/Ca.lean`, `Compiler/So.lean` | The pill's Nock of the arms `hed`, `tel`, `con`, `all`, `int`, `uni`, `lack`, `app` of `+ca` and `hed`, `tel`, `jibe`, `knit`, `purr` of `+so` computes the models of `Ska/Sock.lean` on every cape and sock.  The arms that read the library core assume only what it gives at the named axes `ca.lib.axis` and `so.lib.axis`.  These are plain files, because the models are. |
| `Iter.lean` | `nockW call`, Nock whose opcodes `2` and `9` hand the formula they compute to `call`, and `iterN k`, Nock with calls at most `k` deep: `nock = nockW nock`, and `nock` returns `p` exactly when some `iterN k` does.  An induction on `k` meets a loop's calls to itself at `iterN k`. |
| `Hoon/Mink.lean` | The gates `frag` and `edit` of the `|^` core of `+mink` are `slot?` and `edit?` as units (`mink_frag_gate`, `mink_edit_gate`), with `+cap` and `+mas` from the context (`MinkIn`). |
| `Compiler/Mink.lean` | `+mink` against `minkF`: one symbolic run of its loop (`mink_loop_unfold`) gives `NStep`, the loop on nouns with its calls as parameters; `NStep` with `nock` is `minkStep` encoded (`nstep_exact`); `mink_gate_iff`: the gate returns `x` exactly when `Mink` returns a tone that `x` encodes, given `MinkIn` and `SlamIsNock lib`. |
| `Compiler/Monk.lean` | `+monk` and `+mack` from `+mink`: `+monk` drops the trace, `+mack` keeps the product of a `%0` (`monk_gate_iff`, `mack_gate_iff`). |
| `Compiler/MinkPill.lean` | The same in the pill's layer 4, where `MinkIn`, `MonkIn`, `MackIn` hold (`mink_pill_iff`, `mink_pill_call`, `monk_pill_iff`, `mack_pill_iff`). |
| `Compiler/Mook.lean` | `+mook` and `+mock` against `mookF` and `Mock`: the test of the tone, `+skip` (`mook_skip`), the `+turn` of `rend` over the trace, `rend` on a `%mean` of a cell through `+mack` and `(soft tank)` (`rend_mean`), and the branches of `rend` that format with constants, `+rip` and `+scow %p` of `+mug` (`rend_leaf`, `rend_hand`).  `mook_gate_iff`, `mock_gate_iff`. |
| `Compiler/MockPill.lean` | The same in layer 4 (`mock_pill_iff`).  What stays assumed of `Lib`, each a statement about the pill's Nock for one field: `(soft tank)` (`SoftTankIs`), the cord of `+skip` (`SkipMsgIs`), `+scow %p` (`HandIs`), and `rend` on `%hunk` of a cell and on `%spot` (`RendRestIs`); and, on `Lib` alone, the frames that `rend` formats with constants and `+rip` (`RendLeafIs`). |
| `Compiler/Pi.lean` | `cons`, `hed`, `tel`, `slot` (on an axis of at least `1`) and `compose` of the provenance core `+pi` compute B's models of `Ska/Pi.lean`; `hed`, `tel`, `slot` read `+peg` (and `+cap`, `+mas`) of layer 1 through the library core (`PegOf`, `AxisOf`). |
| `Compiler/PiEdit.lean` | `edit` and `prune` of `+pi`, `+distribute` and `+double-int` against B's models (`pi_edit_gate`, `pi_prune_gate`, `distribute_gate`, `double_int_gate'`), and on the pill's library core with no assumption (`*_pill`).  The upward loop of `edit` is the noun of the upward loop of `+darn:so` (`pi_edit_up`); `prune` computes `distribute` with its arguments swapped. |
| `Compiler/Inlineable.lean` | `+inlineable` computes `inlineable` of `Ska/FolLoop.lean` on every noun and in every context (`inlineable_gate'`); it reads nothing from its context. |
| `Compiler/Lib.lean` | `dif` of `+ca` and `huge` of `+so`, whose crash messages quote a noun that holds the hoon core, so that the generator names them in the bulk chain (`ca.dif.mean` is the quoted noun).  And the pill's library core `lib` satisfies `CaOf`, `SoOf`, `AxisOf`, `YeaOf`: every gate of `+ca` and `+so` computes its model on the pill's core (`ca_int_pill`, ..., `so_darn_pill`) with no assumption. |
| `Compiler/Axes.lean` | `pat`, `lot` of `+ca` and `pull` of `+so`, which walk an axis with `+cap` and `+mas` of layer 1, read through the library core at `ca.lib.layer1.axis`; B's `cap` and `mas` equal `capF` and `masF`.  And `yea` of `+ca`, with `+peg` and `+weld`, and `darn` of `+so`. |
| `Ska/Types.lean` | Models of the IR types (`Bell`, `Sock`, `Cape`, `Pole`, `Termin`, `Blob`, `Straight`, `Tone`, ...), each with its Hoon noun layout. |
| `Ska/Mink.lean`, `Ska/MinkTrace.lean` | Models of `+mink`, `+mook` and `+mock`; what Nock computes, `+mink` returns. |
| `Ska/Interp.lean`, `Ska/Steps.lean` | A model of the Hoon interpreter (`+eval-top`, `+eval-blob`, `+eval-pole`, `+eval-mook`), with the compiler as a parameter that answers pokes. |
| `Ska/Contract.lean`, `Ska/ContractExamples.lean` | The contract: what the code answered for a bell must do, given the same of its callees. It is met by a tail call and by an indirect `[2 b c]`. |
| `Ska/Theorems.lean`, `Ska/Statements.lean` | From the contract alone: `meek`, `weak`, `converse` for the models, on every reachable compiler state. |
| `Ska/Sock.lean`, `Ska/SockFacts.lean`, `Ska/CapeFacts.lean` | Models of the `+ca` and `+so` cores, and what their operations do to the nouns a sock describes. |
| `Ska/NommSem.lean` | `nomm`, a semantics for it, and the invariant `Annot` the analysis must give it. Not yet proved to agree with `+mink`. |
| `Ska/NommAgree.lean` | `nomm_agree`: a nomm satisfying `Annot`, with a code table satisfying `CodeOK`, returns exactly the tones `+mink` returns on the formula. |
| `Ska/Pi.lean` | Models of the provenance core `+pi`, of `+distribute` and `+double-int`, and of `sock-anno`. |
| `Ska/FolLoop.lean`, `Ska/FolLoopFacts.lean` | A model of `fol-loop` for one function, with direct calls answered from a table, and of `+inlineable`, `+safe-nomm`, `+safe-fol-fol`. |
| `Ska/FolLoopSound.lean` | `folLoop_good`: given a sound table, the nomm of `fol-loop` satisfies `Annot` and its product sock holds of every product; `+safe-fol-fol` and `saf` give what the inline and memo cases assume. |
| `Ska/CallGraph.lean` | Models of the call graph's arms (`+patch-prod`, `+msg-anno`, `+git:mi`, `+recursive-call`), and what a converged graph gives. The fixed point itself is not proved: `WantSound` and the soundness of the table on products are hypotheses. |
| `Ska/Prov.lean`, `Ska/ProvFacts.lean` | The provenance invariant on products (`ProvR`, `ProvO`): a part with axis provenance is that axis of the function's subject. Nock 0, cons, Nock 10, the join of two branches and a direct call through `compose:pi` keep it; `+patch-prod` is sound under it. |
| `Ska/WantMono.lean` | `want` only grows along a run of `fol-loop`. |
| `Ska/AppPath.lean` | `app:ca` below a covered path; the static conditions `StatS` and `ShapeOK`; `known_formula`: on subjects of the code requirement, a fully known formula-formula is that formula. |
| `Ska/Stat.lean` | The static condition `StatOK` (the product sock generalizes what the subject sock knows at each axis provenance), kept by every sock operation of `fol-loop`. |
| `Ska/AppMask.lean` | `+app:ca` under a mask, and the subject half of a call site, `call_sub_fits`: on the code requirement, a call's subject fits the callee's requirement. |
| `Ska/FolLoopRel.lean` | `folLoop_rgood`: the soundness of `fol-loop` relative to the code requirement, every case; `folLoop_wantSound`, `folLoop_relProd`. |
| `Ska/Converge.lean` | `converged_agree`: the analysis output of every entry of a converged graph agrees with `+mink` on its code requirement. `ConvergeProd.lean` removes its assumption `ProdRel`. |
| `Ska/MinkFuel.lean` | `+mink` taken apart with its fuel: a run with fuel `k+1` has its parts, and the callee of Nock 2, with fuel `k`. |
| `Ska/FolLoopProd.lean` | `folLoop_rprod`: the product half of `folLoop_rgood` for runs with fuel `K+1`, from a table right on callee runs with fuel `K`. |
| `Ska/ConvergeProd.lean` | `prodRel_of_converged`: `ProdRel` at convergence, by induction on the fuel. `agree_at_convergence` assuming `RunEntryM`: the stored product is the merge (`+msg-anno` or `+double-int`) of the last run's with some older one, which is what `+run` stores. `merge_no_fixed_point`: the two merges have no common fixed point. |
| `Ska/CompSim.lean` | The relation `+comp` must establish for nomm without calls and hints (`CompDone`, `CompRel` per block and goal), which gives `BellContract`; composition for `%7` and `%6`; the leaves `[1 k]`, `[0 1]`, `[0 0]` meet the contract. `+comp` itself is not modelled. |
| `Ska/WellFormedFacts.lean` | Every sock operation of the analysis keeps `WellFormed`; `folLoopTop_wf`: on a well-formed subject sock, products are well formed and the table is read only at well-formed subject socks. |
| `Ska/RunStep.lean` | A model of `+run` after `fol-loop` (`runDatum`); the writes of `+ska-callgraph` keep the graph well formed (`GStep.wf`); the poke's code table `codeOf`; `ConvergedGraph`. The loop that makes the writes (`resolve`, `+analyze`, the SCC iteration) is not modelled. |
| `Ska/ConvergeGraph.lean` | `agree_poke`: agreement with `+mink` from the final graph of a poke, each run with its own table, with well-formedness proved from the poke's sock. It assumes the graph converged, and it does not cover memo hits from earlier pokes. |
| `Ska/CompSimOps.lean` | The block relation of `+comp` through cons (`%next` with a pair need), `[3 p]`, `[4 p]`, `[5 p q]`, from the blocks each case emits. |
| `Ska/Analysis.lean` | A state-passing model of `+ska-callgraph` (`fol-loop` with the whole `gen`, `resolve`, `+analyze`, `+run`, the pass and member loops, `+dirty`, `+sweep`, `+above`, `+cull`, `+pop`), `+prune-callgraph`, `+memo-final-entry` and the analysis part of `+ska-poke`, arm by arm and fuelled. Maps and sets are the parameter `Treap`; `+he-sock`, `+soft-spot` and `+register-fast` are the parameter `Env`. This is the model the pill is to be compared with; the fixed-table model of `FolLoop.lean` is a special case. |
| `Ska/FolRel.lean` | `FolR`: `fol-loop` with answers that change during a run, and its soundness (`folR_mono`, `folR_wf`, `folR_rgood`, `folR_rprod`). |
| `Ska/ConvergeRel.lean` | Agreement from the final graph with each last run in `FolR` (`ConvergedGraphR`, `GStepR`, `agree_pokeR`); the older statements as special cases; `RunEntryR.pop`. |
| `Ska/Bridge.lean` | The state-passing `fol-loop`, projected, is in `FolR` (`bridge_step`, `folLoop_goOK`, `run_folTopR`), under an invariant that `resolve` keeps, which is assumed; the write of `+run` is a `GStepR.run`. |
| `Ska/MemoPoke.lean` | Memo hits from earlier pokes: `MemoEntryOK`, the hit entry as a third kind (`ConvergedGraphM`, `agree_pokeM`), and the memo invariant kept by every poke (`MemoInv`, `memoInv_poke`). |
| `Ska/CompModel.lean` | A model of `+comp`'s `run` for nomm without calls, hints and forks (`[^ *]`, `%0`, `%1`, `%3`, `%4`, `%5`, `%7`) and its helpers (`emit`, `from`, `split`, `copy`, `mede`, `collapse-lazy-atom`, `forl`); `HoonSet` abstracts the sets. |
| `Ska/CompSem.lean` | `RunOK`, the relation for one run of `run` against `execBlob` (goals with looks and jump arguments, the necessity of the looks). |
| `Ska/CompRun.lean`, `Ska/CompLook.lean`, `Ska/CompMede.lean`, `Ska/CompUnary.lean` | `%0`, `%1`, `%7`, `%4` (`%done`, `%pick`) and `%3` (`%pick`) meet `RunOK`; `+sure-require-look`; `+mede`. |
| `Ska/CompFrag.lean` | `run_ok`: the model of `run` meets `RunOK` on the fragment `Frag`, by induction, with no assumption about `+comp`. Not yet connected to `BellContract`: `coerce-lazy` and `to-straight` are not modelled. |
| `Ska/BugWitness.lean` | The three places where the Hoon broke the contract when this was written (an inlined call dropping its formula's formula, malformed operands, `%bare`). Fixed in the Hoon since; the models still describe the old code. |
| `NockSmallStep.lean`, `Nomm.lean`, `DecExample.lean`, `NOMM_PROOF.md` | The earlier work: small-step semantics, a model of `nomm-1`, a toy decrement. |

Every main theorem depends on `propext`, `Classical.choice` and `Quot.sound`
only.  There is no `sorry` and no `native_decide`.

## How a proof about an arm goes

A proof never unfolds Nock by hand.  It opens the arm's formula once
(`nock_open dec.loop`), and `simp only [nock_exec, ...]` runs it on a subject
that has variables in it, up to the first branch that the hypotheses do not
decide.  Calls into other arms are rewritten by those arms' theorems, and
recursion by the induction hypothesis.  For example the whole proof that the
Nock of `+put:by` computes `putF` is nine lines for ten cases.

Formulas that are constants stay closed until a proof opens them, so a
recursive call cannot unfold forever.

A theorem about a gate quantifies over the gate's context `c` and assumes
only what the gate's Nock reads from it: a predicate such as `LthIn c` says
that `c` holds the arm `+lth` at `lth.axis` and what `+lth` reads in turn.
The predicates are `abbrev`s of conjunctions of `slot?` equations, so a
hypothesis `hc : LthIn c` given to `simp` rewrites the `slot?` that the
executor cannot compute on the variable `c`.  Each family file proves that
the pill's layer satisfies its predicates (`arith_layer1`,
`mugNeeds_layer2`), so a change elsewhere in the pill leaves the theorems
standing.

Arithmetic in models stays out of reach of reduction.  The models of `+muk`
and `+mug` recurse through generic combinators (`iterDown`, `retry`,
`foldNoun`), and they are tied to the expressions that the execution
produces by small equations over variables (`mukBlock_eq`, `fmix32_eq`),
proved by `delta` and `Eq.refl`.  An equation lemma of a recursive
definition whose body calls the murmur3 arithmetic, or an `rfl` between two
such expressions that are not syntactically equal, took the elaborator past
3 GB.

A function that `simp` runs on the pill's formulas must not be structurally
recursive.  `nockW` of `Iter.lean` was first defined by structural recursion
on the formula, and `simp only` with its rules on the loop of `+mink` took
more than 2 GB after a few hundred steps, where the same rules for `nock` ran
in half a second.  Defined with `partial_fixpoint`, like `nock`, it runs as
fast as `nock`.

## Regenerating from a new pill

```sh
python3 tools/pill2core.py pill/steel.pill core/Pill.lean
python3 tools/pill2lean.py pill/steel.pill lemmas/Pill
```

`pill/steel.pill` is the steel pill of this branch (sha256 `57a5de13...`): its
`desk/sys/hoon.hoon` built from nothing and `desk/lib/nock-compilation.hoon`
on it, by the vere test harness without a ship (`U3NC_STEEL_GEN=out.pill`,
`U3NC_STEEL_SYS`, `U3NC_STEEL_LIB`).  `pill2lean.py` finds the arms by their
`%fast` labels, and the few arms without one through the arms that call them,
so a new pill needs no edits to the proofs unless the Nock of an arm changed.
The axes in `core/Statement.lean` are not regenerated: check them after a
change to the arms of the last three cores of the library.

## Caching

The generated files and the theorem files are Lean modules.  An arm file
exports its nouns without their bodies, except the exposed axis constants.
The arm's own theorem file reads the bodies with `import all`, and its callers
import only its theorems.  So:

1. A change to the Nock of one arm, after regeneration, changes its arm file
   only: an arm file is byte-identical when the arm's Nock and axis did not
   change, and the chain refers to arms by name.  It rechecks the arm file,
   the arm's theorem file, `Facts.lean` and `Audit.lean`, and nothing else,
   as long as the arm's theorems still hold.  (Measured by changing a
   character of the tape in `dec.battery`.)
2. A change to a declaration of the chain rebuilds the rest of the chain,
   `Facts.lean` and the layer files, and no gate theorem file.  A comment
   rebuilds the edited file only.
3. A clean build takes about 63 seconds (3 min 40 s of CPU) and peaks at
   2.5 GB for the whole build (measured 2026-11-23 under a 3 GB scope).

## Gaps

1. **Nothing connects to the statements.**  The compiler and the interpreter
   have no Lean models yet, and no proofs.
2. **The pill is not tied to `root`.**  No theorem says `cue pill = some root`,
   where `root` is the noun of `lemmas/Pill/Nouns/`.  The kernel cannot
   evaluate `cue` on 792 KB in one piece.  The way through is a proof in
   pieces: a relation `Enc pill pos noun end` with one lemma per definition of
   `Nouns.lean`, each small enough for the kernel, and one general theorem
   that `cue` returns what the relation accepts.
3. **`IsMap` and `+apt:by` differ on one shape.**  `apt_by` proves that the
   pill's `+apt:by` accepts exactly the `IsMap` nouns and the lone nodes
   `[x ~ ~]` with an atom `x`: on a node without bounds and without children
   `+apt:by` never reads its head.
4. **Failure is proved for few arms.**  `(dec 0)`, `+sub` below zero,
   `+dvr`, `+div`, `+mod` by zero and `+snag` past the end crash; nothing is
   proved about gates slammed on nouns of the wrong shape, nor about nouns on
   which a model is `none`.
5. **Not done among the arms of the library:** `+uni`, `+int`, `+dif` of `+by`
   and `+in`.
6. **The arms of `+ca` and `+so` are all done.**  No arm of `+ca` or `+so`
   disagrees with B's model.
7. **The virtualization arms are done** up to formatting: `+mink`, `+monk`,
   `+mack`, `+mook` and `+mock`.  `+scow`, `+smyt`, `+crip` and `+soft` are
   not proved; `mock_pill_iff` assumes what they compute, field by field of
   `Lib`.
8. **Not done among the compiler's arms:** `+safe-nomm`, `+safe-fol-fol`,
   `+knit-anno`, `+patch-prod`, `+msg-sock`, `+msg-anno`.
