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
tools/capped.sh -m 3G lake build                   # about 50 s from scratch, 1.6 GB peak
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
| `Exec.lean` | Symbolic execution with `simp only [nock_exec]`, and simprocs that compute `slot?` and `edit?` at a literal axis. |
| `CueSpec.lean` | `cue` of `core/` checked by the kernel on jams made by `tools/nouns.py`. |
| `CueWords.lean`, `CueExample.lean` | An earlier `cue` on 32-bit words, built for the kernel, checked on a 150-cell jam. |
| `Pill/Arm/<Family>.lean` | Generated: the named nouns of one arm family (`dec.arm`, `dec.battery`, `dec.loop`, ..., and the axis constant `dec.axis`), as a Lean module whose nouns are public but whose bodies are not exposed. |
| `Pill/Nouns/P000.lean`, ... | Generated: the rest of the pill's noun and of the SKA core (21,478 definitions named by a hash of their content), as a chain of modules. |
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
| `Hoon/Bits.lean` | `+bex`, `+lsh`, `+rsh`, `+end`, `+met`, `+cut`, `+cat`, `+can`, and `+mix`, `+dis`, `+con` as `^^^`, `&&&`, `|||`. |
| `Hoon/Muk.lean` | The arms `sit`, `sum`, `rol` of the door `+fe`, and `+muk` against the model `mukF`. |
| `Hoon/Mug.lean` | `mug_spec`: `+mug` computes `mugF` on every noun, which proves `MugSpec mugF`. |
| `Hoon/Layer1.lean`, `Hoon/Layer2.lean` | The pill's layers satisfy the predicates of their arms, and `+gor`, `+mor` and the map and set theorems hold on `layer2` with no assumption.  The only theorem files that import `Facts.lean` and the bulk. |
| `Compiler/Ca.lean`, `Compiler/So.lean` | The pill's Nock of the arms `hed`, `tel`, `con`, `all`, `int`, `uni`, `lack` of `+ca` and `hed`, `tel`, `jibe` of `+so` computes the models of `Ska/Sock.lean` on every cape and sock.  These are plain files, because the models are. |
| `Ska/Types.lean` | Models of the IR types (`Bell`, `Sock`, `Cape`, `Pole`, `Termin`, `Blob`, `Straight`, `Tone`, ...), each with its Hoon noun layout. |
| `Ska/Mink.lean`, `Ska/MinkTrace.lean` | Models of `+mink`, `+mook` and `+mock`; what Nock computes, `+mink` returns. |
| `Ska/Interp.lean`, `Ska/Steps.lean` | A model of the Hoon interpreter (`+eval-top`, `+eval-blob`, `+eval-pole`, `+eval-mook`), with the compiler as a parameter that answers pokes. |
| `Ska/Contract.lean`, `Ska/ContractExamples.lean` | The contract: what the code answered for a bell must do, given the same of its callees. It is met by a tail call and by an indirect `[2 b c]`. |
| `Ska/Theorems.lean`, `Ska/Statements.lean` | From the contract alone: `meek`, `weak`, `converse` for the models, on every reachable compiler state. |
| `Ska/Sock.lean`, `Ska/SockFacts.lean`, `Ska/CapeFacts.lean` | Models of the `+ca` and `+so` cores, and what their operations do to the nouns a sock describes. |
| `Ska/NommSem.lean` | `nomm`, a semantics for it, and the invariant `Annot` the analysis must give it. Not yet proved to agree with `+mink`. |
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
3. A clean build takes about 50 seconds and peaks at 1.6 GB.

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
6. **Not done among the arms of the compiler's leaf cores:** `app`, `pat`,
   `lot`, `yea`, `dif` of `+ca`, and `knit`, `pull`, `purr`, `darn`, `huge` of
   `+so`.  `dif:ca` and `huge:so` quote data that holds the hoon core, so the
   generator does not name them.  The others read `+so`, `+ca` or arms of
   `hoon.hoon` through the library core, whose battery the generator does not
   name for the same reason.
