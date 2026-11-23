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
tools/capped.sh lake build core                    # 3 s
tools/capped.sh lake build                         # about 1 minute from scratch
tools/capped.sh lake env lean lemmas/Audit.lean    # axioms of the main theorems
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
| `Pill/Nouns.lean` | Generated: the pill's noun and the SKA core that the pill builds, 21,710 definitions, with names for the nouns the proofs use. |
| `Pill/Facts.lean` | Generated, kernel-checked: the pill's formula on its trap evaluates to the core, and the arms sit at their axes. |
| `Hoon/Dec.lean` | `+dec` of the pill: `dec_gate_eval (n) (h : 0 < n) : Eval [dec.battery n layer1] dec.battery (n - 1)`. |
| `Hoon/Order.lean` | `+lth`, `+dor`, `+gor`, `+mor` of the pill compute `<`, `dorF`, `gorF`, `morF`. |
| `Hoon/MapModel.lean` | The Lean models `dorF`, `gorF`, `morF`, `putF`, and the map invariant `IsMap`. |
| `Hoon/Treap.lean` | Pure Lean: the three orders are total orders, and `putF` inserts into an `IsMap`. |
| `Hoon/PutBy.lean` | `put_by`: `+put:by` of the pill ends on an `IsMap`, keeps the invariant, and holds the new pair and the old pairs under other keys. |
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

## Regenerating from a new pill

```sh
python3 tools/pill2core.py pill/steel.pill core/Pill.lean
python3 tools/pill2lean.py pill/steel.pill lemmas/Pill
```

`pill/steel.pill` is the steel pill of this branch (sha256 `70311abc...`): its
`desk/sys/hoon.hoon` built from nothing and `desk/lib/nock-compilation.hoon`
on it, by the vere test harness without a ship (`U3NC_STEEL_GEN=out.pill`,
`U3NC_STEEL_SYS`, `U3NC_STEEL_LIB`).  `pill2lean.py` finds the arms by their
`%fast` labels, so a new pill needs no edits to the proofs unless the Nock of
an arm changed.  The axes in `core/Statement.lean` are not regenerated: check
them after a change to the arms of the last three cores of the library.

## Gaps

1. **Nothing connects to the statements.**  The compiler and the interpreter
   have no Lean models yet, and no proofs.
2. **The pill is not tied to `root`.**  No theorem says `cue pill = some root`,
   where `root` is the noun of `lemmas/Pill/Nouns.lean`.  The kernel cannot
   evaluate `cue` on 792 KB in one piece.  The way through is a proof in
   pieces: a relation `Enc pill pos noun end` with one lemma per definition of
   `Nouns.lean`, each small enough for the kernel, and one general theorem
   that `cue` returns what the relation accepts.
3. **`+mug` is assumed.**  `gor_gate`, `mor_gate` and `put_by` take
   `MugSpec mug`: the pill's `+mug` gate ends on every noun with an atom.
4. **`IsMap` is not `+apt:by`.**  It is the same invariant stated for every key
   of a subtree.  That the pill's `+apt` computes it is not proved.
5. **Only success is proved for the arms.**  `dec_gate` says nothing about
   `(dec 0)`, and `put_loop` says nothing about nouns on which `putF` is
   `none`.
