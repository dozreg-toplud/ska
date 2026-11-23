# Nock Lean formalization

Lean 4 (v4.33.1, no dependencies). It states Nock 4K, and it proves facts about
Nock code taken from a steel pill, without porting that code to Lean.

## Build

```sh
cd formalization
tools/capped.sh lake build                               # about 1 minute from scratch
tools/capped.sh lake env lean Formalization/Audit.lean   # axioms of the main theorems
```

`tools/capped.sh` runs a command under a memory cap (8 GB unless `-m SIZE`).
Use it for anything that makes the kernel evaluate: an uncapped check of `cue`
on the whole pill took the machine down.

## What is here

| File | Content |
| --- | --- |
| `Nock.lean` | Nouns, `Slot`, `Edit`, the big-step relation `Eval` (the specification), and the fuelled `evalFuel`. |
| `Sound.lean` | `slot?_iff`, `edit?_iff`, and `evalFuel_sound`: a fuelled run is a derivation of `Eval`. |
| `Run.lean` | `nock`, the evaluator as a partial function, with one rewrite rule per opcode and `nock_eq_some_iff : nock s f = some p ↔ Eval s f p`. |
| `Exec.lean` | Symbolic execution with `simp only [nock_exec]`, and simprocs that compute `slot?` and `edit?` at a literal axis. |
| `Cue.lean` | `cue`, on a jam given as 32-bit words. `CueExample.lean` checks it in the kernel on a 150-cell jam. |
| `Pill/Nouns.lean` | Generated: the pill's noun and the SKA core that the pill builds, 21,453 definitions, with names for the nouns the proofs use. |
| `Pill/Facts.lean` | Generated, kernel-checked: the pill's formula on its trap evaluates to the core (236 steps), layer 2 sits at axis 2,097,151 of the core, and the arms sit at their axes. |
| `Pill/Words.lean` | Generated: the pill file as 32-bit words. Nothing uses it yet (see the gaps). |
| `Hoon/Dec.lean` | `+dec` of the pill: `dec_gate_eval (n) (h : 0 < n) : Eval [dec.battery n layer1] dec.battery (n - 1)`. |
| `Hoon/Order.lean` | `+lth`, `+dor`, `+gor`, `+mor` of the pill compute `<`, `dorF`, `gorF`, `morF`. |
| `Hoon/MapModel.lean` | The Lean models `dorF`, `gorF`, `morF`, `putF`, and the map invariant `IsMap`. |
| `Hoon/Treap.lean` | Pure Lean: the three orders are total orders, and `putF` inserts into an `IsMap`. |
| `Hoon/PutBy.lean` | `put_by`: `+put:by` of the pill ends on an `IsMap`, keeps the invariant, and holds the new pair and the old pairs under other keys. |
| `NockSmallStep.lean`, `Nomm.lean`, `DecExample.lean`, `NOMM_PROOF.md` | The earlier work: small-step semantics, a model of `nomm-1`, a toy decrement. |

Every main theorem depends on `propext`, `Classical.choice` and `Quot.sound`
only. There is no `sorry` and no `native_decide`.

## How a proof about an arm goes

A proof never unfolds Nock by hand. It opens the arm's formula once
(`nock_open dec.loop`), and `simp only [nock_exec, ...]` runs it on a subject
that has variables in it, up to the first branch that the hypotheses do not
decide. Calls into other arms are rewritten by those arms' theorems, and
recursion by the induction hypothesis. For example the whole proof that the
Nock of `+put:by` computes `putF` is nine lines for ten cases.

Formulas that are constants stay closed until a proof opens them, so a
recursive call cannot unfold forever.

## Regenerating the pill files

```sh
python3 tools/pill2lean.py pill/steel.pill Formalization/Pill
```

`pill/steel.pill` is the steel pill of ska master 9fef7d8 (sha256 `5dbc617e...`),
built without a ship by the vere test harness with `U3NC_STEEL_GEN`,
`U3NC_STEEL_SYS=desk/sys/hoon.hoon` and `U3NC_STEEL_LIB=desk/lib/nock-compilation.hoon`.
The script finds the arms by their `%fast` labels, so a new pill needs no edits
to the proofs unless the Nock of an arm changed.

## Gaps

1. **The pill is not tied to `root`.** No theorem says `cue words = some root`.
   The kernel checks `cue` on a 150-cell jam, but it keeps every intermediate
   term of an evaluation: 3.4 GB for 2,000 cells, over 6 GB for 8,000, and the
   pill has 270,000. A compiled check is out too, because comparing the result
   with `root` as trees would visit about 10^23 nodes. The way through is a
   proof in pieces: a relation `Enc words pos noun end` with one lemma per
   definition of `Nouns.lean`, each small enough for the kernel, joined by the
   constructors of the relation. Everything after `root` is checked.
2. **`+mug` is assumed.** `gor_gate`, `mor_gate` and `put_by` take
   `MugSpec mug`: the pill's `+mug` gate ends on every noun with an atom. A
   proof needs `+muk` and the bit arithmetic under it (`met`, `cut`, `rsh`,
   `mix`, `mul`, ...), each of which is a proof like `+lth`.
3. **`IsMap` is not `+apt:by`.** It is the same invariant stated for every key
   of a subtree. That the pill's `+apt` computes it is not proved.
4. **Only success is proved.** `dec_gate` says nothing about `(dec 0)`, and
   `put_loop` says nothing about nouns on which `putF` is `none`.
5. **Nothing here touches the analysis yet.**
