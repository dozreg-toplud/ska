# Nock Lean Formalization

This directory contains a small Lean 4 formalization of the Nock 4K rules from
`docs/nock/4.txt`.

- `Formalization/Nock.lean` defines nouns, axis lookup, edit, an inductive
  big-step `Eval` relation, and a fuelled `evalFuel` executable counterpart.
- `Formalization/NockSmallStep.lean` defines a one-step reduction relation over
  explicit non-noun evaluation terms and proves it equivalent to the big-step
  relation, including termination equivalence and result preservation.
- `Formalization/Nomm.lean` defines a Lean model of SKA's post-analysis
  `nomm-1` IR, its big-step semantics, sock-template matching, and the
  equivalence predicate an analyzer correctness proof should establish. It
  intentionally does not formalize the current unstable analyzer algorithm.
- `NOMM_PROOF.md` describes the proof obligations for showing that a Nomm body
  produced by a stabilized SKA analysis is equivalent to the input Nock formula
  under a subject sock.
- `Formalization/DecExample.lean` encodes a compact Nock battery for the Hoon
  decrement arm and runs it through the compiled arm-invocation formula
  `[9 2 0 1]`.
- `examples/dec.hoon` is the Hoon source for the trivial decrement arm, based on
  `desk/tests/tests.hoon`'s `++test-dec`.
- `examples/dec-core.nock` records the compact compiled Nock core used by the
  Lean example, and `examples/dec.nock` records the compiled invocation formula
  used by the repo's Hoon test.

With Lean installed, run:

```sh
cd formalization
lake env lean Formalization/DecExample.lean
```

The main checked statements are:

```lean
theorem decArmInvocation_decrements_five :
    evalFuel 128 (decCore 5) decArmInvocation = some (A (5 - 1))

theorem decArmInvocation_decrements_three :
    evalFuel 128 (decCore 3) decArmInvocation = some (A (3 - 1))

theorem decArmInvocation_bigStep_decrements_three :
    Eval (decCore 3) decArmInvocation (A (3 - 1))
```
