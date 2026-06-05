# Nock Lean Formalization

This directory contains a small Lean 4 formalization of the Nock 4K rules from
`docs/nock/4.txt`.

- `Formalization/Nock.lean` defines nouns, axis lookup, edit, an inductive
  big-step `Eval` relation, and a fuelled `evalFuel` executable counterpart.
- `Formalization/NockSmallStep.lean` defines a one-step reduction relation over
  explicit non-noun evaluation terms and proves it equivalent to the big-step
  relation, including termination equivalence and result preservation.
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
