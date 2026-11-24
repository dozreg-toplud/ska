#!/usr/bin/env python3
"""Write lemmas/Ska/CompRunLC.lean: runLC, the model of +run with the case %2
(callL of CompCall.lean), generated from the text of runL and of the %6 arms
sixNextFork, sixNextSimple, sixNextL of CompLazyRun.lean.

Run from formalization/.  Every extraction and replacement asserts its count.

* sixNextForkC, sixNextSimpleC, sixNextLC: the %6 arms with the code table
  `cod` that +hinted reads (`noCode` in the originals), recursion to the copies.
* runLC env: the parameter `sup` of +run (the head of the composition the
  nomm is the tail of: `some p` for q of [7 p q], inherited elsewhere, as the
  Hoon's `$(nomm q.nomm, sup `p.nomm)` and `$(nomm ..., goal ...)` do), the
  code table `env.cod` in place of `noCode`, recursion to itself, and the case
  %2 as callL with the runs of p and q.
"""
import re, sys

src = open('lemmas/Ska/CompLazyRun.lean').read()

def extract(start, end):
    i = src.index(start)
    assert src.count(start) == 1, start
    j = src.index(end, i)
    return src[i:j]

def rep(s, old, new, n):
    c = s.count(old)
    assert c == n, (old, c, n)
    return s.replace(old, new)

# the %6 arms
fork = extract('def sixNextFork [HoonMapKeys Map]', '/-- The simpler branch of the case `%6`')
simple = extract('def sixNextSimple [HoonMapKeys Map]', '/-- **The case `%6` of `run` for a goal `%next laz th`**')
six = extract('def sixNextL [HoonMapKeys Map]', '/-- **On a fork-free goal the case `%6` takes its simpler branch.** -/')
run = extract('def runL [HoonMapKeys Map] :', '/-- **The case `%6` of `runL` for a goal `%next`**')

fork = rep(fork, 'def sixNextFork [HoonMapKeys Map] (rp', 'def sixNextForkC [HoonMapKeys Map] (cod : Bell → Option Bool) (rp', 1)
fork = rep(fork, 'noCode', 'cod', 1)
simple = rep(simple, 'def sixNextSimple [HoonMapKeys Map] (rp', 'def sixNextSimpleC [HoonMapKeys Map] (cod : Bell → Option Bool) (rp', 1)
simple = rep(simple, 'noCode', 'cod', 1)
six = rep(six, 'def sixNextL [HoonMapKeys Map] (rp', 'def sixNextLC [HoonMapKeys Map] (cod : Bell → Option Bool) (rp', 1)
six = rep(six, 'sixNextL rp rq rr', 'sixNextLC cod rp rq rr', 2)
six = rep(six, 'sixNextFork rp rq rr', 'sixNextForkC cod rp rq rr', 1)
six = rep(six, 'sixNextSimple rp rq rr', 'sixNextSimpleC cod rp rq rr', 1)
assert 'noCode' not in six

run = rep(run, 'def runL [HoonMapKeys Map] : Nomm → CGoalL S → List Nat → CM Map (NextL S)',
          'def runLC [HoonMapKeys Map] (env : CallEnv) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)', 1)
run = rep(run, '  | Nomm.n0 ', '  | _, Nomm.n0 ', 1)
run = rep(run, '  | Nomm.n1 ', '  | _, Nomm.n1 ', 1)
run = rep(run, '  | Nomm.', '  | sup, Nomm.', 7)
run = rep(run, 'sixNextL (runL p) (runL q) (runL r) p q r 3',
          'sixNextLC env.cod (runLC env sup p) (runLC env sup q) (runLC env sup r) p q r 3', 1)
run = rep(run, 'noCode', 'env.cod', 7)
run = rep(run, '      let nex ← runL q goal region\n      runL p nex.goal region',
          '      let nex ← runLC env (some p) q goal region\n      runL p nex.goal region', 1)
run = rep(run, 'runL ', 'runLC env sup ', 19)
run = rep(run, '  | _, _, _ => fun _ => Option.none',
          '  | sup, Nomm.n2 p q info, goal, region =>\n'
          '      callL env (runLC env sup p) (runLC env sup q) p q info sup goal region\n'
          '  | _, _, _, _ => fun _ => Option.none', 1)
assert 'runL ' not in run and 'noCode' not in run

head = '''import lemmas.Ska.CompCall

/-!
# `run` with calls: `runLC` (generated)

Written by `tools/gen/runlc.py` from the text of `runL`, `sixNextFork`,
`sixNextSimple` and `sixNextL` of `CompLazyRun.lean`; do not edit by hand.

* `sixNextForkC`, `sixNextSimpleC`, `sixNextLC`: the arms of `%6` for a goal
  `%next` with the code table `cod` that `+hinted` reads (the originals
  pass `noCode`, which answers no callee).
* `runLC env sup`: `runL` with the case `%2` as `callL` (README Gaps 12.9),
  the code table `env.cod` for `+past` and `+past-fork`, and the parameter
  `sup` of `+run`: `some p` when `q` of `[7 p q]` is compiled, inherited
  everywhere else (the Hoon's `$(nomm q.nomm, sup `p.nomm)` and
  `$(nomm ..., goal ...)`, which keeps the sample's `sup`).

On nomms without `%2` it is `runL` (`runLC_eq`, `CompRunLCEq.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

'''
tail = '''end Comp
end SkaModel
end Formalization
'''
out = head + fork + simple + six + run + tail
open('lemmas/Ska/CompRunLC.lean', 'w').write(out)
print('wrote lemmas/Ska/CompRunLC.lean', len(out.splitlines()), 'lines')
