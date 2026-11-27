#!/usr/bin/env python3
"""Write lemmas/Ska/CompSixNxRunU.lean: `runLCU`, the text of `runLC`
(CompRunLC.lean) with the result of every `%6` under `%next` replaced by its
unwrapped need (`unwrapL`), and `finishLUCU`.  For the semantic check of
`RunOKLT` in CompSixNxCheck.lean (README Gaps 12.36)."""
import re, sys, os
root = os.path.join(os.path.dirname(__file__), '..', '..')
src = open(os.path.join(root, 'lemmas/Ska/CompRunLC.lean')).read()
a = src.index('def runLC [HoonMapKeys Map]')
b = src.index('end Comp', a)
body = src[a:b].rstrip() + '\n'
n = body.count('runLC env')
assert n == 25, n
body = body.replace('def runLC [HoonMapKeys Map]', 'def runLCU [HoonMapKeys Map]')
body = body.replace('runLC env', 'runLCU env')
old = ('      | CGoalL.next laz th => sixNextLC env.cod (runLCU env sup p) (runLCU env sup q) (runLCU env sup r) '
       'p q r 3 laz th region\n')
assert body.count(old) == 1
new = ('      | CGoalL.next laz th => do\n'
       '          let nex ← sixNextLC env.cod (runLCU env sup p) (runLCU env sup q) (runLCU env sup r) '
       'p q r 3 laz th region\n'
       '          pure ⟨unwrapL nex.laz, nex.th⟩\n')
body = body.replace(old, new)
head = '''import lemmas.Ska.CompWhole
import lemmas.Ska.CompRunLC

/-!
# `runLC` with every `%6` under `%next` unwrapped (generated)

Written by `tools/gen/sixnxu.py` from the text of `runLC`
(`CompRunLC.lean`); do not edit by hand.  README Gaps 12.36: the semantic
check of `RunOKLT` (`CompSixNxCheck.lean`) runs the whole-subject code made
when every parent reads the UNWRAPPED need of a `%6` under `%next`.

* `unside`, `unwrapL`: a fork side `[bunt ~ [o a]~]` at label `o` is `a`.
* `runLCU`, `finishLUCU`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A side of a fork, unwrapped when it is the wrapper of `+past-fork`. -/
def unside : Nat × Lazy S → Nat × Lazy S
  | (o, Lazy.mk s [] [(o', a)]) =>
    if decide (s.ned = Need.none) && HoonSet.isEmpty s.lok && decide (o' = o) then (o, a)
    else (o, Lazy.mk s [] [(o', a)])
  | e => e

/-- Every fork side unwrapped. -/
def unwrapL : Lazy S → Lazy S
  | Lazy.mk s f b => Lazy.mk s (f.map fun e => (unside e.1, unside e.2)) b

'''
tail = '''
/-- `finishLUC` with `runLCU`. -/
def finishLUCU [HoonMapKeys Map] (env : CallEnv) (nm : Nomm) : Option (Straight Map) :=
  (runLCU env Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

end Comp
end SkaModel
end Formalization
'''
open(os.path.join(root, 'lemmas/Ska/CompSixNxRunU.lean'), 'w').write(head + body + tail)
print('ok')
