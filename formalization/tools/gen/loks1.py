#!/usr/bin/env python3
"""The measurement of README Gaps 12.36: the goal-side generalization.
Writes lemmas/Ska/CompSixNxGoal.lean: `LOKS1` (the text of `LOKS`,
CompConsLS.lean, with the premise `Tree1 L` in place of `Flat L`) and copies
of constructor lemmas with `LOKS1` for the part that runs under the goal.
Argument `--with-n0` also copies `lokS_n0` (it does not build: see Gaps)."""
import os, sys
root = os.path.join(os.path.dirname(__file__), '..', '..')
def grab(path, start, stop):
    s = open(os.path.join(root, path)).read()
    a = s.index(start); b = s.index(stop, a)
    return s[a:b].rstrip() + '\n'
loks = grab('lemmas/Ska/CompConsLS.lean', '/-- **The hypothesis under a flat lazy goal**', '/-! ## `+from`')
assert loks.count('structure LOKS (') == 1 and loks.count('    Flat L → Clean') == 1
loks = loks.replace('structure LOKS (', 'structure LOKS1 (').replace('    Flat L → Clean', '    Tree1 L → Clean')
loks = loks.replace('/-- **The hypothesis under a flat lazy goal**', '/-- **`LOKS` at one-level tree goals** (generated)')
seven = grab('lemmas/Ska/CompSevenLS.lean', 'theorem lokS_seven {', '/-- **The jump of a hinted')
assert seven.count('LOKS (S := S)') == 3
seven = seven.replace('theorem lokS_seven {', 'theorem lokS1_seven {')
# q runs under the goal: LOKS1; p under q's flat result: LOKS; the whole: LOKS1
parts = seven.split('LOKS (S := S)')
seven = parts[0] + 'LOKS1 (S := S)' + parts[1] + 'LOKS (S := S)' + parts[2] + 'LOKS1 (S := S)' + parts[3]
out = ['''import lemmas.Ska.CompSixNxRel
import lemmas.Ska.CompSevenLS

/-!
# `LOKS` at one-level tree goals: the measurement (generated)

Written by `tools/gen/loks1.py`; do not edit by hand.  README Gaps 12.36:
which constructor lemmas of `LOKS` go through for a goal that is a
one-level tree (`Tree1`, the unwrapped result of a `%6`) by the same proof
text.  `LOKS1` is `LOKS` with the premise `Tree1 L` in place of `Flat L`.

* `LOKS1`, `LOKS1.toS` (a member of `LOKS1` is one of `LOKS`).
* `lokS1_seven`: the text of `lokS_seven`, with `LOKS1` for `q`: it builds
  unchanged (the goal's premises are passed to `q`, `p` runs under `q`'s
  flat result).

The copy of `lokS_n0` (`--with-n0`) fails at three places: `entries_flat`
(the entries of a forked goal include its forks'), `fromL_flat` (`+from`
over forks has no spec), and `[0 1]`, whose result is the goal itself, so a
`Flat` result is FALSE at a forked goal: the goal-side relation must
conclude `Tree1` of the result too (`LOKT` with `Tree1` goals).
''' + ('* `lokS1_n0`: the text of `lokS_n0`.\n' if '--with-n0' in sys.argv else '') + '''-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

''', loks, '''
/-- **A member of `LOKS1` is one of `LOKS`** (a flat goal is a one-level tree). -/
theorem LOKS1.toS {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS1 (S := S) (Map := Map) x lib N env P f nm) : LOKS (S := S) (Map := Map) x lib N env P f nm :=
  ⟨H.clean, fun c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 hr =>
    H.run c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 (flat_tree1 c16) c17 c18 hr⟩

''', seven]
if '--with-n0' in sys.argv:
    n0 = grab('lemmas/Ska/CompConsLS.lean', 'theorem lokS_n0 (', 'end Comp')
    assert n0.count('LOKS (S := S)') == 1
    out.append('\n' + n0.replace('theorem lokS_n0 (', 'theorem lokS1_n0 (').replace('LOKS (S := S)', 'LOKS1 (S := S)'))
out.append('\nend Comp\nend SkaModel\nend Formalization\n')
open(os.path.join(root, 'lemmas/Ska/CompSixNxGoal.lean'), 'w').write(''.join(out))
print('ok')
