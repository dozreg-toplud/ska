#!/usr/bin/env python3
"""Write the runner text `csxRun` of lemmas/Ska/RawInvCLCheckSix.lean (track D,
README Gaps 14 (b)): `runLC` of lemmas/Ska/CompRunLC.lean with every recursive
call `runLC env sup x` replaced by `csxWrap M Sel tag x K (csxRun M Sel K env sup x)`,
`tag` the number of the call site in textual order.
Usage: csxrun.py FORMALIZATION_DIR OUT"""
import re, sys
root, out = sys.argv[1], sys.argv[2]
lines = open(root + '/lemmas/Ska/CompRunLC.lean').read().split('\n')
s = next(i for i, l in enumerate(lines) if l.startswith('def runLC '))
j = s + 1
while j < len(lines) and (lines[j].startswith(' ') or lines[j] == '' and lines[j + 1].startswith(' ')):
    j += 1
t = '\n'.join(lines[s:j])
t = t.replace('def runLC [HoonMapKeys Map] (env : CallEnv) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)',
  'def csxRun (M : Nat) (Sel : Nat → Nomm → Bool) (K : List (Nat × List Nat)) (env : CallEnv) : '
  'Option Nomm → Nomm → CGoalL LS → List Nat → CM FM (NextL LS)')
t = t.replace('CM Map', 'CM FM').replace('CGoalL S', 'CGoalL LS').replace('NextL S', 'NextL LS')
n = [0]
def sub(m):
    n[0] += 1
    return '(csxWrap M Sel %d %s K (csxRun M Sel K env %s %s))' % (n[0], m.group(2), m.group(1), m.group(2))
t = re.sub(r'runLC env (sup|\(some p\)) (\w+)', sub, t)
open(out, 'w').write(t + '\n')
