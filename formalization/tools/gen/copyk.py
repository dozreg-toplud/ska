#!/usr/bin/env python3
"""Write the runner text of lemmas/Ska/RawInvCLCheckLab.lean (track D, README
Gaps 14 (b)): runLC / runLCH and the helpers that hold a `copyL`
(copyAll, callL, callDM, callLM, sixNextForkC, sixNextSimpleC, sixNextLC)
with every copyL replaced by `copyK M`, the parameter M threaded through.
Usage: copyk.py FORMALIZATION_DIR OUT; the text goes between the markers
`-- BEGIN copyk.py` and `-- END copyk.py` of the check file."""
import re, sys
root = sys.argv[1]
out = sys.argv[2]

def defs(path, names):
    lines = open(root + '/' + path).read().split('\n')
    res = {}
    for n in names:
        start = None
        for i, l in enumerate(lines):
            if re.match(r'def ' + re.escape(n) + r'\b', l):
                start = i
                break
        assert start is not None, n
        j = start + 1
        while j < len(lines) and (lines[j] == '' and j + 1 < len(lines) and lines[j + 1].startswith(' ') or lines[j].startswith(' ')):
            j += 1
        res[n] = '\n'.join(lines[start:j])
    return res

src = {}
src.update(defs('lemmas/Ska/CompLazyRun.lean', ['copyAll']))
src.update(defs('lemmas/Ska/CompCall.lean', ['callL']))
src.update(defs('lemmas/Ska/CompDirectM.lean', ['callDM', 'callLM']))
src.update(defs('lemmas/Ska/CompRunLC.lean', ['sixNextForkC', 'sixNextSimpleC', 'sixNextLC', 'runLC']))
src.update(defs('lemmas/Ska/CompRunLCH.lean', ['runLCH']))
order = ['copyAll', 'callL', 'callDM', 'callLM', 'sixNextForkC', 'sixNextSimpleC', 'sixNextLC', 'runLC', 'runLCH']
ren = order + ['copyL']
def tr(t):
    def sub(m):
        n = m.group(1)
        return (n if n != 'copyL' else 'copy') + 'K M'
    t = re.sub(r'\b(' + '|'.join(ren) + r')\b(?!\.)', sub, t)
    t = re.sub(r'^def (\w+)K M', r'def \1K (M : Nat)', t, flags=re.M)
    return t
body = '\n\n'.join(tr(src[n]) for n in order)
open(out, 'w').write(body + '\n')
