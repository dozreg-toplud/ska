#!/usr/bin/env python3
# usage: sccofhit.py OUTDIR      then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 900 > out.txt
#   tools/hoon/sccofhit.py --sum out.txt
# Which path of +scc-of a miss in nary.cache takes (README Gaps 19 (g), track K): the
# instrumented library and the 37 %full pokes of calleecomp.py, plus, in the miss branch of
# +callee-compiled, before its +scc-of, the print
#   [%sco b in-sccs scc-size callees-outside-sccs mono-run-flag-unknown]
# with in-sccs: sccs.cache holds b (the HIT path of +scc-of: [u.s sccs], no sub loop, no
# +tarjan), scc-size: the size of the stored SCC (0 when absent), and the number of b's
# callees (calls.long-ska) that sccs.cache lacks (what the sub loop would walk first).
# Also, in the %full driver, before the poke's own +scc-of, [%top f in-sccs].
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__))
if sys.argv[1] == '--sum':
    import re
    txt = open(sys.argv[2]).read()
    sco = re.findall(r'\[%sco ([0-9.]+) (\S+?) ([0-9.]+) ([0-9.]+)\]', txt.replace('\n', ' '))
    top = re.findall(r'\[%top ([0-9.]+) (\S+?)\]', txt.replace('\n', ' '))
    h = len(sco) // 2
    if h and sco[:h] == sco[h:]: sco = sco[:h]
    h = len(top) // 2
    if h and top[:h] == top[h:]: top = top[:h]
    hit = sum(1 for s in sco if s[1] in ('%.y', '0', '&'))
    print('misses in nary.cache (+scc-of from +callee-compiled):', len(sco))
    print('  of them, b in sccs.cache (HIT path):', hit)
    print('  SCC sizes on the HIT path:', sorted(set(s[2] for s in sco if s[1] in ('%.y', '0', '&'))))
    print('  callees outside sccs.cache:', sorted(set(s[3] for s in sco)))
    print('top +scc-of of the poke:', len(top), 'in sccs before:', sorted(set(t[1] for t in top)))
    sys.exit(0)
out = sys.argv[1]
subprocess.check_call([sys.executable, os.path.join(D, 'calleecomp.py'), out])
lib = open(os.path.join(out, 'lib.hoon')).read().split('\n')
a = '    =^  new-scc=(set bell)  sccs.cache.gen'
k = [i for i, l in enumerate(lib) if l == a]
assert len(k) == 1
lib[k[0]:k[0]] = [
    '    ~&  ^-  *',
    '        :*  %sco  (mug b-callee)  (~(has by sccs.cache.gen) b-callee)',
    '            ~(wyt in (~(gut by sccs.cache.gen) b-callee ~))',
    '            %-  lent  %+  skip  ~(tap in (~(gut by calls.long-ska) b-callee ~))',
    '            |=(c=bell (~(has by sccs.cache.gen) c))',
    '        ==',
]
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(lib))
ck = open(os.path.join(out, 'ck.hoon')).read().split('\n')
a = '=^  scc=(set bell)  sccs.cache.state'
k = [i for i, l in enumerate(ck) if l == a]
assert len(k) == 1
ck[k[0]:k[0]] = ['~&  ^-(* [%top (mug func) (~(has by sccs.cache.state) func)])']
open(os.path.join(out, 'ck.hoon'), 'w').write('\n'.join(ck))
