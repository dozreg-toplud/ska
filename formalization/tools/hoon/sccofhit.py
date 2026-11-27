#!/usr/bin/env python3
# usage: sccofhit.py OUTDIR      then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 900 > out.txt
#   tools/hoon/sccofhit.py --sum out.txt   (raw nouns: %sco is 7.299.955, %top 7.368.564)
# Which path of +scc-of a miss in nary.cache takes (README Gaps 19 (g), track K): the
# instrumented library and the 37 %full pokes of calleecomp.py, plus, in the miss branch of
# +callee-compiled, before its +scc-of, the print
#   [%sco b in-sccs scc-size callees-outside-sccs]
# with in-sccs: sccs.cache holds b (the HIT path of +scc-of: [u.s sccs], no sub loop, no
# +tarjan), scc-size: the size of the stored SCC (0 when absent), and the number of b's
# callees (calls.long-ska) that sccs.cache lacks (what the sub loop would walk first).
# Also, in the %full driver, before the poke's own +scc-of, [%top f in-sccs].
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__))
if sys.argv[1] == '--sum':
    import re
    from collections import Counter
    ls = re.findall(r'\[([0-9. ]+)\]', open(sys.argv[2]).read())
    ls = [[int(x.replace('.', '')) for x in l.split()] for l in ls]
    h = len(ls) // 2
    if h and ls[:h] == ls[h:]:
        ls = ls[:h]                      # the harness evaluates twice
    sco = [l for l in ls if l[0] == 7299955 and len(l) == 5]   # %sco
    top = [l for l in ls if l[0] == 7368564 and len(l) == 3]   # %top
    print('misses in nary.cache:', len(sco), ' in sccs.cache (0 = yes):', Counter(l[2] for l in sco))
    print('  SCC sizes:', Counter(l[3] for l in sco), ' callees outside sccs.cache:', Counter(l[4] for l in sco))
    print('poke +scc-of:', len(top), ' func in sccs.cache before (0 = yes):', Counter(l[2] for l in top))
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
