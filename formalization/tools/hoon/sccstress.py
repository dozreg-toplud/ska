#!/usr/bin/env python3
# usage: sccstress.py OUTDIR [SEED] [N]    then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 1700 > out.txt
#   tools/hoon/sccstress.py --sum out.txt
# Stress cases for the sweep loop of +compile-scc-in (README Gaps 21.8): the instrumented library
# of sccloop.py, and N generated SCCs (seed SEED) of one to three gates whose sample is the cell
# [[a b] [c d]], so that the bells' capes are cells at the sample: members that read the whole
# sample and its parts (splits up to seven registers, over split-max), call each other on
# rebuilt or permuted samples, and fork on the parts.  Also the fixed cases of FIXED.
# --sum prints, per SCC: the case, its size, the sweeps, the most %must compiles of a member,
# whether keep was set, and each member's entries along the loop.
import os, random, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, D)
from sccloop_parse import parse, cord, lst, show

PARTS = ['a.s', 'b.s', 'c.s', 'd.s']
ARGS = PARTS + ['0', 's', '-.s', '+.s']
LEAVES = PARTS + ['s', '-.s', '+.s', '0', '[a.s s]', '[-.s +.s]', '[s -.s +.s]']


def body(rng, mem, depth, used=()):
    """A gate body; `used`: the parts already tested by an enclosing ?@ (no second test, which
    would be mint-vain)."""
    k = rng.random()
    free = [x for x in PARTS if x not in used]
    if depth == 0 or k < 0.25:
        if rng.random() < 0.5:
            return rng.choice(LEAVES)
        return call(rng, mem)
    if k < 0.6 and free:
        x = rng.choice(free)
        u = used + (x,)
        return '?@(%s %s %s)' % (x, body(rng, mem, depth - 1, u), body(rng, mem, depth - 1, u))
    if k < 0.8:
        return '?:(.=(%s %s) %s %s)' % (rng.choice(PARTS), rng.choice(PARTS),
                                       body(rng, mem, depth - 1, used),
                                       body(rng, mem, depth - 1, used))
    return '[%s %s]' % (body(rng, mem, depth - 1, used), body(rng, mem, depth - 1, used))


def call(rng, mem):
    f = rng.choice(mem)
    xs = [rng.choice(ARGS) for _ in range(4)]
    return '(%s [[%s %s] [%s %s]])' % (f, *xs)


def gen(rng, i):
    n = rng.choice([1, 1, 2, 2, 3])
    mem = ['p', 'q', 'r'][:n]
    arms = []
    for m in mem:
        b = body(rng, mem, 3)
        while '(' not in b:
            b = body(rng, mem, 3)
        arms.append('++  %s  |=(s=[[a=* b=*] [c=* d=*]] %s)' % (m, b))
    return 'g%d' % i, arms


FIXED = [
    # the whole sample in one branch, a split of seven registers through a self call in the other
    ('big', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s s (p [[s -.s] [+.s [a.s b.s c.s d.s]]])))']),
    # swaps that move the halves around
    ('swp', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s [s -.s +.s] (p [[b.s a.s] [d.s c.s]])))']),
    # the whole in one branch and a call that reads parts in the other, two bells
    ('osc', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s s (q [[s s] [s s]])))',
             '++  q  |=(s=[[a=* b=*] [c=* d=*]] ?@(b.s [a.s b.s c.s d.s] (p [[-.s +.s] [a.s c.s]])))']),
    # towards the cycle of Comp.msgOrd_cycle: the whole sample in one branch, a call on the
    # swapped halves in another, every part and half in a third
    ('cyc1', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s s ?@(c.s (p [+.s -.s]) [-.s +.s a.s b.s c.s d.s])))']),
    ('cyc2', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s s (p [[c.s d.s] [-.s b.s]])))']),
    ('cyc3', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s s (q [+.s -.s])))',
              '++  q  |=(s=[[a=* b=*] [c=* d=*]] ?@(c.s [-.s a.s b.s] (p [+.s [c.s d.s]])))']),
    ('cyc4', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s s ?@(b.s (p [+.s -.s]) ?@(c.s [-.s a.s b.s] (p [[d.s c.s] -.s])))))']),
    ('cyc5', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(a.s +.s ?@(b.s (p [+.s -.s]) ?@(c.s s (p [[s a.s] [c.s s]])))))']),
    ('grow', ['++  p  |=(s=[[a=* b=*] [c=* d=*]] ?@(c.s -.s ?@(d.s (p [[s a.s] [b.s c.s]]) (p [[a.s s] [-.s +.s]]))))']),
]


def driver(cases):
    out = ['=/  cases=(list [nam=@tas gat=*])', '  :~']
    for nam, arms in cases:
        out.append('      :-  %%%s' % nam)
        out.append('        =>  ~  =<  p')
        out.append('        |%  ' + arms[0])
        for a in arms[1:]:
            out.append('            ' + a)
        out.append('        --')
    out.append('  ==')
    return '\n'.join(out) + r'''
|-  ^-  @
?~  cases  0
~&  ^-(* [%case nam.i.cases])
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=.  sure.cache.state  ~
=.  inl.cache.state  ~
=/  fol=*  [8 [1 gat.i.cases] [9 2 [10 [6 [[0 12] [0 13]] [[0 14] [0 15]]] [0 2]]]]
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol) fol)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
$(cases t.cases)
'''


if sys.argv[1] == '--sum':
    raw = open(sys.argv[2]).read().split('\n')
    ls = []; cur = None; dep = 0
    for l in raw:
        if cur is None:
            if not l.startswith('['):
                continue
            cur = ''
        cur += ' ' + l.strip()
        dep += l.count('[') - l.count(']')
        if dep == 0:
            ls.append(cur.strip()); cur = None
    h = len(ls) // 2
    if ls[:h] == ls[h:]:          # runhoon prints the sequence twice
        ls = ls[:h]
    case = None; groups = {}; keys = []
    for l in ls:
        e = parse(l)
        tag = cord(e[0])
        if tag == 'case':
            case = cord(e[1]); continue
        k = (case, e[1][0])
        if k not in groups:
            groups[k] = []; keys.append(k)
        groups[k].append((tag, e[1][1]))
    mx = (0, None); tot = 0
    for k in keys:
        g = groups[k]
        scc = [x for t, x in g if t == 'scc']
        if not scc or scc[0][0] == 0:
            continue
        mem = lst(scc[0][1][0])
        swps = [x for t, x in g if t == 'swp']
        outs = [x for t, x in g if t == 'out']
        musts = {}; keep = False; ents = {}
        for o in outs:
            b, (mode, (kp, rest)) = o
            if cord(mode) != 'must':
                continue
            musts[b] = musts.get(b, 0) + 1
            keep = keep or kp == 0
            np = rest[1][1][1][1][1][1][1]
            ents.setdefault(b, []).append(show(np))
        tot += 1
        fin = [x for t, x in g if t == 'fin']
        if len(swps) > mx[0]:
            mx = (len(swps), k[0])
        print('%-5s |scc| %d  sweeps %d  max-must %d  keep %s  final %s' % (
            k[0], len(mem), len(swps), max(musts.values() or [0]), keep, 'yes' if fin else 'NO'))
        for b in ents:
            print('      %s' % ' -> '.join(ents[b]))
    print('SCCs through the loop: %d, most sweeps: %d (%s)' % (tot, mx[0], mx[1]))
    sys.exit(0)

out = sys.argv[1]
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
n = int(sys.argv[3]) if len(sys.argv) > 3 else 50
subprocess.check_call([sys.executable, os.path.join(D, 'sccloop.py'), out])
rng = random.Random(seed)
cases = FIXED + [gen(rng, i) for i in range(n)]
open(os.path.join(out, 'ck.hoon'), 'w').write(driver(cases))
open(os.path.join(out, 'cases.txt'), 'w').write(
    '\n'.join('%s\n  %s' % (nm, '\n  '.join(a)) for nm, a in cases) + '\n')
