#!/usr/bin/env python3
# usage: splitmax-cores.py OUT.hoon SEED N [DEEP] [--targeted]
# Track S (README Gaps 30): a driver of N generated SCCs (seed SEED) built to make +split-max act
# in the sweep loop of +compile-scc-in, in the form of sccstress.py's driver (the direct compile
# call: +ska-poke, +scc-of, +compiled-mono).  One to three gates whose sample is the cell of eight
# leaves [[[a b] [c d]] [[e f] [g h]]] (DEEP 1, the default) or of four [[a b] [c d]] (DEEP 0),
# so that the capes are cells over seven or three inner nodes and a split of the sample is over
# six registers: members that pass the sample whole (need %this) beside members that take it
# apart on every path, calls on rebuilt, permuted, deeper and shallower samples, conses of calls,
# forks on leaves and on a call's product.  Run with a copy of splitmax.py --trace:
#   RUNHOON_LIB=LIB runhoon.sh OUT.hoon 1200 > out.txt; splitmax-sum.py out.txt
# Every case prints [%case nam] first, so a run that does not end names its case.
import os, random, sys
D = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, D)
_t = open(os.path.join(D, 'sccstress.py')).read()   # its driver only (importing runs its main)
exec(_t[_t.index('def driver(cases):'):_t.index("if sys.argv[1] == '--sum':")])

out, seed, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
deep = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4].isdigit() else 1
# the unknown leaves, and at every other leaf the same known gate G (=>(~ |=(x=* x))), which the
# members call, so that the bells know the cell structure down to it: the capes are cells
if deep:
    LEAF = ['a.s', 'c.s', 'e.s', 'g.s']
    GATE = ['b.s', 'd.s', 'f.s', 'h.s']
    MID = ['-<.s', '->.s', '+<.s', '+>.s']
    HALF = ['-.s', '+.s']
    SAM = 's=[[[a=* b=$-(* *)] [c=* d=$-(* *)]] [[e=* f=$-(* *)] [g=* h=$-(* *)]]]'
    SAMF = '[[[[0 48] [1 g]] [[0 50] [1 g]]] [[[0 52] [1 g]] [[0 54] [1 g]]]]'
else:
    LEAF = ['a.s', 'c.s']
    GATE = ['b.s', 'd.s']
    MID = []
    HALF = ['-.s', '+.s']
    SAM = 's=[[a=* b=$-(* *)] [c=* d=$-(* *)]]'
    SAMF = '[[[0 12] [1 g]] [[0 14] [1 g]]]'
ALL = LEAF + MID + HALF + ['s']
def every(rng):
    """A noun that reads many parts on every path: leaves, gate calls, the halves, the whole."""
    xs = rng.sample(ALL, rng.randint(2, len(ALL)))
    xs += ['(%s %s)' % (rng.choice(GATE), rng.choice(LEAF)) for _ in range(rng.randint(0, 2))]
    rng.shuffle(xs)
    return '[%s]' % ' '.join(xs) if len(xs) > 1 else xs[0]


def arg(rng):
    """A sample for a call: the same gates at the gate leaves, anything at the unknown ones,
    or parts of the sample of the right shape (halves, quarters, the whole)."""
    if rng.random() < 0.15:
        return 's'
    sh = {2: HALF, 1: MID} if deep else {1: HALF}

    def piece(lv):
        if lv == 0:
            return '[%s %s]' % (rng.choice(LEAF + MID + HALF + ['s', '0']), rng.choice(GATE))
        if rng.random() < 0.3:
            return rng.choice(sh[lv + 1] if (lv + 1) in sh else HALF)
        return '[%s %s]' % (piece(lv - 1), piece(lv - 1))
    top = 1 if deep else 0
    return '[%s %s]' % (piece(top), piece(top))


def call(rng, mem):
    f = rng.choice(mem)
    return '(%s %s)' % (f, arg(rng))


def body(rng, mem, depth, used=()):
    k = rng.random()
    free = [x for x in LEAF if x not in used]
    if depth == 0 or k < 0.2:
        r = rng.random()
        if r < 0.3:
            return rng.choice(['s', '-.s', '+.s'])
        if r < 0.5:
            return every(rng)
        return call(rng, mem)
    if k < 0.55 and free:
        x = rng.choice(free)
        u = used + (x,)
        return '?@(%s %s %s)' % (x, body(rng, mem, depth - 1, u), body(rng, mem, depth - 1, u))
    if k < 0.65:
        return '?:(.=(0 %s) %s %s)' % (call(rng, mem), body(rng, mem, depth - 1, used),
                                       body(rng, mem, depth - 1, used))
    if k < 0.8:
        return '=/(t %s ?@(t s %s))' % (call(rng, mem), body(rng, mem, depth - 1, used))
    return '[%s %s]' % (body(rng, mem, depth - 1, used), body(rng, mem, depth - 1, used))


def gen(rng, i):
    m = rng.choice([1, 2, 2, 3, 3])
    mem = ['p', 'q', 'r'][:m]
    arms = []
    for x in mem:
        b = body(rng, mem, 3)
        while '(' not in b:
            b = body(rng, mem, 3)
        arms.append('++  %s  |=(%s %s)' % (x, SAM, b))
    return 's%d-%d' % (seed, i), arms


# hand-made: one member passes the sample whole, the other takes it apart on every path; a
# member whose need follows another's through a cons or an edit
FIXED = [
    ('whole-deep', ['++  p  |=(%s ?@(a.s s (q s)))' % SAM,
                    '++  q  |=(%s ?@(c.s [a.s (b.s c.s) -.s +.s %s] (p [+.s -.s])))' % (SAM, ' '.join(ALL))]),
    ('grow-drop', ['++  p  |=(%s ?@(a.s (q s) ?@(c.s s (p [+.s -.s]))))' % SAM,
                   '++  q  |=(%s ?@(c.s [%s (d.s a.s)] (p [-.s -.s])))' % (SAM, ' '.join(ALL))]),
    ('cons', ['++  p  |=(%s ?@(a.s [s (q s)] [(q [+.s -.s]) a.s]))' % SAM,
              '++  q  |=(%s ?@(c.s [%s] (p s)))' % (SAM, ' '.join(ALL))]),
    ('edit', ['++  p  |=(%s ?@(a.s s (q s(- +.s))))' % SAM,
              '++  q  |=(%s ?@(c.s [%s] (p s(+ -.s))))' % (SAM, ' '.join(ALL))]),
]


def targeted(rng, i):
    """The pattern of the cuts on real code: a member's first compile reads the %may need (top)
    of a callee not compiled yet, which is a big split, where the callee's collapsed need is
    %this (the fork cut of +laze-collapse: one branch the whole, the other a big split); the
    member passes its sample on to that callee outside a fork, so its own need follows."""
    ARG = ['s', '[+.s -.s]', '[-.s -.s]', '[+.s +.s]'] + (['[[+<.s -<.s] +.s]', '[-.s [->.s +<.s]]'] if deep else [])

    def big():
        xs = rng.sample(ALL, rng.randint(min(4, len(ALL)), len(ALL)))
        xs += ['(%s %s)' % (rng.choice(GATE), rng.choice(LEAF)) for _ in range(rng.randint(0, 1))]
        return ' '.join(xs)
    x = rng.choice(LEAF + MID + HALF)
    tp = rng.choice(['[%s (q %s)]', '(q %s)', '=/(t (q %s) [t %s])', '?:(.=(0 (q %s)) s %s)',
                     '[(q %s) (q %s)]'])
    if tp == '[%s (q %s)]':
        pb = tp % (x, rng.choice(ARG))
    elif tp == '(q %s)':
        pb = tp % rng.choice(ARG)
    elif tp == '[(q %s) (q %s)]':
        pb = tp % (rng.choice(ARG), rng.choice(ARG))
    else:
        pb = tp % (rng.choice(ARG), x)
    l1, l2 = rng.sample(LEAF, 2)
    tq = rng.choice(['?@(%s s [(p %s) %s])', '?@(%s [(p %s) %s] s)', '?@(%s s ?@(%s [(p %s) %s] [%s]))',
                     '?@(%s -.s [(p %s) %s])'])
    if tq.count('%s') == 3:
        qb = tq % (l1, rng.choice(ARG), big())
    else:
        qb = tq % (l1, l2, rng.choice(ARG), big(), big())
    arms = ['++  p  |=(%s %s)' % (SAM, pb), '++  q  |=(%s %s)' % (SAM, qb)]
    if rng.random() < 0.3:      # a third member between them
        arms[0] = arms[0].replace('(q ', '(r ')
        arms.append('++  r  |=(%s %s)' % (SAM, rng.choice(['[%s (q s)]' % rng.choice(LEAF), '(q [+.s -.s])', '[(q s) %s]' % rng.choice(MID + HALF)])))
    return 't%d-%d' % (seed, i), arms


rng = random.Random(seed)
mk = targeted if '--targeted' in sys.argv else gen
cases = FIXED + [mk(rng, i) for i in range(n)]
# every product cast to * (a recursive product type is a rest-loop for ?@ on a call's product)
cases = [(nm, [a.replace('|=(%s ' % sm, '|=(%s ^-(* ' % sm, 1) + ')' for a in arms])
         for nm, arms in cases for sm in [SAM]]
drv = driver(cases).replace('[9 2 [10 [6 [[0 12] [0 13]] [[0 14] [0 15]]] [0 2]]]',
                            '[9 2 [10 [6 %s] [0 2]]]' % SAMF)
drv = drv.replace('=/  fol=*', '=/  g=*  =>(~ |=(x=* x))\n=/  fol=*')
open(out, 'w').write(drv)
print(out, len(cases))
