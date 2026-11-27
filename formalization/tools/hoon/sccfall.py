#!/usr/bin/env python3
# usage: sccfall.py OUTDIR CASEFILE      then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 1700 > out.txt
#   tools/hoon/sccfall.py --sum out.txt
# The search for a fall of an entry from a split back to `this` (README Gaps 21.8.5): the
# instrumented library of sccloop.py, plus, at every %must compile of a member b, the PROBE of
# its compile as a function of the view of its own entry: for each shape N of the list PROBES
# (at the sample, cape [[| |] [| |]]), the need-new that +run-shape, +laze-collapse and
# +bake-need-ord give with b's entry of map-local set to [none [N none]] (the rest of the views,
# top and sure.cache as they are).  CASEFILE: one case per paragraph, a name line then the arm
# lines (`++  p  |=(s=[[a=* b=*] [c=* d=*]] ...)`), p first.
# --sum prints, per SCC: sweeps, each member's need-new / entry per %must compile, the probe
# table F of the first %must compile, and the orbit e' = msg (F e) e from the first entry under
# F of that table (`cycle` when a state recurs with a change between, `fixed` when it settles).
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, D)
sys.path.insert(0, os.path.join(D, '..', 'msgord'))
from sccloop_parse import parse, cord, lst
import msgpy
from msgpy import N, T, P, B

C4 = ('c', ('c', 'n', 'n'), ('c', 'n', 'n'))
VERBOSE = bool(os.environ.get('SCCFALL_VERBOSE'))
BTT = B(T, T); TT = P(T, T)
HALVES = [N, T, TT, BTT, P(T, N), P(N, T), B(T, N), B(N, T)]
# every shape within the cape [[| |] [| |]]: none, this, and a pair or %both of two halves
PROBES = [N, T] + [k(h, t) for k in (P, B) for h in HALVES for t in HALVES
                   if not (k is P and h == N and t == N)]


def tonoun(n):
    """A parsed need-ordered noun as a msgpy shape."""
    h, t = n
    if isinstance(h, tuple):
        return P(tonoun(h), tonoun(t))
    c = cord(h)
    if c == 'none': return N
    if c == 'this': return T
    if c == 'both': return B(tonoun(t[0]), tonoun(t[1]))
    raise Exception(c)


def samp(x):
    """The sample part of a need of the gate core [battery [sample context]]."""
    if x in (N, T): return x
    tl = x[2]
    if tl in (N, T): return tl
    return tl[1]


def lines(path):
    raw = open(path).read().split('\n')
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
    if ls[:h] == ls[h:]:
        ls = ls[:h]
    return ls


def summ(path):
    case = None; groups = {}; keys = []
    for l in lines(path):
        e = parse(l)
        tag = cord(e[0])
        if tag == 'case':
            case = cord(e[1]); continue
        k = (case, e[1][0])
        if k not in groups:
            groups[k] = []; keys.append(k)
        groups[k].append((tag, e[1][1]))
    stats = {'cycle': 0, 'fall': 0}
    for k in keys:
        g = groups[k]
        scc = [x for t, x in g if t == 'scc']
        if not scc or scc[0][0] == 0:
            continue
        mem = lst(scc[0][1][0])
        swps = [x for t, x in g if t == 'swp']
        fin = [x for t, x in g if t == 'fin']
        print('%-6s |scc| %d  sweeps %d  final %s' % (k[0], len(mem), len(swps),
                                                     'yes' if fin else 'NO'))
        ents = {}; nns = {}; prb = {}
        for t, x in g:
            if t == 'out':
                b, (mode, (kp, rest)) = x
                if cord(mode) != 'must':
                    continue
                nn = samp(tonoun(rest[0]))
                np = samp(tonoun(rest[1][1][1][1][1][1][1]))
                ents.setdefault(b, []).append(np); nns.setdefault(b, []).append(nn)
            if t == 'prb':
                b, tab = x
                if b not in prb:
                    prb[b] = {tonoun(n): samp(tonoun(f)) for n, f in lst(tab)}
        for b in ents:
            es = ents[b]
            fell = any(es[i] not in (N, T) and es[i + 1] == T for i in range(len(es) - 1))
            if fell: stats['fall'] += 1
            print('   %s  need-new %s' % ('FALL' if fell else '    ',
                                         ' ; '.join(msgpy.show(x) for x in nns[b])))
            print('         entry    %s' % ' -> '.join(msgpy.show(x) for x in es))
            if b in prb and len(mem) == 1:
                F = prb[b]
                outs = {}
                for a, c in F.items():
                    outs.setdefault(c, []).append(a)
                print('         F: %d outputs: %s' % (len(outs), '  '.join(
                    '%s (%d)' % (msgpy.show(c), len(v)) for c, v in outs.items())))
                if VERBOSE:
                    print('         F: %s' % '  '.join('%s>%s' % (msgpy.show(a), msgpy.show(c))
                                                     for a, c in F.items()))

                def orbit(e):
                    orb = [e]; res = 'off-table'
                    for _ in range(12):
                        if e not in F: break
                        e2 = msgpy.msg(F[e], e, C4)
                        if e2 == e: res = 'fixed'; break
                        if e2 in orb: res = 'CYCLE'; orb.append(e2); break
                        orb.append(e2); e = e2
                    return res, orb
                res, orb = orbit(es[0])
                if res == 'CYCLE': stats['cycle'] += 1
                print('         orbit %s: %s' % (res, ' -> '.join(msgpy.show(x) for x in orb)))
                # from every probed start: a cycle, or a fall split -> this
                cyc = []; fal = []
                for e in F:
                    r, o = orbit(e)
                    if r == 'CYCLE': cyc.append(o)
                    if any(o[i] not in (N, T) and o[i + 1] == T for i in range(len(o) - 1)):
                        fal.append(o)
                if cyc or fal:
                    stats['anystart'] = stats.get('anystart', 0) + 1
                    for o in (cyc + fal)[:3]:
                        print('         ANY-START %s' % ' -> '.join(msgpy.show(x) for x in o))
                # `Ranked` of lemmas/Ska/SccLoopTotal.lean on this table (the entry is the
                # view of itself): the steps p -> msg (F p) p, p /= msg (F p) p, over the probes
                # whose step stays in the table, have no cycle; H = the longest chain.  Also the
                # stronger form for a member that does not read its own entry: the steps
                # p -> msg n p for every output n (`img`)
                h = ranked(F)
                hi = ranked({p: list(outs) for p in F}, img=True)
                stats['tables'] = stats.get('tables', 0) + 1
                if h is None:
                    stats['unranked'] = stats.get('unranked', 0) + 1
                    print('         NOT RANKED')
                else:
                    stats['H'] = max(stats.get('H', 0), h)
                    if hi is None: stats['unimg'] = stats.get('unimg', 0) + 1
                    print('         ranked, longest chain %d; over every output: %s' % (
                        h, 'no (a cycle)' if hi is None else 'yes, %d' % hi))
    print('falls %d, probe cycles %d, tables with a cycle or fall from some start %d' % (
        stats['fall'], stats['cycle'], stats.get('anystart', 0)))
    print('tables %d, not ranked %d, longest chain %d, not ranked over every output %d' % (
        stats.get('tables', 0), stats.get('unranked', 0), stats.get('H', 0),
        stats.get('unimg', 0)))


def ranked(F, img=False):
    """None when the graph p -> msg n p (n = F p, or with img every n of F p; over the probes
    and, with img, their closure) has a cycle of length > 1, else its longest path."""
    starts = list(F)
    outs = F[starts[0]] if img else None
    seen = set(starts); todo = list(starts); succ = {}
    while todo:
        p = todo.pop()
        s = set()
        ns = outs if img else ([F[p]] if p in F else [])
        for n in ns:
            q = msgpy.msg(n, p, C4)
            if q != p:
                s.add(q)
                if img and q not in seen:
                    seen.add(q); todo.append(q)
        succ[p] = s
    for p in list(seen):
        for q in succ[p]:
            succ.setdefault(q, set())
    memo = {}; onst = set()

    def depth(p):
        if p in memo: return memo[p]
        if p in onst: raise ValueError
        onst.add(p)
        d = 1 + max([depth(q) for q in succ[p]], default=-1)
        onst.discard(p); memo[p] = d
        return d
    try:
        return max(depth(p) for p in succ)
    except ValueError:
        return None


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


def readcases(path):
    cases = []; cur = None
    for l in open(path).read().split('\n'):
        if not l.strip():
            cur = None; continue
        if l.startswith('#'):
            continue
        if cur is None:
            cur = (l.strip(), []); cases.append(cur)
        else:
            cur[1].append(l.strip())
    return cases


LF = ['a.s', 'b.s', 'c.s', 'd.s']
HV = ['-.s', '+.s'] + ['[%s %s]' % (x, y) for x in LF for y in LF if x != y]
TESTS = ['.=(s 0)', '.=(-.s 0)', '.=(+.s 0)', '.=(a.s 0)', '.=(a.s c.s)', '.=(-.s +.s)']
LEAVES = LF + ['s', '-.s', '+.s', '[s -.s]', '[-.s +.s a.s b.s c.s d.s]', '0', '-.a.s', '+.c.s']


def gbody(rng, mem, depth):
    """A body on the sample s=[[a b] [c d]]: forks on tests of the whole and the parts, calls of
    the members on samples of the same cape (halves -.s, +.s or pairs of leaves)."""
    k = rng.random()
    if depth == 0 or k < 0.3:
        if rng.random() < 0.4:
            return rng.choice(LEAVES)
        return '(%s [%s %s])' % (rng.choice(mem), rng.choice(HV), rng.choice(HV))
    if k < 0.85:
        if rng.random() < 0.25:
            t = '.=(0 (%s [%s %s]))' % (rng.choice(mem), rng.choice(HV), rng.choice(HV))
        else:
            t = rng.choice(TESTS)
        return '?:(%s %s %s)' % (t, gbody(rng, mem, depth - 1), gbody(rng, mem, depth - 1))
    return '[%s %s]' % (gbody(rng, mem, depth - 1), gbody(rng, mem, depth - 1))


def gen(seed, n, sizes=(1,), depth=3):
    import random
    rng = random.Random(seed)
    out = []
    for i in range(n):
        mem = ['p', 'q'][:rng.choice(sizes)]
        arms = []
        for m in mem:
            b = gbody(rng, mem, depth)
            while '(' not in b:
                b = gbody(rng, mem, depth)
            arms.append('++  %s  |=(s=[[a=* b=*] [c=* d=*]] %s)' % (m, b))
        out.append('r%d-%d\n%s\n' % (seed, i, '\n'.join(arms)))
    return '\n'.join(out)


if __name__ == '__main__':
    if sys.argv[1] == '--sum':
        summ(sys.argv[2]); sys.exit(0)
    if sys.argv[1] == '--gen':
        sys.stdout.write(gen(int(sys.argv[2]), int(sys.argv[3]),
                             tuple(int(x) for x in (sys.argv[4] if len(sys.argv) > 4 else '1').split(','))))
        sys.exit(0)
    out = sys.argv[1]
    subprocess.check_call([sys.executable, os.path.join(D, 'sccloop.py'), out])
    lib = open(os.path.join(out, 'lib.hoon')).read().split('\n')
    a = lib.index('++  compile-scc-in')
    anchor = '    =.  cache.gen  cache'
    k = [i for i in range(a, a + 400) if lib[i] == anchor]
    assert len(k) == 1
    probe = [
        '    ~&  ^-  *',
        '        ?.  ?=(%must mode)  ~',
        '        :*  %prb  (mug scc)  (mug b)',
        '            %+  turn  `(list need-ordered)`:~(' + ' '.join(msgpy.hoon(x) for x in PROBES) + ')',
        '            |=  n=need-ordered',
        '            =/  ml  (~(put by map-local) b `straight`[[[%none ~] [n [%none ~]]] 0 ~])',
        '            =/  cp  (^comp scc long-ska jets-hot ml top b)',
        '            =/  l=laze  -:(~(run-shape cp gen) nomm [%done ~] ~)',
        '            [n (bake-need-ord (laze-collapse l cape.less.b) less.b)]',
        '        ==',
    ]
    lib[k[0] + 1:k[0] + 1] = probe
    open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(lib))
    cases = readcases(sys.argv[2])
    open(os.path.join(out, 'ck.hoon'), 'w').write(driver(cases))
