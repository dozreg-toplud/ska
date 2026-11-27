#!/usr/bin/env python3
# usage: splitmax-sum.py OUT.txt [--show N] [--quiet] [--codes OUT.json]
# Track S (README Gaps 30): the summary of a run of a copy of splitmax.py --trace.  Per SCC
# through the loop and over all: the sweeps, the joins of the loop (%sm records of mode %must),
# how many reach the cut line of +msg-need-ord (some call of the recursion has one side
# %this/%none, the other a split, and the cape a cell), how many it FIRES in (the join differs
# from the uncut join; computed with msgpy.py, which is checked against the printed result), the
# sweep it fires in (first sweep, last sweep, between), the kind of the stored entry it fires on
# (a split or %this/%none), and every SHRINK of a stored entry (fewer registers, or a split
# becoming %this).  --show N prints the first N firing or shrinking joins in full.
import os, re, sys
from functools import lru_cache
D = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(D, '..', 'msgord'))
sys.setrecursionlimit(100000)
import msgpy  # noqa: E402

NONE, THIS, BOTH = 1701736302, 1936287860, 1752461154
MAY, MUST, DONE = 7954797, 1953723757, 1701736292


def cord(n):
    s = b''
    while n:
        s += bytes([n & 255]); n >>= 8
    return s.decode('latin1')


def parse(t):
    toks = re.findall(r'\[|\]|[0-9.]+|~', t)
    pos = [0]

    def one():
        x = toks[pos[0]]; pos[0] += 1
        if x == '[':
            xs = []
            while toks[pos[0]] != ']':
                xs.append(one())
            pos[0] += 1
            r = xs[-1]
            for y in reversed(xs[:-1]):
                r = (y, r)
            return r
        if x == '~':
            return 0
        return int(x.replace('.', ''))
    return one()


def records(path):
    ls = []; cur = None; dep = 0
    for l in open(path, errors='replace'):
        l = l.rstrip('\n')
        if cur is None:
            if not l.startswith('['):
                continue
            cur = ''
        cur += ' ' + l.strip()
        dep += l.count('[') - l.count(']')
        if dep == 0:
            ls.append(cur.strip()); cur = None
    h = len(ls) // 2
    if h and ls[:h] == ls[h:]:
        ls = ls[:h]
    for l in ls:
        try:
            yield parse(l)
        except (IndexError, ValueError):
            pass


def need(n):
    h, t = n
    if h == NONE: return msgpy.N
    if h == THIS: return msgpy.T
    if h == BOTH: return msgpy.B(need(t[0]), need(t[1]))
    return msgpy.P(need(h), need(t))


def cape(c):
    if isinstance(c, tuple): return ('c', cape(c[0]), cape(c[1]))
    return 'y' if c == 0 else 'n'


def ch(c): return c[1] if isinstance(c, tuple) else c
def ct(c): return c[2] if isinstance(c, tuple) else c


def leaf(x): return x[0] in 'TN'


@lru_cache(maxsize=None)
def reach(a, b, c):
    """Does the recursion of msg a b c reach the cut line?"""
    if a == b: return False
    if leaf(a) and leaf(b): return False
    if leaf(a) or leaf(b):
        if not isinstance(c, tuple): return False
        s, d = (a, b) if leaf(a) else (b, a)
        return True
    return reach(a[1], b[1], ch(c)) or reach(a[2], b[2], ct(c))


def msg(a, b, c, cut):
    msgpy.SPLIT = 6 if cut else 10 ** 9
    msgpy.mnone.cache_clear(); msgpy.msg.cache_clear()
    return msgpy.msg(a, b, c)


def regs(n): return msgpy.regs(10 ** 9, n, 0)


def show(x): return msgpy.show(x)


def main():
    path = sys.argv[1]
    nshow = int(sys.argv[sys.argv.index('--show') + 1]) if '--show' in sys.argv else 0
    quiet = '--quiet' in sys.argv
    sccs = {}      # S -> dict(size, sweeps, cape per bell, joins list)
    cur = {}       # S -> current sweep counter, or 'x' for a late cut sweep
    T = dict(shrinkcut=0, joins=0, reach=0, fire=0, shrink=0, grow=0, eq=0, mismatch=0, done=0, donediff=0)
    fires = []; shrinks = []; codes = {}
    for e in records(path):
        if not isinstance(e, tuple): continue
        tag = cord(e[0]) if isinstance(e[0], int) else ''
        if tag == 'sc':
            S, n = e[1]
            sccs[S] = dict(size=n, sweeps=0, cape={}, ent={}, nj=0, nfire=0, nreach=0, cuts=0)
        elif tag == 'fz':
            S, z = e[1]
            codes.setdefault(S, []).append(z)
        elif tag == 'sw':
            S, k = e[1]
            if S in sccs: sccs[S]['sweeps'] = max(sccs[S]['sweeps'], k + 1); cur[S] = k
        elif tag == 'sx':
            S, k = e[1]
            if S in sccs: sccs[S]['cuts'] += 1; cur[S] = 'x'
        elif tag == 's0':
            S, (b, (mode, (nn, c))) = e[1]
            if mode != MUST or S not in sccs: continue
            if isinstance(nn, int):          # --small: registers and mug
                sccs[S]['ent'][b] = [c]; continue
            sccs[S]['cape'][b] = cape(c)
            sccs[S]['ent'][b] = [need(nn)]
        elif tag == 'sn':
            S, (b, (mode, (rp, (rnn, (rnp, (runc, (fired, (rch, (mnp, (mpv, full)))))))))) = e[1]
            if S not in sccs: continue
            sc = sccs[S]
            if mode == DONE:
                T['done'] += 1
                if mnp != mpv: T['donediff'] += 1
                continue
            if mode != MUST: continue
            fired = fired == 0; rch = rch == 0
            T['joins'] += 1; sc['nj'] += 1
            T['reach'] += rch; sc['nreach'] += rch
            rec = dict(S=S, b=b, sweep=cur.get(S))
            if full != 0:
                nn, (prev, (np, c)) = full
                nn, prev, np, c = need(nn), need(prev), need(np), cape(c)
                real = msg(nn, prev, c, True); unc = msg(nn, prev, c, False)
                if cur.get(S) != 'x' and real != np and unc != np: T['mismatch'] += 1
                rec.update(nn=nn, prev=prev, np=np, cape=c, real=real, unc=unc)
            if fired:
                T['fire'] += 1; sc['nfire'] += 1; fires.append(rec)
            if mnp == mpv: T['eq'] += 1
            elif full != 0 and (rnp < rp or (not leaf(rec['prev']) and leaf(rec['np']))):
                T['shrink'] += 1; shrinks.append(rec)
                if fired: T['shrinkcut'] += 1
            else:
                T['grow'] += 1
            sc['ent'].setdefault(b, []).append(mnp)
        elif tag == 'sm':
            S, (b, (mode, (nn, (prev, np)))) = e[1]
            if S not in sccs: continue
            sc = sccs[S]; c = sc['cape'].get(b)
            nn, prev, np = need(nn), need(prev), need(np)
            if mode == DONE:
                T['done'] += 1
                if np != prev: T['donediff'] += 1
                continue
            if mode != MUST: continue
            T['joins'] += 1; sc['nj'] += 1
            r = reach(nn, prev, c)
            real = msg(nn, prev, c, True); unc = msg(nn, prev, c, False)
            if cur.get(S) != 'x' and real != np and unc != np:
                T['mismatch'] += 1
            fired = real != unc
            T['reach'] += r; sc['nreach'] += r
            k = cur.get(S)
            rec = dict(S=S, b=b, sweep=k, nn=nn, prev=prev, np=np, cape=c, real=real, unc=unc)
            if fired:
                T['fire'] += 1; sc['nfire'] += 1; fires.append(rec)
            rp, rn = regs(prev), regs(np)
            if np == prev: T['eq'] += 1
            elif rn < rp or (not leaf(prev) and leaf(np)):
                T['shrink'] += 1; shrinks.append(rec)
                if fired: T['shrinkcut'] += 1
            else:
                T['grow'] += 1
            sc['ent'].setdefault(b, []).append(np)
    # the sweep a firing join is in: first (0), last (sweeps-1), or between
    def where(r):
        k = r['sweep']; n = sccs[r['S']]['sweeps']
        if k == 'x': return 'cut-sweep'
        return 'first' if k == 0 else ('last' if k == n - 1 else 'middle')
    hist = {}
    for s in sccs.values():
        hist[s['sweeps']] = hist.get(s['sweeps'], 0) + 1
    sizes = {}
    for s in sccs.values():
        sizes[s['size']] = sizes.get(s['size'], 0) + 1
    print('SCCs through the loop: %d (by size %s)' % (len(sccs), dict(sorted(sizes.items()))))
    print('sweeps per SCC: %s; most %d' % (dict(sorted(hist.items())), max(hist) if hist else 0))
    print('late cut sweeps: %d' % sum(s['cuts'] for s in sccs.values()))
    print('joins (%%must, with an entry): %d; reach the cut line: %d; cut fires: %d' %
          (T['joins'], T['reach'], T['fire']))
    print('entry: same %d, grows %d, SHRINKS %d (%d of them where the cut fires); printed result unlike msgpy: %d' %
          (T['eq'], T['grow'], T['shrink'], T['shrinkcut'], T['mismatch']))
    print('final (%%done) joins: %d, need-pessimized unlike the entry: %d' % (T['done'], T['donediff']))
    if fires:
        w = {}
        for r in fires:
            kk = (where(r), 'split' if 'prev' in r and not leaf(r['prev']) else 'this/none')
            w[kk] = w.get(kk, 0) + 1
        print('fires by sweep and entry kind:', w)
    if shrinks:
        w = {}
        for r in shrinks:
            w[where(r)] = w.get(where(r), 0) + 1
        print('shrinks by sweep:', w)
    # the stored sequence of each member: does any return to an earlier entry?
    back = 0
    for s in sccs.values():
        for b, seq in s['ent'].items():
            for i in range(2, len(seq)):
                if seq[i] != seq[i - 1] and seq[i] in seq[:i - 1]:
                    back += 1; break
    print('members whose entry returns to an earlier one: %d' % back)
    if '--codes' in sys.argv:
        import json
        json.dump({str(k): v for k, v in codes.items()}, open(sys.argv[sys.argv.index('--codes') + 1], 'w'))
    print('final passes (code mugs): %d over %d SCCs' % (sum(len(v) for v in codes.values()), len(codes)))
    if not quiet:
        big = sorted(sccs.items(), key=lambda kv: -kv[1]['sweeps'])[:5]
        for S, s in big:
            print('  SCC %d: size %d, sweeps %d, joins %d, reach %d, fires %d' %
                  (S, s['size'], s['sweeps'], s['nj'], s['nreach'], s['nfire']))
    for r in [x for x in fires + shrinks if 'nn' in x][:nshow]:
        print('--- SCC %d bell %d sweep %s (%s)' % (r['S'], r['b'], r['sweep'], where(r)))
        cs = show(r['cape'])
        print('  cape %s' % (cs if len(cs) < 160 else cs[:160] + '...'))
        print('  need-new %s (%d regs)' % (show(r['nn']), regs(r['nn'])))
        print('  prev     %s (%d regs)' % (show(r['prev']), regs(r['prev'])))
        print('  np       %s (%d regs); uncut %s (%d regs)' %
              (show(r['np']), regs(r['np']), show(r['unc']), regs(r['unc'])))


main()
