#!/usr/bin/env python3
# usage: calleecomp.py OUTDIR      then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 900 > out.txt
#   tools/hoon/calleecomp.py --sum out.txt          (the tables of README Gaps 19 (g); misM:
#                                                    misses in the mono run of +compile-unary,
#                                                    inlM: of those, callees +inlined inlined)
#   tools/hoon/calleecomp.py --trace out.txt CASE   (the trace of one case)
# Every call of +callee-need on the real compiler (README Gaps 19 (g), track K), over %full
# pokes run as the %full branch of +poke runs them (+ska-poke, +scc-of, +compiled-mono), with
# the caches emptied before each case.  The instrumented copy of the library prints, as raw
# nouns (bells as their mugs):
#   [%case nam]                 before each case
#   [%cmo f]                    +compiled-mono of f (the poke's own compile)
#   [%csi S n hit]              at the start of +compile-scc-in (n members, hit: every member
#                               already in nary.cache)
#   [%mem S b mode]             at the start of member
#   [%mob f] / [%moe f]         around the whole-subject run of +compile-unary (mono &)
#   [%cne c b kind inl]         +callee-need of b from the door of c: kind %hot (a hot jet),
#                               %loc / %top / %non (b in scc: map-local, top, neither), %hit
#                               (nary.cache holds b), %mis (+callee-compiled compiles b's SCC);
#                               inl: inl.cache holds b (its code was inlined somewhere, or b
#                               was a member before)
#   [%beg b] / [%end b n]       around the compile of a miss (n members of b's SCC)
#   [%inl b c]                  +inlined replaces, in the code of b, the call of c by c's code
import os, re, sys
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))


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


def events(path):
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
    if h and ls[:h] == ls[h:]:
        ls = ls[:h]
    return [parse(l) for l in ls]


def walk(evs):
    """Per case: the list of (event, nesting depth of +compile-scc-in runs opened by a miss,
    in-mono flag)."""
    out = {}; order = []
    case = None; dep = 0; mono = []
    for e in evs:
        tag = cord(e[0]); a = e[1]
        if tag == 'case':
            case = cord(a); out[case] = []; order.append(case); dep = 0; mono = []; continue
        if tag == 'beg':
            out[case].append(('beg', a, dep, bool(mono))); dep += 1; continue
        if tag == 'end':
            dep -= 1; out[case].append(('end', a, dep, bool(mono))); continue
        if tag == 'mob':
            mono.append(dep); out[case].append(('mob', a, dep, True)); continue
        if tag == 'moe':
            mono.pop(); out[case].append(('moe', a, dep, bool(mono))); continue
        out[case].append((tag, a, dep, bool(mono) and mono[-1] == dep))
    return order, out


if sys.argv[1] in ('--sum', '--trace'):
    order, out = walk(events(sys.argv[2]))
    if sys.argv[1] == '--trace':
        names = {}

        def nm(m):
            if m not in names:
                names[m] = 'b%d' % (len(names) + 1)
            return names[m]
        for (tag, a, dep, mono) in out[sys.argv[3]]:
            ind = '  ' * dep
            if tag == 'cne':
                c, (b, (k, inl)) = a
                print('%scne %s -> %s %s%s%s' % (ind, nm(c), nm(b), cord(k),
                      ' inl' if inl == 0 else '', ' [mono]' if mono else ''))
            elif tag == 'mem':
                s, (b, mode) = a
                print('%smember %s %%%s' % (ind, nm(b), cord(mode)))
            elif tag == 'csi':
                s, (n, hit) = a
                print('%scompile-scc-in (%d members%s)' % (ind, n, ', hit' if hit == 0 else ''))
            elif tag == 'beg':
                print('%smiss %s: compile its SCC' % (ind, nm(a)))
            elif tag == 'end':
                print('%send %s (%d members)' % (ind, nm(a[0]), a[1]))
            elif tag in ('mob', 'moe', 'cmo'):
                print('%s%s %s' % (ind, {'mob': 'mono run of', 'moe': 'end mono run of',
                                         'cmo': 'compiled-mono'}[tag], nm(a)))
        sys.exit(0)
    tot = {}
    print('%-10s %5s %5s %5s %5s %5s %5s %7s %9s' %
          ('case', 'cne', 'loc', 'hit', 'mis', 'misM', 'inlM', 'maxdep', 'misM-dep'))
    for c in order:
        cnt = {'cne': 0, 'loc': 0, 'hit': 0, 'mis': 0, 'misM': 0, 'inlM': 0, 'hot': 0}
        md = 0; mdm = []; inl = set()
        for (tag, a, dep, mono) in out[c]:
            if tag == 'inl':
                inl.add(a[1])
            if tag == 'cne':
                k = cord(a[1][1][0]); cnt['cne'] += 1
                if k in ('loc', 'top', 'non'): cnt['loc'] += 1
                elif k in cnt: cnt[k] += 1
                if k == 'mis' and mono:
                    cnt['misM'] += 1; mdm.append(dep)
                    if a[1][0] in inl: cnt['inlM'] += 1
            if tag == 'beg':
                md = max(md, dep + 1)
        for k in cnt: tot[k] = tot.get(k, 0) + cnt[k]
        print('%-10s %5d %5d %5d %5d %5d %5d %7d %9s' %
              (c, cnt['cne'], cnt['loc'], cnt['hit'], cnt['mis'], cnt['misM'], cnt['inlM'],
               md, ','.join(map(str, mdm)) or '-'))
    print('total', tot)
    sys.exit(0)

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
src = open(os.path.join(W, 'desk/lib/nock-compilation.hoon')).read().split('\n')


def ins(anchor, lines, after=True, start=None):
    a = 0 if start is None else src.index(start)
    k = [i for i in range(a, len(src)) if src[i] == anchor]
    if start is not None:
        k = k[:1]
    assert len(k) == 1, anchor
    i = k[0] + 1 if after else k[0]
    src[i:i] = lines


ins('    ?^  j=(biff rin ~(get by jets-hot))  [need.u.j gen]', [
    '    ~&  ^-  *',
    '        :*  %cne  (mug b)  (mug b-callee)',
    '            ?^  (biff rin ~(get by jets-hot))  %hot',
    '            ?:  (~(has in scc) b-callee)',
    '              ?:  (~(has by map-local) b-callee)  %loc',
    '              ?:((~(has by top) b-callee) %top %non)',
    '            ?:((~(has by nary.cache.gen) b-callee) %hit %mis)',
    '            (~(has by inl.cache.gen) b-callee)',
    '        ==',
], after=False)
ins('    =^  new-scc=(set bell)  sccs.cache.gen', [
    '    ~&  ^-(* [%beg (mug b-callee)])',
], after=False)
ins('    [need:(~(got by m) b-callee) gen]', [
    '    ~&  ^-(* [%end (mug b-callee) ~(wyt in new-scc)])',
], after=False)
ins('  ?:  (levy ~(tap in scc) ~(has by nary.cache))', [
    '  ~&  ^-(* [%csi (mug scc) ~(wyt in scc) (levy ~(tap in scc) ~(has by nary.cache))])',
], after=False, start='++  compile-scc-in')
ins('    =/  comp  (comp scc long-ska jets-hot map-local top b)', [
    '    ~&  ^-(* [%mem (mug scc) (mug b) mode])',
], after=False)
ins('  =^  nex=next  gen', [
    '  ~&  ^-(* [%mob (mug func)])',
], after=False, start='++  compile-unary')
ins('  =^  [o=@uwoo sub=@uvre]  gen  (~(kerf comp gen) nex)', [
    '  ~&  ^-(* [%moe (mug func)])',
], after=False, start='++  compile-unary')
ins('    [[%7 p m] cache]', [
    '    ~&  ^-(* [%inl (mug b) (mug c)])',
], after=False, start='++  inlined')
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(src))

# The corpus: the cases of tools/hoon/sccloop.py, then chains, shared callees, callees reached
# only through inlined code, and SCCs with callees outside.  Small non-recursive arms are
# inlined by +inlined (at most 48 nodes, alone in their SCC, no self call); arms that loop
# with $ are not.
sl = open(os.path.join(D, 'sccloop.py')).read()
old = sl[sl.index("  :~  :-  %dec"):sl.index("\n  ==\n'''")]
NEW = r'''
      :-  %in3
        =>  ~  =<  a
        |%  ++  a  |=(n=@ (b (dc n)))
            ++  b  |=(n=@ (c (dc n)))
            ++  c  |=(n=@ (dc n))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %in6
        =>  ~  =<  a
        |%  ++  a  |=(n=@ (b (dc n)))
            ++  b  |=(n=@ (c n))
            ++  c  |=(n=@ (d (dc n)))
            ++  d  |=(n=@ (e n))
            ++  e  |=(n=@ (f (dc n)))
            ++  f  |=(n=@ (dc n))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %rc3
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) (b 5) $(n (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) (c 5) $(n (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %rc6
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) (b 5) $(n (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) (c 5) $(n (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) (d 5) $(n (dc n))))
            ++  d  |=(n=@ ?:(.=(0 n) (e 5) $(n (dc n))))
            ++  e  |=(n=@ ?:(.=(0 n) (f 5) $(n (dc n))))
            ++  f  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %mix4
        =>  ~  =<  a
        |%  ++  a  |=(n=@ (b (dc n)))
            ++  b  |=(n=@ ?:(.=(0 n) (c 5) $(n (dc n))))
            ++  c  |=(n=@ (d (dc n)))
            ++  d  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %share
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) [(b 5) (c 6)] $(n (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) (d 5) $(n (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) (d 6) $(n (dc n))))
            ++  d  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %share2
        =>  ~  =<  a
        |%  ++  a  |=(n=@ [(b n) (b (dc n)) (c n)])
            ++  b  |=(n=@ (dc (dc n)))
            ++  c  |=(n=@ ?:(.=(0 n) (b 5) $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %diam
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) (ad (b 5) (c 6)) $(n (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) (d 5) $(n (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) (d 6) $(n (dc n))))
            ++  d  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  ad  |=([a=@ b=@] |-(?:(.=(0 a) b $(a (dc a), b .+(b)))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %mutout
        =>  ~  =<  ev
        |%  ++  ev  |=(n=@ ?:(.=(0 n) (sq 3) (od (dc n))))
            ++  od  |=(n=@ ?:(.=(0 n) (ad 1 2) (ev (dc n))))
            ++  sq  |=(n=@ [n n])
            ++  ad  |=([a=@ b=@] |-(?:(.=(0 a) b $(a (dc a), b .+(b)))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %mutout2
        =>  ~  =<  p
        |%  ++  p  |=(x=* ?@(x (r x) (q +.x)))
            ++  q  |=(x=* ?@(x (t x) (p -.x)))
            ++  r  |=(n=@ ?:(.=(0 n) (s 4) $(n (dc n))))
            ++  s  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  t  |=(n=@ (s (dc n)))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %inlonly
        =>  ~  =<  a
        |%  ++  a  |=(n=@ [(b n) n])
            ++  b  |=(n=@ (c n))
            ++  c  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %inlonly2
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) (b 3) $(n (dc n))))
            ++  b  |=(n=@ (c n))
            ++  c  |=(n=@ [(d n) 1])
            ++  d  |=(n=@ ?:(.=(0 n) 7 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %deep6
        =>  ~  =<  a1
        |%  ++  a1  |=(n=@ ?:(.=(0 n) (b1 5) (a2 (dc n))))
            ++  a2  |=(n=@ ?:(.=(0 n) (b2 5) (a1 (dc n))))
            ++  b1  |=(n=@ ?:(.=(0 n) (c1 5) (b2 (dc n))))
            ++  b2  |=(n=@ ?:(.=(0 n) (c2 5) (b1 (dc n))))
            ++  c1  |=(n=@ ?:(.=(0 n) 7 (c2 (dc n))))
            ++  c2  |=(n=@ ?:(.=(0 n) 8 (c1 (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %tree2
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) [(b 1) (c 2)] $(n (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) [(d 1) (e 2)] $(n (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) [(e 1) (f 2)] $(n (dc n))))
            ++  d  |=(n=@ ?:(.=(0 n) 4 $(n (dc n))))
            ++  e  |=(n=@ ?:(.=(0 n) 5 $(n (dc n))))
            ++  f  |=(n=@ ?:(.=(0 n) 6 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %selfout
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) [(b 1) (c 2)] $(n (dc n))))
            ++  b  |=(n=@ [n n])
            ++  c  |=(n=@ ?:(.=(0 n) 6 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %cyc3out
        =>  ~  =<  a
        |%  ++  a  |=(n=@ ?:(.=(0 n) (x 1) (b (dc n))))
            ++  b  |=(n=@ ?:(.=(0 n) (y 1) (c (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) (z 1) (a (dc n))))
            ++  x  |=(n=@ ?:(.=(0 n) 4 $(n (dc n))))
            ++  y  |=(n=@ ?:(.=(0 n) 5 $(n (x n))))
            ++  z  |=(n=@ (y n))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %drop
        =>  ~  =<  a
        |%  ++  a  |=(n=@ =/(x (b n) (c n)))
            ++  b  |=(n=@ ?:(.=(0 n) 4 $(n (dc n))))
            ++  c  |=(n=@ ?:(.=(0 n) 5 $(n (dc n))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %big
        =>  ~  =<  a
        |%  ++  a  |=(n=@ (b (dc n)))
            ++  b
              |=  n=@
              :*  (c (dc n))  (c (dc (dc n)))  (c n)  (dc (dc (dc n)))
                  (dc (dc (dc (dc n))))  (dc (dc (dc (dc (dc n)))))  n  n
              ==
            ++  c
              |=  n=@
              :*  (dc (dc n))  (dc (dc (dc n)))  (dc (dc (dc (dc n))))
                  (dc (dc (dc (dc (dc n)))))  (dc (dc (dc (dc (dc (dc n))))))  n  n
              ==
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --
      :-  %ackout
        =>  ~  =<  ack
        |%  ++  ack
              |=  [m=@ n=@]
              ?:  .=(0 m)  (inc n)
              ?:  .=(0 n)  (ack (dc m) 1)
              (ack (dc m) (ack m (dc n)))
            ++  inc  |=(n=@ (ad n 1))
            ++  ad  |=([a=@ b=@] |-(?:(.=(0 a) b $(a (dc a), b .+(b)))))
            ++  dc  |=(a=@ =|(b=@ |-(?:(.=(a .+(b)) b $(b .+(b))))))
        --'''
cases = sl[sl.index("=/  cases=(list [nam=@tas gat=*])"):sl.index("\n  ==\n'''")] + NEW + '\n  ==\n'
ck = cases + r'''
|-  ^-  @
?~  cases  0
~&  ^-(* [%case nam.i.cases])
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=.  sure.cache.state  ~
=.  inl.cache.state  ~
=.  sccs.cache.state  ~
=/  fol=*  [8 [1 gat.i.cases] [9 2 [10 [6 [0 7]] [0 2]]]]
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol) fol)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
~&  ^-(* [%cmo (mug func)])
=^  raw=straight  cache.state  (compiled-mono func scc)
$(cases t.cases)
'''
open(os.path.join(out, 'ck.hoon'), 'w').write(ck)
