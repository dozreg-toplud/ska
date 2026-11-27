#!/usr/bin/env python3
# usage: sccreal.py OUTDIR      then
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 900 > out.txt
#   tools/hoon/sccreal.py --lean out.txt > lemmas/Ska/SccLoopRealData.lean
#   sccreal.py OUTDIR --tally-lib, the same run, then
#   tools/hoon/sccreal.py --tally out.txt        (the entries of +run-shape per case of the nomm
#                                                 and goal, in %must and %may compiles: each
#                                                 counted under the mode of the last member begun)
# The %done compiles of the members of real SCCs (README Gaps 21.14, the model memDoneM of
# lemmas/Ska/SccLoopReal.lean), on the 18 formulas of sccloop.py.  The instrumented copy of the
# library prints, as raw nouns:
#   [%case nam]                  before each case
#   [%dn S b less nomm laz ord ned-final need-new sur o nosoft mem out]
#                                in member, on the %done path (lines 3530 to 3539): the bell
#                                (its mug), less.b, the nomm, laz.nex, +shape-collapse of laz,
#                                ned-final, need-new, the raw sur, o, =(~ soft.gen) after the
#                                run; mem: each member [bell view-need view-sure pure jet];
#                                out: each key of nary.cache [bell need sure pure jet]
#   [%ds S b soft]               right after: ~(tap by soft.gen) after the run, each [o soft-call]
#   [%dp S b prev np]            at the product: the previous entry's need (or ~) and
#                                need-pessimized
#   [%dc S b soft mug wyt]       in finish after +coerce-lazy: ~(tap by soft.gen), the mug and size of
#                                blocks.gen; [%dd S b mug wyt] the same after +soft-done
#   [%dz S b need n-args blocks] the straight of (finish ~), its blocks as ~(tap by blocks)
#   [%fin S entries]             the needs of the entries the final pass returns (as mugs)
#   [%rs tag]                    (with --tally) each case of +run-shape entered
import os, re, sys
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))
sys.setrecursionlimit(100000)


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


def lst(n):
    out = []
    while n != 0:
        out.append(n[0]); n = n[1]
    return out


def ns(n):
    """A noun as the compact string the Lean parser reads: atoms in decimal, cells [h t]."""
    out = []
    st = [n]
    while st:
        x = st.pop()
        if isinstance(x, str):
            out.append(x); continue
        if isinstance(x, tuple):
            out.append('[')
            st.append(']'); st.append(x[1]); st.append(' '); st.append(x[0])
        else:
            out.append(str(x))
    return ''.join(out)


def records(path):
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


def callees(nm, acc):
    """The bells of the direct calls of a nomm (noun), in order."""
    st = [nm]
    while st:
        n = st.pop()
        if not isinstance(n, tuple):
            continue
        h, t = n
        if isinstance(h, tuple):
            st.append(h); st.append(t); continue
        if h in (0, 1):
            continue
        if h == 2:
            p, (q, info) = t
            if info != 0:
                b = info[1][0]
                if b not in acc: acc.append(b)
            st.append(p); st.append(q); continue
        if h in (3, 4):
            st.append(t); continue
        if h in (5, 7, 12):
            st.append(t[0]); st.append(t[1]); continue
        if h == 6:
            st.append(t[0]); st.append(t[1][0]); st.append(t[1][1]); continue
        if h == 10:
            st.append(t[0][1]); st.append(t[1]); continue
        if h == 11:
            p, (q, body) = t
            if isinstance(p, tuple):
                st.append(p[1])
            st.append(q); continue
        # %mean and others: walk every cell (bells found by the %2 shape only)
        st.append(t)
    return acc


if sys.argv[1] in ('--lean', '--tally'):
    evs = records(sys.argv[2])
    if sys.argv[1] == '--tally':
        case = None; tal = {}; tot = {}; mode = None
        want = sys.argv[3] if len(sys.argv) > 3 else 'must'
        for e in evs:
            tag = cord(e[0])
            if tag == 'case':
                case = cord(e[1])
            elif tag == 'rm':
                mode = cord(e[1])
            elif tag == 'rs' and mode == want:
                c0, g = e[1]
                k = '%s/%s' % (cord(c0) if c0 > 20 else 'n%d' % c0, cord(g))
                tot[k] = tot.get(k, 0) + 1
                tal.setdefault(k, set()).add(case)
        for k in sorted(tot, key=lambda k: -tot[k]):
            print('%-8s %6d  %s' % (k, tot[k], ' '.join(sorted(tal[k]))))
        sys.exit(0)
    case = None; recs = []; pend = {}
    for e in evs:
        tag = cord(e[0])
        if tag == 'case':
            case = cord(e[1]); continue
        if tag == 'dn':
            S, (b, (less, (nomm, (laz, (ord_, (nedf, (nn, (sur, (o, (nosoft, (mem, out))))))))))) = e[1]
            recs.append(dict(case=case, b=b, less=less, nomm=nomm, laz=laz, ord=ord_, nedf=nedf,
                             nn=nn, sur=sur, o=o, nosoft=nosoft, mem=lst(mem), out=lst(out)))
            pend[(S, b)] = recs[-1]
        elif tag == 'ds':
            S, (b, sl) = e[1]
            pend[(S, b)]['soft'] = lst(sl)
        elif tag == 'dc':
            S, (b, (sl, _)) = e[1]
            for r in reversed(recs):
                if r['b'] == b and 'csoft' not in r:
                    r['csoft'] = lst(sl); break
        elif tag == 'dz':
            S, (b, (zn, (za, zb))) = e[1]
            for r in reversed(recs):
                if r['b'] == b and 'zneed' not in r:
                    r['zneed'] = zn; r['znargs'] = za; r['zblocks'] = lst(zb); break
        elif tag == 'dp':
            S, (b, (prev, np)) = e[1]
            r = pend.pop((S, b))
            r['prev'] = prev; r['np'] = np
    print('import lemmas.Ska.SccLoopReal\n')
    print('/-! Generated by `tools/hoon/sccreal.py --lean` from the dump of `tools/hoon/sccreal.py`')
    print('    (the `%done` compiles of `member` in the instrumented `+compile-scc-in`).  Nouns are')
    print('    strings read by `SccLoopRealCheck.nounOfStr`: atoms in decimal, cells `[h t]`. -/\n')
    print('namespace Formalization.SkaModel.SccLoop.RealData\n')
    print('/-- One `%done` compile: the case, the bell\'s mug, `less.b`, the nomm, `laz`, the `ord` of')
    print('`+shape-collapse`, `ned-final`, `need-new`, the raw `sur`, `o`, no soft call, the members')
    print('`[bell need sure pure jet]` (the views), the callees outside `[bell need sure pure jet]`')
    print('(only those the nomm calls), the previous entry (`~` or `[~ need]`), `need-pessimized`,')
    print('the soft map after the run (`~(tap by soft.gen)`, each `[o soft-call]`), the soft map after')
    print('`+coerce-lazy` in `finish` (`csoft`), the straight of `(finish ~)`: need, `n-args`, the blocks')
    print('`~(tap by blocks)` (each `[o blob]`). -/')
    print('structure DoneRec where\n  cs : String\n  b : Nat\n  less : String\n  nomm : String\n  laz : String')
    print('  ord : String\n  nedf : String\n  nn : String\n  sur : String\n  o : Nat\n  nosoft : Bool')
    print('  mem : List String\n  out : List String\n  prev : String\n  np : String')
    print('  soft : List String := []\n  csoft : List String := []\n  zneed : String := "0"')
    print('  znargs : Nat := 0\n  zblocks : List String := []\n')
    names = []
    for i, r in enumerate(recs):
        cal = callees(r['nomm'], [])
        out = [x for x in r['out'] if x[0] in cal]
        nm = 'r%d' % i; names.append(nm)
        print('def %s : DoneRec where' % nm)
        print('  cs := "%s"\n  b := %d' % (r['case'], r['b']))
        for k in ('less', 'nomm', 'laz', 'ord', 'nedf', 'nn', 'sur'):
            print('  %s := "%s"' % (k, ns(r[k])))
        print('  o := %d\n  nosoft := %s' % (r['o'], 'true' if r['nosoft'] == 0 else 'false'))
        print('  mem := [%s]' % ', '.join('"%s"' % ns(x) for x in r['mem']))
        print('  out := [%s]' % ', '.join('"%s"' % ns(x) for x in out))
        print('  prev := "%s"\n  np := "%s"' % (ns(r['prev']), ns(r['np'])))
        print('  soft := [%s]' % ', '.join('"%s"' % ns(x) for x in r.get('soft', [])))
        print('  csoft := [%s]' % ', '.join('"%s"' % ns(x) for x in r.get('csoft', [])))
        print('  zneed := "%s"\n  znargs := %d' % (ns(r['zneed']), r['znargs']))
        print('  zblocks := [%s]\n' % ', '.join('"%s"' % ns(x) for x in r['zblocks']))
    print('def recs : List DoneRec := [%s]\n' % ', '.join(names))
    print('end Formalization.SkaModel.SccLoop.RealData')
    sys.exit(0)

tally = '--tally-lib' in sys.argv
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
src = open(os.path.join(W, 'desk/lib/nock-compilation.hoon')).read().split('\n')
a = src.index('++  compile-scc-in')


def ins(anchor, lines, after=True, lo=None, hi=None):
    lo = a if lo is None else lo
    hi = src.index('++  bake-need') if hi is None else hi
    k = [i for i in range(lo, hi) if src[i] == anchor]
    assert len(k) == 1, anchor
    i = k[0] + 1 if after else k[0]
    src[i:i] = lines


ENT = [
    '                :*  k',
    '                    ?^  s=(~(get by map-local) k)  need.u.s',
    '                    (~(gut by top) k [%none ~])',
    '                    (~(gut by sure.cache.gen) k [%none ~])',
    '                    ?~(e=(~(get by code.long-ska) k) | pure.u.e)',
    '                    (~(has by call.cole.jets.long-ska) k)',
    '                ==',
]
ins('      [[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]', [
    '      ~&  ^-  *',
    '          :*  %dn  (mug scc)  (mug b)  less.b  nomm  laz',
    '              (shape-collapse laz cape.less.b)',
    '              ned-final  (need-to-ordered ned.bak)  sur  o  =(~ soft.gen)',
    '              %+  turn  ~(tap in scc)',
    '              |=  k=bell',
] + ENT + [
    '              %+  turn  ~(tap by nary.cache.gen)',
    '              |=  [k=bell s=straight]',
    '              :*  k  need.s',
    '                  (~(gut by sure.cache.gen) k [%none ~])',
    '                  ?~(e=(~(get by code.long-ska) k) | pure.u.e)',
    '                  (~(has by call.cole.jets.long-ska) k)',
    '              ==',
    '          ==',
], after=False)
ins('      [[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]', [
    '      ~&  ^-(* [%ds (mug scc) (mug b) ~(tap by soft.gen)])',
], after=False)
ins('    ?~  s-previous=(~(get by map-local) b)', [
    '    ~&  ^-  *',
    '        ?.  done  ~',
    '        =/  sp  (~(get by map-local) b)',
    '        :*  %dp  (mug scc)  (mug b)',
    '            ?~(sp ~ `need.u.sp)',
    '            ?~(sp need-new (msg-need-ord need-new need.u.sp cape.less.b))',
    '        ==',
], after=False)
# inside finish: the soft map and the blocks after +coerce-lazy, the blocks after +soft-done,
# and the straight of (finish ~)
ins('      =.  gen  ~(soft-done comp gen)', [
    '      ~&  ^-(* [%dc (mug scc) (mug b) ~(tap by soft.gen) (mug blocks.gen) ~(wyt by blocks.gen)])',
], after=False)
ins('      =.  gen  ~(soft-done comp gen)', [
    '      ~&  ^-(* [%dd (mug scc) (mug b) (mug blocks.gen) ~(wyt by blocks.gen)])',
])
k = [i for i in range(a, src.index('++  bake-need'))
     if src[i] == '      ?~  pessimized  (~(to-straight comp gen) res)']
assert len(k) == 1
src[k[0]:k[0] + 1] = [
    '      ?~  pessimized',
    '        =/  z  (~(to-straight comp gen) res)',
    '        ~&  ^-(* [%dz (mug scc) (mug b) need.z n-args.z ~(tap by blocks.z)])',
    '        z',
]
ins('      [m c(nary (~(uni by nary.c) m))]', [
    '      ~&  ^-  *',
    '          [%fin (mug scc) (turn ~(tap by m) |=([b=bell s=straight] [(mug b) need.s]))]',
], after=False)
if tally:
    # each entry of +run-shape: the case of the nomm (%2 split into direct and indirect, the
    # autocons %cons, a hint by its kind) and the kind of the goal, printed before its ?-
    r0 = src.index('  ++  run-shape')
    k = next(i for i in range(r0, len(src)) if src[i] == '    ?-    nomm')
    src[k:k] = ['    ~&  ^-  *',
                '        :+  %rs',
                '          ?+  nomm  ?@(-.nomm -.nomm %cons)',
                '            [%2 *]   ?~(info.nomm %ind %dir)',
                '            [%11 *]  ?@(p.nomm %hs %hd)',
                '          ==',
                '        -.goal']
    ins('    =/  comp  (comp scc long-ska jets-hot map-local top b)',
        ['    ~&  ^-(* [%rm mode])'], after=False)
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(src))

cs = open(os.path.join(D, 'sccloop.py')).read()
CASES = re.search(r"CASES = r'''(.*?)'''", cs, re.S).group(1)
ck = CASES + r'''
|-  ^-  @
?~  cases  0
~&  ^-(* [%case nam.i.cases])
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=.  sure.cache.state  ~
=.  inl.cache.state  ~
=/  fol=*  [8 [1 gat.i.cases] [9 2 [10 [6 [0 7]] [0 2]]]]
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol) fol)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
$(cases t.cases)
'''
open(os.path.join(out, 'ck.hoon'), 'w').write(ck)
