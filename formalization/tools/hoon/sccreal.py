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


def tset(n):
    """A treap set as a sorted list noun."""
    xs = []; st = [n]
    while st:
        x = st.pop()
        if isinstance(x, tuple):
            xs.append(x[0]); st.append(x[1][0]); st.append(x[1][1])
    r = 0
    for v in reversed(sorted(set(xs))):
        r = (v, r)
    return r


def lazen(l):
    """A laze with its sets as sorted lists."""
    (ned, lok), (fk, bd) = l
    fs = [((y[0], lazen(y[1])), (n[0], lazen(n[1]))) for (y, n) in lst(fk)]
    bs = [(o, lazen(z)) for (o, z) in lst(bd)]
    def mk(xs):
        r = 0
        for x in reversed(xs):
            r = (x, r)
        return r
    return ((ned, tset(lok)), (mk(fs), mk(bs)))


if sys.argv[1] == '--shape-lean':
    evs = records(sys.argv[2])
    case = None; recs = []; pend = {}; codes = {}
    for e in evs:
        tag = cord(e[0])
        if tag == 'case':
            case = cord(e[1]); continue
        if tag == 'sm':
            S, (b, (mode, (bel, (nomm, (l, (col, (shp, (sur, (idg, (sofs, (mem, out))))))))))) = e[1]
            r = dict(case=case, b=b, mode=cord(mode), less=bel[0], bell=bel, nomm=nomm, l=lazen(l), col=col, shape=shp,
                     sur=sur, idg=idg, sofs=sorted(lst(sofs)), mem=lst(mem), out=lst(out))
            recs.append(r); pend[(S, b)] = r
        elif tag == 'sp':
            S, (b, (mode, (keep, (was, (sur, (moved, (prev, (np, chg)))))))) = e[1]
            r = pend.pop((S, b))
            assert r['mode'] == cord(mode)
            r.update(keep=keep, was=was, fsur=sur, moved=moved, prev=prev, np=np, chg=chg)
        elif tag == 'code':
            codes[case] = lst(e[1])
    assert not pend, len(pend)
    print('import lemmas.Ska.SccLoopShape\n')
    print('/-! Generated by `tools/hoon/sccreal.py --shape-lean` from the dump of `sccreal.py OUT --shape-lib`')
    print('    (the `%must` and `%may` compiles of `member`, README Gaps 21.18).  Nouns are strings read by')
    print('    `SccLoopRealCheck.nounOfStr`; the sets of a `laze` are sorted lists. -/\n')
    print('namespace Formalization.SkaModel.SccLoop.ShapeData\n')
    print('/-- One sweep compile: the case, the bell\'s mug, the mode, `less.b`, the nomm, the `laze` of')
    print('`+run-shape` (`l`), `collapsed`, `shape`, the raw `sur` (`+sure-of` of `sure.l`), `id-gen` and')
    print('`sofs` after the run, the views of the members and the outside callees `[bell need sure pure jet]`')
    print('(`jet` as `+run-shape` reads it); at the product `keep`, `was`, the `sur` put, `moved`, the entry')
    print('(`~` or `[~ need]`), the need put `np` and `chg`. -/')
    print('structure ShapeRec where\n  cs : String\n  b : Nat\n  must : Bool\n  bell : String\n  less : String\n  nomm : String')
    print('  l : String\n  col : String\n  shape : String\n  sur : String\n  idg : Nat\n  sofs : List Nat')
    print('  mem : List String\n  out : List String\n  keep : Bool\n  was : String\n  fsur : String')
    print('  moved : Bool\n  prev : String\n  np : String\n  chg : Bool\n')
    names = []
    for i, r in enumerate(recs):
        nm = 's%d' % i; names.append(nm)
        print('def %s : ShapeRec where' % nm)
        print('  cs := "%s"\n  b := %d\n  must := %s' % (r['case'], r['b'], 'true' if r['mode'] == 'must' else 'false'))
        for k in ('bell', 'less', 'nomm', 'l', 'col', 'shape', 'sur'):
            print('  %s := "%s"' % (k, ns(r[k])))
        print('  idg := %d\n  sofs := [%s]' % (r['idg'], ', '.join(str(x) for x in r['sofs'])))
        print('  mem := [%s]' % ', '.join('"%s"' % ns(x) for x in r['mem']))
        cal = callees(r['nomm'], [])
        print('  out := [%s]' % ', '.join('"%s"' % ns(x) for x in r['out'] if x[0] in cal))
        print('  keep := %s\n  was := "%s"\n  fsur := "%s"' % ('true' if r['keep'] == 0 else 'false', ns(r['was']), ns(r['fsur'])))
        print('  moved := %s\n  prev := "%s"\n  np := "%s"' % ('true' if r['moved'] == 0 else 'false', ns(r['prev']), ns(r['np'])))
        print('  chg := %s\n' % ('true' if r['chg'] == 0 else 'false'))
    print('def recs : List ShapeRec := [%s]\n' % ', '.join(names))
    # the code table of each case, restricted to the bells the case's compiles reach
    print('/-- Per case, `[bell nomm pure]` of the code table entries the compiles reach. -/')
    print('def codes : List (String × List String) := [')
    rows = []
    for cs, ents in codes.items():
        tab = {k: (n, p) for (k, (n, p)) in ents}
        reach = []
        for r in recs:
            if r['case'] == cs:
                callees(r['nomm'], reach)
        i = 0
        while i < len(reach):
            if reach[i] in tab:
                callees(tab[reach[i]][0], reach)
            i += 1
        rows.append('  ("%s", [%s])' % (cs, ', '.join('"%s"' % ns((k, tab[k])) for k in reach if k in tab)))
    print(',\n'.join(rows) + ']\n')
    print('end Formalization.SkaModel.SccLoop.ShapeData')
    sys.exit(0)

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
shape = '--shape-lib' in sys.argv
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
if shape:
    # the sweeps' compiles (README Gaps 21.18): in the ?.  done branch the laze of +run-shape,
    # collapsed, shape, sur, id-gen and sofs after the run, the views (jet as +run-shape reads
    # it), the outside callees; at the product prev, np, moved, chg, was, keep and sur
    SHJ = '                    ?=(^ (biff (~(get by call.cole.jets.long-ska) k) ~(get by jets-hot)))'
    ins('        [shape *need-lazy *need *baked `@uwoo`0 (sure-of sure.l cape.less.b)]', [
        '        ~&  ^-  *',
        '            :*  %sm  (mug scc)  (mug b)  mode  b  nomm  l',
        '                ?:(?=(%must mode) (laze-collapse l cape.less.b) (laze-may l cape.less.b))',
        '                shape  (sure-of sure.l cape.less.b)  id-gen.gen  ~(tap in sofs.gen)',
        '                %+  turn  ~(tap in scc)',
        '                |=  k=bell',
    ] + ENT[:-2] + [SHJ, '                ==',
        '                %+  turn  ~(tap by nary.cache.gen)',
        '                |=  [k=bell s=straight]',
        '                :*  k  need.s',
        '                    (~(gut by sure.cache.gen) k [%none ~])',
        '                    ?~(e=(~(get by code.long-ska) k) | pure.u.e)',
        SHJ,
        '                ==',
        '            ==',
    ], after=False)
    ins('    ?~  s-previous=(~(get by map-local) b)', [
        '    ~&  ^-  *',
        '        ?:  done  ~',
        '        =/  sp  (~(get by map-local) b)',
        '        =/  np  ?~(sp need-new (msg-need-ord need-new need.u.sp cape.less.b))',
        '        :*  %sp  (mug scc)  (mug b)  mode  keep  was  sur  moved',
        '            ?~(sp ~ `need.u.sp)  np',
        '            ?~  sp',
        '              ?|  moved  !?=([%none ~] need-new)',
        '                  !?=([%none ~] (~(gut by top) b [%none ~]))',
        '              ==',
        '            |(moved !=(np need.u.sp))',
        '        ==',
    ], after=False)
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
if shape:
    # the code table after each case: [bell nomm pure] of every entry (for +sound-far, +hinted)
    ck = ck.replace('$(cases t.cases)\n', '~&  ^-  *\n    :-  %code\n    %+  turn  ~(tap by code.long-ska.state)\n'
                    '    |=([k=bell v=code-entry] [k nomm.v pure.v])\n$(cases t.cases)\n')
open(os.path.join(out, 'ck.hoon'), 'w').write(ck)
