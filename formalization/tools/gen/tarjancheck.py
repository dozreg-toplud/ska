"""`+tarjan` of the library against the model `tarjanM` (lemmas/Ska/Tarjan.lean,
track Q).

usage: tarjancheck.py hoon OUT.hoon        the driver (tools/hoon/tarjandump.hoon)
       tarjancheck.py trim RUN.out > tools/hoon/tarjandump.txt
       tarjancheck.py lean DUMP.txt        writes lemmas/Ska/TarjanData.lean

The driver builds each graph as a `(jug @ud @ud)` with `+gas:by` and prints
one line per case, `[%tj N (jam [ord out])]`: `ord` is the graph as
`~(rep by g)` visits it (each key with its kids as `~(rep in kids)` visits
them: the pre-order node, left, right of the raw treap, which is the order of
`+rep`; the test's own `~(rep by g)` with a typed gate fails to compile with
`fuse-loop`), `out` is
the product of `(tarjan g)` as a unit: the list of the components, each set
as a list in `rep in` order; on the empty graph only `+mule`'s flag (`~` on a
crash, `[~ ~]` if it returns: a `?-` on the `+mule` of the wet gate fails to
compile with `fuse-loop`).  The harness evaluates the
test twice, so every line appears twice; `trim` keeps one of each.
"""
import random, re, sys

SEED = 20261127


def cases():
    R = random.Random(SEED)
    out = []  # (kind, [(key, [kids])])

    def labels(n):
        return R.sample(range(100), n)

    def add(kind, edges, keys=None):
        # edges: dict key -> list of kids; keys: the key order (any)
        out.append((kind, [(k, list(edges[k])) for k in (keys or list(edges))]))

    out.append(('empty', []))
    for _ in range(3):
        v = labels(1)[0]
        add('single', {v: []})
    for _ in range(3):
        v = labels(1)[0]
        add('selfloop1', {v: [v]})
    # chains, last key present or the last vertex outside the key set
    for n in range(2, 13):
        vs = labels(n)
        add('chain', {vs[i]: ([vs[i + 1]] if i + 1 < n else []) for i in range(n)})
        add('chain-out', {vs[i]: [vs[i + 1]] for i in range(n - 1)})
        add('chain-rev', {vs[i]: ([vs[i - 1]] if i > 0 else []) for i in range(n)})
    # cycles
    for n in range(1, 13):
        for _ in range(2):
            vs = labels(n)
            add('cycle', {vs[i]: [vs[(i + 1) % n]] for i in range(n)})
    # two cycles sharing a vertex
    for _ in range(14):
        a = R.randint(1, 6); b = R.randint(1, 6)
        vs = labels(a + b - 1 if a + b - 1 >= 1 else 1)
        s = vs[0]
        c1 = [s] + vs[1:a]
        c2 = [s] + vs[a:a + b - 1]
        e = {v: [] for v in vs}
        for c in (c1, c2):
            for i in range(len(c)):
                e[c[i]].append(c[(i + 1) % len(c)])
        add('two-cycles', {k: sorted(set(v)) for k, v in e.items()})
    # a DAG of cycles: cycles of sizes 1..4, DAG edges between them
    for _ in range(24):
        sizes = []
        tot = 0
        while tot < 12:
            s = R.randint(1, 4)
            if tot + s > 12: break
            sizes.append(s); tot += s
            if R.random() < 0.25: break
        vs = labels(tot)
        comps = []; p = 0
        for s in sizes:
            comps.append(vs[p:p + s]); p += s
        e = {v: set() for v in vs}
        for c in comps:
            if len(c) > 1 or R.random() < 0.5:
                for i in range(len(c)):
                    e[c[i]].add(c[(i + 1) % len(c)])
            if len(c) > 2 and R.random() < 0.5:
                e[c[0]].add(c[2])
        for i in range(len(comps)):
            for j in range(i + 1, len(comps)):
                if R.random() < 0.4:
                    e[R.choice(comps[i])].add(R.choice(comps[j]))
        keys = list(e); R.shuffle(keys)
        add('dag-of-cycles', {k: sorted(e[k]) for k in keys})
    # random, several densities, with self loops sometimes
    for d in (0.08, 0.15, 0.25, 0.4, 0.6, 0.9):
        for _ in range(16):
            n = R.randint(1, 12)
            vs = labels(n)
            loops = R.random() < 0.4
            e = {v: sorted(w for w in vs if (w != v or loops) and R.random() < d) for v in vs}
            add('random-%g' % d, e)
    # kids outside the key set
    for _ in range(24):
        n = R.randint(1, 9); m = R.randint(1, 3)
        vs = labels(n + m)
        keys, outs = vs[:n], vs[n:]
        e = {v: sorted(set(w for w in vs if R.random() < 0.3)) for v in keys}
        if not any(w in outs for k in e for w in e[k]):
            e[keys[0]] = sorted(set(e[keys[0]] + [outs[0]]))
        add('kids-out', e)
    return out


def hoon(path):
    cs = cases()
    L = [':: +tarjan of the library against the model tarjanM (lemmas/Ska/Tarjan.lean, track Q):',
         ':: written by tools/gen/tarjancheck.py; %d graphs; per case one line' % len(cs),
         ':: [%tj N (jam [ord out])], ord the graph in ~(rep by g) order (kids in ~(rep in) order),',
         ':: out ~ on a crash, else the components as lists in ~(rep in) order.',
         '=/  cases=(list [@ud (list [@ud (list @ud)])])',
         '  :~']
    for i, (kind, g) in enumerate(cs):
        gl = ' '.join('[%d %s]' % (k, ('~[' + ' '.join(map(str, ks)) + ']') if ks else '~') for k, ks in g)
        L.append('    [%d %s]  :: %s' % (i, ('~[' + gl + ']') if g else '~', kind))
    L += ['  ==',
          '|-  ^-  @',
          '?~  cases  0',
          '=/  g=(jug @ud @ud)',
          '  %-  ~(gas by *(jug @ud @ud))',
          '  %+  turn  +.i.cases',
          '  |=([k=@ud ks=(list @ud)] [k (silt ks)])',
          '::  the order of +rep (node, left, right) by a walk of the raw treap: the',
          '::  test\'s own ~(rep by g) with a typed gate fails to compile with fuse-loop',
          '=/  pre',
          '  |=  t=*',
          '  ^-  (list *)',
          '  ?@  t  ~',
          '  [-.t (weld $(t +<.t) $(t +>.t))]',
          '=/  ord=(list *)',
          '  (turn (pre g) |=(n=* ?@(n !! [-.n (pre +.n)])))',
          '::  the empty graph: only whether it crashes (a ?- on the +mule of the wet',
          '::  gate fails with fuse-loop): `~ if it returns, ~ if it crashes',
          '=/  out=(unit (list (list *)))',
          '  ?:  =(~ g)',
          '    ?:  -:(mule |.((tarjan g)))  [~ ~]  ~',
          '  `(turn (tarjan g) |=(s=(set @ud) (pre s)))',
          '~&  [%tj -.i.cases (jam [ord out])]',
          '$(cases t.cases)', '']
    open(path, 'w').write('\n'.join(L))
    sys.stderr.write('%d cases\n' % len(cs))


def cue(a):
    bits = bin(a)[2:][::-1] if a else ''
    pos = [0]; refs = {}

    def rd(n):
        v = 0
        for j in range(n): v |= (int(bits[pos[0] + j]) if pos[0] + j < len(bits) else 0) << j
        pos[0] += n; return v

    def mat():
        if bits[pos[0]] == '1': pos[0] += 1; return 0
        z = 0
        while bits[pos[0] + z] == '0': z += 1
        pos[0] += z + 1
        b = rd(z - 1) | (1 << (z - 1)) if z > 1 else 1
        return rd(b)

    def go():
        p = pos[0]
        if bits[pos[0]] == '0':
            pos[0] += 1; v = mat(); refs[p] = v; return v
        pos[0] += 1
        if bits[pos[0]] == '0':
            pos[0] += 1; h = go(); t = go(); refs[p] = (h, t); return (h, t)
        pos[0] += 1; return refs[mat()]
    return go()


def hlist(n):
    out = []
    while isinstance(n, tuple):
        out.append(n[0]); n = n[1]
    assert n == 0
    return out


def records(path):
    res = {}
    for m in re.finditer(r'\[\s*%tj\s+([0-9.]+)\s+([0-9.]+)\s*\]', open(path).read()):
        k = int(m.group(1).replace('.', '')); v = int(m.group(2).replace('.', ''))
        assert res.get(k, v) == v, k
        res[k] = v
    return res


def decode(v):
    ord_, out = cue(v)
    g = [(k, hlist(ks)) for k, ks in (x for x in hlist(ord_))]
    r = None if out == 0 else [hlist(s) for s in hlist(out[1])]
    return g, r


def lean(path):
    res = records(path)
    n = len(cases())
    assert sorted(res) == list(range(n)), (len(res), n)
    kinds = [k for k, _ in cases()]
    rows = []
    for i in range(n):
        g, r = decode(res[i])
        gs = '[' + ', '.join('(%d, [%s])' % (k, ', '.join(map(str, ks))) for k, ks in g) + ']'
        rs = 'none' if r is None else 'some [' + ', '.join('[%s]' % ', '.join(map(str, s)) for s in r) + ']'
        rows.append('  (%d, %s, %s)' % (i, gs, rs))
    CH = 40
    L = ['import lemmas.Ska.Tarjan', '', '/-!',
         '# The dump of `+tarjan` on %d graphs' % n, '',
         'Written by `tools/gen/tarjancheck.py lean tools/hoon/tarjandump.txt` from the output of',
         '`tools/hoon/tarjandump.hoon` on the real compiler: per case its number, the graph as',
         '`~(rep by g)` visits it (each key with its kids in `~(rep in kids)` order) and the product',
         'of the library\'s `(tarjan g)`, each set as a list in `rep in` order, `none` on a crash.',
         'The checks are `lemmas/Ska/TarjanCheck.lean`.', '-/', '',
         'namespace Formalization', 'namespace Tarjan', '']
    names = []
    for c in range(0, n, CH):
        nm = 'tjDump%d' % (c // CH); names.append(nm)
        L.append('def %s : List (Nat × Gr Nat × Option (List (List Nat))) := [' % nm)
        L.append(',\n'.join(rows[c:c + CH]) + ']')
        L.append('')
    L.append('def tjDump : List (Nat × Gr Nat × Option (List (List Nat))) :=')
    L.append('  ' + ' ++ '.join(names))
    L += ['', 'end Tarjan', 'end Formalization', '']
    open('lemmas/Ska/TarjanData.lean', 'w').write('\n'.join(L))
    from collections import Counter
    c = Counter(k.split('-0')[0] if k.startswith('random') else k for k in kinds)
    sys.stderr.write('%d cases: %s\n' % (n, ', '.join('%s %d' % kv for kv in sorted(c.items()))))
    crashes = [i for i in range(n) if decode(res[i])[1] is None]
    sys.stderr.write('crashes: %s\n' % crashes)


def trim(path):
    res = records(path)
    for k in sorted(res):
        print('[%%tj %d %d]' % (k, res[k]))


if __name__ == '__main__':
    {'hoon': hoon, 'lean': lean, 'trim': trim}[sys.argv[1]](sys.argv[2])
