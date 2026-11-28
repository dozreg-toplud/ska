#!/usr/bin/env python3
"""Write lemmas/Ska/CompRingCheck.lean from the output of tools/hoon/ringdump.hoon
(track K, README Gaps 19 (h)): for every case of part A, the whole-subject
code that finishLUCMR makes from the dumped nomm and the n-ary code that
finishLFCR makes from the dumped inlined nomm, the dumped need and less, as
`#guard`s against the raw blocks of +compiled-mono and +compiled-nary,
compared as NOUNS (`C (A k) blob.toNoun` against the dumped `[k blob]`).

usage: ringcheck.py DUMP.out > lemmas/Ska/CompRingCheck.lean
"""
import sys, re

txt = open(sys.argv[1]).read()
# the harness evaluates twice: keep the first evaluation
i1 = txt.index('[%cole-a')
i2 = txt.find('[%cole-a', i1 + 1)
txt = txt[i1:i2 if i2 > 0 else len(txt)]

toks = re.findall(r'\[|\]|[^\s\[\]]+', txt)
pos = 0
def parse():
    global pos
    t = toks[pos]; pos += 1
    if t == '[':
        l = []
        while toks[pos] != ']':
            l.append(parse())
        pos += 1
        return l
    return t
entries = []
while pos < len(toks):
    entries.append(parse())

def word(w):
    if isinstance(w, str) and re.fullmatch(r'[0-9.]+', w):
        return int(w.replace('.', ''))
    if w == '~':
        return 0
    return w
def noun(x):
    """a parsed raw print as a noun: an int or a pair"""
    if isinstance(x, list):
        assert len(x) >= 2, x
        xs = [noun(y) for y in x]
        r = xs[-1]
        for y in reversed(xs[:-1]):
            r = (y, r)
        return r
    v = word(x)
    assert isinstance(v, int), x
    return v

def lean(n):
    if isinstance(n, int):
        return f'(A {n})'
    return f'(C {lean(n[0])} {lean(n[1])})'

def lst(n):
    out = []
    while n != 0:
        out.append(n[0]); n = n[1]
    return out

def nomm(n):
    """Nomm.toNoun inverted"""
    h, t = n
    if isinstance(h, tuple):
        return f'(Nomm.cons {nomm(h)} {nomm(t)})'
    if h == 0: return f'(Nomm.n0 {t})'
    if h == 1: return f'(Nomm.n1 {lean(t)})'
    if h == 2:
        p, (q, info) = t
        if info == 0:
            inf = 'Option.none'
        else:
            b, k = info[1]
            kk = 'Option.none' if k == 0 else f'(some {lean(k[1])})'
            inf = f'(some (bellN {lean(b)}, {kk}))'
        return f'(Nomm.n2 {nomm(p)} {nomm(q)} {inf})'
    if h == 3: return f'(Nomm.n3 {nomm(t)})'
    if h == 4: return f'(Nomm.n4 {nomm(t)})'
    if h == 5: return f'(Nomm.n5 {nomm(t[0])} {nomm(t[1])})'
    if h == 6: return f'(Nomm.n6 {nomm(t[0])} {nomm(t[1][0])} {nomm(t[1][1])})'
    if h == 7: return f'(Nomm.n7 {nomm(t[0])} {nomm(t[1])})'
    if h == 10: return f'(Nomm.n10 {t[0][0]} {nomm(t[0][1])} {nomm(t[1])})'
    raise ValueError(h)

# the arms and their rings: [/mm axe]
def hn(s):
    toks2 = re.findall(r'\[|\]|[^\s\[\]]+', s)
    global toks, pos
    sv = (toks, pos); toks, pos = toks2, 0
    r = noun(parse()); toks, pos = sv
    return r
ma = hn('[6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [0 3]]')
mb = hn('[4 [9 4 [0 1]]]')
mc = hn('[[9 4 [0 1]] [9 10 [0 1]]]')
mm = 0x6d6d
axes = {}

cases = {}
order = []
cur = None
for e in entries:
    if not isinstance(e, list) or len(e) < 2 or not isinstance(e[0], str):
        continue
    tag, kind = e[0], e[1]
    m = re.fullmatch(r'%(r[a-z])(?:-(mono|nary|callee))?', tag)
    if not m:
        continue
    nam, part = m.group(1), m.group(2)
    c = cases.setdefault(nam, {'mono': [], 'nary': [], 'callees': []})
    if nam not in order: order.append(nam)
    if part is None:
        if kind == '%rawnomm':
            c['nomm'] = noun(e[2]); c['less'] = noun(e[4])
        elif kind == '%rawinl':
            c['inl'] = noun(e[2])
        elif kind == '%rawcalleeinl':
            ui = noun(e[2])
            if ui != 0:
                c['callees'][-1]['nomm'] = ui[1]
                c['callees'][-1]['inl'] = True
        elif kind == '%rawcallee':
            un = noun(e[3])
            c['callees'].append({'bell': noun(e[2]), 'blocks': [], 'nomm': un[1] if un != 0 else None})
        continue
    tgt = c['callees'][-1] if part == 'callee' else c[part] if False else None
    if part == 'callee':
        d = c['callees'][-1]
    else:
        d = c.setdefault(part + 'd', {'blocks': []})
    if kind == '%need':
        d['nargs'] = int(word(e[-1]))
    elif kind == '%rawneed':
        d['need'] = noun(e[2])
    elif kind == '%raw':
        d['blocks'].append(noun(e[2]))

def ringOf(bell):
    fol = bell[1]
    for f, ax in ((ma, 4), (mb, 10), (mc, 11)):
        if fol == f:
            return ((mm, 0), ax)
    raise ValueError('no ring for callee')

out = []
w = out.append
w('''import lemmas.Ska.CompRingRunEq
import lemmas.Ska.CompCall

/-!
# The direct call through a ring against the real compiler (generated)

Written by `tools/gen/ringcheck.py` from the output of `tools/hoon/ringdump.hoon` (track K,
README Gaps 19 (h), 2026-11-28); do not edit by hand.

The core `[[ma [mb mc]] 1 2 0]` is registered by `%fast` (`/mm`) before any compile, so its arms
get the rings `[/mm 4]`, `[/mm 10]`, `[/mm 11]` at the analysis that first sees them; `ma =
[6 [3 [0 3]] [9 4 [10 [3 [0 7]] [0 1]]] [0 3]]` recurs on the tail of its payload, `mb = [4 [9
4 [0 1]]]`, `mc = [[9 4 [0 1]] [9 10 [0 1]]]`.  The roots, each `[7 [0 1] X]` on the core:
`rt` a tail call of `ma`, `rn` under `%4`, `rc` / `rk` in the head / tail of a cons, `rp` as the
test of a `%6`, `rb` in a branch of a `%6`, `rm` a tail call of `mb`, `rx` a tail call of `mc`.

For each root, `ringMono` (`finishLUCMR` on the dumped nomm) against the raw blocks of
`+compiled-mono`, `ringNary` (`finishLFCR` on the dumped INLINED nomm, the dumped need and cape,
nothing baked) against those of `+compiled-nary`, and for every callee (`ma`, `mb`, `mc`) its
n-ary code against `nary.cache`.  The environment: each callee's dumped need and its ring, `sure`
`[%none ~]`, impure, not hinted, `sof` false.  The blocks are compared as nouns: the dump's `[k
blob]` against `C (A k) blob.toNoun` of the model, so the ring nouns are the dump's.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

/-- The cape of a noun (`&` is `0`, `|` is `1`). -/
def capeN : Noun → Cape
  | Noun.atom 1 => Cape.no
  | Noun.cell h t => Cape.cell (capeN h) (capeN t)
  | _ => Cape.yes

/-- The bell of a noun `[[cape data] fol]`. -/
def bellN : Noun → Bell
  | Noun.cell (Noun.cell c d) f => ⟨Sock.mk (capeN c) d, f⟩
  | Noun.cell _ f => ⟨Sock.void, f⟩
  | Noun.atom _ => ⟨Sock.void, A 0⟩

/-- The `need-ordered` of a noun. -/
def needOrdN : Noun → NeedOrd
  | Noun.cell (Noun.atom t) r =>
      if t = Tag.this then NeedOrd.this else if t = Tag.none then NeedOrd.none
      else match r with
        | Noun.cell h q => NeedOrd.both (needOrdN h) (needOrdN q)
        | _ => NeedOrd.none
  | Noun.cell p q => NeedOrd.pair (needOrdN p) (needOrdN q)
  | Noun.atom _ => NeedOrd.none

/-- The environment of the dump: the callees' needs and rings (by the noun of the bell). -/
def envRing (cs : List (Noun × Noun × Noun)) : CallEnv :=
  ⟨fun b => (cs.find? (fun c => c.1 == b.toNoun)).map fun c => needOrdN c.2.1,
   fun _ => NeedOrd.none, fun _ => false, fun b => (cs.find? (fun c => c.1 == b.toNoun)).map fun c => c.2.2,
   fun _ => some false, fun _ _ _ _ _ => false⟩

/-- The need, the argument count and the present blocks `[k blob]` below `n`, as nouns. -/
def strOut (c : Straight FM) (n : Nat) : Noun × Nat × List Noun :=
  (c.need.toNoun, c.nargs, (List.range n).filterMap fun k => (c.blocks.f k).map fun bl => C (A k) bl.toNoun)

def ringMono (env : CallEnv) (nm : Nomm) (n : Nat) : Option (Noun × Nat × List Noun) :=
  (finishLUCMR (S := LS) (Map := FM) env nm).map fun c => strOut c n

def ringNary (env : CallEnv) (nm : Nomm) (ord : Noun) (less : Noun) (n : Nat) : Option (Noun × Nat × List Noun) :=
  (finishLFCR (S := LS) (Map := FM) env nm (needOrdN ord) (capeN (match less with | Noun.cell c _ => c | _ => A 0))
    (fun ned => (ned, []))).map fun c => strOut c n
''')

def blocks_out(bl):
    n = max(b[0] for b in bl) + 1
    return n, '[' + ',\n    '.join(lean(b) for b in bl) + ']'

seen_callees = {}
for nam in order:
    c = cases[nam]
    if 'nomm' not in c:
        continue
    cs = []
    for d in c['callees']:
        cs.append(f'({lean(d["bell"])}, {lean(d["need"])}, {lean(ringOf(d["bell"]))})')
    w(f'/-- The environment of `{nam}`. -/')
    w(f'def env_{nam} : CallEnv := envRing [' + ',\n    '.join(cs) + ']\n')
    w(f'/-- The nomm of `{nam}`. -/')
    w(f'def nomm_{nam} : Nomm := {nomm(c["nomm"])}\n')
    inl = c['inl']
    assert inl != 0
    w(f'/-- The inlined nomm of `{nam}` (`inl.cache`). -/')
    w(f'def inl_{nam} : Nomm := {nomm(inl[1])}\n')
    md = c['monod']; n, bl = blocks_out(md['blocks'])
    w(f'/- `{nam}`, the whole-subject code (`+compiled-mono`). -/')
    w(f'#guard ringMono env_{nam} nomm_{nam} {n} ==\n  some ({lean(md["need"])}, {md["nargs"]},\n    {bl})\n')
    nd = c['naryd']; n, bl = blocks_out(nd['blocks'])
    w(f'/- `{nam}`, the n-ary code (`+compiled-nary`). -/')
    w(f'#guard ringNary env_{nam} inl_{nam} {lean(nd["need"])} {lean(c["less"])} {n} ==\n'
      f'  some ({lean(nd["need"])}, {nd["nargs"]},\n    {bl})\n')
    for k, d in enumerate(c['callees']):
        key = repr(d['bell'])
        if key in seen_callees:
            continue
        seen_callees[key] = nam
        cn = d.get('nomm')
        assert d.get('inl'), 'callee without inl entry'
        n, bl = blocks_out(d['blocks'])
        w(f'/- `{nam}`, the n-ary code of its callee {k} (`nary.cache`, from its `inl.cache` nomm). -/')
        w(f'#guard ringNary env_{nam} {nomm(cn)} {lean(d["need"])} {lean(d["bell"][0])} {n} ==\n'
          f'  some ({lean(d["need"])}, {d["nargs"]},\n    {bl})\n')

w('''end Comp
end SkaModel
end Formalization''')
print('\n'.join(out))
