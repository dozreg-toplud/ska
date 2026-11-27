#!/usr/bin/env python3
"""+run-shape of the real library against the model `runShape` (lemmas/Ska/RunShape.lean).

usage:
  runshapecheck.py hoon OUT.hoon         the driver (tools/hoon/runshape.hoon)
  runshapecheck.py lean DUMP OUT.lean    the #guards (lemmas/Ska/RunShapeCheck.lean)
  runshapecheck.py agree DUMP OUT.lean   step 3: runShape against runLC (lemmas/Ska/RunShapeAgree.lean)

The driver calls the gate `~(run-shape cmp gen)` of the library with its samples replaced by
raw nouns (`.*` of the gate core, the door's sample `[scc long-ska jets-hot map-local top b]`
and `gen` edited), so no library type is used on the inputs.  The environment: five bells
A..E (see ENV below) with code entries, A B C E in the SCC, D outside it with an n-ary entry;
map-local holds A and E, top holds B, sure.cache holds A and E; no jets.
Each case prints `[%rs name laze id-gen sofs]`, the sets as lists in the order of +rep:in.
"""
import random, re, sys

def cord(s):
    return int.from_bytes(s.encode(), 'little')

T_THIS, T_NONE, T_BOTH, T_MEAN = cord('this'), cord('none'), cord('both'), cord('mean')
TAG = {T_THIS: 'this', T_NONE: 'none', T_BOTH: 'both'}
HINTS_S = ['bout', 'xray', 'memo', 'fast', 'spot']     # static: bout xray are hint-static
HINTS_D = ['spot', 'slog', 'hunk', 'mean', 'memo', 'fast', 'bout', 'live']

# needs (ordered): 'none' 'this' ('both',h,t) ('pair',p,q)
def nedN(n):
    if n == 'none': return (T_NONE, 0)
    if n == 'this': return (T_THIS, 0)
    if n[0] == 'both': return (T_BOTH, (nedN(n[1]), nedN(n[2])))
    return (nedN(n[1]), nedN(n[2]))

def nedL(n):
    if n == 'none': return 'NeedOrd.none'
    if n == 'this': return 'NeedOrd.this'
    if n[0] == 'both': return f'(NeedOrd.both {nedL(n[1])} {nedL(n[2])})'
    return f'(NeedOrd.pair {nedL(n[1])} {nedL(n[2])})'

# a laze: (ned, lok-list, forks [((oy,l),(on,l))], bonds [(o,l)])
def lz(ned='none', lok=(), fork=(), bond=()):
    return (ned, tuple(lok), tuple(fork), tuple(bond))

def dots(n):
    s = str(n)
    if len(s) <= 3: return s
    g = []
    while s:
        g.append(s[-3:]); s = s[:-3]
    return '.'.join(reversed(g))

def hoonN(x):
    if isinstance(x, tuple): return f'[{hoonN(x[0])} {hoonN(x[1])}]'
    return dots(x)

def lazH(l):
    ned, lok, fork, bond = l
    lk = '~' if not lok else '(silt `(list @)`~[' + ' '.join(map(dots, lok)) + '])'
    fk = '~' if not fork else '~[' + ' '.join(f'[[{dots(a)} {lazH(y)}] [{dots(b)} {lazH(n)}]]' for (a, y), (b, n) in fork) + ']'
    bd = '~' if not bond else '~[' + ' '.join(f'[{dots(o)} {lazH(x)}]' for o, x in bond) + ']'
    return f'[[{hoonN(nedN(ned))} {lk}] {fk} {bd}]'

def lazL(l):
    ned, lok, fork, bond = l
    fk = ', '.join(f'(({a}, {lazL(y)}), ({b}, {lazL(n)}))' for (a, y), (b, n) in fork)
    bd = ', '.join(f'({o}, {lazL(x)})' for o, x in bond)
    return f'(Laze.mk ⟨{nedL(ned)}, ⟨[{", ".join(map(str, lok))}]⟩⟩ [{fk}] [{bd}])'

# nouns in Lean
def nounL(x):
    if isinstance(x, tuple): return f'(C {nounL(x[0])} {nounL(x[1])})'
    return f'(A {x})'

# nomms as nouns
def n0(a): return (0, a)
def n1(k): return (1, k)
def n2(p, q, info=None): return (2, (p, (q, 0 if info is None else (0, info))))
def n3(p): return (3, p)
def n4(p): return (4, p)
def n5(p, q): return (5, (p, q))
def n6(p, q, r): return (6, (p, (q, r)))
def n7(p, q): return (7, (p, q))
def n10(a, v, q): return (10, ((a, v), q))
def n11s(t, q): return (11, (cord(t), (q, 0)))
def n11d(t, h, q): return (11, ((cord(t), h), (q, 0)))
def n12(p, q): return (12, (p, q))
def mean(p, b, q, k=None): return (T_MEAN, (p, (b, (q, (0, 0 if k is None else (0, k))))))

def capeL(c):
    if c == 0: return 'Cape.yes'
    if c == 1: return 'Cape.no'
    return f'(Cape.cell {capeL(c[0])} {capeL(c[1])})'

def bellL(b):
    (cape, data), fol = b
    return f'(⟨Sock.mk {capeL(cape)} {nounL(data)}, {nounL(fol)}⟩ : Bell)'

def unitL(u, f):
    return 'Option.none' if u == 0 else f'(some {f(u[1])})'

def nommL(x):
    h, t = x
    if isinstance(h, tuple): return f'(Nomm.cons {nommL(h)} {nommL(t)})'
    if h == 0: return f'(Nomm.n0 {t})'
    if h == 1: return f'(Nomm.n1 {nounL(t)})'
    if h == 2:
        p, (q, info) = t
        inf = 'Option.none' if info == 0 else f'(some ({bellL(info[1][0])}, {unitL(info[1][1], nounL)}))'
        return f'(Nomm.n2 {nommL(p)} {nommL(q)} {inf})'
    if h == 3: return f'(Nomm.n3 {nommL(t)})'
    if h == 4: return f'(Nomm.n4 {nommL(t)})'
    if h == 5: return f'(Nomm.n5 {nommL(t[0])} {nommL(t[1])})'
    if h == 6: return f'(Nomm.n6 {nommL(t[0])} {nommL(t[1][0])} {nommL(t[1][1])})'
    if h == 7: return f'(Nomm.n7 {nommL(t[0])} {nommL(t[1])})'
    if h == 10: return f'(Nomm.n10 {t[0][0]} {nommL(t[0][1])} {nommL(t[1])})'
    if h == 11:
        p, (q, body) = t
        if isinstance(p, tuple): return f'(Nomm.n11d {p[0]} {nommL(p[1])} {nommL(q)} {nounL(body)})'
        return f'(Nomm.n11s {p} {nommL(q)} {nounL(body)})'
    if h == 12: return f'(Nomm.n12 {nommL(t[0])} {nommL(t[1])})'
    if h == T_MEAN:
        p, (b, (q, (body, k))) = t
        return f'(Nomm.mean {nommL(p)} {bellL(b)} {nommL(q)} {nounL(body)} {unitL(k, nounL)})'
    raise ValueError(x)

# the environment
L0 = (1, 0)
BA = (L0, (0, 2)); BB = (L0, (0, 3)); BC = (L0, (0, 6)); BD = (L0, (0, 7))
BE = (((0, 1), (5, 0)), (0, 14))
BELLS = [BA, BB, BC, BD, BE]
ENV = {  # bell: (code nomm, pure, need, sure)
    BA: (((0, 2), (0, 3)), True, ('pair', 'this', 'none'), 'this'),
    BB: ((0, 6), False, ('both', 'this', 'none'), 'none'),
    BC: ((1, 5), True, 'none', 'none'),
    BD: ((0, 1), True, 'this', 'none'),
    BE: (((0, 6), (0, 7)), False, ('pair', 'none', ('pair', 'this', 'this')), ('pair', 'none', 'this')),
}

# goals
G_THIS = lz('this')
G_PAIR = lz(('pair', 'this', 'none'))
G_LOK = lz('none', [6])
G_BOTH = lz(('both', 'this', ('pair', 'none', 'this')), [3])
G_FORK = lz('none', [], [((10, lz('this')), (11, lz(('pair', 'none', 'this'))))])
G_BOND = lz('this', [], [], [(20, lz(('pair', 'this', 'none')))])
G_SOFT = lz('none', [], [], [(30, lz(('pair', 'this', 'this'))), (21, lz('none', [7]))])
G_FB = lz(('pair', 'none', 'this'), [2], [((12, lz('none', [6], [], [(22, lz('this'))])), (13, lz('this')))],
          [(23, lz('none', [], [((14, lz(('pair', 'this', 'none'))), (15, lz('none')))]))])
G_BIG = lz('none', [], [], [(1000 + i, lz('this')) for i in range(520)])
NEXTS = [G_THIS, G_PAIR, G_LOK, G_BOTH, G_FORK, G_BOND, G_SOFT, G_FB]
GOALS = [('done',), ('pick',)] + [('next', g) for g in NEXTS]

def goalH(g):
    if g[0] == 'done': return '[%done ~]'
    if g[0] == 'pick': return '[%pick ~]'
    return f'[%next {lazH(g[1])}]'

def goalL(g):
    if g[0] == 'done': return 'GoalS.done'
    if g[0] == 'pick': return 'GoalS.pick'
    return f'(GoalS.next {lazL(g[1])})'

def cases():
    out = []
    def add(nom, goal, sup=None, idg=100, sofs=(30,)):
        out.append((f'c{len(out):03d}', nom, goal, sup, idg, tuple(sofs)))
    leaves = [n0(0), n0(1), n0(2), n0(3), n0(6), n0(13), n1(7), n1((1, 2))]
    for nom in leaves:
        for g in GOALS: add(nom, g)
    small = [n0(2), n0(7), n1(0), (n0(2), n0(3)), n4(n0(3))]
    for g in GOALS:
        add((n0(2), n0(3)), g)
        add((n0(6), (n0(14), n1(0))), g)
        add(n7(n0(3), (n0(2), n0(1))), g)
        add(n7((n0(3), n0(2)), n0(2)), g, sup=n0(5))
        add(n3(n0(2)), g); add(n4(n0(6)), g); add(n5(n0(2), n0(3)), g); add(n12(n0(2), n0(7)), g)
        add(n10(6, n0(3), n0(1)), g); add(n10(1, n0(2), n0(3)), g); add(n10(13, n4(n0(2)), n0(6)), g)
        add(n2(n0(2), n0(3)), g)
        for b in BELLS:
            add(n2(n0(1), n0(2), (b, 0)), g)
        add(n2((n0(6), n0(7)), n1(0), (BE, 0)), g)
        add(n2(n0(7), n0(2), (BA, (0, (1, 2)))), g)
        add(n2(n0(7), n0(2), (BD, (0, 5))), g)
        add(n2(n0(1), n0(2), (BE, 0)), g, sup=n0(3))
        add(n2(n11d('spot', n1(0), n0(6)), n0(2), (BA, 0)), g)
        add(n11s('bout', n0(6)), g); add(n11s('memo', n0(6)), g)
        add(n11d('spot', n1(0), n0(6)), g); add(n11d('memo', n1(0), n0(6)), g)
        add(n11d('fast', n0(2), n0(6)), g); add(n11d('slog', n0(7), (n0(2), n0(3))), g)
        add(mean(n0(6), BA, n0(7)), g); add(mean(n0(6), BD, n0(7), 9), g); add(mean((n0(6), n0(7)), BE, n0(2)), g)
        # %6 in each phase
        add(n6(n0(2), n0(6), n0(7)), g)
        add(n6(n0(2), (n0(6), n0(7)), (n0(6), n1(0))), g)
        add(n6(n0(2), n4(n0(6)), n4(n0(7))), g)
        add(n6(n3(n0(2)), (n0(12), n0(13)), (n0(13), n0(12))), g)
        add(n6(n11d('spot', n1(0), n0(2)), n0(6), n0(7)), g)
        add(n6(n0(2), n2(n0(1), n0(2), (BE, 0)), n0(3)), g)
        add(n6(n0(2), n0(3), n0(3)), g)
    for g in [('next', G_BIG)]:
        add((n0(2), n0(3)), g); add(n6(n0(2), n0(6), n0(7)), g); add(n6(n0(2), (n0(6), n0(7)), (n0(7), n0(6))), g)
    rnd = random.Random(7)
    def rn(d):
        k = rnd.randrange(16 if d > 0 else 3)
        ax = [1, 2, 3, 6, 7, 12, 13, 14, 15, 0]
        if k == 0 or d == 0 and k == 2: return n0(rnd.choice(ax))
        if k == 1: return n1(rnd.choice([0, 3, (1, 2)]))
        if k == 2: return n0(rnd.choice(ax))
        if k == 3: return (rn(d - 1), rn(d - 1))
        if k == 4: return n2(rn(d - 1), rn(d - 1), rnd.choice([None, None] + [(b, 0) for b in BELLS] + [(BA, (0, 4))]))
        if k == 5: return n3(rn(d - 1))
        if k == 6: return n4(rn(d - 1))
        if k == 7: return n5(rn(d - 1), rn(d - 1))
        if k in (8, 9): return n6(rn(d - 1), rn(d - 1), rn(d - 1))
        if k == 10: return n7(rn(d - 1), rn(d - 1))
        if k == 11: return n10(rnd.choice([1, 2, 3, 6, 7, 13]), rn(d - 1), rn(d - 1))
        if k == 12: return n11s(rnd.choice(HINTS_S), rn(d - 1))
        if k == 13: return n11d(rnd.choice(HINTS_D), rn(d - 1), rn(d - 1))
        if k == 14: return n12(rn(d - 1), rn(d - 1))
        return mean(rn(d - 1), rnd.choice(BELLS), rn(d - 1), rnd.choice([None, 4]))
    for i in range(220):
        add(rn(rnd.choice([2, 3, 3, 4])), rnd.choice(GOALS), sup=rnd.choice([None, None, n0(2)]),
            sofs=rnd.choice([(), (30,), (30, 22)]))
    return out

PRE = r'''
=/  pre
  |=  [t=* acc=*]
  ^-  *
  ?@  t  acc
  ?>  ?=([* * *] t)
  [-.t $(t +<.t, acc $(t +>.t))]
=/  plain
  |=  l=*
  ^-  *
  ?>  ?=([[* *] * *] l)
  =/  fk=*  +<.l
  =/  bd=*  +>.l
  :+  [-<.l (pre ->.l 0)]
    |-  ^-  *
    ?@  fk  0
    ?>  ?=([[[* *] [* *]] *] fk)
    [[[-<-.fk ^$(l -<+.fk)] [->-.fk ^$(l ->+.fk)]] $(fk +.fk)]
  |-  ^-  *
  ?@  bd  0
  ?>  ?=([[* *] *] bd)
  [[-<.bd ^$(l ->.bd)] $(bd +.bd)]
=/  ax  |=([a=@ n=*] .*(n [0 a]))
'''

def hoon_driver():
    cs = cases()
    L = [':: +run-shape on raw samples, written by tools/gen/runshapecheck.py; do not edit by hand.',
         ':: Each case prints [%rs name laze id-gen sofs], the sets as lists (order of +rep:in).']
    L.append(PRE)
    for nm, b in zip('ABCDE', BELLS):
        L.append(f'=/  b{nm.lower()}=*  {hoonN(b)}')
    ents = ' '.join(f'[b{nm.lower()} [{hoonN(ENV[b][0])} {"&" if ENV[b][1] else "|"} &]]' for nm, b in zip('ABCDE', BELLS))
    L.append(f'=/  code=*  (~(gas by *(map * *)) `(list [* *])`~[{ents}])')
    L.append('=/  scc=*  (silt `(list *)`~[ba bb bc be])')
    L.append(f'=/  ml=*  (~(gas by *(map * *)) `(list [* *])`~[[ba [{hoonN(nedN(ENV[BA][2]))} 0 ~]] [be [{hoonN(nedN(ENV[BE][2]))} 0 ~]]])')
    L.append(f'=/  top=*  (~(gas by *(map * *)) `(list [* *])`~[[bb {hoonN(nedN(ENV[BB][2]))}]])')
    L.append(f'=/  nary=*  (~(gas by *(map * *)) `(list [* *])`~[[bd [{hoonN(nedN(ENV[BD][2]))} 0 ~]]])')
    L.append(f'=/  sure=*  (~(gas by *(map * *)) `(list [* *])`~[[ba {hoonN(nedN(ENV[BA][3]))}] [be {hoonN(nedN(ENV[BE][3]))}]])')
    L.append('=/  lon=*  [code jets.long-ska.state ~]')
    L.append('=/  cmp  (comp *(set bell) [code jets calls]:long-ska.state ~ ~ ~ *bell)')
    L.append('=/  g=*  ~(run-shape cmp *line-short)')
    L.append('=/  ctx=*  [(ax 62 g) [[scc lon ~ ml top ba] (ax 127 g)]]')
    L.append('=/  run')
    L.append('  |=  [nam=@tas sam=* idg=@ sofs=*]')
    L.append('  ^-  @')
    L.append('  =/  gen=*  [0 1 idg %drop ~ ~ ~ [nary ~ ~ ~ sure] ~ sofs]')
    L.append('  =/  res=*  .*([(ax 2 g) [sam [(ax 14 g) [gen ctx]]]] [9 2 0 1])')
    L.append('  ~&  [%rs nam `*`[(plain (ax 2 res)) (ax 14 (ax 3 res)) (pre (ax 1.023 (ax 3 res)) 0)]]')
    L.append('  0')
    for nm, nom, goal, sup, idg, sofs in cs:
        sp = '~' if sup is None else f'[~ {hoonN(sup)}]'
        so = '~' if not sofs else '(silt `(list @)`~[' + ' '.join(map(str, sofs)) + '])'
        L.append(f'=+  (run %{nm} [{hoonN(nom)} {goalH(goal)} {sp}] {idg} {so})')
    L.append('0')
    return '\n'.join(L) + '\n'

def tokens(s):
    for m in re.finditer(r'\[|\]|%[a-z0-9-]+|[0-9][0-9.]*', s):
        yield m.group(0)

def parse(toks):
    t = next(toks)
    if t == '[':
        items = []
        while True:
            x = parse(toks)
            if x == ']': break
            items.append(x)
        r = items[-1]
        for x in reversed(items[:-1]): r = (x, r)
        return r
    if t == ']': return ']'
    if t.startswith('%'): return t
    return int(t.replace('.', ''))

def dump(path):
    toks = list(tokens(open(path).read()))
    res = {}
    i = 0
    while i < len(toks):
        if toks[i] == '[' and i + 1 < len(toks) and toks[i + 1] == '%rs':
            it = iter(toks[i:])
            x = parse(it)
            nam = x[1][0][1:]
            res[nam] = x[1][1]
            i += 1
        else:
            i += 1
    return res

def lst(n):
    out = []
    while n != 0:
        out.append(n[0]); n = n[1]
    return out

def listNoun(xs):
    r = 0
    for x in reversed(xs): r = (x, r)
    return r

def normLaze(l):
    """The dumped laze with each set (a list) sorted: the noun the model's `normN` gives."""
    (ned, lok), (fk, bd) = l
    def forks(f):
        if f == 0: return 0
        ((oy, y), (on, n)), rest = f
        return (((oy, normLaze(y)), (on, normLaze(n))), forks(rest))
    def bonds(b):
        if b == 0: return 0
        (o, x), rest = b
        return ((o, normLaze(x)), bonds(rest))
    return ((ned, listNoun(sorted(set(lst(lok))))), (forks(fk), bonds(bd)))

HEAD = '''import lemmas.Ska.RunShape

/-!
# `+run-shape` against the real compiler

Generated by `tools/gen/runshapecheck.py lean` from the output of `tools/hoon/runshape.hoon`
(2026-11-27): for each case the nomm, the goal, `sup`, `id-gen` and `sofs`, and what the
library's `+run-shape` returned (the `laze`, `id-gen` and `sofs` of the new `gen`).  The sets
are lists (`RL`), compared sorted (`normN`).
-/

set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp
namespace RunShapeCheck

open Nock Compiler Laze

/-- A set as a list without repeats. -/
structure RL where
  l : List Nat

instance : HoonSet RL where
  empty := ⟨[]⟩
  toList s := s.l
  put s x := if x ∈ s.l then s else ⟨s.l ++ [x]⟩
  uni a b := ⟨a.l ++ b.l.filter (fun x => x ∉ a.l)⟩
  isEmpty s := s.l.isEmpty
  small s := s.l.all (· == 1)
  toNoun _ := A 0
  mem_empty x := by simp
  mem_put s x y := by
    show y ∈ (if x ∈ s.l then s else (⟨s.l ++ [x]⟩ : RL)).l ↔ y = x ∨ y ∈ s.l
    by_cases h : x ∈ s.l
    · simp only [h, if_true]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact h
        · exact h'
    · simp only [h, if_false, List.mem_append, List.mem_singleton]
      exact Or.comm
  mem_uni a b y := by
    show y ∈ a.l ++ b.l.filter (fun x => x ∉ a.l) ↔ _
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    by_cases h : y ∈ a.l <;> simp [h]
  isEmpty_iff s := by simp [List.isEmpty_iff]
  small_iff s := by simp
  toNoun_empty := rfl

/-- A sorted list as a noun. -/
def sortN (l : List Nat) : Noun := listNoun A ((l.eraseDups).mergeSort (fun a b => decide (a ≤ b)))

mutual
/-- The noun of a `laze` with its sets sorted. -/
def normN : Laze RL → Noun
  | mk s f b => C (C s.ned.toNoun (sortN s.lok.l)) (C (normF f) (normB b))
def normF : List ((Nat × Laze RL) × (Nat × Laze RL)) → Noun
  | [] => A 0
  | ((oy, ly), (on, ln)) :: rest => C (C (C (A oy) (normN ly)) (C (A on) (normN ln))) (normF rest)
def normB : List (Nat × Laze RL) → Noun
  | [] => A 0
  | (o, l) :: rest => C (C (A o) (normN l)) (normB rest)
end

'''

def envL():
    L = []
    for nm, b in zip('ABCDE', BELLS):
        L.append(f'def bell{nm} : Bell := {bellL(b)}')
    def sel(f, dflt):
        s = dflt
        for nm, b in reversed(list(zip('ABCDE', BELLS))):
            s = f'if b = bell{nm} then {f(ENV[b])} else {s}'
        return s
    L.append('/-- The environment of the driver. -/')
    L.append('def rsEnv : ShapeEnv where')
    L.append(f'  need b := {sel(lambda e: "some " + nedL(e[2]), "Option.none")}')
    L.append(f'  sure b := {sel(lambda e: nedL(e[3]), "NeedOrd.none")}')
    L.append('  jet _ := false')
    L.append(f'  pure b := {sel(lambda e: "some " + ("true" if e[1] else "false"), "Option.none")}')
    L.append(f'  cod b := {sel(lambda e: "some " + nommL(e[0]), "Option.none")}')
    L.append('')
    L.append('/-- The output: the laze with sorted sets, `id-gen`, `sofs` sorted. -/')
    L.append('def rsOut (o : Option (Laze RL × RSt RL)) : Option (Noun × Nat × Noun) :=')
    L.append('  o.map fun (l, st) => (normN l, st.idg, sortN st.sofs.l)')
    L.append('')
    return '\n'.join(L)

def lean_check(dpath, out):
    d = dump(dpath)
    cs = cases()
    L = [HEAD, envL()]
    miss = 0
    for nm, nom, goal, sup, idg, sofs in cs:
        if nm not in d:
            miss += 1
            continue
        laz, (idg2, sofs2) = d[nm]
        exp = f'some ({nounL(normLaze(laz))}, {idg2}, {nounL(listNoun(sorted(set(lst(sofs2)))))})'
        sp = 'Option.none' if sup is None else f'(some {nommL(sup)})'
        L.append(f'-- {nm}')
        L.append(f'#guard rsOut (runShape rsEnv {sp} {nommL(nom)} {goalL(goal)} ⟨{idg}, ⟨[{", ".join(map(str, sofs))}]⟩⟩) =')
        L.append(f'  {exp}')
    L.append('\nend RunShapeCheck\nend Comp\nend SkaModel\nend Formalization')
    open(out, 'w').write('\n'.join(L) + '\n')
    print(f'{len(cs) - miss} guards, {miss} cases missing from the dump', file=sys.stderr)

if __name__ == '__main__':
    if sys.argv[1] == 'hoon':
        open(sys.argv[2], 'w').write(hoon_driver())
        print(len(cases()), 'cases', file=sys.stderr)
    elif sys.argv[1] == 'lean':
        lean_check(sys.argv[2], sys.argv[3])
