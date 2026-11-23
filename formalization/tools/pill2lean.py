#!/usr/bin/env python3
"""Turn a steel pill into Lean definitions.

    pill2lean.py PILL OUTDIR

writes, under OUTDIR (lemmas/Pill):

  Nouns.lean   one definition per shared cell of the pill's noun and of the
               SKA core that the pill builds, plus named definitions for the
               nouns that the proofs talk about
  Facts.lean   the evaluation of the pill's trap to the core and the axes of
               the named arms, checked by the Lean kernel

The definitions are not trusted where a theorem of Facts.lean ties them to
each other.  One link is missing: nothing checks `cue pill = some root` (the
pill as an atom is core/Pill.lean, made by tools/pill2core.py), so `root` is
the pill's noun on the word of this script.  See the README.
"""
import hashlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nouns as N
from nouns import NODES, atom, cell, cord, head, tail, is_atom, nock, slot

LIMIT = 192          # cells per definition


def reach(roots):
    seen = set()
    todo = list(roots)
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        n = NODES[i]
        if type(n) is tuple:
            todo.extend(n)
    return seen


def find_axis(hay, needle):
    from collections import deque
    q = deque([(hay, 1)])
    seen = {hay}
    while q:
        i, ax = q.popleft()
        if i == needle:
            return ax
        n = NODES[i]
        if type(n) is int:
            continue
        for j, a in ((n[0], 2 * ax), (n[1], 2 * ax + 1)):
            if j not in seen:
                seen.add(j)
                q.append((j, a))
    raise KeyError('not found')


def unlist(i, k):
    """[a b c ... rest] -> the first k heads and the rest"""
    out = []
    for _ in range(k):
        out.append(head(i))
        i = tail(i)
    return out, i


class Emitter:
    def __init__(self, roots, names, formulas):
        """names: node id -> Lean name; formulas: ids written out in full
        (down to other named nodes) rather than through anonymous
        definitions."""
        self.names = dict(names)
        self.user = set(names)
        self.formulas = set(formulas)
        live = reach(roots)
        rc = {}
        for i in live:
            n = NODES[i]
            if type(n) is tuple:
                for j in n:
                    rc[j] = rc.get(j, 0) + 1
        # post-order over the DAG
        post = []
        vis = set()
        st = [(r, 0) for r in roots]
        while st:
            i, ph = st.pop()
            if ph:
                post.append(i)
                continue
            if i in vis:
                continue
            vis.add(i)
            st.append((i, 1))
            n = NODES[i]
            if type(n) is tuple:
                st.append((n[1], 0))
                st.append((n[0], 0))
        defs = set(i for i in live if type(NODES[i]) is tuple and
                   (rc.get(i, 0) > 1 or i in self.names))
        defs.update(r for r in roots if type(NODES[r]) is tuple)
        size = {}
        for i in post:
            n = NODES[i]
            if type(n) is int:
                size[i] = 0
                continue
            s = 1 + sum(0 if (j in defs) else size[j] for j in n)
            if s > LIMIT and i not in defs:
                defs.add(i)
            size[i] = s
        self.post = post
        self.defs = defs
        for i in defs:
            if i not in self.names:
                self.names[i] = 'n%d' % i

    @staticmethod
    def lit(n):
        return str(n) if n < 1 << 16 else hex(n)

    def term(self, i, top, full):
        """Lean term for node i; `top` suppresses the reference to i itself."""
        out = []
        # iterative right-spine printing keeps Python's stack shallow
        def go(i, top, paren):
            n = NODES[i]
            if type(n) is int:
                out.append('(A %s)' % self.lit(n) if paren else 'A %s' % self.lit(n))
                return
            if not top and (i in self.user if full else i in self.defs):
                out.append(self.names[i])
                return
            if paren:
                out.append('(')
            out.append('C ')
            go(n[0], False, True)
            out.append(' ')
            go(n[1], False, True)
            if paren:
                out.append(')')
        go(i, top, False)
        return ''.join(out)

    def emit(self, f):
        named = []
        for i in self.post:
            if i not in self.defs:
                continue
            full = i in self.formulas
            f.write('def %s : Noun := %s\n' % (self.names[i], self.term(i, True, full)))


def find_loops(formula):
    """the L of every [8 [1 L] 9 2 0 1] inside formula"""
    kick = cell(atom(9), cell(atom(2), cell(atom(0), atom(1))))
    out = []
    for i in sorted(reach([formula])):
        n = NODES[i]
        if type(n) is int or NODES[n[0]] != 8:
            continue
        m = NODES[n[1]]
        if type(m) is int or m[1] != kick:
            continue
        q = NODES[m[0]]
        # a tape literal compiles to the same shape with a constant for L
        if type(q) is tuple and NODES[q[0]] == 1 and NODES[head(q[1])] != 1:
            out.append(q[1])
    return out


def main():
    pill, outdir = sys.argv[1], sys.argv[2]
    data = open(pill, 'rb').read()
    sha = hashlib.sha256(data).hexdigest()
    root = N.cue(data)
    assert N.jam(root) == int.from_bytes(data, 'little')
    (tag, nok, trap), nil = unlist(root, 3)
    assert NODES[tag] == cord('steel') and NODES[nil] == 0
    N.STEPS = 0
    core = nock(cell(trap, atom(0)), nok)
    steps = N.STEPS

    # ---- the nouns that the proofs name
    names = {root: 'root', nok: 'nok', trap: 'trap', core: 'core'}
    formulas = set()
    facts = []
    live = reach([core])
    FAST = cord('fast')

    def hint_of(label):
        res = []
        for i in live:
            n = NODES[i]
            if type(n) is int or NODES[n[0]] != 11:
                continue
            hb = NODES[n[1]]
            if type(hb) is int:
                continue
            h = NODES[hb[0]]
            if type(h) is int or NODES[h[0]] != FAST:
                continue
            clue = NODES[h[1]]
            if type(clue) is int or NODES[clue[0]] != 1:
                continue
            if NODES[NODES[clue[1]][0]] == cord(label):
                res.append(i)
        assert len(res) == 1, (label, res)
        return res[0]

    def arms_of(label):
        hint = hint_of(label)
        seven = atom(7)
        res = []
        for i in live:
            n = NODES[i]
            if type(n) is int or n[0] != seven:
                continue
            m = NODES[n[1]]
            if type(m) is tuple and m[1] == hint:
                res.append(i)
        return res

    def gate_battery(arm):
        # [7 [8 [1 sample] [1 battery] 0 1] hint]
        x = head(tail(arm))
        assert NODES[head(x)] == 8
        return tail(head(tail(tail(x))))

    l0 = [i for i in live if type(NODES[i]) is tuple and NODES[tail(i)] == 135
          and type(NODES[head(i)]) is tuple]
    assert len(l0) == 1
    layer0 = l0[0]
    def layer_over(parent, label):
        (a,) = arms_of(label)
        res = []
        for i in live:
            if type(NODES[i]) is tuple and tail(i) == parent:
                try:
                    res.append((find_axis(head(i), a), i))
                except KeyError:
                    pass
        # the core is the candidate whose head holds the arm at the least depth
        res.sort()
        assert res and (len(res) == 1 or res[0][0] < res[1][0]), (label, res)
        return res[0][1]

    layer1 = layer_over(layer0, 'dec')
    layer2 = layer_over(layer1, 'gor')
    names.update({layer0: 'layer0', layer1: 'layer1', layer2: 'layer2',
                  head(layer1): 'layer1.battery', head(layer2): 'layer2.battery'})
    facts.append(('core_layer2', 'slot? %d core = some layer2' % find_axis(core, layer2)))
    facts.append(('layer2_layer1', 'slot? 3 layer2 = some layer1'))

    # (name, axis, statement) for every named arm: Facts.lean defines
    # `name.axis` and proves the statement as `name.arm_at`
    axes = []

    def name(i, nm):
        assert names.get(i, nm) == nm, (nm, names[i])
        names[i] = nm

    def name_loops(label, g, loops):
        """name the loops [8 [1 L] 9 2 0 1] of g: `loops` of them, or all of
        them if `loops` is 'any', or none if it is None"""
        ls = find_loops(g) if loops is not None else []
        if loops != 'any':
            assert loops is None or len(ls) == loops, (label, len(ls))
        for k, l in enumerate(ls):
            # a loop whose Nock is that of a loop named before keeps that name
            if l in names:
                continue
            name(l, label + ('.loop' if len(ls) == 1 else '.loop%d' % k))
            formulas.add(l)

    def arm(label, layer, lname, loops=0, full=True):
        """the arm with %fast label `label` in the battery of `layer`"""
        cands = [a for a in arms_of(label)]
        inside = []
        for a in cands:
            try:
                find_axis(head(layer), a)
                inside.append((find_axis(layer, a), a))
            except KeyError:
                pass
        assert len(inside) == 1, (label, inside)
        ax, a = inside[0]
        name(a, label + '.arm')
        g = gate_battery(a)
        name(g, label + '.battery')
        formulas.add(a)
        if full:
            formulas.add(g)
        name_loops(label, g, loops)
        axes.append((label, ax, 'slot? %s.axis %s = some %s.arm' % (label, lname, label)))
        return a

    def callee(formula, ctx, exclude=()):
        """the axis of the one arm, other than those at the axes in `exclude`,
        that `formula` pulls with [9 axis 0 ctx]"""
        res = set()
        for i in reach([formula]):
            n = NODES[i]
            if type(n) is int or NODES[n[0]] != 9:
                continue
            m = NODES[n[1]]
            if type(m) is int or type(NODES[m[0]]) is not int:
                continue
            if m[1] == cell(atom(0), atom(ctx)) and NODES[m[0]] not in exclude:
                res.add(NODES[m[0]])
        assert len(res) == 1, res
        return res.pop()

    # unsigned arithmetic
    arm('dec', layer1, 'layer1', loops=1)
    arm('add', layer1, 'layer1')
    arm('sub', layer1, 'layer1')
    arm('mul', layer1, 'layer1', loops=1)
    arm('lth', layer1, 'layer1', loops=1)
    arm('lte', layer1, 'layer1')
    arm('gth', layer1, 'layer1')
    arm('gte', layer1, 'layer1')
    arm('max', layer1, 'layer1')
    arm('min', layer1, 'layer1')
    arm('dvr', layer1, 'layer1', loops=1)
    arm('div', layer1, 'layer1')
    arm('mod', layer1, 'layer1')

    # tree addressing
    arm('cap', layer1, 'layer1')
    arm('mas', layer1, 'layer1')
    arm('peg', layer1, 'layer1')

    # noun ordering and hashing
    arm('dor', layer2, 'layer2')
    arm('gor', layer2, 'layer2')
    arm('mor', layer2, 'layer2')
    mug = arm('mug', layer2, 'layer2', loops=1)

    # lists
    for label in ['lent', 'weld', 'snag', 'scag', 'slag', 'turn', 'roll', 'levy',
                  'lien']:
        arm(label, layer2, 'layer2', loops=1)
    flop = arm('flop', layer2, 'layer2', loops=1)
    for label in ['skip', 'murn', 'zing', 'spin', 'skim', 'rear', 'snip', 'sort', 'welp',
                  'skid']:
        arm(label, layer2, 'layer2', loops='any')
    # +homo has no %fast label: it is the arm that +flop pulls from its context
    homo_ax = callee(gate_battery(flop), 7)
    name(slot(homo_ax, layer2), 'homo.arm')
    formulas.add(slot(homo_ax, layer2))
    axes.append(('homo', homo_ax, 'slot? homo.axis layer2 = some homo.arm'))

    # units
    arm('need', layer2, 'layer2')

    # bit arithmetic
    for label in ['bex', 'rsh', 'lsh', 'end', 'cut', 'cat', 'can', 'rip']:
        arm(label, layer2, 'layer2')
    for label in ['met', 'mix', 'dis', 'con']:
        arm(label, layer2, 'layer2', loops=1)

    # +mug: a |^ core [8 [1 [buc mum]] 9 4 0 1], where buc is the recursive arm $
    # and mum the gate that hashes an atom; mug.loop is the loop of mum
    mug_core = tail(head(tail(gate_battery(mug))))
    assert NODES[head(head(tail(gate_battery(mug))))] == 1
    name(head(mug_core), 'mug.buc')
    formulas.add(head(mug_core))
    mum = tail(mug_core)
    name(mum, 'mug.mum.arm')
    formulas.add(mum)
    def is_gate_builder(a):
        """a is [8 [1 bunt] [1 battery] 0 1]"""
        try:
            return (NODES[head(a)] == 8 and NODES[head(head(tail(a)))] == 1
                    and NODES[head(head(tail(tail(a))))] == 1
                    and tail(tail(tail(a))) == cell(atom(0), atom(1)))
        except (TypeError, IndexError):
            return False

    def door_gate_battery(a):
        assert is_gate_builder(a)
        return tail(head(tail(tail(a))))
    name(door_gate_battery(mum), 'mug.mum.battery')
    formulas.add(door_gate_battery(mum))

    # +muk, its loop, and the gate fmix32 of its |^ core
    muk = arm('muk', layer2, 'layer2', loops=1)
    kick4 = cell(atom(9), cell(atom(4), cell(atom(0), atom(1))))
    fmix = []
    for i in reach([gate_battery(muk)]):
        n = NODES[i]
        if type(n) is int or NODES[n[0]] != 8 or type(NODES[n[1]]) is int:
            continue
        q, k = NODES[n[1]]
        if k == kick4 and NODES[head(q)] == 1:
            fmix.append(tail(tail(q)))
    (fmix_arm,) = fmix
    name(door_gate_battery(fmix_arm), 'muk.fmix.battery')
    formulas.add(door_gate_battery(fmix_arm))

    # the door +fe, which +muk builds with [9 fe 0 7], and the arms sit, sum
    # and rol of it, told apart by what their gates pull
    fe_ax = callee(gate_battery(muk), 7)
    fe_arm = slot(fe_ax, layer2)
    name(fe_arm, 'fe.arm')
    formulas.add(fe_arm)
    fe_door = nock(layer2, fe_arm)
    assert tail(tail(fe_door)) == layer2
    name(head(fe_door), 'fe.battery')
    axes.append(('fe', fe_ax, 'slot? fe.axis layer2 = some fe.arm'))
    ax_of = dict((nm, ax) for nm, ax, _ in axes)

    def fe_arms(i, ax, depth=0, limit=12):
        """the arms of a battery: the leaves of its tree of cells whose heads
        are cells, down to a depth `limit` (the battery of layer 2 needs 40)"""
        n = NODES[i]
        if type(NODES[n[0]]) is int or depth >= limit:
            yield ax, i
            return
        yield from fe_arms(n[0], 2 * ax, depth + 1, limit)
        yield from fe_arms(n[1], 2 * ax + 1, depth + 1, limit)

    def pulls(formula):
        """the [axis ctx] of every [9 axis 0 ctx] in formula, in pre-order,
        each subterm visited once"""
        out = []
        seen = set()
        st = [formula]
        while st:
            i = st.pop()
            if i in seen:
                continue
            seen.add(i)
            n = NODES[i]
            if type(n) is int:
                continue
            if NODES[n[0]] == 9 and type(NODES[n[1]]) is tuple:
                m = NODES[n[1]]
                if type(NODES[m[0]]) is int and type(NODES[m[1]]) is tuple \
                        and NODES[head(m[1])] == 0:
                    out.append((NODES[m[0]], NODES[tail(m[1])]))
            st.append(n[1])
            st.append(n[0])
        return out

    found = {}
    for ax, a in fe_arms(head(fe_door), 2):
        if not is_gate_builder(a):
            continue
        ps = pulls(door_gate_battery(a))
        if ps == [(ax_of['end'], 31)]:
            found['sit'] = (ax, a)
    for ax, a in fe_arms(head(fe_door), 2):
        if not is_gate_builder(a):
            continue
        ps = pulls(door_gate_battery(a))
        if sorted(ps) == sorted([(found['sit'][0], 7), (ax_of['add'], 63)]):
            found['sum'] = (ax, a)
        shifts = [x for x, _ in ps if x in (ax_of['lsh'], ax_of['rsh'])]
        if (ax_of['con'], 255) in ps and shifts and shifts[0] == ax_of['lsh']:
            assert 'rol' not in found
            found['rol'] = (ax, a)
    for label in ['sit', 'sum', 'rol']:
        ax, a = found[label]
        name(a, 'fe.%s.arm' % label)
        formulas.add(a)
        name(door_gate_battery(a), 'fe.%s.battery' % label)
        formulas.add(door_gate_battery(a))
        axes.append(('fe.' + label, ax, '∀ x, slot? fe.%s.axis (C fe.battery x) = some fe.%s.arm'
                     % (label, label)))

    # the doors +by and +in, with some of their arms
    def door(label, layer, lname):
        (ax, a), = [(find_axis(layer, a), a) for a in arms_of(label)]
        name(a, label + '.arm')
        formulas.add(a)
        d = nock(layer, a)
        assert tail(tail(d)) == layer and NODES[head(tail(d))] == 0
        name(head(d), label + '.battery')
        axes.append((label, ax, 'slot? %s.axis %s = some %s.arm' % (label, lname, label)))
        return head(d)

    def door_arm(dlabel, battery, label, loops):
        res = []
        for a in arms_of(label):
            try:
                find_axis(battery, a)
                res.append((find_axis(cell(battery, atom(0)), a), a))
            except KeyError:
                pass
        assert len(res) == 1, (dlabel, label, res)
        ax, a = res[0]
        full = dlabel + '.' + label
        if a in names:
            # the same noun as an arm of another door: keep its name
            axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s'
                         % (full, dlabel, names[a])))
            return a
        name(a, full + '.arm')
        formulas.add(a)
        g = gate_battery(a)
        name(g, full + '.battery')
        formulas.add(g)
        name_loops(full, g, loops)
        axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s.arm'
                     % (full, dlabel, full)))
        return a

    by_battery = door('by', layer2, 'layer2')
    door_arm('by', by_battery, 'put', 1)
    get_arm = door_arm('by', by_battery, 'get', 1)
    # +some has no %fast label: it is the arm other than +gor that the loop of
    # +get:by pulls from the context of the door
    (get_loop,) = find_loops(gate_battery(get_arm))
    gor_ax = [ax for nm, ax, _ in axes if nm == 'gor'][0]
    some_ax = callee(get_loop, 63, exclude=(gor_ax,))
    name(slot(some_ax, layer2), 'some.arm')
    formulas.add(slot(some_ax, layer2))
    axes.append(('some', some_ax, 'slot? some.axis layer2 = some some.arm'))
    door_arm('by', by_battery, 'has', 0)
    door_arm('by', by_battery, 'del', 'any')
    for label in ['rep', 'jab', 'uni', 'run', 'dif', 'any', 'int']:
        door_arm('by', by_battery, label, 'any')
    door_arm('by', by_battery, 'gas', 1)

    def door_trap(dlabel, battery, label):
        """an arm [7 [7 [8 [1 bunt] [1 battery] 0 1] hint] 9 2 0 1] of a door:
        a trap whose state is the bunt"""
        kick = cell(atom(9), cell(atom(2), cell(atom(0), atom(1))))
        res = []
        for inner in arms_of(label):
            for ax, a in fe_arms(battery, 2):
                if NODES[head(a)] == 7 and head(tail(a)) == inner and tail(tail(a)) == kick:
                    res.append((ax, a, inner))
        assert len(res) == 1, (dlabel, label, res)
        ax, a, inner = res[0]
        full = dlabel + '.' + label
        name(a, full + '.arm')
        formulas.add(a)
        g = gate_battery(inner)
        name(g, full + '.battery')
        formulas.add(g)
        axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s.arm'
                     % (full, dlabel, full)))

    door_trap('by', by_battery, 'apt')
    door_trap('by', by_battery, 'tap')
    door_trap('by', by_battery, 'key')

    def door_gate_pulling(dlabel, battery, label, want):
        """the unhinted gate arm of a door whose battery pulls exactly `want`"""
        res = []
        for ax, a in fe_arms(battery, 2):
            if is_gate_builder(a) and sorted(pulls(door_gate_battery(a))) == sorted(want):
                res.append((ax, a))
        assert len(res) == 1, (dlabel, label, res)
        ax, a = res[0]
        full = dlabel + '.' + label
        name(a, full + '.arm')
        formulas.add(a)
        name(door_gate_battery(a), full + '.battery')
        formulas.add(door_gate_battery(a))
        axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s.arm'
                     % (full, dlabel, full)))
        return a

    ax_of = dict((nm, ax) for nm, ax, _ in axes)
    door_gate_pulling('by', by_battery, 'got', [(ax_of['need'], 31), (ax_of['by.get'], 7)])
    # +fall has no %fast label: it is the other arm that +gut:by pulls
    gut = None
    for ax, a in fe_arms(by_battery, 2):
        if is_gate_builder(a):
            ps = pulls(door_gate_battery(a))
            if len(ps) == 2 and (ax_of['by.get'], 7) in ps and \
                    [x for x in ps if x[1] == 31 and x[0] != ax_of['need']]:
                assert gut is None
                gut = [x for x in ps if x[1] == 31][0][0]
    name(slot(gut, layer2), 'fall.arm')
    formulas.add(slot(gut, layer2))
    axes.append(('fall', gut, 'slot? fall.axis layer2 = some fall.arm'))
    door_gate_pulling('by', by_battery, 'gut', [(gut, 31), (ax_of['by.get'], 7)])
    in_battery = door('in', layer2, 'layer2')
    door_arm('in', in_battery, 'put', 1)
    for label in ['gas', 'del', 'rep', 'run', 'uni', 'int', 'dif', 'any']:
        door_arm('in', in_battery, label, 'any')
    has_in = door_arm('in', in_battery, 'has', 1)
    # +has:in slams an inner gate [8 [8 [1 0] [1 gate] 0 1] 9 2 10 ...]
    inner = tail(head(tail(tail(head(tail(gate_battery(has_in)))))))
    assert NODES[head(inner)] == 7
    name(inner, 'in.has.gate')
    formulas.add(inner)

    # the doors +ju and +ja have no %fast labels: they are the door arms of
    # layer 2 whose arms pull +by and +in (+ju), or hold the hinted +zip (+ja)
    ax_of = dict((nm, ax) for nm, ax, _ in axes)
    by_ax, in_ax = ax_of['by'], ax_of['in']
    zip_inner = set(arms_of('zip'))
    ju_ja = {}
    for ax, a in fe_arms(head(layer2), 2):
        if not is_gate_builder(a):
            continue
        bat = door_gate_battery(a)
        sub = list(fe_arms(bat, 2))
        if len(sub) < 3:
            continue
        ps = set()
        for _, sa in sub:
            ps.update(pulls(sa))
        if zip_inner & reach([bat]):
            ju_ja.setdefault('ja', []).append((ax, a))
        elif len(sub) == 5 and any(x == by_ax for x, _ in ps) and any(x == in_ax for x, _ in ps):
            ju_ja.setdefault('ju', []).append((ax, a))
    for dlabel in ['ju', 'ja']:
        (ax, a), = ju_ja[dlabel]
        name(a, dlabel + '.arm')
        formulas.add(a)
        name(door_gate_battery(a), dlabel + '.battery')
        axes.append((dlabel, ax, 'slot? %s.axis layer2 = some %s.arm' % (dlabel, dlabel)))

    def door_arm_pulling(dlabel, label, pred, loops):
        """the gate arm of a door without %fast labels whose pulls satisfy pred"""
        battery = [i for i, nm in names.items() if nm == dlabel + '.battery'][0]
        res = []
        for ax, a in fe_arms(battery, 2):
            if is_gate_builder(a) and pred(set(pulls(door_gate_battery(a)))):
                res.append((find_axis(cell(battery, atom(0)), a), a))
        assert len(res) == 1, (dlabel, label, res)
        ax, a = res[0]
        full = dlabel + '.' + label
        if a in names:
            axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s'
                         % (full, dlabel, names[a])))
            return ax
        name(a, full + '.arm')
        formulas.add(a)
        g = door_gate_battery(a)
        name(g, full + '.battery')
        formulas.add(g)
        name_loops(full, g, loops)
        axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s.arm'
                     % (full, dlabel, full)))
        return ax

    ju_get = door_arm_pulling('ju', 'get', lambda ps: ps == {(by_ax, 31)}, 0)
    door_arm_pulling('ju', 'has', lambda ps: ps == {(in_ax, 31), (ju_get, 7)}, 0)
    ju_put = door_arm_pulling('ju', 'put',
                              lambda ps: ps == {(ju_get, 7), (by_ax, 63), (in_ax, 63)}, 0)
    door_arm_pulling('ju', 'del', lambda ps: (by_ax, 127) in ps and (ju_get, 7) in ps, 0)
    door_arm_pulling('ju', 'gas', lambda ps: (ju_put, 15) in ps, 1)
    ja_get = door_arm_pulling('ja', 'get', lambda ps: ps == {(by_ax, 31)}, 0)
    door_arm_pulling('ja', 'add', lambda ps: ps == {(ja_get, 7), (by_ax, 63)}, 0)

    # +wyt of +by and +in (one noun): the trap [7 [8 [1 battery] hint] 9 2 0 1]
    # whose hint has the %fast label wyt
    wyt_hint = hint_of('wyt')
    (wyt_core,) = [i for i in live if type(NODES[i]) is tuple and tail(i) == wyt_hint
                   and type(NODES[head(i)]) is tuple and NODES[head(head(i))] == 1]
    wyt_arm = cell(atom(7), cell(cell(atom(8), wyt_core),
                                 cell(atom(9), cell(atom(2), cell(atom(0), atom(1))))))
    for dlabel, battery in [('by', by_battery), ('in', in_battery)]:
        ax = find_axis(cell(battery, atom(0)), wyt_arm)
        full = dlabel + '.wyt'
        if wyt_arm in names:
            axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s'
                         % (full, dlabel, names[wyt_arm])))
            continue
        name(wyt_arm, full + '.arm')
        formulas.add(wyt_arm)
        name(tail(head(wyt_core)), full + '.battery')
        formulas.add(tail(head(wyt_core)))
        axes.append((full, ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s.arm'
                     % (full, dlabel, full)))

    # +snoc and +biff have no %fast labels: +snoc is the gate arm of layer 2
    # whose battery pulls +weld and nothing else, +biff the gate arm whose
    # battery is ?~(a ~ (b u.a))
    def layer2_gate(label, pred):
        res = [(ax, a) for ax, a in fe_arms(head(layer2), 2, limit=40)
               if is_gate_builder(a) and pred(door_gate_battery(a))]
        assert len(res) == 1, (label, res)
        ax, a = res[0]
        name(a, label + '.arm')
        formulas.add(a)
        name(door_gate_battery(a), label + '.battery')
        formulas.add(door_gate_battery(a))
        axes.append((label, find_axis(layer2, a), 'slot? %s.axis layer2 = some %s.arm'
                     % (label, label)))
    ax_of = dict((nm, ax) for nm, ax, _ in axes)
    layer2_gate('snoc', lambda g: pulls(g) == [(ax_of['weld'], 7)])
    def f0(ax): return cell(atom(0), atom(ax))
    def f1(x): return cell(atom(1), x)
    slam = cell(atom(9), cell(atom(2), cell(atom(10), cell(cell(atom(6), f0(57)), f0(2)))))
    biff_battery = cell(atom(6), cell(cell(atom(5), cell(f1(atom(0)), f0(12))),
                                      cell(f1(atom(0)), cell(atom(8), cell(f0(13), slam)))))
    layer2_gate('biff', lambda g: g == biff_battery)

    # the gate that +sort hands to +skid: the one core [[1 battery] 0 1] that
    # its loop builds
    sort_loop = [i for i, nm in names.items() if nm == 'sort.loop'][0]
    cmp = set(tail(head(i)) for i in reach([sort_loop])
              if type(NODES[i]) is tuple and tail(i) == f0(1)
              and type(NODES[head(i)]) is tuple and NODES[head(head(i))] == 1)
    (cmp,) = cmp
    name(cmp, 'sort.cmp')
    formulas.add(cmp)

    # ---- layers 3 and 4 of hoon.hoon, and +mink with the arms of its |^ core:
    # the loop `$` and the gates `frag` and `edit`
    (mink_a,) = arms_of('mink')
    l4 = [i for i in live if type(NODES[i]) is tuple and type(NODES[head(i)]) is tuple
          and type(NODES[tail(i)]) is tuple and tail(tail(i)) == layer2]
    l4 = [i for i in l4 if type(NODES[head(i)]) is tuple and mink_a in reach([head(i)])]
    (layer4,) = l4
    layer3 = tail(layer4)
    assert tail(layer3) == layer2
    names.update({layer3: 'layer3', layer4: 'layer4'})
    facts.append(('layer4_layer3', 'slot? 3 layer4 = some layer3'))
    facts.append(('layer3_layer2', 'slot? 3 layer3 = some layer2'))
    mink_a = arm('mink', layer4, 'layer4', loops=None)
    # the layer of +cap and +mas, which `frag` and `edit` read
    axes.append(('mink.layer1', 15, 'slot? mink.layer1.axis layer4 = some layer1'))
    assert tail(tail(tail(layer4))) == layer1
    g = gate_battery(mink_a)
    # [8 [1 0] [8 [1 battery] [9 11 0 1]]]: =| trace, then the |^ core
    assert NODES[head(g)] == 8 and tail(head(tail(g))) == atom(0)
    x = tail(tail(g))
    assert tail(tail(x)) == cell(atom(9), cell(atom(11), cell(atom(0), atom(1))))
    mbat = tail(head(tail(x)))
    name(mbat, 'mink.core')
    name(tail(tail(mbat)), 'mink.loop')
    formulas.add(tail(tail(mbat)))
    for lab, a in (('frag', head(mbat)), ('edit', head(tail(mbat)))):
        name(a, 'mink.%s.arm' % lab)
        formulas.add(a)
        gb = door_gate_battery(a)
        name(gb, 'mink.%s.battery' % lab)
        formulas.add(gb)
        name_loops('mink.' + lab, gb, 'any')

    # +monk and +mock, and +mack, the gate of layer 4 that slams +monk from
    # its context and has no %fast label
    arm('monk', layer4, 'layer4', loops=None)
    arm('mock', layer4, 'layer4', loops=None)
    monk_ax = [ax for nm, ax, _ in axes if nm == 'monk'][0]
    macks = [(ax, a) for ax, a in fe_arms(head(layer4), 2, limit=40)
             if is_gate_builder(a) and (monk_ax, 7) in pulls(door_gate_battery(a))]
    assert len(macks) == 1, len(macks)
    mack_ax, mack_a = macks[0]
    name(mack_a, 'mack.arm')
    formulas.add(mack_a)
    name(door_gate_battery(mack_a), 'mack.battery')
    formulas.add(door_gate_battery(mack_a))
    axes.append(('mack', mack_ax, 'slot? mack.axis layer4 = some mack.arm'))

    # +mook has no %fast label: it is the arm other than +mink that +mock pulls
    # from its context.  Its battery is ?.(?=([%2 *] ton) ton [8 [1 core] 9 11 0 1]),
    # the |^ core [rend skip buc] with the gate `rend`, the arm `skip` and the
    # arm `$` (`buc`).  The branches of `rend` are a chain of tests of the tag;
    # the %mean branch slams +mack and then (soft tank), which names +soft of
    # layer 4 and the mold +tank of layer 2.
    ax_of = dict((nm, ax) for nm, ax, _ in axes)
    mock_battery = [i for i, nm in names.items() if nm == 'mock.battery'][0]
    mook_ax = callee(mock_battery, 7, exclude=(ax_of['mink'],))
    mook_a = slot(mook_ax, layer4)
    name(mook_a, 'mook.arm')
    formulas.add(mook_a)
    mook_bat = door_gate_battery(mook_a)
    name(mook_bat, 'mook.battery')
    formulas.add(mook_bat)
    axes.append(('mook', mook_ax, 'slot? mook.axis layer4 = some mook.arm'))
    assert NODES[head(mook_bat)] == 6
    yes = head(tail(tail(mook_bat)))
    assert NODES[head(yes)] == 8 and tail(tail(yes)) == \
        cell(atom(9), cell(atom(11), cell(atom(0), atom(1))))
    mook_core = tail(head(tail(yes)))
    name(mook_core, 'mook.core')
    rend_a, skip_a, buc = head(mook_core), head(tail(mook_core)), tail(tail(mook_core))
    name(rend_a, 'mook.rend.arm')
    formulas.add(rend_a)
    rend_bat = door_gate_battery(rend_a)
    name(rend_bat, 'mook.rend.battery')
    name(skip_a, 'mook.skip')
    formulas.add(skip_a)
    name(buc, 'mook.buc')
    formulas.add(buc)
    # the cord of the %lose frame that +skip puts in: [[1 %lose] msg]
    msgs = [tail(i) for i in reach([skip_a]) if type(NODES[i]) is tuple
            and head(i) == cell(atom(1), atom(cord('lose')))]
    (msg,) = msgs
    name(msg, 'mook.skip.msg')
    # the branches of rend: [6 [5 [1 tag] 0 12] yes no], in the order of the ?+
    br = rend_bat
    for tag in ['hunk', 'lose', 'hand', 'mean', 'spot']:
        t5, yes_b, no_b = head(tail(br)), head(tail(tail(br))), tail(tail(tail(br)))
        assert NODES[head(br)] == 6 and t5 == cell(atom(5), cell(cell(atom(1), atom(cord(tag))),
                                                                cell(atom(0), atom(12)))), tag
        name(yes_b, 'mook.rend.%s' % tag)
        formulas.add(yes_b)
        br = no_b
    name(br, 'mook.rend.other')
    formulas.add(br)
    formulas.add(rend_bat)
    # the loop of a tape interpolation, ?@(a b [i.a $(a t.a)]); the other
    # [8 [1 L] 9 2 0 1] of rend are traps that build tapes
    (weld_l,) = [l for l in find_loops(rend_bat) if NODES[head(l)] == 6]
    name(weld_l, 'mook.rend.loop')
    formulas.add(weld_l)
    # the %mean branch: [6 atom-test leaf [8 mack-call [6 [5 [1 0] 0 2] hash [8 sof ..]]]]
    mean_b = [i for i, nm in names.items() if nm == 'mook.rend.mean'][0]
    cell_b = tail(tail(tail(mean_b)))
    sof = head(tail(tail(tail(tail(tail(tail(cell_b)))))))
    # sof = [8 [8 [9 soft 0 127] 9 2 10 [6 7 [0 3] 9 tank 0 511] 0 2] 9 2 10 [6 0 13] 0 2]
    inner = head(tail(sof))
    soft_ax = NODES[head(tail(head(tail(inner))))]
    assert tail(tail(head(tail(inner)))) == cell(atom(0), atom(127))
    smp = tail(head(tail(tail(tail(tail(tail(inner)))))))
    # smp = [7 [0 3] 9 tank 0 511]
    tk = tail(tail(smp))
    assert NODES[head(tk)] == 9 and tail(tail(tk)) == cell(atom(0), atom(511))
    tank_ax = NODES[head(tail(tk))]
    soft_a = slot(soft_ax, layer4)
    name(soft_a, 'soft.arm')
    formulas.add(soft_a)
    axes.append(('soft', soft_ax, 'slot? soft.axis layer4 = some soft.arm'))
    # +soft is a gate whose product is the gate |=(fud=* ...)
    soft_bat = door_gate_battery(soft_a)
    name(soft_bat, 'soft.battery')
    formulas.add(soft_bat)
    name(door_gate_battery(soft_bat), 'soft.gate.battery')
    tank_a = slot(tank_ax, layer2)
    name(tank_a, 'tank.arm')
    formulas.add(tank_a)
    axes.append(('tank', tank_ax, 'slot? tank.axis layer2 = some tank.arm'))
    name(door_gate_battery(tank_a), 'tank.battery')
    # +scow, which the %hand branch of rend slams on [%p (mug dat)]
    arm('scow', layer4, 'layer4')
    # the layer of +turn, +lent, +weld, +scag, +slag that +mook reads
    axes.append(('mook.layer2', 7, 'slot? mook.layer2.axis layer4 = some layer2'))

    # ---- the compiler's leaf cores +ca and +so: arms of the library core,
    # [[1 battery] [11 [%fast [1 [label [0 511] 0]]] [0 1]]], whose own arms
    # carry %fast labels except for a few
    def core_label_arm(label):
        clue = cell(atom(cord(label)), cell(cell(atom(0), atom(511)), atom(0)))
        hint = cell(atom(11), cell(cell(atom(FAST), cell(atom(1), clue)), cell(atom(0), atom(1))))
        res = [i for i in live if type(NODES[i]) is tuple and tail(i) == hint
               and type(NODES[head(i)]) is tuple and NODES[head(head(i))] == 1]
        assert len(res) == 1, (label, res)
        return res[0], tail(head(res[0]))

    def label_of(a):
        """the %fast label of a gate arm [7 builder [11 [%fast [1 [label ..]]] 0 1]]"""
        try:
            if NODES[head(a)] != 7:
                return None
            h = head(tail(tail(a)))
            if NODES[h] != 11:
                return None
            hb = head(tail(tail(tail(a))))
            if NODES[head(hb)] != FAST:
                return None
            q = tail(hb)
            if NODES[head(q)] != 1:
                return None
            return N.tape(head(tail(q)))
        except (TypeError, IndexError):
            return None

    # Each arm is named on its own; its axis is relative to its core
    # [battery payload], and Facts.lean checks it on [battery x] for every x.
    # The batteries `ca.battery` and `so.battery` belong to the bulk, because
    # two arms quote a noun that holds the hoon core: +dif of +ca and +huge of
    # +so, through their crash messages.  Such an arm is named in the bulk
    # (IN_BULK), and so is the quoted noun (`ca.dif.mean`, the battery of the
    # trap of its %mean hint), so that the arm's formula is written out down
    # to that name.
    unlabeled = {'ca': {95: 'lot', 171: 'lack', 87: 'dif'}, 'so': {4: 'jibe'}, 'pi': {}}
    bulk_named = set(i for i, nm in names.items() if nm.split('.')[0] in
                     ('root', 'nok', 'trap', 'core', 'layer0', 'layer1', 'layer2',
                      'layer3', 'layer4'))
    in_bulk = []
    for clabel in ['ca', 'so', 'pi']:
        carm, cbat = core_label_arm(clabel)
        name(cbat, clabel + '.battery')
        IN_BULK.add(clabel + '.battery')
        core_cell = cell(cbat, atom(0))
        for ax, a in fe_arms(cbat, 2):
            lab = label_of(a)
            full_ax = find_axis(core_cell, a)
            if lab:
                g = gate_battery(a)
            elif is_gate_builder(a) and full_ax in unlabeled[clabel]:
                lab = unlabeled[clabel][full_ax]
                g = door_gate_battery(a)
            else:
                continue
            full = clabel + '.' + lab
            if reach([a]) & bulk_named:
                # the outermost constants [1 q] of the formula that reach the bulk
                quotes = set()
                st = [g]
                while st:
                    i = st.pop()
                    if type(NODES[i]) is int or not reach([i]) & bulk_named:
                        continue
                    if NODES[head(i)] == 1:
                        quotes.add(tail(i))
                    else:
                        st.extend(NODES[i])
                assert len(quotes) == 1, (full, len(quotes))
                name(quotes.pop(), full + '.mean')
                IN_BULK.update([full + '.arm', full + '.battery', full + '.mean'])
                in_bulk.append(full)
            name(a, full + '.arm')
            formulas.add(a)
            name(g, full + '.battery')
            formulas.add(g)
            name_loops(full, g, 'any' if full not in in_bulk else None)
            axes.append((full, full_ax, '∀ x, slot? %s.axis (C %s.battery x) = some %s.arm'
                         % (full, clabel, full)))
    sys.stderr.write('compiler arms named in the bulk: %s\n' % in_bulk)

    # the library core: the first core on the tail spine of `core` whose
    # battery holds the arms [8 [1 battery] hint] of +ca and +so.  Its axes of
    # +ca and +so, and of the layers of hoon.hoon below it, name the context
    # that the arms of +ca and +so read.
    ca_arm8 = cell(atom(8), core_label_arm('ca')[0])
    so_arm8 = cell(atom(8), core_label_arm('so')[0])
    pi_arm8 = cell(atom(8), core_label_arm('pi')[0])
    lib = core
    while True:
        if type(NODES[head(lib)]) is tuple:
            lib_arms = dict((a, ax) for ax, a in fe_arms(head(lib), 2, limit=20))
            if ca_arm8 in lib_arms and so_arm8 in lib_arms:
                ca_lib, so_lib, pi_lib = lib_arms[ca_arm8], lib_arms[so_arm8], lib_arms[pi_arm8]
                break
        lib = tail(lib)
    def spine_axis(x, target):
        ax = 1
        while x != target:
            x = tail(x)
            ax = 2 * ax + 1
        return ax
    knit_battery = [i for i, nm in names.items() if nm == 'so.knit.battery'][0]
    assert (ca_lib, 15) in pulls(knit_battery), (ca_lib, so_lib, spine_axis(core, lib), pulls(knit_battery))
    name(lib, 'lib')
    facts.append(('core_lib', 'slot? %d core = some lib' % spine_axis(core, lib)))
    for clabel, ax, arm8 in (('ca', ca_lib, ca_arm8), ('so', so_lib, so_arm8),
                             ('pi', pi_lib, pi_arm8)):
        name(arm8, clabel + '.lib.arm')
        IN_BULK.add(clabel + '.lib.arm')
        formulas.add(arm8)
        axes.append((clabel + '.lib', ax, 'slot? %s.lib.axis lib = some %s.lib.arm'
                     % (clabel, clabel)))
    axes.append(('ca.lib.layer2', spine_axis(lib, layer2),
                 'slot? ca.lib.layer2.axis lib = some layer2'))
    axes.append(('ca.lib.layer1', spine_axis(lib, layer1),
                 'slot? ca.lib.layer1.axis lib = some layer1'))

    # the gates +distribute and +double-int of the library core, which recurse
    # on themselves (the Lean names drop the dash)
    for label, lname in (('distribute', 'distribute'), ('double-int', 'double_int')):
        res = []
        for a in arms_of(label):
            try:
                find_axis(head(lib), a)
                res.append((find_axis(lib, a), a))
            except KeyError:
                pass
        (ax, a), = res
        name(a, lname + '.arm')
        formulas.add(a)
        name(gate_battery(a), lname + '.battery')
        formulas.add(gate_battery(a))
        axes.append((lname, ax, 'slot? %s.axis lib = some %s.arm' % (lname, lname)))

    # +inlineable, a gate whose %fast parent is ..ride and which reads nothing
    # from its context: named without an axis
    (inl,) = arms_of('inlineable')
    name(inl, 'inlineable.arm')
    formulas.add(inl)
    name(gate_battery(inl), 'inlineable.battery')
    formulas.add(gate_battery(inl))

    # the analysis core `ana` (the |% of +ska-callgraph, the second core above
    # `lib` on the tail spine): the first spine core whose battery holds
    # +patch-prod.  Its arms +patch-prod and +msg-anno carry %fast labels;
    # +knit-anno, +msg-sock, +safe-nomm and +safe-fol-fol are found through
    # their callers.  `knit_anno.lib.axis` is the axis of `lib` in `ana`,
    # through which +knit-anno, +patch-prod and +msg-anno reach +so and +pi.
    (pp_arm,) = arms_of('patch-prod')
    ana = core
    while True:
        if type(NODES[head(ana)]) is tuple:
            ana_arms = dict((a, ax) for ax, a in fe_arms(head(ana), 2, limit=20))
            if pp_arm in ana_arms:
                break
        ana = tail(ana)
    name(ana, 'ana')
    facts.append(('core_ana', 'slot? %d core = some ana' % spine_axis(core, ana)))
    def ana_arm(a, lname, labelled):
        name(a, lname + '.arm')
        formulas.add(a)
        g = gate_battery(a) if labelled else door_gate_battery(a)
        name(g, lname + '.battery')
        formulas.add(g)
        axes.append((lname, ana_arms[a], 'slot? %s.axis ana = some %s.arm' % (lname, lname)))
        return g
    pp_bat = ana_arm(pp_arm, 'patch_prod', True)
    (ma_arm,) = arms_of('msg-anno')
    ma_bat = ana_arm(ma_arm, 'msg_anno', True)
    # +knit-anno: the one arm that +patch-prod pulls from its context, the core
    knit_ax = callee(pp_bat, 7)
    assert callee(ma_bat, 7) == knit_ax
    knit_bat = ana_arm(slot(knit_ax, ana), 'knit_anno', False)
    lib_in_ana = spine_axis(ana, lib)
    # +knit-anno reaches +so and +pi through `lib`, at axis 7 of its context
    assert set(c for _, c in pulls(knit_bat) if c != 1) == {4 * lib_in_ana + 3}
    axes.append(('knit_anno.lib', lib_in_ana, 'slot? knit_anno.lib.axis ana = some lib'))
    # +msg-sock: the gate of `ana` that +recursive-call pulls and that pulls
    # nothing but +knit:so (the arm `knit` of the core of +so, at axis 31)
    (rc_arm,) = arms_of('recursive-call')
    knit_so_ax = dict((nm, ax_) for nm, ax_, _ in axes)['so.knit']
    cands = []
    for ax_, c in pulls(gate_battery(rc_arm)):
        try:
            a = slot(ax_, ana)
        except Exception:
            continue
        if a in ana_arms and is_gate_builder(a) and not label_of(a):
            ps = set(pulls(door_gate_battery(a)))
            if ps == {(so_lib, 4 * lib_in_ana + 3), (knit_so_ax, 1)}:
                cands.append(a)
    (ms_arm,) = set(cands)
    ana_arm(ms_arm, 'msg_sock', False)
    # +safe-fol-fol and +safe-nomm: the gates of `ana` whose formulas test for
    # the tags %memo and %mean, of which +safe-fol-fol pulls +safe-nomm from
    # its context and +safe-nomm pulls nothing
    def atoms_in(i):
        return set(NODES[j] for j in reach([i]) if type(NODES[j]) is int)
    MEAN, MEMO = cord('mean'), cord('memo')
    sn, sff = [], []
    for a, ax_ in ana_arms.items():
        if label_of(a) or not is_gate_builder(a):
            continue
        g = door_gate_battery(a)
        if not {MEAN, MEMO} <= atoms_in(g):
            continue
        ps = pulls(g)
        if ps == []:
            sn.append(a)
        elif len(ps) == 1 and ps[0][1] == 7:
            sff.append((ps[0][0], a))
    (sn_arm,) = sn
    (sff_arm,) = [a for ax_, a in sff if slot(ax_, ana) == sn_arm]
    ana_arm(sn_arm, 'safe_nomm', False)
    ana_arm(sff_arm, 'safe_fol_fol', False)

    # ---- write
    emit_all(outdir, names, formulas, axes, facts, root, core, steps, sha, len(data))
    print('steps', steps)
    for nm, st in facts:
        print(nm, ':', st)
    for nm, ax, st in axes:
        print(nm, ax, ':', st)

# ---------------------------------------------------------------------------
# Emission into small files.
#
# Named nouns belong to a family (the first component of the name: dec, by,
# fe, ...) or to the bulk (root, nok, trap, core and the layers).  Each family
# goes to lemmas/Pill/Arm/<Family>.lean with the anonymous helpers that it
# needs, and imports only the families whose named nouns it mentions.  The
# bulk goes to a chain lemmas/Pill/Nouns/P000.lean, P001.lean, ..., and
# Facts.lean sits on top.  Anonymous definitions are named by a hash of their
# content, in which a named noun counts by its name, so a region that did not
# change regenerates to the same text.

BULK = {'root', 'nok', 'trap', 'core', 'layer0', 'layer1', 'layer2', 'layer3', 'layer4', 'lib',
        'ana'}
IN_BULK = set()      # names of other families that belong to the bulk

CHUNK_MIN = 1000     # bulk definitions per chain file, at least
CHUNK_DIV = 500      # a file ends after a definition whose hash is 0 mod this
CHUNK_MAX = 2000     # bulk definitions per chain file, at most


def family_of(nm):
    if nm in IN_BULK:
        return None
    f = nm.split('.')[0]
    return None if f in BULK else f


RESERVED = {'con', 'prn', 'aux', 'nul'}   # file names that some systems reserve


def module_of(fam):
    m = fam[0].upper() + fam[1:]
    return m + 'Arm' if fam in RESERVED else m


def content_keys(roots, named):
    """a hex key for every cell reachable from roots, where a named cell
    below the top counts by its name"""
    key = {}

    def leaf(j):
        n = NODES[j]
        if type(n) is int:
            return hashlib.sha256(b'a%d' % n).digest()
        if j in named:
            return hashlib.sha256(b'n' + named[j].encode()).digest()
        return key[j]

    for r in roots:
        st = [(r, False)]
        while st:
            i, done = st.pop()
            n = NODES[i]
            if type(n) is int:
                continue
            if done:
                key[i] = hashlib.sha256(b'c' + leaf(n[0]) + leaf(n[1])).digest()
                continue
            if i in key:
                continue
            st.append((i, True))
            for j in (n[1], n[0]):
                if type(NODES[j]) is tuple and j not in named and j not in key:
                    st.append((j, False))
    return key


class Unit:
    """the definitions of a set of named roots: the roots, and anonymous
    helpers for the roots that are not printed in full"""

    def __init__(self, roots, named, formulas, prefix):
        self.roots = roots
        self.named = named
        self.full = set(r for r in roots if r in formulas)
        inside = set()
        order = []
        for r in roots:
            if r in self.full:
                continue
            st = [(r, False)]
            while st:
                i, done = st.pop()
                if done:
                    order.append(i)
                    continue
                if i in inside:
                    continue
                inside.add(i)
                st.append((i, True))
                n = NODES[i]
                for j in (n[1], n[0]):
                    if type(NODES[j]) is tuple and j not in named and j not in inside:
                        st.append((j, False))
        rc = {}
        for i in inside:
            for j in NODES[i]:
                if j in inside:
                    rc[j] = rc.get(j, 0) + 1
        defs = set(i for i in inside if rc.get(i, 0) > 1)
        defs.update(r for r in roots if r not in self.full)
        size = {}
        for i in order:
            sz = 1 + sum(0 if (j in defs or j in named or type(NODES[j]) is int) else size[j]
                         for j in NODES[i])
            if sz > LIMIT and i not in defs:
                defs.add(i)
            size[i] = sz
        self.helpers = defs - set(roots)
        keys = content_keys([r for r in roots if r not in self.full], named)
        self.names = dict((i, named[i]) for i in roots)
        for i in self.helpers:
            self.names[i] = '%sh%s' % (prefix, keys[i].hex()[:12])
        self.key = keys

    def stops(self, i):
        """the definitions that the term of i refers to by name"""
        return lambda j: j != i and (j in self.named or
                                     (i not in self.full and j in self.helpers))

    def term(self, i):
        stop = self.stops(i)
        out = []
        refs = []

        def go(j, top, paren):
            n = NODES[j]
            if type(n) is int:
                out.append('(A %s)' % lit(n) if paren else 'A %s' % lit(n))
                return
            if not top and stop(j):
                out.append(self.names.get(j) or self.named[j])
                refs.append(j)
                return
            if paren:
                out.append('(')
            out.append('C ')
            go(n[0], False, True)
            out.append(' ')
            go(n[1], False, True)
            if paren:
                out.append(')')
        go(i, True, False)
        return ''.join(out), refs

    def emit(self):
        """(name, text, external named refs) in an order where each definition
        comes after the ones it refers to"""
        texts = {}
        for i in list(self.roots) + sorted(self.helpers, key=lambda i: self.names[i]):
            texts[i] = self.term(i)
        mine = set(texts)
        done = set()
        out = []
        for r in sorted(self.roots, key=lambda i: self.names[i]):
            st = [(r, False)]
            while st:
                i, ready = st.pop()
                if ready:
                    if i not in done:
                        done.add(i)
                        text, refs = texts[i]
                        out.append((i, self.names[i], text,
                                    [j for j in refs if j not in mine]))
                    continue
                if i in done:
                    continue
                st.append((i, True))
                for j in reversed(texts[i][1]):
                    if j in mine and j not in done:
                        st.append((j, False))
        return out


def lit(n):
    return str(n) if n < 1 << 16 else hex(n)


def sccs(nodes, edges):
    """Tarjan's strongly connected components, in a deterministic order"""
    index = {}
    low = {}
    on = set()
    stack = []
    out = []
    counter = [0]

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in sorted(edges.get(v, ())):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))
    for v in sorted(nodes):
        if v not in index:
            strong(v)
    return out


GEN = '/-\nGenerated by tools/pill2lean.py from a steel pill; do not edit.\n-/\n'

ARM_DOC = (
    '\n/-! The nouns are public and their bodies are not exposed: a file sees the\n'
    'Nock of an arm only through `import all`, which the arm\'s own theorem file\n'
    'does, so a change to the Nock rechecks that file and nothing above it. -/\n')


def emit_all(outdir, names, formulas, axes, facts, root, core, steps, sha, nbytes):
    named = dict(names)
    fams = {}
    bulk_roots = []
    for i, nm in names.items():
        f = family_of(nm)
        if f is None:
            bulk_roots.append(i)
        else:
            fams.setdefault(f, []).append(i)

    # the families and what they refer to
    units = {}
    for f, roots in fams.items():
        units[f] = Unit(roots, named, formulas, f + '.')
    edges = {}
    emitted = {}
    for f, u in units.items():
        emitted[f] = u.emit()
        for _, _, _, refs in emitted[f]:
            for j in refs:
                g = family_of(named[j])
                assert g is not None, (f, named[j])
                if g != f:
                    edges.setdefault(f, set()).add(g)
    comps = sccs(list(units), edges)
    unit_of = {}
    for comp in comps:
        for f in comp:
            unit_of[f] = comp[0]
    merged = {}
    for comp in comps:
        merged[comp[0]] = comp

    axes_of = {}
    for nm, ax, st in axes:
        axes_of.setdefault(unit_of[nm.split('.')[0]], []).append((nm, ax))

    arm_dir = os.path.join(outdir, 'Arm')
    os.makedirs(arm_dir, exist_ok=True)
    for old in os.listdir(arm_dir):
        if old.endswith('.lean'):
            os.remove(os.path.join(arm_dir, old))
    for head_f, comp in merged.items():
        deps = set()
        body = []
        for f in comp:
            for i, nm, text, refs in emitted[f]:
                for j in refs:
                    g = unit_of[family_of(named[j])]
                    if g != head_f:
                        deps.add(g)
                body.append('def %s : Noun := %s\n' % (nm, text))
        with open(os.path.join(arm_dir, module_of(head_f) + '.lean'), 'w') as fh:
            fh.write('module\n\npublic import core.Nock\n')
            for g in sorted(deps):
                fh.write('public import lemmas.Pill.Arm.%s\n' % module_of(g))
            fh.write('\n' + GEN)
            fh.write(ARM_DOC)
            if len(comp) > 1:
                fh.write('\n-- The families %s refer to each other.\n' % ', '.join(comp))
            fh.write('\nset_option maxRecDepth 100000\n')
            fh.write('\nnamespace Formalization\nnamespace Pill\n\nopen Nock\n\n')
            for nm, ax in sorted(axes_of.get(head_f, [])):
                fh.write('public abbrev %s.axis : Nat := %d\n' % (nm, ax))
            if axes_of.get(head_f):
                fh.write('\n')
            fh.writelines(['public ' + line for line in body])
            fh.write('\nend Pill\nend Formalization\n')

    # the bulk, as a chain of files
    bulk = Unit(sorted(bulk_roots, key=lambda i: named[i]), named,
                set(i for i in bulk_roots if i in formulas), 'n')
    defs = []
    st_done = set()
    texts = {}
    for i in list(bulk.roots) + list(bulk.helpers):
        texts[i] = bulk.term(i)
    mine = set(texts)
    for r in [core, root] + sorted(bulk.roots, key=lambda i: named[i]):
        st = [(r, False)]
        while st:
            i, ready = st.pop()
            if ready:
                if i not in st_done:
                    st_done.add(i)
                    defs.append(i)
                continue
            if i in st_done:
                continue
            st.append((i, True))
            for j in reversed(texts[i][1]):
                if j in mine and j not in st_done:
                    st.append((j, False))
    chunks = [[]]
    for i in defs:
        chunks[-1].append(i)
        k = bulk.key.get(i) or hashlib.sha256(named[i].encode()).digest()
        n = len(chunks[-1])
        if (n >= CHUNK_MIN and int.from_bytes(k[:8], 'big') % CHUNK_DIV == 0) or n >= CHUNK_MAX:
            chunks.append([])
    if not chunks[-1]:
        chunks.pop()
    chain_dir = os.path.join(outdir, 'Nouns')
    os.makedirs(chain_dir, exist_ok=True)
    for old in os.listdir(chain_dir):
        if old.endswith('.lean'):
            os.remove(os.path.join(chain_dir, old))
    for k, chunk in enumerate(chunks):
        deps = set()
        for i in chunk:
            for j in texts[i][1]:
                if j not in mine:
                    deps.add(unit_of[family_of(named[j])])
        with open(os.path.join(chain_dir, 'P%03d.lean' % k), 'w') as fh:
            fh.write('module\n\n')
            fh.write('public import core.Nock\n' if k == 0
                     else 'public import lemmas.Pill.Nouns.P%03d\n' % (k - 1))
            for g in sorted(deps):
                fh.write('public import lemmas.Pill.Arm.%s\n' % module_of(g))
            fh.write('\n' + GEN)
            fh.write('\nset_option maxRecDepth 100000\n')
            fh.write('\n@[expose] public section\n')
            fh.write('\nnamespace Formalization\nnamespace Pill\n\nopen Nock\n\n')
            for i in chunk:
                fh.write('def %s : Noun := %s\n' % (bulk.names[i], texts[i][0]))
            fh.write('\nend Pill\nend Formalization\n\nend\n')

    # the facts, on top of the chain
    head_ = ('/-\nGenerated by tools/pill2lean.py from a steel pill; do not edit.\n'
             'sha256 of the pill: %s (%d bytes)\n-/\n' % (sha, nbytes))
    with open(os.path.join(outdir, 'Facts.lean'), 'w') as fh:
        fh.write('module\n\npublic import lemmas.Sound\npublic import lemmas.KernelRfl\n')
        fh.write('public import lemmas.Pill.Nouns.P%03d\n' % (len(chunks) - 1))
        for f in sorted(merged):
            fh.write('public import lemmas.Pill.Arm.%s\n' % module_of(f))
        for f in sorted(merged):
            fh.write('import all lemmas.Pill.Arm.%s\n' % module_of(f))
        fh.write('\n' + head_)
        fh.write('\n/-! The kernel checks these facts on the bodies of the nouns, which it\n'
                 'sees through `import all` of the arm files. -/\n')
        fh.write('\n@[expose] public section\n')
        fh.write('\nnamespace Formalization\nnamespace Pill\n\nopen Nock\n\n')
        fh.write('/-- `root` is `[%steel nok trap ~]`. -/\n')
        fh.write('theorem root_eq : root = C (A %s) (C nok (C trap (A 0))) := rfl\n\n'
                 % lit(cord('steel')))
        fh.write('/-- Running the pill\'s formula on its trap builds the SKA core (%d steps). -/\n'
                 % steps)
        fh.write('theorem core_evalFuel : evalFuel %d (C trap (A 0)) nok = some core := by kernel_rfl\n\n'
                 % (steps + 8))
        for nm, st in facts:
            fh.write('theorem %s : %s := by kernel_rfl\n\n' % (nm, st))
        fh.write('/-! Each named arm sits at its axis.  The constants `x.axis` are in the\n'
                 'arm files. -/\n\n')
        for nm, ax, st in axes:
            if st is None:
                continue
            if st.startswith('∀'):
                fh.write('theorem %s.arm_at : %s := by\n  intro x; kernel_rfl\n\n' % (nm, st))
            else:
                fh.write('theorem %s.arm_at : %s := by kernel_rfl\n\n' % (nm, st))
        fh.write('end Pill\nend Formalization\n\nend\n')
    print('families', len(units), 'arm files', len(merged), 'chain files', len(chunks),
          'bulk definitions', len(defs))
    for comp in comps:
        if len(comp) > 1:
            print('merged', comp)


if __name__ == '__main__':
    main()
