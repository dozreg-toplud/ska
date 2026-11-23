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
        ls = find_loops(g) if loops is not None else []
        assert loops is None or len(ls) == loops, (label, len(ls))
        for k, l in enumerate(ls):
            name(l, label + ('.loop' if loops == 1 else '.loop%d' % k))
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
    # +homo has no %fast label: it is the arm that +flop pulls from its context
    homo_ax = callee(gate_battery(flop), 7)
    name(slot(homo_ax, layer2), 'homo.arm')
    formulas.add(slot(homo_ax, layer2))
    axes.append(('homo', homo_ax, 'slot? homo.axis layer2 = some homo.arm'))

    # bit arithmetic
    for label in ['bex', 'rsh', 'lsh', 'end', 'cut', 'cat', 'can']:
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

    def fe_arms(i, ax):
        n = NODES[i]
        if type(NODES[n[0]]) is int:
            yield ax, i
            return
        yield from fe_arms(n[0], 2 * ax)
        yield from fe_arms(n[1], 2 * ax + 1)

    def pulls(formula):
        """the [axis ctx] of every [9 axis 0 ctx] in formula, in pre-order"""
        out = []
        st = [formula]
        while st:
            i = st.pop()
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
    in_battery = door('in', layer2, 'layer2')
    door_arm('in', in_battery, 'put', 1)
    has_in = door_arm('in', in_battery, 'has', 1)
    # +has:in slams an inner gate [8 [8 [1 0] [1 gate] 0 1] 9 2 10 ...]
    inner = tail(head(tail(tail(head(tail(gate_battery(has_in)))))))
    assert NODES[head(inner)] == 7
    name(inner, 'in.has.gate')
    formulas.add(inner)

    # ---- write
    em = Emitter([root, core], names, formulas)
    os.makedirs(outdir, exist_ok=True)
    head_ = ('/-\nGenerated by tools/pill2lean.py from a steel pill; do not edit.\n'
             'sha256 of the pill: %s (%d bytes)\n-/\n' % (sha, len(data)))

    with open(os.path.join(outdir, 'Nouns.lean'), 'w') as f:
        f.write('import lemmas.Fuel\n\n')
        f.write(head_)
        f.write('\nset_option maxRecDepth 100000\n')
        f.write('\nnamespace Formalization\nnamespace Pill\n\nopen Nock\n\n')
        em.emit(f)
        f.write('\nend Pill\nend Formalization\n')

    with open(os.path.join(outdir, 'Facts.lean'), 'w') as f:
        f.write('import lemmas.Sound\nimport lemmas.KernelRfl\n'
                'import lemmas.Pill.Nouns\n\n')
        f.write(head_)
        f.write('\nnamespace Formalization\nnamespace Pill\n\nopen Nock\n\n')
        f.write('/-- `root` is `[%steel nok trap ~]`. -/\n')
        f.write('theorem root_eq : root = C (A %s) (C nok (C trap (A 0))) := rfl\n\n'
                % Emitter.lit(cord('steel')))
        f.write('/-- Running the pill\'s formula on its trap builds the SKA core (%d steps). -/\n'
                % steps)
        f.write('theorem core_evalFuel : evalFuel %d (C trap (A 0)) nok = some core := by kernel_rfl\n\n'
                % (steps + 8))
        for nm, st in facts:
            f.write('theorem %s : %s := by kernel_rfl\n\n' % (nm, st))
        f.write('/-! The axes of the named arms.  A proof names an axis by its constant,\n'
                'never by its number. -/\n\n')
        for nm, ax, st in axes:
            f.write('abbrev %s.axis : Nat := %d\n\n' % (nm, ax))
            if st.startswith('∀'):
                f.write('theorem %s.arm_at : %s := by\n  intro x; kernel_rfl\n\n' % (nm, st))
            else:
                f.write('theorem %s.arm_at : %s := by kernel_rfl\n\n' % (nm, st))
        f.write('end Pill\nend Formalization\n')
    print('cells', sum(1 for i in reach([root, core]) if type(NODES[i]) is tuple),
          'definitions', len(em.defs), 'steps', steps)
    for nm, st in facts:
        print(nm, ':', st)
    for nm, ax, st in axes:
        print(nm, ax, ':', st)


if __name__ == '__main__':
    main()
