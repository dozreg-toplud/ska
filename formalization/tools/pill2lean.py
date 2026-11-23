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

    def arm(label, layer, lname, loops=0, full=True):
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
        names[a] = label + '.arm'
        g = gate_battery(a)
        names[g] = label + '.battery'
        formulas.add(a)
        if full:
            formulas.add(g)
        ls = find_loops(g) if loops is not None else []
        assert loops is None or len(ls) == loops, (label, len(ls))
        for k, l in enumerate(ls):
            names[l] = label + ('.loop' if loops == 1 else '.loop%d' % k)
            formulas.add(l)
        facts.append((label + '.arm_at', 'slot? %d %s = some %s.arm' % (ax, lname, label)))
        return a

    arm('dec', layer1, 'layer1', loops=1)
    arm('add', layer1, 'layer1')
    arm('lth', layer1, 'layer1', loops=1)
    arm('dor', layer2, 'layer2')
    arm('gor', layer2, 'layer2')
    arm('mor', layer2, 'layer2')
    arm('mug', layer2, 'layer2', loops=None, full=False)

    # the +by door and its +put
    by_arm = [a for a in arms_of('by')]
    by_in = [(find_axis(layer2, a), a) for a in by_arm]
    assert len(by_in) == 1
    by_ax, by_a = by_in[0]
    names[by_a] = 'by.arm'
    formulas.add(by_a)
    door = nock(layer2, by_a)
    assert tail(tail(door)) == layer2 and NODES[head(tail(door))] == 0
    names[head(door)] = 'by.battery'
    facts.append(('by.arm_at', 'slot? %d layer2 = some by.arm' % by_ax))
    puts = []
    for a in arms_of('put'):
        try:
            find_axis(head(door), a)
            puts.append((find_axis(door, a), a))
        except KeyError:
            pass
    assert len(puts) == 1
    put_ax, put_a = puts[0]
    names[put_a] = 'put.arm'
    formulas.add(put_a)
    g = gate_battery(put_a)
    names[g] = 'put.battery'
    formulas.add(g)
    (l,) = find_loops(g)
    names[l] = 'put.loop'
    formulas.add(l)
    facts.append(('put.arm_at',
                  'slot? %d (C by.battery (C a layer2)) = some put.arm' % put_ax))

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
            if nm == 'put.arm_at':
                f.write('theorem %s (a : Noun) : %s := by\n  cases a <;> kernel_rfl\n\n' % (nm, st))
            else:
                f.write('theorem %s : %s := by kernel_rfl\n\n' % (nm, st))
        f.write('end Pill\nend Formalization\n')
    print('cells', sum(1 for i in reach([root, core]) if type(NODES[i]) is tuple),
          'definitions', len(em.defs), 'steps', steps)
    for nm, st in facts:
        print(nm, ':', st)


if __name__ == '__main__':
    main()
