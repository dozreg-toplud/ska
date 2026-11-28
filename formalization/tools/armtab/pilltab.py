"""The arm table and the pill's nouns by Hoon path (track T, README Gaps 32).

    from pilltab import *

`load_pill(path)`: cue a steel pill and run its formula on its trap (the
SKA core, `core` of lemmas/Pill).  `load_table(path)`: the JSON of
tools/armtab/armtab.json (written by armtab.py from tools/hoon/armtab.hoon).
`locate(table, core)`: for every core path its battery and for every arm path
its formula, as noun ids of tools/nouns.py (hash-consed: two pills cued in one
process share their equal subtrees, so equality is `==` of ids).
`lean_names(dir)`: the nouns of a generated lemmas/Pill directory, noun id
-> names.  Run under tools/capped.sh (a pill and its Lean nouns take about
1.5 GB).
"""
import glob
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import nouns as N                                   # noqa: E402
from nouns import NODES, atom, cell, head, tail     # noqa: E402

FORM = os.path.normpath(os.path.join(HERE, '..', '..'))


def load_pill(path):
    data = open(path, 'rb').read()
    root = N.cue(data)
    nok = head(tail(root))
    trap = head(tail(tail(root)))
    core = N.nock(cell(trap, atom(0)), nok)
    return dict(root=root, nok=nok, trap=trap, core=core, path=path,
                sha=hashlib.sha256(data).hexdigest(), size=len(data))


def load_table(path=None):
    return json.load(open(path or os.path.join(HERE, 'armtab.json')))


def slot_or_none(ax, i):
    for b in bin(ax)[3:]:
        n = NODES[i]
        if type(n) is int:
            return None
        i = n[1] if b == '1' else n[0]
    return i


def covers(bat, axes):
    """the battery `bat` has its arms exactly at `axes` (battery axes): every
    node above an arm is a cell with both sides used, every arm a cell"""
    todo = [(bat, sorted(axes))]
    while todo:
        i, axs = todo.pop()
        if type(NODES[i]) is int:
            return False
        if axs == [1]:
            continue
        if 1 in axs:
            return False
        lft, rgt = [], []
        for a in axs:
            b = bin(a)[3:]
            r = int('1' + b[1:], 2)
            (lft if b[0] == '0' else rgt).append(r)
        if not lft or not rgt:
            return False
        todo.append((head(i), lft))
        todo.append((tail(i), rgt))
    return True


ZERO1 = None


def builder_battery(f):
    """the battery that the formula f quotes as the core it returns: f is
    [[1 bat] 0 1] under 7s and 8s, a %fast hint [7 b [11 h 0 1]] read as b"""
    global ZERO1
    if ZERO1 is None:
        ZERO1 = cell(atom(0), atom(1))
    for _ in range(256):
        n = NODES[f]
        if type(n) is int:
            return None
        h, t = n
        hn = NODES[h]
        if type(hn) is tuple:
            if NODES[hn[0]] == 1 and t == ZERO1:
                return hn[1]
            return None
        if type(NODES[t]) is int:
            return None
        if hn == 7:
            a, b = NODES[t]
            bn = NODES[b]
            if type(bn) is tuple and NODES[bn[0]] == 11 and type(NODES[bn[1]]) is tuple \
                    and NODES[bn[1]][1] == ZERO1:
                f = a
            else:
                f = b
            continue
        if hn == 8:
            b, c = NODES[t]
            bn = NODES[b]
            # [8 [1 bat] 0 1], or with a hint [8 [1 bat] 11 h 0 1]: the core
            # [bat subject]
            if type(bn) is tuple and NODES[bn[0]] == 1 and (c == ZERO1 or (
                    type(NODES[c]) is tuple and NODES[NODES[c][0]] == 11
                    and type(NODES[NODES[c][1]]) is tuple and NODES[NODES[c][1]][1] == ZERO1)):
                return bn[1]
            f = c
            continue
        if hn == 11:
            f = NODES[t][1]
            continue
        return None
    return None


class TooLong(Exception):
    pass


def nock_lim(s, f, limit=100000):
    """*[s f] by tools/nouns.py, abandoned after `limit` steps"""
    real = N.nock
    count = [0]

    def lim(s, f):
        count[0] += 1
        if count[0] > limit:
            raise TooLong()
        return real(s, f)
    # nouns.nock calls itself through the module global: count those calls
    N.nock = lim
    try:
        return real(s, f)
    finally:
        N.nock = real


def parent(path):
    return path.rsplit('/', 1)[0] if '/' in path else None


def locate(tab, core):
    """(bat, arm, core_noun, bad): core path -> battery id, arm path ->
    formula id, spine path -> core id, and the paths that could not be
    located with the reason"""
    cores, arms = tab['cores'], tab['arms']
    by_core = {}
    for p, a in arms.items():
        by_core.setdefault(parent(p), []).append(p)
    bat, arm, cnoun, bad = {}, {}, {}, {}
    order = sorted(cores, key=lambda p: (p.count('/'), p))
    for p in order:
        c = cores[p]
        axes = [arms[a]['bax'] for a in by_core.get(p, [])]
        if c['abs'] is not None:
            cn = slot_or_none(c['abs'], core)
            if cn is None or type(NODES[cn]) is int:
                bad[p] = 'no core at abs'
                continue
            cnoun[p] = cn
            b = head(cn)
        else:
            if p not in arm:
                bad[p] = 'arm not located'
                continue
            b = builder_battery(arm[p])
            q = parent(p)
            if b is None and q in cnoun:
                # an alias or a computed core: run the arm on its core
                try:
                    cn = nock_lim(cnoun[q], arm[p])
                    if type(NODES[cn]) is tuple:
                        b = head(cn)
                        cnoun[p] = cn
                except (TooLong, N.Crash, RecursionError, TypeError, AssertionError):
                    pass
            if b is None:
                bad[p] = 'no [[1 bat] 0 1] in the arm'
                continue
        if not covers(b, axes):
            bad[p] = 'battery shape differs from the table'
            continue
        bat[p] = b
        for a in by_core.get(p, []):
            arm[a] = N.slot(arms[a]['bax'], b)
            if p in cnoun:
                assert N.slot(arms[a]['cax'], cnoun[p]) == arm[a], a
    return bat, arm, cnoun, bad


DEF = re.compile(r'^(?:public )?def ([A-Za-z0-9_.]+) : Noun := (.*)$')
TOK = re.compile(r'\(|\)|[A-Za-z_][A-Za-z0-9_.]*|0x[0-9a-fA-F]+|[0-9]+')


def parse_defs(texts):
    """{name: body text} -> {name: noun id}, bodies of C, A, literals and
    names of other bodies; a body naming anything else is left out"""
    toks = {nm: TOK.findall(b) for nm, b in texts.items()}
    out = {}
    state = {}
    for start in toks:
        if start in out or start in state:
            continue
        stack = [start]
        while stack:
            nm = stack[-1]
            if nm in out:
                stack.pop()
                continue
            deps = [t for t in toks[nm] if t not in ('C', 'A', '(', ')') and not t[0].isdigit()]
            miss = [d for d in deps if d not in out]
            unk = [d for d in miss if d not in toks or state.get(d) == 'bad']
            if unk:
                state[nm] = 'bad'
                stack.pop()
                continue
            todo = [d for d in miss if state.get(d) != 'open']
            if todo and state.get(nm) != 'open':
                state[nm] = 'open'
                stack.extend(todo)
                continue
            if miss:            # a cycle or a bad dependency
                state[nm] = 'bad'
                stack.pop()
                continue
            out[nm] = build(toks[nm], out)
            stack.pop()
    return out


def build(ts, env):
    """the noun of the token list ts (prefix C/A with parentheses)"""
    pos = 0
    # iterative: a stack of pending C applications
    vals = []
    ops = []        # 'C' frames: [count of children wanted]

    def push(v):
        while True:
            if not ops:
                vals.append(v)
                return
            fr = ops[-1]
            fr.append(v)
            if len(fr) == 2:
                ops.pop()
                v = cell(fr[0], fr[1])
                continue
            return
    while pos < len(ts):
        t = ts[pos]
        pos += 1
        if t in ('(', ')'):
            continue
        if t == 'C':
            ops.append([])
        elif t == 'A':
            push(atom(int(ts[pos], 0)))
            pos += 1
        else:
            push(env[t])
    assert len(vals) == 1 and not ops, ts[:20]
    return vals[0]


def lean_names(pill_dir):
    """noun id -> sorted names, and name -> id, of a lemmas/Pill directory"""
    texts = {}
    for f in glob.glob(pill_dir + '/Nouns/*.lean') + glob.glob(pill_dir + '/Arm/*.lean'):
        for line in open(f):
            m = DEF.match(line)
            if m:
                texts[m.group(1)] = m.group(2)
    ids = parse_defs(texts)
    rev = {}
    for nm, i in ids.items():
        rev.setdefault(i, []).append(nm)
    for v in rev.values():
        v.sort(key=lambda s: (s.startswith('n') and s[1:2] in 'h0123456789', s))
    return rev, ids


HASHNAME = re.compile(r'\b(?:nh[0-9a-f]{12}|[a-z_]+\.h[0-9a-f]{12})\b')


def hand_names(root=FORM):
    """hash names that files outside lemmas/Pill mention: name -> files"""
    out = {}
    for f in glob.glob(root + '/lemmas/**/*.lean', recursive=True):
        if '/lemmas/Pill/' in f:
            continue
        for m in HASHNAME.finditer(open(f).read()):
            out.setdefault(m.group(0), set()).add(os.path.relpath(f, root))
    return out


def parents_map(roots):
    """node -> [(parent, 2 or 3)] over the DAG below roots"""
    par = {}
    seen = set()
    todo = list(roots)
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        n = NODES[i]
        if type(n) is tuple:
            par.setdefault(n[0], []).append((i, 2))
            par.setdefault(n[1], []).append((i, 3))
            todo.append(n[0])
            todo.append(n[1])
    return par


def place(i, targets, par):
    """the nearest target above node i: (target, axis of i in it), by BFS
    up the parent map"""
    from collections import deque
    q = deque([(i, [])])
    seen = {i}
    while q:
        j, bits = q.popleft()
        if j in targets:
            ax = 1
            for b in reversed(bits):
                ax = 2 * ax + (b - 2)
            return j, ax
        for p, b in par.get(j, ()):
            if p not in seen:
                seen.add(p)
                q.append((p, bits + [b]))
    return None, None
