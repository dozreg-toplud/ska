"""The map of `+soft-emit`'s try path `seTryPath` (README Gaps 21.21): its pushes (`7` / `8`) and
`%6` tests, nested to depth 3, with the cell count of each head and rest (shared parts named in
`CompSccLoopSoftEmitCut.lean` counted again).  The first step of the pill link of the try path
against `softEmit` (`Ska/SccLoopSoftTry.lean`): cut at these pushes and state one lemma per push.

    python3 tools/gen/softtry.py
"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '..', '..', 'lemmas', 'Compiler', 'CompSccLoopSoftEmitCut.lean')

s = open(SRC).read()
defs = {m.group(1): m.group(2) for m in re.finditer(r'def (\w+) : Noun :=\n((?:  .*\n)+)', s)}


def parse_text(body):
    toks = re.findall(r'\(|\)|0x[0-9a-fA-F]+|\d+|[A-Za-z_][A-Za-z0-9_]*', body)
    pos = [0]

    def p():
        t = toks[pos[0]]
        if t == '(':
            pos[0] += 1
            v = p()
            assert toks[pos[0]] == ')'
            pos[0] += 1
            return v
        if t == 'C':
            pos[0] += 1
            a = p()
            b = p()
            return ('c', a, b)
        if t == 'A':
            pos[0] += 1
            n = toks[pos[0]]
            pos[0] += 1
            return ('a', int(n, 0))
        pos[0] += 1
        return ('n', t)
    return p()


memo = {}


def cells(v):
    if v[0] == 'c':
        return 1 + cells(v[1]) + cells(v[2])
    if v[0] == 'n' and v[1] in defs:
        if v[1] not in memo:
            memo[v[1]] = cells(parse_text(defs[v[1]]))
        return memo[v[1]]
    return 0


def show(cur, depth=0, lab=''):
    k = 0
    while cur[0] == 'c' and cur[1][0] == 'a' and cur[1][1] in (7, 8) and cur[2][0] == 'c':
        print('  ' * depth + lab + 'push', k, 'op', cur[1][1], 'head', cells(cur[2][1]), 'rest', cells(cur[2][2]))
        k += 1
        cur = cur[2][2]
    if cur[0] == 'c' and cur[1][0] == 'a' and cur[1][1] == 6:
        t, y, n = cur[2][1], cur[2][2][1], cur[2][2][2]
        print('  ' * depth + lab + '%6 test', cells(t), 'yes', cells(y), 'no', cells(n))
        if depth < 3:
            show(y, depth + 1, 'yes:')
            show(n, depth + 1, 'no:')
    else:
        print('  ' * depth + lab + 'tail', cells(cur), 'cells')


v = parse_text(defs['seTryPath'])
print('seTryPath: total cells', cells(v))
show(v)
