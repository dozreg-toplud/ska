"""The nouns of the map path of `+to-straight` (the branch of the `|^` core
with `proxies` `&`), cut into named parts, as Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/tsmap.py OUTFILE

The core is `tsCoreBat` (`slot? 268435453` of the gate `tsBat`, door arm
`6892`).  Each arm `[8 [1 BUNT] [1 BODY] 0 1]` gets `<p>Bunt` and `<p>Body`
and the kernel fact `<p>_at` on its battery axis: `rewrite-par` (`250`,
`tsmPar`), `rewrite-body` (`502`, `tsmBod`), `rewrite-op` (`2`, `tsmOp`),
`rewrite-fin` (`1006`, `tsmFin`), `rewrite-jump` (`255`, `tsmJmp`),
`rewrite-hop` (`124`, `tsmHop`), `rewrite-args` (`1007`, `tsmArg`).  The
gates built in place inside a body (the `+spin` gates) are `<p>G`, the mold
bunts they compute `<p>BuntF`.  The map branch of `$` (`tsMapBr`, slot `4095`
of the arm `$`) is cut into the gate of its `+rep:by` (`tsmGate`) and the
bunt of the gate's sample (`tsmRepBuntF`).  Parts are substituted by
structural equality, so each `_at` fact is `kernel_rfl`.  Writes OUTFILE
between `-- BEGIN tsmap` and `-- END tsmap`."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm, lean, eqn
OUT = sys.argv[1]
DOOR = ('R', 'comp.door')
core = slot(268435453, slot(109, slot(6892, DOOR)))

memo = {}
def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    k = id(n)
    if k not in memo:
        memo[k] = ('C', full(n[1]), full(n[2]))
    return memo[k]

def sl(ax, n):
    for b in bin(ax)[3:]:
        n = norm(n)
        assert n[0] == 'C'
        n = n[1] if b == '0' else n[2]
    return full(n)

def isA(n, v):
    n = norm(n)
    return n[0] == 'A' and n[1] == v

def gate_parts(arm):
    """[8 [1 BUNT] [1 BODY] 0 1] -> BUNT, BODY"""
    assert isA(sl(2, arm), 8) and isA(sl(12, arm), 1) and isA(sl(28, arm), 1)
    return sl(13, arm), sl(29, arm)

def inner_gates(n, out):
    """gates [8 S [1 G] 0 1] built inside n, innermost first"""
    n = norm(n)
    if n[0] != 'C':
        return
    inner_gates(n[1], out); inner_gates(n[2], out)
    if isA(n[1], 8):
        r = norm(n[2])
        if r[0] == 'C':
            g = norm(r[2])
            if g[0] == 'C' and norm(g[1])[0] == 'C' and isA(norm(g[1])[1], 1) and eqn(g[2], ('C', ('A', 0), ('A', 1))):
                out.append((full(r[1]), full(norm(g[1])[2])))

def size(n):
    n = norm(n)
    return 0 if n[0] == 'A' else 1 + size(n[1]) + size(n[2])

defs = []   # (name, noun, doc)
facts = []  # (name, axis, armnoun-expr)
ARMS = [(250, 'tsmPar', '`rewrite-par`'), (502, 'tsmBod', '`rewrite-body`'), (1007, 'tsmArg', '`rewrite-args`'),
        (255, 'tsmJmp', '`rewrite-jump`'), (124, 'tsmHop', '`rewrite-hop`'), (2, 'tsmOp', '`rewrite-op`'),
        (1006, 'tsmFin', '`rewrite-fin`')]
for ax, p, nm in ARMS:
    arm = sl(ax, core)
    bunt, body = gate_parts(arm)
    gs = []
    inner_gates(body, gs)
    for i, (s, g) in enumerate(gs):
        sfx = '' if len(gs) == 1 else str(i)
        defs.append((p + 'G' + sfx, g, 'The gate built inside the body of %s.' % nm))
        s = norm(s)
        if s[0] == 'C' and not isA(s[1], 1):
            defs.append((p + 'BuntF' + sfx, full(s), 'The formula of the bunt of the sample of `%sG%s`.' % (p, sfx)))
    defs.append((p + 'Body', body, 'The body of the gate %s (battery axis `%d` of `tsCoreBat`).' % (nm, ax)))
    facts.append((p, ax, arm))

dol = sl(126, core)
mb = sl(4095, dol)
gs = []
inner_gates(mb, gs)
assert len(gs) == 2
s, g = gs[1]
defs.append(('tsmGate', g, 'The gate of the `+rep:by` of the map branch.'))
defs.append(('tsmRepBuntF', s, 'The bunt of the sample of `tsmGate`: `[[0 blob] [(map) gen]]`.'))

with open(OUT) as f:
    text = f.read()
a = text.index('-- BEGIN tsmap')
b = text.index('-- END tsmap')
out = ['-- BEGIN tsmap\n']
subs = []
for name, n, doc in defs:
    if doc:
        out.append('/-- %s -/\n' % doc)
    out.append('def %s : Noun :=\n  %s\n\n' % (name, lean(n, subs)))
    if size(n) >= 8:
        subs.insert(0, (name, n))
for p, ax, arm in facts:
    out.append('theorem %s_at : slot? %d tsCoreBat = some %s := by\n  kernel_rfl\n\n' % (p, ax, lean(arm, subs)))
out.append('/-- **The map branch of `$`**, cut into its parts. -/\n')
out.append('theorem tsm_br_eq : tsMapBr = %s := by\n  unfold tsMapBr tsDolArm\n  kernel_rfl\n\n' % lean(mb, subs))
for name, n, doc in defs:
    print(name, size(n))
open(OUT, 'w').write(text[:a] + ''.join(out) + text[b:])
