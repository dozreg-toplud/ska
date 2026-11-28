#!/usr/bin/env python3
"""Check the axes that the proofs use against the arm table (track T, README
Gaps 32).

    axischeck.py [--table armtab.json] [--names names.json] [--cited cited.json] > axischeck.txt

(`--cited`: the paths of part B that matched, for armlean.py)

Part A: every fact `X.arm_at : slot? X.axis Y = some X.arm` (or `∀ x, slot?
X.axis (C Y x) = some ..`, or a core `slot? X.axis Y = some Z`) of
lemmas/Pill/Facts.lean, with the constant `X.axis` of lemmas/Pill/Arm: Y is
mapped to its path through names.json (the Lean name of the core or of its
battery), the arm by its name (`_` read as `-`, or ABBR), and the constant
must be the arm's axis in the core (cax), or the core Z's axis in Y.

Part B: every mention in a file outside lemmas/Pill (and the notes
tools/pillswitch-*.md, README.md) of the form `+name` ... (arm|axis|battery
axis|door arm|...) `N`: N must be the battery axis (bax) or the core axis
(cax) of an arm called `name` in the table; the line says which, or MISS
with the axes the table has for that name.
"""
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FORM = os.path.normpath(os.path.join(HERE, '..', '..'))

ABBR = {'mfe': 'memo-final-entry', 'ska_cg': 'ska-callgraph', 'prune_cg': 'prune-callgraph',
        'ident_mold': 'identity', 'soft': 'soft', 'register_fast': 'register-fast'}


def main():
    a = sys.argv[1:]

    def opt(k, d):
        return a[a.index(k) + 1] if k in a else d
    tab = json.load(open(opt('--table', HERE + '/armtab.json')))
    nam = json.load(open(opt('--names', HERE + '/names.json')))
    arms, cores = tab['arms'], tab['cores']
    # Lean name of a core or battery -> core path
    lean2core = {}
    for p, e in nam['cores'].items():
        for n in e.get('battery', []) + e.get('core', []):
            lean2core.setdefault(n, p)
    axes = {}
    for f in glob.glob(FORM + '/lemmas/Pill/Arm/*.lean'):
        for m in re.finditer(r'abbrev ([A-Za-z0-9_.]+)\.axis : Nat := ([0-9]+)', open(f).read()):
            axes[m.group(1)] = int(m.group(2))
    facts = open(FORM + '/lemmas/Pill/Facts.lean').read()
    pat = re.compile(r'theorem ([A-Za-z0-9_.]+)\.arm_at : (?:∀ x, )?slot\? \1\.axis '
                     r'(?:\(C ([A-Za-z0-9_.]+) x\)|([A-Za-z0-9_.]+)) = some ([A-Za-z0-9_.]+)')
    ok = bad = unm = 0
    out = []
    for m in pat.finditer(facts):
        x, y, rhs = m.group(1), m.group(2) or m.group(3), m.group(4)
        n = axes.get(x)
        cp = lean2core.get(y)
        if cp is None or n is None:
            out.append('A  UNMAPPED  %s  in %s  (%s)' % (x, y, n))
            unm += 1
            continue
        if rhs == x + '.arm':
            last = x.split('.')[-1]
            cands = [ABBR.get(last, last.replace('_', '-')), last]
            ps = [cp + '/' + c for c in cands if cp + '/' + c in arms]
            if not ps:
                out.append('A  UNMAPPED  %s = %d  in %s = %s: no arm %s' % (x, n, y, cp, cands[0]))
                unm += 1
                continue
            t = arms[ps[0]]['cax']
            what = ps[0]
        else:
            zp = lean2core.get(rhs)
            if zp is None or cores[zp]['abs'] is None or cores[cp]['abs'] is None:
                out.append('A  UNMAPPED  %s = %d: %s in %s' % (x, n, rhs, y))
                unm += 1
                continue
            za, ya = bin(cores[zp]['abs'])[2:], bin(cores[cp]['abs'])[2:]
            t = int('1' + za[len(ya):], 2) if za.startswith(ya) else None
            what = '%s in %s' % (zp, cp)
        if t == n:
            ok += 1
            out.append('A  ok    %-28s %10d  %s' % (x, n, what))
        else:
            bad += 1
            out.append('A  MISS  %-28s %10d  %s has %s' % (x, n, what, t))
    print('Part A (lemmas/Pill/Facts.lean): %d ok, %d mismatched, %d unmapped' % (ok, bad, unm))
    # ---- part B
    by_name = {}
    for p, e in arms.items():
        by_name.setdefault(p.split('/')[-1], []).append((p, e))
    files = [f for f in glob.glob(FORM + '/lemmas/**/*.lean', recursive=True)
             if '/lemmas/Pill/' not in f]
    files += glob.glob(FORM + '/tools/pillswitch-*.md') + [FORM + '/README.md']
    men = re.compile(r'`\+([a-z][a-z0-9-]*)`[^.`;]{0,30}?\(?((?:door |core |K )?(?:battery )?'
                     r'(?:arm|axis))\s+`([0-9]+)`')
    seen = set()
    cited = set()
    bok = bmiss = bunk = 0
    lines = []
    for f in sorted(files):
        for k, ln in enumerate(open(f), 1):
            for m in men.finditer(ln):
                nm, how, n = m.group(1), m.group(2), int(m.group(3))
                key = (nm, n)
                if key in seen:
                    continue
                seen.add(key)
                src = '%s:%d' % (os.path.relpath(f, FORM), k)
                cs = by_name.get(nm, [])
                hit = [(p, w) for p, e in cs for w in ('bax', 'cax') if e[w] == n]
                if hit:
                    cited.add(hit[0][0])
                    bok += 1
                    lines.append('B  ok    +%-24s %10d  %s %s  (%s: %s)' % (
                        nm, n, hit[0][0], hit[0][1], how, src))
                elif cs:
                    bmiss += 1
                    lines.append('B  MISS  +%-24s %10d  table: %s  (%s: %s)' % (
                        nm, n, ', '.join('%s bax %d cax %d' % (p, e['bax'], e['cax'])
                                         for p, e in cs[:4]), how, src))
                else:
                    bunk += 1
                    lines.append('B  none  +%-24s %10d  no arm of that name  (%s: %s)' % (
                        nm, n, how, src))
    print('Part B (texts): %d distinct (name, axis) mentions: %d ok, %d mismatched, %d with no '
          'arm of that name' % (bok + bmiss + bunk, bok, bmiss, bunk))
    print()
    for ln in out + lines:
        print(ln)
    if '--cited' in a:
        json.dump(sorted(cited), open(a[a.index('--cited') + 1], 'w'), indent=0)


if __name__ == '__main__':
    main()
