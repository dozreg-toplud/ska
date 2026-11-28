#!/usr/bin/env python3
"""The report of a pill switch, by Hoon path (track T, README Gaps 32).

    switch.py OLD.pill NEW.pill [--old-table T] [--new-table T]
              [--old-lean DIR] [--new-lean DIR] [--old-hand ROOT]

OLD.pill, NEW.pill: the two steel pills.  Tables: tools/armtab/armtab.json
for both unless given (arm axes follow arm names: one table serves both
pills when no arm was added, removed or renamed; else run `armtab.py table
--lib OLD_LIB --out T`).  `--old-lean`, `--new-lean`: the generated
lemmas/Pill of each pill (default: this worktree's for NEW; the old one from
git, `git archive <commit> formalization/lemmas`).  `--old-hand`: the
`formalization/` tree whose hand-written files hold the old names (default:
this worktree).  Prints:

  1. the arms whose Nock changed, by path: OWN (no other changed path noun
     inside: the arm's own formula changed) and HELD (changed because a
     changed arm or battery is inside), the batteries that changed, the
     arms and cores added or removed, and how many are unchanged;
  2. for every hash name of lemmas/Pill that a file outside lemmas/Pill
     mentions: its old noun, where it sits (path and axis), and its new name
     (the noun at the same path and axis in the new pill), `=` if the noun
     did not change;
  3. the nouns written out in files outside lemmas/Pill (bodies of `def X :
     Noun :=` made of C, A and names) that are in the old pill and not in the
     new one: the files to regenerate, with the generator that the file
     names (tools/gen/*.py) and the changed path that holds the old noun.
"""
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pilltab as T                     # noqa: E402
from pilltab import NODES               # noqa: E402


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
            todo.append(n[0])
            todo.append(n[1])
    return seen


def size(i):
    n = tree_size(i)
    return n if n < 10 ** 7 else len(reach([i]))


def tree_size(i, memo={}):
    if i in memo:
        return memo[i]
    order = []
    todo = [i]
    while todo:
        j = todo.pop()
        if j in memo:
            continue
        n = NODES[j]
        if type(n) is int:
            memo[j] = 0
            continue
        if n[0] in memo and n[1] in memo:
            memo[j] = 1 + memo[n[0]] + memo[n[1]]
            continue
        todo.append(j)
        todo.extend(k for k in n if k not in memo)
        order.append(j)
    return memo[i]


DEFRE = re.compile(r'^(?:public |private |protected )*(?:noncomputable )?(?:def|abbrev) '
                   r'([A-Za-z0-9_.\']+) : Noun :=\s*(.*)$')
GENRE = re.compile(r'tools/gen/([A-Za-z0-9_]+\.py)')


def hand_nouns(root, env):
    """(file, name) -> noun id of the noun literals of files outside
    lemmas/Pill, with names resolved in the file and in env"""
    out = {}
    for f in sorted(glob.glob(root + '/lemmas/**/*.lean', recursive=True)):
        if '/lemmas/Pill/' in f:
            continue
        lines = open(f).read().split('\n')
        texts = {}
        k = 0
        while k < len(lines):
            m = DEFRE.match(lines[k])
            if not m:
                k += 1
                continue
            body = [m.group(2)]
            k += 1
            while k < len(lines) and lines[k].startswith(' ') and lines[k].strip():
                body.append(lines[k])
                k += 1
            texts[m.group(1)] = ' '.join(body)
        if not texts:
            continue
        loc = dict(texts)
        # names of the Pill resolve to env: give them as constant bodies
        toks = set(t for b in texts.values() for t in T.TOK.findall(b))
        allt = dict(loc)
        envn = {}
        for t in toks:
            if t not in loc and t in env:
                envn[t] = env[t]
        ids = parse_with_env(allt, envn)
        for nm, i in ids.items():
            out[(os.path.relpath(f, root), nm)] = i
    return out


def parse_with_env(texts, env):
    toks = {nm: T.TOK.findall(b) for nm, b in texts.items()}
    res = dict(env)
    bad = set()

    def ok(nm, depth=0):
        if nm in res:
            return True
        if nm in bad or nm not in toks or depth > 200:
            return False
        for t in toks[nm]:
            if t in ('C', 'A', '(', ')') or t[0].isdigit():
                continue
            if not ok(t, depth + 1):
                bad.add(nm)
                return False
        try:
            res[nm] = T.build(toks[nm], res)
        except Exception:
            bad.add(nm)
            return False
        return True
    for nm in toks:
        ok(nm)
    return {nm: i for nm, i in res.items() if nm in toks}


def main():
    a = sys.argv[1:]
    oldp, newp = a[0], a[1]

    def opt(k, d=None):
        return a[a.index(k) + 1] if k in a else d
    newtab = T.load_table(opt('--new-table'))
    oldtab = T.load_table(opt('--old-table')) if opt('--old-table') else newtab
    O = T.load_pill(oldp)
    Nw = T.load_pill(newp)
    print('old pill %s (%d bytes), new pill %s (%d bytes)' % (O['sha'][:16], O['size'],
                                                              Nw['sha'][:16], Nw['size']))
    obat, oarm, ocor, obad = T.locate(oldtab, O['core'])
    nbat, narm, ncor, nbad = T.locate(newtab, Nw['core'])
    for p, w in sorted(obad.items()):
        print('  old pill: not located', p, w)
    for p, w in sorted(nbad.items()):
        print('  new pill: not located', p, w)

    # ---- 1. paths
    onoun = {('arm', p): i for p, i in oarm.items()}
    onoun.update({('bat', p): i for p, i in obat.items()})
    nnoun = {('arm', p): i for p, i in narm.items()}
    nnoun.update({('bat', p): i for p, i in nbat.items()})
    both = set(onoun) & set(nnoun)
    changed = sorted(k for k in both if onoun[k] != nnoun[k])
    same = [k for k in both if onoun[k] == nnoun[k]]
    # strict ancestors (in the old pill) of the changed nouns
    par = T.parents_map([O['core']])
    marked = set()
    todo = [p for k in changed for p, _ in par.get(onoun[k], ())]
    while todo:
        j = todo.pop()
        if j in marked:
            continue
        marked.add(j)
        todo.extend(p for p, _ in par.get(j, ()))
    own = [k for k in changed if k[0] == 'arm' and onoun[k] not in marked]
    held = [k for k in changed if k[0] == 'arm' and onoun[k] in marked]
    bats = [k for k in changed if k[0] == 'bat']
    print()
    print('1. Paths: %d arms and %d batteries in both pills; %d unchanged, %d changed'
          % (sum(1 for k in both if k[0] == 'arm'), sum(1 for k in both if k[0] == 'bat'),
             len(same), len(changed)))
    print('   OWN (the arm\'s formula changed, no changed path inside): %d' % len(own))
    for k in own:
        print('     %-50s %7d -> %7d cells (or distinct cells past 10^7)'
              % (k[1], size(onoun[k]), size(nnoun[k])))
    print('   HELD (a changed arm or battery inside): %d arms' % len(held))
    for k in held:
        print('     ' + k[1])
    print('   batteries changed: %d' % len(bats))
    for k in bats:
        print('     ' + k[1])
    for k in sorted(set(onoun) - set(nnoun)):
        print('   only in the old pill: %s %s' % k)
    for k in sorted(set(nnoun) - set(onoun)):
        print('   only in the new pill: %s %s' % k)

    # ---- 2. hash names of hand-written files
    oldlean = opt('--old-lean')
    newlean = opt('--new-lean', os.path.join(T.FORM, 'lemmas', 'Pill'))
    hroot = opt('--old-hand', T.FORM)
    nrev, nids = T.lean_names(newlean)
    if oldlean:
        orev, oids = T.lean_names(oldlean)
    else:
        orev, oids = nrev, nids
    hand = T.hand_names(hroot)
    targets = {}
    for k in both:
        targets.setdefault(onoun[k], k)
    for p in set(ocor) & set(ncor):
        onoun[('core', p)] = ocor[p]
        nnoun[('core', p)] = ncor[p]
        targets.setdefault(ocor[p], ('core', p))
    print()
    print('2. Hash names of lemmas/Pill used outside it: %d' % len(hand))
    pairs = []
    for h in sorted(hand):
        i = oids.get(h)
        if i is None:
            print('   %s: not a name of the old lemmas/Pill (%s)' % (h, ', '.join(sorted(hand[h]))[:80]))
            continue
        if i in nrev:
            new = nrev[i][0]
            where = ''
        else:
            j, ax = T.place(i, set(targets), par)
            if j is None:
                print('   %s: not under a path' % h)
                continue
            kind, p = targets[j]
            ni = T.slot_or_none(ax, nnoun[(kind, p)])
            new = nrev.get(ni, ['(no name in the new lemmas/Pill)'])[0] if ni is not None else '(gone)'
            where = '%s of %s at %d' % ({'arm': 'arm', 'bat': 'battery', 'core': 'core'}[kind], p, ax)
        mark = '=' if new == h else ''
        if new != h:
            pairs.append((h, new))
        print('   %s %s %s  %s  [%s]' % (h, new, mark, where, ', '.join(sorted(hand[h]))))
    print('   pairs to rename (old new):')
    for h, n in pairs:
        print('   ' + h + ' ' + n)

    # ---- 3. noun literals of hand-written files
    print()
    newreach = reach([Nw['core'], Nw['root']])
    oldreach = reach([O['core'], O['root']])
    lits = hand_nouns(hroot, oids)
    stale = {}
    for (f, nm), i in sorted(lits.items()):
        if i in oldreach and i not in newreach:
            stale.setdefault(f, []).append((nm, i))
    print('3. Noun literals outside lemmas/Pill: %d parsed; %d in the old pill and not in the '
          'new one, in %d files' % (len(lits), sum(len(v) for v in stale.values()), len(stale)))
    for f, defs in sorted(stale.items()):
        gens = sorted(set(GENRE.findall(open(os.path.join(hroot, f)).read())))
        print('   %s  (generator: %s)' % (f, ', '.join(gens) or 'none named: by hand'))
        for nm, i in defs:
            j, ax = T.place(i, set(targets), par)
            w = '%s %s at %d' % (targets[j][0], targets[j][1], ax) if j is not None else '?'
            print('     %-24s %7d cells, in %s' % (nm, size(i), w))


if __name__ == '__main__':
    main()
