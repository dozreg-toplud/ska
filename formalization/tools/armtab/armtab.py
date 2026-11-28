#!/usr/bin/env python3
"""The arm table and the names of the pill's nouns by Hoon path (track T,
README Gaps 32).

    armtab.py table [--lib LIB.hoon] [--out armtab.json] [--rows ROWS.tsv]
    armtab.py names [--pill P] [--lean DIR] [--table T] [--out names.json]
    armtab.py all          both, for this worktree's library and pill

`table` runs tools/hoon/armtab.hoon on hoon.hoon and the library (the copy
runhoon-here.sh of tools/hoon/runhoon.sh, about 15 s; `--lib` another
library, as RUNHOON_LIB) and writes the JSON:

    cores: path -> {abs, kind, hoon}     abs: axis in the core of the pill
                                         (`core` of lemmas/Pill), or null for
                                         a core built at run time
    arms:  path -> {bax, cax, abs, kind} bax: axis in the battery, cax: in
                                         the core, abs: in `core` or null
    alias: the names that lemmas/Pill and the link files give spine cores

A path is `s<i>` (the i-th core of the subject's tail spine, s0 the outer
SKA core) followed by arm names; `$` is the arm of a gate.  kind: `value`,
`gate`, `door`, `core` (a |% on the arm's subject), `trap`, `cory` (a core
on something else, e.g. under a =/ or =*), `spine`.

`names` locates every path in the pill (a spine core by its axis, a core
built by an arm by the battery its formula quotes, `[[1 bat] 0 1]` under 7s,
8s and %fast hints; every battery is checked to have its arms exactly at the
table's axes) and writes, for each path, the Lean names of lemmas/Pill whose
noun is that arm's formula (`arm`) or that core's battery (`battery`), and
the nearest named noun that holds it with the axis (`in`).
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pilltab as T  # noqa: E402

ALIAS = {
    # the spine, as lemmas/Pill and core/Statement.lean name it
    'core': 's0', 'interp': 's1', 'cor': 's2', 'K': 's6', 'optC': 's5', 'ana': 's8',
    'lib': 's10', 'layer5': 's12', 'layer4': 's13', 'layer3': 's14', 'layer2': 's15',
    'layer1': 's16', 'layer0': 's17',
}


def run_table(lib=None, rows_out=None):
    env = dict(os.environ)
    if lib:
        env['RUNHOON_LIB'] = os.path.abspath(lib)
    out = subprocess.run([os.path.join(HERE, 'runhoon-here.sh'),
                          os.path.join(T.FORM, 'tools', 'hoon', 'armtab.hoon'), '900'],
                         env=env, capture_output=True, text=True).stdout
    lines = out.split('\n')
    try:
        b = lines.index("'armtab-begin'")
        e = lines.index("'armtab-end'", b)
    except ValueError:
        sys.exit('armtab.hoon failed:\n' + '\n'.join(lines[-20:]))
    rows = [ln.strip("'").replace('\\09', '\t') for ln in lines[b + 1:e]]
    if rows_out:
        open(rows_out, 'w').write('\n'.join(rows) + '\n')
    cores, arms = {}, {}
    for r in rows:
        f = r.split('\t')
        if f[0] == 'C':
            cores[f[1]] = dict(abs=None if f[2] == '-' else int(f[2]), kind=f[3], hoon=f[4] == 'y')
        elif f[0] == 'A':
            arms[f[1]] = dict(bax=int(f[2]), cax=int(f[3]),
                              abs=None if f[4] == '-' else int(f[4]), kind=f[5])
        else:
            sys.exit('bad row ' + r)
    return dict(cores=cores, arms=arms, alias=ALIAS)


def run_names(tab, pill, lean):
    P = T.load_pill(pill)
    bat, arm, cnoun, bad = T.locate(tab, P['core'])
    rev, ids = T.lean_names(lean)
    named = set(rev)
    par = T.parents_map([P['core']])

    def where(i):
        if i in rev:
            return None
        j, ax = T.place(i, named, par)
        return None if j is None else [rev[j][0], ax]
    out = {'pill': dict(sha256=P['sha'], bytes=P['size']), 'cores': {}, 'arms': {},
           'unlocated': bad}
    for p in sorted(bat):
        out['cores'][p] = dict(battery=rev.get(bat[p], []), **({'in': where(bat[p])} if bat[p] not in rev else {}))
        if p in cnoun:
            out['cores'][p]['core'] = rev.get(cnoun[p], [])
    for p in sorted(arm):
        e = dict(arm=rev.get(arm[p], []))
        if arm[p] not in rev:
            e['in'] = where(arm[p])
        out['arms'][p] = e
    return out


def main():
    a = sys.argv[1:]
    cmd = a[0] if a else 'all'

    def opt(k, d=None):
        return a[a.index(k) + 1] if k in a else d
    tpath = opt('--table', os.path.join(HERE, 'armtab.json'))
    if cmd in ('table', 'all'):
        tab = run_table(opt('--lib'), opt('--rows'))
        out = opt('--out', tpath) if cmd == 'table' else tpath
        json.dump(tab, open(out, 'w'), indent=0, sort_keys=True)
        print('table: %d cores, %d arms -> %s' % (len(tab['cores']), len(tab['arms']), out))
    if cmd in ('names', 'all'):
        tab = T.load_table(tpath)
        pill = opt('--pill', os.path.join(T.FORM, 'pill', 'steel.pill'))
        lean = opt('--lean', os.path.join(T.FORM, 'lemmas', 'Pill'))
        res = run_names(tab, pill, lean)
        out = opt('--out', os.path.join(HERE, 'names.json')) if cmd == 'names' else \
            os.path.join(HERE, 'names.json')
        json.dump(res, open(out, 'w'), indent=0, sort_keys=True)
        nn = sum(1 for e in res['arms'].values() if e['arm'])
        print('names: %d cores and %d arms located (%d arms with a Lean name), %d not -> %s'
              % (len(res['cores']), len(res['arms']), nn, len(res['unlocated']), out))
        for p, why in sorted(res['unlocated'].items()):
            print('  unlocated', p, why)


if __name__ == '__main__':
    main()
