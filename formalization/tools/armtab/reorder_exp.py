#!/usr/bin/env python3
"""The `?=` reorder experiment of README Gaps 32 (track T), on COPIES of the
library:

    reorder_exp.py OUTDIR

writes OUTDIR/lib-noop.hoon (an unused arm `+track-t-noop` in the first core
of the library, s11, below every use site), lib-flat.hoon (the nested tag
sets flat: `+hint-dynamic`, `hint-free`, `hint-pure` and the four
`?(hint-safe %memo)`), lib-flat-noop.hoon (both).  Then build each pill
(U3NC_STEEL_GEN, 22 s each), `armtab.py table --lib` each copy, and
`switch.py A.pill B.pill --old-table --new-table --paths-only`.
"""
import os
import sys

FORM = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
d = sys.argv[1]
src = open(FORM + '/../desk/lib/nock-compilation.hoon').read()


def rep(s, old, new, n=1):
    assert s.count(old) == n, (old, s.count(old))
    return s.replace(old, new)


noop_old = "+$  spring  $~(~ *)\n--\n"
noop_new = "+$  spring  $~(~ *)\n++  track-t-noop  ~\n--\n"
flat = rep(src, "+$  hint-dynamic  ?(%bout %xray %spin %jinx %live hint-dynamic-stop)",
           "+$  hint-dynamic  ?(%bout %xray %spin %jinx %live %hunk %hand %lose %mean %spot %slog)")
flat = rep(flat, "=*  hint-free  ,?(hint-safe %fast %memo)",
           "=*  hint-free  ,?(%hunk %hand %lose %mean %spot %fast %memo)")
flat = rep(flat, "=*  hint-pure  ,?(hint-safe %fast %memo)",
           "=*  hint-pure  ,?(%hunk %hand %lose %mean %spot %fast %memo)")
flat = rep(flat, "?=(?(hint-safe %memo) ", "?=(?(%hunk %hand %lose %mean %spot %memo) ", 4)
os.makedirs(d, exist_ok=True)
open(d + '/lib-noop.hoon', 'w').write(rep(src, noop_old, noop_new))
open(d + '/lib-flat.hoon', 'w').write(flat)
open(d + '/lib-flat-noop.hoon', 'w').write(rep(flat, noop_old, noop_new))
