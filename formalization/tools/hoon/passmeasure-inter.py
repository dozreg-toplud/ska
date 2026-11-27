#!/usr/bin/env python3
# usage: passmeasure-inter.py OUTDIR
# Matches the failures of candidate D of passmeasure-stab.py on OUTDIR/u*.out (the cores of
# passmeasure-u.py) with the cases that have a %rec takeover (a (caller, kid) pair resolved to two
# targets in turn, %pm-rec / %pm-ex) and an A..B..A return (track F, README Gaps 16: all 39 cases
# with a D failure have a takeover, 11 a return, 2026-11-27).
import os, sys, glob, io, contextlib, re
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure-stab.py')).read()
g = {}; exec(src.split("\nv = '-v'")[0], g)
files = sorted(glob.glob(sys.argv[1] + '/u*.out'))
ret = set(); take = set()
for p in files:
    case = None; seq = {}
    def flush():
        for k, v in seq.items():
            c = [v[0]]
            for t in v[1:]:
                if t != c[-1]: c.append(t)
            if len(c) > 1: take.add((p, case))
            if len(set(c)) < len(c): ret.add((p, case))
    for l in g['pmlines'](p):
        t = l.strip('[]').split()
        if t[0] == '%pm-case': flush(); seq = {}; case = t[2]
        elif t[0] == '%pm-rec': seq.setdefault((t[1], t[2]), []).append(t[3])
        elif t[0] == '%pm-ex': seq.setdefault((t[1], t[2]), []).append(t[2])
    flush()
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    g['analyse'](files, True)
dcases = set(); on = False
for l in buf.getvalue().split('\n'):
    if l.startswith('fails of candidate D:'): on = True; continue
    if l.startswith('fails of'): on = False
    if on and l.strip():
        m = re.match(r"\s*\(\('(u\d+)\.out', '\[%pm-case \d+ (%\S+)\]'\)", l)
        if m: dcases.add((m.group(1), m.group(2)))
retc = {(p.split('/')[-1][:-4], c) for p, c in ret}
takec = {(p.split('/')[-1][:-4], c) for p, c in take}
print('cases with an A..B..A return', len(retc), 'with a takeover', len(takec))
print('cases with a D failure', len(dcases), 'of them with a return', len(dcases & retc), 'with a takeover', len(dcases & takec))
