#!/usr/bin/env python3
# usage: passmeasure-show.py OUT.txt CASETAG ROOTMUG
# Prints one case's pass loop (root ROOTMUG) pass by pass: the members of every %pm-ent (mug, DFS
# number, entry classes, callees, +dirty) with the %pm-new, %pm-pass, %pm-end, %pm-cull lines
# between (track F, README Gaps 16; uses the parser of passmeasure-stab.py beside this script).
import os, sys
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure-stab.py')).read()
g = {}; exec(src.split("\nv = '-v'")[0], g)
path, casetag, root = sys.argv[1], sys.argv[2], sys.argv[3]
on = False
for l in g['pmlines'](path):
    t = l.strip('[]').split()
    if t[0] == '%pm-case': on = (t[2] == casetag); continue
    if not on: continue
    if t[0] == '%pm-ent':
        r, p, mem = g['parse_ent'](l)
        if r == root:
            print('pass', p)
            for m in mem: print('   ', m)
    elif t[0] in ('%pm-new', '%pm-end', '%pm-cull', '%pm-pass'): print(' ', l[:160])
