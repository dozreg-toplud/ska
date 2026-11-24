#!/usr/bin/env python3
# usage: closedsteps.py OUTDIR
# Writes OUTDIR/nc.hoon, a copy of desk/lib/nock-compilation.hoon whose +cull and +pop print
# the closure checks of lemmas/Ska/GraphClose.lean at every state they see, and OUTDIR/drv.hoon
# (closed.hoon).  Run: RUNHOON_LIB=OUTDIR/nc.hoon runhoon.sh OUTDIR/drv.hoon 900
# [%cullchk n f m]: n callee edges from entries outside the component, f of them into it, m
# callees of any entry missing from the graph.  [%popchk n f m]: n callee edges of finalized
# entries after the pop, f of them to an identity in order, m missing from the graph.
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
s = open(os.path.join(D, '../../../desk/lib/nock-compilation.hoon')).read()
old_cull = """    =/  members=(set identity)  (silt (above id stk.st))
    =/  live=(set identity)"""
new_cull = """    =/  members=(set identity)  (silt (above id stk.st))
    =/  chk
      %-  ~(rep by g.st)
      |=  [[i=identity d=datum] n=@ud f=@ud m=@ud]
      %-  ~(rep in callees.d)
      |=  [c=callee-entry n=_n f=_f m=_m]
      :+  ?:((~(has in members) i) n +(n))
        ?:(&(!(~(has in members) i) (~(has in members) id.c)) +(f) f)
      ?:((~(has by g.st) id.c) m +(m))
    ~&  [%cullchk n=-.chk f=+<.chk m=+>.chk]
    =/  live=(set identity)"""
old_pop = """    =.  done.st   (put:mi done.st top d)
    ?:  =(top id)  st
    $"""
new_pop = """    =.  done.st   (put:mi done.st top d)
    ?:  =(top id)
      =/  chk
        %-  ~(rep by g.st)
        |=  [[i=identity d=datum] n=@ud f=@ud m=@ud]
        ?:  (~(has by order.st) i)  [n f m]
        %-  ~(rep in callees.d)
        |=  [c=callee-entry n=_n f=_f m=_m]
        [+(n) ?:((~(has by order.st) id.c) +(f) f) ?:((~(has by g.st) id.c) m +(m))]
      ~&  [%popchk n=-.chk f=+<.chk m=+>.chk]
      st
    $"""
assert s.count(old_cull) == 1 and s.count(old_pop) == 1
s = s.replace(old_cull, new_cull).replace(old_pop, new_pop)
open(os.path.join(out, 'nc.hoon'), 'w').write(s)
open(os.path.join(out, 'drv.hoon'), 'w').write(open(os.path.join(D, 'closed.hoon')).read())
