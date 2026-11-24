#!/usr/bin/env python3
# usage: selfkeep.py OUTDIR
# The register facts of lemmas/Ska/CompUnproxyRegs.lean on the real compiler.  Writes into OUTDIR
# an instrumented copy of desk/lib/nock-compilation.hoon (lib.hoon: every run of +comp's `run` in
# %run mode prints [%ck-ok px |sur| |wri| |lzr| |keys| |sur&keys|] or [%ck-bad ...]) and a driver
# (ck.hoon: the 74 formulas of thread-a.hoon and the two cases of proxy-dump.hoon, through
# +ska-poke, +scc-of, +compiled-mono).  Run:
#   RUNHOON_LIB=OUTDIR/lib.hoon tools/hoon/runhoon.sh OUTDIR/ck.hoon 550 > out.txt
# A %ck-bad line is a failure.  Checked: i1 the ops a run emits (new blocks, ops put in front of
# old blocks, parameters of new blocks and of the targets of new jumps with arguments) write no
# register of its result's sure need; i2 no register of a need of the result (sure need, every
# lazy entry's) is a key of cond; i3 those ops write no register of a lazy entry's need; i4 the
# sure need and the entries' needs share no register.  px: the run made a proxy.
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
HELPERS = r'''++  chk-run
  |=  [g0=line-short nex=next g1=line-short]
  ^-  *
  =/  sur=(set @uvre)  (silt (chk-flat ned.sure.laz.nex))
  =/  lzr=(set @uvre)  (chk-lazy-regs laz.nex)
  =/  wri=(set @uvre)  (chk-writes g0 g1)
  =/  keys=(set @uvre)  ~(key by cond.g1)
  =/  i1=?  =(~ (~(int in sur) wri))
  =/  i2=?  &(=(~ (~(int in sur) keys)) =(~ (~(int in lzr) keys)))
  =/  i3=?  =(~ (~(int in lzr) wri))
  =/  i4=?  =(~ (~(int in lzr) sur))
  =/  px=?  !=(cond.g0 cond.g1)
  ?:  &(i1 i2 i3 i4)  [%ck-ok px ~(wyt in sur) ~(wyt in wri) ~(wyt in lzr) ~(wyt in keys) ~(wyt in (~(int in sur) keys))]
  [%ck-bad i1=i1 i2=i2 i3=i3 i4=i4 px=px sur=sur lzr=lzr wri=wri keys=keys]
::
++  chk-flat
  |=  ned=need
  ^-  (list @uvre)
  ?-  -.ned
    %none  ~
    %this  ~[r.ned]
    ^      (weld (chk-flat -.ned) (chk-flat +.ned))
    %both  [r.ned (weld (chk-flat h.ned) (chk-flat t.ned))]
  ==
::
++  chk-lazy-regs
  |=  laz=need-lazy
  ^-  (set @uvre)
  =/  out=(set @uvre)  ~
  =.  out
    %+  roll  fork.laz
    |=  [[y=[o=@uwoo laz=need-lazy] n=[o=@uwoo laz=need-lazy]] acc=_out]
    ^-  (set @uvre)
    %-  ~(uni in acc)
    %-  ~(uni in (silt (chk-flat ned.sure.laz.y)))
    %-  ~(uni in (chk-lazy-regs laz.y))
    %-  ~(uni in (silt (chk-flat ned.sure.laz.n)))
    (chk-lazy-regs laz.n)
  %+  roll  bond.laz
  |=  [[o=@uwoo laz=need-lazy] acc=_out]
  ^-  (set @uvre)
  %-  ~(uni in acc)
  %-  ~(uni in (silt (chk-flat ned.sure.laz)))
  (chk-lazy-regs laz)
::
++  chk-dst
  |=  op=pole
  ^-  (unit @uvre)
  ?+  -.op  ~
    %imm  `d.op
    %mov  `d.op
    %inc  `d.op
    %con  `d.op
    %hed  `d.op
    %tal  `d.op
    %spy  `d.op
    %nok  `d.op
    %cal  `d.op
    %caf  `d.op
    %cam  `d.op
    %csl  `d.op
    %csf  `d.op
    %csm  `d.op
  ==
::
++  chk-jump-pars
  |=  [g=line-short f=termin]
  ^-  (list @uvre)
  =/  js=(list jmp)
    ?+  -.f  ~
      %hop  ~[t.f]
      %brn  ~[z.f o.f]
      %brz  ~[z.f o.f]
      %clq  ~[z.f o.f]
      %eqq  ~[z.f o.f]
    ==
  %-  zing
  %+  turn  js
  |=  j=jmp
  ^-  (list @uvre)
  ?~  args.j  ~
  =/  b=(unit blob)  (~(get by blocks.g) there.j)
  ?~  b  ~
  par.u.b
::
++  chk-writes
  |=  [g0=line-short g1=line-short]
  ^-  (set @uvre)
  =/  l=(list [k=@uwoo b=blob])  ~(tap by blocks.g1)
  =|  acc=(list @uvre)
  |-  ^-  (set @uvre)
  ?~  l  (silt acc)
  =/  k=@uwoo  k.i.l
  =/  b=blob  b.i.l
  =/  has=?  (~(has by blocks.g0) k)
  =/  ob=blob  ?:(has (~(got by blocks.g0) k) b)
  ?:  &(has =(ob b))  $(l t.l)
  =/  bod=(list pole)  body.b
  =/  obd=(list pole)  ?:(has body.ob ~)
  =/  n=@ud  (lent bod)
  =/  m=@ud  (lent obd)
  =/  pre=?  &((gte n m) =((slag (sub n m) bod) obd))
  =/  new-ops=(list pole)  ?:(pre (scag (sub n m) bod) bod)
  =/  dsts=(list @uvre)  (murn new-ops chk-dst)
  =/  pars=(list @uvre)  ?:(has ~ par.b)
  =/  newfin=?  |(!has !=(fin.b fin.ob))
  =/  tgts=(list @uvre)  ?.(newfin ~ (chk-jump-pars g1 fin.b))
  $(l t.l, acc :(weld dsts pars tgts acc))
::'''
WRAP = r'''    =/  gen0=_gen  gen
    =;  res=[next _gen]
      ?.  ?=(%run mode.+.res)  res
      ~&  (chk-run gen0 -.res +.res)
      res'''
src = open(os.path.join(W, 'desk/lib/nock-compilation.hoon')).read().split('\n')
i = src.index('++  comp')
assert src[i + 12].strip().startswith('|^  ^-  [next _gen]')
lib = src[:i] + HELPERS.split('\n') + src[i:i + 13] + WRAP.split('\n') + src[i + 13:]
open(os.path.join(out, 'lib.hoon'), 'w').write('\n'.join(lib))
ta = open(os.path.join(D, 'thread-a.hoon')).read().split('\n')
n = next(k for k, l in enumerate(ta) if l == '  ==')
drv = ta[:n] + [
  '      [100 %h [0 5] [7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]]',
  '      [101 %c [1 0 0 5] [7 [6 [0 2] [1 0] [6 [0 6] [0 7] [0 1]]] [6 [0 2] [0 3] [0 1]]]]',
  '  ==', '|-  ^-  @', '?~  cases  0', '~&  [%case nam.i.cases]',
  '=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state',
  '  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))',
  '=^  scc=(set bell)  sccs.cache.state', '  (scc-of func calls.long-ska.state sccs.cache.state)',
  '=^  raw=straight  cache.state  (compiled-mono func scc)', '$(cases t.cases)', '']
open(os.path.join(out, 'ck.hoon'), 'w').write('\n'.join(drv))
