#!/usr/bin/env python3
# usage: splitmax.py OUT.hoon [--fix none|nocut|loop|sticky|late] [--trace [--small]] [--in LIB]
# Track S (README Gaps 30): +split-max in the sweep loop of +compile-scc-in.  Writes a COPY of the
# library (default desk/lib/nock-compilation.hoon of this worktree); every textual patch asserts
# that its text occurs exactly once.  desk/ is never written.
#   --fix none     unpatched
#   --fix nocut    the cut line of +msg-need-ord removed (forks and loop): split-max infinite
#   --fix loop     the join of the sweep loop (line 3601) is +msg-need-ord-uncut, a copy of
#                  +msg-need-ord without the cut line; the forks (+laze-collapse) keep the cut
#   --fix sticky   the join is +msg-need-ord, but once it cut (its result differs from the uncut
#                  join), the member's entry is frozen: later joins keep it.  The flag is the
#                  n-args field of the placeholder straight (only need is read off %done)
#   --fix late     the join is uncut until the loop is stable; then one more sweep compiles every
#                  member with the cut join; a member whose entry that cut changes is frozen at
#                  the cut entry (as sticky) and the loop goes on; it ends with a cut sweep that
#                  changes nothing
#   --trace        prints, as raw nouns (bells, SCCs as mugs):
#     [%sc S size]                     the loop starts on SCC S (not for a lone bell without
#                                      self call)
#     [%sw S counter]                  a sweep starts ([%sx S counter] a late cut sweep)
#     [%s0 S b mode need-new cape]     a member with no entry yet (its entry is need-new)
#     [%sm S b mode need-new prev np]  a member with an entry: prev, need-pessimized
#     [%se S counter]                  the loop is stable after sweep counter
#     [%fz S mug]                      the final pass: the mug of its map of straights (the code)
#   --small (with --trace) for the big compiles: [%s0 S b mode regs mug] and, for a member with
#     an entry, [%sn S b mode regs-prev regs-new regs-np regs-uncut fired reach mug-np mug-prev
#     full] where fired: the join differs from the uncut one, reach: +msg-reach, full: ~ or
#     [need-new prev np cape] when it fired or the entry shrank
# Then splitmax-sum.py OUT.txt.
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))
args = sys.argv[1:]
out = args[0]
fix = args[args.index('--fix') + 1] if '--fix' in args else 'none'
inp = args[args.index('--in') + 1] if '--in' in args else os.path.join(W, 'desk/lib/nock-compilation.hoon')
trace = '--trace' in args
src = open(inp).read()


def sub(old, new):
    global src
    assert src.count(old) == 1, old
    src = src.replace(old, new)


CUT = '    ?:  (gth (need-ord-regs res split-max) split-max)  this+~\n'
JOIN = '    =/  need-pessimized  (msg-need-ord need-new need.u.s-previous cape.less.b)\n'
FIN0 = '      ?.  done  [?~(pessimized need-new u.pessimized) 0 ~]\n'


def uncut_arm():
    """+msg-need-ord-uncut: the arm without the cut line and without its jet hint."""
    a = src.index('++  msg-need-ord\n')
    e = src.index('::\n::  Registers of a shape', a)
    arm = src[a:e]
    assert arm.count(CUT) == (0 if fix == 'nocut' else 1)
    arm = arm.replace(CUT, '').replace('++  msg-need-ord\n', '++  msg-need-ord-uncut\n')
    arm = arm.replace('  ~%  %msg-need-ord  ..ride  ~\n', '')
    return arm


if fix == 'nocut':
    sub(CUT, '')
elif fix in ('loop', 'sticky', 'late'):
    arm = uncut_arm()
    sub('::\n::  Registers of a shape', arm + '::\n::  Registers of a shape')
    if fix == 'loop':
        sub(JOIN, JOIN.replace('(msg-need-ord ', '(msg-need-ord-uncut '))
    else:
        # .frz: the previous entry is frozen (n-args 1 of its placeholder); .cut-now: this
        # join cuts (sticky: always; late: only in a cut sweep, told by top holding the
        # marker bell [[| ~] 0 0], which no real bell is)
        cutnow = '&' if fix == 'sticky' else '(~(has by top) ^-(bell [[| ~] 0 0]))'
        sub(JOIN,
            '    =/  frz=?  =(1 n-args.u.s-previous)\n'
            '    =/  cut-now=?  ' + cutnow + '\n'
            '    =/  np-uncut  (msg-need-ord-uncut need-new need.u.s-previous cape.less.b)\n'
            '    =/  np-cut  ?.(cut-now np-uncut (msg-need-ord need-new need.u.s-previous cape.less.b))\n'
            '    =/  need-pessimized  ?:(frz need.u.s-previous np-cut)\n'
            '    =.  frz  |(frz !=(np-cut np-uncut))\n'
            '    =/  fin2\n'
            '      |=  p=(unit need-ordered)\n'
            '      ^-  straight\n'
            '      ?.  done  [?~(p need-new u.p) ?:(frz 1 0) ~]\n'
            '      (finish p)\n')
        sub('      ?:  =(need-pessimized need-new)  (finish ~)\n      (finish `need-pessimized)\n',
            '      ?:  =(need-pessimized need-new)  (fin2 ~)\n      (fin2 `need-pessimized)\n')
        if fix == 'late':
            # the stable end runs a cut sweep first: every member compiled with top
            # carrying the marker bell
            sub('  ?.  any.st.res  (final & map-local cache)\n',
                '  ?.  any.st.res\n'
                + ('    ~&  ^-(* [%sx (mug scc) counter])\n' if trace else '') +
                '    =/  cs\n'
                '      %+  roll  order\n'
                '      |=  [b=bell st=_st.res m=_m.res c=_c.res]\n'
                '      =/  t=@ud  +(tick.st)\n'
                '      =/  r  (member b %must (gth t (mul 4 ~(wyt in scc))) m (~(put by top) ^-(bell [[| ~] 0 0]) [%none ~]) c)\n'
                '      :_  [ray cache]:r\n'
                '      :^  any.st  t\n'
                '        (~(put by ran.st) b t)\n'
                '      ?:(chg.r (~(put by chg.st) b t) chg.st)\n'
                '    ?:  =(chg.st.cs chg.st.res)  (final & m.cs c.cs)\n'
                '    %=  sweep-loop\n'
                '      st         st.cs(any |)\n'
                '      map-local  m.cs\n'
                '      cache      c.cs\n'
                '      counter    +(counter)\n'
                '    ==\n')
elif fix != 'none':
    raise SystemExit('unknown fix ' + fix)

if trace:
    # where the loop starts, each sweep, its stable end
    sub('  =/  counter=@ud  0\n  |-  ^+  [map-local cache]\n  =*  sweep-loop  $\n',
        '  =/  counter=@ud  0\n'
        '  ~&  ^-(* [%sc (mug scc) ~(wyt in scc)])\n'
        '  |-  ^+  [map-local cache]\n  =*  sweep-loop  $\n'
        '  ~&  ^-(* [%sw (mug scc) counter])\n')
    sub('  ?.  any.st.res', '  ~?  !any.st.res  ^-(* [%se (mug scc) counter])\n  ?.  any.st.res')
    # the code: the mug of the map of straights the final pass makes (also for a lone bell)
    sub('      [m c(nary (~(uni by nary.c) m))]\n',
        '      ~&  ^-(* [%fz (mug scc) (mug m)])\n      [m c(nary (~(uni by nary.c) m))]\n')
    # compact (--trace small, for the big compiles): no shapes but where the cut fires or the
    # entry shrinks; registers, mugs and the two flags computed in the copy
    small = '--small' in args
    if 'msg-need-ord-uncut' not in src:
        arm = uncut_arm()
        sub('::\n::  Registers of a shape', arm + '::\n::  Registers of a shape')
    # +msg-reach: does the recursion of +msg-need-ord reach the cut line
    sub('::\n::  Registers of a shape',
        '::\n++  msg-reach\n'
        '  |=  [a=need-ordered b=need-ordered less=cape]\n'
        '  ^-  ?\n'
        '  ?:  =(a b)  |\n'
        '  =/  la  ?=(?(%this %none) -.a)\n'
        '  =/  lb  ?=(?(%this %none) -.b)\n'
        '  ?:  &(la lb)  |\n'
        '  ?:  |(la lb)  ?=(^ less)\n'
        '  =/  [ha=need-ordered ta=need-ordered]  ?:(?=(%both -.a) [h t]:a ?>(?=(^ -.a) a))\n'
        '  =/  [hb=need-ordered tb=need-ordered]  ?:(?=(%both -.b) [h t]:b ?>(?=(^ -.b) b))\n'
        '  |($(a ha, b hb, less (hed:ca less)) $(a ta, b tb, less (tel:ca less)))\n'
        '::\n::  Registers of a shape')
    sub('    ?~  s-previous=(~(get by map-local) b)\n',
        '    ~?  &(!done ?=(~ (~(get by map-local) b)))\n'
        + ('      ^-(* [%s0 (mug scc) (mug b) mode (need-ord-regs need-new 1.000.000) (mug need-new)])\n'
           if small else
           '      ^-(* [%s0 (mug scc) (mug b) mode need-new cape.less.b])\n') +
        '    ?~  s-previous=(~(get by map-local) b)\n')
    if small:
        sub('    ::  Debug assert: the final pass finds the shape of the sweeps\n',
            '    ~&  =/  pv  need.u.s-previous\n'
            '        =/  unc  (msg-need-ord-uncut need-new pv cape.less.b)\n'
            '        =/  rp  (need-ord-regs pv 1.000.000)\n'
            '        =/  rn  (need-ord-regs need-pessimized 1.000.000)\n'
            '        =/  fired=?  !=(unc (msg-need-ord need-new pv cape.less.b))\n'
            '        =/  fall=?  |((lth rn rp) &(?=(^ -.pv) ?=(%this -.need-pessimized)) &(?=(%both -.pv) ?=(%this -.need-pessimized)))\n'
            '        ^-  *\n'
            '        :*  %sn  (mug scc)  (mug b)  mode  rp  (need-ord-regs need-new 1.000.000)  rn\n'
            '            (need-ord-regs unc 1.000.000)  fired  (msg-reach need-new pv cape.less.b)\n'
            '            (mug need-pessimized)  (mug pv)\n'
            '            ?.  |(fired fall)  ~\n'
            '            [need-new pv need-pessimized cape.less.b]\n'
            '        ==\n'
            '    ::  Debug assert: the final pass finds the shape of the sweeps\n')
    else:
        sub('    ::  Debug assert: the final pass finds the shape of the sweeps\n',
            '    ~&  ^-(* [%sm (mug scc) (mug b) mode need-new need.u.s-previous need-pessimized])\n'
            '    ::  Debug assert: the final pass finds the shape of the sweeps\n')
open(out, 'w').write(src)
print(out, fix, 'trace' if trace else '')
