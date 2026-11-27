#!/usr/bin/env python3
# usage: passfix.py OUT.hoon --fix NAME [--in LIB] [--n N] [--cap N]      (track F, README Gaps 16)
# Writes a PATCHED COPY of nock-compilation.hoon (never the tree's desk/) with one candidate fix of
# the non-terminating pass loop of +analyze (takecycle.hoon).  Every patch is textual and asserts
# that the text it replaces occurs exactly once.  NAME:
#   none     the library unchanged (the control)
#   keep     (a) +cull keeps the datum of every member it drops (a new map .kept of ska-state), and
#            +analyze starts a re-pushed identity from that datum instead of the bunt: the entry of an
#            identity is one monotone chain over the whole call of +ska-callgraph
#   endcull  (b) no +cull inside the pass loop, only when it is stable (before +pop); stable now also
#            needs every member .id reaches to be clean (+dirty), since a member left unreached at a
#            pass start is not swept, and a run of that pass can reach it again and read its entry
#            from before its callees changed.  The +cull before the first pass stays
#   late     (c) the original for the first N passes of a loop (default 64), (b) after them: the
#            +cull at the end of a pass only while pass =< N, and the clean test of (b) when stable
# --cap N    (measurement only) a pass loop at pass N+1 prints [%pm-capped mug pass] and pops
#            (what a loop that does not end does in the table of passfix-run.sh: no return)
# Then PASSMEASURE_IN=OUT.hoon passmeasure.py DIR instruments the patched copy (DIR/lib.hoon).
import os, sys
D = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.path.join(D, '..', '..', '..'))
a = sys.argv[1:]
out = a[0]
opt = lambda k, d=None: a[a.index(k) + 1] if k in a else d
fix = opt('--fix', 'none')
n = int(opt('--n', '64'))
cap = opt('--cap')
src = open(opt('--in') or os.path.join(W, 'desk/lib/nock-compilation.hoon')).read()

def sub(old, new):
    global src
    k = src.count(old)
    assert k == 1, (k, old)
    src = src.replace(old, new)

END_OLD = '''    ?.  =(low index)  [low st]
    ::  members that .id does not reach anymore are dropped
    ::
    =.  st  (cull id st)
    ::  stable: no member was dirty, or no entry changed and no function was
    ::  found (a new function was seen in progress, as an empty entry, by the
    ::  members that called it, which are dirty now)
    ::
    ?:  &(!changed =(next.st next-before))
      [next.st (pop id st)]
    pass-loop(pass +(pass))
'''
CLEAN = '''      ?:  %+  lien  (sweep id (silt (above id stk.st)) st)
          |=(m=identity (dirty m st))
        pass-loop(pass +(pass))
      [next.st (pop id (cull id st))]
'''
if fix == 'none':
    pass
elif fix == 'keep':
    sub('      moved=(set identity)    ::  functions whose product changed already\n',
        '      moved=(set identity)    ::  functions whose product changed already\n'
        '      kept=(map identity datum)  ::  last entries of the members +cull dropped\n')
    sub('        g      (~(put by g.st) id *datum)\n',
        '        g      (~(put by g.st) id (~(gut by kept.st) id *datum))\n')
    sub('''    %=  st
      order  (~(del by order.st) i)
      ticks  (~(del by ticks.st) i)
      g      (~(del by g.st) i)
    ==
''', '''    %=  st
      order  (~(del by order.st) i)
      ticks  (~(del by ticks.st) i)
      kept   (~(put by kept.st) i (git-g g.st i))
      g      (~(del by g.st) i)
    ==
''')
elif fix == 'endcull':
    sub(END_OLD, '''    ?.  =(low index)  [low st]
    ::  stable: no member was dirty, or no entry changed and no function was
    ::  found, and every member that .id reaches is clean: one that a pass
    ::  start did not reach was not swept, and a run of the pass can reach
    ::  it again. Only then are the members .id does not reach dropped
    ::
    ?:  &(!changed =(next.st next-before))
''' + CLEAN + '''    pass-loop(pass +(pass))
''')
elif fix == 'late':
    sub(END_OLD, '''    ?.  =(low index)  [low st]
    ::  members that .id does not reach anymore are dropped, in the first
    ::  %N passes only
    ::
    =?  st  (lte pass %N)  (cull id st)
    ::  stable: no member was dirty, or no entry changed and no function was
    ::  found, and every member that .id reaches is clean (one left unreached
    ::  at a pass start after pass %N was not swept)
    ::
    ?:  &(!changed =(next.st next-before))
'''.replace('%N', str(n)) + CLEAN + '''    pass-loop(pass +(pass))
''')
else:
    sys.exit('unknown fix ' + fix)
if cap:
    sub('''    |-  ^-  [@ ska-state]
    =*  pass-loop  $
''', '''    |-  ^-  [@ ska-state]
    =*  pass-loop  $
    ?:  (gth pass %C)
      ~&  [%pm-capped (mug id) pass]
      [next.st (pop id (cull id st))]
'''.replace('%C', cap))
open(out, 'w').write(src)
print('wrote', out, 'fix', fix, 'n', n, 'cap', cap)
