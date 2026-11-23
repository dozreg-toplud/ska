#!/bin/bash
# usage: runhoon.sh TEST.hoon [seconds]
# Runs the Hoon expression in TEST.hoon against hoon.hoon and nock-compilation.hoon of the
# integration worktree, with the reference +mink (its jet off).  The subject of the expression
# is the library's core, so +poke, +eval-top, +eval-blob, +mink, +mook, state are in scope.
# Output: the ~& prints of the test, on stdout.  The expression must produce an atom.
set -u
W=~/work/ska-scratch/wt/ska-formalization
D=$(dirname "$(readlink -f "$0")")
T=$(readlink -f "$1"); S=${2:-300}
tmp=$(mktemp -d "$D/run.XXXXXX")
python3 - "$W" "$T" "$D" "$tmp" <<'PY'
import sys
W,T,D,tmp=sys.argv[1:5]
sys_=open(W+'/desk/sys/hoon.hoon','rb').read()
import os
lib=open(os.environ.get('RUNHOON_LIB') or W+'/desk/lib/nock-compilation.hoon','rb').read()
d=lambda n: f"{n:,}".replace(',','.')
tst=open(T,'rb').read()
open(tmp+'/sample.bin','wb').write(sys_+lib+tst)
s=open(D+'/samx5.hoon').read().split('\n')
s[0]=f"=/  sys=@t  (cut 3 [0 {d(len(sys_))}] sam)"
s[1]=f"=/  lib=@t  (cut 3 [{d(len(sys_))} {d(len(lib))}] sam)"
s[2]=f"=/  tst=@t  (cut 3 [{d(len(sys_)+len(lib))} {d(len(tst))}] sam)"
open(tmp+'/samx.hoon','w').write('\n'.join(s))
PY
ulimit -c 0
U3NC_LOOM=32 U3NC_ONLY=n U3NC_PROBE='|=(a=* .*(-.a +.a))' U3NC_PROBE_OFF=mink \
  U3NC_PROBE_FILE=$tmp/sample.bin U3NC_PROBE_SAMX=@$tmp/samx.hoon \
  $W/formalization/tools/capped.sh -m 3G timeout -s KILL "$S" /home/kirill/work/ska-scratch/nocw/nct > $tmp/out 2>&1
echo "exit $?"
tr '\r' '\n' < $tmp/out | grep -v '^$' | awk '/arms off|registered cores/{f=1;next} f' | grep -v "^u3n\|slogs\|probe sample\|^test"
rm -rf "$tmp"
