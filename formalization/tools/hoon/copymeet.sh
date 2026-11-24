#!/bin/bash
# usage: copymeet.sh [seconds]
# The cnMeet test of lemmas/Compiler/CompCopyLink.lean on the real compiler: runs the
# control copyprobe.hoon (a ~? that prints) and thread-a/b/c.hoon and proxy-dump.hoon
# (162 + 2 formulas through +comp), and counts the lines printed by the ~? of
# +copy-need-make-ops (%copy-this-l-a, %copy-this-l-b, %copy-this-r, %copy-both), which
# print when a %mov of the walk would join a register to itself.
D=$(dirname "$(readlink -f "$0")")
S=${1:-1500}
for t in copyprobe thread-a thread-b thread-c proxy-dump; do
  out=$("$D/runhoon.sh" "$D/$t.hoon" "$S")
  n=$(printf '%s\n' "$out" | grep -c '^\[%copy-')
  k=$(printf '%s\n' "$out" | grep -o 'summary n=[0-9]*' | head -1)
  echo "$t: $(printf '%s\n' "$out" | head -1) copy-lines=$n $k"
done
