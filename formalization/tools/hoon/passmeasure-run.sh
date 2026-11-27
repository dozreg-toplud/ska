#!/bin/bash
# usage: passmeasure-run.sh LIB.hoon OUTDIR DRIVER.hoon...
# Runs each driver with the instrumented library LIB.hoon of passmeasure.py, six at a time, 900 s
# each, into OUTDIR/<driver>.out (track F, README Gaps 16).  Then passmeasure-stab.py OUTDIR/*.out,
# passmeasure-freeze.py OUTDIR/*.out.
L=$(readlink -f "$1"); O=$(readlink -f "$2"); shift 2
cd "$(dirname "$(readlink -f "$0")")/../.."
mkdir -p "$O"
printf '%s\n' "$@" | xargs -P6 -I{} sh -c 'b=$(basename {} .hoon); RUNHOON_LIB='"$L"' tools/hoon/runhoon.sh {} 900 > '"$O"'/$b.out 2>&1'
echo ALLDONE
