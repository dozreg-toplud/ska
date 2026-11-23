#!/bin/bash
# capped.sh [-m SIZE] CMD...: run CMD under a memory cap (default 8G, no swap),
# so that a runaway Lean check dies alone instead of taking the machine down.
MEM=8G
if [ "$1" = "-m" ]; then MEM=$2; shift 2; fi
exec systemd-run --user --scope -q -p MemoryMax=$MEM -p MemorySwapMax=0 -- "$@"
