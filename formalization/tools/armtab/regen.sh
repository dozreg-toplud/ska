#!/bin/bash
# regen.sh: the arm table, the names, the axis check and lemmas/Pill/Arms.lean of this
# worktree's library and pill (track T, README Gaps 32), about 20 s (plus any wait for a heavy slot).  Run from anywhere.
# After a pill switch: run tools/pill2lean.py first (the names are those of lemmas/Pill).
set -e
H=$(dirname "$(readlink -f "$0")")
F=$(readlink -f "$H/../..")
cd "$F"
# the table: a Hoon run (runhoon-here.sh caps it at 3G), the python only parses its prints
python3 tools/armtab/armtab.py table
# the names: loads the pill and lemmas/Pill (peak 0.2 GB), through the machine-wide slots
/home/kirill/work/ska-scratch/formalization-keep/tools/heavy.sh 4G python3 tools/armtab/armtab.py names
python3 tools/armtab/axischeck.py --cited tools/armtab/cited.json > tools/armtab/axischeck.txt
head -2 tools/armtab/axischeck.txt
python3 tools/armtab/armlean.py
