"""Print the gate arms that the case `%6` of `+run` calls, as Lean
definitions: each arm `[8 [1 BUNT] [1 BAT] 0 1]` (a gate built on its
bunt) as `def <name>Bat` and `def <name>Arm`, with the fact that ties it to
the pill (`slot? <axis> comp.door` or `slot? <axis> compK`).

    tools/capped.sh -m 3G python3 tools/gen/sixhelp.py NAME...

Names: pastFork (door 4061), softLess (door 52), lazyShut (door 218495),
lazyBig (K 11199), lazySize (K 348), thisOnly (K 178934), softFork (door
221182), leap (door 441179), forkSure (door 884727), forkNeed (door 62),
fork (door 862), sect (door 6906), whole (ana 1372)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm, lean

K = ('C', ('R', 'nh3d89e8d5f4f5'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))
ARMS = {
    'pastFork': ('door', 4061, 'pf'), 'softLess': ('door', 52, 'sl'), 'lazyShut': ('door', 218495, 'lsh'),
    'lazyBig': ('K', 11199, 'lb'), 'lazySize': ('K', 348, 'lsz'), 'thisOnly': ('K', 178934, 'tho'),
    'softFork': ('door', 221182, 'sfk'), 'leap': ('door', 441179, 'lp6'), 'forkSure': ('door', 884727, 'fks'),
    'forkNeed': ('door', 62, 'fkn'), 'fork': ('door', 862, 'fk'), 'sect': ('door', 6906, 'sc'),
    'whole': ('ana', 1372, 'wh'),
}

def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    return ('C', full(n[1]), full(n[2]))

for name in sys.argv[1:]:
    where, ax, p = ARMS[name]
    base = {'door': ('R', 'comp.door'), 'K': K, 'ana': ('R', 'ana')}[where]
    arm = full(slot(ax, base))
    # [8 [1 BUNT] [1 BAT] 0 1]  or  [7 [8 [1 BUNT] [1 BAT] 0 1] HINT]
    hint = None
    if arm[1] == ('A', 7):
        hint = arm[2][2]
        arm = arm[2][1]
    assert arm[1] == ('A', 8), name
    b1 = arm[2][1]
    assert b1[1] == ('A', 1)
    bunt = b1[2]
    rest = arm[2][2]
    assert rest[1][1] == ('A', 1) and rest[2] == ('C', ('A', 0), ('A', 1)), name
    bat = rest[1][2]
    lname = {'door': 'comp.door', 'K': 'compK', 'ana': 'ana'}[where]
    print('/-- The battery of `+%s` (%s arm `%d`). -/' % (name, where, ax))
    print('def %sBat : Noun :=\n  %s\n' % (p, lean(bat)))
    print('def %sBunt : Noun :=\n  %s\n' % (p, lean(bunt)))
    if hint is None:
        print('def %sArm : Noun := C (A 8) (C (C (A 1) %sBunt) (C (C (A 1) %sBat) (C (A 0) (A 1))))\n' % (p, p, p))
    else:
        print('def %sArm : Noun :=\n  C (A 7) (C (C (A 8) (C (C (A 1) %sBunt) (C (C (A 1) %sBat) (C (A 0) (A 1))))) %s)\n'
              % (p, p, p, lean(hint)))
    print('theorem %s_at : slot? %d %s = some %sArm := by kernel_rfl\n' % (p, ax, lname, p))
    print('theorem %s_arm (d : Noun) : nock d %sArm = some (C %sBat (C %sBunt d)) := by\n  unfold %sArm; simp only [nock_exec]\n'
          % (p, p, p, p, p))
