#!/usr/bin/env python3
"""Write lemmas/Ska/CompSixLSR.lean (track C, README Gaps 12.35).

`six_doneGBN` is the text of `six_doneGB` (CompSixLSDone.lean) with the
conclusion `SixDN` (`SixD` and the jump at no entry) and one more bullet at
the end; `finishLFC_contractGBN` is the text of `finishLFC_contractGB`
(CompNaryTop.lean) from `RunOKGB` and the jump at no entry in place of
`DoneOK`.  The rest (the tree of `nommR`) is written here.
Run from formalization/: python3 tools/gen/sixr.py
"""
import re, sys

def grab(path, name):
    s = open(path).read()
    i = s.index('theorem ' + name + ' ')
    j = s.rfind('/--', 0, i)
    assert s[j:i].count('-/') == 1, name
    k = s.index('\n\n', i)
    # the proof ends at the first blank line followed by a non-indented line
    m = re.search(r'\n\n(?=[^ \n])', s[i:])
    return s[j:i + m.start()]

six = grab('lemmas/Ska/CompSixLSDone.lean', 'six_doneGB')
def rep(t, a, b, n=1):
    assert t.count(a) == n, (a, t.count(a))
    return t.replace(a, b)
six = rep(six, 'theorem six_doneGB ', 'theorem six_doneGBN ')
six = rep(six, '    SixD (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (kc + ka + kb + 2) := by',
          '    SixDN (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (kc + ka + kb + 2) := by')
six = rep(six, '    fun r hr => by rw [hc43]; exact Rc.ncond r hr, ?_, ?_, ?_⟩, ?_⟩',
          '    fun r hr => by rw [hc43]; exact Rc.ncond r hr, ?_, ?_, ?_⟩, ?_, ?_⟩')
six = six.replace('/-- **`[6 c a b]` under `%done` with a call-free test and branches that may\ncall**',
                  '/-- **`six_doneGB` with the jump at no entry** (`SixDN`).  The text of\n`six_doneGB`: `[6 c a b]` under `%done` with a call-free test and branches that may\ncall', 1)
six += '''
  · -- the jump at no entry: the block of `+copy`, above every label
    intro hm
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hm
    simp only [jmp0] at hee
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · have := lc e h; omega
    · dsimp only at hee; omega
    · have := la e h; omega
    · dsimp only at hee; omega
    · have := lb e h; omega
'''

top = grab('lemmas/Ska/CompNaryTop.lean', 'finishLFC_contractGB')
top = rep(top, 'theorem finishLFC_contractGB ', 'theorem finishLFC_contractGBN ')
top = rep(top, '      some (nex, gE) → DoneOK lib N P f gen0 gE nex)',
          '      some (nex, gE) → RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nex ∧\n        nex.th.there ∉ (entries nex.laz).map Prod.fst)')
top = rep(top, '  have R := D.run\n', '  have R := D.1\n')
top = rep(top, 'D.nent', 'D.2', 2)
top = re.sub(r'^/--.*?-/', '/-- **`finishLFC_contractGB` from `RunOKGB` and the jump at no entry**, the\ntwo fields of `DoneOK` it reads (a `%6` meets no `DoneOK`: its result is\nnot flat).  The text of `finishLFC_contractGB`. -/', top, count=1, flags=re.S)

head = open('tools/gen/sixr_head.lean').read()
tail = open('tools/gen/sixr_tail.lean').read()
out = head + six + '\n' + top + '\n' + tail
open('lemmas/Ska/CompSixLSR.lean', 'w').write(out)
print('ok', len(out))
