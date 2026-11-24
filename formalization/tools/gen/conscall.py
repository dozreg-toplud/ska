#!/usr/bin/env python3
"""Generate `consNC_ok` of lemmas/Ska/CompConsCall.lean from the structural
part of `binaryGV_ok` (lemmas/Ska/CompConsV.lean): the head is a run that
calls (`RunOKNC`), the tail a `TailNV`, the goal a fork-free `%next`, and
the `sem` is new (written below).  Exact-match replacements with asserted
counts.  Usage: conscall.py > body.lean (the text between the markers
`-- BEGIN consNC_ok` and `-- END consNC_ok` of CompConsCall.lean)."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, '../../lemmas/Ska/CompConsV.lean')).read().split('\n')
# lines 230..402 (1-based) of CompConsV.lean: from the labels to the econd bullet
start = src.index('  -- the labels of the two runs are apart')
end = src.index('  · -- the copy block')
body = '\n'.join(src[start:end])
def rep(a, b, n=1):
    global body
    c = body.count(a)
    assert c == n, (a, c)
    body = body.replace(a, b)
rep("""    ⟨(hq.labs e he).1, Nat.lt_trans (hq.labs e he).2.1 hq.hi⟩""",
    """    ⟨(hq.labs e he).1, Nat.lt_of_le_of_lt (hq.labs e he).2.1 hq.hi⟩""")
rep("""  have gm : ∀ r, GMem goal r → r < g0.re := fun r hr => by
    cases goal with
    | next laz th => exact hg.2 r hr
    | _ => exact hr.elim""",
    """  have gm : ∀ r, GMem (CGoal.next sur th : CGoal S) r → r < g0.re := fun r hr => hg.2 r hr""")
rep("""copy_down (goal := goal)""", """copy_down (goal := CGoal.next sur th)""")
rep("""    size := ?_
""", "")
rep("""  · rw [(entries_side_perm _ _ _).length_eq, List.length_append]
    have := hp.size; have := hq.size; omega
""", "")
# nec: the tail's need fits every subject
i = body.index("  · rw [hev]\n    have hn : ¬ FitsS")
j = body.index("  · rw [kc3]\n    rcases CM r hr")
body = body[:i] + """  · have a : ¬ FitsS nexp.laz.sure s := fun a => hs ((CF s).mpr ⟨a, hqt s⟩)
    rw [pureEval_cons, hp.nec s a]
    rfl
""" + body[j:]
rep("""    · obtain ⟨x, y, th, z⟩ := hq.labs e a
      have := hq.hi""", """    · obtain ⟨x, y, th, z⟩ := hq.labs e a
      have := hq.hi
      have := hq.lo""")
rep("""    sem := fun cf hcf c ned σ O st t gul s0 s ag hned regs hh hn => ?_ }""",
    """    sem := fun cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn => ?_ }""")
head = open(os.path.join(here, 'conscall_head.lean')).read()
sem = open(os.path.join(here, 'conscall_sem.lean')).read()
rep("""  · rcases (memN e).mp he with a | a
    · exact ⟨(hp.eregs e a).1, fun r hr => by have := (hp.eregs e a).2 r hr; omega⟩
    · exact ⟨(hq.eregs e a).1, fun r hr => by have := (hq.eregs e a).2 r hr; omega⟩""",
    """  · rcases (memN e).mp he with a | a
    · refine ⟨(hp.eregs e a).1, fun r hr => ⟨?_, by have := ((hp.eregs e a).2 r hr).2; omega⟩⟩
      rcases ((hp.eregs e a).2 r hr).1 with b | b
      · rcases hlp r b with b' | ⟨b', _⟩
        · exact Or.inl b'
        · exact Or.inr b'
      · exact Or.inr (by omega)
    · refine ⟨(hq.eregs e a).1, fun r hr => ⟨?_, by have := ((hq.eregs e a).2 r hr).2; omega⟩⟩
      rcases ((hq.eregs e a).2 r hr).1 with b | b
      · rcases hlq r b with b' | ⟨b', _⟩
        · exact Or.inl b'
        · exact Or.inr b'
      · exact Or.inr b""")
print(head + body + '\n' + sem, end='')
