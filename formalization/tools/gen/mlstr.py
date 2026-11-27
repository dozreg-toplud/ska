#!/usr/bin/env python3
"""Generate lemmas/Compiler/CompSccLoopStrGen.lean (README Gaps 21.17).

Copies, with asserted replacements, the `%done` member step and the loop's gate so that the
relation of the loop carries `MlStr` (every value of `map-local` is a straight's noun):

* `mem_done_step` -> `mem_done_stepStr` (hR : LoopRS, `+coerce-soft` gives a straight),
* `MemDoneCall` -> `MemDoneCallStr`, `memGate_done_real` -> `memGate_done_realStr`,
  `memGate_done_K` -> `memGate_done_KStr`,
* `csi_gate_loop_d` -> `csi_gate_loop_dStr`, `csi_gate_ranked` -> `csi_gate_rankedStr`.

Run from formalization/:  python3 tools/gen/mlstr.py > lemmas/Compiler/CompSccLoopStrGen.lean
"""
import re
import sys

STEP = 'lemmas/Compiler/CompSccLoopMemStep.lean'
CLOSE = 'lemmas/Compiler/CompSccLoopClose.lean'


def block(text, start, end):
    i = text.index(start)
    j = text.index(end, i + len(start))
    return text[i:j]


def rep(s, old, new, count=1):
    n = s.count(old)
    assert n == count, (old[:80], n, count)
    return s.replace(old, new)


step = open(STEP).read()
close = open(CLOSE).read()

# ---- mem_done_step ----
md = block(step, 'theorem mem_done_step ', '/-! ## `MemGate` on `%done` -/')
md = rep(md, 'theorem mem_done_step ', 'theorem mem_done_stepStr ')
md = rep(md, '(hR : LoopR r.scc outC nout (QK envK RR P S x) st.ml st.sure ML CACHE)',
         '(hR : LoopRS r.scc outC nout (QK envK RR P S x) st.ml st.sure ML CACHE)')
CS_OLD = '∃ t, nock (C finBody'
CS_NEW = ('∃ t, (∃ s : Straight (TreapMap mugF), C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev '
          'cape).toNoun t = s.toNoun) ∧ nock (C finBody')
md = rep(md, CS_OLD, CS_NEW)
md = rep(md, '      LoopR r.scc outC nout (QK envK RR P S x)\n        (member',
         '      LoopRS r.scc outC nout (QK envK RR P S x)\n        (member')
md = rep(md, '        ML\' CA\' := by\n  generalize hB',
         '        ML\' CA\' := by\n  obtain ⟨hR, hRS⟩ := hR\n  generalize hB')
md = rep(md, "exact ⟨csMlExact_put hR.1 hp', hSH', hout' nn, hQ'⟩",
         "exact ⟨⟨csMlExact_put hR.1 hp', hSH', hout' nn, hQ'⟩, mlStr_put hRS ⟨s, rfl⟩ hml hp⟩")
md = rep(md, "exact ⟨csMlExact_put hR.1 hp', hSH', hout' _, hQ'⟩",
         "exact ⟨⟨csMlExact_put hR.1 hp', hSH', hout' _, hQ'⟩, mlStr_put hRS ⟨s, rfl⟩ hml hp⟩")
md = rep(md, "obtain ⟨t', ht'⟩ := hcs prev SURE' hm hnp",
         "obtain ⟨t', ⟨s', hs'⟩, ht'⟩ := hcs prev SURE' hm hnp")
md = rep(md, "exact ⟨csMlExact_put hR.1 hp, hSH', hout' _, hQ'⟩",
         "exact ⟨⟨csMlExact_put hR.1 hp, hSH', hout' _, hQ'⟩, mlStr_put hRS ⟨s', hs'⟩ hml hp⟩")

# ---- MemDoneCall ----
mc = block(step, 'def MemDoneCall ', '/-- **`MemGate` on `%done` for a real SCC**')
mc = rep(mc, 'def MemDoneCall ', 'def MemDoneCallStr ')
mc = rep(mc, CS_OLD, CS_NEW)

# ---- memGate_done_real ----
mg = block(step, 'theorem memGate_done_real ', '/-- **The start rest of a miss')
mg = rep(mg, 'theorem memGate_done_real ', 'theorem memGate_done_realStr ')
mg = rep(mg, '      MemDoneCall r order', '      MemDoneCallStr r order')
mg = rep(mg, '    MemGate (cfgReal r order kids) (LoopR (cfgReal r order kids).scc',
         '    MemGate (cfgReal r order kids) (LoopRS (cfgReal r order kids).scc')
mg = rep(mg, ':= hcall st keep b ML CA hb hR', ':= hcall st keep b ML CA hb hR.1')
mg = rep(mg, 'exact mem_done_step r order', 'exact mem_done_stepStr r order')

# ---- memGate_done_K ----
mk = block(step, 'theorem memGate_done_K ', 'end Compiler')
mk = rep(mk, 'theorem memGate_done_K ', 'theorem memGate_done_KStr ')
mk = rep(mk, '      MemDoneCall r order', '      MemDoneCallStr r order')
mk = rep(mk, '    MemGate (cfgReal r order kids) (LoopR (cfgReal r order kids).scc',
         '    MemGate (cfgReal r order kids) (LoopRS (cfgReal r order kids).scc')
mk = rep(mk, '  memGate_done_real r order', '  memGate_done_realStr r order')

# ---- csi_gate_loop_d ----
gl = block(close, 'theorem csi_gate_loop_d ', '/-- **The gate with no model fuel**')
gl = rep(gl, 'theorem csi_gate_loop_d ', 'theorem csi_gate_loop_dStr ')
gl = rep(gl, 'MemGate c (LoopR bs outC nout Q)', 'MemGate c (LoopRS bs outC nout Q)', 3)
gl = rep(gl, '∃ M NR REST NARYU, LoopR bs outC nout Q s.ml s.sure M (C NR REST)',
         '∃ M NR REST NARYU, LoopRS bs outC nout Q s.ml s.sure M (C NR REST)')
gl = rep(gl, '''  have hR : LoopR bs outC nout Q st0.ml st0.sure (A 0) (C NARY CR) :=
    ⟨hml0' ▸ mlExact_none, hsu0, fun b hb => by rw [hml0'] at hb; simp at hb, hq0⟩''',
         '''  have hR : LoopRS bs outC nout Q st0.ml st0.sure (A 0) (C NARY CR) :=
    ⟨⟨hml0' ▸ mlExact_none, hsu0, fun b hb => by rw [hml0'] at hb; simp at hb, hq0⟩, mlStr_nil⟩''')
gl = rep(gl, 'csi_gate_loop c (LoopR bs outC nout Q)', 'csi_gate_loop c (LoopRS bs outC nout Q)')
gl = rep(gl, '(loopR_reset bs outC nout Q)', '(loopRS_reset bs outC nout Q)')
gl = rep(gl, 'top_of_exact p (listN c.order) CA1 hR1.1', 'top_of_exact p (listN c.order) CA1 hR1.1.1')
gl = rep(gl, "hQ CA' hR'.2.2.2", "hQ CA' hR'.1.2.2.2")
gl = rep(gl, "NR M hNR hR'.1.1", "NR M hNR hR'.1.1.1")

# ---- csi_gate_ranked ----
gr = block(close, 'theorem csi_gate_ranked ', '/-! ## The consumers -/')
gr = rep(gr, 'theorem csi_gate_ranked ', 'theorem csi_gate_rankedStr ')
gr = rep(gr, 'MemGate c (LoopR bs outC nout Q)', 'MemGate c (LoopRS bs outC nout Q)', 3)
gr = rep(gr, '∃ M NR REST NARYU, LoopR bs outC nout Q s.ml s.sure M (C NR REST)',
         '∃ M NR REST NARYU, LoopRS bs outC nout Q s.ml s.sure M (C NR REST)')
gr = rep(gr, 'csi_gate_loop_d c bs', 'csi_gate_loop_dStr c bs')

HEAD = '''import lemmas.Compiler.CompSccLoopStr

/-! # The member step and the loop's gate with `MlStr` (README Gaps 21.17)

Generated by `tools/gen/mlstr.py` from `CompSccLoopMemStep.lean` and `CompSccLoopClose.lean`
(copies with asserted replacements; do not edit by hand):

* **`mem_done_stepStr`**: `mem_done_step` at `LoopRS` (the `+put:by` of `map-local` puts the
  straight `finishLFC` gives, so `MlStr` is kept), with `+coerce-soft`'s product a straight;
* `MemDoneCallStr` (`MemDoneCall` with that `+coerce-soft`), **`memGate_done_realStr`**,
  **`memGate_done_KStr`**: the `%done` gate at `LoopRS`;
* **`csi_gate_loop_dStr`**, **`csi_gate_rankedStr`**: the loop's gate at `LoopRS`, so its
  product `M` holds straights (`CompSccLoopStr.lean` decodes it). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

'''

sys.stdout.write(HEAD + md + mc + mg + mk + gl + gr + 'end Compiler\nend Formalization\n')
