#!/usr/bin/env python3
"""Generate `lemmas/Compiler/CompSccOfDec.lean` and `CompSccOfDecH.lean` (README Gaps 19 (g),
decoding (b)): copies of the chain from `calleeCompiled_sccA` to `calleeH_of_S` with the rest
predicate `RKD SC0 MO0 inl Pf` (`RKP` with the cache decoded) in place of `RKP SC0 inl Pf`.

Every copy is renamed (suffix `D`), `MO0` is bound next to `SC0` and passed after `SC0` to the
renamed definitions, and the few proof lines that build or take apart the rest predicate are
replaced.  Every replacement is asserted to apply exactly as often as stated.

Usage: python3 tools/gen/sccdec.py   (from `formalization/`)
"""
import re
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
CDIR = ROOT / 'lemmas' / 'Compiler'

STARTS = ('/--', '/-!', 'theorem ', 'def ', 'end ', 'structure ', 'noncomputable ', '@[', 'private ', 'abbrev ')


def block(path, name):
    lines = (CDIR / path).read_text().split('\n')
    pat = re.compile(r'^(theorem|def|structure|abbrev) ' + re.escape(name) + r'\b')
    idx = [i for i, l in enumerate(lines) if pat.match(l)]
    assert len(idx) == 1, (path, name, idx)
    i = idx[0]
    s = i
    if i > 0 and lines[i - 1].rstrip().endswith('-/'):
        s = i - 1
        while not lines[s].startswith('/--'):
            s -= 1
    e = i + 1
    while e < len(lines) and not lines[e].startswith(STARTS):
        e += 1
    while lines[e - 1].strip() == '':
        e -= 1
    return '\n'.join(lines[s:e])


RENAME = {
    'RKP': 'RKD', 'rKP_sure': 'rKD_sure', 'rKP_mono': 'rKD_mono', 'EM': 'EMD',
    'calleeCompiled_sccA': 'calleeCompiled_sccD', 'eM_step': 'eMD_step', 'eM_start': 'eMD_start',
    'memDoneCall_of': 'memDoneCall_ofD', 'MemDoneRest': 'MemDoneRestD', 'memDoneCall_of_rest': 'memDoneCall_of_restD',
    'sccLoopAtA_real': 'sccLoopAtD_real', 'calleeCompiled_oneKA': 'calleeCompiled_oneKD',
    'CCBelow': 'CCBelowD', 'cCBelow_mono': 'cCBelowD_mono', 'SccLoopData': 'SccLoopDataD', 'CalleeH': 'CalleeHD',
    'calleeCompiled_stepH': 'calleeCompiled_stepHD', 'calleeCompiled_heights': 'calleeCompiled_heightsD', 'calleeCompiled_heights0': 'calleeCompiled_heights0D',
    'callOkTN_outW': 'callOkTN_outD', 'callOkTN_memOk': 'callOkTN_memOkD', 'MemDoneRestS': 'MemDoneRestSD',
    'memDoneRest_of_S': 'memDoneRest_of_SD', 'SccLoopDataS': 'SccLoopDataSD', 'sccLoopData_of_S': 'sccLoopData_of_SD',
    'CalleeHS': 'CalleeHSD', 'calleeH_of_S': 'calleeH_of_SD',
}

# the renamed names that take `SC0` explicitly: `MO0` goes right after it
EXPL = ['RKD', 'EMD', 'MemDoneRestD', 'memDoneCall_ofD', 'sccLoopAtD_real', 'CCBelowD', 'SccLoopDataD', 'CalleeHD',
        'MemDoneRestSD', 'SccLoopDataSD', 'CalleeHSD']


def sub(text, old, new, count):
    n = text.count(old)
    assert n == count, (old[:80], n, count)
    return text.replace(old, new)


def convert(text, fixes):
    for old, new, count in fixes:
        text = sub(text, old, new, count)
    for a, b in RENAME.items():
        text = re.sub(r'(?<![A-Za-z0-9_.])' + re.escape(a) + r'(?![A-Za-z0-9_])', b, text)
    # binders: `SC0 ... : Noun` gets `MO0`
    text, nb = re.subn(r'\bSC0((?: [A-Z][A-Za-z0-9]*)*) : Noun', r'SC0 MO0\1 : Noun', text)
    # call sites of the renamed definitions taking `SC0` explicitly
    alt = '|'.join(EXPL)
    text = re.sub(r'\b(' + alt + r')((?: [A-Za-z0-9_\'.]+)*?) SC0\b(?! MO0)', r'\1\2 SC0 MO0', text)
    return text


# ---------------------------------------------------------------- CompSccOfDec.lean
ANYK = 'CompSccOfAnyK.lean'
ONE = 'CompSccOfOneAny.lean'

F_SCC = [
    ('obtain ⟨⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩, hPf0⟩ := hR',
     'obtain ⟨⟨⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩, hPf0⟩, hD0⟩ := hR', 1),
    ('obtain ⟨c, r, outC, nout, hcfg, hmay, hdone, hmust, henv⟩ :=\n    hloop',
     'obtain ⟨⟨c, r, outC, nout, hcfg, hmay, hdone, hmust, henv⟩, hdec⟩ :=\n    hloop', 1),
    ('obtain ⟨⟨⟨NRb, MOb, INLb, SUb, hcb, hilb, hinb⟩, NRd, hNRd, hcld⟩, hPfq⟩ := hRq',
     'obtain ⟨⟨⟨⟨NRb, MOb, INLb, SUb, hcb, hilb, hinb⟩, NRd, hNRd, hcld⟩, hPfq⟩, hDq⟩ := hRq', 1),
    ('ext_trans hEq hE2, ?_, ⟨⟨⟨NARYU,', 'ext_trans hEq hE2, ?_, ⟨⟨⟨⟨NARYU,', 1),
    ('fun k u hu => ?_⟩, hPfU⟩, ?_⟩', 'fun k u hu => ?_⟩, hPfU⟩, cacheDec_uni hDq (hdec _ _ hgate) hNU hus⟩, ?_⟩', 1),
    ('      SccLoopAtA env (RKP SC0 inl Pf) P S CODE JETS CALLS JH x NR CR) :',
     '      SccLoopAtA env (RKP SC0 inl Pf) P S CODE JETS CALLS JH x NR CR ∧ CsiDec S CODE JETS CALLS JH NR CR) :', 1),
]
F_STEP = [
    ('fun k hk => hR.2 NR', 'fun k hk => hR.1.2 NR', 1),
]
F_START = [
    ('obtain ⟨⟨⟨NR2, MO2, INL2, SU2, hc2, -, -⟩, NRc, hNRc, hcl⟩, hPf⟩ := hR',
     'obtain ⟨⟨⟨⟨NR2, MO2, INL2, SU2, hc2, -, -⟩, NRc, hNRc, hcl⟩, hPf⟩, hD⟩ := hR', 1),
    ('  have hRK : ∀ s f, RKP SC inl Pf ⟨CA1, s, f⟩ :=\n'
     '    fun s f => ⟨⟨⟨NRq, MO, INL\', SU, hc1, hil\', hin\'⟩, NRc, (hs2 NRc).2 hNRc, hcl⟩,\n'
     '      fun N hN k hk => hPf N ((hs2 N).1 hN) k hk⟩',
     '  have hD1 : CacheDec MO0 CA1 := by\n'
     '    rw [hc1]; rw [hc] at hD; exact cacheDec_cacheN hD\n'
     '  have hRK : ∀ s f, RKD SC MO0 inl Pf ⟨CA1, s, f⟩ :=\n'
     '    fun s f => ⟨⟨⟨⟨NRq, MO, INL\', SU, hc1, hil\', hin\'⟩, NRc, (hs2 NRc).2 hNRc, hcl⟩,\n'
     '      fun N hN k hk => hPf N ((hs2 N).1 hN) k hk⟩, hD1⟩', 1),
    ('    ⟨(hRK _ _).1, fun N hN k hk => ?_⟩,', '    ⟨⟨(hRK _ _).1.1, fun N hN k hk => ?_⟩, hD1⟩,', 1),
]
F_ONE = [
    ('obtain ⟨⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩, hPf0⟩ := hR',
     'obtain ⟨⟨⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩, hPf0⟩, hD0⟩ := hR', 1),
    ('  · refine ⟨⟨⟨NRU, MO, INL\', SUU, rfl, hil\', hin\'⟩, NRU, by simp [cacheN, nock_exec], sccClosed_put hnr h0 hpn hsc hcl⟩,\n'
     '      fun N hN k hk => ?_⟩',
     '  · refine ⟨⟨⟨⟨NRU, MO, INL\', SUU, rfl, hil\', hin\'⟩, NRU, by simp [cacheN, nock_exec], sccClosed_put hnr h0 hpn hsc hcl⟩,\n'
     '      fun N hN k hk => ?_⟩, cacheDec_put (b := ⟨Sock.mk cape DATA, FOL⟩) hD0 hpn⟩', 1),
]

DEC_HEAD = '''import lemmas.Compiler.CompSccOfDecDefs
import lemmas.Compiler.CompSccOfOneAny

/-!
# The chain of the gate with the cache decoded (README Gaps 19 (g), decoding (b))

GENERATED by `tools/gen/sccdec.py` from `CompSccOfAnyK.lean` and `CompSccOfOneAny.lean`: each
theorem is the one without `D` with the rest predicate `RKD SC0 MO0 inl Pf` (`RKP` with `mono`
kept at `MO0` and `nary` a map of straights, `CacheDec`) in place of `RKP SC0 inl Pf`, and
`EMD` (`EM` at `RKD`).  What changed in the proofs: the rest predicate is taken apart and built
with its `CacheDec` field; `calleeCompiled_sccD` asks of the loop, next to `SccLoopAtA`, the
decoding (a) `CsiDec` of its map and gets `CacheDec` of the union by `cacheDec_uni`;
`eMD_start` gets it through `+inlined` by `cacheDec_cacheN`; `calleeCompiled_oneKD` through the
`+put:by` of the one straight by `cacheDec_put`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

'''

DEC = [
    (ANYK, 'calleeCompiled_sccA', F_SCC),
    (ANYK, 'EM', []),
    (ANYK, 'eM_step', F_STEP),
    (ANYK, 'eM_start', F_START),
    (ANYK, 'memDoneCall_of', []),
    (ANYK, 'MemDoneRest', []),
    (ANYK, 'memDoneCall_of_rest', []),
    (ANYK, 'sccLoopAtA_real', []),
    (ONE, 'calleeCompiled_oneKA', F_ONE),
]

# ---------------------------------------------------------------- CompSccOfDecH.lean
HT = 'CompSccOfHeight.lean'
HS = 'CompSccOfHeightS.lean'

F_LOOPDATA = [
    ('  ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR →\n    ∃ (r : RealCfg)',
     '  ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR → CsiDec S CODE JETS CALLS JH NR CR ∧\n    ∃ (r : RealCfg)', 1),
]
F_STEPH = [
    ('obtain ⟨r, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩ := hdat P Pf hab x NR CR hx',
     'obtain ⟨hdec, r, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩ := hdat P Pf hab x NR CR hx', 1),
    ('    exact sccLoopAtA_real env SC0 inl P Pf S CODE JETS CALLS JH x NR CR hx hPS hbell r order kids rk nout\n'
     '      hcfg hmay hmust henv fun st keep b0 ML CACHE hb hL => hcall st keep b0 ML CACHE hb hL hIH',
     '    exact ⟨sccLoopAtA_real env SC0 inl P Pf S CODE JETS CALLS JH x NR CR hx hPS hbell r order kids rk nout\n'
     '      hcfg hmay hmust henv fun st keep b0 ML CACHE hb hL => hcall st keep b0 ML CACHE hb hL hIH, hdec⟩', 1),
]
F_H0 = [
    ('CalleeCompiled env (RK SC0 inl) ctx b nb', 'CalleeCompiled env (RKP SC0 inl (fun _ => False)) ctx b nb', 1),
    ('(rKP_empty.2 hR)', 'hR', 1),
    ('rKP_empty.1 h4', 'h4', 1),
    ('`CalleeCompiled` with `RK`', '`CalleeCompiled` with `RKD` at no bell in progress', 1),
]
F_OUTW = [
    ('(fun x h => h.2.1.2)', '(fun x h => h.2.1.1.2)', 1),
]
F_LOOPDATAS = [
    ('  ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR →\n    ∃ (r : RealCfg)',
     '  ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR → CsiDec S CODE JETS CALLS JH NR CR ∧\n    ∃ (r : RealCfg)', 1),
]
F_LDOF = [
    ('obtain ⟨r, order, kids, rk, nout, hre, hcfg, hmay, hmust, henv, hcall⟩ := H x NR CR hx',
     'obtain ⟨hdec, r, order, kids, rk, nout, hre, hcfg, hmay, hmust, henv, hcall⟩ := H x NR CR hx', 1),
    ('exact ⟨r, order, kids, rk, nout, hcfg,', 'exact ⟨hdec, r, order, kids, rk, nout, hcfg,', 1),
]

DECH_HEAD = '''import lemmas.Compiler.CompSccOfDec
import lemmas.Compiler.CompSccOfHeightS

/-!
# The induction on height with the cache decoded (README Gaps 19 (g), decoding (b))

GENERATED by `tools/gen/sccdec.py` from `CompSccOfHeight.lean` and `CompSccOfHeightS.lean`:
each definition and theorem is the one without `D` at the rest predicate `RKD SC0 MO0 inl Pf`
and `EMD`.  What changed: the loop data `SccLoopDataD` and `SccLoopDataSD` carry, next to the
loop, the decoding (a) `CsiDec` of the loop's map (track I), which `calleeCompiled_stepHD`
hands to `calleeCompiled_sccD`; `calleeCompiled_heights0D` ends at `RKD` with no bell in
progress (no conversion to `RK`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

'''

DECH = [
    (HT, 'CCBelow', []),
    (HT, 'cCBelow_mono', []),
    (HT, 'SccLoopData', F_LOOPDATA),
    (HT, 'CalleeH', []),
    (HT, 'calleeCompiled_stepH', F_STEPH),
    (HT, 'calleeCompiled_heights', []),
    (HT, 'calleeCompiled_heights0', F_H0),
    (HS, 'callOkTN_outW', F_OUTW),
    (HS, 'callOkTN_memOk', []),
    (HS, 'MemDoneRestS', []),
    (HS, 'memDoneRest_of_S', []),
    (HS, 'SccLoopDataS', F_LOOPDATAS),
    (HS, 'sccLoopData_of_S', F_LDOF),
    (HS, 'CalleeHS', []),
    (HS, 'calleeH_of_S', []),
]

TAIL = '\n\nend Compiler\nend Formalization\n'


def emit(out, head, items):
    parts = [convert(block(p, n), fx) for p, n, fx in items]
    (CDIR / out).write_text(head + '\n\n'.join(parts) + TAIL)


emit('CompSccOfDec.lean', DEC_HEAD, DEC)
emit('CompSccOfDecH.lean', DECH_HEAD, DECH)
print('ok')
