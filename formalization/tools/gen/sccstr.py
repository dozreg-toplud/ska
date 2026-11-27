#!/usr/bin/env python3
"""Generate `lemmas/Compiler/CompSccOfStr.lean` (README Gaps 19 (g), the switch to track I's
decoding): copies of the `D` chain (`CompSccOfDec.lean`, `CompSccOfDecH.lean`, themselves made by
`tools/gen/sccdec.py`) with the loop's `%may` / `%must` / `%done` gates at `LoopRS` (`LoopR` with
`MlStr`, track I) in place of `LoopR`, so that decoding (a) of each nested loop's map comes from
`csi_gate_ranked_dec` inside `calleeCompiled_sccDStr` and the loop data lose their `CsiDec` field.

Every copy is renamed (suffix `Str`).  What changes:
* `SccLoopAtAStr`: `SccLoopAtA` with its three gates at `LoopRS`;
* `calleeCompiled_sccDStr`: `csi_gate_ranked_dec` (members bells from `SccsGood`) in place of
  `csi_gate_ranked` with `printId_pill`; the decoded map in place of `hdec`;
* `memDoneCall_ofDStr`, `MemDoneRestDStr`, `MemDoneRestSDStr`: track I's `MemDoneCallStr`, whose
  `+coerce-soft` hypothesis `hcs` also asks that `t` is a straight's tail;
* `sccLoopAtD_realStr`: `memGate_done_realStr`;
* `SccLoopDataDStr`, `SccLoopDataSDStr`: the `%may` / `%must` gates at `LoopRS`, no `CsiDec`.
Every replacement is asserted to apply exactly as often as stated.

Usage: python3 tools/gen/sccstr.py   (from `formalization/`)
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


NAMES = ['SccLoopAtA', 'calleeCompiled_sccD', 'memDoneCall_ofD', 'MemDoneCall', 'MemDoneRestD',
         'memDoneCall_of_restD', 'sccLoopAtD_real', 'memGate_done_real', 'SccLoopDataD', 'CalleeHD',
         'calleeCompiled_stepHD', 'calleeCompiled_heightsD', 'calleeCompiled_heights0D', 'MemDoneRestSD',
         'memDoneRest_of_SD', 'SccLoopDataSD', 'sccLoopData_of_SD', 'CalleeHSD', 'calleeH_of_SD']
RENAME = {n: n + 'Str' for n in NAMES}


def sub(text, old, new, count):
    n = text.count(old)
    assert n == count, (old[:80], n, count)
    return text.replace(old, new)


def convert(text, fixes):
    for old, new, count in fixes:
        text = sub(text, old, new, count)
    for a, b in RENAME.items():
        text = re.sub(r'(?<![A-Za-z0-9_.])' + re.escape(a) + r'(?![A-Za-z0-9_])', b, text)
    return text


ANYK = 'CompSccOfAnyK.lean'
DEC = 'CompSccOfDec.lean'
DECH = 'CompSccOfDecH.lean'

HCS_OLD = '∃ t, nock (C finBody'
HCS_NEW = ('∃ t, (∃ s : Straight (TreapMap mugF), C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev '
           'cape).toNoun t = s.toNoun) ∧ nock (C finBody')
F_HCS = [(HCS_OLD, HCS_NEW, 1)]

F_LOOPAT = [
    ('MemGate c (LoopR c.scc', 'MemGate c (LoopRS c.scc', 3),
    ('**`SccLoopAt` without `PrintId`**', '**`SccLoopAt` without `PrintId`, at `LoopRS`**', 1),
    ('the three `MemGate`s for `LoopR`', 'the three `MemGate`s for `LoopRS` (track I: `LoopR` with `MlStr`)', 1),
]
F_SCC = [
    ('SccLoopAtA env (RKD SC0 MO0 inl Pf) P S CODE JETS CALLS JH x NR CR ∧ CsiDec S CODE JETS CALLS JH NR CR) :',
     'SccLoopAtA env (RKD SC0 MO0 inl Pf) P S CODE JETS CALLS JH x NR CR) :', 1),
    ('obtain ⟨⟨c, r, outC, nout, hcfg, hmay, hdone, hmust, henv⟩, hdec⟩ :=',
     'obtain ⟨c, r, outC, nout, hcfg, hmay, hdone, hmust, henv⟩ :=', 1),
    ('obtain ⟨s, hs, hsome, hout, M, NR\', REST, NARYU, hLR, hNR\', hNU, hus, hgate⟩ :=\n    csi_gate_ranked c r',
     'obtain ⟨s, hs, hsome, hout, M, NR\', REST, NARYU, ⟨hLR, -⟩, hNR\', hNU, hus, hgate, mD, hmD, -⟩ :=\n'
     '    csi_gate_ranked_dec c r', 1),
    ('⟨hSset, hcj.1, hcj.2, hnr⟩ ⟨_, hbS, h0⟩ hnd hcfg\n      hmay hdone',
     '⟨hSset, hcj.1, hcj.2, hnr⟩ ⟨_, hbS, h0⟩ hnd hcfg (fun k hk => (hSmem k hk).2)\n      hmay hdone', 1),
    ('(fun _ _ => printId_pill _) (fun _ => rfl) hsu0 hq0', '(fun _ => rfl) hsu0 hq0', 1),
    ('(hdec _ _ hgate)', '⟨mD, hmD⟩', 1),
]
F_REAL = [
    ('(LoopR (cfgReal r order kids).scc', '(LoopRS (cfgReal r order kids).scc', 2),
]
F_LOOPDATA = [
    ('(LoopR (cfgReal r order kids).scc', '(LoopRS (cfgReal r order kids).scc', 2),
    ('LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR → CsiDec S CODE JETS CALLS JH NR CR ∧\n',
     'LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR →\n', 1),
]
F_STEPH = [
    ('obtain ⟨hdec, r, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩',
     'obtain ⟨r, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩', 1),
    ('    exact ⟨sccLoopAtD_real env', '    exact sccLoopAtD_real env', 1),
    ('hcall st keep b0 ML CACHE hb hL hIH, hdec⟩', 'hcall st keep b0 ML CACHE hb hL hIH', 1),
]
F_LDOF = [
    ('obtain ⟨hdec, r, order, kids, rk, nout, hre,', 'obtain ⟨r, order, kids, rk, nout, hre,', 1),
    ('exact ⟨hdec, r, order,', 'exact ⟨r, order,', 1),
]

HEAD = '''import lemmas.Compiler.CompSccOfDecH
import lemmas.Compiler.CompSccLoopStrDec

/-!
# The chain of the gate with the loops at `LoopRS` (README Gaps 19 (g), the switch)

GENERATED by `tools/gen/sccstr.py` from `CompSccOfAnyK.lean` (`SccLoopAtA`) and the `D` chain
(`CompSccOfDec.lean`, `CompSccOfDecH.lean`): each definition and theorem is the one without
`Str` with the loop's member gates at track I's `LoopRS` (`LoopR` with `MlStr`: every value of
`map-local` is a straight's noun) in place of `LoopR`.  What changed: `calleeCompiled_sccDStr`
takes the loop's gate from `csi_gate_ranked_dec` (its `M` decoded, the members bells by
`SccsGood`), so the loop data `SccLoopDataDStr` and `SccLoopDataSDStr` have no `CsiDec` field;
the `%done` gate is `memGate_done_realStr` (with `rKD_sure`) at track I's `MemDoneCallStr`, whose
`+coerce-soft` hypothesis also asks that its `t` is a straight's tail (`MemDoneRestDStr`,
`MemDoneRestSDStr`).  Do not edit by hand.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

'''

ITEMS = [
    (ANYK, 'SccLoopAtA', F_LOOPAT),
    (DEC, 'calleeCompiled_sccD', F_SCC),
    (DEC, 'memDoneCall_ofD', F_HCS),
    (DEC, 'MemDoneRestD', F_HCS),
    (DEC, 'memDoneCall_of_restD', []),
    (DEC, 'sccLoopAtD_real', F_REAL),
    (DECH, 'SccLoopDataD', F_LOOPDATA),
    (DECH, 'CalleeHD', []),
    (DECH, 'calleeCompiled_stepHD', F_STEPH),
    (DECH, 'calleeCompiled_heightsD', []),
    (DECH, 'calleeCompiled_heights0D', []),
    (DECH, 'MemDoneRestSD', F_HCS),
    (DECH, 'memDoneRest_of_SD', []),
    (DECH, 'SccLoopDataSD', F_LOOPDATA),
    (DECH, 'sccLoopData_of_SD', F_LDOF),
    (DECH, 'CalleeHSD', []),
    (DECH, 'calleeH_of_SD', []),
]

TAIL = '\n\nend Compiler\nend Formalization\n'

parts = [convert(block(p, n), fx) for p, n, fx in ITEMS]
(CDIR / 'CompSccOfStr.lean').write_text(HEAD + '\n\n'.join(parts) + TAIL)
print('ok')
