#!/usr/bin/env python3
"""Write lemmas/Ska/CompDirectMLS.lean and lemmas/Ska/CompDirectMLSCons.lean:
the copies, for the run with `mono` `&` (`runLCM env true`), of track C's
constructors of `LOKS` / `LOKSF` / `JNewLS` / `JNewLSF` and the `DoneOK`
lemmas at the top, generated from their source text (no source is changed).

Run from formalization/:  python3 tools/gen/loksm.py
(`--counts` prints the table COUNTS from the current sources instead.)

* The declarations copied are the closure of ROOTS: every declaration of
  lemmas/Ska/*.lean that a copied one names (outside comments) and whose text
  names `runLC` or a copied declaration.  `LOKS` and `runLC` themselves are
  not copied: their copies `LOKSM` (CompDirectMCal.lean) and `runLCM`
  (CompRunLCM.lean, tools/gen/runlcm.py) exist.
* Substitutions, each counted per declaration against COUNTS:
  - `runLC env` / `runLC (Map := Map) env` -> `runLCM ... env true`;
  - `unfold runLC` -> `unfold runLCM`, `simp only [runLC ...` ->
    `simp only [runLCM, callLM ...` (the case `%2` of `runLCM` is
    `callLM env true`, which is `callL` when the call has no bell);
  - every copied name `X` -> its copy: `runLC_x` -> `runLCM_x`, `LOKS` ->
    `LOKSM`, any other `X` -> `XM` (`LOKS.toF` -> `LOKSM.toF`).
  After them no `runLC` token is left (asserted).
* A copy is sound as text when the source unfolds `runLC` only on the parent
  (the equations `runLC_n7`, `runLC_n4_next`, ...): `runLCM env true` unfolds
  to the same case bodies with `runLCM env true` on the parts, except `%2`
  with a bell, which no copied lemma unfolds.
"""
import re, glob, sys, os

ROOTS = ['LOKS.toF', 'JNewLS.toF',
         'lokS_consF', 'jNewLSF_cons', 'lokS_consS', 'jNewLS_cons', 'lokS_consH', 'jNewLS_consH',
         'lokS_indirectF', 'jNewLS_indirectF', 'lokS_sevenF', 'jNewLSF_seven', 'lokS_seven', 'jNewLS_seven',
         'lokS_four', 'jNewLS_four', 'lokS_three', 'jNewLS_three', 'lokS_five', 'jNewLS_five',
         'lokS_doneF', 'done_of_lokSF', 'four_doneB', 'three_doneB', 'five_doneB']
EXISTING = {'LOKS': 'LOKSM', 'runLC': 'runLCM'}
TYPES = ['LOKS', 'LOKSF', 'JNewLS', 'JNewLSF', 'JNewL']
# the source files in import order (a copy is emitted in this order)
FILES = ['CompRunLC', 'CompRunLCEq', 'CompSevenG', 'CompIndirect', 'CompNCFour', 'CompConsCallTop',
         'CompCallTreeTop', 'CompConsLS', 'CompConsLSCall', 'CompSevenLS', 'CompFourLS', 'CompConsLSF',
         'CompThreeLS', 'CompFiveLS', 'CompOneLS', 'CompFourTop']
CONS_OUT = lambda n, fn: ('cons' in n and n.startswith(('lokS_', 'jNewLS')))

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|def|structure|lemma|abbrev|inductive)\s+([^\s(:{\[]+)')
STOP = re.compile(r'^(/-!|end |section|namespace|variable|open |set_option|macro|local macro|syntax|attribute|'
                  r'/--|theorem|def|structure|lemma|abbrev|inductive|@\[|private|noncomputable|example|#)')

decls, order = {}, []
for fn in sorted(glob.glob('lemmas/Ska/*.lean')):
    base = os.path.basename(fn)[:-5]
    lines = open(fn).read().split('\n')
    i = 0
    while i < len(lines):
        m = DECL.match(lines[i])
        if not m:
            i += 1
            continue
        s = i
        if s > 0 and lines[s - 1].rstrip().endswith('-/'):
            k = s - 1
            while k >= 0 and not lines[k].startswith('/--'):
                k -= 1
            if k >= 0:
                s = k
        j = i + 1
        while j < len(lines) and not STOP.match(lines[j]):
            j += 1
        name = m.group(2)
        if base in FILES:
            assert name not in decls or decls[name][0] not in FILES, ('duplicate', name)
        if name not in decls or base in FILES:
            decls[name] = (base, s, '\n'.join(lines[s:j]).rstrip() + '\n')
        i = j

def strip(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return re.sub(r'--[^\n]*', '', text)

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")
def refs(text):
    return {t for t in IDENT.findall(strip(text)) if t in decls}

reach, stack = set(), list(ROOTS)
while stack:
    n = stack.pop()
    if n in reach or n not in decls:
        continue
    reach.add(n)
    stack.extend(refs(decls[n][2]))
need = set(TYPES)
changed = True
while changed:
    changed = False
    for n in reach:
        if n not in need and (re.search(r'\brunLC\b', strip(decls[n][2])) or
                              any(r in need for r in refs(decls[n][2]) if r != n)):
            need.add(n)
            changed = True
copy = [n for n in need if n in reach and n not in EXISTING]
for n in copy:
    assert decls[n][0] in FILES, ('source file not in FILES', n, decls[n][0])
copy.sort(key=lambda n: (FILES.index(decls[n][0]), decls[n][1]))

def newname(n):
    if n in EXISTING:
        return EXISTING[n]
    if n.startswith('runLC_'):
        return 'runLCM_' + n[len('runLC_'):]
    if '.' in n:
        return n  # renamed through its prefix
    return n + 'M'
renames = sorted(set(copy) | set(EXISTING) - {'runLC'}, key=len, reverse=True)
renames = [n for n in renames if '.' not in n]

SUBS = [  # (key, regex, replacement)
    ('env', re.compile(r'\brunLC((?:\s+\(Map := Map\))?)\s+env\b'), r'runLCM\1 env true'),
    ('unfold', re.compile(r'\bunfold runLC\b'), 'unfold runLCM'),
    ('simp', re.compile(r'\bsimp only \[runLC\b'), 'simp only [runLCM, callLM'),
]

def convert(n):
    text = decls[n][2]
    counts = {}
    for key, rx, rp in SUBS:
        text, c = rx.subn(rp, text)
        if c:
            counts[key] = c
    left = re.findall(r'\brunLC\b', text)
    assert not left, ('runLC left in', n, len(left))
    tot = 0
    for r in renames:
        text, c = re.subn(r"(?<![A-Za-z0-9_.'])" + re.escape(r) + r"(?![A-Za-z0-9_'])", newname(r), text)
        tot += c
    counts['names'] = tot
    note = f'(Generated by `tools/gen/loksm.py`: `{n}` for `runLCM env true`.)'
    if text.startswith('/--'):
        text = '/-- ' + note + '\n' + text[3:].lstrip(' ')
    else:
        text = f'/-- {note} -/\n' + text
    return text, counts

COUNTS = {
    'runLC_n7': {'env': 3, 'simp': 1, 'names': 1},
    'runLC_n2_none': {'env': 3, 'simp': 1, 'names': 1},
    'runLC_n4_last': {'env': 6, 'unfold': 2, 'names': 1},
    'runLC_cons_done': {'env': 2, 'unfold': 1, 'names': 1},
    'runLC_done_next': {'env': 2, 'simp': 2, 'names': 2},
    'JNewLS': {'env': 1, 'names': 3},
    'lokS_cons_run': {'env': 4, 'names': 4},
    'lokS_consS': {'env': 3, 'names': 9},
    'jNewLS_cons': {'names': 8},
    'lokS_seven': {'names': 10},
    'jNewLS_seven': {'names': 7},
    'LOKSF': {'env': 2, 'names': 2},
    'LOKS.toF': {'names': 5},
    'JNewLSF': {'env': 1, 'names': 2},
    'JNewLS.toF': {'names': 3},
    'runLC_n4_next': {'env': 2, 'unfold': 1, 'names': 1},
    'lokS_four_run': {'env': 1, 'names': 6},
    'lokS_four': {'names': 7},
    'jNewLS_four': {'names': 4},
    'lokS_cons_runF': {'env': 4, 'names': 8},
    'lokS_consF': {'env': 3, 'names': 9},
    'jNewLSF_cons': {'names': 8},
    'lokS_indirect_runF': {'env': 1, 'names': 6},
    'lokS_indirectF': {'names': 8},
    'jNewLS_indirectF': {'names': 5},
    'lokS_sevenF': {'names': 12},
    'jNewLSF_seven': {'names': 7},
    'runLC_n3_next': {'env': 3, 'unfold': 1, 'names': 1},
    'lokS_three_run': {'env': 1, 'names': 5},
    'lokS_three': {'names': 7},
    'jNewLS_three': {'names': 7},
    'pairRun_ok': {'env': 2, 'names': 4},
    'runLC_n5_next': {'env': 3, 'unfold': 1, 'names': 1},
    'runLC_n5_split': {'env': 3, 'names': 2},
    'lokS_five_run': {'env': 1, 'names': 9},
    'lokS_five': {'names': 8},
    'jNewLS_five': {'names': 5},
    'runLC_n5_done_split': {'env': 6, 'unfold': 1, 'names': 1},
    'five_doneB': {'env': 1, 'names': 8},
    'lokS_cons_runH': {'env': 4, 'names': 7},
    'lokS_consH': {'env': 3, 'names': 10},
    'jNewLS_consH': {'names': 6},
    'four_doneB': {'env': 3, 'unfold': 1, 'names': 4},
    'three_doneB': {'env': 3, 'unfold': 1, 'names': 3},
    'lokS_doneF': {'env': 1, 'names': 4},
    'done_of_lokSF': {'env': 1, 'names': 6},
}

out = {False: [], True: []}
observed = {}
for n in copy:
    text, counts = convert(n)
    observed[n] = counts
    out[CONS_OUT(n, decls[n][0])].append(text)
if '--counts' in sys.argv:
    print('COUNTS = {')
    for n in copy:
        print(f'    {n!r}: {observed[n]!r},')
    print('}')
    sys.exit(0)
for n in copy:
    assert n in COUNTS, ('new declaration in the closure, check it and rerun --counts', n)
    assert COUNTS[n] == observed[n], ('substitution counts changed', n, COUNTS[n], observed[n])
for n in COUNTS:
    assert n in observed, ('declaration left the closure', n)

# Copies of this track's `callLBM_run`, `lokSM_direct` (CompDirectMCal.lean) and
# `tailP_done` (CompDirectMTailP.lean)
# for a `p` that meets `LOKSFM` (so may itself hold a direct call): the run of
# `p` is under `%next (lazy-from-reg sub-pes)`, a flag-free goal with no entry.
PATCHES = [
    ('callLBM_run', 'callLBM_runM', [
        ('(Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true)',
         '(Sp : LOKSFM (S := S) (Map := Map) lib N env P fb p)', 1),
        ('  rw [runLCM_true env hpd] at hp\n', '', 1),
        ('(L := ofSure (lazyReg (g2.re + 1))) (th := jmp0 o\') hcount',
         '(L := ofSure (lazyReg (g2.re + 1))) (th := jmp0 o\') (Or.inr e3) hcount', 1)]),
    ('lokSM_direct', 'lokSM_directF', [
        ('(Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true)',
         '(Sp : LOKSFM (S := S) (Map := Map) lib N env P fb p)', 1),
        ('    rw [runLCM_true env hpd] at hp\n', '', 1),
        ('callLBM_run lib env hring hned hNf hNt Sp hpd hc6', 'callLBM_runM lib env hring hned hNf hNt Sp hc6', 1)]),
    ('tailP_done', 'tailP_doneM', [
        ('(Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true)',
         '(Sp : LOKSFM (S := S) (Map := Map) lib N env P fb p)', 1),
        ('  rw [runLCM_true env hpd] at hp\n', '', 1),
        ("(L := ofSure (lazyReg gA.re)) (th := jmp0 o') hcount",
         "(L := ofSure (lazyReg gA.re)) (th := jmp0 o') (Or.inr e3) hcount", 1)]),
]
for src, dst, subs in PATCHES:
    text = decls[src][2]
    assert text.count(f'theorem {src} ') == 1, src
    text = text.replace(f'theorem {src} ', f'theorem {dst} ')
    for o, nw, c in subs:
        assert text.count(o) == c, (src, o, text.count(o), c)
        text = text.replace(o, nw)
    assert 'hpd' not in text, (src, 'hpd left')
    note = f'(Generated by `tools/gen/loksm.py`: `{src}` for a `p` that meets `LOKSFM`.)'
    assert text.startswith('/--')
    out[False].append('/-- ' + note + '\n' + text[3:].lstrip(' '))

macro = re.search(r'/-- `omega` after reducing.*?\n\n', open('lemmas/Ska/CompFourTop.lean').read(), re.S).group(0)

def head(imports, title, doc):
    return ('\n'.join(f'import {i}' for i in imports) + f'''

/-!
# {title} (generated)

Written by `tools/gen/loksm.py` from the text of track C's lemmas; do not edit
by hand.  {doc}
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {{S : Type}} [HoonSet S] {{Map : Type → Type}} [HoonMap Map] [HoonMapKeys Map]

''' + macro)

tail = '''end Comp
end SkaModel
end Formalization
'''
docA = ('The copies for `runLCM env true` of `LOKSF`, `JNewLS`, `JNewLSF`, the equations of the '
        'cases of `runLC` they unfold, and the constructors of `[7 p q]`, `[4 p]`, `[3 p]`, `[5 p q]`, the '
        'indirect call and the `DoneOK` lemmas at the top.')
docB = 'The copies for `runLCM env true` of the constructors of the cons.'
A = head(['lemmas.Ska.CompDirectMCal'], '`LOKSM` constructors', docA) + '\n'.join(out[False]) + '\n' + tail
B = head(['lemmas.Ska.CompDirectMLS'], '`LOKSM` constructors of the cons', docB) + '\n'.join(out[True]) + '\n' + tail
open('lemmas/Ska/CompDirectMLS.lean', 'w').write(A)
open('lemmas/Ska/CompDirectMLSCons.lean', 'w').write(B)
print('wrote lemmas/Ska/CompDirectMLS.lean', len(A.splitlines()), 'lines,',
      'lemmas/Ska/CompDirectMLSCons.lean', len(B.splitlines()), 'lines,', len(copy), 'declarations')
