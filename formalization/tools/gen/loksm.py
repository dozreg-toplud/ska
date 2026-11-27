#!/usr/bin/env python3
"""Write lemmas/Ska/CompDirectMLS.lean and lemmas/Ska/CompDirectMLSCons.lean:
the copies, for the run with `mono` `&` (`runLCM env true`), of track C's
constructors of `LOKS` / `LOKSF` / `JNewLS` / `JNewLSF` and the `DoneOK`
lemmas at the top, generated from their source text (no source is changed).

Run from formalization/:  python3 tools/gen/loksm.py
(`--counts` prints the table COUNTS from the current sources instead.)

* The declarations copied are the closure of ROOTS: every declaration of
  FILES that a copied one names (outside comments) and whose text names
  `runLC` or a copied declaration.  References are followed only into FILES.  `LOKS` and `runLC` themselves are
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

# Follow references only into declarations of FILES: a bare identifier (a
# local name, a field such as `holds`) can match a declaration of an unrelated
# file, whose own closure is not ours (a copy must come from FILES anyway).
reach, stack = set(), list(ROOTS)
while stack:
    n = stack.pop()
    if n in reach or n not in decls or decls[n][0] not in FILES:
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

# ---------------------------------------------------------------------------
# The n-ary class `CallTreeDN` (README Gaps 18.15 (d)): the text of
# CompDirectMTree.lean's class and its induction with the ORIGINAL names
# (every copy `XM` back to track C's `X`, `runLCM env true` back to `runLC
# env`), the direct call by this track's n-ary lemmas (CompNaryTopCal.lean,
# CompNaryTopDirect.lean) for a `p` that meets `LOKSF`.  Written to
# lemmas/Ska/CompNaryTopDN.lean.
NPATCHES = [  # n-ary lemmas for a `p` that meets `LOKSF` (so may itself hold a direct call)
    ('callLBN_run', 'callLBN_runF', [
        ('(Sp : LOKS (S := S) (Map := Map) false lib N env P fb p)', '(Sp : LOKSF (S := S) (Map := Map) lib N env P fb p)', 1),
        ('(L := ofSure ⟨sub, HoonSet.empty⟩) (th := jmp0 g2.bo) hcount',
         '(L := ofSure ⟨sub, HoonSet.empty⟩) (th := jmp0 g2.bo) (Or.inr e3) hcount', 1)]),
    ('lokS_directN', 'lokS_directNF', [
        ('(Sp : LOKS (S := S) (Map := Map) false lib N env P fb p)', '(Sp : LOKSF (S := S) (Map := Map) lib N env P fb p)', 1),
        ('callLBN_run lib env', 'callLBN_runF lib env', 1)]),
    ('tailN_done', 'tailN_doneF', [
        ('(Sp : LOKS (S := S) (Map := Map) false lib N env P fb p)', '(Sp : LOKSF (S := S) (Map := Map) lib N env P fb p)', 1),
        ('(L := ofSure ⟨sub, HoonSet.empty⟩) (th := jmp0 g0.bo) hcount',
         '(L := ofSure ⟨sub, HoonSet.empty⟩) (th := jmp0 g0.bo) (Or.inr e3) hcount', 1)]),
]
DIRECT_OLD = ('env.ring bl = Option.none → env.need bl = some bNed → N bl false = some bNed → N bl true = some ndT →')
DIRECT_NEW = ('env.ring bl = Option.none → env.need bl = some bNed → N bl false = some bNed →\n'
              '      (SplitsLess bl bNed ∧ ∀ m, env.sof m p q bl bNed = false) →')
TREE = ['CallTreeD', 'CallTreeD.toA', 'CallTreeD.sixCount', 'CallTreeD.cell', 'CallTreeD.hinted_of', 'CallTreeD.kind',
        'jNewLSM_direct', 'lokSM_callTreeD', 'callTreeD_done']
TPATCHES = {  # (old, new, count) on the source text, before the renames
    'CallTreeD': [
        ('{bl : Bell} {bNed ndT : NeedOrd}', '{bl : Bell} {bNed : NeedOrd}', 1), (DIRECT_OLD, DIRECT_NEW, 1),
        ('(`env.ring b = none`, `env.need b = some bNed` with `N b false\n= some bNed`, some `N b true`), the callee not pure',
         '(`env.ring b = none`, `env.need b = some bNed` with `N b false\n= some bNed`), every noun that fits the bell splitting by its need\n'
         '(`SplitsLess`), no soft call, the callee not pure', 1),
        ('for the run with `mono` `&`.', 'for the n-ary run (`runLC`, `mono` `|`).', 1),
        ('(it runs under `%next (lazy-from-reg\nsub-pes)`, a flag-free goal)', '(it runs under `%next (ofSure\nsub)`, a flag-free goal)', 1)],
    'jNewLSM_direct': [
        ('{b : Bell} {bNed ndT : NeedOrd}', '{b : Bell} {bNed : NeedOrd}', 1),
        ('(hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false)',
         '(hsof : ∀ m, env.sof m p q b bNed = false) (hNf : N b false = some bNed) (hspl : SplitsLess b bNed)\n'
         '    (hpure : env.pure b = false)', 1),
        ('callLBM_runM lib env hring hned hNf hNt Sp', 'callLBN_runF lib env hring hned hsof hNf hspl Sp', 1)],
    'lokSM_callTreeD': [
        ('with the copies for `runLCM env true`,\nthe leaves by `LOKS.toM`, the direct call', "with track C's constructors (`runLC env`),\nthe leaves as they are, the direct call", 1),
        ('@direct P b1 fb fq p q bl bNed ndT hp hring hned hNf hNt hpure', '@direct P b1 fb fq p q bl bNed hp hring hned hNf hsn hpure', 1),
        ('lokSM_directF (S := S) (Map := Map) lib env hring hned\n      hNf hNt hpure',
         'lokSM_directF (S := S) (Map := Map) lib env hring hned\n      hsn.2 hNf hsn.1 hpure', 1),
        ('jNewLSM_direct (S := S) (Map := Map) lib env hring hned\n      hNf hNt hpure',
         'jNewLSM_direct (S := S) (Map := Map) lib env hring hned\n      hsn.2 hNf hsn.1 hpure', 1)],
    'callTreeD_done': [
        ('of `callTreeA_done` with the copies for `runLCM env true`; the leaves by\n`runLCM_true`, ', "of `callTreeA_done` with track C's constructors (`runLC env`); the leaves\nas they are, ", 1),
        ('@direct P b1 fb fq p q bl bNed ndT hp hring hned hNf hNt hpure', '@direct P b1 fb fq p q bl bNed hp hring hned hNf hsn hpure', 1),
        ('    rw [runLCM_true env rfl] at hr\n', '', 2),
        ('tailP_doneM lib hring hned hNf hNt (lokSM_callTreeD lib env hp).1.1',
         'tailP_doneM lib hring hned hsn.2 hNf hsn.1 (lokSM_callTreeD lib env hp).1.1', 1)],
}
NRENAME = {'CallTreeD': 'CallTreeDN', 'lokSM_callTreeD': 'lokS_callTreeDN', 'callTreeD_done': 'callTreeDN_done',
           'jNewLSM_direct': 'jNewLS_directN', 'lokSM_directF': 'lokS_directNF', 'callLBM_runM': 'callLBN_runF',
           'tailP_doneM': 'tailN_doneF', 'LOKSM': 'LOKS'}
for n in copy:
    NRENAME[newname(n)] = n
NSUBS = [  # (regex, replacement, count of the whole file)
    (re.compile(r'\brunLCM((?:\s+\(Map := Map\))?)\s+env true\b'), r'runLC\1 env'),
    (re.compile(r'\.toM rfl\b'), ''),
]
ntexts = []
for src, dst, subs in NPATCHES:
    text = decls[src][2]
    assert text.count(f'theorem {src} ') == 1, src
    text = text.replace(f'theorem {src} ', f'theorem {dst} ')
    for o, nw, c in subs:
        assert text.count(o) == c, (src, o, text.count(o), c)
        text = text.replace(o, nw)
    assert text.startswith('/--')
    ntexts.append('/-- ' + f'(Generated by `tools/gen/loksm.py`: `{src}` for a `p` that meets `LOKSF`.)\n' + text[3:].lstrip(' '))
tcount = {'subs': 0, 'names': 0}
ttexts = []
for n in TREE:
    base, _, text = decls[n]
    assert base == 'CompDirectMTree', (n, base)
    for o, nw, c in TPATCHES.get(n, []):
        assert text.count(o) == c, (n, o, text.count(o), c)
        text = text.replace(o, nw)
    for rx, rp in NSUBS:
        text, c = rx.subn(rp, text)
        tcount['subs'] += c
    for r in sorted(NRENAME, key=len, reverse=True):
        text, c = re.subn(r"(?<![A-Za-z0-9_.'])" + re.escape(r) + r"(?![A-Za-z0-9_'])", NRENAME[r], text)
        tcount['names'] += c
    assert not re.search(r'\brunLCM\b|\bLOKS[A-Z]*M\b|\bJNewLS[A-Z]*M\b|\bndT\b|\bhNt\b', text), (n, 'M left')
    note = f'(Generated by `tools/gen/loksm.py`: `{n}` with the original names, for the n-ary run.)'
    text = ('/-- ' + note + '\n' + text[3:].lstrip(' ')) if text.startswith('/--') else f'/-- {note} -/\n' + text
    ttexts.append(text)
assert tcount == {'subs': 3, 'names': 96}, tcount
docN = ('The n-ary class `CallTreeDN` (README Gaps 18.15 (d)): `CallTreeD` (CompDirectMTree.lean) for '
        '`runLC env`, with track C\'s own constructors, and the n-ary direct call (`lokS_directNF`, `tailN_doneF`).')
NT = (head(['lemmas.Ska.CompNaryTopCal', 'lemmas.Ska.CompDirectMTree'], 'The n-ary class `CallTreeDN`', docN)
      + '\n'.join(ntexts) + '\n' + ttexts[0] + '\nsection\nvariable {lib : Lib} {env : CallEnv} {N : Needs}\n\n'
      + '\n'.join(ttexts[1:6]) + '\n' + '\n'.join(ttexts[6:]) + '\n' + tail)
assert ttexts[5].rstrip().endswith('\nend'), 'the section of CallTreeD.* ends with CallTreeD.kind'
open('lemmas/Ska/CompNaryTopDN.lean', 'w').write(NT)
print('wrote lemmas/Ska/CompNaryTopDN.lean', len(NT.splitlines()), 'lines')

# ---------------------------------------------------------------------------
# `[6 c a b]` at the top (README Gaps 18.16): track C's `%6` under `%done`
# (CompSixLSDone.lean, CompSixLSWrap.lean), copied twice.
# * For the whole-subject entry (`finishLUCM`, `runLCM env true`): the
#   relations `PickD`, `SixDW`, the run taken apart, `six_doneGBW` and the
#   top `finishLUC_contractGBW`, with the substitutions of SUBS and the names
#   of SIXM (lemmas/Ska/CompNaryTopSixM.lean).
# * For the n-ary entry (`finishLFC`, `runLC env`): `SixDW` and `six_doneGBW`
#   with `WalkEqB` (the walk in the order of `+coerce-lazy`,
#   CompNaryTopSixW.lean) in place of `WalkEq`, and the clause that the
#   jump is no lazy entry (`DoneOK.nent`), with its proof
#   (lemmas/Ska/CompNaryTopSixN.lean).
SIXFILES = ('CompSixLSDone', 'CompSixLSWrap')
SIXM = {'PickD': 'PickDM', 'SixDW': 'SixDWM', 'runLC_six_done_apartW': 'runLCM_six_done_apartW',
        'six_doneGBW': 'six_doneGBWM', 'finishLUC_contractGBW': 'finishLUCM_contractGBW', 'finishLUC': 'finishLUCM'}
SIXM_COUNTS = {'PickD': {'env': 1, 'names': 1}, 'SixDW': {'env': 1, 'names': 1},
               'runLC_six_done_apartW': {'env': 4, 'simp': 1, 'names': 1},
               'six_doneGBW': {'env': 0, 'names': 9}, 'finishLUC_contractGBW': {'env': 1, 'names': 3}}
def convert_six(n, ren, subs=SUBS):
    base, _, text = decls[n]
    assert base in SIXFILES, (n, base)
    counts = {'env': 0}
    for key, rx, rp in subs:
        text, c = rx.subn(rp, text)
        if c:
            counts[key] = counts.get(key, 0) + c
    assert not re.findall(r'\brunLC\b', text), ('runLC left in', n)
    tot = 0
    for r in sorted(ren, key=len, reverse=True):
        text, c = re.subn(r"(?<![A-Za-z0-9_.'])" + re.escape(r) + r"(?![A-Za-z0-9_'])", ren[r], text)
        tot += c
    counts['names'] = tot
    return text, counts
mtexts = []
for n in ['PickD', 'SixDW', 'runLC_six_done_apartW', 'six_doneGBW', 'finishLUC_contractGBW']:
    text, counts = convert_six(n, SIXM)
    assert counts == SIXM_COUNTS[n], ('six M counts', n, counts)
    note = f'(Generated by `tools/gen/loksm.py`: `{n}` for `runLCM env true`.)'
    assert text.startswith('/--')
    mtexts.append('/-- ' + note + '\n' + text[3:].lstrip(' '))
docM = ('The copies for `runLCM env true` (the whole-subject entry `finishLUCM`) of track C\'s `%6` under '
        '`%done` with any test (`PickD`, `SixDW`, `six_doneGBW`) and of its top `finishLUC_contractGBW` '
        '(README Gaps 18.16, step 3).')
MT = (head(['lemmas.Ska.CompNaryTopSixW', 'lemmas.Ska.CompDirectMEq'], 'The `%6` at the top for `runLCM env true`', docM)
      + '\n'.join(mtexts) + '\n' + tail)
open('lemmas/Ska/CompNaryTopSixM.lean', 'w').write(MT)
print('wrote lemmas/Ska/CompNaryTopSixM.lean', len(MT.splitlines()), 'lines')

NENT = '''  · -- the jump at no entry
    intro hm
    obtain ⟨e, he, he1⟩ := List.mem_map.mp hm
    simp only [jmp0] at he1
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · have := lc e h; omega
    · simp only at he1; omega
    · have := la e h; omega
    · simp only at he1; omega
    · have := lb e h; omega
  · -- grow
'''
SIXN = {  # (old, new, count) on the source text
    'SixDW': [('`SixD` read on the unwrapped need', '`SixD` read on the unwrapped need for the n-ary top', 1),
              ('walked alike, that meets `RunOKGB`.', 'walked alike in the order of `+coerce-lazy` (`WalkEqB`), whose jump\nis no lazy entry, that meets `RunOKGB`.', 1),
              ('WalkEq (Map := Map) nex.laz nexU.laz ∧',
               'WalkEqB (Map := Map) nex.laz nexU.laz ∧\n      nexU.th.there ∉ (entries nexU.laz).map Prod.fst ∧', 1)],
    'six_doneGBW': [('obtain ⟨⟨x1U, h1th, W1, Rb⟩, sb⟩', 'obtain ⟨⟨x1U, h1th, W1, -, Rb⟩, sb⟩', 1),
                    ('obtain ⟨⟨x0U, h0th, W0, Ra⟩, sa⟩', 'obtain ⟨⟨x0U, h0th, W0, -, Ra⟩, sa⟩', 1),
                    ('jmp0 g3.bo⟩, rfl, ?_, E04, ?_,', 'jmp0 g3.bo⟩, rfl, ?_, ?_, E04, ?_,', 1),
                    ('refine walkEq_six _', 'refine walkEqB_six _', 1),
                    ('walkLazy_wrap hf', 'walkLazyB_wrap hf', 2),
                    ('  · -- grow\n', NENT, 1)],
}
SIXN_REN = {'SixDW': 'SixDWN', 'six_doneGBW': 'six_doneGBWN'}
ntexts6 = []
for n in ['SixDW', 'six_doneGBW']:
    base, _, text = decls[n]
    assert base == 'CompSixLSWrap', (n, base)
    for o, nw, c in SIXN[n]:
        assert text.count(o) == c, (n, o, text.count(o), c)
        text = text.replace(o, nw)
    tot = 0
    for r in sorted(SIXN_REN, key=len, reverse=True):
        text, c = re.subn(r"(?<![A-Za-z0-9_.'])" + re.escape(r) + r"(?![A-Za-z0-9_'])", SIXN_REN[r], text)
        tot += c
    assert tot == {'SixDW': 1, 'six_doneGBW': 6}[n], (n, tot)
    assert not re.search(r'\bWalkEq\b|\bwalkEq_six\b|\bwalkLazy_wrap\b', strip(text)), (n, 'WalkEq left')
    note = f'(Generated by `tools/gen/loksm.py`: `{n}` for the n-ary top.)'
    assert text.startswith('/--')
    ntexts6.append('/-- ' + note + '\n' + text[3:].lstrip(' '))
docN6 = ('Track C\'s `SixDW` and `six_doneGBW` for the n-ary top (`finishLFC_contractGBW`): the result '
         'walked alike in the order of `+coerce-lazy` (`WalkEqB`), its jump no lazy entry (README Gaps 18.16, step 2).')
N6 = (head(['lemmas.Ska.CompNaryTopSixW'], 'The `%6` under `%done` for the n-ary top', docN6)
      + '\n'.join(ntexts6) + '\n' + tail)
open('lemmas/Ska/CompNaryTopSixN.lean', 'w').write(N6)
print('wrote lemmas/Ska/CompNaryTopSixN.lean', len(N6.splitlines()), 'lines')
