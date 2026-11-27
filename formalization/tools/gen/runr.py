#!/usr/bin/env python3
"""Write lemmas/Compiler/CompRunR{Res,Leaf,Cons,Five,Ten}.lean: copies of track
A's case lemmas of +run (and of their results) against `runLCM env true msup`
with the link `CompRunAtX ... X` (CompRunRBase.lean), parts as `PartR` and
+past as `PastAt ctx env.cod` (README Gaps 19).  The originals are not
changed; rerun after they change.  Run from formalization/.

Every copied declaration `n` is renamed `nR` (and so are its uses in the
copies).  The rules are textual and every rule asserts its count per file
(`--counts` prints them, to update the table after a change upstream).

* links: `CompRunAtR (runLC env msup) ctx` -> `CompRunAtX (runLCM env true msup)
  ctx X`; the rest, `mono`, `sup` of every link come with `hX : X x mono sup`
  (`intro x mono sup hx hX`, applications `x mono sup hx hX`, and a last
  binder `(hX : X x mono sup := by assumption)` on the lemmas that take
  `x mono sup` as parameters);
* model: `runLC env` -> `runLCM env true`, `runLC` -> `runLCM` (simp sets),
  `ResFor env msup` -> `ResForR (runLCM env true msup)`;
* +past: `pastL noCode` -> `pastL env.cod`, `hinted noCode n ≠ none` ->
  `PastAt ctx env.cod n`, `comp_past h7 hcode x g nex n region h` ->
  `h x g nex region`, `hinted_nd env.cod P.nd` -> `P.past`, the switches
  `pastL_cod` dropped.
"""
import re, sys

D = 'lemmas/Compiler/'
COUNTS = '--counts' in sys.argv

TOP = re.compile(r'^(?:/--|/-!|theorem |def |noncomputable def |structure |end |example|@\[|abbrev |variable |open |namespace |set_option )', re.M)

def chunks(path):
    src = open(path).read()
    st = [m.start() for m in TOP.finditer(src)] + [len(src)]
    cs = [src[a:b] for a, b in zip(st, st[1:])]
    out = []
    i = 0
    while i < len(cs):
        if cs[i].startswith('/--') and i + 1 < len(cs):
            out.append(cs[i] + cs[i + 1]); i += 2
        else:
            out.append(cs[i]); i += 1
    return out

DECL = re.compile(r'^(?:/--.*?-/\s*)?(?:theorem|def|noncomputable def|structure) (\S+)', re.S)

def extract(path, names):
    got = {}
    for c in chunks(path):
        m = DECL.match(c)
        if m and m.group(1) in names:
            assert m.group(1) not in got, m.group(1)
            got[m.group(1)] = c.rstrip() + '\n'
    for n in names:
        assert n in got, (path, n)
    return [got[n] for n in names]

RENAMED = []

def rename(s):
    for n in RENAMED:
        s = re.sub(r'(?<![\w.])' + re.escape(n) + r'(?![\w\'])', n + 'R', s)
    return s

RULES = [
    ('linkR', r'CompRunAtR \(runLC env msup\) ctx', 'CompRunAtX (runLCM env true msup) ctx X'),
    ('intro', r'intro x mono sup hx\b(?! hX)', 'intro x mono sup hx hX'),
    ('app', r'(?<!intro) x mono sup hx\b(?! hX)', ' x mono sup hx hX'),
    ('resfor', r'ResFor env (msup|\(some p\))', r'ResForR (runLCM env true \1)'),
    ('partL', r'PartL env msup ctx', 'PartR env msup ctx X'),
    ('runenv', r'runLC ((?:\(\w+ := [^)]*\) )*)env ', r'runLCM \1env true '),
    ('n2none', r'\brunLC_n2_none\b', 'runLCM_n2_none'),
    ('consdone', r'\brunLC_cons_done\b', 'runLCM_cons_done'),
    ('runsimp', r'\brunLC\b', 'runLCM'),
    ('pastL', r'pastL ((?:\(\w+ := [^)]*\) )*)noCode', r'pastL \1env.cod'),
    ('hpn', r'\((h\w+) : hinted noCode (\w+) ≠ Option\.none\)', r'(\1 : PastAt ctx env.cod \2)'),
    ('comppast', r'comp_past h7 hcode (\w+) (\w+) (⟨[^⟩]*⟩|\w+) (\w+) (\w+) (h\w+)', r'\6 \1 \2 \3 \5'),
    ('ndpair', r'(\n *)obtain ⟨(\w+), (\w+)⟩ := hinted_nd env\.cod (\w+)\.nd', r'\1have \3 := \4.past'),
    ('ndone', r'\n *obtain ⟨\w+, -⟩ := hinted_nd env\.cod \w+\.nd', ''),
    ('ndsnd', r'(\n *)obtain ⟨-, (\w+)⟩ := hinted_nd env\.cod (\w+)\.nd', r'\1have \2 := \3.past'),
    ('pastcod', r'\n *simp only \[pastL_cod \w+(?:, pastL_cod \w+)*\]', ''),
]

AUTO = '(hX : X x mono sup := by assumption)'

def transform(block, pre):
    cnt = {}
    for old, new in pre:
        c = block.count(old)
        cnt['pre:' + old[:30]] = c
        block = block.replace(old, new)
    for key, pat, rep in RULES:
        block, c = re.subn(pat, rep, block)
        cnt[key] = c
    # the lemmas that take `x mono sup` as parameters get the last binder `hX`
    hdr_end = re.search(r'[\)\}\]] :\n', block)
    hdr = block[:hdr_end.start()] if hdr_end else ''
    if ('intro x mono sup hx hX' not in block and '(x : GenRest)' in hdr and re.search(r'\bmono\b', hdr)
            and re.search(r'\bsup\b', hdr) and AUTO not in block):
        i = hdr_end.start() + 1
        block = block[:i] + ' ' + AUTO + block[i:]
        cnt['auto'] = 1
    else:
        cnt['auto'] = 0
    return block, cnt

def gen(out, header, parts, expect):
    """parts: list of (source file, names, pre-replacements)."""
    total = {}
    body = []
    for path, names, pre in parts:
        for blk in extract(D + path, names):
            b, cnt = transform(blk, pre)
            for k, v in cnt.items():
                total[k] = total.get(k, 0) + v
            body.append(b)
        RENAMED.extend(names)
    body = [rename(b) for b in body]
    if COUNTS:
        print(out, {k: v for k, v in sorted(total.items()) if v})
    else:
        for k, v in total.items():
            assert expect.get(k, 0) == v, (out, k, v, expect.get(k, 0))
    for b in body:
        assert 'runLC ' not in b and 'runLC]' not in b and 'pastL noCode' not in b, (out, b[:200])
    txt = header + '\n'.join(body) + '\nend Compiler\nend Formalization\n'
    open(D + out, 'w').write(txt)

def head(imports, doc):
    return ('\n'.join('import ' + i for i in imports) + '\n\n/-!\n' + doc +
            '\n\nGenerated by `tools/gen/runr.py` from track A\'s files; do not edit.\n-/\n\n'
            'namespace Formalization\nnamespace Compiler\n\nopen Nock Pill Hoon SkaModel SkaModel.Comp\n\n'
            'set_option linter.unusedSimpArgs false\nset_option linter.unusedSectionVars false\n'
            'set_option linter.unusedVariables false\n\n'
            'variable {ctx : Noun} {X : GenRest → Noun → Noun → Prop}\n\n')

# --- results ---------------------------------------------------------------
gen('CompRunRRes.lean',
    head(['lemmas.Compiler.CompRunRBase'],
         '# What a run against `runLCM env true` returns (copies of `CompRunResAll.lean`)'),
    [('CompRunResAll.lean', ['tail_all', 'tail_fresh', 'tail_bunt', 'res_last', 'res_n3', 'res_n4', 'res_n7',
                             'res_n5', 'res_n2', 'res_cons_next', 'res_cons', 'res_n10'], [])],
    {'n2none': 1, 'resfor': 28, 'runenv': 9, 'runsimp': 10})

# --- %3, %4, %7 -------------------------------------------------------------
N7 = [('(hq : CompRunAtR (runLC env (some p)) ctx q goal region g)',
       '{Xq : GenRest → Noun → Noun → Prop}\n    (hq : CompRunAtX (runLCM env true (some p)) ctx Xq q goal region g)\n'
       '    (hXq : ∀ x mono sup, X x mono sup → Xq x mono (C (A 0) p.toNoun))'),
      ('hq x mono (C (A 0) p.toNoun) hx', 'hq x mono (C (A 0) p.toNoun) hx (hXq x mono sup hX)')]
gen('CompRunRLeaf.lean',
    head(['lemmas.Compiler.CompRunRRes'],
         '# `%3`, `%4`, `%7` of `+run` against `runLCM env true` (copies of `CompRunCall.lean`, `CompRunLeafL.lean`)'),
    [('CompRunLeafL.lean', ['hp_toL'], []),
     ('CompRunCall.lean', ['comp_run_n4C', 'comp_run_n3C'], []),
     ('CompRunCall.lean', ['comp_run_n7C'], N7),
     ('CompRunLeafL.lean', ['comp_run_n4_next', 'comp_run_n4L', 'comp_run_n3_next', 'comp_run_n3L'], [])],
    {'app': 13, 'intro': 5, 'linkR': 18, 'pre:(hq : CompRunAtR (runLC env (s': 1, 'pre:hq x mono (C (A 0) p.toNoun) h': 1, 'runenv': 8, 'runsimp': 23})

# --- cons -------------------------------------------------------------------
gen('CompRunRCons.lean',
    head(['lemmas.Compiler.CompRunRLeaf'],
         '# The cons of `+run` against `runLCM env true` (copies of `CompRunConsL.lean`)'),
    [('CompRunConsL.lean', ['crc_ntailL', 'runLC_cons_next', 'runLC_cons_pick', 'crc_nextL', 'crc_pickL',
                            'comp_run_consL'], [])],
    {'app': 4, 'auto': 3, 'comppast': 3, 'consdone': 1, 'hpn': 2, 'intro': 1, 'linkR': 3, 'ndone': 1, 'ndpair': 3, 'partL': 6, 'pastL': 11, 'pastcod': 2, 'runenv': 18, 'runsimp': 2})

# --- %5 and the indirect %2 ----------------------------------------------------
gen('CompRunRFive.lean',
    head(['lemmas.Compiler.CompRunRCons'],
         '# `%5` and the indirect `%2` of `+run` against `runLCM env true` (copies of `CompRunFiveL.lean`)'),
    [('CompRunFiveL.lean', ['cr5_tailL', 'cr5_modelL', 'comp_run_n5L', 'cr2_tailL', 'cr2KfML', 'cr2_kfL',
                            'comp_run_n2L'],
      [('rw [cr2_model]; unfold cr2KfM cr2KfML; simp only [pastL_cod hpc]', 'rfl')])],
    {'app': 4, 'auto': 3, 'comppast': 2, 'hpn': 2, 'intro': 2, 'linkR': 6, 'ndone': 1, 'ndpair': 1, 'ndsnd': 1, 'partL': 6, 'pastL': 9, 'pastcod': 1, 'pre:rw [cr2_model]; unfold cr2KfM ': 1, 'runenv': 20, 'runsimp': 2})

# --- %10 --------------------------------------------------------------------
gen('CompRunRTen.lean',
    head(['lemmas.Compiler.CompRunRFive'],
         '# `%10` of `+run` against `runLCM env true` (copies of `CompRunTenL.lean`)'),
    [('CompRunTenL.lean', ['cr10_tailL', 'runLC_n10', 'comp_run_n10L'], [])],
    {'app': 2, 'auto': 1, 'comppast': 2, 'hpn': 2, 'intro': 1, 'linkR': 3, 'ndpair': 2, 'partL': 2, 'pastL': 10, 'pastcod': 1, 'runenv': 10, 'runsimp': 1})
