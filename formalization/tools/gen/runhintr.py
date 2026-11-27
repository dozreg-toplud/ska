#!/usr/bin/env python3
"""Write lemmas/Compiler/CompRunHint{Res,Leaf,Cons,Five,Ten,SixS,SixN,SixF,
SixL,SixAll}.lean: copies of track K's case lemmas of +run against
`runLCM env true msup` (`CompRunR*.lean`, themselves made by `runr.py`)
against the model with hints `runLCH env snd true msup` (README Gaps 25).
The case lemmas of the hint-free constructors are then usable on parts that
hold hints.  The originals are not changed; rerun after they change.  Run
from formalization/.

Every declaration `n` of the copied files is renamed `nH` (and so are its
uses).  The rules are textual and each asserts its count per file
(`--counts` prints them, to update `EXPECT` after a change upstream):

* model: `runLCM (S := ..) (Map := ..) env true` and `runLCM env true` ->
  the same with `runLCH .. env snd true`; `runLCM` in simp sets and
  `unfold` -> `runLCH`; the two model equations of `CompRunRBase.lean`
  (`runLCM_n2_none`, `runLCM_cons_done`) are copied as `runLCH_n2_none`,
  `runLCH_cons_done` at the head of the first file;
* parts: `PartR env msup` -> `PartH env snd msup` (`CompRunHintS.lean`),
  `SixPartsR env msup` -> `SixPartsRH env snd msup` (the structure gets the
  parameter `snd`);
* every file gets `variable {snd : Nomm → NeedOrd → Bool}`.
"""
import re, sys

D = 'lemmas/Compiler/'
COUNTS = '--counts' in sys.argv
FILES = ['Res', 'Leaf', 'Cons', 'Five', 'Ten', 'SixS', 'SixN', 'SixF', 'SixL', 'SixAll']
SRC = {f: open(D + 'CompRunR%s.lean' % f).read() for f in FILES}

DECL = re.compile(r'^(?:theorem|def|noncomputable def|structure|abbrev) ([^\s(:{\[]+)', re.M)
names = set()
for f in FILES:
    names |= set(DECL.findall(SRC[f]))
base = open(D + 'CompRunRBase.lean').read()
i = base.index('section\nvariable {S : Type} [HoonSet S]')
j = base.index('end\n', i) + 4
MODEL = base[i:j]
assert 'runLCM_n2_none' in MODEL and 'runLCM_cons_done' in MODEL
assert MODEL.count('variable {S : Type} [HoonSet S]') == 1
MODEL = MODEL.replace('variable {S : Type} [HoonSet S]', 'variable {snd : Nomm → NeedOrd → Bool} {S : Type} [HoonSet S]')

SNDDEFS = set()
for f in FILES:
    SNDDEFS |= set(re.findall(r'^(?:noncomputable )?def (\S+) \(env : CallEnv\) \(msup', SRC[f], re.M))

def rename(s):
    for n in sorted(names, key=len, reverse=True):
        s = re.sub(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", n + 'H', s)
    return s

RULES = [
    ('modelS', r'\brunLCM((?: \((?:S|Map) := [^)]*\))+) env true\b', r'runLCH\1 env snd true'),
    ('model', r'\brunLCM env true\b', 'runLCH env snd true'),
    ('modelM', r'\brunLCM env mono\b', 'runLCH env snd mono'),
    ('bare', r'\brunLCM\b', 'runLCH'),
    ('n2none', r'\brunLCM_n2_none\b', 'runLCH_n2_none'),
    ('consdone', r'\brunLCM_cons_done\b', 'runLCH_cons_done'),
    ('part', r'\bPartR env msup\b', 'PartH env snd msup'),
    ('six', r'\bSixPartsRH env msup\b', 'SixPartsRH env snd msup'),
    ('sixdef', r'structure SixPartsRH \(env : CallEnv\) \(msup', 'structure SixPartsRH (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup'),
    ('var', r'^variable \{ctx : Noun\}', 'variable {ctx : Noun} {snd : Nomm → NeedOrd → Bool}'),
]
EXPECT = {
    'Res': {'modelS': 0, 'model': 45, 'modelM': 0, 'bare': 12, 'n2none': 2, 'consdone': 1, 'part': 0, 'six': 0, 'sixdef': 0, 'var': 1, 'snddefs': 0},
    'Leaf': {'modelS': 4, 'model': 24, 'modelM': 0, 'bare': 23, 'n2none': 0, 'consdone': 0, 'part': 0, 'six': 0, 'sixdef': 0, 'var': 1, 'snddefs': 0},
    'Cons': {'modelS': 4, 'model': 18, 'modelM': 0, 'bare': 2, 'n2none': 0, 'consdone': 1, 'part': 6, 'six': 0, 'sixdef': 0, 'var': 1, 'snddefs': 0},
    'Five': {'modelS': 4, 'model': 23, 'modelM': 0, 'bare': 2, 'n2none': 0, 'consdone': 0, 'part': 6, 'six': 0, 'sixdef': 0, 'var': 1, 'snddefs': 3},
    'Ten': {'modelS': 2, 'model': 12, 'modelM': 0, 'bare': 1, 'n2none': 0, 'consdone': 0, 'part': 2, 'six': 0, 'sixdef': 0, 'var': 1, 'snddefs': 0},
    'SixS': {'modelS': 3, 'model': 24, 'modelM': 0, 'bare': 0, 'n2none': 0, 'consdone': 0, 'part': 0, 'six': 3, 'sixdef': 1, 'var': 1, 'snddefs': 7},
    'SixN': {'modelS': 1, 'model': 23, 'modelM': 0, 'bare': 0, 'n2none': 0, 'consdone': 0, 'part': 0, 'six': 6, 'sixdef': 0, 'var': 1, 'snddefs': 8},
    'SixF': {'modelS': 3, 'model': 31, 'modelM': 0, 'bare': 0, 'n2none': 0, 'consdone': 0, 'part': 0, 'six': 3, 'sixdef': 0, 'var': 1, 'snddefs': 10},
    'SixL': {'modelS': 0, 'model': 21, 'modelM': 0, 'bare': 0, 'n2none': 0, 'consdone': 0, 'part': 0, 'six': 12, 'sixdef': 0, 'var': 1, 'snddefs': 0},
    'SixAll': {'modelS': 0, 'model': 29, 'modelM': 0, 'bare': 0, 'n2none': 0, 'consdone': 0, 'part': 0, 'six': 20, 'sixdef': 0, 'var': 1, 'snddefs': 3},
}
IMPORT = {
    'Res': ['lemmas.Compiler.CompRunHintS'],
    'Leaf': ['lemmas.Compiler.CompRunHintRes'],
    'Cons': ['lemmas.Compiler.CompRunHintLeaf'],
    'Five': ['lemmas.Compiler.CompRunHintCons'],
    'Ten': ['lemmas.Compiler.CompRunHintFive'],
    'SixS': ['lemmas.Compiler.CompRunHintTen'],
    'SixN': ['lemmas.Compiler.CompRunHintSixS'],
    'SixF': ['lemmas.Compiler.CompRunHintSixN'],
    'SixL': ['lemmas.Compiler.CompRunHintSixN'],
    'SixAll': ['lemmas.Compiler.CompRunHintSixF', 'lemmas.Compiler.CompRunHintSixL'],
}
counts = {}
for f in FILES:
    s = SRC[f]
    s = re.sub(r'^import .*\n', '', s, flags=re.M)
    s = rename(s)
    if f == 'Res':
        k = s.index('variable {ctx : Noun}')
        s = s[:k] + MODEL + '\n' + s[k:]
    c = {}
    for nm, pat, rep in RULES:
        s, n = re.subn(pat, rep, s, flags=re.M)
        c[nm] = n
    # defs of the model take `snd` explicitly
    nd = 0
    for d in SNDDEFS:
        s, n1 = re.subn(r'def %sH \(env : CallEnv\) \(msup' % d,
                        'def %sH (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup' % d, s)
        s, n2 = re.subn(r'\b%sH env msup\b' % d, '%sH env snd msup' % d, s)
        left = len(re.findall(r"\b%sH env (?!snd)" % d, s))
        assert left == 0, (f, d, left)
        nd += n1 + n2
    c['snddefs'] = nd
    counts[f] = c
    assert 'runLCM' not in s.replace('runLCM_true', ''), (f, s[s.index('runLCM') - 80:s.index('runLCM') + 80])
    hdr = ''.join('import %s\n' % m for m in IMPORT[f])
    hdr += '\n/-! Generated by `tools/gen/runhintr.py` from `CompRunR%s.lean` (README Gaps 25):\nthe same lemmas against `runLCH env snd true msup`, every name `n` as `nH`. -/\n' % f
    if not COUNTS:
        open(D + 'CompRunHint%s.lean' % f, 'w').write(hdr + s)
if COUNTS:
    for f in FILES:
        print(repr(f), ':', counts[f], ',')
else:
    for f in FILES:
        if f in EXPECT:
            assert counts[f] == EXPECT[f], (f, counts[f], EXPECT[f])
    print('wrote', len(FILES), 'files;', len(names), 'names renamed')
