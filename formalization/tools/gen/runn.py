#!/usr/bin/env python3
"""Write lemmas/Compiler/CompRunRN*.lean and CompRunTN*.lean: the case lemmas of
`+run` at `mono` `|` (the n-ary run of `+compile-scc-in`'s members, lines 3511
and 3531 of the Hoon), copied from the `mono` `&` files CompRunR*.lean
(runr.py) and CompRunT*.lean (runt.py) (README Gaps 19 (g)).  Rerun after
those change.  Run from formalization/.

The case lemmas of cons, `%3`, `%4`, `%5`, the indirect `%2`, `%6`, `%10` do
not read `mono` on the pill's side (the pill reads it only at a direct call,
lines 4004, 4016, 4036, and at `%mean`, line 4312), so the copy changes the
model alone: `runLCM env true` -> `runLCM env false`.  The rule asserts its
count per file.  A declaration whose text the rule changes is copied with
the name `n` -> `nN`, and so is every declaration that names a copied one
(closure); the others are not copied (the originals are imported).  The
direct call at `mono` `|` differs in substance and is by hand
(CompRunTNCall.lean).
"""
import re, sys

D = 'lemmas/Compiler/'
COUNTS = '--counts' in sys.argv

TOP = re.compile(r'^(?:/--|/-!|theorem |def |noncomputable def |structure |end |example|@\[|abbrev |variable |open |namespace |set_option |section)', re.M)
DECL = re.compile(r'^(?:/--.*?-/\s*)?(?:theorem|def|noncomputable def|structure|abbrev) (\S+)', re.S)
FLAG = re.compile(r'(runLCM(?: \(S := CSet\))?(?: \(Map := TreapMap mugF\))? env) true\b')

def chunks(src):
    st = [m.start() for m in TOP.finditer(src)] + [len(src)]
    cs = [src[a:b] for a, b in zip(st, st[1:])]
    out = []
    i = 0
    while i < len(cs):
        if cs[i].startswith('/--') and i + 1 < len(cs):
            out.append(cs[i] + cs[i + 1]); i += 2
        else:
            out.append(cs[i]); i += 1
    return src[:st[0]], out

# (source, target, names never copied, expected count of the flag rule)
FILES = [
    ('CompRunRBase', 'CompRunRNBase', {'crx_of_runLC', 'partR_of_partL', 'crx_iff_mm', 'partLM_of_partR'}, 9),
    ('CompRunRRes', 'CompRunRNRes', set(), 37),
    ('CompRunRLeaf', 'CompRunRNLeaf', set(), 27),
    ('CompRunRCons', 'CompRunRNCons', set(), 21),
    ('CompRunRFive', 'CompRunRNFive', set(), 26),
    ('CompRunRTen', 'CompRunRNTen', set(), 13),
    ('CompRunRSixS', 'CompRunRNSixS', set(), 26),
    ('CompRunRSixN', 'CompRunRNSixN', set(), 23),
    ('CompRunRSixF', 'CompRunRNSixF', set(), 33),
    ('CompRunRSixL', 'CompRunRNSixL', set(), 20),
    ('CompRunRSixAll', 'CompRunRNSixAll', set(), 28),
    ('CompRunTBase', 'CompRunTNBase', set(), 2),
    ('CompRunTLeaf', 'CompRunTNLeaf', set(), 22),
    ('CompRunTCons', 'CompRunTNCons', set(), 15),
    ('CompRunTFive', 'CompRunTNFive', set(), 21),
    ('CompRunTTen', 'CompRunTNTen', set(), 10),
    ('CompRunTSixS', 'CompRunTNSixS', set(), 18),
    ('CompRunTSixN', 'CompRunTNSixN', set(), 6),
    ('CompRunTSixF', 'CompRunTNSixF', set(), 15),
    ('CompRunTSixL', 'CompRunTNSixL', set(), 10),
    ('CompRunTSixAll', 'CompRunTNSixAll', set(), 6),
]
TGT = {s: t for s, t, _, _ in FILES}

def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    return m.group(1) + 'N' + m.group(2)

# pass 1: chunks, changed declarations
data = []
names = {}
for src, tgt, excl, _ in FILES:
    pre, cs = chunks(open(D + src + '.lean').read())
    data.append((src, tgt, excl, pre, cs))
    for c in cs:
        m = DECL.match(c)
        if m:
            assert m.group(1) not in names, m.group(1)
            names[m.group(1)] = (src, c)

def refs(n, c):
    return re.search(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", c) is not None

copied = {n for n, (s, c) in names.items() if FLAG.search(c)}
excl_all = set().union(*[e for _, _, e, _, _ in data])
copied -= excl_all
while True:
    more = {n for n, (s, c) in names.items() if n not in copied and n not in excl_all
            and any(refs(k, c) for k in copied)}
    if not more:
        break
    copied |= more

ren = sorted(copied, key=len, reverse=True)
def rename(c):
    for n in ren:
        c = re.sub(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", newname(n), c)
    return c

for (src, tgt, excl, pre, cs), (_, _, _, exp) in zip(data, FILES):
    body = []
    cnt = 0
    for c in cs:
        m = DECL.match(c)
        if c.startswith('example'):
            continue
        if m:
            if m.group(1) not in copied:
                continue
            c2, k = FLAG.subn(r'\1 false', c)
            cnt += k
            body.append(rename(c2))
        elif c.startswith('/-!'):
            continue
        else:
            assert not re.search(r'\benv true\b', c), (src, c[:200])
            body.append(c)
    if COUNTS:
        print(src, cnt)
        continue
    assert cnt == exp, (src, cnt, exp)
    imps = re.findall(r'^import (\S+)$', pre, re.M)
    new = []
    for i in imps:
        new.append(i)
        b = i.split('.')[-1]
        if b in TGT:
            new.append('lemmas.Compiler.' + TGT[b])
    new.append('lemmas.Compiler.' + src)
    if src.startswith('CompRunR') and src != 'CompRunRBase':
        new.append('lemmas.Compiler.CompRunRNBase')
    if src.startswith('CompRunT') and src != 'CompRunTBase':
        new.append('lemmas.Compiler.CompRunTNBase')
    if src == 'CompRunTBase':
        new.append('lemmas.Compiler.CompRunRNBase')
    seen = []
    for i in new:
        if i not in seen and i != 'lemmas.Compiler.' + tgt:
            seen.append(i)
    head = ''.join('import ' + i + '\n' for i in seen)
    doc = ('\n/-!\n# `{s}.lean` at `mono` `|` (README Gaps 19 (g))\n\n'
           'Generated by `tools/gen/runn.py` from `{s}.lean`: `runLCM env true` -> `runLCM env false`,\n'
           'every declaration the rule reaches renamed `n` -> `nN`; do not edit.\n-/\n\n').format(s=src)
    out = head + doc + ''.join(body)
    assert not re.search(r'\benv true\b', ''.join(body)), src
    open(D + tgt + '.lean', 'w').write(out)
print(len(copied), 'declarations copied')
