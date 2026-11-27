"""Corollaries of the loop's gate theorems without the hypothesis `PrintId` (discharged by
`printId_pill`, README Gaps 21.14).  For each theorem NAME, the signature is copied without
its binder `hpr`, and the proof applies NAME to every binder in order, `hpr` by
`printId_pill`.  Prints the Lean text.

    python3 tools/gen/noprint.py FILE:NAME:NEWNAME ..."""
import sys, re

def binders(sig):
    """Top-level binder groups of `sig` (text after the name), and the rest (`: type`)."""
    out, i, n = [], 0, len(sig)
    while True:
        while i < n and sig[i].isspace():
            i += 1
        if i < n and sig[i] in '({[⦃':
            op = sig[i]; cl = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}[op]
            d, j = 0, i
            while True:
                if sig[j] in '({[⦃':
                    d += 1
                elif sig[j] in ')}]⦄':
                    d -= 1
                    if d == 0:
                        break
                j += 1
            out.append(sig[i:j + 1]); i = j + 1
        else:
            return out, sig[i:]

def names(b):
    inner = b[1:-1]
    if b[0] == '[':
        return b[0], []
    k = inner.index(':') if ':' in inner else len(inner)
    return b[0], inner[:k].split()

for arg in sys.argv[1:]:
    f, name, new = arg.split(':')
    txt = open(f).read()
    m = re.search(r'^theorem %s\b(.*?):= by' % re.escape(name), txt, re.S | re.M)
    if not m:
        m = re.search(r'^theorem %s\b(.*?):=' % re.escape(name), txt, re.S | re.M)
    sig = m.group(1)
    bs, rest = binders(sig)
    keep, args = [], []
    for b in bs:
        kind, ns = names(b)
        if kind == '(' and ns == ['hpr']:
            args.append('(fun _ _ => printId_pill _)' if '∀ TOP MAY' in b else '(printId_pill _)')
            continue
        keep.append(b)
        if kind == '(':
            args += ns
    print('/-- `%s` with `PrintId` discharged (`printId_pill`). -/' % name)
    print('theorem %s %s %s :=' % (new, ' '.join(keep), rest.strip()))
    print('  %s %s\n' % (name, ' '.join(args)))
