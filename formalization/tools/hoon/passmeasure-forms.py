#!/usr/bin/env python3
# usage: passmeasure-forms.py --instrument IN.hoon OUT.hoon
#        passmeasure-forms.py OUT.txt...                            (track F, README Gaps 16)
# The formulas of pushed identities against the nouns of the poke.  --instrument adds, to a
# library already instrumented by passmeasure.py (it needs its %pm-new line in +analyze), one
# arm +pf-subs (the mugs of every subnoun of a noun, memoized) and, right after the push of
# +analyze, one print
#   [%pf-new mug-id mug-fol in sock]   in: %.y when the formula is a subnoun of
#        [fol data] of the bottom of the stack (the root of the poke: its formula and the data
#        of its subject sock); sock: the subject sock of the pushed identity, or %big
#        (and the formula itself, or %big, when it is not a subnoun)
# The check: per case (a %pm-case line, or a %pm-new at index 0 and depth 0), the distinct
# pushed formulas, and the pushes whose formula is not a subnoun of the root's nouns.
import re, sys, os

SUBS = [
    '++  pf-subs',
    '  |=  n=*',
    '  ^-  (set @)',
    '  ~+',
    '  =|  s=(set @)',
    '  =/  q=(list *)  ~[n]',
    '  |-  ^-  (set @)',
    '  ?~  q  s',
    '  =/  m  (mug i.q)',
    '  ?:  (~(has in s) m)  $(q t.q)',
    '  =.  s  (~(put in s) m)',
    '  ?@  i.q  $(q t.q)',
    '  $(q [-.i.q +.i.q t.q])',
    '::',
]

NEW = [
    '    =/  pf-root=identity  (rear stk.st)',
    '    =/  pf-in=?',
    '      %.  (mug fol.id)',
    '      ~(has in (pf-subs [fol.pf-root ?@(more.pf-root ~ data.more.pf-root)]))',
    '    ~&  :*  %pf-new  (mug id)  (mug fol.id)  pf-in',
    '            ?:((lth (met 3 (jam more.id)) 400) more.id %big)',
    '            ?:(|(pf-in (gth (met 3 (jam fol.id)) 400)) %big fol.id)',
    '        ==',
]

def instrument(inp, out):
    src = open(inp).read().split('\n')
    h = [i for i, l in enumerate(src) if l == '++  he-sock'][0]
    src[h:h] = SUBS
    k = [i for i, l in enumerate(src) if l.startswith('    ~&  [%pm-new (mug id) index')][0]
    j = [i for i in range(k, k + 12) if src[i] == '      =='][0]
    src[j + 1:j + 1] = NEW
    open(out, 'w').write('\n'.join(src))

def lines(path):
    raw = []
    for l in open(path, errors='replace').read().split('\n'):
        if l[:1] in (' ', '\t') and raw:
            raw[-1] += ' ' + l.strip()
        else:
            raw.append(l)
    raw = [re.sub(r'\s+', ' ', l).replace('[ %p', '[%p') for l in raw]
    return [l.strip() for l in raw if l[:3] in ('[%p', '%pm', '%pf')]

def check(paths):
    cases = 0; pushes = 0; outside = []; maxf = (0, None); hist = {}
    for path in paths:
        fam = os.path.basename(path); forms = None; name = None
        def flush():
            nonlocal maxf
            if forms is None: return
            n = len(forms); hist[n] = hist.get(n, 0) + 1
            if n > maxf[0]: maxf = (n, name)
        for l in lines(path):
            t = l.strip('[]').split()
            if t[0] == '%pm-case' or (t[0] == '%pm-new' and t[2] in ('0', '0x0') and t[3] == '0'):
                flush(); cases += 1; forms = set(); name = fam + ':' + ' '.join(t[1:3])
                continue
            if t[0] == '%pf-new':
                if forms is None: cases += 1; forms = set(); name = fam
                pushes += 1; forms.add(t[2])
                if t[3] != '%.y': outside.append((name, l[:400]))
        flush()
    print('cases', cases, 'pushes', pushes, 'largest distinct pushed formulas of one case:', maxf)
    print('histogram of distinct pushed formulas per case:', sorted(hist.items())[:30])
    print('pushes whose formula is not a subnoun of the root formula and subject:', len(outside))
    for x in outside[:15]: print('  ', x)

if __name__ == '__main__':
    if sys.argv[1] == '--instrument':
        instrument(sys.argv[2], sys.argv[3])
    else:
        check(sys.argv[1:])
