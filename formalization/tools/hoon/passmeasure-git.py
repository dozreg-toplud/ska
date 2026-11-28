#!/usr/bin/env python3
# usage: passmeasure-git.py --instrument LIB.hoon OUT.hoon        (track F, README Gaps 16)
#        passmeasure-git.py [-v] OUT.txt...
# The `done` answers of +git:mi across the passes of a pass loop (point (c) of Gaps 16).
# --instrument adds to a library of passmeasure.py (any of its descendants) an arm +pw-all and,
# at the `done` hit of the resolution of a %2 in +fol-loop, a print
#   [%pw-hit fol-mug sock-mug entry-mug patched-mug less-mug [tot npass ndistinct]]
# (the mug of the formula and of the caller's subject sock, of the identity of the entry that
# answered, of the patched [prod map], of its less-code; the entries stored for the formula,
# how many of them pass the hit test at that sock, and how many distinct patched products those
# give).  The check: per pass loop of root r (from its [%pm-pass r 1 ..] to the last pass of r
# before the next pass 1 of r; hits inside nested loops count for every open loop), per
# (formula, sock): the answers per pass.  Prints (i) the calls answered in two passes of one loop
# by different entries, or with different patched products; (ii) the hits with more than one
# passing entry and more than one distinct patched product; (iii) per loop with the most passes
# and for the loop with the most pushes, what each pass did (pushes, hits, changed hits).
import sys, re, os, collections

def instrument(lib, out):
    s = open(lib).read()
    helper = '''++  pw-all
  |=  [m=memo f=^ s=sock]
  ^-  [@ud @ud @ud]
  =/  entries=(list [* id=identity d=datum])  ~(tap by (gut:mi m f))
  =/  tot=@ud  (lent entries)
  =|  n=@ud
  =|  ps=(set *)
  |-  ^-  [@ud @ud @ud]
  ?~  entries  [tot n ~(wyt in ps)]
  ?.  ?&  (huge:so less-code.d.i.entries s)
          %+  huge:so  (app:ca indi.d.i.entries s)
          (app:ca indi.d.i.entries more.id.i.entries)
      ==
    $(entries t.entries)
  =/  p  (patch-prod [prod map]:d.i.entries s)
  $(entries t.entries, n +(n), ps (~(put in ps) p))
::
'''
    assert s.count('++  pf-subs\n') == 1, 'needs the library of passmeasure-forms.py'
    s = s.replace('++  pf-subs\n', helper + '++  pf-subs\n')
    old = '''        ?^  m=(git:mi done.st.gen fol-new more.id-there)
          [u.m gen]
'''
    assert s.count(old) == 1
    new = '''        ?^  m=(git:mi done.st.gen fol-new more.id-there)
          ~&  :*  %pw-hit  (mug fol-new)  (mug more.id-there)  (mug -.u.m)
                  (mug [prod map]:+.u.m)  (mug less-code.+.u.m)
                  (pw-all done.st.gen fol-new more.id-there)
              ==
          [u.m gen]
'''
    open(out, 'w').write(s.replace(old, new))

def num(x):
    x = x.strip('[]').replace('.', '')
    return int(x, 16) if x.startswith('0x') else int(x)

def pmlines(path):
    raw = []
    for l in open(path, errors='replace').read().split('\n'):
        if l[:1] in (' ', '\t') and raw:
            raw[-1] += ' ' + l.strip()
        else:
            raw.append(l)
    raw = [re.sub(r'\s+', ' ', l).replace('[ %p', '[%p') for l in raw]
    return [l.strip() for l in raw if l[:3] == '[%p']

def cases(path):
    ev = []
    for l in pmlines(path):
        t = l.replace('[', ' ').replace(']', ' ').split()
        tag = t[0]
        if tag == '%pm-case' or (tag == '%pm-new' and num(t[2]) == 0 and num(t[3]) == 0):
            if ev: yield ev
            ev = []
            if tag == '%pm-case': continue
        if tag == '%pm-new': ev.append(('new', t[1], num(t[3])))
        elif tag == '%pm-pass': ev.append(('pass', t[1], num(t[2]), num(t[5])))
        elif tag == '%pm-end': ev.append(('end', t[1], num(t[2])))
        elif tag == '%pw-hit':
            ev.append(('hit', (t[1], t[2]), t[3], t[4], t[5], num(t[6]), num(t[7]), num(t[8])))
    if ev: yield ev

def loops(ev):
    # [root, first index, last pass-start index, end index, passes]
    out, open_ = [], {}
    for k, e in enumerate(ev):
        if e[0] == 'pass':
            r, p = e[1], e[2]
            if p == 1 or r not in open_:
                if r in open_: out.append(open_[r])
                open_[r] = [r, k, k, k, 1]
            else:
                L = open_[r]; L[2] = k; L[3] = k; L[4] = max(L[4], p)
        elif e[0] == 'end' and e[1] in open_:
            open_[e[1]][3] = k
    out += open_.values()
    return out

def main(paths, verbose):
    tot = collections.Counter()
    multi = []          # hits with more than one distinct patched product
    diff_e, diff_p = [], []
    best_pass, best_push = (0, None), (0, None)
    for path in paths:
        fam = os.path.basename(path)
        for ci, ev in enumerate(cases(path)):
            for e in ev:
                if e[0] == 'hit':
                    tot['hits'] += 1
                    if e[6] > 1: tot['hits with >1 passing entry'] += 1
                    if e[7] > 1:
                        tot['hits with >1 patched product'] += 1; multi.append((fam, ci, e))
            for (r, k0, k1, kend, np) in loops(ev):
                tot['loops'] += 1
                cur = 0; per = collections.defaultdict(dict); pushes = collections.Counter()
                hits = collections.Counter()
                for k in range(k0, kend + 1):
                    e = ev[k]
                    if e[0] == 'pass' and e[1] == r: cur = e[2]
                    elif e[0] == 'new': pushes[cur] += 1
                    elif e[0] == 'hit':
                        hits[cur] += 1
                        per[e[1]].setdefault(cur, set()).add((e[2], e[3]))
                de = dp = 0
                for key, byp in per.items():
                    if len(byp) < 2: continue
                    ents = {x[0] for s in byp.values() for x in s}
                    pats = {x[1] for s in byp.values() for x in s}
                    if len(ents) > 1: de += 1
                    if len(pats) > 1: dp += 1
                if de: diff_e.append((de, fam, ci, r, np))
                if dp: diff_p.append((dp, fam, ci, r, np))
                tot['(formula, sock) called in two passes of a loop'] += sum(1 for b in per.values() if len(b) > 1)
                info = (fam, ci, r, np, dict(pushes), dict(hits), per)
                if np > best_pass[0]: best_pass = (np, info)
                s = sum(pushes.values())
                if s > best_push[0]: best_push = (s, info)
    for k, v in tot.items(): print(f'{k}: {v}')
    print('(i) loops with a call answered by different entries in two passes:', len(diff_e), sorted(diff_e, reverse=True)[:5])
    print('(i) loops with a call answered with different patched products in two passes:', len(diff_p), sorted(diff_p, reverse=True)[:5])
    print('(ii) hits with >1 distinct patched product among the passing entries (first 5):')
    for m in multi[:5]: print('  ', m)
    for name, (n, info) in (('most passes', best_pass), ('most pushes', best_push)):
        if info is None: continue
        fam, ci, r, np, pushes, hits, per = info
        print(f'(iii) {name}: {n}: {fam} case {ci} root {r} passes {np}')
        for p in range(1, np + 1):
            ch = sum(1 for b in per.values() if p in b and p - 1 in b and b[p] != b[p - 1])
            same = sum(1 for b in per.values() if p in b and p - 1 in b and b[p] == b[p - 1])
            print(f'    pass {p}: pushes {pushes.get(p, 0)} hits {hits.get(p, 0)} calls also in pass {p-1}: same answer {same}, other answer {ch}')

if __name__ == '__main__':
    if sys.argv[1] == '--instrument':
        instrument(sys.argv[2], sys.argv[3])
    else:
        v = sys.argv[1] == '-v'
        main(sys.argv[2:] if v else sys.argv[1:], v)
