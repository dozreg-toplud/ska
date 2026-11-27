#!/usr/bin/env python3
# usage: passmeasure-freeze.py [-v] OUT.txt...
# Track F, the freezing argument (2026-11-27, README Gaps 16, lemmas/Ska/PassFreeze.lean): reads
# %pm-ent (every member at a pass start: mug, DFS number, +dirty, entry classes, callees) and
# %pm-tik (the same start: tick and [ran chg] of every function in progress) of the library of
# passmeasure.py, and tests per pass loop, from the start of pass p to that of p+1 (the pass went on):
#   T0  +dirty is "some callee has chg >= the member's ran" (missing ticks [0 0]), at every start;
#   T1  a member that did not run in pass p keeps its callees and entry; a member clean at p that
#       ran in pass p (the member loop tests +dirty at the member's turn, not at the start) has a
#       callee whose chg at p+1 is at least its ran at p;
#   T1d a member dirty at p ran in pass p (its ran grew);
#   T2  a callee (at p+1) of a member present at p+1 that was a member at p is a member at p+1, the
#       same instance (not culled, not pushed again): the callees of a live member stay on the stack;
#   T3  the callees a dirty member at p+1 owes its dirt to (chg >= its ran), by kind: itself, pushed
#       in pass p, fell in pass p, unchanged (would be "dirty with nothing changed"), not a member;
#   T4  runs of consecutive starts at which a member is dirty while its entry and callee set are the
#       same as at the previous start (the open case of the argument), per member and per loop
#       (some member), their longest length and what ended them;
#       T4 also splits the stuck starts by the callees owed: only transient ones (not on the stack at
#       the loop's last start: the analogue of the open case, where persistent callees are frozen);
#   T5  every pass that went on had a dirty member at its start (passOn_dirty);
#   T6  every member at p+1 is reached from the root over callees among the members (+cull);
#   T7  per member, how often it changed its callee set with the same entry (claim R: finitely often);
#   E   lex by DFS number at p of (entry, the set of dirty callers charged to the member: each
#       dirty member is charged to the newest callee it owes its dirt to), the first position that
#       differs falls (E: by inclusion of the sets, Ec: by their size);
#   P2A some member at p falls or is culled by the start of p+2;
#   P2D lex by DFS number of (entry, +dirty) between p and p+2, the first difference a fall.
import re, sys, os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'passmeasure-stab.py')).read()
g = {}; exec(src.split("\nv = '-v'")[0], g)
pmlines, parse_ent, runclass, num = g['pmlines'], g['parse_ent'], g['runclass'], g['num']

def parse_tik(l):
    t = l.replace('[', ' [ ').replace(']', ' ] ').split()
    root, pas, tick = t[2], num(t[3]), num(t[4])
    body = t[5:]; tk = {}
    i = 0
    while i < len(body):
        if body[i] == '[' and i + 4 < len(body) and body[i + 4] == ']' and body[i + 1] not in '[]~':
            tk[body[i + 1]] = (num(body[i + 2]), num(body[i + 3])); i += 5
        else:
            i += 1
    return root, pas, tick, tk

def loops_of(path):
    # per case, per root: the list of starts [(pass, {mug: member}, ticks)], split when pass restarts
    out = []
    case = None; cur = {}; pend = {}
    for l in pmlines(path):
        tag = l.strip('[]').split()[0]
        if tag == '%pm-case':
            for r, ls in cur.items(): out.extend((case, r, x) for x in ls)
            case = (os.path.basename(path), l); cur = {}; pend = {}; continue
        if tag == '%pm-ent':
            root, pas, mem = parse_ent(l)
            pend[root] = (pas, mem)
        elif tag == '%pm-tik':
            root, pas, tick, tk = parse_tik(l)
            pas0, mem = pend.pop(root)
            assert pas0 == pas, l[:200]
            ls = cur.setdefault(root, [])
            if pas == 1 or not ls or ls[-1][-1][0] != pas - 1:
                ls.append([])
            ls[-1].append((pas, {m[0]: m for m in mem}, tk))
    for r, ls in cur.items(): out.extend((case, r, x) for x in ls)
    return out

def fall(cls): return runclass(*cls) not in ('none', None)

def analyse(paths, verbose):
    c = {}
    def inc(k, n=1): c[k] = c.get(k, 0) + n
    fails = {k: [] for k in ('T0', 'T1', 'T1d', 'T2', 'T6', 'T3same', 'T5', 'E', 'Ec', 'P2A', 'P2D')}
    runs_m = []; runs_l = []; switches = []; tmax = [(0,)]
    for path in paths:
        for case, root, starts in loops_of(path):
            inc('loops')
            gut = lambda tk, m: tk.get(m, (0, 0))
            for s, (pas, mem, tk) in enumerate(starts):
                inc('starts')
                for mug, m in mem.items():
                    d = any(gut(tk, k)[1] >= gut(tk, mug)[0] for k in m[3])
                    inc('T0 checked')
                    if d != m[4]: fails['T0'].append((case, root, pas, mug))
            stuck_prev = {}; lrun = 0; lstart = None; sw = {}; tstuck = {}; tstuck_prev = {}
            for s in range(len(starts) - 1):
                (p, M0, T0), (_, M1, T1) = starts[s], starts[s + 1]
                inc('passes that go on')
                if not any(m[4] for m in M0.values()): fails['T5'].append((case, root, p))
                for mug, m in M0.items():
                    n = M1.get(mug)
                    if n is None or n[1] != m[1]: continue
                    ran = gut(T1, mug)[0] != gut(T0, mug)[0]
                    if not ran:
                        inc('T1 not run')
                        if n[3] != m[3] or fall(n[2]): fails['T1'].append((case, root, p, mug, 'kept?'))
                    if not m[4]:
                        moved = any(k not in T1 and k in T0 or gut(T1, k)[1] >= gut(T0, mug)[0] for k in m[3])
                        inc('T1 clean at the start, a callee changed in the pass' if moved else
                            'T1 clean at the start, no callee changed in the pass')
                        if ran: inc('T1 clean at the start and run (dirty at its turn)')
                        if ran and not moved: fails['T1'].append((case, root, p, mug, 'ran'))
                    else:
                        inc('T1d checked')
                        if not ran: fails['T1d'].append((case, root, p, mug))
                    if not fall(n[2]) and n[3] != m[3]:
                        sw[(root, mug, m[1])] = sw.get((root, mug, m[1]), 0) + 1
                # T6: every member at p+1 is reached from the root over callees among members
                seen = {root}; q = [root]
                while q:
                    x = q.pop()
                    for k in M1[x][3] if x in M1 else ():
                        if k in M1 and k not in seen: seen.add(k); q.append(k)
                inc('T6 checked')
                if set(M1) - seen: fails['T6'].append((case, root, p + 1, sorted(set(M1) - seen)))
                for mug, n in M1.items():
                    for k in n[3]:
                        if k in M0:
                            inc('T2 checked')
                            if k not in M1 or M1[k][1] != M0[k][1]:
                                fails['T2'].append((case, root, p, mug, k))
                # T3: what the dirt at p+1 is owed to
                charge = {}
                for mug, n in M1.items():
                    if not n[4]: continue
                    owe = [k for k in n[3] if gut(T1, k)[1] >= gut(T1, mug)[0]]
                    kinds = set()
                    for k in owe:
                        if k == mug: kinds.add('self')
                        elif k not in M1: kinds.add('not a member')
                        elif k not in M0 or M0[k][1] != M1[k][1]: kinds.add('pushed in the pass')
                        elif fall(M1[k][2]): kinds.add('fell in the pass')
                        else: kinds.add('unchanged')
                    for kd in kinds: inc('T3 dirty owed to: ' + kd)
                    if kinds == {'unchanged'}: fails['T3same'].append((case, root, p + 1, mug, owe))
                    inc('T3 dirty members at a start >= 2')
                    if owe: charge[mug] = max(owe, key=lambda k: M1[k][1] if k in M1 else -1)
                # T4: stuck = dirty at p+1 with entry and callees the same as at p
                stuck = {}
                for mug, n in M1.items():
                    m = M0.get(mug)
                    if m and m[1] == n[1] and n[4] and not fall(n[2]) and n[3] == m[3]:
                        stuck[mug] = stuck_prev.get(mug, (p + 1, 0))[0], stuck_prev.get(mug, (p + 1, 0))[1] + 1
                for mug, (st0, ln) in stuck_prev.items():
                    if mug not in stuck:
                        n = M1.get(mug); m = M0.get(mug)
                        why = ('culled' if n is None or n[1] != m[1] else 'clean' if not n[4] else
                               'entry fell' if fall(n[2]) else 'callees changed' if n[3] != m[3] else '?')
                        runs_m.append((ln, why, case, root, st0, mug))
                last = starts[-1][1]
                for mug in stuck:
                    n = M1[mug]
                    owe = [k for k in n[3] if gut(T1, k)[1] >= gut(T1, mug)[0]]
                    tr = all(k != mug and (k not in last or last[k][1] != M1.get(k, (0, -1))[1]) for k in owe)
                    inc('T4 stuck starts owed only to transient callees' if tr else
                        'T4 stuck starts owed to a callee on the stack until the end or to itself')
                    if tr:
                        ln = tstuck_prev.get(mug, 0) + 1; tstuck[mug] = ln
                        tmax[0] = max(tmax[0], (ln, case, root, p + 1, mug))
                tstuck_prev = {m: tstuck[m] for m in tstuck if m in stuck}; tstuck.clear()
                stuck_prev = stuck
                if stuck:
                    if lrun == 0: lstart = p + 1
                    lrun += 1
                elif lrun:
                    runs_l.append((lrun, 'no member stuck', case, root, lstart)); lrun = 0
                # E / Ec: positions = members at p by DFS number
                if s == 0: charge_prev = {}
                def dset(chg, x): return {m for m, k in chg.items() if k == x}
                for cand in ('E', 'Ec'):
                    verdict = None
                    for mug, m in sorted(M0.items(), key=lambda x: x[1][1]):
                        n = M1.get(mug)
                        if n is None or n[1] != m[1] or fall(n[2]): verdict = 'fall'; break
                        a, b = dset(charge_prev, mug), dset(charge, mug)
                        if a == b: continue
                        if cand == 'E': verdict = 'fall' if b < a else 'rise'
                        else: verdict = 'fall' if len(b) < len(a) else 'rise' if len(b) > len(a) else None
                        if verdict: break
                    if verdict != 'fall': fails[cand].append((case, root, p, verdict))
                charge_prev = charge
                # P2
                if s + 2 < len(starts):
                    _, M2, _ = starts[s + 2]
                    inc('P2 pairs')
                    fellA = False; verdict = None
                    for mug, m in sorted(M0.items(), key=lambda x: x[1][1]):
                        n1, n2 = M1.get(mug), M2.get(mug)
                        gone = n1 is None or n1[1] != m[1] or n2 is None or n2[1] != m[1]
                        if gone or fall(n1[2]) or fall(n2[2]):
                            fellA = True
                            if verdict is None: verdict = 'fall'
                            continue
                        if verdict is None and m[4] != n2[4]: verdict = 'fall' if m[4] else 'rise'
                    if not fellA: fails['P2A'].append((case, root, p))
                    if verdict != 'fall': fails['P2D'].append((case, root, p, verdict))
            for mug, (st0, ln) in stuck_prev.items():
                runs_m.append((ln, 'loop ended', case, root, st0, mug))
            if lrun: runs_l.append((lrun, 'loop ended', case, root, lstart))
            for k, v in sw.items(): switches.append((v, len(starts), case, k))
    for k in sorted(c): print(k, c[k])
    for k, v in fails.items():
        print('fails of', k + ':', len(v))
        for x in v[:(10 ** 6 if verbose else 4)]: print('   ', x)
    print('T4 longest run of consecutive starts at which one member is stuck owing only to transient callees:', tmax[0])
    h = {}
    for x in switches: h[x[0]] = h.get(x[0], 0) + 1
    print('T7 members that changed callees with the same entry:', len(switches), 'by number of such changes', dict(sorted(h.items())))
    for x in sorted(switches, key=lambda x: x[:2], reverse=True)[:(20 if verbose else 3)]: print('   ', x)
    for name, rs in (('T4 per member', runs_m), ('T4 per loop (some member)', runs_l)):
        h = {}
        for r in rs: h[r[0]] = h.get(r[0], 0) + 1
        e = {}
        for r in rs: e[r[1]] = e.get(r[1], 0) + 1
        print(name + ': runs', len(rs), 'lengths', dict(sorted(h.items())), 'ended by', e)
        for r in sorted(rs, key=lambda x: x[0], reverse=True)[:(20 if verbose else 3)]: print('   ', r)

v = '-v' in sys.argv
analyse([p for p in sys.argv[1:] if p != '-v'], v)
