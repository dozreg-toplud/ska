"""The nouns of the optimizer's arms for the pill link (`Compiler/OptLink*.lean`),
as Lean definitions, cut into named parts.

    tools/capped.sh -m 3G python3 tools/gen/optlink.py WHICH [OUTDIR]

writes `OUTDIR/<WHICH>.lean` (default `.`).  The optimizer is the core `optC`
at axis `31` of `cor` (battery `nh58984ad6cdbd`, payload `compK`); the
helpers are arms of `compTypes` (axis `3` of `compK`).  An arm of `optC` is
`[7 [8 [1 bunt] [1 body] [0 1]] hint]`, an arm of `compTypes` is
`[8 [1 bunt] [1 body] [0 1]]`.  WHICH is one of:

* `helpers`: the bodies and bunts of `+get-jmps` (`1502`), `+jmp-regs`
  (`175`), `+get-regs` (`84`), `+get-reg-safe-assignment` (`750`).
* `rub`: `+remove-useless-branching` (`363` of `optC`): its body, the gate of
  the `+rep:by` cut into the `?+` over the terminator and the rest.
* `rdc`: `+remove-dead-code` (`724` of `optC`): its body, the outer trap and
  the inner trap.
* `rev`: `+rev-cfg` (`732` of `optC`): its body, the gate of the `+rep:by`
  and the gate of the `+roll`.

Every part is checked against the pill when the Lean file states the arm as
a kernel fact; the script asserts the shape it cuts."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
WHICH = sys.argv[1]
OUT = sys.argv[2] if len(sys.argv) > 2 else '.'
cor = ('R', 'cor')
optc = slot(31, cor)
ctypes = ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana')))


def seq(n, k):
    """[a b c ... z] as a list of k elements, the last the rest."""
    out = []
    n = norm(n)
    for _ in range(k - 1):
        assert n[0] == 'C', n
        out.append(norm(n[1]))
        n = norm(n[2])
    out.append(n)
    return out


def emit(f, defs):
    """defs: list of (name, noun, doc), smallest first; later ones name
    the earlier ones."""
    subs = []
    for name, n, doc in defs:
        if doc is not False:
            if doc:
                f.write('/-- %s -/\n' % doc)
            f.write('def %s : Noun :=\n  %s\n\n' % (name, lean(n, subs)))
        if norm(n)[0] == 'C':
            subs.insert(0, (name, n))


def ct_arm(ax):
    """bunt and body of an arm of compTypes"""
    a = norm(slot(ax, ctypes))
    e, b, rest = seq(a, 3)
    assert e == ('A', 8)
    one, bunt = seq(b, 2)
    assert one == ('A', 1)
    ob, z = seq(rest, 2)
    oneb, body = seq(ob, 2)
    assert oneb == ('A', 1) and z == ('C', ('A', 0), ('A', 1)), z
    return bunt, body


def opt_arm(ax):
    """bunt, body and hint of an arm of optC"""
    a = norm(slot(ax, optc))
    s, g, hint = seq(a, 3)
    assert s == ('A', 7)
    bunt, body = ct_arm_of(g)
    return bunt, body, hint


def ct_arm_of(a):
    e, b, rest = seq(a, 3)
    assert e == ('A', 8)
    one, bunt = seq(b, 2)
    assert one == ('A', 1)
    ob, z = seq(rest, 2)
    oneb, body = seq(ob, 2)
    assert oneb == ('A', 1) and z == ('C', ('A', 0), ('A', 1)), z
    return bunt, body


defs = []
if WHICH == 'helpers':
    for nm, ax, doc in [('gj', 1502, '`+get-jmps`'), ('jr', 175, '`+jmp-regs`'),
                        ('gr', 84, '`+get-regs`'), ('gs', 750, '`+get-reg-safe-assignment`')]:
        bunt, body = ct_arm(ax)
        defs.append((nm + 'Bunt', bunt, 'The sample bunt of %s.' % doc))
        defs.append((nm + 'Body', body, 'The gate body of %s (arm `%d` of `compTypes`).' % (doc, ax)))
elif WHICH == 'rub':
    bunt, body, hint = opt_arm(363)
    # body = [8 REPDOOR [9 2 [10 [6 [7 [0 3] [8 [1 GB] [1 GATE] [0 1]]]] [0 2]]]]
    _, repdoor, slam = seq(body, 3)
    _, two, ed = seq(slam, 3)
    _, e6, z2 = seq(ed, 3)
    six, mk = seq(e6, 2)
    _, z3, mk2 = seq(mk, 3)
    _, gb1, gate1, z1 = seq(mk2, 4)
    gbunt = norm(gb1)[2]
    gate = norm(gate1)[2]
    # gate = [8 SW REST]
    _, sw, rest = seq(gate, 3)
    defs += [
        ('rubSw', sw, 'The `?+` over the terminator: `[epilogue new-fin]`.'),
        ('rubRest', rest, 'The new flag and the `+put:by` of the new block.'),
        ('rubGate', gate, 'The gate of the `+rep:by` of `+remove-useless-branching`.'),
        ('rubGBunt', gbunt, 'The sample bunt of that gate, `[[0 *blob] | ~]`.'),
        ('rubBody', body, 'The gate body of `+remove-useless-branching`.'),
        ('rubHint', hint, 'Its `%fast` hint.'),
    ]
elif WHICH == 'rdc':
    bunt, body, hint = opt_arm(724)
    # body = [8 [1 0] [8 [1 0] [8 [1 TRAP] [9 2 [0 1]]]]]
    _, _, b1 = seq(body, 3)
    _, _, b2 = seq(b1, 3)
    _, trapq, kick = seq(b2, 3)
    trap = norm(trapq)[2]
    # TRAP = [6 TEST [0 14] [8 GOT [8 R CONT]]]
    _, test, done, t1 = seq(trap, 4)
    _, got, t2 = seq(t1, 3)
    _, r, cont = seq(t2, 3)
    # R = [8 FLOP [7 [10 [30 GASFIN] [0 1]] [8 [1 0] [8 [1 INNER] [9 2 [0 1]]]]]]
    _, flop, r1 = seq(r, 3)
    _, ed, r2 = seq(r1, 3)
    _, ax30, _ = seq(ed, 3)
    gasfin = norm(ax30)[2]
    _, _, r3 = seq(r2, 3)
    _, innerq, _ = seq(r3, 3)
    inner = norm(innerq)[2]
    defs += [('rdcInner', inner, 'The inner trap of `+remove-dead-code`, over the reversed body.'),
             ('rdcGasFin', gasfin, '`(~(gas in saw) (get-regs fin.b))`.'),
             ('rdcCont', cont, 'The put of the new block and the next turn of the outer trap.'),
             ('rdcGot', got, '`(~(got by blocks) i.rev-topo)`.'),
             ('rdcTrap', trap, 'The outer trap of `+remove-dead-code`, over `rev-topo`.'),
             ('rdcBody', body, 'The gate body of `+remove-dead-code`.'),
             ('rdcBunt', bunt, 'Its sample bunt.'), ('rdcHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'rev':
    bunt, body, hint = opt_arm(732)
    # body = [8 REPDOOR [9 2 [10 [6 [7 [0 3] [8 [1 GB] [[1 GATE] [0 1]]]]] [0 2]]]]
    _, repdoor, slam = seq(body, 3)
    _, two, ed = seq(slam, 3)
    _, e6, z2 = seq(ed, 3)
    six, mk = seq(e6, 2)
    _, z3, mk2 = seq(mk, 3)
    _, gb1, gate1, z1 = seq(mk2, 4)
    gate = norm(gate1)[2]
    # GATE = [6 HAS [8 ROLL [9 2 [10 [6 [JMPS [7 [0 3] [8 [[1 0 0] [0 13]] [[1 RG] [0 1]]]]]] [0 2]]]] [0 13]]
    _, has, yes, no = seq(gate, 4)
    _, rolld, rs = seq(yes, 3)
    _, two2, ed2 = seq(rs, 3)
    _, e62, z22 = seq(ed2, 3)
    _, smp = seq(e62, 2)
    jmps, mkr = seq(smp, 2)
    _, z4, mkr2 = seq(mkr, 3)
    _, rb, rg1, z5 = seq(mkr2, 4)
    rgate = norm(rg1)[2]
    defs += [('revRGate', rgate, 'The gate of the `+roll` over the jumps: `(~(add ja acc) o1 o)`.'),
             ('revGate', gate, 'The gate of the `+rep:by` of `+rev-cfg`.'),
             ('revBody', body, 'The gate body of `+rev-cfg`.'),
             ('revBunt', bunt, 'Its sample bunt.'), ('revHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'bb':
    bunt, body, hint = opt_arm(2942)
    # body = [8 [1 0] [8 [1 0] [8 [1 0] [7 [8 [1 TRAP] [9 2 [0 1]]] [0 2]]]]]
    _, _, b1 = seq(body, 3)
    _, _, b2 = seq(b1, 3)
    _, _, b3 = seq(b2, 3)
    _, run, _ = seq(b3, 3)
    _, trapq, _ = seq(run, 3)
    trap = norm(trapq)[2]
    # TRAP = [7 [0 1] [7 [10 [30 PUT] [0 1]] [7 [[0 6] ROLL] [[[0 2] [0 6]] [0 7]]]]]
    _, _, t1 = seq(trap, 3)
    _, edput, t2 = seq(t1, 3)
    _, a30, _ = seq(edput, 3)
    put = norm(a30)[2]
    _, pr, _ = seq(t2, 3)
    _, roll = seq(pr, 2)
    # ROLL = [8 ROLLARM [9 2 [10 [6 [JMPS MK]] [0 2]]]]
    _, rolld, rs = seq(roll, 3)
    _, _, ed2 = seq(rs, 3)
    _, e62, _ = seq(ed2, 3)
    _, smp = seq(e62, 2)
    jmps, mkr = seq(smp, 2)
    _, _, mkr2 = seq(mkr, 3)
    _, rb, rg1, _ = seq(mkr2, 4)
    rgate = norm(rg1)[2]
    defs += [('bbRGate', rgate, 'The gate of the `+roll` over the jumps: skip a label in `saw`, else `dfs-buc`.'),
             ('bbJmps', jmps, '`(get-jmps fin:(~(got by blocks) o))`.'),
             ('bbPut', put, '`(~(put in saw) o)`.'),
             ('bbTrap', trap, 'The trap `dfs-buc` of `+bb-topo`.'),
             ('bbBody', body, 'The gate body of `+bb-topo`.'),
             ('bbBunt', bunt, 'Its sample bunt.'), ('bbHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'rh':
    bunt, body, hint = opt_arm(4)
    # body = [7 [0 1] [8 ROLLCALL FLAG]]
    _, _, b1 = seq(body, 3)
    _, rollcall, flag = seq(b1, 3)
    # ROLLCALL = [8 ROLLARM [9 2 [10 [6 [[0 59] [7 [0 3] [8 [1 BUNT] [[1 GATE] [0 1]]]]]] [0 2]]]]
    _, rolld, rs = seq(rollcall, 3)
    _, _, ed = seq(rs, 3)
    _, e6, _ = seq(ed, 3)
    _, smp = seq(e6, 2)
    lst, mk = seq(smp, 2)
    _, _, mk2 = seq(mk, 3)
    _, gb1, g1, _ = seq(mk2, 4)
    gate = norm(g1)[2]
    # GATE = [6 HAS [0 13] [8 [0 12] [8 GOT [8 [1 0] [8 [1 TRAP] [9 2 [0 1]]]]]]]
    _, has, keep, rest = seq(gate, 4)
    _, _, r1 = seq(rest, 3)
    _, got, r2 = seq(r1, 3)
    _, _, r3 = seq(r2, 3)
    _, trapq, _ = seq(r3, 3)
    trap = norm(trapq)[2]
    # TRAP = [7 [0 1] [6 TESTHOP HOPBR DONE]]
    _, _, t1 = seq(trap, 3)
    _, testhop, hopbr, done = seq(t1, 4)
    # HOPBR = [8 [0 239] [8 GETJA [6 [5 [1 0] [0 2]] [0 0] [6 TEST1 MERGE DONE2]]]]
    _, _, h1 = seq(hopbr, 3)
    _, getja, h2 = seq(h1, 3)
    _, _, _, h3 = seq(h2, 4)
    _, test1, merge, done2 = seq(h3, 4)
    # MERGE = [7 [10 [2043 PUTSAW] [0 1]] [8 GOT1 [8 SEG KICK]]]
    _, edsaw, m1 = seq(merge, 3)
    _, m2, m3 = seq(m1, 3)
    got1 = m2
    _, seg, kick = seq(m3, 3)
    # SEG = [8 [0 2030] [8 [0 12] [8 [0 58] [8 [1 SEGT] [9 2 [0 1]]]]]]
    _, _, s1 = seq(seg, 3)
    _, _, s2 = seq(s1, 3)
    _, _, s3 = seq(s2, 3)
    _, segtq, _ = seq(s3, 3)
    segt = norm(segtq)[2]
    defs += [('rhSegT', segt, 'The trap of the segment: the moves of the hop\'s arguments in front of the body.'),
             ('rhSeg', seg, 'The segment of the merged block `b1`.'),
             ('rhDone', done, '`done`: the put of the block built so far at `o-new`.'),
             ('rhDone2', done2, '`done` under the pushes of `o1` and `pre-o1`.'),
             ('rhMerge', merge, 'The merge of `o1`: `saw`, `b1`, the segment and the next turn.'),
             ('rhGetJa', getja, '`(~(get ja rev) o1)`.'),
             ('rhTrap', trap, 'The trap of `+remove-hops` that follows the hops from `o-new`.'),
             ('rhGot', got, '`(~(got by blocks) o)`.'),
             ('rhGate', gate, 'The gate of the `+roll` over `topo`.'),
             ('rhBody', body, 'The gate body of `+remove-hops`.'),
             ('rhBunt', bunt, 'Its sample bunt.'), ('rhHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'rem':
    bunt, body, hint = opt_arm(2940)
    # body = [8 READERS [8 [1 BAT] [9 10 [0 1]]]]
    _, readers, r2 = seq(body, 3)
    _, batq, _ = seq(r2, 3)
    bat = norm(batq)[2]
    hop, mj = seq(bat, 2)
    main, jump = seq(mj, 2)
    hbunt, hbody = ct_arm_of(hop)
    jbunt, jbody = ct_arm_of(jump)
    # READERS = [6 ANYCALL REPCALL [1 0]]
    _, anycall, repcall, _ = seq(readers, 4)
    def slam_gate(call):
        # [8 DOOR [9 2 [10 [6 [7 [0 3] [8 [1 GB] [[1 GATE] [0 1]]]]] [0 2]]]]
        _, door, sl = seq(call, 3)
        _, _, ed = seq(sl, 3)
        _, e6, _ = seq(ed, 3)
        _, mk = seq(e6, 2)
        _, _, mk2 = seq(mk, 3)
        _, gb1, g1, _ = seq(mk2, 4)
        return norm(gb1)[2], norm(g1)[2]
    anyb, anyg = slam_gate(anycall)
    rdb, rdg = slam_gate(repcall)
    mainb, maing = slam_gate(main)
    # rdg = [8 [8 [1 [0 0]] [[1 PUT] [0 1]]] [7 [10 [29 ROLLFIN] [0 1]] ROLLBODY]]
    _, putmk, rd1 = seq(rdg, 3)
    _, _, pm2 = seq(putmk, 3)
    putg = norm(norm(pm2)[1])[2]
    _, ed29, rollbody = seq(rd1, 3)
    # ROLLBODY = [8 ROLLARM [9 2 [10 [6 [[0 486] [7 [0 3] [8 [BUNTF [[1 OPG] [0 1]]]]]]] [0 2]]]]
    _, _, rb1 = seq(rollbody, 3)
    _, _, rb2 = seq(rb1, 3)
    _, rb3, _ = seq(rb2, 3)
    _, rb4 = seq(rb3, 2)
    _, rb5 = seq(rb4, 2)
    _, _, rb6 = seq(rb5, 3)
    _, buntf, opg1, _ = seq(rb6, 4)
    opg = norm(opg1)[2]
    # HOP body: [8 GOT [6 T1 [6 T2 [6 LEVY [8 SUB [8 PASS KICK]] [0 14]] [0 14]] [0 14]]]
    _, hgot, h1 = seq(hbody, 3)
    _, _, h2, _ = seq(h1, 4)
    _, _, h3, _ = seq(h2, 4)
    _, levy, h4, _ = seq(h3, 4)
    _, sub, h5 = seq(h4, 3)
    _, passg, hkick = seq(h5, 3)
    # LEVY = [8 LEVYARM [9 2 [10 [6 [[0 12] [7 [0 3] [8 [1 0] [[1 LG] [0 1]]]]]] [0 2]]]]
    _, _, l1 = seq(levy, 3)
    _, _, l2 = seq(l1, 3)
    _, l3, _ = seq(l2, 3)
    _, l4 = seq(l3, 2)
    _, l5 = seq(l4, 2)
    _, _, l6 = seq(l5, 3)
    _, _, lg1, _ = seq(l6, 4)
    levyg = norm(lg1)[2]
    # SUB = [8 [1 0] [8 [0 12] [8 [0 124] [8 [1 SUBT] [9 2 [0 1]]]]]]
    _, _, s1 = seq(sub, 3)
    _, _, s2 = seq(s1, 3)
    _, _, s3 = seq(s2, 3)
    _, subtq, _ = seq(s3, 3)
    subt = norm(subtq)[2]
    # PASS = [8 [1 0] [[1 PB] [0 1]]]
    _, _, p1 = seq(passg, 3)
    ob, _ = seq(p1, 2)
    passb = norm(ob)[2]
    _, msw, mrest = seq(maing, 3)
    defs += [('remPutG', putg, 'The gate `put` of `readers`: `(~(put ju acc) r o)`.'),
             ('remOpG', opg, 'The gate of the `+roll` over `body.b` in `readers`.'),
             ('remBuntF', buntf, 'The sample of that gate, `[*pole acc]`, its bunt made by the mold `pole` (arm `2743` of `compTypes`).'),
             ('remRdG', rdg, 'The gate of the `+rep:by` that makes `readers`.'),
             ('remRdB', rdb, 'Its sample bunt.'),
             ('remAnyG', anyg, 'The test of the `+any:by`: an empty block with parameters that ends in a `%hop`.'),
             ('remAnyB', anyb, 'Its sample bunt.'),
             ('remReaders', readers, '`readers`.'),
             ('remLevyG', levyg, 'The gate of the `+levy` of `rewrite-hop`: no reader but `there.j`.'),
             ('remSubT', subt, 'The trap that makes `sub`.'),
             ('remPassB', passb, 'The body of the gate `pass`.'),
             ('remHopBody', hbody, 'The gate body of `rewrite-hop` (arm `4` of the `|^` core).'),
             ('remJumpBody', jbody, 'The gate body of `rewrite-jump` (arm `11` of the `|^` core).'),
             ('remSw', msw, 'The `?+` over the terminator in the gate of `$`: the new terminator.'),
             ('remRest', mrest, 'The new flag and the `+put:by` of the block with its new terminator.'),
             ('remMainG', maing, 'The gate of the `+rep:by` of `$` (arm `10` of the `|^` core).'),
             ('remMainB', mainb, 'Its sample bunt.'),
             ('remBat', bat, 'The battery of the `|^` core: `rewrite-hop`, `$`, `rewrite-jump`.'),
             ('remBody', body, 'The gate body of `+remove-empty-middle`.'),
             ('remBunt', bunt, 'Its sample bunt.'), ('remHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'oo':
    bunt, body, hint = opt_arm(180)
    # body = [8 TOPO [8 REV [7 [0 1] [8 [7 [0 1] [8 [1 LOOP] [9 2 [0 1]]]] AFTER]]]]
    _, topo, b1 = seq(body, 3)
    _, rev, b2 = seq(b1, 3)
    _, _, b3 = seq(b2, 3)
    _, run, after = seq(b3, 3)
    _, _, r1 = seq(run, 3)
    _, loopq, _ = seq(r1, 3)
    loop = norm(loopq)[2]
    _, _, ahint = opt_arm(725)
    _, _, thint = opt_arm(23)
    defs += [('ooAliasHint', ahint, 'The `%fast` hint of `+alias`.'),
             ('ooTrimHint', thint, 'The `%fast` hint of `+trim-trace-hints`.')]
    defs += [('ooLoop', loop, 'The structural loop of `+optimize-once`: the three passes, and `+bb-topo` and `+rev-cfg` again after a change.'),
             ('ooAfter', after, '`+alias`, `+trim-trace-hints`, `+remove-dead-code` and the three passes once more.'),
             ('ooBody', body, 'The gate body of `+optimize-once`.'),
             ('ooBunt', bunt, 'Its sample bunt.'), ('ooHint', hint, 'Its `%fast` hint.')]
else:
    raise SystemExit('unknown ' + WHICH)
with open(os.path.join(OUT, WHICH + '.lean'), 'w') as f:
    emit(f, defs)
print('ok')
