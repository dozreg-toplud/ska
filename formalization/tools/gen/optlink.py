"""The nouns of the optimizer's arms for the pill link (`Compiler/OptLink*.lean`),
as Lean definitions, cut into named parts.

    tools/capped.sh -m 3G python3 tools/gen/optlink.py WHICH [OUTDIR]

writes `OUTDIR/<WHICH>.lean` (default `.`).  The optimizer is the core `optC`
at axis `31` of `cor` (battery `nh6e49f3724ff1`, payload `compK`); the
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
* `bb`, `rh`, `rem`: `+bb-topo`, `+remove-hops`, `+remove-empty-middle`.
* `oo`: `+optimize-once` (`180`): the structural loop and the rest `ooAfter`.
* `ooa`: `ooAfter` cut at each `=^` and `=.` (`ooR1` to `ooR12`, `ooFin`).
* `opt`: `+optimize` (`2941`): its trap and the call of `+switch-chains`.
* `switch`: `+switch-chains` (`182`): its gates `test-of`, `chain-of`,
  `plain-of`, `plains-of`, `cases`, `tree`, `uses`, `nex` and the walk, cut
  at each test and branch the proofs step through.

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
elif WHICH == 'ooa':
    # ooAfter cut at each =^ and =. of +optimize-once after the loop
    bunt, body, hint = opt_arm(180)
    _, _, b1 = seq(body, 3)
    _, _, b2 = seq(b1, 3)
    _, _, b3 = seq(b2, 3)
    _, _, after = seq(b3, 3)
    def tail7(n):
        s, a, b = seq(n, 3)
        assert s == ('A', 7), s
        return a, b
    e251, r = tail7(after)
    p43, r1 = tail7(r)
    pieces = [('ooR1', r1)]
    # R1 = [7 [0 1] [8 CALL R2]]
    _, r = tail7(r1)
    _, call, r2 = seq(r, 3)
    pieces.append(('ooR2', r2))
    # R2 = [7 E [7 P R3]]
    _, r = tail7(r2)
    _, r3 = tail7(r)
    pieces.append(('ooR3', r3))
    _, r4 = tail7(r3)
    pieces.append(('ooR4', r4))
    _, r5 = tail7(r4)
    pieces.append(('ooR5', r5))
    _, r6 = tail7(r5)
    pieces.append(('ooR6', r6))
    _, r7 = tail7(r6)
    pieces.append(('ooR7', r7))
    _, r = tail7(r7)
    _, _, r8 = seq(r, 3)
    pieces.append(('ooR8', r8))
    _, r = tail7(r8)
    _, r9 = tail7(r)
    pieces.append(('ooR9', r9))
    _, r = tail7(r9)
    _, _, r10 = seq(r, 3)
    pieces.append(('ooR10', r10))
    _, r = tail7(r10)
    _, r11 = tail7(r)
    pieces.append(('ooR11', r11))
    _, r = tail7(r11)
    _, _, r12 = seq(r, 3)
    pieces.append(('ooR12', r12))
    _, r = tail7(r12)
    _, fin = tail7(r)
    pieces.append(('ooFin', fin))
    docs = {'ooR1': '`=^  f-alias=?  blocks.s  (alias n-args.s blocks.s rev topo)` and the rest.',
            'ooR2': 'The edit of `blocks.s` by the product of `+alias`, then the rest.',
            'ooR3': '`=.  topo  (skim topo ~(has by blocks.s))` and the rest.',
            'ooR4': '`=.  rev  (rev-cfg blocks.s (sy topo))` and the rest.',
            'ooR5': '`=.  blocks.s  (trim-trace-hints blocks.s topo rev)` and the rest.',
            'ooR6': '`=.  blocks.s  (remove-dead-code blocks.s (flop topo))` and the rest.',
            'ooR7': '`=^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)` and the rest.',
            'ooR8': 'The edit of `blocks.s` by the product of `+remove-hops`, then the rest.',
            'ooR9': '`=^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)` and the rest.',
            'ooR10': 'The edit of `blocks.s` by the product of `+remove-useless-branching`, then the rest.',
            'ooR11': '`=^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)` and the rest.',
            'ooR12': 'The edit of `blocks.s` by the product of `+remove-empty-middle`, then the rest.',
            'ooFin': '`[|(f-alias c-hops c-branch c-middle) s]`.'}
    for nm, n in reversed(pieces):
        defs.append((nm, n, docs[nm]))
    defs.append(('ooAfterCut', after, '`ooAfter` with its pieces named.'))
elif WHICH == 'opt':
    bunt, body, hint = opt_arm(2941)
    # body = [7 [10 [6 [8 [1 TRAP] [9 2 [0 1]]]] [0 1]] [10 [7 SW] [0 6]]]
    _, ed, sw0 = seq(body, 3)
    _, e6, _ = seq(ed, 3)
    _, run = seq(e6, 2)
    _, trapq, _ = seq(run, 3)
    trap = norm(trapq)[2]
    _, e7, _ = seq(sw0, 3)
    _, sw = seq(e7, 2)
    _, _, swhint = opt_arm(182)
    defs += [('optSwHint', swhint, 'The `%fast` hint of `+switch-chains`.')]
    defs += [('optTrap', trap, 'The trap of `+optimize`: `+optimize-once` until no change.'),
             ('optSw', sw, '`(switch-chains blocks.s)`.'),
             ('optBody', body, 'The gate body of `+optimize`.'),
             ('optBunt', bunt, 'Its sample bunt.'), ('optHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'uno':
    # +uno:by, arm 2 of by.battery: [8 [0 6] [[1 OUTER] [0 1]]]
    arm = norm(slot(2, ('R', 'by.battery')))
    _, s6, mk = seq(arm, 3)
    assert norm(s6) == ('C', ('A', 0), ('A', 6))
    o1, _ = seq(mk, 2)
    outer = norm(o1)[2]
    # OUTER = [8 [1 MEGBUNT] [[1 MEGGATE] [0 1]]]
    _, mb, mk2 = seq(outer, 3)
    megbunt = norm(mb)[2]
    g1, _ = seq(mk2, 2)
    meggate = norm(g1)[2]
    # MEGGATE = [8 [1 TRAP] [9 2 [0 1]]]
    _, tq, _ = seq(meggate, 3)
    trap = norm(tq)[2]
    defs += [('unoTrap', trap, 'The trap of `+uno:by`.'),
             ('unoMegGate', meggate, 'The body of the gate `|*  meg` that `+uno:by` makes: the trap, kicked.'),
             ('unoMegBunt', megbunt, 'Its sample bunt.'),
             ('unoOuter', outer, 'The body of the gate `|*  b=_a`: it makes the gate `|*  meg`.'),
             ('unoArm', arm, 'The arm `+uno:by` (axis `2` of the battery of `+by`).')]
elif WHICH == 'trim':
    bunt, body, hint = opt_arm(23)
    # BODY = [7 [0 1] [8 TRACE [8 UNSAFE [8 OPENED RUN]]]]
    _, _, b1 = seq(body, 3)
    _, trace, b2 = seq(b1, 3)
    _, unsafe, b3 = seq(b2, 3)
    _, opened, run = seq(b3, 3)
    # TRACE = [8 [1 TBUNT] [[1 TRACEB] [0 1]]]
    _, tb, tmk = seq(trace, 3)
    tbunt = norm(tb)[2]
    tg1, _ = seq(tmk, 2)
    traceb = norm(tg1)[2]
    # UNSAFE = [8 [1 [0 0]] [8 [1 OTRAP] [9 2 [0 1]]]]
    _, _, u1 = seq(unsafe, 3)
    _, otq, _ = seq(u1, 3)
    otrap = norm(otq)[2]
    # OTRAP = [6 [5 [1 0] [0 250]] [0 12] [8 OGOT [8 OROLL [8 [0 26] [8 [1 ITRAP] [9 2 [0 1]]]]]]]
    _, _, _, o1 = seq(otrap, 4)
    _, ogot, o2 = seq(o1, 3)
    _, oroll, o3 = seq(o2, 3)
    _, _, o4 = seq(o3, 3)
    _, itq, _ = seq(o4, 3)
    itrap = norm(itq)[2]
    # OROLL = [8 [9 ROLL L] [9 2 [10 [6 [GETJA [7 [0 3] [8 [1 RB] [[1 RGATE] [0 1]]]]]] [0 2]]]]
    _, _, rs = seq(oroll, 3)
    _, _, ed = seq(rs, 3)
    _, e6, _ = seq(ed, 3)
    _, smp = seq(e6, 2)
    getja, mk = seq(smp, 2)
    _, _, mk2 = seq(mk, 3)
    _, rb1, rg1, _ = seq(mk2, 4)
    rgate = norm(rg1)[2]
    rbunt = norm(rb1)[2]
    # RGATE = [8 UNOB [9 2 [10 [6 [7 [0 3] [8 [1 MXB] [[1 MXG] [0 1]]]]] [0 2]]]]
    _, unob, rg2 = seq(rgate, 3)
    _, _, ed = seq(rg2, 3)
    _, e6, _ = seq(ed, 3)
    _, mk = seq(e6, 2)
    _, _, mk2 = seq(mk, 3)
    _, mxb1, mxg1, _ = seq(mk2, 4)
    mxbunt = norm(mxb1)[2]
    mxg = norm(mxg1)[2]
    # ITRAP = [6 TEST END STEP]
    _, itest, iend, istep = seq(itrap, 4)
    # END = [7 [10 [252 UPD] [0 1]] NEXT]
    _, eed, enext = seq(iend, 3)
    _, e252, _ = seq(eed, 3)
    _, eupd = seq(e252, 2)
    # EUPD = [6 FINT UNI [0 252]]
    _, fint, euni, _ = seq(eupd, 4)
    # STEP = [8 [0 12] [8 HINT [6 TEST NOHINT HINTC]]]
    _, _, s1 = seq(istep, 3)
    _, shint, s2 = seq(s1, 3)
    _, _, snoh, shc = seq(s2, 4)
    # NOHINT = [6 NCT SKIPK WIDEN]
    _, nct, skipk, widen = seq(snoh, 4)
    # HINTC = [8 GUT [6 [0 26] OPENK [6 LTE DELK DECK]]]
    _, hgut, h1 = seq(shc, 3)
    _, _, openk, closek = seq(h1, 4)
    _, lte, delk, deck = seq(closek, 4)
    # OPENED = [8 REPDOOR [9 2 [10 [6 [7 [0 3] [8 [1 OB] [[1 OG] [0 1]]]]] [0 2]]]]
    _, _, os1 = seq(opened, 3)
    _, _, ed = seq(os1, 3)
    _, e6, _ = seq(ed, 3)
    _, mk = seq(e6, 2)
    _, _, mk2 = seq(mk, 3)
    _, ob1, og1, _ = seq(mk2, 4)
    obunt = norm(ob1)[2]
    ogate = norm(og1)[2]
    # OGATE = [8 ROLLARM [9 2 [10 [6 [[0 230] [7 [0 3] [8 [BUNTF [[1 OPG] [0 1]]]]]]] [0 2]]]]
    _, _, og2 = seq(ogate, 3)
    _, _, ed = seq(og2, 3)
    _, e6, _ = seq(ed, 3)
    _, smp = seq(e6, 2)
    _, mk = seq(smp, 2)
    _, _, mk2 = seq(mk, 3)
    _, obuntf, opg1, _ = seq(mk2, 4)
    opg = norm(opg1)[2]
    # RUN = [8 RUNDOOR [9 2 [10 [6 [7 [0 3] [8 [1 RNB] [[1 RNG] [0 1]]]]] [0 2]]]]
    _, _, rn1 = seq(run, 3)
    _, _, ed = seq(rn1, 3)
    _, e6, _ = seq(ed, 3)
    _, mk = seq(e6, 2)
    _, _, mk2 = seq(mk, 3)
    _, rnb1, rng1, _ = seq(mk2, 4)
    rnbunt = norm(rnb1)[2]
    rngate = norm(rng1)[2]
    # RNGATE = [10 [6 [8 [9 SKIP L] [9 2 [10 [6 [[0 58] [7 [0 3] [8 [1 SB] [[1 SG] [0 1]]]]]] [0 2]]]]] [0 6]]
    _, r6, _ = seq(rngate, 3)
    _, sk = seq(r6, 2)
    _, _, sk1 = seq(sk, 3)
    _, _, ed = seq(sk1, 3)
    _, e6, _ = seq(ed, 3)
    _, smp = seq(e6, 2)
    _, mk = seq(smp, 2)
    _, _, mk2 = seq(mk, 3)
    _, sb1, sg1, _ = seq(mk2, 4)
    sbunt = norm(sb1)[2]
    sgate = norm(sg1)[2]
    defs += [('trTraceB', traceb, 'The body of the gate `trace`: the key of a trace hint op and whether it opens the hint.'),
             ('trTBunt', tbunt, 'Its sample bunt.'),
             ('trMaxG', mxg, 'The body of the gate `|=([k=key v=@ud w=@ud] (max v w))`.'),
             ('trMaxB', mxbunt, 'Its sample bunt.'),
             ('trUnoB', unob, '`(~(uno by acc) (~(gut by out) p *(map key @ud)))`: the gate `|*  meg` of `+uno:by`.'),
             ('trRGate', rgate, 'The gate of the `+roll` over the predecessors.'),
             ('trRBunt', rbunt, 'Its sample bunt.'),
             ('trGetJa', getja, '`(~(get ja rev) i.topo)`.'),
             ('trORoll', oroll, '`open`: the `+roll` over the predecessors.'),
             ('trOGot', ogot, '`(~(got by blocks) i.topo)`.'),
             ('trFinT', fint, '`!?=(?(%clq %eqq %brz %hop) -.fin.b)`.'),
             ('trEUni', euni, '`(~(uni in unsafe) ~(key by open))` at the end of a block.'),
             ('trEUpd', eupd, 'The `=?` of `unsafe` at the end of a block.'),
             ('trENext', enext, 'The next turn of the outer trap: `topo` and `out` edited.'),
             ('trIEnd', iend, 'The end of a block in the inner trap.'),
             ('trIHint', shint, '`(trace op)`.'),
             ('trNcT', nct, '`?=(pole-not-crashing -.op)`.'),
             ('trSkipK', skipk, '`$(body t.body)`.'),
             ('trWiden', widen, '`$(body t.body, unsafe (~(uni in unsafe) ~(key by open)))`.'),
             ('trINoHint', snoh, 'An op without key: `pole-not-crashing` or the unsafe keys widened.'),
             ('trHGut', hgut, '`(~(gut by open) key.u.hint 0)`.'),
             ('trOpenK', openk, '`$(body t.body, open (~(put by open) key.u.hint +(n)))`.'),
             ('trLte', lte, '`(lte n 1)`.'),
             ('trDelK', delk, '`$(body t.body, open (~(del by open) key.u.hint))`.'),
             ('trDecK', deck, '`$(body t.body, open (~(put by open) key.u.hint (dec n)))`.'),
             ('trIHintC', shc, 'An op with a key: its count opened or closed.'),
             ('trIStep', istep, 'A turn of the inner trap on an op.'),
             ('trITest', itest, '`?=(~ body)`.'),
             ('trITrap', itrap, 'The inner trap over the body of a block.'),
             ('trOTrap', otrap, 'The outer trap over `topo`.'),
             ('trOpg', opg, 'The gate of the `+roll` over the body in `opened`.'),
             ('trOBuntF', obuntf, 'Its sample, the bunt of `pole` made by its mold.'),
             ('trOGate', ogate, 'The gate of the `+rep:by` of `opened`.'),
             ('trOBunt', obunt, 'Its sample bunt.'),
             ('trSGate', sgate, 'The test of the `+skip`: a hint op whose key is not unsafe and is opened.'),
             ('trSBunt', sbunt, 'Its sample bunt.'),
             ('trRnGate', rngate, 'The gate of the `+run:by`: the body skipped.'),
             ('trRnBunt', rnbunt, 'Its sample bunt.'),
             ('trBody', body, 'The gate body of `+trim-trace-hints`.'),
             ('trBunt', bunt, 'Its sample bunt.'), ('trHint', hint, 'Its `%fast` hint.')]
elif WHICH == 'switch':
    bunt, body, hint = opt_arm(182)
    def dig(n, axes):
        for ax in axes:
            n = norm(slot(ax, n))
            assert n is not None
        return n
    def gate_of(g):
        # [8 [1 BUNT] [[1 BODY] [0 1]]]
        e, bq, mk = seq(g, 3)
        assert e == ('A', 8)
        b1, ctx = seq(mk, 2)
        assert ctx == ('C', ('A', 0), ('A', 1)), ctx
        return norm(bq)[2], norm(b1)[2]
    # BODY = [8 TOPO [8 REV [8 USES [7 [0 1] [8 TO [8 CH [7 [0 1] [8 PO [8 PS [7 [0 1]
    #        [8 CS [8 TR [8 [0 0xffe] [8 [1 0] [8 NEX [8 [1 WALK] [9 2 [0 1]]]]]]]]]]]]]]]]]
    _, topo, r = seq(body, 3)
    _, rev, r = seq(r, 3)
    _, uses, r = seq(r, 3)
    _, _, r = seq(r, 3)
    _, tog, r = seq(r, 3)
    _, chg, r = seq(r, 3)
    _, _, r = seq(r, 3)
    _, pog, r = seq(r, 3)
    _, psg, r = seq(r, 3)
    _, _, r = seq(r, 3)
    _, csg, r = seq(r, 3)
    _, trg, r = seq(r, 3)
    _, outi, r = seq(r, 3)
    _, donei, r = seq(r, 3)
    _, nex, r = seq(r, 3)
    _, walkq, _ = seq(r, 3)
    walk = norm(walkq)[2]
    _, tob = gate_of(tog)
    _, chb = gate_of(chg)
    _, pob = gate_of(pog)
    _, psb = gate_of(psg)
    _, csb = gate_of(csg)
    trbunt, trb = gate_of(trg)
    # USES = [8 PUTGATE [8 REPDOOR [9 2 [10 [6 [7 [0 3] [8 [1 RB] [[1 RG] [0 1]]]]] [0 2]]]]]
    putb = dig(uses, [6, 7, 2, 3])
    rb = dig(uses, [7, 7, 7, 13, 7, 6, 3])
    rg = dig(uses, [7, 7, 7, 13, 7, 7, 2, 3])
    # RG = [7 [10 [13 PARROLL] [0 1]] [7 [10 [13 FINROLL] [0 1]] BODYROLL]]
    opg = dig(rg, [7, 7, 7, 7, 13, 3, 7, 7, 2, 3])
    # test-of: [8 GOT [6 CLQ Y [1 0]]]
    toclq = dig(tob, [7, 6])
    toy = dig(tob, [7, 14])
    toyb = dig(toy, [7, 7, 14])
    toeqq = dig(toyb, [7, 14, 6])
    tobod = dig(toyb, [7, 14, 14, 14])
    tohm = dig(tobod, [7, 14])
    toh = dig(tohm, [6])
    tom = dig(tohm, [7, 6])
    tos = dig(tohm, [7, 7, 15, 15])
    toc = dig(tos, [14])
    tolth = dig(toc, [7, 14, 6])
    toeq = dig(toc, [7, 14, 14, 6])
    touses = dig(toc, [7, 14, 14, 14, 6])
    # plain-of: [8 GOT [6 EQQ [8 M REST] [1 0]]]
    poeqq = dig(pob, [7, 6])
    assert eqn(poeqq, toeqq)  # the test of `fin.b` in `plain-of` is `swTOEqq`
    pomt = dig(pob, [7, 14, 6, 7, 6, 3])
    poc = dig(pob, [7, 14, 7])
    # cases: [8 [1 0 0] [8 [1 TRAP] [9 2 [0 1]]]]
    cst = dig(csb, [7, 6, 3])
    cssg = dig(cst, [14, 7, 7, 13, 3, 7, 7, 2, 3])
    # tree
    trleaf = dig(trb, [14, 14])
    trsplit = dig(trb, [14, 15])
    trrec = dig(trsplit, [7, 7, 7, 14, 14])
    # nex: [8 ROLL [9 2 [10 [6 [KEYS [7 [0 3] [8 [1 0 0] [[1 G] [0 1]]]]]] [0 2]]]]
    nexg = dig(nex, [7, 7, 13, 3, 7, 7, 2, 3])
    # walk: [6 [5 [1 0] [0 0x3ffe]] [0 30] [6 HAS SKIP [8 CS [6 GTE4 [6 [3 [0 2]] TAG [0 0]] PLAIN]]]]
    whas = dig(walk, [15, 6])
    wcs = dig(walk, [15, 15, 6])
    wgte = dig(walk, [15, 15, 7, 6])
    wtag = dig(walk, [15, 15, 7, 14, 14])
    wplain = dig(walk, [15, 15, 7, 15])
    # TAG = [8 [0 8] [8 [0 0x33e] [8 [0 0x39e] [8 MIS [8 IDS [7 DONE [7 OUT [8 CAS [8 NODE TFIN]]]]]]]]]
    wtids = dig(wtag, [7, 7, 7, 7, 6])
    wtr = dig(wtag, [7, 7, 7, 7, 7])
    wtdel = dig(wtr, [7, 6, 13])
    wtcas = dig(wtr, [7, 7, 6])
    wtfin = dig(wtr, [7, 7, 7])
    # PLAIN = [8 PS [6 LTH4 SKIP [6 [3 [0 2]] PB [0 0]]]]
    wpb = dig(wplain, [7, 15, 14])
    wpr = dig(wpb, [7, 7, 7])
    wpdel = dig(wpr, [7, 6, 13])
    wpcas = dig(wpr, [7, 7, 6])
    wpned = dig(wpr, [7, 7, 7, 6])
    wpfin = dig(wpr, [7, 7, 7, 7])
    wpidt = dig(wpfin, [7, 6, 7, 7, 6, 3])
    wpnode = dig(wpfin, [7, 7, 7, 7])
    wpskg = dig(wpnode, [7, 7, 7, 6, 7, 7, 13, 3, 7, 7, 2, 3])
    defs += [('swPutB', putb, 'The body of the gate `put` of `uses`: `(~(put by acc) r +((~(gut by acc) r 0)))`.'),
             ('swOpG', opg, 'The gate of the `+roll` over `body.b` in `uses`.'),
             ('swRepG', rg, 'The gate of the `+rep:by` that makes `uses`.'),
             ('swRepB', rb, 'Its sample bunt.'),
             ('swUses', uses, '`uses`: how many times each register is mentioned.'),
             ('swTOClq', toclq, '`?=([%clq * [~ *] [~ *]] fin.b)` in `test-of`.'),
             ('swTOEqq', toeqq, '`?=([%eqq * * [~ *] [~ *]] fin.yb)` in `test-of`.'),
             ('swTOH1', dig(toh, [15]), 'The unit `h` of `test-of` when the first op is no `%hed`.'),
             ('swTOM1', dig(tom, [15]), 'The unit `m` of `test-of` when the first op is no `%imm`.'),
             ('swTOH', toh, 'The unit `h` of `test-of`: the `%hed` of the two ops.'),
             ('swTOM', tom, 'The unit `m` of `test-of`: the `%imm` of the two ops.'),
             ('swTOLth', tolth, '`(lth c (bex 31))` in `test-of`.'),
             ('swTOEq', toeq, 'The test of the registers of the `%eqq` in `test-of`.'),
             ('swTOUses', touses, 'The test of the `uses` of `d` and `r` in `test-of`.'),
             ('swTOC', toc, '`test-of` from `c`: its tests and the test it returns.'),
             ('swTOS', tos, '`test-of` from `=(s.u.h s.fin.b)`.'),
             ('swTOHM', tohm, '`test-of` from `h`.'),
             ('swTOBod', tobod, '`test-of` from `bod`.'),
             ('swTOYb', toyb, '`test-of` from `yb`.'),
             ('swTOY', toy, '`test-of` after the test of `fin.b`.'),
             ('swTOB', tob, 'The body of the gate `test-of`.'),
             ('swCHB', chb, 'The body of the gate `chain-of`.'),
             ('swPOMT', pomt, 'The trap of `m` in `plain-of`: the first `%imm` into `l` or `r`.'),
             ('swPOC', poc, '`plain-of` from `?~  m`.'),
             ('swPOB', pob, 'The body of the gate `plain-of`.'),
             ('swPSShape', dig(psb, [7, 15, 3, 7, 14, 6]), '`?=([[%imm *] ~] body.nb)` in `plains-of`.'),
             ('swPSB', psb, 'The body of the gate `plains-of`.'),
             ('swCSSG', cssg, 'The gate of the `+sort` in `cases`: `(lth c.a c.b)`.'),
             ('swCST', cst, 'The trap of `cases`.'),
             ('swCSB', csb, 'The body of the gate `cases`.'),
             ('swTRLeaf', trleaf, 'The leaf of `tree`: `[~[[%imm c r]] [%eqq d r [~ hit] [~ mis]] ids out]`.'),
             ('swTRRec', trrec, 'The two recursions of `tree` and the node it returns.'),
             ('swTRSplit', trsplit, '`tree` from `haf`.'),
             ('swTRB', trb, 'The body of the gate `tree`.'),
             ('swTRBunt', trbunt, 'Its sample bunt.'),
             ('swNexG', nexg, 'The gate of the `+roll` of `nex`.'),
             ('swNex', nex, '`nex`: the first label that no block has.'),
             ('swWHas', whas, '`(~(has in done) i.topo)`.'),
             ('swWCs', wcs, '`(chain-of i.topo)`.'),
             ('swWGte', wgte, '`(gte (lent cs) 4)`.'),
             ('swWTIds', wtids, 'The labels `ids` of a tagged chain.'),
             ('swWTDel', wtdel, '`(roll ids |=([o=@uwoo acc=_out] (~(del by acc) o)))` of a tagged chain.'),
             ('swWTCas', wtcas, '`cas` of a tagged chain.'),
             ('swWTFin', wtfin, 'A tagged chain from `node`: the tree, the head, the next turn.'),
             ('swWTR', wtr, 'A tagged chain from `done`.'),
             ('swWTag', wtag, 'A tagged chain, after `?>  ?=(^ cs)`.'),
             ('swWPDel', wpdel, '`(roll old |=([o=@uwoo acc=_out] (~(del by acc) o)))` of a plain chain.'),
             ('swWPCas', wpcas, '`cas` of a plain chain.'),
             ('swWPNed', wpned, '`ned` of a plain chain.'),
             ('swWPIdT', wpidt, 'The trap of `ids` of a plain chain: new labels from `nex`.'),
             ('swWPSkG', wpskg, 'The test of the `+skip` of a plain chain: an `%imm` into the register of the first test.'),
             ('swWPNode', wpnode, 'A plain chain from `node`: the tree, the head, the next turn.'),
             ('swWPFin', wpfin, 'A plain chain from `ids`.'),
             ('swWPR', wpr, 'A plain chain from `done`.'),
             ('swWPB', wpb, 'A plain chain, after `?>  ?=(^ ps)`.'),
             ('swWPlain', wplain, 'The plain branch of the walk: `ps` and its tests.'),
             ('swWalk', walk, 'The walk of `+switch-chains` over `topo`.'),
             ('swBodyCut', body, 'The gate body of `+switch-chains`.')]
else:
    raise SystemExit('unknown ' + WHICH)
with open(os.path.join(OUT, WHICH + '.lean'), 'w') as f:
    emit(f, defs)
print('ok')
