"""The nouns of `+sure-of`, `+inter1-to-inter2` and of the gate `member` of
`+compile-scc-in`, cut into named parts, as Lean definitions.

    tools/capped.sh -m 3G python3 tools/gen/member.py OUTDIR

writes `OUTDIR/sureof.lean` (arm `0x2bae` of `K`, `+sure-of`, and arm
`0xbbbb`, `+inter1-to-inter2`) and `OUTDIR/member.lean` (the gate at axis
`358182910` of `K`).  Each part is named inside the larger ones (by
structural equality), so that the arm in the pill is a `kernel_rfl` fact
about the definitions.  The parts are found by walking the Nock: `seq(n, k)`
takes a right-nested list of `k` elements."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
OUT = sys.argv[1] if len(sys.argv) > 1 else '.'
K = ('C', ('R', 'nh3d89e8d5f4f5'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))


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
        subs.insert(0, (name, n))


# +inter1-to-inter2 and +sure-of
i2arm = slot(0xbbbb, K)
_, i2core, i2hint = seq(i2arm, 3)
_, i2bunt, i2b = seq(i2core, 3)
i2body = norm(norm(i2b[1])[2])
_, _, i2pair = seq(i2body, 3)
i2rep, i2turn = norm(i2pair[1]), norm(i2pair[2])
# the rep: [8 PUSH [9 2 [10 [6 [7 [0 3] [8 [[1 0] [0 48]] [[1 GATE] [0 1]]]]] [0 2]]]]
_, _, slam = seq(i2rep, 3)
_, _, e10 = seq(slam, 3)                    # [10 [6 X] [0 2]]
_, e6, _ = seq(e10, 3)
samf = norm(norm(e6)[2])                    # [6 X] -> X
_, _, mk = seq(samf, 3)                     # [7 [0 3] MK]
_, _, gpair = seq(mk, 3)                    # [8 BUNT [[1 GATE] [0 1]]]
i2gate = norm(norm(norm(gpair[1])[2]))
gs = seq(i2gate, 4)                         # [6 T Y N]
gs2 = seq(gs[3], 4)                         # [6 AIC [0 13] [8 [1 TRAP] [9 2 0 1]]]
_, trapc, _ = seq(gs2[3], 3)
i2trap = norm(norm(trapc)[2])
soarm = slot(0x2bae, K)
_, sobunt, sob = seq(soarm, 3)
sobody = norm(norm(sob[1])[2])

with open(os.path.join(OUT, 'sureof.lean'), 'w') as f:
    emit(f, [
        ('i2Trap', i2trap, 'The trap of the gate of the `+rep:in`: the look at `axe` made sure in `new`.'),
        ('i2Gate', i2gate, 'The gate of the `+rep:in` over `lok.sure.intr`.'),
        ('i2Rep', i2rep, 'The `+rep:in` over `lok.sure.intr`.'),
        ('i2Turn', i2turn, 'The `+turn` over `fork.intr`.'),
        ('i2Body', i2body, 'The gate body of `+inter1-to-inter2`.'),
        ('i2Bunt', norm(i2bunt)[2], 'Its sample bunt.'),
        ('i2Hint', i2hint, 'Its `%fast` hint.'),
        ('soBody', sobody, 'The gate body of `+sure-of`.'),
        ('soBunt', norm(sobunt)[2], 'Its sample bunt.'),
    ])

# member
marm = slot(358182910, K)
_, mcore, mhint = seq(marm, 3)
_, mbunt, mb = seq(mcore, 3)
mbody = norm(norm(mb[1])[2])
_, mdone, mtest = seq(mbody, 3)
_, _, memX, _ = seq(mtest, 4)
_, memComp, memR1 = seq(memX, 3)
_, _, r1 = seq(memR1, 3)
_, memInl, memR2 = seq(r1, 3)
r2 = seq(memR2, 3)[2]          # [7 [[0 4] 0 3] [8 [1 bunt] [7 E R3]]]
r2 = seq(r2, 3)[2]
_, gbunt, r2 = seq(r2, 3)
memR3 = seq(r2, 3)[2]
r3 = seq(memR3, 3)[2]
r3 = seq(r3, 3)[2]
_, memRes, memAfter = seq(r3, 3)
_, _, rsel = seq(memRes, 3)
_, _, memFinal, memShape = seq(rsel, 4)
f1 = seq(memFinal, 3)[2]       # [7 [0 1] [8 RUN F2]]
_, memRun, memF2 = seq(seq(f1, 3)[2], 3)
f2 = seq(memF2, 3)[2]          # [7 [[0 4] 0 3] [7 [0 1] [8 CS F3]]]
f2 = seq(f2, 3)[2]
_, memCs, memF3 = seq(seq(f2, 3)[2], 3)
f3 = seq(memF3, 3)[2]
f3 = seq(f3, 3)[2]             # [8 BAK [8 SUR TUPLE]]
_, memBak, f4 = seq(f3, 3)
_, memSur, memTuple = seq(f4, 3)
a1 = seq(memAfter, 3)[2]       # [7 [[0 4] 0 3] [7 [10 [8159 ..]] [8 WAS ..]]]
a1 = seq(a1, 3)[2]
_, _, a2 = seq(a1, 3)          # [8 WAS [8 SURK [7 PUT [8 MOVED [7 [0 1] [8 FIN PROD]]]]]]
_, memWas, a3 = seq(a2, 3)
_, memSurK, a4 = seq(a3, 3)
_, memPut, a5 = seq(a4, 3)
_, memMoved, a6 = seq(a5, 3)
_, _, a7 = seq(a6, 3)
_, finA, memProd = seq(a7, 3)
_, memSprev, psel = seq(memProd, 3)
_, _, memNew, memOld = seq(psel, 4)

finBodyN = norm(norm(norm(seq(seq(finA, 3)[1], 3)[2])[1])[2])

with open(os.path.join(OUT, 'member.lean'), 'w') as f:
    emit(f, [
        ('finBody', finBodyN, False),
        ('finArm', finA, False),
        ('cuBunt', norm(gbunt)[2], False),
        ('memShape', memShape, 'The branch of the shape passes (`?.  done`), not run on the final pass.'),
        ('memRun', memRun, '`(~(run comp gen) | nomm [%done ~] ~ ~)`.'),
        ('memCs', memCs, '`(~(collapse-shape comp gen) nex cape.less.b)`.'),
        ('memBak', memBak, '`(bake-need ned-final less.b)`.'),
        ('memSur', memSur, '`(sure-of [(need-to-ordered ned.sure.laz) lok.sure.laz] cape.less.b)`.'),
        ('memTuple', memTuple, '`[[(need-to-ordered ned.bak) laz ned-final bak o sur] gen]`.'),
        ('memF3', memF3, 'The `=^` of `+collapse-shape`, `bak`, `sur` and the tuple.'),
        ('memF2', memF2, 'The `=^` of the run, then `+collapse-shape` and the rest.'),
        ('memFinal', memFinal, 'The final pass: `mode.gen` set to `%run`, the run and the rest.'),
        ('memRes', memRes, 'The `!@` of `dedicated-shape-pass`: `?.  done` with the shape passes and the final pass.'),
        ('memWas', memWas, '`was`: `(~(get by sure.cache) b)`.'),
        ('memSurK', memSurK, '`sur`: `?:(&(keep ?=(^ was)) u.was sur)`.'),
        ('memPut', memPut, '`=.  sure.cache  (~(put by sure.cache) b sur)`.'),
        ('memMoved', memMoved, '`moved`: `!=(sur (fall was [%none ~]))`.'),
        ('memNew', memNew, 'The product when `map-local` has no straight of `b`.'),
        ('memOld', memOld, 'The product when `map-local` has a straight of `b`.'),
        ('memSprev', memSprev, '`s-previous`: `(~(get by map-local) b)`.'),
        ('memProd', memProd, 'After the push of `finish`: `s-previous` and the product.'),
        ('memAfter', memAfter, 'After the final pass: the `=^` of `res`, the `sure.cache` updates, the push of `finish`, the product.'),
        ('memR3', memR3, 'After the `=.  cache.gen  cache`: the final pass and the rest.'),
        ('memInl', memInl, '`(inlined b long-ska jets-hot cache)`.'),
        ('memR2', memR2, 'The `=^` of `+inlined`, the `=|` of `gen`, `=.  cache.gen  cache`.'),
        ('memR1', memR1, 'After the push of `comp`: `+inlined` and the rest.'),
        ('memComp', memComp, '`(comp scc long-ska jets-hot map-local top b)`.'),
        ('memBody', mbody, 'The gate body of `member`.'),
        ('memBunt', norm(mbunt)[2], 'Its sample bunt.'),
        ('memHint', mhint, 'Its `%fast` hint.'),
    ])
# +inlined: the bunt and the hint of its arm (the body stays a slot of the pill)
iarm = slot(0x5dde, K)
_, icore, ihint = seq(iarm, 3)
_, ibunt, _ = seq(icore, 3)
with open(os.path.join(OUT, 'inlined.lean'), 'w') as f:
    emit(f, [
        ('inlBunt', norm(ibunt)[2], 'The sample bunt of `+inlined`.'),
        ('inlHint', ihint, 'Its `%fast` hint.'),
    ])
print('ok')
