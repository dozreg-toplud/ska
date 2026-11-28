"""Write lemmas/Compiler/CompSofNouns.lean: the arms that the push of `sof`
(`crDKc6`, step 6 of the direct call) slams, read from the pill (README
Gaps 19, item (f)): `+sound` (door arm 13654 of `comp.door`), `+sound-far`
(arm 5467 of `K`), `+need-soft` (arm 5466 of `K`); each arm with its gate
battery named.  Run from formalization/: python3 tools/gen/sofpush.py"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
from nouns import *
def core2bat(ax):
    b = bin(ax)[2:]; assert b[:2] == '10', ax
    return int('1' + b[2:], 2)
Kbat = ('R', 'nh290d8f32435a'); door = ('R', 'comp.door')
def cells(n):
    n = norm(n)
    return 0 if n[0] == 'A' else 1 + cells(n[1]) + cells(n[2])
out = []
def emit(name, arm, batax, where, at, doc):
    bat = slot(batax, arm)
    assert norm(arm)[0] == 'C'
    out.append('/-- The gate battery of %s (%d cells). -/' % (doc, cells(bat)))
    out.append('def %sBat : Noun :=\n  %s\n' % (name, lean(bat)))
    out.append('/-- The arm %s. -/' % doc)
    out.append('def %sArm : Noun :=\n  %s\n' % (name, lean(arm, sub=[('%sBat' % name, bat)])))
    out.append('theorem %s : slot? %d %s = some %sArm := by kernel_rfl\n' % (at, where[1], where[0], name))
snd = slot(13654, door)
assert lean(slot(2, snd)) == '(A 8)'
emit('snd', snd, 29, ('comp.door', 13654), 'comp_sound_at', '`+sound` (door arm `13654`)')
sf = slot(core2bat(5467), Kbat)
assert lean(slot(2, sf)) == '(A 7)'
emit('sf', sf, 109, ('compK', 5467), 'compK_sf', '`+sound-far` (arm `5467` of `K`)')
ns = slot(core2bat(5466), Kbat)
assert lean(slot(2, ns)) == '(A 8)'
emit('ns', ns, 29, ('compK', 5466), 'compK_ns', '`+need-soft` (arm `5466` of `K`)')
noe = slot(core2bat(5596), Kbat)
assert lean(slot(2, noe)) == '(A 8)'
emit('noe', noe, 29, ('compK', 5596), 'compK_noe', '`+need-ord-edit` (arm `5596` of `K`)')
cs = slot(core2bat(48047), Kbat)
assert lean(slot(2, cs)) == '(A 8)'
emit('cs', cs, 29, ('compK', 48047), 'compK_cs', '`+cell-sure` (arm `48047` of `K`)')
hdr = '''import lemmas.Compiler.CompPastLink

/-!
# The arms the push of `sof` slams (README Gaps 19, item (f))

Written by `tools/gen/sofpush.py` from the pill: `+sound` (door arm
`13654`, `(sound-far nom ned code.long-ska 3)`), `+sound-far` (arm `5467` of
`K`, behind its `%fast` hint), `+need-soft` (arm `5466` of `K`), `+need-ord-edit`
(arm `5596` of `K`), `+cell-sure` (arm `48047` of `K`), each with
its gate battery and the kernel fact of where it sits.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

'''
open('lemmas/Compiler/CompSofNouns.lean', 'w').write(hdr + '\n'.join(out) + '\nend Compiler\nend Formalization\n')
print('cells: snd %d sf %d ns %d' % (cells(slot(29, snd)), cells(slot(109, sf)), cells(slot(29, ns))))
