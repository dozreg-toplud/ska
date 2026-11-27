"""Writes lemmas/Compiler/CompStraightMapPre.lean: the pushes of `+to-straight`
with the noun `PX` of `proxies` as a parameter (README Gaps 20).  The lemmas
whose proof does not read `proxies` are copied from CompStraightN.lean with
`tsS5N`, `tsS7N`, `tsCoreStN` replaced by `tsS5P PX`, `tsS7P PX`,
`tsCoreStP PX` (every replacement asserts its count); pushes 1 to 5 are copied
with `cond` a cell (`proxies` is `&`).  Run from formalization/:
python3 tools/gen/tsmpre.py"""
import re

SRC = 'lemmas/Compiler/CompStraightN.lean'
OUT = 'lemmas/Compiler/CompStraightMapPre.lean'
src = open(SRC).read()


def lemma(name):
    """The text of `theorem name` up to the next blank line followed by a doc
    comment, a theorem or a section header."""
    m = re.search(r'(/-- [^\n]*(?:\n(?!/--)[^\n]*)*?\n)?theorem ' + re.escape(name) + r' .*?(?=\n\n(?:/--|theorem|/-!|noncomputable|def))',
                  src, re.S)
    assert m, name
    return m.group(0)


def rep(text, old, new, count):
    n = text.count(old)
    assert n == count, (old, n, count)
    return text.replace(old, new)


# Pushes 1 to 5 with `cond` a cell: `proxies` is `&`.
pre1 = lemma('tsn_pre1')
pre1 = rep(pre1, 'theorem tsn_pre1 ', 'theorem tsnp_pre1 ', 1)
pre1 = rep(pre1, '(hcd : slot? 254 G = some (A 0))', '(ca cb : Noun) (hcd : slot? 254 G = some (C ca cb))', 1)
pre1 = rep(pre1, 'tsS5N BN BN', 'tsS5P (A 0) BN BN', 1)
pre1 = rep(pre1, 'tsS5N,', 'tsS5P,', 1)
pre1 = rep(pre1, '**Pushes 1 to 5** on any need:', '**Pushes 1 to 5** on any need with `cond` a cell (`proxies` is `&`):', 1)

lay = lemma('tsn_r_layer1')
lay = rep(lay, 'theorem tsn_r_layer1 {ctx : Noun} (hc : CompIn ctx) (', 'theorem tsnp_r_layer1 {ctx : Noun} (hc : CompIn ctx) (PX ', 1)
lay = rep(lay, '(C (A 1) (C (C tsUnBat', '(C PX (C (C tsUnBat', 1)

pre2 = lemma('tsn_pre2')
pre2 = rep(pre2, 'theorem tsn_pre2 {ctx : Noun} (hc : CompIn ctx) (', 'theorem tsnp_pre2 {ctx : Noun} (hc : CompIn ctx) (PX ', 1)
pre2 = rep(pre2, 'tsn_r_layer1 hc BN', 'tsnp_r_layer1 hc PX BN', 1)
pre2 = rep(pre2, 'tsS5N BN', 'tsS5P PX BN', 1)
pre2 = rep(pre2, 'tsS7N BN', 'tsS7P PX BN', 2)
pre2 = rep(pre2, '[tsS5N, tsS7N, tsS0N]', '[tsS5P, tsS7P, tsS0N]', 1)

ren = lemma('tsn_ren')
ren = rep(ren, 'theorem tsn_ren {ctx : Noun} (hc : CompIn ctx) (', 'theorem tsnp_ren {ctx : Noun} (hc : CompIn ctx) (PX ', 1)
ren = rep(ren, 'tsS7N B', 'tsS7P PX B', 1)
ren = rep(ren, '[tsS0N, tsS7N, tsS5N]', '[tsS0N, tsS7P, tsS5P]', 1)

pre3 = lemma('tsn_pre3')
pre3 = rep(pre3, 'theorem tsn_pre3 {ctx : Noun} (hc : CompIn ctx) (', 'theorem tsnp_pre3 {ctx : Noun} (hc : CompIn ctx) (PX ', 1)
pre3 = rep(pre3, 'tsS7N BN', 'tsS7P PX BN', 1)
pre3 = rep(pre3, 'tsCoreStN SB', 'tsCoreStP PX SB', 1)
pre3 = rep(pre3, '[tsCoreStN, tsS0N, tsS5N, tsS7N, tsSampleN]', '[tsCoreStP, tsS0N, tsS5P, tsS7P, tsSampleN]', 1)

pre3n = lemma('tsn_pre3_nil')
pre3n = rep(pre3n, 'theorem tsn_pre3_nil {ctx : Noun} (hc : CompIn ctx) (', 'theorem tsnp_pre3_nil {ctx : Noun} (hc : CompIn ctx) (PX ', 1)
pre3n = rep(pre3n, 'tsS7N BN', 'tsS7P PX BN', 1)
pre3n = rep(pre3n, '[tsS0N, tsS5N, tsS7N, tsSampleN]', '[tsS0N, tsS5P, tsS7P, tsSampleN]', 1)

HEAD = '''import lemmas.Compiler.CompStraightMapTop

/-!
# The pushes of `+to-straight` with any `proxies`

Written by `tools/gen/tsmpre.py` (README Gaps 20).  The third push of the
gate is `proxies`, `?:(=(~ cond.gen) | &)`: `(A 1)` when the noun of `cond`
is `~` (`tsS5N`, `CompStraightN.lean`), `(A 0)` when it is a cell.  Here the
states with the noun `PX` of `proxies` as a parameter (`tsS5P`, `tsS7P`,
`tsCoreStP`), pushes 1 to 5 with `cond` a cell (`tsnp_pre1`), and the lemmas
of `CompStraightN.lean` that do not read `proxies`, copied with `PX`
(`tsnp_r_layer1`, `tsnp_pre2`, `tsnp_ren`, `tsnp_pre3`, `tsnp_pre3_nil`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The subject after the first five pushes, `proxies` being `PX`. -/
def tsS5P (PX B Bo S0 : Noun) (r0 : Nat) (INS : Noun) : Noun :=
  C (A r0) (C INS (C PX (C (C tsUnBat (C (A 0) (C Bo S0))) (C B S0))))

/-- The subject after `run`. -/
def tsS7P (PX B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) : Noun :=
  C RUN (C (A n) (tsS5P PX B Bo S0 r0 INS))

/-- The `|^` core. -/
noncomputable def tsCoreStP (PX SB REN B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) : Noun :=
  C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (tsS7P PX B Bo S0 r0 INS n RUN))))

theorem tsS5N_eq_P (B Bo S0 : Noun) (r0 : Nat) (INS : Noun) : tsS5N B Bo S0 r0 INS = tsS5P (A 1) B Bo S0 r0 INS := rfl

theorem tsCoreStN_eq_P (SB REN B Bo S0 : Noun) (r0 : Nat) (INS : Noun) (n : Nat) (RUN : Noun) :
    tsCoreStN SB REN B Bo S0 r0 INS n RUN = tsCoreStP (A 1) SB REN B Bo S0 r0 INS n RUN := rfl

/-! ## The pushes -/

'''

TAIL = '''
end Compiler
end Formalization
'''

open(OUT, 'w').write(HEAD + '\n\n'.join([pre1, lay, pre2, ren, pre3, pre3n]) + '\n' + TAIL)
print('wrote', OUT)
