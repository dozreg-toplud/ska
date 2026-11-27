"""Writes lemmas/Compiler/CompStraightMapOps.lean: the gate `rewrite-op` of
the map path of `+to-straight` on one op of each of the 25 tags
(`tsm_op_<tag>`) and on any op (`tsm_op`), and the gate `rewrite-fin` on each
terminator (`tsm_fin_<tag>`, `tsm_fin`), from one template each.  Run from
formalization/: python3 tools/gen/tsmops.py"""
OPS = [
    ('imm', '(n : Noun) (d : Nat)', 'n d'), ('mov', '(s d : Nat)', 's d'),
    ('inc', '(s d : Nat)', 's d'), ('con', '(h t d : Nat)', 'h t d'),
    ('hed', '(s d : Nat)', 's d'), ('tal', '(s d : Nat)', 's d'),
    ('cel', '(p : Nat)', 'p'), ('lob', '(p : Nat)', 'p'), ('equ', '(l r : Nat)', 'l r'),
    ('hsp', '(n : Nat) (f : Noun)', 'n f'), ('hse', '(n : Nat) (f : Noun)', 'n f'),
    ('hdp', '(n p : Nat) (f : Noun)', 'n p f'), ('hde', '(n p : Nat) (f : Noun)', 'n p f'),
    ('hmp', '(a : Bell) (v : List Nat) (f : Noun)', 'a v f'),
    ('hme', '(a : Bell) (v : List Nat) (f : Noun)', 'a v f'),
    ('hcp', '(n f : Noun)', 'n f'), ('hce', '(n f : Noun)', 'n f'),
    ('spy', '(e p d : Nat)', 'e p d'), ('nok', '(u f d : Nat)', 'u f d'),
    ('cal', '(a : Bell) (v : List Nat) (d : Nat)', 'a v d'),
    ('caf', '(a : Bell) (v : List Nat) (d : Nat) (n : Ring)', 'a v d n'),
    ('cam', '(a : Bell) (v : List Nat) (d : Nat) (k : Noun)', 'a v d k'),
    ('csl', '(a : Bell) (s d : Nat)', 'a s d'),
    ('csf', '(a : Bell) (s d : Nat) (n : Ring)', 'a s d n'),
    ('csm', '(a : Bell) (s d : Nat) (k : Noun)', 'a s d k'),
]
TAGS = 'Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti'
out = ['''import lemmas.Compiler.CompStraightMap

/-!
# The map path of `+to-straight`: `rewrite-op` and `rewrite-fin`

Written by `tools/gen/tsmops.py` (README Gaps 20).  In a core whose `rer`
renames by `f` and keeps `gen` (`MapCoreS`), `rewrite-op` on each of the 25
op tags is `renPole f` with `gen` kept (`tsm_op_<tag>`, `tsm_op`), as
`rewriteOp_stateless` of the model; `rewrite-fin` on each terminator is
`chaseFin bs f` (`tsm_fin_<tag>`, `tsm_fin`), as `rewriteFin_stateless`:
the registers through `rer`, the branch jumps through `rewrite-jump`, the
hop through `rewrite-hop`, `%bom` through `+chase`.  `%lti` falls into the
last case (`%bom`, under `%toss`) and crashes, as the model's `none`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The hypotheses on a core `[tsCoreBat [G R]]` of the map path: the
stateless `rer`, `layer2`, the bunt of the units of `rewrite-args`, the
blocks `bs`. -/
structure MapCoreS (bs : TreapMap mugF Blob) (f : Nat → Nat) (G R : Noun) : Prop where
  hrer : RerS f G R
  hL : slot? 0x7fffffff R = some layer2
  hU : ∀ J, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (A 0)
  hB : slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)

''']
for tag, binders, args in OPS:
    out.append(f'''theorem tsm_op_{tag} {{bs : TreapMap mugF Blob}} {{rn : Nat → Nat}} {{G R : Noun}} (hc : MapCoreS bs rn G R)
    {binders} :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.{tag} {args})) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn (Pole.{tag} {args}))) G) := by
  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => {{ lhs; arg 2; unfold tsmOpBody }}
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  simp [nock_exec, Pole.toNoun, renPole, Tag.{tag}, hra, hrer, hpa, hp]
''')
cases = '\n'.join(f'  | {tag} {args} => exact tsm_op_{tag} hc {args}' for tag, _, args in OPS)
out.append(f'''/-- **`rewrite-op`** on any op: `renPole rn op`, `gen` kept. -/
theorem tsm_op {{bs : TreapMap mugF Blob}} {{rn : Nat → Nat}} {{G R : Noun}} (hc : MapCoreS bs rn G R) (op : Pole) :
    nock (C tsmOpBody (C (Pole.toNoun op) (C tsCoreBat (C G R)))) tsmOpBody
      = some (C (Pole.toNoun (renPole rn op)) G) := by
  cases op with
{cases}
''')
PRE = '''  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerS at hrer
  have hp := tsm_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsm_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsm_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
'''
GEN = '''  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha HX ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja HX ⊢
  generalize tsmHopBody = HB at hh hha HX ⊢
'''
SIMP = 'simp [nock_exec, Termin.toNoun, chaseFin, ' + TAGS + ', hra, hrer, hpa, hp, hja, hj, hha, hh, HY]'
FINS = [
  ('clq', '(s : Nat) (z o : Jmp)', 's z o', 'zo'), ('eqq', '(l r : Nat) (z o : Jmp)', 'l r z o', 'zo'),
  ('brn', '(s : Nat) (z o : Jmp)', 's z o', 'zo'), ('brz', '(s : Nat) (z o : Jmp)', 's z o', 'zo'),
  ('hop', '(t : Jmp)', 't', 't'), ('jmp', '(a : Bell) (v : List Nat)', 'a v', ''),
  ('jmf', '(a : Bell) (v : List Nat) (n : Ring)', 'a v n', ''), ('jsp', '(a : Bell) (s : Nat)', 'a s', ''),
  ('jsf', '(a : Bell) (s : Nat) (n : Ring)', 'a s n', ''), ('don', '(s : Nat)', 's', ''),
]
for tag, binders, args, kind in FINS:
    if kind == 'zo':
        body = PRE + '''  have HX := And.intro (hj z) (hj o)
  have HY := True.intro
''' + GEN + '''  obtain ⟨hz, ho⟩ := HX
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    ''' + SIMP.replace(', HY]', ', hz, ho, ez, eo]')
    elif kind == 't':
        body = PRE + '''  have HX := hh t
  have HY := True.intro
''' + GEN + '''  cases et : chase bs false t <;> rw [et] at HX <;>
    ''' + SIMP.replace(', HY]', ', HX, et]')
    else:
        body = PRE + '''  have HX := True.intro
  have HY := True.intro
''' + GEN.replace(' HX ⊢', ' ⊢') + '  ' + SIMP.replace(', HY]', ']')
    out.append(f'''theorem tsm_fin_{tag} {{bs : TreapMap mugF Blob}} {{rn : Nat → Nat}} {{G R : Noun}} (hc : MapCoreS bs rn G R)
    {binders} :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.{tag} {args})) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.{tag} {args})).map fun t => C (Termin.toNoun t) G := by
{body}
''')
open('lemmas/Compiler/CompStraightMapOps.lean', 'w').write('\n'.join(out) + '\nend Compiler\nend Formalization\n')
