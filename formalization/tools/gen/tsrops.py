"""Writes lemmas/Compiler/CompStraightRunOps.lean: the map path of
`+to-straight` with the state `[re-gen m]` (`run` `|`): `rewrite-jump`,
`rewrite-hop` (`tsr_jmp`, `tsr_hop`), the gate `rewrite-op` on each of the 25
tags (`tsr_op_<tag>`, `tsr_op`) and `rewrite-fin` on each terminator
(`tsr_fin_<tag>`, `tsr_fin`).  A copy of `tsmops.py` (track I, stateless)
where each `=^` is one step of the model's `RM`: the proof cases on the
result of each step in the Hoon's order.  Run from formalization/:
python3 tools/gen/tsrops.py"""
import sys

# (tag, binders, args, steps): a step is (kind, field) with kind `rr` (one
# `rer`), `par` (`rewrite-par`), `jmp` (`rewrite-jump`), `hop` (`rewrite-hop`).
OPS = [
    ('imm', '(n : Noun) (d : Nat)', 'n d', [('rr', 'd')]),
    ('mov', '(s d : Nat)', 's d', [('rr', 's'), ('rr', 'd')]),
    ('inc', '(s d : Nat)', 's d', [('rr', 's'), ('rr', 'd')]),
    ('con', '(h t d : Nat)', 'h t d', [('rr', 'h'), ('rr', 't'), ('rr', 'd')]),
    ('hed', '(s d : Nat)', 's d', [('rr', 's'), ('rr', 'd')]),
    ('tal', '(s d : Nat)', 's d', [('rr', 's'), ('rr', 'd')]),
    ('cel', '(p : Nat)', 'p', [('rr', 'p')]),
    ('lob', '(p : Nat)', 'p', [('rr', 'p')]),
    ('equ', '(l r : Nat)', 'l r', [('rr', 'l'), ('rr', 'r')]),
    ('hsp', '(n : Nat) (f : Noun)', 'n f', []),
    ('hse', '(n : Nat) (f : Noun)', 'n f', []),
    ('hdp', '(n p : Nat) (f : Noun)', 'n p f', [('rr', 'p')]),
    ('hde', '(n p : Nat) (f : Noun)', 'n p f', [('rr', 'p')]),
    ('hmp', '(a : Bell) (v : List Nat) (f : Noun)', 'a v f', [('par', 'v')]),
    ('hme', '(a : Bell) (v : List Nat) (f : Noun)', 'a v f', [('par', 'v')]),
    ('hcp', '(n f : Noun)', 'n f', []),
    ('hce', '(n f : Noun)', 'n f', []),
    ('spy', '(e p d : Nat)', 'e p d', [('rr', 'e'), ('rr', 'p'), ('rr', 'd')]),
    ('nok', '(u f d : Nat)', 'u f d', [('rr', 'u'), ('rr', 'f'), ('rr', 'd')]),
    ('cal', '(a : Bell) (v : List Nat) (d : Nat)', 'a v d', [('par', 'v'), ('rr', 'd')]),
    ('caf', '(a : Bell) (v : List Nat) (d : Nat) (n : Ring)', 'a v d n', [('par', 'v'), ('rr', 'd')]),
    ('cam', '(a : Bell) (v : List Nat) (d : Nat) (k : Noun)', 'a v d k', [('par', 'v'), ('rr', 'd')]),
    ('csl', '(a : Bell) (s d : Nat)', 'a s d', [('rr', 's'), ('rr', 'd')]),
    ('csf', '(a : Bell) (s d : Nat) (n : Ring)', 'a s d n', [('rr', 's'), ('rr', 'd')]),
    ('csm', '(a : Bell) (s d : Nat) (k : Noun)', 'a s d k', [('rr', 's'), ('rr', 'd')]),
]
FINS = [
    ('clq', '(s : Nat) (z o : Jmp)', 's z o', [('rr', 's'), ('jmp', 'z'), ('jmp', 'o')]),
    ('eqq', '(l r : Nat) (z o : Jmp)', 'l r z o', [('rr', 'l'), ('rr', 'r'), ('jmp', 'z'), ('jmp', 'o')]),
    ('brn', '(s : Nat) (z o : Jmp)', 's z o', [('rr', 's'), ('jmp', 'z'), ('jmp', 'o')]),
    ('brz', '(s : Nat) (z o : Jmp)', 's z o', [('rr', 's'), ('jmp', 'z'), ('jmp', 'o')]),
    ('hop', '(t : Jmp)', 't', [('hop', 't')]),
    ('jmp', '(a : Bell) (v : List Nat)', 'a v', [('par', 'v')]),
    ('jmf', '(a : Bell) (v : List Nat) (n : Ring)', 'a v n', [('par', 'v')]),
    ('jsp', '(a : Bell) (s : Nat)', 'a s', [('rr', 's')]),
    ('jsf', '(a : Bell) (s : Nat) (n : Ring)', 'a s n', [('rr', 's')]),
    ('don', '(s : Nat)', 's', [('rr', 's')]),
]
ONLY = sys.argv[1:]  # tags to emit (a test run); all when empty
TAGS = 'Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti'
CALL = {'rr': 'rr {x} {s}', 'par': 'rewritePar rr {x} {s}', 'jmp': 'rewriteJump rr bs {x} {s}',
        'hop': 'rewriteHop rr bs {x} {s}'}


def tree(steps, simp, depth=0, st='st', ind='  '):
    """Nested cases on the result of each step, `simp` at every leaf."""
    if depth == len(steps):
        return f'{ind}{simp.format(E=es(depth))}\n'
    kind, x = steps[depth]
    e = f'e{depth + 1}'
    call = CALL[kind].format(x=x, s=st)
    out = f'{ind}cases {e} : {call} with\n'
    out += f'{ind}| none =>\n' + f'{ind}  {simp.format(E=es(depth + 1))}\n'
    nst = f'st{depth + 1}'
    out += f'{ind}| some p{depth + 1} =>\n'
    out += f'{ind}  obtain ⟨_, {nst}⟩ := p{depth + 1}\n'
    out += tree(steps, simp, depth + 1, nst, ind + '  ')
    return out


def es(n):
    return ''.join(f', e{i + 1}' for i in range(n))


HEAD = '''import lemmas.Compiler.CompStraightRun

/-!
# `+to-straight` with `run` `|`: the jumps, `rewrite-op` and `rewrite-fin`

Written by `tools/gen/tsrops.py` (README Gaps 20).  In a core
`[tsCoreBat [(rmN st) R]]` whose `rer` is the model's stateful `rr`
(`MapCoreM`: `RerM`, `layer2`, the bunt of the units of `rewrite-args`, the
blocks `bs`), every gate returns the noun of the model's `RM` step on `st`
and the state it leaves: `rewrite-jump` and `rewrite-hop` (`tsr_jmp`,
`tsr_hop`: `+chase`, then `tsr_args`), `rewrite-op` on each of the 25 tags
(`tsr_op_<tag>`, `tsr_op`: `rewriteOp rr`) and `rewrite-fin` on each
terminator (`tsr_fin_<tag>`, `tsr_fin`: `rewriteFin rr bs`), each `=^` one
step in the Hoon's order.  The stateless copies are track I's
`CompStraightMapOps.lean` (`tools/gen/tsmops.py`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The hypotheses on a core `[tsCoreBat [(rmN st) R]]` of the map path with
the state, for every `st`: the stateful `rer` `rr`, `layer2`, the bunt of the
units of `rewrite-args`, the blocks `bs`. -/
structure MapCoreM (bs : TreapMap mugF Blob) (rr : Nat → RM (TreapMap mugF) Nat) (R : Noun) : Prop where
  hrer : RerM rr R
  hL : slot? 0x7fffffff R = some layer2
  hU : ∀ J (st : Nat × TreapMap mugF Nat), nock (C tsmArgBody (C J (C tsCoreBat (C (rmN st) R)))) tsmArgBuntF1
    = some (C (A 0) (rmN st))
  hB : ∀ G, slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)

/-- **`rewrite-args` with the state**, `tsr_args` with the bunt of the units
asked only at the states `rmN st` (a cell, which the kernel can reduce). -/
theorem tsr_argsM {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J (st : Nat × TreapMap mugF Nat), nock (C tsmArgBody (C J (C tsCoreBat (C (rmN st) R)))) tsmArgBuntF1
      = some (C (A 0) (rmN st))) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    nock (C tsmArgBody (C (Jmp.toNoun j) (C tsCoreBat (C (rmN st) R)))) tsmArgBody
      = (rewriteArgs rr j st).map fun p => C (Jmp.toNoun p.1) (rmN p.2) := by
  obtain ⟨args, there⟩ := j
  cases args with
  | nil =>
    conv => { lhs; arg 2; unfold tsmArgBody }
    simp [nock_exec, Jmp.toNoun, listNoun, rewriteArgs, pure, StateT.pure]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T (unitNoun A) (unitNoun A) rmN layer2 spinIn_layer2 tsmArgG1 (C (A 0) (rmN st))
      (C tsmArgBody (C (Jmp.toNoun ⟨a0 :: as, there⟩) (C tsCoreBat (C (rmN st) R))))
      (fun a s => argStep rr a s) (a0 :: as) st
      (fun a _ s => tsr_argG hrer _ _ _ a s)
    rw [spinM_mapM] at hSpin
    have hm : (fun a => match a with
        | Option.none => (pure Option.none : RM (TreapMap mugF) (Option Nat))
        | some r => do let r1 ← rr r; pure (some r1)) = argStep rr := by
      funext a; cases a <;> rfl
    have hu := hU (Jmp.toNoun ⟨a0 :: as, there⟩) st
    have hR : rewriteArgs rr ⟨a0 :: as, there⟩ st
        = (List.mapM (argStep rr) (a0 :: as) st).bind (fun p => some ((⟨p.1, there⟩ : Jmp), p.2)) := by
      unfold rewriteArgs
      rw [if_neg (List.cons_ne_nil _ _), ← hm]
      rfl
    rw [hR]
    cases em : List.mapM (argStep rr) (a0 :: as) st with
    | none =>
      rw [em] at hSpin
      simp only [Option.map_none] at hSpin
      rw [← listNoun_map_listN] at hSpin
      simp only [Jmp.toNoun, listNoun, List.map_cons] at hSpin hu
      conv => { lhs; arg 2; unfold tsmArgBody }
      generalize tsmArgBuntF1 = UB at hu ⊢
      generalize tsCoreBat = K at hSpin hu ⊢
      generalize tsmArgG1 = AG at hSpin ⊢
      generalize tsmArgBody = AB at hSpin hu ⊢
      generalize rmN st = GS at hSpin hu ⊢
      simp [nock_exec, Jmp.toNoun, listNoun, hL, hs1, spin.axis, hsp, hSpin, hu]
    | some q =>
      rw [em] at hSpin
      simp only [Option.map_some] at hSpin
      rw [← listNoun_map_listN, ← listNoun_map_listN] at hSpin
      simp only [Jmp.toNoun, listNoun, List.map_cons] at hSpin hu
      conv => { lhs; arg 2; unfold tsmArgBody }
      generalize tsmArgBuntF1 = UB at hu ⊢
      generalize tsCoreBat = K at hSpin hu ⊢
      generalize tsmArgG1 = AG at hSpin ⊢
      generalize tsmArgBody = AB at hSpin hu ⊢
      generalize rmN st = GS at hSpin hu ⊢
      simp [nock_exec, Jmp.toNoun, listNoun, hL, hs1, spin.axis, hsp, hSpin, hu]

theorem rewriteJump_eq (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    rewriteJump rr bs j st = (chase bs true j).bind fun j' => rewriteArgs rr j' st := by
  unfold rewriteJump
  simp only [liftR, bind, StateT.bind]
  cases chase bs true j <;> rfl

theorem rewriteHop_eq (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    rewriteHop rr bs j st = (chase bs false j).bind fun j' => rewriteArgs rr j' st := by
  unfold rewriteHop
  simp only [liftR, bind, StateT.bind]
  cases chase bs false j <;> rfl

'''

JMP = '''/-- **`rewrite-{name}` with the state**: `(rewrite-args (chase {flag} j))`. -/
theorem tsr_{short} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}} (bs : TreapMap mugF Blob) (hrer : RerM rr R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J (st : Nat × TreapMap mugF Nat), nock (C tsmArgBody (C J (C tsCoreBat (C (rmN st) R)))) tsmArgBuntF1
      = some (C (A 0) (rmN st)))
    (hB : ∀ G, slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    nock (C {body} (C (Jmp.toNoun j) (C tsCoreBat (C (rmN st) R)))) {body}
      = ({model} rr bs j st).map fun p => C (Jmp.toNoun p.1) (rmN p.2) := by
  have hL' : slot? 0x1ffffffff (C tsCoreBat (C (rmN st) R)) = some layer2 := by simp [nock_exec, hL]
  have hY := (tsm_core_l2 (G := rmN st) hL).2
  have hch := ch_gate bs {br} (C tsCoreBat (C (rmN st) R)) (hB _) hL' hY j
  rw [show loob {br} = A {lb} from rfl] at hch
  obtain ⟨h1519, h21⟩ := tsm_core_arms (rmN st) R
  rw [{model}_eq]
  cases e : chase bs {br} j with
  | none =>
    rw [e] at hch
    generalize tsCoreBat = K at hch h1519 h21 ⊢
    conv => {{ lhs; arg 2; unfold {body} }}
    simp [nock_exec, h1519, h21, tsChaseArm, hch, loob]
  | some j' =>
    rw [e] at hch
    have ha := tsr_argsM hrer hL hU j' st
    generalize tsCoreBat = K at hch h1519 h21 ha ⊢
    conv => {{ lhs; arg 2; unfold {body} }}
    simp [nock_exec, h1519, h21, tsChaseArm, hch, ha, loob]

'''

out = [HEAD]
out.append(JMP.format(name='jump', short='jmp', flag='&', body='tsmJmpBody', model='rewriteJump', br='true',
                      lb='0'))
out.append(JMP.format(name='hop', short='hop', flag='|', body='tsmHopBody', model='rewriteHop', br='false',
                      lb='1'))

OPPRE = '''  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  conv => { lhs; arg 2; unfold tsmOpBody }
  generalize tsCoreBat = K at hra hrer hp hpa ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
'''
for tag, binders, args, steps in OPS:
    if ONLY and tag not in ONLY:
        continue
    simp = (f'simp [nock_exec, Pole.toNoun, Tag.{tag}, hra, hrer, hpa, hp, rewriteOp, bind, StateT.bind, pure, '
            'StateT.pure{E}]')
    body = OPPRE + tree(steps, simp)
    out.append(f'''theorem tsr_op_{tag} {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}}
    (hc : MapCoreM bs rr R) {binders} (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun (Pole.{tag} {args})) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr (Pole.{tag} {args}) st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
{body}''')
if not ONLY:
    cases = '\n'.join(f'  | {tag} {args} => exact tsr_op_{tag} hc {args} st' for tag, _, args, _ in OPS)
    out.append(f'''/-- **`rewrite-op` with the state** on any op: the model's `rewriteOp rr`. -/
theorem tsr_op {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}} (hc : MapCoreM bs rr R)
    (op : Pole) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmOpBody (C (Pole.toNoun op) (C tsCoreBat (C (rmN st) R)))) tsmOpBody
      = (rewriteOp rr op st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  cases op with
{cases}

''')

FINPRE = '''  have hra := ts_rer_at
  have hrer := hc.hrer
  unfold RerM at hrer
  have hp := tsr_par hc.hrer hc.hL
  have hpa := tsmPar_at
  have hj := tsr_jmp bs hc.hrer hc.hL hc.hU hc.hB
  have hja := tsmJmp_at
  have hh := tsr_hop bs hc.hrer hc.hL hc.hU hc.hB
  have hha := tsmHop_at
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hra hrer hp hpa hj hja hh hha ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmJmpBody = JB at hj hja ⊢
  generalize tsmHopBody = HB at hh hha ⊢
'''
for tag, binders, args, steps in FINS:
    if ONLY and tag not in ONLY:
        continue
    simp = (f'simp [nock_exec, Termin.toNoun, {TAGS}, hra, hrer, hpa, hp, hja, hj, hha, hh, rewriteFin, bind, '
            'StateT.bind, pure, StateT.pure{E}]')
    body = FINPRE + tree(steps, simp)
    out.append(f'''theorem tsr_fin_{tag} {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}}
    (hc : MapCoreM bs rr R) {binders} (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.{tag} {args})) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.{tag} {args}) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
{body}''')

if not ONLY:
    out.append(f'''theorem tsr_fin_bom_none {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}}
    (hc : MapCoreM bs rr R) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.bom Option.none)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.bom Option.none) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  conv => {{ lhs; arg 2; unfold tsmFinBody }}
  generalize tsCoreBat = K
  simp [nock_exec, Termin.toNoun, unitNoun, rewriteFin, pure, StateT.pure, {TAGS}]

theorem tsr_fin_bom_some {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}}
    (hc : MapCoreM bs rr R) (x : Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.bom (some x))) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.bom (some x)) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  obtain ⟨hL', hY⟩ := tsm_core_l2 (G := rmN st) hc.hL
  have ht := ch_gate bs true (C tsCoreBat (C (rmN st) R)) (hc.hB _) hL' hY ⟨[], x⟩
  rw [show loob true = A 0 from rfl] at ht
  simp only [Jmp.toNoun, listNoun] at ht
  have h21 := (tsm_core_arms (rmN st) R).2
  conv => {{ lhs; arg 2; unfold tsmFinBody }}
  generalize tsCoreBat = K at ht h21 ⊢
  cases et : chase bs true ⟨[], x⟩ <;> rw [et] at ht <;>
    simp [nock_exec, Termin.toNoun, Jmp.toNoun, listNoun, unitNoun, rewriteFin, liftR, bind, StateT.bind, pure,
      StateT.pure, {TAGS}, h21, tsChaseArm, ht, et]

theorem tsr_fin_lti {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}}
    (hc : MapCoreM bs rr R) (n s : Nat) (z o : Jmp) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.lti n s z o)) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs (Termin.lti n s z o) st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  have hx := tsm_chase_cell (hc.hB (rmN st)) hc.hL (A 0) (A s) (C (Jmp.toNoun z) (Jmp.toNoun o))
  have h21 := (tsm_core_arms (rmN st) R).2
  conv => {{ lhs; arg 2; unfold tsmFinBody }}
  generalize tsCoreBat = K at hx h21 ⊢
  simp [nock_exec, Termin.toNoun, rewriteFin, {TAGS}, h21, tsChaseArm, hx]

/-- **`rewrite-fin` with the state** on any terminator: the model's
`rewriteFin rr bs`, a crash where it is `none`. -/
theorem tsr_fin {{bs : TreapMap mugF Blob}} {{rr : Nat → RM (TreapMap mugF) Nat}} {{R : Noun}} (hc : MapCoreM bs rr R)
    (fin : Termin) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmFinBody (C (Termin.toNoun fin) (C tsCoreBat (C (rmN st) R)))) tsmFinBody
      = (rewriteFin rr bs fin st).map fun p => C (Termin.toNoun p.1) (rmN p.2) := by
  cases fin with
''' + '\n'.join(f'  | {tag} {args} => exact tsr_fin_{tag} hc {args} st' for tag, _, args, _ in FINS) + '''
  | bom o =>
    cases o with
    | none => exact tsr_fin_bom_none hc st
    | some x => exact tsr_fin_bom_some hc x st
  | lti n s z o => exact tsr_fin_lti hc n s z o st

''')
open('lemmas/Compiler/CompStraightRunOps.lean', 'w').write(''.join(out) + 'end Compiler\nend Formalization\n')
