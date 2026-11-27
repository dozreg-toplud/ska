"""Writes lemmas/Compiler/CompShapeColBake.lean: the chain of the one-bell top
with the real bake (`CompSccSixBake.lean`, from `fin_gate_ts_B` to
`cu_gate_scc_one_six_q_B`) with `hT : TsAny` (`+to-straight` on every input,
`CompStraightRunIn.lean`) in place of `hT : TsOn Q`, and without the
hypothesis that the residual of the bake is a run (`hrun`, `BakeRunO`): each
theorem copied under the name `<name>_any`; then the top without `BakeRunO`.
Run from formalization/: python3 tools/gen/bakeany.py"""
import re

SRC = open('lemmas/Compiler/CompSccSixBake.lean').read()
NAMES = ['fin_gate_ts_B', 'fin_gate_finishLF_six_B', 'mem_gate_six_B', 'csi_gate_scc_one_m_six_B',
         'csi_gate_scc_one_f_six_B', 'cu_gate_scc_one_six_q_B']


def block(name):
    """The text of `theorem name` up to the next top-level item."""
    a = SRC.index(f'theorem {name} ')
    m = re.compile(r'\n(theorem|def|noncomputable def|example|/-!|/--|end ) ?').search(SRC, a + 1)
    return SRC[a:m.start() + 1]


def drop_binder(t, head):
    """Removes every binder `(head ...)` (balanced parentheses), with the
    blank it leaves."""
    while True:
        i = t.find('(' + head)
        if i < 0:
            return t
        d, j = 0, i
        while True:
            if t[j] == '(':
                d += 1
            elif t[j] == ')':
                d -= 1
                if d == 0:
                    break
            j += 1
        k = i
        while k > 0 and t[k - 1] == ' ':
            k -= 1
        if t[k - 1] == '\n' and t[j + 1] in '\n':
            t = t[:k - 1] + t[j + 1:]
        elif t[k - 1] == '\n' and t[j + 1:j + 3] == ' :':
            # the binder opened the line and the colon of the statement follows
            t = t[:k - 1] + t[j + 1:]
        else:
            t = t[:k] + (' ' if t[j + 1] not in ' \n' and t[k - 1] not in ' \n' else '') + t[j + 1:]


out = []
for name in NAMES:
    t = block(name)
    t = t.replace('(hT : TsOn Q)', '(hT : TsAny)')
    t = drop_binder(t, 'hrun : isRun')
    t = drop_binder(t, 'hbake : BakeRunO')
    t = t.replace('generalize bakeNeed nedF know = bak at hrun ⊢', 'generalize bakeNeed nedF know = bak')
    t = t.replace('simp only at hrun ⊢', 'try simp only')
    t = t.replace('hT ctx h7 g4 x o nedB (by rw [kc4, kc3]; exact hQ) hrun', 'hT ctx h7 g4 x o nedB')
    t = t.replace('\n          (hbake nex g1 nedF g2 hr hno) SURE\' hp]', ' SURE\' hp]')
    t = t.replace(' (hbake nex g1 nedF g2 hr hno)', '')
    t = re.sub(r' hrun\b(?![LN])', '', t)
    t = re.sub(r' hbake\b', '', t)
    t = t.replace('cu_gate_six Q hT ', 'cu_gate_six Q (tsOn_of_any Q hT) ')
    for n in NAMES:
        t = re.sub(rf'\b{n}\b', f'{n}_any', t)
    out.append(t)

HEAD = '''import lemmas.Compiler.CompShapeColNorm
import lemmas.Compiler.CompStraightRunIn

/-!
# The one-bell top with the real bake and no hypothesis on the bake

Written by `tools/gen/bakeany.py` (README Gaps 9).  `+to-straight` is
linked on every input need (`tsAny_holds`, `CompStraightRunIn.lean`: the
renaming path, the map path with proxies, and the map path with `run` `|`
through the state `[re-gen m]`).  So the chain of `CompSccSixBake.lean` from
`fin_gate_ts_B` to `cu_gate_scc_one_six_q_B` holds with `TsAny` in place of
`TsOn Q` and without the residual of `+bake-need` being a run (`BakeRunO`):
each theorem is copied as `<name>_any` with the hypothesis `hrun` (and
`hbake`) dropped.  The top **`cu_gate_scc_one_six_bake_all`** assumes the
state nouns, `SixOk`, `NoSelfCall` and `NoAx0` (`FolMade` in `_fol_all`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `TsAny` gives `TsOn Q` for every `Q`. -/
theorem tsOn_of_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (h : TsAny) : TsOn Q :=
  fun ctx h7 g x o ned _ _ => h ctx h7 g x o ned

'''

TAIL = '''/-- **The one-bell top on `SixOk` with the real bake**, nothing assumed on
`+shape-collapse`, on the bake or on `+to-straight`: the n-ary entry is
`finishLFB env nm (scOrdR p.1 cape) (Sock.mk cape DATA)`. -/
theorem cu_gate_scc_one_six_bake_all (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFB (S := CSet) (Map := TreapMap mugF) env nm (scOrdR p.1 cape) (Sock.mk cape DATA)).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_q_B_any (fun _ => True) tsAny_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls nm INL' hinl env hn hax (fun nex => scOrdR nex cape)
    (scAt_R env hn hax cape (normRun_six env hn)) (fun _ _ _ => trivial) FUNC V n hn' hax'
    (fun _ _ _ _ _ _ => trivial) hgot hv

/-- `cu_gate_scc_one_six_bake_all` on the nomms that `+fol-loop` makes
(`FolMade`). -/
theorem cu_gate_scc_one_six_bake_fol_all (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hf' : FolMade n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFB (S := CSet) (Map := TreapMap mugF) env nm (scOrdR p.1 cape) (Sock.mk cape DATA)).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_bake_all cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm
    INL' hinl env hn (folMade_noAx0 hf) FUNC V n hn' (folMade_noAx0 hf') hgot hv

/-- `%m01` of `tools/hoon/bakedump.hoon`: `[[0 2] [0 6] [0 7]]` on the bell
`[[| [& |]] [0 7 0]]` (the middle of the subject known, `7`). -/
def m01Nomm : Nomm := Nomm.cons (Nomm.n0 2) (Nomm.cons (Nomm.n0 6) (Nomm.n0 7))

/-- The cape `[| [& |]]`. -/
def capeM01 : Cape := Cape.cell Cape.no (Cape.cell Cape.yes Cape.no)

/- The model's final pass of `m01Nomm` (over `LS`, `FM`, in the environment
of the dumps): the `ord` is `[%this [%this %this]]`, the registers `[5 6 7]`;
`+bake-need` bakes the middle one and leaves `[5 7]`, not a run, so
`+to-straight` takes the map path with `run` `|` (`tsr_at`). -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none m01Nomm (CGoalL.done : CGoalL LS) [] gen0).bind fun p =>
    (shapeCol 64 p.1.laz capeM01).bind fun ord => (needOrdAllocRegs ord p.2).map fun q =>
      let b := bakeNeed q.1 (Sock.mk capeM01 (C (A 0) (C (A 7) (A 0))))
      (ord, b.2.length, flattenNeed q.1, flattenNeed b.1, isRun (flattenNeed b.1) ((flattenNeed b.1).headD 0) 0))
  = some (NeedOrd.pair NeedOrd.this (NeedOrd.pair NeedOrd.this NeedOrd.this), 1, [5, 6, 7], [5, 7], false)

/- The n-ary entry of the model with the bake succeeds there with two
arguments. -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none m01Nomm (CGoalL.done : CGoalL LS) [] gen0).bind fun p =>
    (finishLFB (S := LS) (Map := FM) envR m01Nomm ((shapeCol 64 p.1.laz capeM01).getD NeedOrd.none)
      (Sock.mk capeM01 (C (A 0) (C (A 7) (A 0))))).map fun st => st.nargs) = some 2

/-- **The top with the real bake on `%m01`** (a known middle, whose residual
is not a run): `m01Nomm` as the SCC's nomm and as the code's nomm, with no
hypothesis but the state nouns. -/
example (FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C capeM01.toNoun (C (A 0) (C (A 7) (A 0)))) FOL) NARY = some (A 0))
    (hnmap : IsMap mugF NARY) (hsmap : IsMap mugF SURE)
    (hcalls : NoSelfCall (C (C capeM01.toNoun (C (A 0) (C (A 7) (A 0)))) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C capeM01.toNoun (C (A 0) (C (A 7) (A 0)))) FOL) CODE INL m01Nomm INL') (env : CallEnv)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some m01Nomm.toNoun) :=
  cu_gate_scc_one_six_bake_all capeM01 (C (A 0) (C (A 7) (A 0))) FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls _ INL' hinl env rfl (by simp [m01Nomm, Bake.NoAx0]) FUNC V m01Nomm rfl
    (by simp [m01Nomm, Bake.NoAx0]) hgot hv

'''
open('lemmas/Compiler/CompShapeColBake.lean', 'w').write(
    HEAD + '\n'.join(out) + '\n' + TAIL + 'end Compiler\nend Formalization\n')
