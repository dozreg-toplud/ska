"""The `%done` member step with soft calls (README Gaps 21.17):

    python3 tools/gen/softmem.py > lemmas/Compiler/CompSccLoopSoftMemDone.lean

copies `mem_gate_done_R` (CompSccLoopMemDone.lean), `mem_done_stepStr`, `MemDoneCallStr`,
`memGate_done_realStr`, `memGate_done_KStr` (CompSccLoopStrGen.lean) with asserted replacements:
the run is `runLCS env snd ~` from `GenSf.ofGen gen0` (a `GenSf`), the pill's run gives
`genNoun g1.g x1` with `x1.soft = softMapNoun g1.soft` (the shape `CompRunAtXTS` gives), the
finish gate is `fin_gate_finishLFCS_BC` (with its hypothesis `hreq`), the straight is that of
`finishLFCS ... TreapMap.tap`, and the model is `cfgRealS r snd`."""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEM = os.path.join(HERE, '..', '..', 'lemmas', 'Compiler')


def block(path, start, end):
    s = open(os.path.join(LEM, path)).read()
    a = s.index(start)
    b = s.index(end, a + len(start)) if end else len(s)
    return s[a:b]


def rep(s, old, new, count=None):
    n = s.count(old)
    assert n >= 1, ('missing', old[:120])
    if count is not None:
        assert n == count, ('count', n, count, old[:120])
    return s.replace(old, new)


HREQ = ('(hreq : ∀ u sf3, coerceLazyLS nedF cape nex.th.there nex.laz ⟨g2, g1.soft⟩ = some (u, sf3) →\n'
        '      ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req)')

# ---------------------------------------------------------------- mem_gate_done_R
mg = block('CompSccLoopMemDone.lean', 'theorem mem_gate_done_R ', '\nend Compiler')
mg = rep(mg, 'theorem mem_gate_done_R ', 'theorem mem_gate_done_RS ', 1)
mg = rep(mg, '(env : CallEnv) (nex : NextL CSet) (g1 : Gen (TreapMap mugF))\n'
             '    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))',
         '(env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nex : NextL CSet) (g1 : GenSf (TreapMap mugF))\n'
         '    (hrunL : runLCS env snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0) = some (nex, g1))', 1)
mg = rep(mg, '= some (C nex.goal.toNoun (genNoun g1 x1)))', '= some (C nex.goal.toNoun (genNoun g1.g x1)))', 1)
mg = rep(mg, '(hs1 : x1.soft = A 0)', '(hs1 : x1.soft = softMapNoun g1.soft)', 1)
mg = rep(mg, '(hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))', '(hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2))', 1)
mg = rep(mg, '((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)\n    (sur : NeedOrd)',
         '((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)\n    ' + HREQ + '\n    (sur : NeedOrd)', 1)
mg = rep(mg, '(finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape',
         '(finishLFCS (S := CSet) (Map := TreapMap mugF) env snd TreapMap.tap nm ord cape', 2)
mg = rep(mg, 'nex g1 x1 hrunN C1 C2 C3 C4 SURE hx1 ord hsc', 'nex g1.g x1 hrunN C1 C2 C3 C4 SURE hx1 ord hsc', 1)
mg = rep(mg, 'have hf := fin_gate_finishLF_six_B (fun _ => True) tsMapAt_holds env\n',
         'have hf := fin_gate_finishLFCS_BC (fun _ => True) tsMapAt_holds env snd\n', 1)
mg = rep(mg, 'sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 x1 hs1 nm ord nex g1 g2\n'
             '    nedF (Sock.mk cape DATA) hrunL hargs trivial hnoar hrun',
         'sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 x1 nm ord nex g1 g2\n'
         '    nedF (Sock.mk cape DATA) hs1 hrunL hargs trivial hnoar hrun hreq', 1)
mg = ('/-- **The product of `member` on `%done` with soft calls**: `mem_gate_done_R` with the run\n'
      '`runLCS env snd ~` and the gate `fin_gate_finishLFCS_BC`. -/\n') + mg

# ---------------------------------------------------------------- mem_done_stepStr
md = block('CompSccLoopStrGen.lean', 'theorem mem_done_stepStr ', 'def MemDoneCallStr ')
md = rep(md, 'theorem mem_done_stepStr (r : RealCfg)', 'theorem mem_done_stepS (r : RealCfg) (snd : Nomm → NeedOrd → Bool)', 1)
md = rep(md, 'cfgReal r order kids', 'cfgRealS r snd order kids')
md = rep(md, '(nex : NextL CSet) (g1 : Gen (TreapMap mugF))\n'
             '    (hrunL : runLC (envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgRealS r snd order kids) st))\n'
             '      Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))',
         '(nex : NextL CSet) (g1 : GenSf (TreapMap mugF))\n'
         '    (hrunL : runLCS (envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgRealS r snd order kids) st))\n'
         '      snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0) = some (nex, g1))', 1)
md = rep(md, '= some (C nex.goal.toNoun (genNoun g1 x1)))', '= some (C nex.goal.toNoun (genNoun g1.g x1)))', 1)
md = rep(md, '(hs1 : x1.soft = A 0)', '(hs1 : x1.soft = softMapNoun g1.soft)', 1)
md = rep(md, '(hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))', '(hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2))', 1)
md = rep(md, '((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)\n    (sur : NeedOrd)',
         '((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)\n    ' + HREQ + '\n    (sur : NeedOrd)', 1)
md = rep(md, '(hfin : ∃ s, finishLFC (S := CSet) (Map := TreapMap mugF)\n'
             '      (envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgRealS r snd order kids) st)) nm ord cape',
         '(hfin : ∃ s, finishLFCS (S := CSet) (Map := TreapMap mugF)\n'
         '      (envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgRealS r snd order kids) st)) snd\n'
         '        TreapMap.tap nm ord cape', 1)
md = rep(md, 'msgOrd nn prev cape := by simp [cfgReal, hinfo]', 'msgOrd nn prev cape := by simp [cfgRealS, hinfo]', 1)
md = rep(md, 'have ho : compReal r B Mode.done', 'have ho : compRealS r snd B Mode.done', 1)
md = rep(md, 'compReal_done r B _ _ _ (by rw [hinfo]; exact memDoneM_eq _ nm cape DATA fuel nex g1 hrunL hargs ord hcol nedF g2 hnoar sur hsur)',
         'compRealS_done r snd B _ _ _ (by rw [hinfo]; exact memDoneMS_eqP _ snd nm cape DATA fuel nex g1 hrunL hargs ord hcol nedF g2 hnoar sur hsur)', 1)
md = rep(md, 'have hg := mem_gate_done_R cape DATA FOL keep ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm CA1\n'
             '    (by rw [hB]; exact hinl) _ nex g1 hrunL x1',
         'have hg := mem_gate_done_RS cape DATA FOL keep ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm CA1\n'
         '    (by rw [hB]; exact hinl) _ snd nex g1 hrunL x1', 1)
md = rep(md, '(sc_gate _ _ _ _ hcol) hargs nedF g2 hnoar hrun sur hsur', '(sc_gate _ _ _ _ hcol) hargs nedF g2 hnoar hrun hreq sur hsur', 1)
md = rep(md, 'exact finishLFC_need _ nm ord cape _ nex g1 hrunL nedF g2 hnoar s hs',
         'exact finishLFCS_need _ snd _ nm ord cape _ nex g1 hrunL nedF g2 hnoar s hs', 1)

# ---------------------------------------------------------------- MemDoneCallStr
mc = block('CompSccLoopStrGen.lean', 'def MemDoneCallStr ', 'theorem memGate_done_realStr ')
mc = rep(mc, 'def MemDoneCallStr (r : RealCfg)', 'def MemDoneCallS (r : RealCfg) (snd : Nomm → NeedOrd → Bool)', 1)
mc = rep(mc, '∃ (nex : NextL CSet) (g1 : Gen (TreapMap mugF)),\n'
             '      runLC (envDone r order kids st) Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))\n'
             '        = some (nex, g1) ∧',
         '∃ (nex : NextL CSet) (g1 : GenSf (TreapMap mugF)),\n'
         '      runLCS (envDoneS r snd order kids st) snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0)\n'
         '        = some (nex, g1) ∧', 1)
mc = rep(mc, 'CompRunAtXT (runLC (envDone r order kids st) Option.none) (memDCtx SCC (C CODE LSR) JH ML (A 0) b) X Y nm\n'
             '        CGoalL.done [] genEntry ∧',
         'CompRunAtXTS (runLCS (envDoneS r snd order kids st) snd Option.none) (memDCtx SCC (C CODE LSR) JH ML (A 0) b) X Y\n'
         '        nm CGoalL.done [] (GenSf.ofGen genEntry) ∧', 1)
mc = rep(mc, 'x1.cache = cacheN C1 C2 C3 C4 SURE ∧ x1.soft = A 0 ∧', 'x1.cache = cacheN C1 C2 C3 C4 SURE ∧', 1)
mc = rep(mc, 'needOrdAllocRegs ord g1 = some (nedF, g2) ∧', 'needOrdAllocRegs ord g1.g = some (nedF, g2) ∧', 1)
mc = rep(mc, '((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true ∧\n',
         '((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true ∧\n'
         '      (∀ u sf3, coerceLazyLS nedF cape nex.th.there nex.laz ⟨g2, g1.soft⟩ = some (u, sf3) →\n'
         '        ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req) ∧\n', 1)
mc = rep(mc, '(∃ s, finishLFC (S := CSet) (Map := TreapMap mugF) (envDone r order kids st) nm ord cape',
         '(∃ s, finishLFCS (S := CSet) (Map := TreapMap mugF) (envDoneS r snd order kids st) snd TreapMap.tap nm ord cape', 1)

# ---------------------------------------------------------------- memGate_done_realStr, _KStr
mr = block('CompSccLoopStrGen.lean', 'theorem memGate_done_realStr ', 'theorem csi_gate_loop_dStr ')
mr = rep(mr, 'theorem memGate_done_realStr (r : RealCfg) (order : List Noun)',
         'theorem memGate_done_realS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun)', 1)
mr = rep(mr, 'theorem memGate_done_KStr (r : RealCfg) (order : List Noun)',
         'theorem memGate_done_KS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun)', 1)
mr = rep(mr, 'cfgReal r order kids', 'cfgRealS r snd order kids')
mr = rep(mr, 'MemDoneCallStr r order kids', 'MemDoneCallS r snd order kids', 2)
mr = rep(mr, 'nedF, g2, hnoar, hrun, sur, hsur, hfin, hcs⟩', 'nedF, g2, hnoar, hrun, hreq, sur, hsur, hfin, hcs⟩', 1)
mr = rep(mr, 'obtain ⟨x1, hY1, heq⟩ := hXT (cuRest CA1) (A 1) (A 0) (cu_entry_nosoft CA1) hX\n'
             '  have hge : (genEntry : Gen (TreapMap mugF)) = gen0 := rfl\n'
             '  rw [hge, hrunL] at heq\n'
             '  obtain ⟨C1, C2, C3, C4, SURE, hx1, hs1, hQ1, hsh1, hout1⟩ := hY x1 hY1\n',
         'obtain ⟨x1, hY1, heq⟩ := hXT (cuRest CA1) (A 1) (A 0) (softMapNoun_empty).symm hX\n'
         '  have hge : (genEntry : Gen (TreapMap mugF)) = gen0 := rfl\n'
         '  rw [hge, hrunL] at heq\n'
         '  obtain ⟨C1, C2, C3, C4, SURE, hx1, hQ1, hsh1, hout1⟩ := hY x1 hY1\n', 1)
mr = rep(mr, 'exact mem_done_stepStr r order kids', 'exact mem_done_stepS r snd order kids', 1)
mr = rep(mr, 'hR CA1 hinl nex g1 hrunL x1 heq C1 C2 C3 C4 SURE hx1 hs1\n'
             '    hQ1 hsh1 hout1 ord hcol hargs nedF g2 hnoar hrun sur hsur hfin (fun prev SURE\' hm hnp => hcs x1 C1 C2 C3 C4 SURE\' prev hm hnp)',
         'hR CA1 hinl nex g1 hrunL { x1 with soft := softMapNoun g1.soft } heq C1 C2 C3 C4 SURE hx1 rfl\n'
         '    hQ1 hsh1 hout1 ord hcol hargs nedF g2 hnoar hrun hreq sur hsur hfin\n'
         '    (fun prev SURE\' hm hnp => hcs _ C1 C2 C3 C4 SURE\' prev hm hnp)', 1)
mr = rep(mr, 'memGate_done_realStr r order kids outC nout env (RK SC0 inl) P S x rK_sure',
         'memGate_done_realS r snd order kids outC nout env (RK SC0 inl) P S x rK_sure', 1)

HEAD = '''import lemmas.Compiler.CompSccLoopSoftFinAll
import lemmas.Compiler.CompSccLoopStrGen

/-! # The `%%done` member step with soft calls (README Gaps 21.17)

Generated by `tools/gen/softmem.py` (do not edit by hand): copies of `mem_gate_done_R`,
`mem_done_stepStr`, `MemDoneCallStr`, `memGate_done_realStr`, `memGate_done_KStr` for a member
whose run makes soft calls:

* the model's run is `runLCS env snd ~` from `GenSf.ofGen gen0` (`g1` a `GenSf`), the pill's run
  gives `genNoun g1.g x1` with `x1.soft = softMapNoun g1.soft` (the shape of `CompRunAtXTS`);
* the gate `finish` is `fin_gate_finishLFCS_BC`, its straight that of `finishLFCS ...
  TreapMap.tap`, with the hypothesis `hreq`: every soft call in the model's soft map after
  `+coerce-lazy` has requirements `%%none` / `%%this` (checked on the FM model of the corpus in
  `Ska/SccLoopSoftReqCheck.lean`);
* the model is `cfgRealS r snd` (`compRealS`, `memDoneMS`).

**`mem_done_stepS`**, `MemDoneCallS`, **`memGate_done_realS`**, **`memGate_done_KS`**: the
`%%done` gate at `LoopRS` for `cfgRealS`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The environment of a member compile on the state `st` of the final pass, for `cfgRealS`. -/
noncomputable def envDoneS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
    (st : St Noun NeedOrd) : CallEnv :=
  envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgRealS r snd order kids) st)

/-- **`memDoneMS` from the pieces of the run.** -/
theorem memDoneMS_eqP (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (cape : Cape) (DATA : Noun)
    (fuel : Nat) (nex : NextL CSet) (g1 : GenSf (TreapMap mugF))
    (hrunL : runLCS env snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0) = some (nex, g1))
    (hargs : nex.th.args = []) (ord : NeedOrd) (hcol : shapeCol fuel nex.laz cape = some ord) (nedF : Need)
    (g2 : Gen (TreapMap mugF)) (hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2)) (sur : NeedOrd)
    (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur) :
    memDoneMS env snd ⟨nm, cape, DATA, fuel⟩ = some ⟨needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1, sur⟩ := by
  simp [memDoneMS, hrunL, hargs, hcol, hnoar, hsur]

/-- **The straight of `finishLFCS` has the need `need-new`.** -/
theorem finishLFCS_need (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (tapS : TreapMap mugF SoftCall → List (Nat × SoftCall)) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) (nex : NextL CSet) (g1 : GenSf (TreapMap mugF))
    (hrunL : runLCS env snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0) = some (nex, g1))
    (nedF : Need) (g2 : Gen (TreapMap mugF)) (hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2))
    (s : Straight (TreapMap mugF))
    (h : finishLFCS (S := CSet) (Map := TreapMap mugF) env snd tapS nm ord less bake = some s) :
    s.need = needToOrd (bake nedF).1 := by
  rw [finishLFCS_tail, hrunL] at h
  simp only [Option.bind_some] at h
  by_cases ha : nex.th.args ≠ []
  · simp [ha] at h
  · simp only [ha, if_false, hnoar, Option.bind_some] at h
    unfold finTailS at h
    cases e1 : coerceLazyLS nedF less nex.th.there nex.laz ⟨g2, g1.soft⟩ with
    | none => simp [e1] at h
    | some r1 =>
      simp only [e1, Option.bind_some] at h
      cases e2 : softDone tapS r1.2 with
      | none => simp [e2] at h
      | some g3 =>
        simp only [e2, Option.bind_some] at h
        cases e3 : addOps nex.th.there ((bake nedF).2.map fun (r, v) => Pole.imm v r) g3 with
        | none => simp [e3] at h
        | some r2 =>
          simp only [e3, Option.bind_some] at h
          exact toStraightF_need _ _ _ _ s h

'''

sys.stdout.write(HEAD.replace('%%', '%'))
sys.stdout.write(mg.rstrip() + '\n\n')
sys.stdout.write(md.rstrip() + '\n\n')
sys.stdout.write(mc.rstrip() + '\n\n')
sys.stdout.write(mr.rstrip() + '\n\nend Compiler\nend Formalization\n')
