import re, sys
S='/tmp/claude-1000/-home-kirill-work-ska-scratch-wt-ska-formalization/f82d372f-f0b4-4933-9658-7b962d5dfef8/scratchpad/track-a/'
def grab(path, name):
    L = open(path).read().split('\n')
    i = next(k for k,l in enumerate(L) if l.startswith('theorem '+name+' '))
    j = i+1
    while j < len(L) and not (L[j].startswith('/--') or L[j].startswith('theorem ') or L[j].startswith('end ') or L[j].startswith('/-!')):
        j += 1
    return '\n'.join(L[i:j]).rstrip()+'\n'
G='lemmas/Compiler/CompSccCallGate.lean'; C='lemmas/Compiler/CompSccCall.lean'
def sub(t, pairs):
    for a,b in pairs:
        if a not in t: sys.exit('MISSING: '+a[:80])
        t = t.replace(a,b)
    return t
QH = '(Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) '
out = []
# fin_gate_finishLF
t = grab(G,'fin_gate_finishLF_c')
t = sub(t,[('theorem fin_gate_finishLF_c {ctx', 'theorem fin_gate_finishLF_six '+QH+'{ctx'),
  ('(hcond1 : ∀ k, HoonMap.get g1.cond k = Option.none)', '(hQ : Q g1.cond)'),
  ('exact fin_gate h7', 'exact fin_gate_ts Q hT h7'),
  ('(fun k => by rw [kc2]; exact hcond1 k)', '(by rw [kc2]; exact hQ)')])
out.append(t)
# mem_to_finish
t = grab(G,'mem_to_finish_c')
t = sub(t,[('theorem mem_to_finish_c', 'theorem mem_to_finish_six'),
  ('(env : CallEnv) (hn : indOk nm = true)', '(env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)'),
  ('comp_run_entry_c h7 hcode env nm hn', 'comp_run_entry_six h7 hcode env nm hn ha')])
out.append(t)
# mem_gate
t = grab(G,'mem_gate_c')
t = sub(t,[('theorem mem_gate_c', 'theorem mem_gate_six '+QH),
  ('(env : CallEnv) (hn : indOk nm = true)', '(env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)'),
  ('(hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))',
   '(hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))\n    (hQ : Q g1.cond)'),
  ('rw [mem_to_finish_c', 'rw [mem_to_finish_six'),
  ('hinl env hn nex g1 hrunL', 'hinl env hn ha nex g1 hrunL'),
  ('have hf := fin_gate_finishLF_c env', 'have hf := fin_gate_finishLF_six Q hT env'),
  ('nedF s hrunL hargs hlaz (mem_cond_frag_c env hn hrunL) hnoar', 'nedF s hrunL hargs hlaz hQ hnoar')])
out.append(t)
# csi_gate_scc_one_m
t = grab(G,'csi_gate_scc_one_m_c')
t = sub(t,[('theorem csi_gate_scc_one_m_c', 'theorem csi_gate_scc_one_m_six '+QH),
  ('(env : CallEnv) (hn : indOk nm = true)', '(env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (hfs : FinSure env nm)'),
  ('(hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))',
   '(hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))\n    (hQ : Q g1.cond) (hargs : nex.th.args = [])'),
  ('obtain ⟨hlz, hsur⟩ := scc_sur_frag_c env hn hrunL cape', 'obtain ⟨hlz, hsur⟩ := scc_sur_six env hn ha hfs hrunL cape'),
  ('  have hargs := args_frag_c env hn hrunL\n', ''),
  ('(indPure_of_indOk nm hn)', '(indPure_of_sixOk nm hn)'),
  ('have hm := mem_gate_c cape', 'have hm := mem_gate_six Q hT cape'),
  ('hi env hn nex g1 hrunL nex.laz.sure', 'hi env hn ha nex g1 hrunL hQ nex.laz.sure')])
out.append(t)
# mem_gate_none
t = grab(G,'mem_gate_none_c')
t = sub(t,[('theorem mem_gate_none_c', 'theorem mem_gate_none_six'),
  ('(env : CallEnv) (hn : indOk nm = true)', '(env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (hfs : FinSure env nm)'),
  ('comp_run_entry_c h7 hcode env nm hn', 'comp_run_entry_six h7 hcode env nm hn ha'),
  ('scc_sur_frag_c env hn hr cape', 'scc_sur_six env hn ha hfs hr cape')])
out.append(t)
# csi_gate_scc_one_f
t = grab(G,'csi_gate_scc_one_f_c')
t = sub(t,[('theorem csi_gate_scc_one_f_c', 'theorem csi_gate_scc_one_f_six '+QH),
  ('(env : CallEnv) (hn : indOk nm = true)', '(env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (hfs : FinSure env nm)\n    (hQ : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →\n      Q g1.cond)'),
  ('(indPure_of_indOk nm hn)', '(indPure_of_sixOk nm hn)'),
  ('(C NARY (C MONO (C SCCS (C INL SURE)))) nm _ hi env hn hc)', '(C NARY (C MONO (C SCCS (C INL SURE)))) nm _ hi env hn ha hfs hc)'),
  ('mem_gate_none_c cape', 'mem_gate_none_six cape'),
  ('rw [csi_gate_scc_one_m_c cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL\'\n          hinl env hn nex g1 hr nedF',
   'rw [csi_gate_scc_one_m_six Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL\'\n          hinl env hn ha hfs nex g1 hr (hQ nex g1 hr) ha nedF')])
out.append(t)
open(S+'chain.lean','w').write('\n\n'.join(out))
