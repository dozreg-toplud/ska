"""Writes lemmas/Compiler/CompStraightMapSix.lean: track A's tops on `SixOk`
(`cu_gate_scc_one_six`, `cu_gate_scc_one_six_fol`, CompSccSix.lean) with their
hypothesis `TsMapAt` discharged by `ts_at_all` (README Gaps 20).  The
statements are copied from CompSccSix.lean without `(hT : TsMapAt) `; every
replacement asserts its count.  Run from formalization/:
python3 tools/gen/tsmsix.py"""
import re
src = open('lemmas/Compiler/CompSccSix.lean').read()


def stmt(name):
    m = re.search(r'\ntheorem ' + re.escape(name) + r' \(hT : TsMapAt\) (.*?) :=\n', src, re.S)
    assert m, name
    return m.group(1)


top = stmt('cu_gate_scc_one_six')
m = re.search(r'\ntheorem cu_gate_six \(Q : TreapMap mugF \(Nat × List Nat\) → Prop\) \(hT : TsOn Q\)\n(.*?) := by\n', src, re.S)
assert m
gate = m.group(1)
hq = """    (hQ : ∀ nex g1 q g2, runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → kerf nex g1 = some (q, g2) → Q g2.cond)
"""
assert gate.count(hq) == 1 and 'theorem' not in gate
gate = gate.replace(hq, '')
fol = stmt('cu_gate_scc_one_six_fol')
assert top.count('(hax : Bake.NoAx0 nm)') == 1 and fol.count('(hf : FolMade nm)') == 1
out = '''import lemmas.Compiler.CompSccSix
import lemmas.Compiler.CompStraightMapAt

/-!
# The tops on `SixOk` without a hypothesis on `+to-straight`

Written by `tools/gen/tsmsix.py` (README Gaps 20).  `TsMapAt`, the one
hypothesis of track A's `cu_gate_scc_one_six` on `+to-straight`, holds
(`tsMapAt_holds`, by `ts_at_all`: `tsn_at` without proxies, `tsmp_at` with
them).  So the tops hold with only `FinSure` and the hypotheses on the state
nouns left (`cu_gate_scc_one_six_ts`, `cu_gate_scc_one_six_fol_ts`), and
the gate of `+compile-unary` on `SixOk` code is `finishLUC` (`cu_gate_six_ts`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- **`+to-straight` on every `cond`** (track A's `TsMapAt`). -/
theorem tsMapAt_holds : TsMapAt :=
  fun _ h7 g x o ned _ hrun => ts_at_all h7 g x o ned hrun

/-- **`cu_gate_scc_one_six` with `TsMapAt` discharged.** -/
theorem cu_gate_scc_one_six_ts ''' + top + ''' :=
  cu_gate_scc_one_six tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls
    nm INL' hinl env hn hax hfs hbake FUNC V n hn' hax' hgot hv

/-- **`cu_gate_scc_one_six_fol` with `TsMapAt` discharged**: on the nomms
that `+fol-loop` makes, nothing but `SixOk`, `FinSure` and the state nouns. -/
theorem cu_gate_scc_one_six_fol_ts ''' + fol + ''' :=
  cu_gate_scc_one_six_fol tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap
    hcalls nm INL' hinl env hn hf hfs hbake FUNC V n hn' hf' hgot hv

/-- **The gate of `+compile-unary` on `SixOk` code** (track A's
`cu_gate_six`) with no hypothesis on `+to-straight`: `finishLUC`, whatever
proxies `+kerf` leaves in `cond`. -/
theorem cu_gate_six_ts
''' + gate + ''' :=
  cu_gate_six (fun _ => True) tsMapAt_holds FUNC SCC CODE LSR JH CACHE NM CA V env n hn ha (fun _ _ _ _ _ _ => trivial)
    hcsi hgot hv

/-- **A `%6` in both passes** (the first example of `CompSccSix.lean`) with
no hypothesis on `+to-straight`. -/
example (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C Cape.no.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C Cape.no.toNoun DATA) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C Cape.no.toNoun DATA) FOL) CODE INL (Nomm.n7 (Nomm.n1 (A 0)) sixEx) INL') (env : CallEnv)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some (Nomm.n7 (Nomm.n1 (A 0)) sixEx).toNoun) :=
  cu_gate_scc_one_six_ts Cape.no DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls _ INL'
    hinl env rfl (by simp [sixEx, Bake.NoAx0]) (finSure_n7_n1 env _ _) (noBakeOneC_no env _ DATA) FUNC V _ rfl
    (by simp [sixEx, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
'''
open('lemmas/Compiler/CompStraightMapSix.lean', 'w').write(out)
print('wrote lemmas/Compiler/CompStraightMapSix.lean')
