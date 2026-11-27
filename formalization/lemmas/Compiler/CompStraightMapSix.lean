import lemmas.Compiler.CompSccSix
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
theorem cu_gate_scc_one_six_ts (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfs : FinSure env nm)
    (hbake : NoBakeOneC env nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls
    nm INL' hinl env hn hax hfs hbake FUNC V n hn' hax' hgot hv

/-- **`cu_gate_scc_one_six_fol` with `TsMapAt` discharged**: on the nomms
that `+fol-loop` makes, nothing but `SixOk`, `FinSure` and the state nouns. -/
theorem cu_gate_scc_one_six_fol_ts (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm) (hfs : FinSure env nm)
    (hbake : NoBakeOneC env nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hf' : FolMade n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_fol tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap
    hcalls nm INL' hinl env hn hf hfs hbake FUNC V n hn' hf' hgot hv

/-- **The gate of `+compile-unary` on `SixOk` code** (track A's
`cu_gate_six`) with no hypothesis on `+to-straight`: `finishLUC`, whatever
proxies `+kerf` leaves in `cond`. -/
theorem cu_gate_six_ts
    (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : SixOk n = true)
    (ha : Bake.NoAx0 n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA :=
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
