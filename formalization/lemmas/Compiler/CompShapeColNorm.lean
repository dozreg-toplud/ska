import lemmas.Compiler.CompRunAllNorm

/-!
# The one-bell tops with `NormRun` proved

`cu_gate_scc_one_six_cl` (nothing baked, `NoBakeOneO`) and
`cu_gate_scc_one_six_bake_cl` (the real bake, `BakeRunO`): the tops of
`CompShapeColFuel.lean` with `NormRun` discharged by `normRun_six`
(`CompRunAllNorm.lean`), and their `FolMade` variants.  On
`+shape-collapse` nothing is assumed now.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- **The one-bell top on `SixOk`, nothing baked, with no hypothesis on `+shape-collapse`**: `cu_gate_scc_one_six_nf` with `NormRun` proved (`normRun_six`). -/
theorem cu_gate_scc_one_six_cl (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (hbake : NoBakeOneO env nm (fun nex => scOrdR nex cape) cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (scOrdR p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_nf cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn hax (normRun_six env hn) hbake FUNC V n hn' hax' hgot hv

/-- **The one-bell top on `SixOk` with the real bake and no hypothesis on `+shape-collapse`**: `cu_gate_scc_one_six_bake_nf` with `NormRun` proved; on the bake only `BakeRunO`. -/
theorem cu_gate_scc_one_six_bake_cl (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (hbake : BakeRunO env nm (fun nex => scOrdR nex cape) cape DATA)
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
  cu_gate_scc_one_six_bake_nf cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn hax (normRun_six env hn) hbake FUNC V n hn' hax' hgot hv

/-- `cu_gate_scc_one_six_cl` on the nomms that `+fol-loop` makes (`FolMade`). -/
theorem cu_gate_scc_one_six_fol_cl (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm)
    (hbake : NoBakeOneO env nm (fun nex => scOrdR nex cape) cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hf' : FolMade n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (scOrdR p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_fol_nf cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn hf (normRun_six env hn) hbake FUNC V n hn' hf' hgot hv

/-- `cu_gate_scc_one_six_bake_cl` on the nomms that `+fol-loop` makes (`FolMade`). -/
theorem cu_gate_scc_one_six_bake_fol_cl (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm)
    (hbake : BakeRunO env nm (fun nex => scOrdR nex cape) cape DATA)
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
  cu_gate_scc_one_six_bake_fol_nf cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn hf (normRun_six env hn) hbake FUNC V n hn' hf' hgot hv

/-- **The top on the bare `%6`** (`sixBare`, cape `|`) with no hypothesis
but the state nouns and the class's. -/
example (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C Cape.no.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C Cape.no.toNoun DATA) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C Cape.no.toNoun DATA) FOL) CODE INL sixBare INL') (env : CallEnv)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some sixBare.toNoun) :=
  cu_gate_scc_one_six_cl Cape.no DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls _
    INL' hinl env rfl (by simp [sixBare, Bake.NoAx0]) (noBakeOneO_no env _ _ DATA) FUNC V sixBare rfl
    (by simp [sixBare, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
