import lemmas.Compiler.CompShapeColRet
import lemmas.Compiler.CompSccSixBake
import lemmas.Ska.ShapeColAlgFix

/-!
# The top without `FixRet`

`FixRet` of `CompShapeColRet.lean` (the model's loop of `+inter2-collapse`
stops within a fixed `fuel`) is replaced by a theorem:

* `l2i_normal`: when every sure need of the lazy need is normal (no
  `[%pair [%none ~] [%none ~]]` in `needToOrd` of it, `SureNorm`), so is
  every node of `l2i`; with `i12_normal` and **`fixRet_bound`**
  (`Ska/ShapeColAlgFix.lean`) the loop returns within `fixFuel` rounds of the
  first tree, so `+shape-collapse` of the model returns at the fuel
  `scFuel nex cape` (`shapeCol_ret`), and `scAt_R` is `ScAt` of the `ord`
  `scOrdR` (the model's `shapeCol` at that fuel);
* `NormRun env nm`: the one hypothesis left on `+shape-collapse`, on the run
  (every sure need of the final pass's lazy need is normal); the `#guard`s of
  `Ska/ShapeColAlgCheck.lean` check it on the enumerations of the class;
* **`cu_gate_scc_one_six_nf`** (no bake) and **`cu_gate_scc_one_six_bake_nf`**
  (the real bake): the tops of `CompShapeColRet.lean` and
  `CompSccSixBake.lean` with `NormRun` in place of `FixRet` and the `ord`
  `scOrdR`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- A sure need with no `[%pair [%none ~] [%none ~]]`. -/
def SureNorm (s : Sure CSet) : Prop := ordNormal (needToOrd s.ned) = true

mutual
/-- **Normal needs in a lazy need, normal needs in `l2i` of it.** -/
theorem l2i_normal : ∀ (o : Nat) (laz : Lazy CSet), WalkP (fun _ s => SureNorm s) o laz → I1.AllN (l2i laz)
  | o, Lazy.mk s f b, h => by
    rw [WalkP] at h
    rw [l2i]
    exact l2iBonds_normal b h.2.2 (needToOrd s.ned) s.lok (l2iForks f) h.1 (l2iForks_normal f h.2.1)
theorem l2iForks_normal : ∀ f : List (Lazy.ForkE CSet), WalkPF (fun _ s => SureNorm s) f → I1.AllNF (l2iForks f)
  | [], _ => by rw [l2iForks, I1.AllNF]; trivial
  | ((oy, y), (on, n)) :: r, h => by
    rw [WalkPF] at h
    rw [l2iForks, I1.AllNF]
    exact ⟨l2i_normal oy y h.1, l2i_normal on n h.2.1, l2iForks_normal r h.2.2⟩
theorem l2iBonds_normal : ∀ b : List (Nat × Lazy CSet), WalkPB (fun _ s => SureNorm s) b →
    ∀ (ned : NeedOrd) (lok : CSet) (fk : List (I1 CSet × I1 CSet)),
    ordNormal ned = true → I1.AllNF fk → I1.AllN (l2iBonds b ned lok fk)
  | [], _, ned, lok, fk, hl, hf => by rw [l2iBonds, I1.AllN]; exact ⟨hl, hf⟩
  | (ob, i) :: r, h, ned, lok, fk, hl, hf => by
    rw [WalkPB] at h
    have hi := l2i_normal ob i h.1
    rw [l2iBonds]
    apply l2iBonds_normal r h.2
    · generalize l2i i = J at hi
      obtain ⟨n', l', f'⟩ := J
      rw [I1.AllN] at hi
      exact ordNormal_uniOrd hi.1 hl
    · apply I1.allNF_append _ _ _ hf
      generalize l2i i = J at hi
      obtain ⟨n', l', f'⟩ := J
      rw [I1.AllN] at hi
      exact hi.2
end

/-- **Every sure need of the final pass's lazy need is normal** (no
`[%pair [%none ~] [%none ~]]`, which `needToOrd` would keep): the one
hypothesis left on `+shape-collapse`. -/
def NormRun (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
    WalkP (fun _ s => SureNorm s) 0 nex.laz

/-- The fuel of the model's `+shape-collapse` on the lazy need of `nex`:
`fixFuel` of its first tree. -/
noncomputable def scFuel (nex : NextL CSet) (cape : Cape) : Nat :=
  match i12 cape (l2i nex.laz) with
  | some t => fixFuel t
  | Option.none => 0

/-- The model's `ord` with that fuel. -/
noncomputable def scOrdR (nex : NextL CSet) (cape : Cape) : NeedOrd := scOrd (scFuel nex cape) nex cape

/-- **The model's `+shape-collapse` returns at `scFuel`** on every final
pass of the class whose needs are normal. -/
theorem shapeCol_ret (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (cape : Cape)
    (hnorm : NormRun env nm) (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hr : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    (shapeCol (scFuel nex cape) nex.laz cape).isSome := by
  have hl := l2i_lokOk 0 nex.laz (entry_lok env hn ha hr)
  obtain ⟨intr, ei⟩ := Option.isSome_iff_exists.1 (i12_some cape (l2i nex.laz) hl)
  have hN := i12_normal cape (l2i nex.laz) intr ei (l2i_normal 0 nex.laz (hnorm nex g1 hr))
  obtain ⟨fix, ef⟩ := Option.isSome_iff_exists.1 (fixRet_bound cape intr hN)
  have hf : scFuel nex cape = fixFuel intr := by unfold scFuel; rw [ei]
  unfold shapeCol
  rw [hf, ei, Option.bind_some]
  exact inter2Collapse_some cape _ intr fix ef

/-- `FixRet` at the fuel of each run, from `NormRun`. -/
theorem fixRet_norm (env : CallEnv) {nm : Nomm} (hnorm : NormRun env nm) (cape : Cape) :
    ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
      ∀ intr, i12 cape (l2i nex.laz) = some intr → (fixLoop cape (fixFuel intr) intr).isSome :=
  fun nex g1 hr intr ei => fixRet_bound cape intr (i12_normal cape (l2i nex.laz) intr ei (l2i_normal 0 nex.laz (hnorm nex g1 hr)))

/-- `ScAt` of the model's `ord` at `scFuel`. -/
theorem scAt_R (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (cape : Cape)
    (hnorm : NormRun env nm) : ScAt env nm (fun nex => scOrdR nex cape) cape := by
  intro nex g1 hr
  have hs := shapeCol_ret env hn ha cape hnorm nex g1 hr
  cases e : shapeCol (scFuel nex cape) nex.laz cape with
  | none => rw [e] at hs; cases hs
  | some r =>
    have hg := sc_gate nex.laz cape (scFuel nex cape) r e
    simp only [scOrdR, scOrd, e, Option.getD_some]
    exact hg

/-- **The top on `SixOk` with the `ord` of `+shape-collapse` and no fuel
hypothesis** (`cu_gate_scc_one_six_fix` with `NormRun` in place of
`FixRet`; nothing baked, `NoBakeOneO`). -/
theorem cu_gate_scc_one_six_nf (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hnorm : NormRun env nm)
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
  cu_gate_scc_one_six_q_L (fun _ => True) tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls nm INL' hinl env hn hax (fun nex => scOrdR nex cape)
    (scAt_R env hn hax cape hnorm) (fun _ _ _ => trivial) hbake FUNC V n hn' hax' (fun _ _ _ _ _ _ => trivial)
    hgot hv

/-- **The top on `SixOk` with the real bake and no fuel hypothesis**
(`cu_gate_scc_one_six_bake` with `NormRun` in place of `FixRet`): the n-ary
entry is `finishLFB` of the model's `ord` at `scFuel`; on `+shape-collapse`
only `NormRun`, on the bake only `BakeRunO`. -/
theorem cu_gate_scc_one_six_bake_nf (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hnorm : NormRun env nm)
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
  cu_gate_scc_one_six_q_B (fun _ => True) tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls nm INL' hinl env hn hax (fun nex => scOrdR nex cape)
    (scAt_R env hn hax cape hnorm) (fun _ _ _ => trivial) hbake FUNC V n hn' hax' (fun _ _ _ _ _ _ => trivial)
    hgot hv

/-- **The top on the bare `%6`** (`sixBare`, cape `|`) with no hypothesis on
`+shape-collapse` but `NormRun` (checked on this nomm by the `#guard`s of
`Ska/ShapeColAlgCheck.lean`), and nothing baked (`noBakeOneO_no`). -/
example (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C Cape.no.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C Cape.no.toNoun DATA) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C Cape.no.toNoun DATA) FOL) CODE INL sixBare INL') (env : CallEnv)
    (hnorm : NormRun env sixBare)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some sixBare.toNoun) :=
  cu_gate_scc_one_six_nf Cape.no DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls _
    INL' hinl env rfl (by simp [sixBare, Bake.NoAx0]) hnorm (noBakeOneO_no env _ _ DATA) FUNC V sixBare rfl
    (by simp [sixBare, Bake.NoAx0]) hgot hv

/-- `cu_gate_scc_one_six_nf` on the nomms that `+fol-loop` makes (`FolMade`). -/
theorem cu_gate_scc_one_six_fol_nf (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm) (hnorm : NormRun env nm)
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
  cu_gate_scc_one_six_nf cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn (folMade_noAx0 hf) hnorm hbake FUNC V n hn' (folMade_noAx0 hf') hgot hv

/-- `cu_gate_scc_one_six_bake_nf` on the nomms that `+fol-loop` makes (`FolMade`). -/
theorem cu_gate_scc_one_six_bake_fol_nf (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm) (hnorm : NormRun env nm)
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
  cu_gate_scc_one_six_bake_nf cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm
    INL' hinl env hn (folMade_noAx0 hf) hnorm hbake FUNC V n hn' (folMade_noAx0 hf') hgot hv

/-- **The top with the real bake on a known head** (`sixHead`, `%s01` of the
bake check, cape `[& |]`, `CompSccSixBake.lean`) with no fuel hypothesis:
`NormRun` (checked on it in `Ska/ShapeColAlgCheck.lean`) and `hord` (the
`ord` of the run is a cell with a `%this` head, computed by the `#guard`s of
`CompSccSixBake.lean`), which gives `BakeRunO` by `bakeRunO_head`. -/
example (dh dt FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C capeHead.toNoun (C dh dt)) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C capeHead.toNoun (C dh dt)) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C capeHead.toNoun (C dh dt)) FOL) CODE INL sixHead INL') (env : CallEnv)
    (hnorm : NormRun env sixHead)
    (hord : ∀ nex g1, runLC env Option.none sixHead (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → ∃ q, scOrdR nex capeHead = NeedOrd.pair NeedOrd.this q)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some sixHead.toNoun) :=
  cu_gate_scc_one_six_bake_nf capeHead (C dh dt) FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap
    hcalls _ INL' hinl env rfl (by simp [sixHead, Bake.NoAx0]) hnorm
    (bakeRunO_head env _ _ Cape.yes dh dt rfl hord) FUNC V sixHead rfl (by simp [sixHead, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
