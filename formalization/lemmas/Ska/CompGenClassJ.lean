import lemmas.Ska.CompGenClassH

/-!
# The state-level fronts of the general cons: `frontsSG_consG`

README Gaps 12.39, item 12.  The interface `FrontsSGConsOf` of
`CompGenClassH.lean`.  At a goal label `a` of the cons's goal `L` the block
gets, in front of its old body, the copy's ops `PC a`, `p`'s front, `q`'s
front and the split's ops `PS a` (a part whose goal has no entry at `a`
puts nothing there: `FrameG.keep`, `cf_frontSG_nil`).  Renamed by any `cf`
that agrees with `g1.cond` below `g1.re`, the copy's and the split's ops are
unchanged (their registers are no keys of `g1.cond`), and the parts' fronts
are their renamed fronts; `frontSG_consG` composes the four.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The cons's state-level fronts from the parts'.** -/
theorem frontsSG_consG : FrontsSGConsOf S Map := by
  intro L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np Qq Qp CA G Fq Gq Nq Rq FSq Fp Gp Np Rp FSp
  have Pq := premG_tel CA G
  have Pp := premG_hed CA G Fq Gq
  have d3 : g3.drop = false := Fp.drop.trans (Fq.drop.trans CA.dS)
  have CO := CA.copyOK d3 Rp.lu Rq.lu
  have HA := halvesApart_split CA G
  have CP : CopyPreAt (Map := Map) (g3.emitted ⟨[], [], Termin.hop np.th⟩) ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) :=
    cc_copyPreAt_re (emitted_re _ _).symm (copyPreG Fq Fp Pq Pp Rq Rp HA)
  obtain ⟨PC, PPC, OC, AC⟩ := CopyOKL.runAt CO
  have hdj : ((g0.bo, L) :: entries L).Pairwise
      fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r := by
    refine List.pairwise_cons.mpr ⟨fun e' he' heq => ?_, G.goal.labDisj⟩
    have := (G.goal.lab e' he').2.1
    simp only at heq; omega
  have hreg0 : ∀ e ∈ (g0.bo, L) :: entries L, Distinct e.2.sure.ned ∧
      ∀ y, NMem e.2.sure.ned y → y < (g0.emitted ⟨[], [], Termin.hop th⟩).re := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨G.goal.dist, G.goal.sregs⟩
    · exact G.goal.eregs e he
  obtain ⟨PS, PPS, -, SA⟩ := SplitOKL.runAt CA.sp.toL hdj hreg0
  have P00 := CA.sp
  obtain ⟨P0, PP0, -, A0⟩ := P00
  -- the ranges
  have r0 := CA.reS
  have r1 := Fq.re
  have r2 := Fp.re
  have r3 : g3.re ≤ g1.re := by have := PPC.re; simpa only [emitted_re] using this
  have bS := CA.boS
  have b2 := Fq.bo
  have b3 := Fp.bo
  have cd1 : g1.cond = g3.cond := PPC.cond
  -- `cond` along the run
  have cbS : CondBelow gS := CA.condBelowS G
  have cb2 : CondBelow g2 := Fq.cfr.below cbS
  have cb3 : CondBelow g3 := Fp.cfr.below cb2
  have c32 : ∀ k, k < g2.re → HoonMap.get g3.cond k = HoonMap.get g2.cond k := fun k hk => by
    rcases Fp.cfr.2 k with e | e
    · exact e
    · omega
  have c2S : ∀ k, k < gS.re → HoonMap.get g2.cond k = HoonMap.get gS.cond k := fun k hk => by
    rcases Fq.cfr.2 k with e | e
    · exact e
    · omega
  have c10 : ∀ k, k < gS.re → HoonMap.get g1.cond k = HoonMap.get g0.cond k := fun k hk => by
    rw [cd1, c32 k (by omega), c2S k hk, CA.condS]
  have Gq' := Fq.goalOut Pq.goal
  have Gp' := Fp.goalOut Pp.goal
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  obtain ⟨-, hlt, B0, th0, hb0⟩ := G.goal.lab e he
  have hk0 : ((g0.bo, L) : Nat × Lazy S).1 ≠ e.1 := by simp only; omega
  have hk3 : ((g3.bo, L) : Nat × Lazy S).1 ≠ e.1 := by simp only; omega
  have eEs : atL ((g0.bo, L) :: entries L) e.1 = atL (entries L) e.1 := atL_cons_ne hk0
  have eHs : atL ((g0.bo, hed) :: entries hed) e.1 = atL (entries hed) e.1 := atL_cons_ne hk0
  have eTs : atL ((g0.bo, tel) :: entries tel) e.1 = atL (entries tel) e.1 := atL_cons_ne hk0
  have eFs : atL ((g3.bo, np.laz) :: entries np.laz) e.1 = atL (entries np.laz) e.1 := atL_cons_ne hk3
  have eGs : atL ((g3.bo, nq.laz) :: entries nq.laz) e.1 = atL (entries nq.laz) e.1 := atL_cons_ne hk3
  have eMs : atL ((g3.bo, nex.laz) :: entries nex.laz) e.1 = atL (entries nex.laz) e.1 := atL_cons_ne hk3
  -- the split at the label
  obtain ⟨Sfit, Sreg1, Sreg2, Srun⟩ := SA e.1
  rw [eEs, eHs, eTs] at Sfit Srun
  rw [eEs, eHs] at Sreg1
  rw [eEs, eTs] at Sreg2
  -- the copy at the label
  have C1 := AC e.1 (CP e.1).1 (CP e.1).2
  rw [eFs, eGs, eMs] at C1
  obtain ⟨Cfit, Creg, -, CRg, Crun⟩ := C1
  -- the registers of the copy's and the split's ops are no keys of `cond`
  have regsC : RegsIn (fun x => x < g1.re ∧ HoonMap.get g1.cond x = Option.none) (PC e.1) := by
    refine RegsIn.mono (fun x hx => ?_) CRg
    rcases hx with ⟨F, hF, hm⟩ | ⟨h1, h2⟩
    · rcases List.mem_append.mp hF with hF | hF
      · obtain ⟨e', he', -, rfl⟩ := mem_atL hF
        have := (Gp'.eregs e' he').2 x hm
        exact ⟨by omega, by rw [cd1]; exact Fp.econd e' he' x hm⟩
      · obtain ⟨e', he', -, rfl⟩ := mem_atL hF
        have := (Gq'.eregs e' he').2 x hm
        exact ⟨by omega, by rw [cd1, c32 x this]; exact Fq.econd e' he' x hm⟩
    · exact ⟨h2, by rw [cd1]; exact condBelow_none cb3 h1⟩
  have bE : HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks e.1 = some ⟨[], B0, Termin.hop th0⟩ := by
    rw [ch_emitted_ne _ _ (by omega)]; exact hb0
  have eP : PS e.1 = P0 e.1 := ch_pref_uniq PPS PP0 bE
  have regsS : RegsIn (fun x => x < gS.re ∧ HoonMap.get g0.cond x = Option.none) (PS e.1) := by
    rw [eP]
    obtain ⟨ps, eps, pE, -, -, sP, -⟩ := A0 e.1
    rw [eps]
    refine ch_regsIn_flatten _ ps (fun p hp => ?_)
    have hp1 : p.1 ∈ atL (entries L) e.1 := by
      rw [← eEs]; exact pE.mem_iff.mp (List.mem_map_of_mem hp)
    obtain ⟨e', he', -, es'⟩ := mem_atL hp1
    have ra := (sP p hp).ra (fun x => HoonMap.get g0.cond x = Option.none)
      (fun r hr => by rw [← es'] at hr; exact G.ec e' he' r hr) (fun r hr => condBelow_none G.cb hr)
    have rb := (sP p hp).rb (fun r hr => by rw [← es'] at hr; exact (G.goal.eregs e' he').2 r hr)
    intro q hq x hx
    exact ⟨by have := rb q hq x hx; simp only [emitted_re] at this; omega, ra q hq x hx⟩
  -- the halves' registers
  have hLh : ∀ H ∈ atL (entries hed) e.1, ∀ r, NMem H.ned r →
      r < gS.re ∧ (r < g0.re → ∃ L' ∈ atL (entries L) e.1, NMem L'.ned r) := by
    intro H hH r hr
    rcases Sreg1 H hH r hr with ⟨L', hL', hm⟩ | ⟨h1, h2⟩
    · obtain ⟨e', he', -, rfl⟩ := mem_atL hL'
      have := (G.goal.eregs e' he').2 r hm
      exact ⟨by omega, fun _ => ⟨_, hL', hm⟩⟩
    · exact ⟨h2, fun h => by simp only [emitted_re] at h1; omega⟩
  have hLt : ∀ T ∈ atL (entries tel) e.1, ∀ r, NMem T.ned r →
      r < gS.re ∧ (r < g0.re → ∃ L' ∈ atL (entries L) e.1, NMem L'.ned r) := by
    intro T hT r hr
    rcases Sreg2 T hT r hr with ⟨L', hL', hm⟩ | ⟨h1, h2⟩
    · obtain ⟨e', he', -, rfl⟩ := mem_atL hL'
      have := (G.goal.eregs e' he').2 r hm
      exact ⟨by omega, fun _ => ⟨_, hL', hm⟩⟩
    · exact ⟨h2, fun h => by simp only [emitted_re] at h1; omega⟩
  have hht : ∀ H ∈ atL (entries hed) e.1, ∀ T ∈ atL (entries tel) e.1, ∀ r, NMem H.ned r → ¬ NMem T.ned r := by
    intro H hH T hT r hr ht
    obtain ⟨eh, heh, kh, rfl⟩ := mem_atL hH
    obtain ⟨et, het, kt, rfl⟩ := mem_atL hT
    exact HA.ee eh heh et het (kh.trans kt.symm) r hr ht
  -- `q`'s front at the label
  have FQ : ∃ Fq0 : List Pole, FrontBlk gS g2 e.1 Fq0 ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
        FrontSG (Map := Map) Qq Need.none gS.re g2.re (suresAt nq.laz e.1) (Fq0.map (renPole (unproxy cf)))
          (suresAt tel e.1) := by
    by_cases hm : e.1 ∈ (entries tel).map Prod.fst
    · exact FSq e.1 hm
    · have hn : e.1 ∉ (entries nq.laz).map Prod.fst := fun hm' => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm'
        rcases (Fq.labs e' he').1 with h' | h'
        · exact hm (e1 ▸ h')
        · omega
      refine ⟨[], fun B fin hb => by rw [Fq.keep e.1 (by omega) hm, hb]; rfl, fun cf hcf => ?_⟩
      rw [suresAt_nil hn, suresAt_nil hm]
      exact cf_frontSG_nil Qq Need.none gS.re g2.re
  -- `p`'s front at the label
  have FP : ∃ Fp0 : List Pole, FrontBlk g2 g3 e.1 Fp0 ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
        FrontSG (Map := Map) Qp Need.none g2.re g3.re (suresAt np.laz e.1) (Fp0.map (renPole (unproxy cf)))
          (suresAt hed e.1) := by
    by_cases hm : e.1 ∈ (entries hed).map Prod.fst
    · exact FSp e.1 hm
    · have hn : e.1 ∉ (entries np.laz).map Prod.fst := fun hm' => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm'
        rcases (Fp.labs e' he').1 with h' | h'
        · exact hm (e1 ▸ h')
        · omega
      refine ⟨[], fun B fin hb => by rw [Fp.keep e.1 (by omega) hm, hb]; rfl, fun cf hcf => ?_⟩
      rw [suresAt_nil hn, suresAt_nil hm]
      exact cf_frontSG_nil Qp Need.none g2.re g3.re
  obtain ⟨Fq0, hbq, hfq⟩ := FQ
  obtain ⟨Fp0, hbp, hfp⟩ := FP
  -- the blocks
  have hbS : FrontBlk g0 gS e.1 (PS e.1) := fun B fin hb => by
    rw [PPS.get, ch_emitted_ne _ _ (by omega), hb]; simp [preBody]
  have hbC : FrontBlk g3 g1 e.1 (PC e.1) := fun B fin hb => by
    rw [PPC.get, ch_emitted_ne _ _ (by omega), hb]; simp [preBody]
  refine ⟨PC e.1 ++ (Fp0 ++ (Fq0 ++ PS e.1)), FrontBlk.trans (FrontBlk.trans (FrontBlk.trans hbS hbq) hbp) hbC,
    fun cf hcf => ?_⟩
  have renC : (PC e.1).map (renPole (unproxy cf)) = PC e.1 :=
    renOps_fix (P := fun x => x < g1.re ∧ HoonMap.get g1.cond x = Option.none)
      (fun x hx => unproxy_none (by rw [hcf x hx.1]; exact hx.2)) regsC
  have renS : (PS e.1).map (renPole (unproxy cf)) = PS e.1 :=
    renOps_fix (P := fun x => x < gS.re ∧ HoonMap.get g0.cond x = Option.none)
      (fun x hx => unproxy_none (by
        have h1 := hx.1
        rw [hcf x (by omega), c10 x h1]; exact hx.2)) regsS
  have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk => by
    rw [hcf k (by omega), cd1]
  have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk => by
    rw [hcf k (by omega), cd1, c32 k hk]
  rw [List.map_append, List.map_append, List.map_append, renC, renS, ← List.append_assoc, ← List.append_assoc]
  exact frontSG_consG (hfp cf hcf3) (hfq cf hcf2) r0 r1 r2 r3 Fp.dreg Fq.dreg hLh hLt hht
    (fun M hM r hr => (Creg M hM).2 r hr) Cfit Crun Sfit Srun

end Comp
end SkaModel
end Formalization
