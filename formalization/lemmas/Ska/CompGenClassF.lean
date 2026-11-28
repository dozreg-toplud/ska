import lemmas.Ska.CompGenClassE
import lemmas.Ska.CompGenClassA

/-!
# The class with the state-level fronts: `NextGCS`

README Gaps 12.39, item 12.  The finding of `CompGenClassE.lean`: the parts'
`FrontLG` do not give the cons's, the state-level `FrontSG` does
(`frontSG_consG`).  So the class carries, beside `NextGC`'s clauses,
`FrontsSG`: at every goal label, ops in front of the block (`FrontBlk`) whose
renamed form is a `FrontSG` from the result's needs at the label to the
goal's (the `x = false`, no re-pointing form).  `[0 axe]` (`closedS_n0`:
no op, the moved needs read the same registers), `[1 k]` (`closedS_n1`: the
pieces of `+mede`, each keeping every register outside its need and the
run's range, `cf_mede_list`) and `[7 p q]` (`closedS_n7`, by `frontSG_seven`:
`q`'s front then `p`'s, `p`'s empty at a label that is no entry of `q`'s
result) are in it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The state-level fronts at every goal label** (`x = false`, no
re-pointing). -/
def FrontsSG (Q : Wit) (g0 g1 : Gen Map) (L : Lazy S) (nex : NextL S) : Prop :=
  ∀ a ∈ (entries L).map Prod.fst, ∃ F : List Pole, FrontBlk g0 g1 a F ∧
    ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      FrontSG (Map := Map) Q Need.none g0.re g1.re (suresAt nex.laz a) (F.map (renPole (unproxy cf)))
        (suresAt L a)

/-- **The class `NextGC` with the state-level fronts.** -/
abbrev NextGCS (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    PremG (Map := Map) L th g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ Q : Wit, RunOKGen lib N P f L th Q false g0 g1 nex ∧ GrowU g0 g1 ∧
      (∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a) ∧ ResG (Map := Map) L g0 g1 nex.laz ∧
      FrontsSG (Map := Map) Q g0 g1 L nex

theorem NextGCS.toGC {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : NextGCS (S := S) (Map := Map) lib N env P f nm) : NextGC (S := S) (Map := Map) lib N env P f nm :=
  fun H hr => let ⟨Q, R, g, n, r, _⟩ := h H hr; ⟨Q, R, g, n, r⟩

/-- The empty front between empty conjunctions. -/
theorem cf_frontSG_nil (Q : Wit) (E : Need) (lo0 lo : Nat) :
    FrontSG (S := S) (Map := Map) Q E lo0 lo [] [] [] :=
  ⟨fun _ h => by simp at h, fun _ _ _ _ _ _ _ _ h => by simp at h, fun _ _ _ _ _ _ _ h => by simp at h,
    fun lib σ O c gul st t R s v d w _ _ _ _ =>
      ⟨fun _ => ⟨R, Runs.nil R, fun _ h => by simp at h, fun _ _ _ => rfl⟩, fun ⟨_, h, _⟩ => by simp at h⟩⟩

/-! ## `[7 p q]` -/

/-- **The state-level fronts compose for `[7 p q]`**: at a goal label the
block holds `p`'s front `Fp` (from `p`'s result needs `Lp` to `q`'s `Lm`)
then `q`'s `Fq` (from `Lm` to the goal's `Ls`); `q`'s run from `lo0` to
`lo1`, `p`'s to `lo2`. -/
theorem frontSG_seven {Qp Qq : Wit} {lo0 lo1 lo2 : Nat} {Lp Lm Ls : List (Sure S)} {Fp Fq : List Pole}
    (FP : FrontSG (Map := Map) Qp Need.none lo1 lo2 Lp Fp Lm)
    (FQ : FrontSG (Map := Map) Qq Need.none lo0 lo1 Lm Fq Ls) (o1 : lo0 ≤ lo1) (o2 : lo1 ≤ lo2)
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r ∧ r < lo2)
    (hdq : ∀ s v d w r, Qq s v d w → NMem d r → lo0 ≤ r ∧ r < lo1) :
    FrontSG (Map := Map) (sevenWit Qp Qq) Need.none lo0 lo2 Lp (Fp ++ Fq) Ls := by
  refine ⟨fun L' hL' r hr => ?_, fun s v d w hq r hr L' hL' hm => ?_, fun s v d w hq fit => ?_,
    fun lib σ O c gul st t R s v d w hq hLp hd hE => ?_⟩
  · obtain ⟨h1, h2⟩ := FP.loc L' hL' r hr
    refine ⟨h1, fun h0 => ?_⟩
    obtain ⟨M, hM, hm⟩ := h2 (by omega)
    exact (FQ.loc M hM r hm).2 h0
  · obtain ⟨u, dp, wp, dq, wq, hp, hq', rfl, rfl⟩ := hq
    rcases hr with hr | hr
    · exact FP.dis s u dp wp hp r hr L' hL' hm
    · have := hdq u v dq wq r hq' hr
      obtain ⟨M, hM, hm'⟩ := (FP.loc L' hL' r hm).2 (by omega)
      exact FQ.dis u v dq wq hq' r hr M hM hm'
  · obtain ⟨u, dp, wp, dq, wq, hp, hq', rfl, rfl⟩ := hq
    exact FP.fit s u dp wp hp (FQ.fit u v dq wq hq' fit)
  · obtain ⟨u, dp, wp, dq, wq, hp, hq', rfl, rfl⟩ := hq
    have hdp' : HoldsN dp R wp := hd.1
    have hdq' : HoldsN dq R wq := hd.2
    have R1spec := FP.run lib σ O c gul st t R s u dp wp hp hLp hdp' trivial
    have after : (∀ M ∈ Lm, FitsS M u) → ∃ R1, Runs lib O c gul st t Fp R R1 ∧ (∀ M ∈ Lm, HoldsS M R1 u) ∧
        (∀ x, (x < lo1 ∨ lo2 ≤ x ∨ NMem dp x) → (∀ M ∈ Lm, ¬ NMem M.ned x) →
          SkaModel.read x R1 = SkaModel.read x R) ∧ HoldsN dq R1 wq := fun fm => by
      obtain ⟨R1, r1, h1, k1⟩ := R1spec.1 fm
      exact ⟨R1, r1, h1, k1, HoldsN.agree dq (fun x hx => k1 x (Or.inl (hdq u v dq wq x hq' hx).2)
        (fun M hM => FQ.dis u v dq wq hq' x hx M hM)) hdq'⟩
    refine ⟨fun fit => ?_, fun nf => ?_⟩
    · obtain ⟨R1, r1, h1, k1, d1⟩ := after (FQ.fit u v dq wq hq' fit)
      obtain ⟨R2, r2, h2, k2⟩ := (FQ.run lib σ O c gul st t R1 u v dq wq hq' h1 d1 trivial).1 fit
      refine ⟨R2, r1.append r2, h2, fun x hx hnx => ?_⟩
      have k2x : SkaModel.read x R2 = SkaModel.read x R1 := by
        refine k2 x ?_ hnx
        rcases hx with hx | hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inl (hdp s u dp wp x hp hx).1)
        · exact Or.inr (Or.inr hx)
      rw [k2x]
      refine k1 x ?_ (fun M hM hm => ?_)
      · rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
        · exact Or.inl (hdq u v dq wq x hq' hx).2
      · have hl := FQ.loc M hM x hm
        rcases hx with hx | hx | hx | hx
        · obtain ⟨L, hL, hm'⟩ := hl.2 hx
          exact hnx L hL hm'
        · omega
        · have := (hdp s u dp wp x hp hx).1; omega
        · exact FQ.dis u v dq wq hq' x hx M hM hm
    · by_cases fm : ∀ M ∈ Lm, FitsS M u
      · obtain ⟨R1, r1, h1, k1, d1⟩ := after fm
        exact Crashes.append_right r1 ((FQ.run lib σ O c gul st t R1 u v dq wq hq' h1 d1 trivial).2 nf)
      · have : ∃ M ∈ Lm, ¬ FitsS M u :=
          Classical.byContradiction fun ne => fm fun M hM => Classical.byContradiction fun nf' => ne ⟨M, hM, nf'⟩
        exact Crashes.append_left (R1spec.2 this)

/-- **`[7 p q]` is in `NextGCS`** when both parts are, at every `P`. -/
theorem closedS_n7 (lib : Lib) (N : Needs) (env : CallEnv) {fb fc : Noun} {p q : Nomm}
    (Hp : ∀ P, NextGCS (S := S) (Map := Map) lib N env P fb p)
    (Hq : ∀ P, NextGCS (S := S) (Map := Map) lib N env P fc q) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q) := by
  intro P sup region g0 g2 L th nex H h
  rw [runLC_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  obtain ⟨Qq, Rq, guq, nrq, Resq, FSq⟩ := Hq (Img lib P fb) H h1
  simp only [NextL.goal] at h2
  have hta : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · have e' : nx.th = th := e
      rw [e']; exact H.ta
  have Hp' : PremG (Map := Map) nx.laz nx.th g1 :=
    { goal := Rq.toFrameG.goalOut H.goal, nc := Rq.ncond, ec := Rq.econd, lu := Resq.lu, cl := Resq.cl,
      ecl := Resq.ecl, sa := Resq.sa, ta := hta, bo := Nat.le_trans H.bo Rq.bo, drop := Rq.drop.trans H.drop,
      up := guq.up H.up, clr := H.clr.growU guq, cb := Rq.cfr.below H.cb }
  obtain ⟨Qp, Rp, gup, nrp, Resp, FSp⟩ := Hp P Hp' h2
  have hre1 := Rq.re
  have hre2 := Rp.re
  have hbo1 := Rq.bo
  refine ⟨sevenWit Qp Qq, runOKGen_sevenGF Rq Rp gup nrp H.goal.sregs (fun e he => (H.goal.lab e he).2.1),
    guq.trans gup, ca_not_repoint H.goal H.up (guq.trans gup), ⟨Resp.lu, Resp.cl, Resp.ecl, Resp.sa, ?_⟩, ?_⟩
  · intro e he r hr
    rcases Resp.eat e he r hr with ⟨e0, he0, hl0, hm0⟩ | hs | hf
    · rcases Resq.eat e0 he0 r hm0 with ⟨e1, he1, hl1, hm1⟩ | hs1 | hf1
      · exact Or.inl ⟨e1, he1, hl1.trans hl0, hm1⟩
      · exact Or.inr (Or.inl hs1)
      · exact Or.inr (Or.inr ⟨hf1.1, by omega⟩)
    · rcases Rq.regs r hs with hs1 | hf1
      · exact Or.inr (Or.inl hs1)
      · exact Or.inr (Or.inr ⟨hf1.1, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, hf.2⟩)
  · intro a ha
    have hal : a < g0.bo := by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact (H.goal.lab e he).2.1
    obtain ⟨Fq, hbq, hfq⟩ := FSq a ha
    have cfq : ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
        ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun cf hcf k hk => by
      rw [hcf k (by omega)]
      rcases Rp.cfr.2 k with e | e
      · exact e
      · omega
    by_cases hm : a ∈ (entries nx.laz).map Prod.fst
    · obtain ⟨Fp, hbp, hfp⟩ := FSp a hm
      refine ⟨Fp ++ Fq, FrontBlk.trans hbq hbp, fun cf hcf => ?_⟩
      rw [List.map_append]
      exact frontSG_seven (hfp cf hcf) (hfq cf (cfq cf hcf)) hre1 hre2 (fun s v d w r hq hr => Rp.dreg s v d w r hq hr)
        (fun s v d w r hq hr => Rq.dreg s v d w r hq hr)
    · have hbp : FrontBlk g1 g2 a [] := fun B fin hb => by
        rw [Rp.keep a (by omega) hm, hb]; rfl
      have hn : a ∉ (entries nex.laz).map Prod.fst := fun hm' => by
        obtain ⟨e, he, e1⟩ := List.mem_map.mp hm'
        rcases (Rp.labs e he).1 with h' | h'
        · exact hm (e1 ▸ h')
        · omega
      refine ⟨[] ++ Fq, FrontBlk.trans hbq hbp, fun cf hcf => ?_⟩
      rw [List.map_append, suresAt_nil hn]
      have F0 : FrontSG (Map := Map) Qp Need.none g1.re g2.re [] ([] : List Pole) (suresAt nx.laz a) := by
        rw [suresAt_nil hm]; exact cf_frontSG_nil Qp Need.none g1.re g2.re
      exact frontSG_seven F0 (hfq cf (cfq cf hcf)) hre1 hre2 (fun s v d w r hq hr => Rp.dreg s v d w r hq hr)
        (fun s v d w r hq hr => Rq.dreg s v d w r hq hr)

/-! ## `[0 axe]` -/

/-- **The front of `[0 axe]` at one label**: no op; the moved needs read
the registers of the needs at the label. -/
theorem cf_frontSG_n0 {axe : Nat} {ps : List (Sure S × Sure S)} {lo : Nat} (W : Noun → Noun)
    (hp : ∀ p ∈ ps, fromSure axe p.1 = some p.2) (hlo : ∀ p ∈ ps, ∀ r, NMem p.1.ned r → r < lo) :
    FrontSG (Map := Map) (pureWit (Nomm.n0 axe) (fun _ => Need.none) W) Need.none lo lo (ps.map Prod.snd) []
      (ps.map Prod.fst) := by
  refine ⟨fun L' hL' r hr => ?_, fun s v d w hq r hr => ?_, fun s v d w hq fit L' hL' => ?_,
    fun lib σ O c gul st t R s v d w hq hLp hd hE => ?_⟩
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL'
    obtain ⟨_, _, _, hmem⟩ := fromSure_spec (Map := Map) (hp p hp')
    exact ⟨hlo p hp' r (hmem r hr), fun _ => ⟨p.1, List.mem_map.mpr ⟨p, hp', rfl⟩, hmem r hr⟩⟩
  · obtain ⟨_, rfl, _⟩ := hq
    exact hr.elim
  · obtain ⟨hv, _, _⟩ := hq
    simp only [pureEval] at hv
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL'
    obtain ⟨_, _, hfit, _⟩ := fromSure_spec (Map := Map) (hp p hp')
    exact hfit s v hv (fit p.1 (List.mem_map.mpr ⟨p, hp', rfl⟩))
  · obtain ⟨hv, _, _⟩ := hq
    simp only [pureEval] at hv
    have hold : ∀ L ∈ ps.map Prod.fst, HoldsS L R v := fun L hL => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hL
      obtain ⟨_, hhold, _, _⟩ := fromSure_spec (Map := Map) (hp p hp')
      obtain ⟨q, hq, hh⟩ := hhold R s (hLp p.2 (List.mem_map.mpr ⟨p, hp', rfl⟩))
      rw [hv] at hq; cases hq; exact hh
    refine ⟨fun _ => ⟨R, Runs.nil R, hold, fun _ _ _ => rfl⟩, fun ⟨L, hL, nf⟩ => ?_⟩
    exact absurd (ce_holdsS_fits (hold L hL)) nf

/-- **`[0 axe]` is in `NextGCS`** (`axe ≥ 2`), at every `P`. -/
theorem closedS_n0 (lib : Lib) (N : Needs) (env : CallEnv) {a : Nat} (ha : 2 ≤ a) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (slot a) (Nomm.n0 a) := by
  intro P sup region g0 g1 L th nex H h
  rw [runLC_n0_next_from env sup ha] at h
  obtain ⟨L', hf, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have M0 : MinkEq lib P (slot a) (Nomm.n0 a) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 a).annot P) hs gul tm r
  refine ⟨_, runOKGen_n0 (N := N) lib M0 hf H.goal H.nc H.ec id, GrowU.refl _, fun _ _ => not_repointG_refl,
    ca_resG_fromL hf H.lu H.cl H.ecl H.sa, fun o ho => ⟨[], fun B fin hb => by simpa using hb, fun cf _ => ?_⟩⟩
  have E := fromL_ent a _ _ hf
  obtain ⟨ps, h1, h2, h3⟩ := E.pairsAt o
  have F := cf_frontSG_n0 (Map := Map) (lo := g0.re) id h3 (fun p hp r hr => by
    have hm : p.1 ∈ atL (entries L) o := h1 ▸ List.mem_map_of_mem hp
    obtain ⟨e, he, _, e2⟩ := mem_suresAt hm
    exact (H.goal.eregs e he).2 r (e2 ▸ hr))
  rw [h1, h2] at F
  exact F

/-! ## `[1 k]` -/

section Mede
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

/-- **The pieces of `+mede` at one label, in sequence**: each writes `k`
into its need, keeping every register outside its need and the run's
range; needs below `lo` and pairwise apart. -/
theorem cf_mede_list {k : Noun} {lo hi a : Nat} : ∀ (As : List (Sure S × List Pole)),
    (∀ p ∈ As, MedeP (Map := Map) k lo hi a p.1 p.2) →
    (∀ p ∈ As, Distinct p.1.ned ∧ ∀ r, NMem p.1.ned r → r < lo) →
    (As.map Prod.fst).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) →
    ∀ R : Map (Option Noun),
    ((∀ p ∈ As, FitsS p.1 k) → ∃ R', Runs lib O c gul st t (As.map Prod.snd).flatten R R' ∧
      (∀ p ∈ As, HoldsS p.1 R' k) ∧
      ∀ y, (∀ p ∈ As, ¬ NMem p.1.ned y) → ¬ (lo ≤ y ∧ y < hi) → SkaModel.read y R' = SkaModel.read y R) ∧
    ((∃ p ∈ As, ¬ FitsS p.1 k) → Crashes lib O c gul st t (As.map Prod.snd).flatten R)
  | [], _, _, _, R => ⟨fun _ => ⟨R, Runs.nil R, fun _ h => by simp at h, fun _ _ _ => rfl⟩,
      fun ⟨_, h, _⟩ => by simp at h⟩
  | p :: As, hP, hD, hW, R => by
    simp only [List.map_cons, List.flatten_cons]
    rw [List.map_cons, List.pairwise_cons] at hW
    obtain ⟨S1, S2⟩ := hP p List.mem_cons_self lib σ O c gul st t R (hD p List.mem_cons_self).1
      (hD p List.mem_cons_self).2
    have ih := cf_mede_list As (fun q hq => hP q (List.mem_cons_of_mem _ hq))
      (fun q hq => hD q (List.mem_cons_of_mem _ hq)) hW.2
    refine ⟨fun f => ?_, fun ⟨q, hq, nf⟩ => ?_⟩
    · obtain ⟨R1, r1, hh1, k1⟩ := S1 (f p List.mem_cons_self)
      obtain ⟨R2, r2, hh2, k2⟩ := (ih R1).1 (fun q hq => f q (List.mem_cons_of_mem _ hq))
      refine ⟨R2, r1.append r2, fun q hq => ?_, fun y hy hr => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · refine ⟨HoldsN.agree _ (fun x hx => k2 x (fun q' hq' => hW.1 q'.1 (List.mem_map_of_mem hq') x hx)
            (fun ⟨a1, _⟩ => by have := (hD q List.mem_cons_self).2 x hx; omega)) hh1.1, hh1.2⟩
        · exact hh2 q hq'
      · rw [k2 y (fun q hq => hy q (List.mem_cons_of_mem _ hq)) hr, k1 y (hy p List.mem_cons_self) hr]
    · by_cases f1 : FitsS p.1 k
      · obtain ⟨R1, r1, _, _⟩ := S1 f1
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact absurd f1 nf
        · exact Crashes.append_right r1 ((ih R1).2 ⟨q, hq', nf⟩)
      · exact Crashes.append_left (S2 f1)

end Mede

/-- **The state-level fronts of `[1 k]`**: the text of `runOKGen_n1` to the
pieces at every goal label, then `cf_mede_list`. -/
theorem cf_frontsSG_n1 {k : Noun} {env : CallEnv} {sup : Option Nomm} {L : Lazy S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (G : GoalG (Map := Map) L th g0)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none)
    (d0 : g0.drop = false) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n1 k) (CGoalL.next L th) region g0 = some (nex, g1)) (W : Noun → Noun) :
    FrontsSG (Map := Map) (pureWit (Nomm.n1 k) (fun _ => Need.none) W) g0 g1 L nex := by
  rw [runLC_n1_nextOne] at h
  simp only [medeL_eq, bind_apply, emit_apply, Option.bind_some, get_apply] at h
  simp only [emitted_drop, d0, Bool.false_eq_true, if_false] at h
  obtain ⟨⟨o', gW⟩, hX, hP⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, g3, hW, h5⟩ := bind_some hX
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5 hP
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g0.emitted ⟨[], [], Termin.hop th⟩ := ⟨_, rfl⟩
  rw [← hgE] at hW
  have dE : gE.drop = false := by simp [hgE, emitted_drop, d0]
  have oE : ∀ o, o ≠ g0.bo → HoonMap.get gE.blocks o = HoonMap.get g0.blocks o := fun o ho => by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put, ho]
  have nlab : g0.bo ∉ (entries L).map Prod.fst := fun hm => by
    obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (G.lab e he).2.1; omega
  have W' := medeWalk_okL k hW dE
  have reE : gE.re = g0.re := by rw [hgE]; rfl
  have kE : gE.cond = g0.cond := by rw [hgE]; rfl
  have c3 : g3.cond = g0.cond := W'.cnd.trans kE
  have le3 : g0.re ≤ g3.re := reE ▸ W'.le
  have cond0 : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g0.cond x with
    | none => rfl
    | some _ => have := hcb x (by simp [e]); omega
  have fix : ∀ cf : Map (Nat × List Nat), (∀ kk, kk < g3.re → HoonMap.get cf kk = HoonMap.get g3.cond kk) →
      ∀ (A : List Pole), RegsIn (fun x => (x < g0.re ∧ HoonMap.get g0.cond x = Option.none) ∨
        (gE.re ≤ x ∧ x < g3.re)) A → A.map (renPole (unproxy cf)) = A :=
    fun cf hcf A hA => renOps_fix (P := fun x => (x < g0.re ∧ HoonMap.get g0.cond x = Option.none) ∨
        (gE.re ≤ x ∧ x < g3.re))
      (fun x hx => unproxy_none (by
        rcases hx with ⟨a, b⟩ | ⟨a, b⟩
        · rw [hcf x (by omega), c3]; exact b
        · rw [hcf x b, c3]; exact cond0 x (by omega))) hA
  have pieceR : ∀ (o : Nat) (p : Sure S × List Pole), (∃ e ∈ entries L, e.2.sure = p.1) ∨ p.1 = L.sure →
      MedePR (Map := Map) k gE.re g3.re o p.1 p.2 →
      RegsIn (fun x => (x < g0.re ∧ HoonMap.get g0.cond x = Option.none) ∨ (gE.re ≤ x ∧ x < g3.re)) p.2 :=
    fun o p hp hP => hP.2.mono fun x hx => by
      rcases hx with hx | hx
      · rcases hp with ⟨e, he, h2⟩ | h2
        · rw [← h2] at hx; exact Or.inl ⟨(G.eregs e he).2 x hx, hec e he x hx⟩
        · rw [h2] at hx; exact Or.inl ⟨G.sregs x hx, hnc x hx⟩
      · exact Or.inr hx
  have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
  intro a ha
  have hab : a ≠ g0.bo := fun e => nlab (e ▸ ha)
  obtain ⟨As, hA, pA, qA⟩ := W'.at_ a
  rw [atL_cons_of_neOne (fun e => hab e.symm)] at pA
  have pA' : (As.map Prod.fst).Perm (suresAt L a) := pA
  refine ⟨_, fun B fin hb => hA B fin (by rw [oE a hab]; exact hb), fun cf hcf => ?_⟩
  have memE : ∀ p ∈ As, ∃ e ∈ entries L, e.1 = a ∧ e.2.sure = p.1 := fun p hp =>
    mem_suresAt (pA'.mem_iff.mp (List.mem_map_of_mem hp))
  rw [fix cf hcf _ (regsIn_flattenOne As fun p hp => pieceR a p
    (let ⟨e, he, _, h2⟩ := memE p hp; Or.inl ⟨e, he, h2⟩) (qA p hp))]
  have hs0 : suresAt (ofSure (Sure.bunt : Sure S)) a = [] := by simp [suresAt, e0]
  rw [hs0]
  have hD : ∀ p ∈ As, Distinct p.1.ned ∧ ∀ r, NMem p.1.ned r → r < g0.re := fun p hp => by
    obtain ⟨e, he, _, h2⟩ := memE p hp
    rw [← h2]; exact G.eregs e he
  have hPW : (As.map Prod.fst).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) :=
    (List.Perm.pairwise_iff (fun {L1 L2} hr r h1 h2 => hr r h2 h1) pA').mpr (labDisj_at G.labDisj a)
  have hM : ∀ p ∈ As, MedeP (Map := Map) k g0.re g3.re a p.1 p.2 := fun p hp => by
    have := (qA p hp).1; rw [reE] at this; exact this
  have mem' : ∀ L0, L0 ∈ suresAt L a ↔ ∃ p ∈ As, p.1 = L0 := fun L0 => by
    rw [← pA'.mem_iff, List.mem_map]
  refine ⟨fun _ h => by simp at h, fun _ _ _ _ _ _ _ _ h => by simp at h, fun _ _ _ _ _ _ _ h => by simp at h,
    fun lib σ O c gul st t R s v d w hq _ _ _ => ?_⟩
  obtain ⟨hv, rfl, rfl⟩ := hq
  simp only [pureEval, Option.some.injEq] at hv
  subst hv
  have ML := cf_mede_list (lib := lib) (O := O) (c := c) (gul := gul) (st := st) (t := t) As hM hD hPW R
  refine ⟨fun fit => ?_, fun ⟨L0, hL0, nf⟩ => ML.2 ?_⟩
  · obtain ⟨R', r', hh, kk⟩ := ML.1 (fun p hp => fit p.1 ((mem' p.1).mpr ⟨p, hp, rfl⟩))
    refine ⟨R', r', fun L0 hL0 => ?_, fun x hx hn => kk x (fun p hp hm => hn p.1 ((mem' p.1).mpr ⟨p, hp, rfl⟩) hm)
      (fun ⟨a1, a2⟩ => ?_)⟩
    · obtain ⟨p, hp, rfl⟩ := (mem' L0).mp hL0
      exact hh p hp
    · rcases hx with hx | hx | hx
      · omega
      · omega
      · exact hx.elim
  · obtain ⟨p, hp, rfl⟩ := (mem' L0).mp hL0
    exact ⟨p, hp, nf⟩

/-- **`[1 k]` is in `NextGCS`**, at every `P`. -/
theorem closedS_n1 (lib : Lib) (N : Needs) (env : CallEnv) (k : Noun) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (quote k) (Nomm.n1 k) := by
  intro P sup region g0 g1 L th nex H h
  have M1 : MinkEq lib P (quote k) (Nomm.n1 k) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 k).annot P) hs gul tm r
  have FS := cf_frontsSG_n1 H.goal H.nc H.ec H.drop H.cb h id
  obtain ⟨hn, R, hgu, hnr⟩ := runOKGen_n1 (N := N) lib M1 H.goal H.nc H.ec H.drop H.up H.cb H.ta h id
  subst hn
  exact ⟨_, R, hgu, hnr, ca_resG_ofSure (by simp [Sure.bunt, Clean]), FS⟩

end Comp
end SkaModel
end Formalization
