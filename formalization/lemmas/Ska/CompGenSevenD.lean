import lemmas.Ska.CompGenSixD
import lemmas.Ska.CompGenLeaf

/-!
# `[7 p q]` under `%done` in the new relation

README Gaps 12.39, item 10.  `runOKGD_sevenG`: `RunOKGD` of `q` under any
goal and `RunOKGen` of `p` at `q`'s result (labels possibly repeated, entry
blocks with bodies) give `RunOKGD` of `[7 p q]`, for a `p` that only fronts
`q`'s labels (`x = false`, no re-pointing, `GrowU`): the text of
`runOKGB_sevenL` with `q`'s agreement taken per label from the whole's and
`p`'s `FrontLG`.  With `runOKGen_n0_at` and `six_doneGD`: the contract of
`[7 [0 axe] q]` for `q` the `%6` with a calling test, whose result repeats
its labels (`seven0_doneGD`, `seven0Six_contract`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- A run that adds no block re-points nothing. -/
theorem not_repointG_refl {g : Gen Map} {a : Nat} : ¬ RepointG g g a := by
  rintro ⟨B, fin, F, o1, o2, F2, _, _, h1, h2, _⟩
  omega

/-- **`[7 p q]` under any goal, in the new relation**: `RunOKGD` of `q`
(labels possibly repeated) and `RunOKGen` of `p` at `q`'s result, `p`
reading no goal register, adding blocks as `GrowU` does and re-pointing none
of `q`'s entries, give `RunOKGD` of the whole.  `q`'s agreement at a label
comes from the whole's at that label and `p`'s `FrontLG` there. -/
theorem runOKGD_sevenG {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    {goal : CGoal S} {Qp : Wit} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGD (Map := Map) lib N (Img lib P fb) fc goal g0 g1 nx)
    (Rp : RunOKGen (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hgu : GrowU g1 g2) (hnr : ∀ a ∈ (entries nx.laz).map Prod.fst, ¬ RepointG g1 g2 a)
    (hg : ∀ r, GMem goal r → r < g0.re) :
    RunOKGD lib N P f goal g0 g2 nex := by
  have q1 := Rq.ext.1
  have q2 := Rq.ext.2.1
  have p1 := Rp.re
  have p2 := Rp.bo
  have qhi := Rq.hi
  have qlab : ∀ o, o ∈ (entries nx.laz).map Prod.fst → g0.bo ≤ o ∧ o < g1.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    have := (Rq.labs e he).2.1
    exact ⟨(Rq.labs e he).1, by omega⟩
  have plab : ∀ o, o ∈ (entries nex.laz).map Prod.fst → o ∈ (entries nx.laz).map Prod.fst ∨ g1.bo ≤ o :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Rp.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
  have nxL : ∀ r, NMem nx.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases Rq.regs r hr with h | h
    · have := hg r h; omega
    · exact h.2
  have hdp : ∀ s v d w r, Qp s v d w → NMem d r → g1.re ≤ r ∧ r < g2.re := Rp.dreg
  -- `p` only fronts `q`'s labels
  have pfr : ∀ o ∈ (entries nx.laz).map Prod.fst, ∃ F : List Pole, FrontBlk g1 g2 o F ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
        FrontLG (Map := Map) Qp (gsE false nx.laz) g1.re g2.re (suresAt nex.laz o)
          (F.map (renPole (unproxy cf))) (suresAt nx.laz o) := fun o ho => by
    rcases Rp.front o ho with h | ⟨h, _⟩
    · exact h
    · exact absurd h (hnr o ho)
  -- the shared part of the two `sem` clauses
  have core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun),
      (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g2 nex.laz s0 s) →
      (∀ x, NMem ned x → g2.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 →
      (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g1 g2 nex.laz s0 s) ∧
      ∀ (u : Noun) (st' : σ) (R1 : Map (Option Noun)) (dp : Need) (wp : Noun), Qp s u dp wp → Inv st' →
        ν st ≤ ν st' → FitsS nx.laz.sure u → HoldsN nx.laz.sure.ned R1 u → HoldsN dp R1 wp →
        (∀ x, ((x < g1.re ∨ NMem ned x) ∧ ¬ NMem nx.laz.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs) →
        (∀ (st'' : σ) (t'' : Trace), AgreeG lib O c gul st'' t'' cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u) ∧
        (∀ x, NMem (Need.pair ned dp) x → g1.re ≤ x) ∧ HoldsS nx.laz.sure R1 u ∧
        HoldsN (Need.pair ned dp) R1 (C s0 wp) ∧
        ∀ r, GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem (Need.pair ned dp) x) ∧ ¬ GMem goal x)
            st' R1 t tm nx.th goal r →
          goJ lib O c gul st regs t nex.th = goJ lib O c gul st' R1 t nx.th →
          GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm
            nex.th goal r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    refine ⟨fun st' t' => ⟨fun o l u hnl => (ag st' t').1 o (by omega) u hnl,
      fun o ho l => (ag st' t').2 o ho (by omega)⟩,
      fun u st' R1 dp wp hqp hI' hν fit h1 hD1 k1 => ?_⟩
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
      have := nxL x hm; have := hned x hx; omega⟩) hn
    refine ⟨fun st'' t'' => ⟨fun o l u' hnl => ?_, fun o ho l => ?_⟩,
      fun r hr => hr.elim (fun h => by have := hned r h; omega) (fun h => (hdp s u dp wp r hqp h).1),
      ⟨h1, fit.2⟩, ⟨hn1, hD1⟩, fun r G e1 => ?_⟩
    · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
        rcases plab o hm with h | h
        · exact hnl h
        · omega
      rw [(ag st'' t'').1 o l (by omega) hn2, Rp.keep o u' hnl]
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      obtain ⟨hge, _, Bq, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := by have := (Rq.labs e he).2.1; omega
      obtain ⟨Fp, hFp, FL⟩ := pfr e.1 ho
      have hb2 := hFp Bq (Termin.hop th') hb1
      have FP := FL cf hcf
      by_cases hm : e.1 ∈ (entries nex.laz).map Prod.fst
      · obtain ⟨A0, B2, th'', hb3, hc3, hf3⟩ := (ag st'' t'').2 e.1 hm (by omega)
        rw [hb2] at hb3
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
        obtain ⟨rfl, rfl⟩ := hb3
        refine ⟨A0 ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, by rw [hc3]; simp, ?_⟩
        exact (FP lib σ O c gul st'' t'' ned A0 s0 s u dp wp hned hqp hf3).conv (N1 := Need.pair ned dp)
          (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))
      · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, ?_, ?_⟩
        · rw [(ag st'' t'').1 e.1 hge (by omega) hm, hb2]
          simp [unproxyBlob, renBlob, renFin]
        · have h0 : FillSemL lib O c gul st'' t'' ned g2.re (suresAt nex.laz e.1) [] s0 s := by
            rw [suresAt_nil hm]; exact fillSemL_nil_nil
          exact (FP lib σ O c gul st'' t'' ned [] s0 s u dp wp hned hqp h0).conv
            (N1 := Need.pair ned dp) (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))
    · refine goalSemCM_step hν (fun x hx => k1 x ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hm => ?_⟩) e1
        goal r (goalSemCM_monoK (fun x hx => ⟨hx.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hx.2⟩) goal r G)
      rcases Rq.regs x hm with h | h
      · exact hx.2 h
      · rcases hx.1 with h' | h'
        · omega
        · have := hned x h'; omega
  refine ⟨⟨by omega, by omega, Rp.drop.trans Rq.ext.2.2.1, fun o ho => ?_⟩, Rq.grow.trans hgu,
    Rq.cfr.trans Rp.cfr, Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ⟨(Rp.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ?_, Rp.labDisj, fun s hs hf => ?_, Rp.ncond, Rp.econd, ?_, ?_⟩
  · -- ext
    have hn' : o ∉ (entries nx.laz).map Prod.fst := fun hm => by have := (qlab o hm).1; omega
    exact (Rp.keep o (by omega) hn').trans (Rq.ext.2.2.2 o ho)
  · -- ent
    rcases Rp.ent with f | e
    · exact Or.inl f
    · have e' : nex.th = nx.th := e
      rw [e']
      rcases Rq.ent with f | e2
      · exact Or.inl (f.growU Rq.hi hgu)
      · exact Or.inr e2
  · -- regs
    rcases Rp.regs r hr with h | h
    · rcases Rq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · -- eregs
    rcases (Rp.eregs e he).2 r hr with ⟨e0, he0, h0⟩ | h | h
    · have := (Rq.eregs e0 he0).2 r h0
      exact ⟨this.1, by omega⟩
    · rcases Rq.regs r h with h' | h'
      · exact ⟨Or.inl h', by have := nxL r h; omega⟩
      · exact ⟨Or.inr h'.1, by omega⟩
    · exact ⟨Or.inr (by omega), h.2⟩
  · -- labs
    obtain ⟨h, blk⟩ := Rp.labs e he
    refine ⟨?_, ?_, blk⟩
    · rcases h with h | h
      · exact (qlab e.1 h).1
      · omega
    · rcases h with h | h
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
        have := (Rq.labs e0 he0).2.1
        rw [← e1]; omega
      · exact h.2
  · -- nec
    obtain ⟨N1, N2⟩ := Rp.nec s hs hf
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n1, _, rb, hb, h | ⟨u, rfl, n2, _, hc⟩⟩ := M.fwd hs hm
      · obtain ⟨hn, hr⟩ := h
        rw [hr]
        rcases N1 gul n1 tm rb hb with e | ⟨q, e, _⟩
        · exact Or.inl e
        · exact absurd e (hn q)
      · rcases N1 gul n1 tm _ hb with e | ⟨q, e, hq⟩
        · cases e
        · cases e
          exact (Rq.nec u (img_of hs hb) hq).1 gul n2 tm r hc
    · obtain ⟨rb, hb, hbad⟩ := N2 gul tm
      rcases hbad with e | ⟨u, rfl, hq⟩
      · subst e
        exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e), Or.inl rfl⟩
      · obtain ⟨r, hr, hbr⟩ := (Rq.nec u ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩ hq).2 gul tm
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, hbr⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    obtain ⟨n1, h1n, rb, hb, hr⟩ := M.fwd hs hm
    have Gp := Rp.sem cf hcf c ned σ Inv ν O n1 gul hN hS (oracleFwd_le hF h1n) st t tm s0 s rb hI htr hs hb agP
      hned regs hh hn
    rcases hr with ⟨hnz, hr⟩ | ⟨u, rfl, n2, h2n, hc⟩
    · rw [hr]
      exact goalSemCM_ret goal _ hnz (returnsC_of_goalSemCMD hnz Gp)
    by_cases fit : FitsS nx.laz.sure u
    · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
      obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
      exact fin r (Rq.sem cf hcf1 c (Need.pair ned dp) σ Inv ν O n2 gul hN hS (oracleFwd_le hF h2n)
        st' t tm (C s0 wp) u r hI' (frames_mono hν htr) (img_of hs hb) hc agQ hnQ R1 hsQ hnQ') e1
    · exact goalSemCM_of_badC ((Rq.nec u (img_of hs hb) fit).1 gul n2 tm r hc) (Gp.2 fit)
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    obtain ⟨rb, hb, Gp⟩ := Rp.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs agP hned regs hh hn
      res hres
    cases rb with
    | one q =>
      exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e),
        goalSemCM_ret goal _ (fun _ e => by cases e) (returnsC_of_goalSemCMD (fun _ e => by cases e) Gp)⟩
    | two t' =>
      exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e),
        goalSemCM_ret goal _ (fun _ e => by cases e) (returnsC_of_goalSemCMD (fun _ e => by cases e) Gp)⟩
    | zero u =>
      have hu : Img lib P fb u := ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩
      by_cases fit : FitsS nx.laz.sure u
      · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
        obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
        obtain ⟨r, hr, Gq⟩ := Rq.semB cf hcf1 c (Need.pair ned dp) σ Inv ν O gul hN hS hB st' t tm (C s0 wp) u hI'
          (frames_mono hν htr) hu agQ hnQ R1 hsQ hnQ' res (by rw [← e1]; exact hres)
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, fin r Gq e1⟩
      · obtain ⟨r, hr, hbad⟩ := (Rq.nec u hu fit).2 gul tm
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, goalSemCM_of_badC hbad (Gp.2 fit)⟩

/-! ## `[7 [0 axe] q]` -/

/-- The `%0` case of `run` under `%next L th` (`runLC_n0_nextT`). -/
theorem runLC_n0_nextG (env : CallEnv) (sup : Option Nomm) (ax : Nat) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.n0 ax) (CGoalL.next L th) region : CM Map (NextL S)) =
      if ax = 0 then bombL (some th.there) else (do
        let nex ← simpleNextL (CGoalL.next L th)
        if ax = 1 then pure nex else
        match fromL ax nex.laz with
        | some laz => pure ⟨laz, nex.th⟩
        | Option.none => fun _ => Option.none) := rfl

/-- **`[0 axe]` under `%next L th`** (the axis at least `2`): `+from`, no op. -/
theorem runLC_n0_next_from (env : CallEnv) (sup : Option Nomm) {axe : Nat} (ha : 2 ≤ axe) (L : Lazy S) (th : Jmp)
    (region : List Nat) (g : Gen Map) :
    (runLC env sup (Nomm.n0 axe) (CGoalL.next L th) region g : Option (NextL S × Gen Map)) =
      (fromL axe L).map fun l => (⟨l, th⟩, g) := by
  rw [runLC_n0_nextG]
  simp only [show axe ≠ 0 by omega, show axe ≠ 1 by omega, if_false, simpleNextL, bind_apply, pure_apply,
    Option.bind_some]
  cases fromL axe L <;> rfl

/-- **`[7 [0 axe] q]` under `%done`, `q` of `SixDG`** (a `%6`, any test, whose
result may repeat its labels): `RunOKGD` of the real result. -/
theorem seven0_doneGD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fq : Noun} {q : Nomm} {k : Nat}
    {axe : Nat} (ha : 2 ≤ axe) (Hq : SixDG (S := S) (Map := Map) lib N env (Img lib P (slot axe)) fq q k)
    {sup : Option Nomm} {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n7 (Nomm.n0 axe) q) (CGoalL.done : CGoalL S) region g0 = some (nex, g2)) :
    RunOKGD lib N P (n3 (A 7) (slot axe) fq) (CGoal.done : CGoal S) g0 g2 nex := by
  rw [runLC_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (Hq b0 d0 hu hcl hcb h1).1
  simp only [NextL.goal] at h2
  rw [runLC_n0_next_from env sup ha] at h2
  obtain ⟨L', hf, e⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have M0 : MinkEq lib P (slot axe) (Nomm.n0 axe) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 axe).annot P) hs gul tm r
  have Rp := runOKGen_n0_at (N := N) Rq b0 (fun r hr => hr.elim) M0 hf id
  exact runOKGD_sevenG (minkC7_seven lib P (slot axe) fq) Rq Rp (GrowU.refl _)
    (fun _ _ => not_repointG_refl) (fun r hr => hr.elim)

/-- **The contract of `[7 [0 axe] [6 [2 [0 3] [0 2]] [0 2] [0 2]]]`**, the
first through `[7 p q]` in the new relation: the `%6` with a calling test
leaves a result with repeated labels and entry blocks with bodies, which
`[0 axe]` moves under the axis. -/
theorem seven0Six_contract (lib : Lib) (env : CallEnv) {axe : Nat} (ha : 2 ≤ axe) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n7 (Nomm.n0 axe) (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2))) =
        some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 7) (slot axe) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2))) [s] c ∧
      ContractBwd lib N s (n3 (A 7) (slot axe) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2))) [s] c :=
  have H := finishLUC_contractGD (P := fun _ => True) lib N
    (fun hr => seven0_doneGD (S := S) (Map := Map) (N := N) lib env ha (sixDG_callTest lib N env _) (by simp [gen0]) rfl upBelow_gen0 clear_gen0
      condBelow_gen0 hr) hc
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
