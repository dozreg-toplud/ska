import lemmas.Ska.CompSimBodyLift

/-!
# `[7 p q]` with bodies at the entries: `runOKLB_seven`

README Gaps 12.23.  `runOKLC_seven` (`CompRunOKLCSeven.lean`) with
`RunOKLB`: `q` under `%next L th`, `p` under the goal `q`'s run returns,
whose entries may have bodies (the ops `q`'s parts put at its own bonds).
At a result entry of `q` that `p` kept, the program's block is `p`'s fill,
`p`'s front and `q`'s body; `p`'s fill and front together are the fill that
`q`'s `AgreeLB` asks for (`FrontLB` of `p`).  `p` must not read its goal's
sure registers in its fronts (`x = false`): those are `q`'s result's sure
registers, and nothing says `q`'s code keeps them until its entries' blocks
(README Gaps 12.23, (b)).  The whole has `q`'s flag.

* `FillSem.conv`: a fill from one input need is a fill from another that
  holds at least as much and names no other register above `lo`.
* `frontLB_seven`, `frontLB_seven_bunt`: the fronts compose.
* `runOKLB_seven`: both `sem` clauses through one `core`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A fill moves to another input need** that holds whenever the first
does, whose registers are the first's or below `lo`. -/
theorem FillSem.conv {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {N1 N2 : Need} {lo : Nat} {L : Sure S} {A : List Pole} {x1 x2 s : Noun}
    (h : FillSem (Map := Map) lib O c gul st t N2 lo L A x2 s) (hh : ∀ R : Map (Option Noun), HoldsN N1 R x1 → HoldsN N2 R x2)
    (hm : ∀ z, NMem N1 z → NMem N2 z ∨ z < lo) : FillSem lib O c gul st t N1 lo L A x1 s := by
  intro R hR
  obtain ⟨F1, F2⟩ := h R (hh R hR)
  refine ⟨fun f => ?_, F2⟩
  obtain ⟨R', r, hs, k⟩ := F1 f
  refine ⟨R', r, hs, fun z hz hn => k z ?_ hn⟩
  rcases hz with hz | hz
  · exact hm z hz
  · exact Or.inr hz

/-- **The fronts compose** (`frontLC_seven` for `FrontLB`), `p` reading no
goal register. -/
theorem frontLB_seven {Qp Qq : Wit} {E : Need} {lo0 lo1 lo2 : Nat} {Lp Lq M : Sure S} {Fp Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r) (h12 : lo1 ≤ lo2)
    (FP : FrontLB (Map := Map) Qp Need.none lo1 lo2 Lp Fp Lq) (FQ : FrontLB (Map := Map) Qq E lo0 lo1 Lq Fq M) :
    FrontLB (Map := Map) (sevenWit Qp Qq) E lo0 lo2 Lp (Fp ++ Fq) M := by
  intro lib σ O c gul st t ned A0 s0 s v d w hned hq hfill
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have h1 := (FP lib σ O c gul st t ned A0 s0 s u dp wp hned hp hfill).conv (x1 := C s0 wp)
    (N1 := Need.pair ned dp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))
  have h2 := FQ lib σ O c gul st t (Need.pair ned dp) (A0 ++ Fp) (C s0 wp) u v dq wq
    (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => hdp s u dp wp r hp h)) hqq h1
  rw [← List.append_assoc]
  refine h2.conv (fun R hR => ⟨⟨⟨hR.1.1, hR.1.2.1⟩, hR.1.2.2⟩, hR.2⟩) (fun z hz => ?_)
  rcases hz with (hz | hz | hz) | hz
  · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hz)))
  · exact Or.inl (Or.inl (Or.inr hz))
  · exact Or.inl (Or.inr hz)

/-- **A front of `q` at an entry that `p` does not see.** -/
theorem frontLB_seven_bunt {Qp Qq : Wit} {E : Need} {lo0 lo1 lo2 : Nat} {M : Sure S} {Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r ∧ r < lo2) (h12 : lo1 ≤ lo2)
    (FQ : FrontLB (Map := Map) Qq E lo0 lo1 Sure.bunt Fq M) :
    FrontLB (Map := Map) (sevenWit Qp Qq) E lo0 lo2 Sure.bunt Fq M := by
  intro lib σ O c gul st t ned A0 s0 s v d w hned hq hfill
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have h1 : FillSem lib O c gul st t (Need.pair ned dp) lo1 (Sure.bunt : Sure S) A0 (C s0 wp) u :=
    ((hfill.pair dp (fun r hr => (hdp s u dp wp r hp hr).2) wp).mono h12).bunt_subj
  have h2 := FQ lib σ O c gul st t (Need.pair ned dp) A0 (C s0 wp) u v dq wq
    (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => (hdp s u dp wp r hp h).1)) hqq h1
  refine h2.conv (fun R hR => ⟨⟨⟨hR.1.1, hR.1.2.1⟩, hR.1.2.2⟩, hR.2⟩) (fun z hz => ?_)
  rcases hz with (hz | hz | hz) | hz
  · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hz)))
  · exact Or.inl (Or.inl (Or.inr hz))
  · exact Or.inl (Or.inr hz)

/-- **`[7 p q]` under `%next L th` with bodies** (`runOKLC_seven` for
`RunOKLB`): `q` with any flag, `p` with `x = false`; the whole has `q`'s
flag and the witness relation `sevenWit`. -/
theorem runOKLB_seven {lib : Lib} {P : Noun → Prop} {fb fc : Noun} {L : Lazy S} {th : Jmp} {Qp Qq : Wit} {x : Bool}
    {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKLB (Map := Map) lib (Img lib P fb) fc L th Qq x g0 g1 nx)
    (Rp : RunOKLB (Map := Map) lib P fb nx.laz nx.th Qp false g1 g2 nex)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo) :
    RunOKLB lib P (n3 (A 7) fb fc) L th (sevenWit Qp Qq) x g0 g2 nex := by
  have q1 := Rq.re
  have q2 := Rq.bo
  have p1 := Rp.re
  have p2 := Rp.bo
  have qhi := Rq.hi
  have qlab : ∀ o, o ∈ (entries nx.laz).map Prod.fst → o ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ o ∧ o < g1.bo) :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Rq.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr h
  have plab : ∀ o, o ∈ (entries nex.laz).map Prod.fst → o ∈ (entries nx.laz).map Prod.fst ∨ g1.bo ≤ o :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Rp.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
  have nxL : ∀ r, NMem nx.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases Rq.regs r hr with h | h
    · have := hL r h; omega
    · exact h.2
  have hdp : ∀ s v d w r, Qp s v d w → NMem d r → g1.re ≤ r ∧ r < g2.re := Rp.dreg
  -- the shared part of the two `sem` clauses
  have core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun), Forall2 (FrameRel lib (ν st)) t tm →
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g2 nex.laz s0 s) → (∀ x, NMem ned x → g2.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 →
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g1 g2 nex.laz s0 s) ∧
      ∀ (u : Noun) (st' : σ) (R1 : Map (Option Noun)) (dp : Need) (wp : Noun), Qp s u dp wp → Inv st' →
        ν st ≤ ν st' → FitsS nx.laz.sure u → HoldsN nx.laz.sure.ned R1 u → HoldsN dp R1 wp →
        (∀ x, ((x < g1.re ∨ NMem ned x) ∧ ¬ NMem nx.laz.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs) →
        (∀ st'' : σ, AgreeLB lib O c gul st'' t cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u) ∧
        (∀ x, NMem (Need.pair ned dp) x → g1.re ≤ x) ∧ HoldsS nx.laz.sure R1 u ∧
        HoldsN (Need.pair ned dp) R1 (C s0 wp) ∧
        ∀ r, GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem (Need.pair ned dp) x) ∧
            ¬ NMem L.sure.ned x) st' R1 t tm nx.th L.sure th (Qq u) r →
          goJ lib O c gul st regs t nex.th = goJ lib O c gul st' R1 t nx.th →
          GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm
            nex.th L.sure th (sevenWit Qp Qq s) r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hn
    refine ⟨fun st' => ⟨fun o l u hnl => (ag st').1 o (by omega) u hnl, fun e he l => (ag st').2 e he (by omega)⟩,
      fun u st' R1 dp wp hqp hI' hν fit h1 hD1 k1 => ?_⟩
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
      have := nxL x hm; have := hned x hx; omega⟩) hn
    refine ⟨fun st'' => ⟨fun o l u' hnl => ?_, fun e he l => ?_⟩,
      fun r hr => hr.elim (fun h => by have := hned r h; omega) (fun h => (hdp s u dp wp r hqp h).1),
      ⟨h1, fit.2⟩, ⟨hn1, hD1⟩, fun r G e1 => ?_⟩
    · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
        rcases plab o hm with h | h
        · exact hnl h
        · omega
      rw [(ag st'').1 o l (by omega) hn2, Rp.keep o u' hnl]
    · obtain ⟨_, Bq, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := by
        rcases (Rq.labs e he).1 with h | h
        · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h; have := hlab e0 he0; omega
        · omega
      obtain ⟨Fp, hFp, Sp'⟩ := Rp.front e he
      have hb2 := hFp Bq (Termin.hop th') hb1
      rcases Sp' cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
      · obtain ⟨A0, B2, th'', hb3, hc3, hf3⟩ := (ag st'').2 (e.1, L') hL' l
        rw [hb2] at hb3
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
        obtain ⟨rfl, rfl⟩ := hb3
        refine ⟨A0 ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, by rw [hc3]; simp, ?_⟩
        exact ((FP lib σ O c gul st'' t ned A0 s0 s u dp wp hned hqp hf3).conv (N1 := Need.pair ned dp)
          (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))).mono (Nat.le_refl _)
      · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, ?_, ?_⟩
        · rw [(ag st'').1 e.1 l (by omega) hn2, hb2]
          simp [unproxyBlob, renBlob, renFin]
        · exact (FP lib σ O c gul st'' t ned [] s0 s u dp wp hned hqp fillSem_bunt_nil).conv
            (N1 := Need.pair ned dp) (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))
    · have G' := goalSemCMD_pair (Q' := sevenWit Qp Qq s) (dp := dp) (wp := wp)
        (fun x hx => ⟨Or.inr (Or.inr hx), fun hm => by have := hL x hm; have := (hdp s u dp wp x hqp hx).1; omega⟩)
        hD1 (fun v d w hq => ⟨u, dp, wp, d, w, hqp, hq, rfl, rfl⟩) G
      refine goalSemCMD_step hν (fun r hr => ?_) e1
        (GoalSemCMD.mono (fun x hx => ⟨hx.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hx.2⟩) (fun _ _ _ h => h) G')
      refine k1 r ⟨hr.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hm => ?_⟩
      rcases Rq.regs r hm with h | h
      · exact hr.2 h
      · rcases hr.1 with h' | h'
        · omega
        · have := hned r h'; omega
  refine ⟨by omega, by omega, Rp.drop.trans Rq.drop, fun o ho hn => ?_, Rq.grow.trans Rp.grow, Rq.cfr.trans Rp.cfr,
    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ⟨(Rp.eregs e he).1, fun r hr => ?_⟩, fun e he => ?_,
    Rp.nodup, fun s v d w r hq hr => ?_, fun s hs hf => ?_, Rp.ncond, Rp.econd, fun e he => ?_, ?_, ?_⟩
  · have hn' : o ∉ (entries nx.laz).map Prod.fst := fun hm => by
      rcases qlab o hm with h | h
      · exact hn h
      · omega
    exact (Rp.keep o (by omega) hn').trans (Rq.keep o ho hn)
  · rcases Rp.ent with f | e
    · exact Or.inl f
    · have e' : nex.th = nx.th := e
      rw [e']
      rcases Rq.ent with f | e2
      · exact Or.inl (f.growU Rq.hi Rp.grow)
      · exact Or.inr e2
  · rcases Rp.regs r hr with h | h
    · rcases Rq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · rcases (Rp.eregs e he).2 r hr with ⟨e0, he0, h0⟩ | h | h
    · rcases (Rq.eregs e0 he0).2 r h0 with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨h'.1, by omega⟩)
    · rcases Rq.regs r h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨h'.1, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · obtain ⟨h, blk⟩ := Rp.labs e he
    refine ⟨?_, blk⟩
    rcases h with h | h
    · rcases qlab e.1 h with h' | h'
      · exact Or.inl h'
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
        have := (Rq.labs e0 he0).1
        rcases this with h'' | h''
        · exact Or.inl (by rw [← e1]; exact h'')
        · exact Or.inr ⟨h'.1, by rw [← e1]; omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    rcases hr with h | h
    · have := Rp.dreg s u dp wp r hp h; exact ⟨by omega, this.2⟩
    · have := Rq.dreg u v dq wq r hqq h; exact ⟨this.1, by omega⟩
  · obtain ⟨N1, N2⟩ := Rp.nec s hs hf
    have step : ∀ {tm : Trace} {rb r : Tone}, BadC (CGoal.next nx.laz.sure nx.th) tm rb →
        ((∀ q, rb ≠ Tone.zero q) ∧ r = rb) → BadC (CGoal.next L.sure th) tm r := fun hb hr => by
      obtain ⟨hn, rfl⟩ := hr
      rcases hb with e | ⟨q, e, _⟩
      · exact Or.inl e
      · exact absurd e (hn q)
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', _, rb, hb, h | ⟨u, rfl, hc⟩⟩ := minkF_sevenC hm
      · exact step (N1 gul n' tm rb hb) h
      · rcases N1 gul n' tm _ hb with e | ⟨q, e, hq⟩
        · cases e
        · cases e
          exact (Rq.nec u (img_of hs hb) hq).1 gul n' tm r hc
    · obtain ⟨rb, hb, hbad⟩ := N2 gul tm
      rcases hbad with e | ⟨u, rfl, hq⟩
      · subst e
        exact ⟨_, (mink_sevenC_bwd (fc := fc) hb).1 (fun _ e => by cases e), Or.inl rfl⟩
      · obtain ⟨r, hr, hbr⟩ := (Rq.nec u ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩ hq).2 gul tm
        exact ⟨r, (mink_sevenC_bwd hb).2 u r rfl hr, hbr⟩
  · obtain ⟨Fq, hFq, Sq⟩ := Rq.front e he
    by_cases hk : e.1 ∈ (entries nx.laz).map Prod.fst
    · obtain ⟨e', he', he1⟩ := List.mem_map.mp hk
      obtain ⟨Fp, hFp, Sp⟩ := Rp.front e' he'
      refine ⟨Fp ++ Fq, fun B fin hb => ?_, fun cf hcf => ?_⟩
      · have h1 := hFq B fin hb
        rw [← he1] at h1
        have h2 := hFp _ fin h1
        rw [he1, ← List.append_assoc] at h2
        exact h2
      · have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
          (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
        obtain ⟨Lq, hLq, FQ⟩ : ∃ L', (e.1, L') ∈ entries nx.laz ∧
            FrontLB (Map := Map) Qq (gsE x L) g0.re g1.re L'.sure (Fq.map (renPole (unproxy cf))) e.2.sure :=
          (Sq cf hcf1).elim id (fun h => absurd hk h.1)
        have ee : e' = (e.1, Lq) := mem_key_eq Rq.nodup he' hLq he1
        subst ee
        simp only [List.map_append]
        rcases Sp cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
        · exact Or.inl ⟨L', hL', frontLB_seven (fun s v d w r hq hr => (hdp s v d w r hq hr).1) p1 FP FQ⟩
        · exact Or.inr ⟨hn2, frontLB_seven (fun s v d w r hq hr => (hdp s v d w r hq hr).1) p1 FP FQ⟩
    · refine ⟨Fq, fun B fin hb => ?_, fun cf hcf => ?_⟩
      · rw [Rp.keep e.1 (by have := hlab e he; omega) hk]; exact hFq B fin hb
      · have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
          (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
        rcases Sq cf hcf1 with ⟨L', hL', _⟩ | ⟨_, FQ⟩
        · exact absurd (List.mem_map.mpr ⟨_, hL', rfl⟩) hk
        · refine Or.inr ⟨fun hm => ?_, frontLB_seven_bunt hdp p1 FQ⟩
          rcases plab e.1 hm with h | h
          · exact hk h
          · have := hlab e he; omega
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hn
    obtain ⟨n', hn', rb, hb, h | ⟨u, rfl, hc⟩⟩ := minkF_sevenC hm
    · have Gp := Rp.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rb hI
        htr hs hb agP hned regs hh hn
      obtain ⟨hnz, rfl⟩ := h
      exact goalSemCMD_ret hnz (returnsC_of_goalSemCMD hnz Gp)
    have Gp := Rp.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s _ hI
      htr hs hb agP hned regs hh hn
    by_cases fit : FitsS nx.laz.sure u
    · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
      obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
      exact fin r (Rq.sem cf hcf1 c (Need.pair ned dp) σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn'))
        st' t tm (C s0 wp) u r hI' (frames_mono hν htr) (img_of hs hb) hc agQ hnQ R1 hsQ hnQ') e1
    · have R2 := Gp.2 fit
      rcases (Rq.nec u (img_of hs hb) fit).1 gul n' tm r hc with e | ⟨v, rfl, nf⟩
      · subst e; exact R2
      · exact ⟨fun f => absurd f nf, fun _ => R2⟩
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hn
    obtain ⟨rb, hb, Gp⟩ := Rp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs agP hned regs hh hn
      res hres
    cases rb with
    | one q =>
      exact ⟨_, (mink_sevenC_bwd hb).1 (fun _ e => by cases e), goalSemCMD_ret (fun _ e => by cases e) Gp⟩
    | two t' =>
      exact ⟨_, (mink_sevenC_bwd hb).1 (fun _ e => by cases e), goalSemCMD_ret (fun _ e => by cases e) Gp⟩
    | zero u =>
      have hu : Img lib P fb u := ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩
      by_cases fit : FitsS nx.laz.sure u
      · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
        obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
        obtain ⟨r, hr, Gq⟩ := Rq.semB cf hcf1 c (Need.pair ned dp) σ Inv ν O gul hS hB st' t tm (C s0 wp) u hI'
          (frames_mono hν htr) hu agQ hnQ R1 hsQ hnQ' res (by rw [← e1]; exact hres)
        exact ⟨r, (mink_sevenC_bwd hb).2 u r rfl hr, fin r Gq e1⟩
      · have R2 := Gp.2 fit
        obtain ⟨r, hr, hbad⟩ := (Rq.nec u hu fit).2 gul tm
        refine ⟨r, (mink_sevenC_bwd hb).2 u r rfl hr, ?_⟩
        rcases hbad with e | ⟨v, rfl, nf⟩
        · subst e; exact R2
        · exact ⟨fun f => absurd f nf, fun _ => R2⟩

end Comp
end SkaModel
end Formalization
