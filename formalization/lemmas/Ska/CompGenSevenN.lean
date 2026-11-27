import lemmas.Ska.CompGenSevenD

/-!
# `[7 p q]` under `%next L th` in `RunOKGen`

README Gaps 12.39, item 10.  `runOKGen_sevenG`: `RunOKGen` of `q` at any
lazy goal `L` (any flag) and `RunOKGen` of `p` at `q`'s result (`x =
false`, adding blocks as `GrowU` does and re-pointing none of `q`'s result
entries) give `RunOKGen` of `[7 p q]` with the witness `sevenWit`: the text
of `runOKLB_seven` with `q`'s agreement taken per label (the `core` of
`runOKGD_sevenG`) and the fronts composed per label (`frontLG_sevenG`,
`frontLG_seven_nil`).  A goal entry that `q` re-pointed stays re-pointed in
the whole's frame (`RepointG.seven`, `GrowG.seven`); its semantic clause,
the whole's `FrontRG` from `q`'s, is `frontRG_sevenQ` (through
`agreeGA_seven` and `EntA.front`), so `runOKGen_sevenGF` takes `q` in any
phase, F included.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The frame -/

/-- **Front blocks compose.** -/
theorem FrontBlk.trans {g0 g1 g2 : Gen Map} {a : Nat} {F1 F2 : List Pole} (h1 : FrontBlk g0 g1 a F1)
    (h2 : FrontBlk g1 g2 a F2) : FrontBlk g0 g2 a (F2 ++ F1) := fun B fin hb => by
  rw [h2 _ fin (h1 B fin hb), List.append_assoc]

/-- **A re-pointed goal entry stays re-pointed** under a later part that
puts ops in front of every old block. -/
theorem RepointG.seven {g0 g1 g2 : Gen Map} {a : Nat} (h : RepointG g0 g1 a) (hbo : g1.bo ≤ g2.bo)
    (hpf : ∀ k, k < g1.bo → ∃ F, FrontBlk g1 g2 k F) (ha : a < g1.bo) : RepointG g0 g2 a := by
  obtain ⟨B, fin, F, o1, o2, F2, h0, h1, l1, u1, l2, u2, h2⟩ := h
  obtain ⟨Fa, hFa⟩ := hpf a ha
  obtain ⟨Fo, hFo⟩ := hpf o2 u2
  refine ⟨B, fin, Fa ++ F, o1, o2, Fo ++ F2, h0, hFa _ _ h1, l1, by omega, l2, by omega, ?_⟩
  rw [hFo _ fin h2, List.append_assoc]

/-- **`GrowG` through a later part that grows as `GrowU`.** -/
theorem GrowG.seven {L : Lazy S} {g0 g1 g2 : Gen Map} (Gq : GrowG L g0 g1) (hgu : GrowU g1 g2)
    (hbo : g0.bo ≤ g1.bo) (hrp : ∀ k, k < g0.bo → RepointG g0 g1 k → RepointG g0 g2 k) : GrowG L g0 g2 where
  keep := fun k b hk hb => by
    obtain ⟨b', h1, p1, f1⟩ := Gq.keep k b hk hb
    obtain ⟨b'', h2, p2, f2⟩ := hgu.keep k b' (by omega) h1
    refine ⟨b'', h2, p2.trans p1, ?_⟩
    rcases f1 with f1 | ⟨hm, hr⟩
    · exact Or.inl (f2.trans f1)
    · exact Or.inr ⟨hm, hrp k hk hr⟩
  new := fun k b'' hb => by
    rcases hgu.new k b'' hb with ⟨b', h1, p1, _⟩ | ⟨l, u, _⟩
    · rcases Gq.new k b' h1 with ⟨b, h0, p0⟩ | ⟨l', u'⟩
      · exact Or.inl ⟨b, h0, p1.trans p0⟩
      · exact Or.inr ⟨l', by have := hgu.bo; omega⟩
    · exact Or.inr ⟨by omega, u⟩

/-! ## The fronts -/

/-- A fill of the empty conjunction does not read the subject. -/
theorem FillSemL.nil_subj {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {N : Need} {lo : Nat} {A : List Pole} {x s s' : Noun}
    (h : FillSemL (S := S) (Map := Map) lib O c gul st t N lo [] A x s) :
    FillSemL (S := S) lib O c gul st t N lo [] A x s' := fun R hR => by
  obtain ⟨F1, _⟩ := h R hR
  obtain ⟨R', r, _, k⟩ := F1 (fun _ h => by simp at h)
  exact ⟨fun _ => ⟨R', r, fun _ h => by simp at h, k⟩, fun ⟨_, h, _⟩ => by simp at h⟩

/-- **The fronts compose per label** (`frontLB_seven` between conjunctions),
`p` reading no goal register. -/
theorem frontLG_sevenG {Qp Qq : Wit} {E : Need} {lo0 lo1 lo2 : Nat} {Lp Lq M : List (Sure S)} {Fp Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r) (h12 : lo1 ≤ lo2)
    (FP : FrontLG (Map := Map) Qp Need.none lo1 lo2 Lp Fp Lq) (FQ : FrontLG (Map := Map) Qq E lo0 lo1 Lq Fq M) :
    FrontLG (Map := Map) (sevenWit Qp Qq) E lo0 lo2 Lp (Fp ++ Fq) M := by
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

/-- **A front of `q` at a label that `p` does not see** (no entry of `q`'s
result there, `p` keeps the block). -/
theorem frontLG_seven_nil {Qp Qq : Wit} {E : Need} {lo0 lo1 lo2 : Nat} {M : List (Sure S)} {Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r ∧ r < lo2) (h12 : lo1 ≤ lo2)
    (FQ : FrontLG (Map := Map) Qq E lo0 lo1 [] Fq M) :
    FrontLG (Map := Map) (sevenWit Qp Qq) E lo0 lo2 [] Fq M := by
  intro lib σ O c gul st t ned A0 s0 s v d w hned hq hfill
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have h1 : FillSemL lib O c gul st t (Need.pair ned dp) lo1 [] A0 (C s0 wp) u :=
    ((hfill.conv (N1 := Need.pair ned dp) (x1 := C s0 wp) (fun R hR => hR.1)
      (fun z hz => hz.elim Or.inl (fun h => Or.inr (hdp s u dp wp z hp h).2))).mono h12).nil_subj
  have h2 := FQ lib σ O c gul st t (Need.pair ned dp) A0 (C s0 wp) u v dq wq
    (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => (hdp s u dp wp r hp h).1)) hqq h1
  refine h2.conv (fun R hR => ⟨⟨⟨hR.1.1, hR.1.2.1⟩, hR.1.2.2⟩, hR.2⟩) (fun z hz => ?_)
  rcases hz with (hz | hz | hz) | hz
  · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hz)))
  · exact Or.inl (Or.inl (Or.inr hz))
  · exact Or.inl (Or.inr hz)

/-! ## `[7 p q]` -/

/-- **`[7 p q]` under `%next L th` in `RunOKGen`** (`runOKLB_seven` at any
lazy goal and any lazy result): `q` with any flag, `p` with `x = false`,
growing as `GrowU` and re-pointing none of `q`'s result entries; the whole
has `q`'s flag and the witness `sevenWit`.  A goal entry that `q`
re-pointed stays re-pointed (frame); its semantic clause, the whole's
`FrontRG` from `q`'s, is the premise `hrq` (`hrq` holds vacuously when `q`
re-points nothing: `runOKGen_sevenG'`).  The agreement is handed at every
state and trace. -/
theorem runOKGen_sevenG {lib : Lib} {N : Needs} {P : Noun → Prop} {fb fc : Noun} {L : Lazy S} {th : Jmp}
    {Qp Qq : Wit} {x : Bool} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGen (Map := Map) lib N (Img lib P fb) fc L th Qq x g0 g1 nx)
    (Rp : RunOKGen (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hgu : GrowU g1 g2) (hnr : ∀ a ∈ (entries nx.laz).map Prod.fst, ¬ RepointG g1 g2 a)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hrq : ∀ a ∈ (entries L).map Prod.fst, RepointG g0 g1 a →
      FrontRG (Map := Map) Qq (gsE x L) g0 g1 nx a (suresAt L a) →
      FrontRG (Map := Map) (sevenWit Qp Qq) (gsE x L) g0 g2 nex a (suresAt L a)) :
    RunOKGen lib N P (n3 (A 7) fb fc) L th (sevenWit Qp Qq) x g0 g2 nex := by
  have q1 := Rq.re
  have q2 := Rq.bo
  have p1 := Rp.re
  have p2 := Rp.bo
  have qhi := Rq.hi
  have qlab : ∀ o, o ∈ (entries nx.laz).map Prod.fst → o ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ o ∧ o < g1.bo) :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      exact (Rq.labs e he).1
  have qlt : ∀ o, o ∈ (entries nx.laz).map Prod.fst → o < g1.bo := fun o ho => by
    rcases qlab o ho with h | h
    · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h; have := hlab e0 he0; omega
    · exact h.2
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
  -- `p` only fronts `q`'s labels, and keeps every other old block
  have pfr : ∀ o ∈ (entries nx.laz).map Prod.fst, ∃ F : List Pole, FrontBlk g1 g2 o F ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
        FrontLG (Map := Map) Qp (gsE false nx.laz) g1.re g2.re (suresAt nex.laz o)
          (F.map (renPole (unproxy cf))) (suresAt nx.laz o) := fun o ho => by
    rcases Rp.front o ho with h | ⟨h, _⟩
    · exact h
    · exact absurd h (hnr o ho)
  have hpf : ∀ k, k < g1.bo → ∃ F, FrontBlk g1 g2 k F := fun k hk => by
    by_cases hm : k ∈ (entries nx.laz).map Prod.fst
    · obtain ⟨F, hF, _⟩ := pfr k hm
      exact ⟨F, hF⟩
    · exact ⟨[], fun B fin hb => by rw [Rp.keep k hk hm]; simpa using hb⟩
  have hrp : ∀ k, k < g0.bo → RepointG g0 g1 k → RepointG g0 g2 k := fun k hk h =>
    h.seven p2 hpf (by omega)
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
        ∀ r, GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem (Need.pair ned dp) x) ∧
            ¬ NMem L.sure.ned x) st' R1 t tm nx.th L.sure th (Qq u) r →
          goJ lib O c gul st regs t nex.th = goJ lib O c gul st' R1 t nx.th →
          GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm
            nex.th L.sure th (sevenWit Qp Qq s) r := by
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
      obtain ⟨_, Bq, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := qlt e.1 ho
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
        · rw [(ag st'' t'').1 e.1 (by omega) (by omega) hm, hb2]
          simp [unproxyBlob, renBlob, renFin]
        · have h0 : FillSemL lib O c gul st'' t'' ned g2.re (suresAt nex.laz e.1) [] s0 s := by
            rw [suresAt_nil hm]; exact fillSemL_nil_nil
          exact (FP lib σ O c gul st'' t'' ned [] s0 s u dp wp hned hqp h0).conv
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
  refine { re := by omega, bo := by omega, drop := Rp.drop.trans Rq.drop, keep := fun o ho hn => ?_,
           grow := Rq.grow.seven hgu q2 hrp, cfr := Rq.cfr.trans Rp.cfr, lo := Rp.lo, hi := Rp.hi, ent := ?_,
           regs := fun r hr => ?_, dist := Rp.dist, eregs := fun e he => ⟨(Rp.eregs e he).1, fun r hr => ?_⟩,
           labs := fun e he => ?_, labDisj := Rp.labDisj, dreg := fun s v d w r hq hr => ?_,
           ncond := Rp.ncond, econd := Rp.econd, fronts := fun e he => ?_,
           nec := fun s hs hf => ?_, front := ?_, sem := ?_, semB := ?_ }
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
      · exact Or.inl (f.growU Rq.hi hgu)
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
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    rcases hr with h | h
    · have := Rp.dreg s u dp wp r hp h; exact ⟨by omega, this.2⟩
    · have := Rq.dreg u v dq wq r hqq h; exact ⟨this.1, by omega⟩
  · -- fronts (frame)
    have hlt : e.1 < g1.bo := by have := hlab e he; omega
    rcases Rq.fronts e he with ⟨Fq, hFq⟩ | hr
    · obtain ⟨Fp, hFp⟩ := hpf e.1 hlt
      exact Or.inl ⟨Fp ++ Fq, hFq.trans hFp⟩
    · exact Or.inr (hrp e.1 (hlab e he) hr)
  · -- nec
    obtain ⟨N1, N2⟩ := Rp.nec s hs hf
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
  · -- the fronts' semantics, per label
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    have hlt : e.1 < g1.bo := by have := hlab e he; omega
    rcases Rq.front e.1 ha with ⟨Fq, hFq, FQ⟩ | ⟨hr, FR⟩
    · have hcf1 : ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
          ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun cf hcf k hk' =>
        (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
      by_cases hk : e.1 ∈ (entries nx.laz).map Prod.fst
      · obtain ⟨Fp, hFp, FP⟩ := pfr e.1 hk
        refine Or.inl ⟨Fp ++ Fq, hFq.trans hFp, fun cf hcf => ?_⟩
        simp only [List.map_append]
        exact frontLG_sevenG (fun s v d w r hq hr => (hdp s v d w r hq hr).1) p1 (FP cf hcf) (FQ cf (hcf1 cf hcf))
      · have hne : e.1 ∉ (entries nex.laz).map Prod.fst := fun hm => by
          rcases plab e.1 hm with h | h
          · exact hk h
          · omega
        refine Or.inl ⟨Fq, fun B fin hb => ?_, fun cf hcf => ?_⟩
        · rw [Rp.keep e.1 hlt hk]; exact hFq B fin hb
        · have FQ' := FQ cf (hcf1 cf hcf)
          rw [suresAt_nil hk] at FQ'
          rw [suresAt_nil hne]
          exact frontLG_seven_nil hdp p1 FQ'
    · exact Or.inr ⟨hrp e.1 (hlab e he) hr, hrq e.1 ha hr FR⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    obtain ⟨n', hn', rb, hb, h | ⟨u, rfl, hc⟩⟩ := minkF_sevenC hm
    · have Gp := Rp.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rb hI
        htr hs hb agP hned regs hh hn
      obtain ⟨hnz, rfl⟩ := h
      exact goalSemCMD_ret hnz (returnsC_of_goalSemCMD hnz Gp)
    have Gp := Rp.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s _ hI
      htr hs hb agP hned regs hh hn
    by_cases fit : FitsS nx.laz.sure u
    · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
      obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
      exact fin r (Rq.sem cf hcf1 c (Need.pair ned dp) σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn'))
        st' t tm (C s0 wp) u r hI' (frames_mono hν htr) (img_of hs hb) hc agQ hnQ R1 hsQ hnQ') e1
    · have R2 := Gp.2 fit
      rcases (Rq.nec u (img_of hs hb) fit).1 gul n' tm r hc with e | ⟨v, rfl, nf⟩
      · subst e; exact R2
      · exact ⟨fun f => absurd f nf, fun _ => R2⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    obtain ⟨rb, hb, Gp⟩ := Rp.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs agP hned regs hh hn
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
        obtain ⟨r, hr, Gq⟩ := Rq.semB cf hcf1 c (Need.pair ned dp) σ Inv ν O gul hN hS hB st' t tm (C s0 wp) u hI'
          (frames_mono hν htr) hu agQ hnQ R1 hsQ hnQ' res (by rw [← e1]; exact hres)
        exact ⟨r, (mink_sevenC_bwd hb).2 u r rfl hr, fin r Gq e1⟩
      · have R2 := Gp.2 fit
        obtain ⟨r, hr, hbad⟩ := (Rq.nec u hu fit).2 gul tm
        refine ⟨r, (mink_sevenC_bwd hb).2 u r rfl hr, ?_⟩
        rcases hbad with e | ⟨v, rfl, nf⟩
        · subst e; exact R2
        · exact ⟨fun f => absurd f nf, fun _ => R2⟩

/-- **`[7 p q]` under `%next L th` when `q` re-points none of the goal's
entries** (no `%6` of `q` in phase F). -/
theorem runOKGen_sevenG' {lib : Lib} {N : Needs} {P : Noun → Prop} {fb fc : Noun} {L : Lazy S} {th : Jmp}
    {Qp Qq : Wit} {x : Bool} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGen (Map := Map) lib N (Img lib P fb) fc L th Qq x g0 g1 nx)
    (Rp : RunOKGen (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hgu : GrowU g1 g2) (hnr : ∀ a ∈ (entries nx.laz).map Prod.fst, ¬ RepointG g1 g2 a)
    (hnq : ∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo) :
    RunOKGen lib N P (n3 (A 7) fb fc) L th (sevenWit Qp Qq) x g0 g2 nex :=
  runOKGen_sevenG Rq Rp hgu hnr hL hlab (fun a ha hr _ => absurd hr (hnq a ha))

/-! ## A goal entry that `q` re-pointed -/

/-- **The entry semantics of an empty conjunction moves** to another input
need, a lower bound and another subject. -/
theorem EntA.nilMove {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {N N1 : Need} {lo lo' : Nat} {a : Nat} {B : List Pole} {fin : Termin} {x x1 s s' : Noun}
    (h : EntA (S := S) (Map := Map) lib O c gul st t N lo [] a B fin x s)
    (hh : ∀ R : Map (Option Noun), HoldsN N1 R x1 → HoldsN N R x)
    (hm : ∀ z, NMem N1 z → NMem N z ∨ z < lo) (hl : lo' ≤ lo) :
    EntA (S := S) lib O c gul st t N1 lo' [] a B fin x1 s' :=
  let ⟨A, hf, hj⟩ := h
  ⟨A, ((hf.conv hh hm).mono hl).nil_subj, fun R hR => hj R (hh R hR)⟩

/-- **A goal entry that `q` re-pointed and `p` fronted or kept** (`[7 p q]`,
`p` with `x = false` and no re-pointing): `q`'s `FrontRG` gives the
whole's, with the witness `sevenWit`.  `q`'s agreement comes from
`agreeGA_seven`; `q`'s entry semantics at the label from the whole's, through
`p`'s front there (`EntA.front`), or unchanged when `p`'s goal has no entry
there. -/
theorem frontRG_sevenQ {Qp Qq : Wit} {E : Need} {g0 g1 g2 : Gen Map} {nx nex : NextL S} {a : Nat}
    {Ls : List (Sure S)}
    (Fp : FrameG (Map := Map) nx.laz nx.th Qp g1 g2 nex) (Sp : FrontsG (Map := Map) Qp false g1 g2 nx.laz nex)
    (hnr : ∀ a ∈ (entries nx.laz).map Prod.fst, ¬ RepointG g1 g2 a) (hbo : g0.bo ≤ g1.bo)
    (qlab : ∀ o ∈ (entries nx.laz).map Prod.fst, g0.bo ≤ o →
      o < g1.bo ∧ ∃ B th, HoonMap.get g1.blocks o = some ⟨[], B, Termin.hop th⟩)
    (hr : RepointG g0 g1 a) (ha : a < g1.bo) (FR : FrontRG (Map := Map) Qq E g0 g1 nx a Ls) :
    FrontRG (Map := Map) (sevenWit Qp Qq) E g0 g2 nex a Ls := by
  have p1 := Fp.re
  have p2 := Fp.bo
  obtain ⟨B, fin, hb0, FR⟩ := FR
  obtain ⟨-, -, F1, o1, -, -, -, hb1, -⟩ := hr
  refine ⟨B, fin, hb0, fun cf hcf lib σ O c gul ned s0 s v d w hned hq ag hent st t => ?_⟩
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf k (by omega)).trans (Fp.cfr.get_lt hk)
  have hdp : ∀ r, NMem dp r → g1.re ≤ r ∧ r < g2.re := fun r hr => Fp.dreg s u dp wp r hp hr
  have hned1 : ∀ r, NMem (Need.pair ned dp) r → g1.re ≤ r := fun r hr =>
    hr.elim (fun h => by have := hned r h; omega) (fun h => (hdp r h).1)
  have agq := agreeGA_seven Fp Sp hbo qlab hcf hned hp ag
  have hE : ∀ R : Map (Option Noun), HoldsN (Need.pair ned dp) R (C s0 wp) →
      HoldsN (Need.pair (Need.pair ned dp) (gsE false nx.laz)) R (C (C s0 wp) u) :=
    fun R hR => ⟨hR, by simp [gsE, HoldsN]⟩
  have hm : ∀ z, NMem (Need.pair ned dp) z → NMem (Need.pair (Need.pair ned dp) (gsE false nx.laz)) z ∨ z < g1.re :=
    fun z hz => Or.inl (Or.inl hz)
  have hentq : ∀ (st' : σ) (t' : Trace), ∃ b, HoonMap.get g1.blocks a = some b ∧
      EntA lib O c gul st' t' (Need.pair ned dp) g1.re (suresAt nx.laz a) a (unproxyBlob cf b).body
        (unproxyBlob cf b).fin (C s0 wp) u := fun st' t' => by
    refine ⟨_, hb1, ?_⟩
    obtain ⟨b2, hb2, E2⟩ := hent st' t'
    by_cases hk : a ∈ (entries nx.laz).map Prod.fst
    · rcases Sp a hk with ⟨Fpa, hF, FP⟩ | ⟨hrp, _⟩
      · rw [hF F1 _ hb1] at hb2
        cases hb2
        simp only [unproxyBlob, renBlob, renFin, List.map_append] at E2 ⊢
        exact E2.front (fun A hA => (FP cf hcf lib σ O c gul st' t' ned A s0 s u dp wp hned hp hA).conv hE hm)
          (fun R hR => hR.1)
      · exact absurd hrp (hnr a hk)
    · have hne : a ∉ (entries nex.laz).map Prod.fst := fun hm' => by
        obtain ⟨e, he, e1⟩ := List.mem_map.mp hm'
        rcases (Fp.labs e he).1 with h | h
        · exact hk (e1 ▸ h)
        · omega
      rw [Fp.keep a ha hk, hb1] at hb2
      cases hb2
      rw [suresAt_nil hne] at E2
      rw [suresAt_nil hk]
      exact E2.nilMove (fun R hR => hR.1) (fun z hz => hz.elim Or.inl (fun h => Or.inr (hdp z h).2)) p1
  have E3 := FR cf hcf1 lib σ O c gul (Need.pair ned dp) (C s0 wp) u v dq wq hned1 hqq agq hentq st t
  refine E3.conv (fun R hR => ⟨⟨⟨hR.1.1, hR.1.2.1⟩, hR.1.2.2⟩, hR.2⟩) (fun z hz => ?_)
  rcases hz with (hz | hz | hz) | hz
  · exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hz)))
  · exact Or.inl (Or.inl (Or.inr hz))
  · exact Or.inl (Or.inr hz)

/-- **`[7 p q]` under `%next L th` in `RunOKGen`, `q` in any phase**
(re-pointed goal entries included): `runOKGen_sevenG` with its premise `hrq`
from `frontRG_sevenQ`. -/
theorem runOKGen_sevenGF {lib : Lib} {N : Needs} {P : Noun → Prop} {fb fc : Noun} {L : Lazy S} {th : Jmp}
    {Qp Qq : Wit} {x : Bool} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGen (Map := Map) lib N (Img lib P fb) fc L th Qq x g0 g1 nx)
    (Rp : RunOKGen (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hgu : GrowU g1 g2) (hnr : ∀ a ∈ (entries nx.laz).map Prod.fst, ¬ RepointG g1 g2 a)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo) :
    RunOKGen lib N P (n3 (A 7) fb fc) L th (sevenWit Qp Qq) x g0 g2 nex := by
  have q2 := Rq.bo
  refine runOKGen_sevenG Rq Rp hgu hnr hL hlab (fun a ha hr FR => ?_)
  have hal : a < g0.bo := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact hlab e he
  refine frontRG_sevenQ Rp.toFrameG Rp.front hnr q2 (fun o ho l => ?_) hr (by omega) FR
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
  obtain ⟨h, blk⟩ := Rq.labs e he
  refine ⟨?_, blk⟩
  rcases h with h | h
  · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
    have := hlab e0 he0; omega
  · exact h.2

end Comp
end SkaModel
end Formalization
