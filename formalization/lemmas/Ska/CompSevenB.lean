import lemmas.Ska.CompSevenL

/-!
# `[7 p q]` as the head of a cons whose tail calls: `BondOKC` of `[7 p q]`

README Gaps 12.21.  A head under the bond goal of `+past` (`BondOKC`) runs
under a lazy goal with one entry.  For `[7 p q]`, `q` runs under that goal
(`BondOKC` of `q`) and `p` under `q`'s result (`LOKC` of `p`), and
`runOKLC_sevenM` (`runOKLC_seven` for any formula with `MinkC7`) composes.

The raw blocks of `[[7 [0 3] [4 [0 1]]] [2 [0 3] [0 2]]]` (`%s7c`) and of
`[[7 [2 [0 3] [0 2]] [4 [0 1]]] [2 [0 3] [0 2]]]` (`%h7c`) are the `#guard`s of
`CompRunOKLC.lean`: in both the head's `[4 [0 1]]` takes the bond entry
(`inc v9 v7`, the bond block `mov v7 v2` behind the tail's call).

* `runOKLC_sevenM`.
* `bondOKC_sevenC`, `bondOKC_sevenA` (the forms `n7`, `inline`, `n9`).
* `HeadP`, `HeadQ`: the parts of such a head; `uokc_head7`, `bondOKC_head7`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`[7 p q]` under `%next L th` for runs that may call, any formula with
`MinkC7`** (`runOKLC_seven` with `+mink` on `f` the composition of `fb` and
`fc`: the same proof, the fuel of each part from `M.fwd`). -/
theorem runOKLC_sevenM {lib : Lib} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc) {L : Lazy S}
    {th : Jmp} {Qp Qq : Wit}
    {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKLC (Map := Map) lib (Img lib P fb) fc L th Qq g0 g1 nx)
    (Rp : RunOKLC (Map := Map) lib P fb nx.laz nx.th Qp g1 g2 nex)
    (hle : nx.th.there ≤ nex.th.there) (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo) :
    RunOKLC lib P f L th (sevenWit Qp Qq) g0 g2 nex := by
  have q1 := Rq.re
  have q2 := Rq.bo
  have p1 := Rp.re
  have p2 := Rp.bo
  have qhi := Rq.hi
  -- the labels of `q`'s result
  have qlab : ∀ o, o ∈ (entries nx.laz).map Prod.fst → o ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ o ∧ o < g1.bo) :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Rq.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, by omega⟩
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
      (∀ st' : σ, AgreeL lib O c gul st' t cf ned g0 g2 nex.laz s0 s) → (∀ x, NMem ned x → g2.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 →
      (∀ st' : σ, AgreeL lib O c gul st' t cf ned g1 g2 nex.laz s0 s) ∧
      ∀ (u : Noun) (st' : σ) (R1 : Map (Option Noun)) (dp : Need) (wp : Noun), Qp s u dp wp → Inv st' →
        ν st ≤ ν st' → FitsS nx.laz.sure u → HoldsN nx.laz.sure.ned R1 u → HoldsN dp R1 wp →
        (∀ x, ((x < g1.re ∨ NMem ned x) ∧ ¬ NMem nx.laz.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs) →
        (∀ st'' : σ, AgreeL lib O c gul st'' t cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u) ∧
        (∀ x, NMem (Need.pair ned dp) x → g1.re ≤ x) ∧ HoldsS nx.laz.sure R1 u ∧
        HoldsN (Need.pair ned dp) R1 (C s0 wp) ∧
        ∀ r, GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem (Need.pair ned dp) x) ∧
            ¬ NMem L.sure.ned x) st' R1 t tm nx.th L.sure th (Qq u) r →
          goJ lib O c gul st regs t nex.th = goJ lib O c gul st' R1 t nx.th →
          GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm
            nex.th L.sure th (sevenWit Qp Qq s) r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
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
    · obtain ⟨_, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := by
        rcases (Rq.labs e he).1 with h | h
        · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h; have := hlab e0 he0; omega
        · omega
      obtain ⟨Fp, hFp, Sp'⟩ := Rp.front e he
      have hb2 := hFp [] (Termin.hop th') hb1
      rw [List.append_nil] at hb2
      rcases Sp' cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
      · obtain ⟨A0, th'', hb3, hc3, hf3⟩ := (ag st'').2 (e.1, L') hL' l
        rw [hb2] at hb3
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
        obtain ⟨rfl, rfl⟩ := hb3
        refine ⟨A0 ++ ([] : List Pole).map (renPole (unproxy cf)), th', hb1, by simpa using hc3, ?_⟩
        exact (FP lib σ O c gul st'' t ned A0 s0 s u dp wp hned hqp hf3).mono (Nat.le_refl _)
      · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), th', hb1, ?_, ?_⟩
        · rw [(ag st'').1 e.1 l (by omega) hn2, hb2]
          simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, List.nil_append]
        · exact FP lib σ O c gul st'' t ned [] s0 s u dp wp hned hqp fillSem_bunt_nil
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
  · -- keep
    have hn' : o ∉ (entries nx.laz).map Prod.fst := fun hm => by
      rcases qlab o hm with h | h
      · exact hn h
      · omega
    exact (Rp.keep o (by omega) hn').trans (Rq.keep o ho hn)
  · -- ent
    rcases Rp.ent with f | e
    · exact Or.inl f
    · have e' : nex.th = nx.th := e
      rw [e']
      rcases Rq.ent with f | e2
      · exact Or.inl (f.growU Rq.hi Rp.grow)
      · exact Or.inr e2
  · -- regs
    rcases Rp.regs r hr with h | h
    · rcases Rq.regs r h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · -- eregs
    rcases (Rp.eregs e he).2 r hr with ⟨e0, he0, h0⟩ | h | h
    · rcases (Rq.eregs e0 he0).2 r h0 with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨h'.1, by omega⟩)
    · rcases Rq.regs r h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨h'.1, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · -- labs
    obtain ⟨h, blk⟩ := Rp.labs e he
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
  · -- dreg
    obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    rcases hr with h | h
    · have := Rp.dreg s u dp wp r hp h; exact ⟨by omega, this.2⟩
    · have := Rq.dreg u v dq wq r hqq h; exact ⟨this.1, by omega⟩
  · -- nec
    obtain ⟨N1, N2⟩ := Rp.nec s hs hf
    have step : ∀ {tm : Trace} {rb r : Tone}, BadC (CGoal.next nx.laz.sure nx.th) tm rb →
        ((∀ q, rb ≠ Tone.zero q) ∧ r = rb) → BadC (CGoal.next L.sure th) tm r := fun hb hr => by
      obtain ⟨hn, rfl⟩ := hr
      rcases hb with e | ⟨q, e, _⟩
      · exact Or.inl e
      · exact absurd e (hn q)
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n1, _, rb, hb, h | ⟨u, rfl, n2, _, hc⟩⟩ := M.fwd hs hm
      · exact step (N1 gul n1 tm rb hb) h
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
  · -- front
    obtain ⟨Fq, hFq, Sq⟩ := Rq.front e he
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
            FrontLC (Map := Map) Qq g0.re g1.re L'.sure (Fq.map (renPole (unproxy cf))) e.2.sure :=
          (Sq cf hcf1).elim id (fun h => absurd hk h.1)
        have ee : e' = (e.1, Lq) := mem_key_eq Rq.nodup he' hLq he1
        subst ee
        simp only [List.map_append]
        rcases Sp cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
        · exact Or.inl ⟨L', hL', frontLC_seven (fun s v d w r hq hr => (hdp s v d w r hq hr).1) p1 FP FQ⟩
        · exact Or.inr ⟨hn2, frontLC_seven (fun s v d w r hq hr => (hdp s v d w r hq hr).1) p1 FP FQ⟩
    · refine ⟨Fq, fun B fin hb => ?_, fun cf hcf => ?_⟩
      · rw [Rp.keep e.1 (by have := hlab e he; omega) hk]; exact hFq B fin hb
      · have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
          (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
        rcases Sq cf hcf1 with ⟨L', hL', _⟩ | ⟨_, FQ⟩
        · exact absurd (List.mem_map.mpr ⟨_, hL', rfl⟩) hk
        · refine Or.inr ⟨fun hm => ?_, frontLC_seven_bunt hdp p1 FQ⟩
          rcases plab e.1 hm with h | h
          · exact hk h
          · have := hlab e he; omega
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hn
    obtain ⟨n1, hn1, rb, hb, h | ⟨u, rfl, n2, hn2, hc⟩⟩ := M.fwd hs hm
    · have Gp := Rp.sem cf hcf c ned σ Inv ν O n1 gul hS (oracleFwd_le hF hn1) st t tm s0 s rb hI
        htr hs hb agP hned regs hh hn
      obtain ⟨hnz, rfl⟩ := h
      exact goalSemCMD_ret hnz (returnsC_of_goalSemCMD hnz Gp)
    have Gp := Rp.sem cf hcf c ned σ Inv ν O n1 gul hS (oracleFwd_le hF hn1) st t tm s0 s _ hI
      htr hs hb agP hned regs hh hn
    by_cases fit : FitsS nx.laz.sure u
    · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
      obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
      exact fin r (Rq.sem cf hcf1 c (Need.pair ned dp) σ Inv ν O n2 gul hS (oracleFwd_le hF hn2)
        st' t tm (C s0 wp) u r hI' (frames_mono hν htr) (img_of hs hb) hc agQ hnQ R1 hsQ hnQ') e1
    · have R2 := Gp.2 fit
      rcases (Rq.nec u (img_of hs hb) fit).1 gul n2 tm r hc with e | ⟨v, rfl, nf⟩
      · subst e; exact R2
      · exact ⟨fun f => absurd f nf, fun _ => R2⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hn
    obtain ⟨rb, hb, Gp⟩ := Rp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs agP hned regs hh hn
      res hres
    cases rb with
    | one q =>
      exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e), goalSemCMD_ret (fun _ e => by cases e) Gp⟩
    | two t' =>
      exact ⟨_, (M.bwd hs hb).1 (fun _ e => by cases e), goalSemCMD_ret (fun _ e => by cases e) Gp⟩
    | zero u =>
      have hu : Img lib P fb u := ⟨s, gul, hs, mink_nil_of_mink_zero hb⟩
      by_cases fit : FitsS nx.laz.sure u
      · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
        obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
        obtain ⟨r, hr, Gq⟩ := Rq.semB cf hcf1 c (Need.pair ned dp) σ Inv ν O gul hS hB st' t tm (C s0 wp) u hI'
          (frames_mono hν htr) hu agQ hnQ R1 hsQ hnQ' res (by rw [← e1]; exact hres)
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, fin r Gq e1⟩
      · have R2 := Gp.2 fit
        obtain ⟨r, hr, hbad⟩ := (Rq.nec u hu fit).2 gul tm
        refine ⟨r, (M.bwd hs hb).2 u r rfl hr, ?_⟩
        rcases hbad with e | ⟨v, rfl, nf⟩
        · subst e; exact R2
        · exact ⟨fun f => absurd f nf, fun _ => R2⟩

/-! ## `BondOKC` of `[7 p q]` -/

/-- **`[7 p q]` as a head under the bond goal**: `q` under the bond goal
(`BondOKC`), `p` under `q`'s result (`LOKC`, with the hypotheses from `q`'s
`RunOKLC`), composed by `runOKLC_sevenM`. -/
theorem bondOKC_sevenC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (Bq : BondOKC (S := S) (Map := Map) lib env (Img lib P fb) fc q)
    (M : MinkC7 lib P f fb fc) : BondOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  refine ⟨fun {sup region g0 g1 nex hed b th} h => ?_, fun {sup region g0 g2 nex hed b th jb} hc b0 d0 hu hcl hcb h1
    h2 ha hne hb hbb hd hen h => ?_⟩
  · rw [runLC_n7] at h
    obtain ⟨nx, g1', hq, hp⟩ := bind_some h
    exact Lp.clean (Bq.clean hq) hp
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have hcnt : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  obtain ⟨Qq, Rq⟩ := Bq.run hcnt.2 b0 d0 hu hcl hcb h1 h2 ha hne hb hbb hd hen hq
  have E := entries_bond1 b hed
  have r1 := Rq.re
  have o1 := Rq.bo
  have nsl : ∀ x, ¬ NMem (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]).sure.ned x :=
    fun x hx => absurd hx (by simp [Sure.bunt, NMem])
  have lb : ∀ o, o ∈ (entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)])).map Prod.fst → o = b := fun o ho => by
    rw [E] at ho; simpa using ho
  obtain ⟨⟨Qp, Rp⟩, hj⟩ := Lp.run hcnt.1 (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (hcl.growU Rq.grow)
    (Rq.cfr.below hcb) Rq.lo Rq.hi (nextArgs_nil Rq.ent ha) Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with h' | h'
      · exact absurd h' (nsl x)
      · exact h'.2, Rq.ncond x hx⟩)
    (fun e he => ⟨by
      rcases (Rq.labs e he).1 with h' | h'
      · have := lb _ h'; omega
      · have := Rq.hi; omega, (Rq.labs e he).2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨by
      rcases (Rq.eregs e he).2 x hx with ⟨e0, he0, h0⟩ | h' | h'
      · rw [E] at he0
        simp only [List.mem_singleton] at he0
        subst he0
        have := (hen x h0).1; omega
      · exact absurd h' (nsl x)
      · exact h'.2, Rq.econd e he x hx⟩⟩) hp
  refine ⟨_, runOKLC_sevenM M Rq Rp ?_ (fun r hr => absurd hr (nsl r)) (fun e he => by
    rw [E] at he; simp only [List.mem_singleton] at he; subst he; exact hb)⟩
  rcases hj with e | e
  · rw [e]; exact Nat.le_refl _
  · have := Rq.hi; omega

/-- **`[7 p q]` as a head under the bond goal on every `Annot`**: the forms
`n7`, `inline`, `n9` and the wrappers (`BondOKC.wrap`); `hpc` excludes the
forms of `[8 b c]`. -/
theorem bondOKC_sevenA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p q : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → LOKC (S := S) (Map := Map) lib env P f p)
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → BondOKC (S := S) (Map := Map) lib env P f q)
    (hpc : (∀ a b, p ≠ Nomm.cons a b) ∧ ∀ k, p ≠ Nomm.n1 k)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n7 p q → BondOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | n7 hb hc _ _ => intro e; cases e; exact bondOKC_sevenC lib env (ihp hb) (ihq hc) (minkC7_seven lib _ _ _)
  | inline hb hc hg _ _ => intro e; cases e; exact bondOKC_sevenC lib env (ihp hb) (ihq hg) (minkC7_inline lib hc)
  | n9 hc hr _ _ => intro e; cases e; exact bondOKC_sevenC lib env (ihp hc) (ihq hr) (minkC7_nine lib _ _ _)
  | n8 => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8g => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8l => intro e; cases e; exact absurd rfl (hpc.2 _)
  | memo hm _ ih' => intro e; exact BondOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact BondOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact BondOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | bareLit => intro e; cases e

/-! ## The heads `[7 p q]` of the fragment -/

/-- **The `p` of such a head**: `[0 axe]`, or the indirect call with
call-free parts (`LOKC`). -/
inductive HeadP : Nomm → Prop
  | n0 {axe : Nat} : 1 ≤ axe → HeadP (Nomm.n0 axe)
  | ind {b c : Nomm} : FragU (S := S) b → FragU (S := S) c → bareLitQ c = false → HeadP (Nomm.n2 b c Option.none)

/-- **The `q` of such a head**: a head of `FragB`, or the indirect call with
call-free parts (`BondOKC`). -/
inductive HeadQ : Nomm → Prop
  | b {q : Nomm} : FragB (S := S) q → HeadQ q
  | ind {b c : Nomm} : FragU (S := S) b → FragU (S := S) c → bareLitQ c = false → HeadQ (Nomm.n2 b c Option.none)

theorem lokc_headP {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p : Nomm}
    (h : HeadP (S := S) p) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f p) :
    LOKC (S := S) (Map := Map) lib env P f p := by
  cases h with
  | n0 ha => exact lokc_n0A hok env ha hA
  | ind hb hc hbl => exact lokc_indA hok env hb hc hbl hA rfl

theorem headP_shape {p : Nomm} (h : HeadP (S := S) p) : (∀ a b, p ≠ Nomm.cons a b) ∧ ∀ k, p ≠ Nomm.n1 k := by
  cases h <;> exact ⟨(fun _ _ e => by cases e), (fun _ e => by cases e)⟩

theorem bondOKC_headQ {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {q : Nomm}
    (h : HeadQ (S := S) q) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f q) :
    BondOKC (S := S) (Map := Map) lib env P f q := by
  cases h with
  | b hq =>
    exact bondOKC_of_bondOK (runU_uok lib (fragB_fragU hq))
      (fun s hs gul tm r => mink_pure hok (fragU_pure (fragB_fragU hq)) hA hs gul tm r) (bondOK_of_fragB lib hq)
  | ind hb hc hbl => exact bondOKC_indA hok env hb hc hbl hA rfl

theorem uokc_headQ {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {q : Nomm}
    (h : HeadQ (S := S) q) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f q) :
    UOKC (S := S) (Map := Map) lib env P f q := by
  cases h with
  | b hq => exact uokcU hok env (fragB_fragU hq) hA
  | ind hb hc hbl => exact (uokc_indDA env (uokcU hok env hb) (uokcU hok env hc) hbl hA rfl).1

theorem hinted_head7 (cod : Bell → Option Bool) {p q : Nomm} (hp : HeadP (S := S) p) (hq : HeadQ (S := S) q) :
    hinted cod (Nomm.n7 p q) = some true ∨ (Nomm.n7 p q).pure = true := by
  cases hp with
  | n0 _ =>
    cases hq with
    | b hq' => exact Or.inr (by simp only [Nomm.pure, fragU_pure (fragB_fragU hq'), Bool.and_self])
    | ind _ _ _ => exact Or.inl (by simp only [hinted]; rfl)
  | ind _ _ _ => exact Or.inl (by simp only [hinted]; rfl)

/-- **The head `[7 p q]` meets `UOKC` on every `Annot`**: call-free, by
`FragU` (`hu`); calling, by `uokc_sevenLA`. -/
theorem uokc_head7 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p q : Nomm}
    (hp : HeadP (S := S) p) (hq : HeadQ (S := S) q) (hu : (Nomm.n7 p q).pure = true → FragU (S := S) (Nomm.n7 p q))
    {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f (Nomm.n7 p q)) :
    UOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  rcases hinted_head7 env.cod hp hq with hh | hpu
  · exact (uokc_sevenLA (Xq := True) env (fun h => lokc_headP hok env hp h) (fun h => ⟨uokc_headQ hok env hq h, trivial⟩)
      (headP_shape hp) hh hA rfl).1
  · exact uokcU hok env (hu hpu) hA

/-- **The head `[7 p q]` meets `BondOKC` on every `Annot`.** -/
theorem bondOKC_head7 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p q : Nomm}
    (hp : HeadP (S := S) p) (hq : HeadQ (S := S) q) {P : Noun → Prop} {f : Noun}
    (hA : Annot lib code P f (Nomm.n7 p q)) : BondOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) :=
  bondOKC_sevenA env (fun h => lokc_headP hok env hp h) (fun h => bondOKC_headQ hok env hq h) (headP_shape hp) hA rfl

end Comp
end SkaModel
end Formalization
