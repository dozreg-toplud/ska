import lemmas.Ska.CompLBSeven

/-!
# Runs for any goal with bodies at the entries, `[7 p q]` under `%done`, the top

README Gaps 12.23.  `RunOKGC` (`CompUOKC.lean`), the relation of a run that
may call under a goal without entries (`%done`, `%pick`, fork-free `%next`),
asks every result entry's block to be empty, which is false for `%bc1`
under `%done` (the bond of `q` keeps `p`'s `[con v6 v7 v2]`): `UOKC` itself
is false for that nomm.  `RunOKGB` is `RunOKGC` with bodies (`labs` with
`⟨[], B, hop th⟩`, `AgreeUB` with the program's block `A ++ B` unproxied);
it replaces `RunOKGC` under `%done`, and the top-level contract follows
from it as from `RunOKGC` (`finishLUC_contractGB`).

* `AgreeUB`, `SemGB`, `SemGBB`, `RunOKGB`; `RunOKGC.toB`.
* `runOKGB_sevenL`: `[7 p q]` for any goal, `q` with `RunOKGB`, `p` with
  `RunOKLB` (`x = false`) under `q`'s result (`runOKGC_sevenL` with bodies).
* `TopSB`, `finishTop_genB`, `finishLUC_contractGB`: the whole-subject code
  of a nomm whose run under `%done` meets `RunOKGB` meets both halves of the
  contract.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- **`AgreeU` with bodies.** -/
def AgreeUB (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (cond : Map (Nat × List Nat)) (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cond)) ∧
  ∀ e ∈ entries laz, ∃ A B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A ++ B.map (renPole (unproxy cond)), Termin.hop (renJmp (unproxy cond) th)⟩ ∧
    FillSem lib O c gul st t ned g1.re e.2.sure A s0 s

theorem AgreeUB.toU {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeUB lib O c gul st t cond ned g0 g1 laz s0 s)
    (hl : ∀ e ∈ entries laz, ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩) :
    AgreeU lib O c gul st t cond ned g0 g1 laz s0 s := by
  refine ⟨h.1, fun e he => ?_⟩
  obtain ⟨A, B, th, h1, h2, h3⟩ := h.2 e he
  obtain ⟨th', h1'⟩ := hl e he
  rw [h1'] at h1
  simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact ⟨A, th', h1', by simpa using h2, h3⟩

/-- **The forward `sem` of `RunOKGB`** (`SemGC` with `AgreeUB`). -/
def SemGB (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ st' : σ, AgreeUB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **The backward `sem` of `RunOKGB`** (`SemGCB` with `AgreeUB`). -/
def SemGBB (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ st' : σ, AgreeUB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **`RunOKGC` with bodies at the result entries.** -/
structure RunOKGB (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (GMem goal r ∨ g0.re ≤ r) ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f goal s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemGB lib N P f goal g0 g1 nex
  semB : SemGBB lib N P f goal g0 g1 nex

/-- **`RunOKGC` is `RunOKGB` with empty bodies.** -/
theorem RunOKGC.toB {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKGC (Map := Map) lib P f goal g0 g1 nex) : RunOKGB lib N P f goal g0 g1 nex := by
  have hl : ∀ e ∈ entries nex.laz, ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ :=
    fun e he => (R.labs e he).2.2
  refine ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs,
    fun e he => ⟨(R.labs e he).1, by have := (R.labs e he).2.1; have := R.hi; omega, [], (R.labs e he).2.2⟩,
    R.nodup, R.nec, R.ncond, R.econd,
    ?_, ?_⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm (fun st' => (ag st').toU hl) hned
      regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs (fun st' => (ag st').toU hl) hned regs
      hh hn res hres

/-! ## `[7 p q]`, `q`'s result with entries -/

/-- **`[7 p q]` for any goal with bodies** (`runOKGC_sevenL` for `RunOKGB`
and `RunOKLB`): `p` reads no goal register (`x = false`). -/
theorem runOKGB_sevenL {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    {goal : CGoal S} {Qp : Wit} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGB (Map := Map) lib N (Img lib P fb) fc goal g0 g1 nx)
    (Rp : RunOKLB (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hg : ∀ r, GMem goal r → r < g0.re) :
    RunOKGB lib N P f goal g0 g2 nex := by
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
  -- the shared part of the two `sem` clauses
  have core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun),
      (∀ st' : σ, AgreeUB lib O c gul st' t cf ned g0 g2 nex.laz s0 s) → (∀ x, NMem ned x → g2.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 →
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g1 g2 nex.laz s0 s) ∧
      ∀ (u : Noun) (st' : σ) (R1 : Map (Option Noun)) (dp : Need) (wp : Noun), Qp s u dp wp → Inv st' →
        ν st ≤ ν st' → FitsS nx.laz.sure u → HoldsN nx.laz.sure.ned R1 u → HoldsN dp R1 wp →
        (∀ x, ((x < g1.re ∨ NMem ned x) ∧ ¬ NMem nx.laz.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs) →
        (∀ st'' : σ, AgreeUB lib O c gul st'' t cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u) ∧
        (∀ x, NMem (Need.pair ned dp) x → g1.re ≤ x) ∧ HoldsS nx.laz.sure R1 u ∧
        HoldsN (Need.pair ned dp) R1 (C s0 wp) ∧
        ∀ r, GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem (Need.pair ned dp) x) ∧ ¬ GMem goal x)
            st' R1 t tm nx.th goal r →
          goJ lib O c gul st regs t nex.th = goJ lib O c gul st' R1 t nx.th →
          GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm
            nex.th goal r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    refine ⟨fun st' => ⟨fun o l u hnl => (ag st').1 o (by omega) u hnl, fun e he _ => (ag st').2 e he⟩,
      fun u st' R1 dp wp hqp hI' hν fit h1 hD1 k1 => ?_⟩
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
      have := nxL x hm; have := hned x hx; omega⟩) hn
    refine ⟨fun st'' => ⟨fun o l u' hnl => ?_, fun e he => ?_⟩,
      fun r hr => hr.elim (fun h => by have := hned r h; omega) (fun h => (hdp s u dp wp r hqp h).1),
      ⟨h1, fit.2⟩, ⟨hn1, hD1⟩, fun r G e1 => ?_⟩
    · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
        rcases plab o hm with h | h
        · exact hnl h
        · omega
      rw [(ag st'').1 o l (by omega) hn2, Rp.keep o u' hnl]
    · obtain ⟨hge, _, Bq, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := by have := (Rq.labs e he).2.1; omega
      obtain ⟨Fp, hFp, Sp'⟩ := Rp.front e he
      have hb2 := hFp Bq (Termin.hop th') hb1
      rcases Sp' cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
      · obtain ⟨A0, B2, th'', hb3, hc3, hf3⟩ := (ag st'').2 (e.1, L') hL'
        rw [hb2] at hb3
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
        obtain ⟨rfl, rfl⟩ := hb3
        refine ⟨A0 ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, by rw [hc3]; simp, ?_⟩
        exact ((FP lib σ O c gul st'' t ned A0 s0 s u dp wp hned hqp hf3).conv (N1 := Need.pair ned dp)
          (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))).mono (Nat.le_refl _)
      · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, ?_, ?_⟩
        · rw [(ag st'').1 e.1 hge (by omega) hn2, hb2]
          simp [unproxyBlob, renBlob, renFin]
        · exact (FP lib σ O c gul st'' t ned [] s0 s u dp wp hned hqp fillSem_bunt_nil).conv
            (N1 := Need.pair ned dp) (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))
    · refine goalSemCM_step hν (fun x hx => k1 x ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hm => ?_⟩) e1
        goal r (goalSemCM_monoK (fun x hx => ⟨hx.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hx.2⟩) goal r G)
      rcases Rq.regs x hm with h | h
      · exact hx.2 h
      · rcases hx.1 with h' | h'
        · omega
        · have := hned x h'; omega
  refine ⟨⟨by omega, by omega, Rp.drop.trans Rq.ext.2.2.1, fun o ho => ?_⟩, Rq.grow.trans Rp.grow,
    Rq.cfr.trans Rp.cfr, Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ⟨(Rp.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ?_, Rp.nodup, fun s hs hf => ?_, Rp.ncond, Rp.econd, ?_, ?_⟩
  · -- ext
    have hn' : o ∉ (entries nx.laz).map Prod.fst := fun hm => by have := (qlab o hm).1; omega
    exact (Rp.keep o (by omega) hn').trans (Rq.ext.2.2.2 o ho)
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

/-! ## Runs under any lazy goal -/


/-! ## The top -/

/-- **`TopS` with bodies at the result entries.** -/
structure TopSB (g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext gen0 g1
  grow : GrowU gen0 g1
  cfr : CondFresh gen0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  args : nex.th.args = []
  regs : ∀ r, NMem nex.laz.sure.ned r → (gen0 : Gen Map).re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (gen0 : Gen Map).re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, (gen0 : Gen Map).bo ≤ e.1 ∧ e.1 < g1.bo ∧
    ∃ B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none

/-- **`finishTop_gen` with the program agreeing at every state**: the
`AgreeU` handed to `hsem` holds at every state of the oracle, as a run that
calls asks (`SemNC`).  Generated by `tools/gen/topall.py`. -/
theorem finishTop_genB (lib : Lib) {g1 : Gen Map} {nex : NextL S} (R : TopSB g1 nex)
    (Φ : (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop)
    (hsem : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      (∀ st' : σ, AgreeUB lib O c gul st' t cf ned gen0 g1 nex.laz s s) → (∀ r, NMem ned r → g1.re ≤ r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
      Φ σ O st t gul s (goJ lib O c gul st regs t nex.th))
    (hnec : ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → Φ σ O st t gul s (some (Tone.two t, st)))
    {o sub : Nat} {g3 : Gen Map} (h2 : kerf nex g1 = some ((o, sub), g3))
    {c' : Straight Map} (hts : toStraightF g3.cond g3.blocks (Need.this sub) o = some c') :
    c'.need = NeedOrd.this ∧ ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (t : Trace) (gul : Noun),
      Φ σ O st t gul s (execEntry lib O st c' [s] t gul) := by
  have d1 : g1.drop = false := R.ext.2.2.1
  have cb1 : CondBelow g1 := R.cfr.below condBelow_gen0
  -- `+kerf`: the hop block, then `+kern`
  unfold kerf at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, g4, h3, h4⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have lt0 : nex.th.there < g1.bo := R.hi
  have hlab : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => (R.labs e he).2.1
  have hn : (((g1.bo, nex.laz) :: entries nex.laz).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := hlab e he; omega, R.nodup⟩
  have cbe : CondBelow (g1.emitted ⟨[], [], Termin.hop nex.th⟩) := cb1
  obtain ⟨hr, W⟩ := kern_spec h3 d1 cbe hn
  simp only [Gen.emitted] at hr
  subst hr
  have eblk : ∀ k, HoonMap.get (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  -- the blocks after `+kern`
  obtain ⟨A0, hA0, P0⟩ := W.at_ (g1.bo, nex.laz) List.mem_cons_self
  have hB0 : HoonMap.get g4.blocks g1.bo = some ⟨[], A0, Termin.hop nex.th⟩ := by
    have := hA0 [] (Termin.hop nex.th) (by simp only [eblk]; simp)
    simpa using this
  have hE : ∀ e ∈ entries nex.laz, ∃ A B th, HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th⟩ ∧
      HoonMap.get g4.blocks e.1 = some ⟨[], A ++ B, Termin.hop th⟩ ∧
      KernP g1.re g4.cond (g1.re + 1) g4.re e.1 e.2.sure A := by
    intro e he
    obtain ⟨_, _, B, th, hth⟩ := R.labs e he
    obtain ⟨A, hA, P⟩ := W.at_ e (List.mem_cons_of_mem _ he)
    refine ⟨A, B, th, hth, ?_, P⟩
    have := hA B (Termin.hop th) (by
      have ne : e.1 ≠ g1.bo := by have := hlab e he; omega
      simp only [eblk, ne, ↓reduceIte]; exact hth)
    simpa using this
  have hO : ∀ k, k ≠ g1.bo → k ∉ (entries nex.laz).map Prod.fst → HoonMap.get g4.blocks k = HoonMap.get g1.blocks k := by
    intro k k1 k2
    rw [W.other k (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨k1, k2⟩)]
    simp only [eblk, k1, ↓reduceIte]
  -- the program: the blocks unproxied
  let c1 : Straight Map := ⟨NeedOrd.none, 0, mapVals (unproxyBlob g4.cond) g4.blocks⟩
  have hag : ∀ k, HoonMap.get c1.blocks k = (HoonMap.get g4.blocks k).map (unproxyBlob g4.cond) :=
    fun k => get_mapVals _ _ k
  have D1 := downRk_gen0 (R.grow.trans (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩)
    (fun j hj => by simp [finJumps] at hj; subst hj; exact ⟨R.lo, lt0⟩) (upBelow_of_growU R.grow)))
  have D4 := downRk_of_fins D1 (bs' := g4.blocks) fun k b' hk => by
    by_cases e1 : k = g1.bo
    · subst e1; rw [hB0] at hk; cases hk; exact ⟨⟨[], [], Termin.hop nex.th⟩, by rw [eblk]; simp, rfl⟩
    by_cases e2 : k ∈ (entries nex.laz).map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e2
      obtain ⟨A, B, th, h1', h4', _⟩ := hE e he
      rw [h4'] at hk; cases hk
      exact ⟨⟨[], B, Termin.hop th⟩, by rw [eblk, if_neg e1]; exact h1', rfl⟩
    · rw [hO k e1 e2] at hk; exact ⟨b', by rw [eblk, if_neg e1]; exact hk, rfl⟩
  have Dc : DownRk (upRk (g1.emitted ⟨[], [], Termin.hop nex.th⟩).blocks) c1.blocks := by
    intro k b hk
    rw [hag k] at hk
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hk
    exact downRk_unproxy _ (D4 k b0 hb0)
  obtain ⟨hneed, start, hst, hent⟩ := toStraightF_entryU hts (by simp [flattenNeed, isRun]) D4 Dc
    (fun k _ => hag k)
  rw [hB0] at hst; cases hst
  refine ⟨hneed, fun σ O st s t gul => ?_⟩
  obtain ⟨R0, hR0, he⟩ := hent lib O st s [s] t gul (by rw [hneed]; rfl)
  rw [he]
  have ag4 : ∀ k, k < g1.re + 1 → HoonMap.get g4.cond k = HoonMap.get g1.cond k := fun k hk => W.cnd.1.get_lt hk
  have u4r : HoonMap.get g4.cond g1.re = Option.none := by
    rw [ag4 _ (Nat.lt_succ_self _)]; exact condBelow_none cb1 (Nat.le_refl _)
  have regs1 : ∀ x, NMem nex.laz.sure.ned x → x < g1.re := fun x hx => (R.regs x hx).2
  have hj : nex.th.args = [] := R.args
  have hrj : renJmp (unproxy g4.cond) nex.th = nex.th := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hj; simp only at hj; subst hj; rfl
  -- the agreement of the program with the run's blocks
  have ag : ∀ st' : σ, AgreeUB lib O c1 gul st' t g4.cond (Need.this g1.re) gen0 g1 nex.laz s s := fun st' => by
    refine ⟨fun o' _ u hnl => ?_, fun e he => ?_⟩
    · rw [hag o', hO o' (by omega) hnl]
    · obtain ⟨A, B, th, h1', h4', P⟩ := hE e he
      refine ⟨A.map (renPole (unproxy g4.cond)), B, th, h1', ?_, ?_⟩
      · rw [hag, h4']; simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, List.map_append]
      · obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P
        have l0' : g1.re + 1 ≤ lo0 := l0
        have regsE : ∀ x, NMem e.2.sure.ned x → x < g1.re := fun x hx => ((R.eregs e he).2 x hx).2
        have KS := sem (by omega) (R.eregs e he).1 regsE (unproxy g4.cond) (unproxy_none u4r)
          (fun x hx => unproxy_none (by rw [ag4 x (by have := regsE x hx; omega)]; exact R.econd e he x hx))
          (fun _ _ => rfl)
        intro R hR
        obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st' t R s hR
        refine ⟨fun f => ?_, S2⟩
        obtain ⟨R', a, b, k⟩ := S1 f
        exact ⟨R', a, b, fun x hx hn => k x (by
          rcases hx with hx | hx
          · simp only [NMem] at hx; omega
          · omega) hn⟩
  -- the ops at the hop block, then the run
  obtain ⟨lo0, hi0, l0, _, src, _, _, sem⟩ := P0
  have l0' : g1.re + 1 ≤ lo0 := l0
  have KS := sem (by omega) R.dist regs1 (unproxy g4.cond) (unproxy_none u4r)
    (fun x hx => unproxy_none (by rw [ag4 x (by have := regs1 x hx; omega)]; exact R.ncond x hx))
    (fun _ _ => rfl)
  obtain ⟨S1, S2⟩ := KS lib σ O c1 gul st t R0 s hR0
  simp only [unproxyBlob, renBlob, List.map_nil, renFin, hrj]
  by_cases fo : FitsS nex.laz.sure s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := S1 fo
    have e1 := hr1 [] (Termin.hop nex.th)
    simp only [List.append_nil] at e1
    rw [e1, execBlob_hop]
    have hn1 : HoldsN (Need.this g1.re) R1 s := by
      show SkaModel.read g1.re R1 = some s
      rw [kr1 g1.re (by omega) (fun hm => by have := regs1 _ hm; omega)]; exact hR0
    exact hsem g4.cond (fun k hk => ag4 k (by omega)) c1 (Need.this g1.re) σ O st t gul s ag
      (fun x hx => by simp only [NMem] at hx; omega) R1 hh1 hn1
  · have e2 := S2 fo [] (Termin.hop nex.th)
    simp only [List.append_nil] at e2
    rw [e2]; exact hnec σ O st t gul s fo

/-- **The contract from `RunOKGB` under `%done`** (`finishLUC_contractG`
with bodies): the whole-subject code of a nomm whose run for `%done` from
`gen0` meets `RunOKGB` at the needs `N` has the need `this` and meets both
halves of the contract for `N` on the subjects of `P`. -/
theorem finishLUC_contractGB (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nex)
    {c : Straight Map} (h : finishLUC (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  unfold finishLUC at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  have R : RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nex := hR hr
  have T : TopSB gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTop_genB lib T (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) hk hts
  have B := finishTop_genB lib T (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs => ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩⟩
  · exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr
  · exact B.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

end Comp
end SkaModel
end Formalization
