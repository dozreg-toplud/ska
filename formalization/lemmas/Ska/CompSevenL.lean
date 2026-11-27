import lemmas.Ska.CompSevenA

/-!
# `[7 p q]` when `q`'s result has entries: `runOKGC_sevenL`

README Gaps 12.21.  `runOKGC_sevenG` asks that `q`'s run return a need
without entries.  When it has entries (the bonds of `+past` behind a call in
`q`, the forks of a `%6`), `p` runs under a goal with entries and must meet
`RunOKLC`: its ops in front of the entries' blocks fill them (`FrontLC`), and
`q` reads them at its run with the input need `pair ned dp`, `dp` the
registers `p` left.  This is the core of `runOKLC_seven` with `q` under any
goal (`RunOKGC`, `%done` among them).

* `runOKGC_sevenL`: both `sem` clauses for any goal.
* `LOKC`: a run under any lazy goal `%next L th` (with the hypotheses that
  `[7 p q]` gives `p`) meets `RunOKLC` for some witness relation, and its
  jump is the goal's or new.  `lokc_n0` (`[0 axe]`, `runOKL_n0_run`),
  `lokc_indirectC` (the indirect call whose parts meet `UOKC`, `kerfLC` after
  `indirectC_inner`, as `bondOKC_indirectC`), `LOKC.wrap`, `lokc_indA`.
* `okc_sevenL`, `uokc_sevenL`, `entNew_sevenL`, `uokc_sevenLA` (the forms
  `n7`, `inline`, `n9`; in the `[8 b c]` forms the `p` part is a cons or a
  literal, which `LOKC` does not cover).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The composition -/

/-- **`[7 p q]` for any goal, `q`'s result with entries**: `RunOKGC` of `q`
under the goal (its subjects the products of `fb`) and `RunOKLC` of `p`
under `q`'s result give `RunOKGC` of the whole for any formula `f` with
`MinkC7`.  `hle`: `p`'s jump is at or after `q`'s; `hg`: the goal's
registers were allocated before the run. -/
theorem runOKGC_sevenL {lib : Lib} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    {goal : CGoal S} {Qp : Wit} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGC (Map := Map) lib (Img lib P fb) fc goal g0 g1 nx)
    (Rp : RunOKLC (Map := Map) lib P fb nx.laz nx.th Qp g1 g2 nex)
    (hle : nx.th.there ≤ nex.th.there) (hg : ∀ r, GMem goal r → r < g0.re) :
    RunOKGC lib P f goal g0 g2 nex := by
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
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g2 nex.laz s0 s) → (∀ x, NMem ned x → g2.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 →
      (∀ st' : σ, AgreeL lib O c gul st' t cf ned g1 g2 nex.laz s0 s) ∧
      ∀ (u : Noun) (st' : σ) (R1 : Map (Option Noun)) (dp : Need) (wp : Noun), Qp s u dp wp → Inv st' →
        ν st ≤ ν st' → FitsS nx.laz.sure u → HoldsN nx.laz.sure.ned R1 u → HoldsN dp R1 wp →
        (∀ x, ((x < g1.re ∨ NMem ned x) ∧ ¬ NMem nx.laz.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs) →
        (∀ st'' : σ, AgreeU lib O c gul st'' t cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u) ∧
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
    · obtain ⟨_, _, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := by have := (Rq.labs e he).2.1; omega
      have hge : g0.bo ≤ e.1 := (Rq.labs e he).1
      obtain ⟨Fp, hFp, Sp'⟩ := Rp.front e he
      have hb2 := hFp [] (Termin.hop th') hb1
      rw [List.append_nil] at hb2
      rcases Sp' cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
      · obtain ⟨A0, th'', hb3, hc3, hf3⟩ := (ag st'').2 (e.1, L') hL'
        rw [hb2] at hb3
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
        obtain ⟨rfl, rfl⟩ := hb3
        refine ⟨A0 ++ ([] : List Pole).map (renPole (unproxy cf)), th', hb1, by simpa using hc3, ?_⟩
        exact (FP lib σ O c gul st'' t ned A0 s0 s u dp wp hned hqp hf3).mono (Nat.le_refl _)
      · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), th', hb1, ?_, ?_⟩
        · rw [(ag st'').1 e.1 hge (by omega) hn2, hb2]
          simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, List.nil_append]
        · exact FP lib σ O c gul st'' t ned [] s0 s u dp wp hned hqp fillSem_bunt_nil
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
    intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    obtain ⟨n1, h1n, rb, hb, hr⟩ := M.fwd hs hm
    have Gp := Rp.sem cf hcf c ned σ Inv ν O n1 gul hS (oracleFwd_le hF h1n) st t tm s0 s rb hI htr hs hb agP
      hned regs hh hn
    rcases hr with ⟨hnz, hr⟩ | ⟨u, rfl, n2, h2n, hc⟩
    · rw [hr]
      exact goalSemCM_ret goal _ hnz (returnsC_of_goalSemCMD hnz Gp)
    by_cases fit : FitsS nx.laz.sure u
    · obtain ⟨st', R1, dp, wp, hI', hν, hqp, h1, hD1, k1, e1⟩ := Gp.1 fit
      obtain ⟨agQ, hnQ, hsQ, hnQ', fin⟩ := K u st' R1 dp wp hqp hI' hν fit h1 hD1 k1
      exact fin r (Rq.sem cf hcf1 c (Need.pair ned dp) σ Inv ν O n2 gul hS (oracleFwd_le hF h2n)
        st' t tm (C s0 wp) u r hI' (frames_mono hν htr) (img_of hs hb) hc agQ hnQ R1 hsQ hnQ') e1
    · exact goalSemCM_of_badC ((Rq.nec u (img_of hs hb) fit).1 gul n2 tm r hc) (Gp.2 fit)
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk' =>
      (hcf k (by omega)).trans (Rp.cfr.get_lt hk')
    obtain ⟨agP, K⟩ := core cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    obtain ⟨rb, hb, Gp⟩ := Rp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs agP hned regs hh hn
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
        obtain ⟨r, hr, Gq⟩ := Rq.semB cf hcf1 c (Need.pair ned dp) σ Inv ν O gul hS hB st' t tm (C s0 wp) u hI'
          (frames_mono hν htr) hu agQ hnQ R1 hsQ hnQ' res (by rw [← e1]; exact hres)
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, fin r Gq e1⟩
      · obtain ⟨r, hr, hbad⟩ := (Rq.nec u hu fit).2 gul tm
        exact ⟨r, (M.bwd hs hb).2 u r rfl hr, goalSemCM_of_badC hbad (Gp.2 fit)⟩

/-! ## Runs under any lazy goal -/

/-- **A run under any lazy goal `%next L th`**, from a state with the
hypotheses that `[7 p q]` gives `p` (`q`'s run's structural fields):
`RunOKLC` for some witness relation, and a jump that is the goal's or new;
and the sure need of every run is clean when the goal's is. -/
structure LOKC (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ th', HoonMap.get g0.blocks e.1 = some ⟨[], [], Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLC (Map := Map) lib P f L th Q g0 g1 nex) ∧ (nex.th = th ∨ g0.bo ≤ nex.th.there)

/-- **`[0 axe]` with `1 ≤ axe` meets `LOKC`** (`runOKL_n01`,
`runOKL_n0_run`, `RunOKL.toLC`): its jump is the goal's. -/
theorem lokc_n0 (lib : Lib) (env : CallEnv) {P : Noun → Prop} {f : Noun} {axe : Nat} (ha : 1 ≤ axe)
    (M : MinkEq lib P f (Nomm.n0 axe)) : LOKC (S := S) (Map := Map) lib env P f (Nomm.n0 axe) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g1 nex} _ _ _ _ _ _ h1 h2 _ hd hsl
    hlab hnd hed h => ?_⟩
  · rw [runLC_eq env _ rfl] at h
    rcases Nat.lt_or_ge axe 2 with lt | ge
    · obtain rfl : axe = 1 := by omega
      rw [runL_n01_next] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
    · rw [runL_n0_next ge] at h
      cases hf : fromL axe L with
      | none => rw [hf] at h; cases h
      | some L' =>
        rw [hf] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact clean_fromSure (fromL_sure hf) hc
  · rw [runLC_eq env _ rfl] at h
    have hemp : ∀ e ∈ entries L, ∃ th', HoonMap.get g0.blocks e.1 = some ⟨[], [], Termin.hop th'⟩ :=
      fun e he => (hlab e he).2
    rcases Nat.lt_or_ge axe 2 with lt | ge
    · obtain rfl : axe = 1 := by omega
      rw [runL_n01_next] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, (runOKL_n01 (Map := Map) lib h1 h2 hd (fun e he => (hed e he).1) hnd hemp
        (fun r hr => (hsl r hr).2) (fun e he r hr => ((hed e he).2 r hr).2) (fun _ => A 0)).toLC M⟩, Or.inl rfl⟩
    · have R := runOKL_n0_run (Map := Map) lib ge h h1 h2 hd (fun e he => (hed e he).1) hnd hemp
        (fun r hr => (hsl r hr).2) (fun e he r hr => ((hed e he).2 r hr).2) (fun _ => A 0)
      refine ⟨⟨_, R.toLC M⟩, Or.inl ?_⟩
      rw [runL_n0_next ge] at h
      cases hf : fromL axe L with
      | none => rw [hf] at h; cases h
      | some L' =>
        rw [hf] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl

/-- **The indirect call whose parts meet `UOKC` meets `LOKC`**: under a
lazy goal `+simple-next` is the identity, `+kerf` fills the goal's blocks
from `pro` (`kerf_specL`), the rest is `indirectC_inner`, and `kerfLC`
composes (as `bondOKC_indirectC` for the bond goal); its jump is new. -/
theorem lokc_indirectC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) : LOKC (S := S) (Map := Map) lib env P f (Nomm.n2 p q Option.none) := by
  refine ⟨fun _ h => indirectC_clean Up Uq h, fun {sup L th region g0 g' nex} hc b0 d0 hu hcl hcb h1 h2 ha hsd
    hsl hlab hnd hed h => ?_⟩
  have hcount : sixCount p + sixCount q ≤ 255 := hc
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, hs1, hk, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs1
  obtain ⟨rfl, rfl⟩ := hs1
  have hlab' : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ :=
    fun e he => by
      obtain ⟨th', hb⟩ := (hlab e he).2
      exact ⟨(hlab e he).1, [], _, hb⟩
  obtain ⟨rfl, rfl, b2, dr2, l2, PF, G2, -, -, -, c0, -⟩ := kerf_specL hk d0 hcb hu h1 h2 hlab' hnd
  have R := indirectC_inner lib Up Uq M hcount (by omega) b0 (by omega) c0 (by omega) (dr2.trans d0) (G2.up hu)
    (hcl.growU G2) (PF.1.below hcb) h3 h4 h5 h6 h7
  exact ⟨⟨_, kerfLC hk d0 hcb hu ha h1 h2 hsd hsl hlab' hnd hed R.1⟩, Or.inr (by have := R.2; omega)⟩

theorem LOKC.wrap {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f f' : Noun} {nm : Nomm}
    (W : WrapRel lib P f f') (B : LOKC (S := S) (Map := Map) lib env P f nm) :
    LOKC (S := S) (Map := Map) lib env P f' nm :=
  ⟨B.clean, fun hc b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed h => by
    obtain ⟨⟨Q, R⟩, j⟩ := B.run hc b0 d0 hu hcl hcb h1 h2 ha hsd hsl hlab hnd hed h
    exact ⟨⟨Q, R.wrap W⟩, j⟩⟩

/-- **The indirect call with call-free parts meets `LOKC` on every
`Annot`** (`lokc_indirectC`, the wrappers by `LOKC.wrap`). -/
theorem lokc_indA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {b c : Nomm}
    (hb : FragU (S := S) b) (hc : FragU (S := S) c) (hbl : bareLitQ c = false)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n2 b c Option.none → LOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | indirect hb' hc' _ _ =>
    intro e
    cases e
    exact lokc_indirectC lib env (uokcU hok env hb hb') (uokcU hok env hc hc') (minkC2_indirect lib _ _ _)
  | bare hf => intro e; cases e; simp [bareLitQ, hf] at hbl
  | bareLit hf _ => intro e; cases e; simp [bareLitQ, hf] at hbl
  | memo hm _ ih' => intro e; exact LOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact LOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact LOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | n11c => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e

/-! ## `UOKC` of `[7 p q]` with `p` under `q`'s lazy result -/

/-- **The pieces of the run of `[7 p q]`** with `q`'s run under the goal
(`RunOKGC` from `UOKC`) and `p`'s under `q`'s lazy result from `LOKC`. -/
theorem sevenL_parts {lib : Lib} {env : CallEnv} {p q : Nomm} {P Pq : Noun → Prop} {fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q)
    {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (hnp : NoPick goal) (ha : GArgs goal) (hj : GJ g0.bo goal) (hok : GoalOK g0 goal) (hcl : GClean goal)
    (hcount : sixCount (Nomm.n7 p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (hkg : ∀ r, GMem goal r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n7 p q) (CGoal.toL goal) region g0 = some (nex, g2)) :
    ∃ (nx : NextL S) (g1 : Gen Map) (Q : Wit), RunOKGC lib Pq fc goal g0 g1 nx ∧
      runLC env (some p) q (CGoal.toL goal) region g0 = some (nx, g1) ∧
      RunOKLC (Map := Map) lib P fb nx.laz nx.th Q g1 g2 nex ∧ (nex.th = nx.th ∨ g1.bo ≤ nex.th.there) ∧
      (∀ r, GMem goal r → r < g0.re) := by
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have Rq := Uq.run hnp ha hj hok hcl hc.2 b0 d0 hu hcl0 hcb hkg hq
  have hg : ∀ r, GMem goal r → r < g0.re := fun r hr => by
    cases goal with
    | next sur th => exact hok.2 r hr
    | done => exact hr.elim
    | pick z o => exact hr.elim
  have nxL : ∀ r, NMem nx.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases Rq.regs r hr with h' | h'
    · have := hg r h'; have := Rq.ext.1; omega
    · exact h'.2
  obtain ⟨⟨Q, Rp⟩, hjp⟩ := Lp.run hc.1 (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
    (hcl0.growU Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi (entry_args Rq.ent ha hnp) Rq.dist
    (fun x hx => ⟨nxL x hx, Rq.ncond x hx⟩)
    (fun e he => ⟨by have := (Rq.labs e he).2.1; have := Rq.hi; omega, (Rq.labs e he).2.2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩) hp
  exact ⟨nx, g1, Q, Rq, hq, Rp, hjp, hg⟩

/-- **`[7 p q]` with `p` meeting `LOKC` and `q` meeting `UOKC` meets `OKCN`**
for a formula with `MinkC7` (`runOKGC_sevenL`), whatever `q`'s result. -/
theorem okc_sevenL (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p)
    (Uq : UOKC (S := S) (Map := Map) lib env (Img lib P fb) fc q) (M : MinkC7 lib P f fb fc) :
    OKCN (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  intro sup goal region g0 g2 nex hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  obtain ⟨nx, g1, Q, Rq, _, Rp, hjp, hg⟩ := sevenL_parts Lp Uq hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  refine runOKGC_sevenL M Rq Rp ?_ hg
  rcases hjp with e | e
  · rw [e]; exact Nat.le_refl _
  · have := Rq.hi; omega

/-- **`[7 p q]` with `p` meeting `LOKC` and `q` meeting `UOKC` meets `UOKC`**
when it is hinted. -/
theorem uokc_sevenL (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p)
    (Uq : UOKC (S := S) (Map := Map) lib env (Img lib P fb) fc q) (M : MinkC7 lib P f fb fc)
    (hh : hinted env.cod (Nomm.n7 p q) = some true) : UOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) := by
  refine ⟨Or.inr hh, fun {sup goal region g0 g2 nex} hnp hcl h => ?_, okc_sevenL lib env Lp Uq M⟩
  rw [runLC_n7] at h
  obtain ⟨nx, g1, hq, hp⟩ := bind_some h
  exact Lp.clean (Uq.clean hnp hcl hq) hp

/-- **`[7 p q]` with `p` meeting `LOKC` meets `EntNew` when `q` does**: `p`'s
jump is `q`'s or new. -/
theorem entNew_sevenL {lib : Lib} {env : CallEnv} {p q : Nomm} {P Pq : Noun → Prop} {fb fc : Noun}
    (Lp : LOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q)
    (Eq : EntNew (S := S) (Map := Map) env q) : EntNew (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup sur th region g0 g2 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  obtain ⟨nx, g1, Q, Rq, hq, Rp, hjp, _⟩ :=
    sevenL_parts (goal := CGoal.next sur th) Lp Uq trivial hth hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have q2 := Rq.ext.2.1
  rcases hjp with e | e
  · rw [e]
    have hc : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
    exact Eq hj hth hok hcl hc b0 d0 hu hcl0 hcb hkg hq
  · omega

/-- **`[7 p q]` with `p` meeting `LOKC` on every `Annot`**: the forms `n7`,
`inline`, `n9` (`minkC7_seven`, `minkC7_inline`, `minkC7_nine`) and the
wrappers; in the forms of `[8 b c]` the `p` part is a cons or a literal,
which `hpc` excludes.  `EntNew` from `q`'s. -/
theorem uokc_sevenLA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p q : Nomm} {Xq : Prop}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → LOKC (S := S) (Map := Map) lib env P f p)
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → UOKC (S := S) (Map := Map) lib env P f q ∧ Xq)
    (hpc : (∀ a b, p ≠ Nomm.cons a b) ∧ ∀ k, p ≠ Nomm.n1 k) (hh : hinted env.cod (Nomm.n7 p q) = some true)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n7 p q → UOKC (S := S) (Map := Map) lib env P f nm ∧
      ((Xq → EntNew (S := S) (Map := Map) env q) → EntNew (S := S) (Map := Map) env nm) := by
  induction hA with
  | n7 hb hc _ _ =>
    intro e; cases e
    exact ⟨uokc_sevenL lib env (ihp hb) (ihq hc).1 (minkC7_seven lib _ _ _) hh,
      fun H => entNew_sevenL (ihp hb) (ihq hc).1 (H (ihq hc).2)⟩
  | inline hb hc hg _ _ =>
    intro e; cases e
    exact ⟨uokc_sevenL lib env (ihp hb) (ihq hg).1 (minkC7_inline lib hc) hh,
      fun H => entNew_sevenL (ihp hb) (ihq hg).1 (H (ihq hg).2)⟩
  | n9 hc hr _ _ =>
    intro e; cases e
    exact ⟨uokc_sevenL lib env (ihp hc) (ihq hr).1 (minkC7_nine lib _ _ _) hh,
      fun H => entNew_sevenL (ihp hc) (ihq hr).1 (H (ihq hr).2)⟩
  | n8 => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8g => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8l => intro e; cases e; exact absurd rfl (hpc.2 _)
  | memo hm _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_memo hm) (ih' e).1, (ih' e).2⟩
  | six0 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | six1 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
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
  | n11c => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | bareLit => intro e; cases e

/-- **`[0 axe]` with `1 ≤ axe` meets `LOKC` on every `Annot`.** -/
theorem lokc_n0A {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {axe : Nat}
    (ha : 1 ≤ axe) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f (Nomm.n0 axe)) :
    LOKC (S := S) (Map := Map) lib env P f (Nomm.n0 axe) :=
  lokc_n0 lib env ha (fun s hs gul tm r => mink_pure hok rfl hA hs gul tm r)

end Comp
end SkaModel
end Formalization
