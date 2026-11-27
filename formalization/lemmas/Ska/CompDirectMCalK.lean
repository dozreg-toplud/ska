import lemmas.Ska.CompDirectMMerge
import lemmas.Ska.CompIndirectLS
import lemmas.Ska.CompLBDone

/-!
# The direct call under `%next` with `mono` `&`: the pieces around the blocks

README Gaps 18.13 (track J, 2026-11-27).  `callLBM` (`CompDirectMCal.lean`)
needs three variants of existing lemmas, because `+need-ord-alloc-regs`
allocates the callee's registers `sub` before `+kerf`, and the tree of
`+mono-try-call` writes them:

* `kerfLBM`: `kerfLB` (`CompIndirectLS.lean`, track C's, unchanged) for a
  `+kerf` that starts from `{g0 with re := k}` (the callee's registers
  allocated from `g0`), with the inner run as `RunOKGB` from the state after
  `+kerf` with its registers lowered back to `g0.re`: it keeps only the
  registers below `g0.re`.
* `runOKGB_sevenLW`: `runOKGB_sevenL` (`CompLBDone.lean`, unchanged) with
  the goal's registers below the state between the two parts (`g1`), not
  below the start: the goal's register `pro` comes from `+kerf`, after
  `g0.re`.
* `monoTry_goW`: `monoTry_go` (`CompDirectMGo.lean`) that also keeps the
  registers at or above the state the tree leaves (the caller's own
  registers, which `RunOKGB`'s `K` keeps).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

section

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+kerf` after the callee's registers -/

/-- **`CondFresh` from a state with more registers.** -/
theorem CondFresh.lower {g g' : Gen Map} {k : Nat} (h : CondFresh ({ g with re := k } : Gen Map) g') (hk : g.re ≤ k) :
    CondFresh g g' := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  exact ⟨by omega, fun x => (h2 x).imp id (fun ⟨a, b⟩ => ⟨by omega, b⟩)⟩

/-- **`kerfLB` for a call whose registers come before `+kerf`**: the
callee's registers are allocated from `g0` (to `k`) before `+kerf`, which
starts from `{g0 with re := k}`; the inner run is `RunOKGB` under `%next
(lazy-from-reg pro) (jmp0 out)` from the state after `+kerf` with its
registers lowered back to `g0.re`, so that it keeps only the registers below
`g0.re` (the callee's registers, `pro` and those of `+kerf` it may write).
The result is `RunOKLS` from `g0` with the witness `kernWit pro`. -/
theorem kerfLBM {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {g0 g2 g' : Gen Map}
    {k out pro : Nat} {nex : NextL S}
    (hk : kerf (⟨L, th⟩ : NextL S) ({ g0 with re := k } : Gen Map) = some ((out, pro), g2)) (hk0 : g0.re ≤ k)
    (d0 : g0.drop = false) (hcb : CondBelow g0)
    (hu : UpBelow g0) (hth : th.args = []) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hre : g2.re ≤ g'.re) (hcf' : CondFresh g2 g')
    (R : RunOKGB (Map := Map) lib N P f (CGoal.next (lazyReg pro : Sure S) (jmp0 out))
      ({ g2 with re := g0.re } : Gen Map) g' nex) :
    RunOKLS (Map := Map) lib N P f L th (kernWit pro) false g0 g' nex := by
  have hcbk : CondBelow ({ g0 with re := k } : Gen Map) := fun x hx => by
    have := hcb x hx; show x < k; omega
  obtain ⟨eo, ep, b2, dr2, l2, PF, G2, ⟨A0, hB0, P0⟩, hE, hO, c0, crng⟩ := kerf_specL hk d0 hcbk hu h1 h2 hlab hnd
  simp only at eo ep b2 dr2 l2 hB0 P0 hE hO c0 crng
  subst out pro
  have hsl' : ∀ x, NMem L.sure.ned x → x < k ∧ HoonMap.get g0.cond x = Option.none := fun x hx =>
    ⟨by have := (hsl x hx).1; omega, (hsl x hx).2⟩
  have hed' : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < k ∧ HoonMap.get g0.cond x = Option.none := fun e he =>
    ⟨(hed e he).1, fun x hx => ⟨by have := ((hed e he).2 x hx).1; omega, ((hed e he).2 x hx).2⟩⟩
  have PFl : ∀ {x : Nat}, x < k → HoonMap.get g2.cond x = HoonMap.get g0.cond x := fun hx => PF.1.get_lt hx
  have e2 : entries (ofSure (lazyReg k : Sure S)) = [] := entries_ofSure _
  have Re : Ext g2 g' := ⟨hre, R.ext.2.1, R.ext.2.2.1, fun o ho => R.ext.2.2.2 o ho⟩
  have rl := hre
  have bl : g2.bo ≤ g'.bo := R.ext.2.1
  have Rg : GrowU g2 g' := ⟨R.grow.bo, R.grow.drop, R.grow.keep, R.grow.new⟩
  have G2' : GrowU g0 g2 := ⟨G2.bo, G2.drop, G2.keep, G2.new⟩
  have lab' : ∀ e ∈ entries nex.laz, g2.bo ≤ e.1 := fun e he => (R.labs e he).1
  -- the later `cond`s
  have hcf2 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun cf hcf x hx =>
    (hcf x (by omega)).trans (hcf'.get_lt hx)
  have hfill : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ {sur : Sure S} {A : List Pole} {o : Nat}, KernPW (Map := Map) k g2.cond (k + 1) g2.re o sur A →
      Distinct sur.ned → (∀ x, NMem sur.ned x → x < k ∧ HoonMap.get g0.cond x = Option.none) →
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
        (R : Map (Option Noun)) (v : Noun), SkaModel.read k R = some v →
      (FitsS sur v → ∃ R', Runs lib O c gul st t (A.map (renPole (unproxy cf))) R R' ∧ HoldsS sur R' v ∧
        ∀ x, (x < k + 1 ∨ (g2.re ≤ x ∧ x ≠ k)) → ¬ NMem sur.ned x →
          SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ FitsS sur v → Crashes lib O c gul st t (A.map (renPole (unproxy cf))) R) :=
    fun cf hcf sur A o KP hd hsl' => kernPW_fill KP (by omega) hd (fun x hx => (hsl' x hx).1)
      (by rw [hcf2 cf hcf _ (by omega)]; exact c0)
      (fun x hx => by rw [hcf2 cf hcf _ (by have := (hsl' x hx).1; omega), PFl (hsl' x hx).1]; exact (hsl' x hx).2)
      (hcf2 cf hcf)
      (fun x a b => by
        rcases crng x (by omega) with e | ⟨tag, e⟩
        · exact Or.inl (unproxy_none (by rw [hcf2 cf hcf x b]; exact e))
        · exact Or.inr (by simp only [unproxy, hcf2 cf hcf x b, e]))
  -- the shared part of the two `sem` clauses: through the block `out`
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g' nex.laz s0 s) → (∀ x, NMem ned x → g'.re ≤ x) →
      Forall2 (FrameRel lib (ν st)) t tm → ∀ r,
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg k : Sure S)
        (jmp0 g0.bo)) x) st regs t tm nex.th (CGoal.next (lazyReg k : Sure S) (jmp0 g0.bo)) r →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
        L.sure th (kernWit k s) r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r G
    have hbo : HoonMap.get c.blocks g0.bo = some ⟨[], A0.map (renPole (unproxy cf)), Termin.hop th⟩ := by
      rw [(ag st).1 g0.bo (Nat.le_refl _) (by omega) (fun hm => by
        obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lab' e he; omega), Re.2.2.2 _ (by omega), hB0]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hth]
    cases r with
    | one q => exact G
    | two t' => exact G
    | zero p =>
      obtain ⟨st1, R1, hI1, hν1, hp1, k1, e1⟩ := G.1 (fitsS_lazyReg _ p)
      obtain ⟨F1, F2⟩ := hfill cf hcf P0 hsd hsl' lib σ O c gul st1 t R1 p hp1
      refine ⟨fun fp => ?_, fun nf => ?_⟩
      · obtain ⟨R2, r2, hh2, k2⟩ := F1 fp
        have e2 : goJ lib O c gul st1 R1 t (jmp0 g0.bo) = goJ lib O c gul st1 R2 t th := by
          have := r2 [] (Termin.hop th)
          simp only [List.append_nil] at this
          rw [goJ_jmp0 _ _ _ _ hbo, this, execBlob_hop]
        refine ⟨st1, R2, Need.this k, p, hI1, hν1, ⟨rfl, rfl⟩, hh2.1,
          (k2 k (Or.inl (by omega)) (fun hm => by have := (hsl' _ hm).1; omega)).trans hp1,
          fun x ⟨x1, x2⟩ => ?_, e1.trans e2⟩
        rw [k2 x (x1.elim (fun h => Or.inl (by omega)) (fun h => Or.inr ⟨by have := hned x h; omega, by
          have := hned x h; omega⟩)) x2]
        exact k1 x ⟨x1, fun e => by
          simp only [GMem, lazyReg, NMem] at e
          rcases x1 with h | h
          · omega
          · have := hned x h; omega⟩
      · exact ⟨Tone.two t, st1, hI1, hν1, by
          rw [e1, goJ_jmp0 _ _ _ _ hbo]
          have := F2 nf [] (Termin.hop th)
          simp only [List.append_nil] at this
          exact this, ToneRel.two (frames_mono hν1 htr)⟩
  have agR : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun), (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g' nex.laz s0 s) →
      ∀ st' : σ, AgreeUB lib O c gul st' t cf ned ({ g2 with re := g0.re } : Gen Map) g' nex.laz s0 s :=
    fun cf c ned σ O gul t s0 s ag st' =>
      ⟨fun o h0 h1 hn => (ag st').1 o (by simp only at h0; omega) h1 hn,
       fun e he => (ag st').2 e he (by have := lab' e he; omega)⟩
  -- the fronts at the state level
  have FS : FrontsS (Map := Map) (kernWit k) false g0 g' L nex := by
    intro e he
    obtain ⟨A, hA, KP⟩ := hE e he
    refine ⟨A, fun B fin hb => by rw [Re.2.2.2 _ (by have := (hlab e he).1; omega)]; exact hA B fin hb,
      fun cf hcf => Or.inr ⟨fun hm => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; have := (hlab e he).1; omega, ?_⟩⟩
    refine ⟨fun r hr => by simp [Sure.bunt, NMem] at hr, fun s v d w _ r _ hr => by simp [Sure.bunt, NMem] at hr,
      fun s v d w _ _ => fitsS_bunt s, fun lib σ O c gul st t R0 s v d w hq _ hd _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨F1, F2⟩ := hfill cf hcf KP (hed' e he).1 (hed' e he).2 lib σ O c gul st t R0 w hd
    refine ⟨fun fv => ?_, F2⟩
    obtain ⟨R2, r2, hh2, k2⟩ := F1 fv
    refine ⟨R2, r2, hh2, fun x hx hn' => k2 x ?_ hn'⟩
    rcases hx with h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
    · simp only [NMem] at h; subst h; exact Or.inl (by omega)
  have dreg : ∀ s v d w r, kernWit k s v d w → NMem d r → g0.re ≤ r ∧ r < g'.re := fun s v d w r hq hr => by
    obtain ⟨rfl, rfl⟩ := hq
    simp only [NMem] at hr; subst hr; exact ⟨hk0, by omega⟩
  have CF : CondFresh g0 g' := (PF.1.trans hcf').lower hk0
  refine ⟨⟨by omega, by omega, Re.2.2.1.trans dr2, fun o ho hn' => by rw [Re.2.2.2 o (by omega), hO o ho hn'],
    G2'.trans Rg, CF, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => Or.inr (Or.inr ?_)⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).2.1⟩, (R.labs e he).2.2⟩, R.nodup,
    dreg, fun s hs hf => ?_, R.ncond, R.econd,
    FS.toFront (by omega) (fun r hr => (hsl r hr).1) (fun e he r hr => (by simp [gsE, NMem] at hr)) dreg, ?_, ?_⟩, FS⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, by rw [Re.2.2.2 _ (by simp only [jmp0]; omega)]; exact hB0, rfl, rfl⟩
  · rcases R.regs r hr with h | h
    · simp only [GMem, ofSure, sure_mk, lazyReg, NMem] at h; subst h; exact Or.inr ⟨hk0, by omega⟩
    · exact Or.inr ⟨h.1, h.2⟩
  · rcases (R.eregs e he).2 r hr with ⟨h | h, h'⟩
    · simp only [GMem, ofSure, sure_mk, lazyReg, NMem] at h; subst h; exact ⟨hk0, h'⟩
    · exact ⟨h, h'⟩
  · obtain ⟨N1, N2⟩ := R.nec s hs hf
    have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg k : Sure S) (jmp0 g0.bo)) tm r →
        BadC (CGoal.next L.sure th) tm r := fun h => by
      rcases h with e | ⟨q, _, nq⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg _ q) nq
    exact ⟨fun gul n tm r hm => bad (N1 gul n tm r hm), fun gul tm => by
      obtain ⟨r, hm, hb⟩ := N2 gul tm; exact ⟨r, hm, bad hb⟩⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm (agR cf c ned σ O gul t s0 s ag) hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs (agR cf c ned σ O gul t s0 s ag)
      hned regs hh hn res hres
    exact ⟨r, hm, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r G⟩

/-! ## `[7 p q]` with the goal's registers below the middle state -/

/-- **`runOKGB_sevenL` with the goal's registers below `g1`** (the state
between `q`'s part and `p`'s), not below `g0`.  The text of
`runOKGB_sevenL`; only the hypothesis `hg` changes. -/
theorem runOKGB_sevenLW {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    {goal : CGoal S} {Qp : Wit} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGB (Map := Map) lib N (Img lib P fb) fc goal g0 g1 nx)
    (Rp : RunOKLB (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hg : ∀ r, GMem goal r → r < g1.re) :
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


end

section Go

variable {Map : Type → Type} [HoonMap Map] {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

/-- **`monoTry_go` keeping the registers above the tree too**: the text of
`monoTry_go` with the kept registers `x < g.re ∨ g'.re ≤ x`. -/
theorem monoTry_goW {fail : Nat} : ∀ (ned : Need) (r o : Nat) (g g' : Gen Map) (o' : Nat),
    monoTryLoop fail ned r o g = some (o', g') → g.drop = false →
    (∀ k, g.bo ≤ k → k < g'.bo → HoonMap.get c.blocks k = HoonMap.get g'.blocks k) →
    NDist ned → (∀ x, NMem ned x → x < g.re) → r < g.re → ¬ NMem ned r →
    ∀ (regs : Map (Option Noun)) (t : Trace) (v : Noun), SkaModel.read r regs = some v →
    ∃ regs', (∀ x, (x < g.re ∨ g'.re ≤ x) → ¬ NMem ned x → SkaModel.read x regs' = SkaModel.read x regs) ∧
      ((Fits ned v ∧ HoldsN ned regs' v ∧
          goJ lib O c gul st regs t (jmp0 o') = goJ lib O c gul st regs' t (jmp0 o)) ∨
       (¬ Fits ned v ∧ goJ lib O c gul st regs t (jmp0 o') = goJ lib O c gul st regs' t (jmp0 fail))) := by
  intro ned
  induction ned with
  | none =>
    intro r o g g' o' h _ _ _ _ _ _ regs t v _
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨regs, fun _ _ _ => rfl, Or.inl ⟨trivial, trivial, rfl⟩⟩
  | this rn =>
    intro r o g g' o' h hd hc _ _ _ hr regs t v hv
    simp only [monoTryLoop] at h
    split at h
    · exact absurd h (by simp [crashM])
    rw [emit_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : HoonMap.get c.blocks g.bo = some ⟨[], [Pole.mov r rn], Termin.hop (jmp0 o)⟩ := by
      rw [hc g.bo (Nat.le_refl _) (by simp only [emitted_bo]; omega), emitted_get_self _ _ hd]
    obtain ⟨regs', hm⟩ := move_of_read hv rn
    refine ⟨regs', fun x _ hx => ?_, Or.inl ⟨trivial, ?_, ?_⟩⟩
    · rw [read_move hm x, if_neg (show ¬ x = rn from hx)]
    · simp only [HoldsN]; rw [read_move hm rn, if_pos rfl]; exact hv
    · rw [goJ_jmp0 _ _ _ _ hb, execBlob_mov_cons hm, execBlob_hop]
  | pair hn tn ihh iht =>
    intro r o g g' o' h hd hc hdist hlt hrlt hr regs t v hv
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    obtain ⟨dh, dt, dht⟩ := hdist
    have hlh : ∀ x, NMem hn x → x < g.re := fun x hx => hlt x (Or.inl hx)
    have hlt' : ∀ x, NMem tn x → x < g.re := fun x hx => hlt x (Or.inr hx)
    have hd2 : g2.drop = false := by rw [d2, d1]; exact hd
    simp only [emitted_bo, emitted_re]
    have hcl : HoonMap.get c.blocks (g2.bo + 1) =
        some ⟨[], [], Termin.clq r (jmp0 g2.bo) (jmp0 fail)⟩ := by
      rw [hc (g2.bo + 1) (by omega) (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ (by simp only [emitted_drop, hd2])
    have hsp : HoonMap.get c.blocks g2.bo =
        some ⟨[], [Pole.hed r (g.re + 1), Pole.tal r g.re], Termin.hop (jmp0 oh)⟩ := by
      rw [hc g2.bo (by omega) (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ hd2
    have hcH : ∀ k, g1.bo ≤ k → k < g2.bo → HoonMap.get c.blocks k = HoonMap.get g2.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega)]
    have hcT : ∀ k, g.bo ≤ k → k < g1.bo → HoonMap.get c.blocks k = HoonMap.get g1.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega), k2 k h2]
    cases v with
    | atom a =>
      refine ⟨regs, fun _ _ _ => rfl, Or.inr ⟨fun h => h.elim, ?_⟩⟩
      rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
      rfl
    | cell vh vt =>
      have e1 : goJ lib O c gul st regs t (jmp0 (g2.bo + 1)) =
          goJ lib O c gul st (store g.re vt (store (g.re + 1) vh regs)) t (jmp0 oh) := by
        rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
        show goJ lib O c gul st regs t (jmp0 g2.bo) = _
        rw [goJ_jmp0 _ _ _ _ hsp, execBlob_hed_cons hv,
          execBlob_tal_cons (by rw [read_store_ne (by omega)]; exact hv), execBlob_hop]
      have hrh : SkaModel.read (g.re + 1) (store g.re vt (store (g.re + 1) vh regs)) = some vh := by
        rw [read_store_ne (by omega), read_store_eq]
      obtain ⟨regs3, f3, c3⟩ := ihh (g.re + 1) ot g1 g2 oh hh (by rw [d1]; exact hd) hcH dh
        (fun x hx => by have := hlh x hx; omega) (by omega)
        (fun hx => by have := hlh _ hx; omega) _ t vh hrh
      have keep3 : ∀ x, (x < g.re ∨ g2.re ≤ x) → ¬ NMem hn x → x ≠ g.re + 1 →
          SkaModel.read x regs3 = SkaModel.read x regs := fun x hx hn' _ => by
        rw [f3 x (hx.elim (fun h => Or.inl (by omega)) Or.inr) hn', read_store_ne (by rcases hx with h | h <;> omega),
          read_store_ne (by rcases hx with h | h <;> omega)]
      rcases c3 with ⟨fh, hh3, gh⟩ | ⟨nfh, gh⟩
      · have hrt : SkaModel.read g.re regs3 = some vt := by
          rw [f3 g.re (Or.inl (by omega)) (fun hx => by have := hlh _ hx; omega), read_store_eq]
        obtain ⟨regs4, f4, c4⟩ := iht g.re o _ g1 ot ht (by simp only; exact hd) hcT dt
          (fun x hx => by have := hlt' x hx; simp only; omega) (by simp only; omega)
          (fun hx => by have := hlt' _ hx; omega) regs3 t vt hrt
        have fr : ∀ x, (x < g.re ∨ g2.re ≤ x) → ¬ NMem (Need.pair hn tn) x →
            SkaModel.read x regs4 = SkaModel.read x regs :=
          fun x hx hnm => by
            simp only [NMem, not_or] at hnm
            rw [f4 x (by rcases hx with h | h <;> simp only <;> omega) hnm.2,
              keep3 x hx hnm.1 (by rcases hx with h | h <;> omega)]
        rcases c4 with ⟨ft, ht4, gt⟩ | ⟨nft, gt⟩
        · refine ⟨regs4, fr, Or.inl ⟨⟨fh, ft⟩, ⟨holdsN_frame hn hh3 (fun x hx => f4 x (Or.inl (by have := hlh x hx; simp only; omega))
            (dht x hx)), ht4⟩, ?_⟩⟩
          rw [e1, gh, gt]
        · exact ⟨regs4, fr, Or.inr ⟨fun hf => nft hf.2, by rw [e1, gh, gt]⟩⟩
      · refine ⟨regs3, fun x hx hnm => ?_, Or.inr ⟨fun hf => nfh hf.1, by rw [e1, gh]⟩⟩
        simp only [NMem, not_or] at hnm
        exact keep3 x hx hnm.1 (by rcases hx with h | h <;> omega)
  | both rn hn tn ihh iht =>
    intro r o g g' o' h hd hc hdist hlt hrlt hr regs t v hv
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    split at h
    · exact absurd h (by simp [crashM])
    rename_i hrn
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    obtain ⟨dh, dt, dht, dhr, dtr⟩ := hdist
    have hlh : ∀ x, NMem hn x → x < g.re := fun x hx => hlt x (Or.inr (Or.inl hx))
    have hlt' : ∀ x, NMem tn x → x < g.re := fun x hx => hlt x (Or.inr (Or.inr hx))
    have hrnl : rn < g.re := hlt rn (Or.inl rfl)
    have hd2 : g2.drop = false := by rw [d2, d1]; exact hd
    simp only [emitted_bo, emitted_re]
    have hcl : HoonMap.get c.blocks (g2.bo + 1) =
        some ⟨[], [], Termin.clq r (jmp0 g2.bo) (jmp0 fail)⟩ := by
      rw [hc (g2.bo + 1) (by omega) (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ (by simp only [emitted_drop, hd2])
    have hsp : HoonMap.get c.blocks g2.bo =
        some ⟨[], [Pole.hed r (g.re + 1), Pole.tal r g.re, Pole.mov r rn], Termin.hop (jmp0 oh)⟩ := by
      rw [hc g2.bo (by omega) (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ hd2
    have hcH : ∀ k, g1.bo ≤ k → k < g2.bo → HoonMap.get c.blocks k = HoonMap.get g2.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega)]
    have hcT : ∀ k, g.bo ≤ k → k < g1.bo → HoonMap.get c.blocks k = HoonMap.get g1.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega), k2 k h2]
    cases v with
    | atom a =>
      refine ⟨regs, fun _ _ _ => rfl, Or.inr ⟨fun h => h.elim, ?_⟩⟩
      rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
      rfl
    | cell vh vt =>
      have hr2 : SkaModel.read r (store g.re vt (store (g.re + 1) vh regs)) = some (C vh vt) := by
        rw [read_store_ne (by omega), read_store_ne (by omega)]; exact hv
      obtain ⟨regsM, hm⟩ := move_of_read hr2 rn
      have e1 : goJ lib O c gul st regs t (jmp0 (g2.bo + 1)) =
          goJ lib O c gul st regsM t (jmp0 oh) := by
        rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
        show goJ lib O c gul st regs t (jmp0 g2.bo) = _
        rw [goJ_jmp0 _ _ _ _ hsp, execBlob_hed_cons hv,
          execBlob_tal_cons (by rw [read_store_ne (by omega)]; exact hv), execBlob_mov_cons hm, execBlob_hop]
      have hrh : SkaModel.read (g.re + 1) regsM = some vh := by
        rw [read_move hm, if_neg (by omega), read_store_ne (by omega), read_store_eq]
      obtain ⟨regs3, f3, c3⟩ := ihh (g.re + 1) ot g1 g2 oh hh (by rw [d1]; exact hd) hcH dh
        (fun x hx => by have := hlh x hx; omega) (by omega)
        (fun hx => by have := hlh _ hx; omega) _ t vh hrh
      have keep3 : ∀ x, (x < g.re ∨ g2.re ≤ x) → ¬ NMem hn x → x ≠ rn →
          SkaModel.read x regs3 = SkaModel.read x regs := fun x hx hn' hxr => by
        rw [f3 x (hx.elim (fun h => Or.inl (by omega)) Or.inr) hn', read_move hm, if_neg hxr,
          read_store_ne (by rcases hx with h | h <;> omega), read_store_ne (by rcases hx with h | h <;> omega)]
      rcases c3 with ⟨fh, hh3, gh⟩ | ⟨nfh, gh⟩
      · have hrt : SkaModel.read g.re regs3 = some vt := by
          rw [f3 g.re (Or.inl (by omega)) (fun hx => by have := hlh _ hx; omega), read_move hm, if_neg (by omega),
            read_store_eq]
        obtain ⟨regs4, f4, c4⟩ := iht g.re o _ g1 ot ht (by simp only; exact hd) hcT dt
          (fun x hx => by have := hlt' x hx; simp only; omega) (by simp only; omega)
          (fun hx => by have := hlt' _ hx; omega) regs3 t vt hrt
        have fr : ∀ x, (x < g.re ∨ g2.re ≤ x) → ¬ NMem (Need.both rn hn tn) x →
            SkaModel.read x regs4 = SkaModel.read x regs :=
          fun x hx hnm => by
            simp only [NMem, not_or] at hnm
            rw [f4 x (by rcases hx with h | h <;> simp only <;> omega) hnm.2.2, keep3 x hx hnm.2.1 hnm.1]
        rcases c4 with ⟨ft, ht4, gt⟩ | ⟨nft, gt⟩
        · have hrn4 : SkaModel.read rn regs4 = some (C vh vt) := by
            rw [f4 rn (Or.inl (by simp only; omega)) dtr, f3 rn (Or.inl (by omega)) dhr, read_move hm, if_pos rfl]
            exact hr2
          refine ⟨regs4, fr, Or.inl ⟨⟨fh, ft⟩, ⟨hrn4, holdsN_frame hn hh3 (fun x hx => f4 x (Or.inl (by have := hlh x hx; simp only; omega))
            (dht x hx)), ht4⟩, ?_⟩⟩
          rw [e1, gh, gt]
        · exact ⟨regs4, fr, Or.inr ⟨fun hf => nft hf.2, by rw [e1, gh, gt]⟩⟩
      · refine ⟨regs3, fun x hx hnm => ?_, Or.inr ⟨fun hf => nfh hf.1, by rw [e1, gh]⟩⟩
        simp only [NMem, not_or] at hnm
        exact keep3 x hx hnm.2.1 hnm.1

end Go

end Comp
end SkaModel
end Formalization
