import lemmas.Ska.CompHintFrame

/-!
# Spots around calls and in sequence (README Gaps 24.16)

* `copyL_noBond`: `+copy` of two lazies with no fork and no bond has none.
* `noBondH_n2_none`: **`NoBondH` of the indirect call** `[2 p q]`, the
  subject `p` not hinted (else `+past` parks the formula's need in a bond).
* `runOKGBT_sevenL`: the text of `runOKGB_sevenL` (`CompLBDone.lean`) for
  `RunOKGBT` (`q`'s run handed the agreement at every trace; `p`'s
  `RunOKLB` at the entry trace).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `+copy` of two lazies with no fork and no bond has no fork and no bond. -/
theorem copyL_noBond {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (hf : first.laz.fork = []) (hb : first.laz.bond = []) (hf2 : second.fork = []) (hb2 : second.bond = [])
    (h : copyL first second g = some (nex, g')) : nex.laz.fork = [] ∧ nex.laz.bond = [] := by
  unfold copyL at h
  obtain ⟨oc, ge, he, h⟩ := bind_some h
  obtain ⟨laz, gf, hc, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rcases first with ⟨⟨s1, f1, b1⟩, th1⟩
  simp only [fork_mk, bond_mk] at hf hb
  subst hf hb
  simp only [copyLazyL, hf2, hb2, List.isEmpty_nil, if_true] at hc
  obtain ⟨⟨ned, ops⟩, g2, -, hc⟩ := bind_some hc
  obtain ⟨u, g3, -, hc⟩ := bind_some hc
  simp only [pure_apply, Option.bind_some, bind_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨rfl, rfl⟩

/-! ## `[7 p q]` for `RunOKGBT` -/

/-- **`[7 p q]` with the agreement at every trace** (the text of
`runOKGB_sevenL` for `RunOKGBT`): `p` reads no goal register (`x = false`). -/
theorem runOKGBT_sevenL {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC7 lib P f fb fc)
    {goal : CGoal S} {Qp : Wit} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKGBT (Map := Map) lib N (Img lib P fb) fc goal g0 g1 nx)
    (Rp : RunOKLB (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hg : ∀ r, GMem goal r → r < g0.re) :
    RunOKGBT lib N P f goal g0 g2 nex := by
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
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g2 nex.laz s0 s) → (∀ x, NMem ned x → g2.re ≤ x) →
      ∀ regs, HoldsN ned regs s0 →
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g1 g2 nex.laz s0 s) ∧
      ∀ (u : Noun) (st' : σ) (R1 : Map (Option Noun)) (dp : Need) (wp : Noun), Qp s u dp wp → Inv st' →
        ν st ≤ ν st' → FitsS nx.laz.sure u → HoldsN nx.laz.sure.ned R1 u → HoldsN dp R1 wp →
        (∀ x, ((x < g1.re ∨ NMem ned x) ∧ ¬ NMem nx.laz.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs) →
        (∀ (st'' : σ) (t'' : Trace), AgreeUB lib O c gul st'' t'' cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u) ∧
        (∀ x, NMem (Need.pair ned dp) x → g1.re ≤ x) ∧ HoldsS nx.laz.sure R1 u ∧
        HoldsN (Need.pair ned dp) R1 (C s0 wp) ∧
        ∀ r, GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem (Need.pair ned dp) x) ∧ ¬ GMem goal x)
            st' R1 t tm nx.th goal r →
          goJ lib O c gul st regs t nex.th = goJ lib O c gul st' R1 t nx.th →
          GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm
            nex.th goal r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s ag hned regs hn
    refine ⟨fun st' => ⟨fun o l u hnl => (ag st' t).1 o (by omega) u hnl, fun e he _ => (ag st' t).2 e he⟩,
      fun u st' R1 dp wp hqp hI' hν fit h1 hD1 k1 => ?_⟩
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree ned (fun x hx => k1 x ⟨Or.inr hx, fun hm => by
      have := nxL x hm; have := hned x hx; omega⟩) hn
    refine ⟨fun st'' t'' => ⟨fun o l u' hnl => ?_, fun e he => ?_⟩,
      fun r hr => hr.elim (fun h => by have := hned r h; omega) (fun h => (hdp s u dp wp r hqp h).1),
      ⟨h1, fit.2⟩, ⟨hn1, hD1⟩, fun r G e1 => ?_⟩
    · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
        rcases plab o hm with h | h
        · exact hnl h
        · omega
      rw [(ag st'' t'').1 o l (by omega) hn2, Rp.keep o u' hnl]
    · obtain ⟨hge, _, Bq, th', hb1⟩ := Rq.labs e he
      have hlt : e.1 < g1.bo := by have := (Rq.labs e he).2.1; omega
      obtain ⟨Fp, hFp, Sp'⟩ := Rp.front e he
      have hb2 := hFp Bq (Termin.hop th') hb1
      rcases Sp' cf hcf with ⟨L', hL', FP⟩ | ⟨hn2, FP⟩
      · obtain ⟨A0, B2, th'', hb3, hc3, hf3⟩ := (ag st'' t'').2 (e.1, L') hL'
        rw [hb2] at hb3
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
        obtain ⟨rfl, rfl⟩ := hb3
        refine ⟨A0 ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, by rw [hc3]; simp, ?_⟩
        exact ((FP lib σ O c gul st'' t'' ned A0 s0 s u dp wp hned hqp hf3).conv (N1 := Need.pair ned dp)
          (x1 := C s0 wp) (fun R hR => ⟨hR, trivial⟩) (fun z hz => Or.inl (Or.inl hz))).mono (Nat.le_refl _)
      · refine ⟨[] ++ Fp.map (renPole (unproxy cf)), Bq, th', hb1, ?_, ?_⟩
        · rw [(ag st'' t'').1 e.1 hge (by omega) hn2, hb2]
          simp [unproxyBlob, renBlob, renFin]
        · exact (FP lib σ O c gul st'' t'' ned [] s0 s u dp wp hned hqp fillSem_bunt_nil).conv
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

/-! ## `DoneOK` with the agreement at every trace -/

/-- **`DoneOK` with `RunOKGBT`**: what a run under `%done` gives a later
run under its result (`CompCallTreeTop.lean`), the run handed the
agreement at every trace. -/
structure DoneOKT (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  run : RunOKGBT lib N P f (CGoal.done : CGoal S) g0 g1 nex
  nent : nex.th.there ∉ (entries nex.laz).map Prod.fst
  flat : Flat nex.laz
  clean : Clean nex.laz.sure.ned
  eclean : ∀ e ∈ entries nex.laz, Clean e.2.sure.ned

theorem DoneOK.toT {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {g0 g1 : Gen Map} {nex : NextL S}
    (D : DoneOK lib N P f g0 g1 nex) : DoneOKT lib N P f g0 g1 nex :=
  ⟨D.run.toT, D.nent, D.flat, D.clean, D.eclean⟩

section Kept
variable {snd : Nomm → NeedOrd → Bool}

/-- **`n11dKept_done` with the shape of the result** (its text, the facts
`DoneOK` adds proved before the run's): the jump at the copy block, not
the bond's label; the one bond flat; the needs clean. -/
theorem n11dKept_doneOK {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fh fq : Noun} {h q : Nomm}
    (Hq : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fq q) (hcq : sixCount q ≤ 255)
    (hnq : NoBondH (S := S) (Map := Map) snd env q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = true) (body : Noun)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH env snd true sup (Nomm.n11d tag h q body) CGoalL.done region g0 = some (nex, g1)) :
    DoneOKT lib N P (n3 (A 11) (C (A tag) fh) fq) g0 g1 nex := by
  obtain ⟨nq, gc, nh, gh, h3, hta, h6, h7⟩ := runLCH_n11d_kept_done hs hsnd hr
  have e0 : ∀ r, entries (ofSure (lazyReg r : Sure S)) = [] := fun r => entries_ofSure _
  -- the state after `don`, `toke` and the epilogue
  have dA : (genA g0 tag body).drop = false := d0
  have reA : (genA g0 tag body).re = g0.re + 2 := rfl
  have boA : (genA g0 tag body).bo = g0.bo + 2 := rfl
  have bA : ∀ k, HoonMap.get (genA g0 tag body).blocks k =
      if k = g0.bo + 1 then some ⟨[], [Pole.hde tag (g0.re + 1) body], Termin.hop (jmp0 g0.bo)⟩
      else if k = g0.bo then some ⟨[], [], Termin.don g0.re⟩ else HoonMap.get g0.blocks k := by
    intro k; simp only [genA, Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have ua : UpBelow ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩ : Gen Map) := G1.up hu
  have G2 : GrowU ({ ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) with re := g0.re + 2 } : Gen Map)
      (genA g0 tag body) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, Gen.emitted]; omega) ua
  have GA : GrowU g0 (genA g0 tag body) := (growU_re g0 _).trans (G1.trans ((growU_re _ _).trans G2))
  have uA : UpBelow (genA g0 tag body) := GA.up hu
  have clA : Clear (genA g0 tag body) := hcl.growU GA
  have cbA : CondBelow (genA g0 tag body) := fun k hk => by
    have := hcb k hk; simp only [genA, Gen.emitted] at this ⊢; omega
  have extA : Ext g0 (genA g0 tag body) := ⟨by rw [reA]; omega, by rw [boA]; omega, dA.trans d0.symm, fun o ho => by
    rw [bA, if_neg (by omega), if_neg (by omega)]⟩
  have ctoke : HoonMap.get g0.cond (g0.re + 1) = Option.none := condBelow_none hcb (by omega)
  -- the formula, its bond
  obtain ⟨⟨Q, RS⟩, -, -, hfl, -⟩ := Hq.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 (g0.bo + 1))
    (region := region) (Or.inr (e0 _)) hcq (by rw [boA]; omega) dA uA clA cbA
    (by simp only [jmp0]; omega) (by simp only [jmp0]; rw [boA]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by rw [reA]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h3
  have hb0 := (hnq h3).2
  have hq : nq.laz = ofSure nq.laz.sure := lazy_eq_ofSure hfl.1 hb0
  have dc : gc.drop = false := RS.drop.trans dA
  have uc : UpBelow gc := RS.grow.up uA
  have RP := RS.past (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr; rw [reA]; omega)
    (fun e he => by rw [e0] at he; cases he) rfl dc uc region
  have eL : (mk Sure.bunt [] ((gc.bo, mk nq.laz.sure nq.laz.fork []) :: nq.laz.bond) : Lazy S) =
      mk Sure.bunt [] [(gc.bo, nq.laz)] := by
    rw [hb0, hfl.1, ← hfl.1, ← hb0, Lazy.eta]
  rw [eL] at RP
  have RG := RP.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; rw [reA]; omega)
  have boD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).bo = gc.bo + 1 := by
    simp only [tagged_bo, Gen.emitted]
  have dD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).drop = false := by
    simp only [tagged_drop, Gen.emitted]; exact dc
  have rcA : g0.re + 2 ≤ gc.re := by have := RG.ext.1; simp only [reA, tagged_re, Gen.emitted] at this; exact this
  have bcA : g0.bo + 2 ≤ gc.bo := by have := RS.bo; rw [boA] at this; exact this
  -- the prologue
  have GE : GrowU ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
      (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, boD]; omega) (RG.grow.up uA)
  have uE := GE.up (RG.grow.up uA)
  have clE := (clA.growU RG.grow).growU GE
  have cbE : CondBelow (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) := RG.cfr.below cbA
  have ctD : HoonMap.get ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).cond (g0.re + 1) = Option.none := by
    rw [RG.cfr.get_lt (by rw [reA]; omega)]; exact ctoke
  -- the clue
  obtain ⟨⟨Qh, RSh⟩, -, -, hflh, -⟩ := Hh.run (sup := sup) (L := ofSure (lazyReg (g0.re + 1))) (th := jmp0 (gc.bo + 1))
    (region := region) (Or.inr (e0 _)) hch (by simp only [Gen.emitted, boD]; omega) (by simp only [emitted_drop]; exact dD)
    uE clE cbE (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted, tagged_bo]; omega) rfl
    (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted, tagged_re]; omega, ctD⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h6
  have RGh := RSh.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted, tagged_re]; omega)
  obtain ⟨hfh, hbh⟩ := hnh h6
  have dh : gh.drop = false := RSh.drop.trans (by simp only [emitted_drop]; exact dD)
  obtain ⟨rfl, r1, b1, d1, c1, k1⟩ := copyL_bond1 dh hfh hbh h7
  -- the copy block, the facts of the states
  have hb1 : ∀ k, HoonMap.get g1.blocks k =
      if k = gh.bo then some ⟨[], [], Termin.hop nh.th⟩ else HoonMap.get gh.blocks k := by
    intro k; rw [k1 k]; simp [Gen.emitted, dh, HoonMap.get_put]
  have hargs : nh.th.args = [] := nextArgs_nil RGh.ent rfl
  have boh : gc.bo + 2 ≤ gh.bo := by have := RGh.ext.2.1; simp only [Gen.emitted, tagged_bo] at this; omega
  have reh : gc.re ≤ gh.re := by have := RGh.ext.1; simp only [Gen.emitted, tagged_re] at this; omega
  have E1 : Ext gh g1 := ⟨by omega, by omega, by rw [d1, dh], fun o ho => by rw [hb1, if_neg (by omega)]⟩
  have EE1 : Ext (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
      ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) g1 := RGh.ext.trans E1
  have ED1 : Ext ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 := (ext_emit _ _).trans EE1
  have EA1 : Ext (genA g0 tag body) g1 := RG.ext.trans ED1
  have CF1 : CondFresh ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 :=
    (condFresh_of_eq (Nat.le_refl _) rfl).trans (RGh.cfr.trans (condFresh_of_eq (by omega) c1))
  have CFA1 : CondFresh (genA g0 tag body) g1 := RG.cfr.trans CF1
  have GG : Grow gh g1 := Grow.congr_right (grow_emit (g := gh) (b := ⟨[], [], Termin.hop nh.th⟩) (fun j hj => by
    simp [finJumps] at hj; subst hj; exact ⟨RGh.lo, RGh.hi⟩)) b1 (by rw [d1, emitted_drop, dh]) k1
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = [(gc.bo, nq.laz)] := by
    rw [hq]; simp [entries, bondEntries, forkEntries, ofSure]
  have hent' : entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) = [(gc.bo, nq.laz)] := by
    rw [hq]; simp [entries, bondEntries, forkEntries, ofSure]
  have hentN : entries nh.laz = [] := by rw [entries_flat hflh, hbh]
  have hmem : ∀ e, e ∈ entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) → e ∈ entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) := fun e he => by
    rw [hent]; rw [hent'] at he; exact he
  -- the blocks in the program
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      HoonMap.get c.blocks gh.bo = some ⟨[], [], Termin.hop nh.th⟩ ∧
      FrameOK c tag (g0.re + 1) body (gc.bo + 1) gc.bo (g0.bo + 1) (jmp0 g0.bo) ∧
      HoonMap.get c.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    intro cf hcf c ned σ O gul st t s0 s ag
    have hnot : ∀ o, o ≠ gc.bo → o ∉ (entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ []
        [(gc.bo, nq.laz)] : Lazy S)).map Prod.fst := fun o ho => by rw [hent']; simpa using ho
    have ct : HoonMap.get cf (g0.re + 1) = Option.none := by
      rw [hcf _ (by omega), CFA1.get_lt (by rw [reA]; omega)]; exact ctoke
    have cr : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by omega), CFA1.get_lt (by rw [reA]; omega)]; exact condBelow_none hcb (Nat.le_refl _)
    have bE : HoonMap.get g1.blocks (gc.bo + 1) =
        some ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩ := by
      rw [EE1.2.2.2 _ (by simp only [Gen.emitted, tagged_bo]; omega), ← boD]; exact hk_emitted_self dD _
    refine ⟨?_, ⟨hst, ?_, ?_⟩, ?_⟩
    · rw [ag.1 gh.bo (by omega) (by omega) (hnot _ (by omega)), hb1, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp_nil _ hargs]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega)), bE]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp, jmp0, unproxy_none ct]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega)), EA1.2.2.2 _ (by rw [boA]; omega), bA, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp, jmp0, unproxy_none ct]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega)), EA1.2.2.2 _ (by rw [boA]; omega), bA, if_neg (by omega),
        if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, unproxy_none cr]
  have agh : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag (g0.re + 1) body], Termin.hop (jmp0 gc.bo)⟩) gh nh.laz s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      simp only [Gen.emitted, tagged_bo] at h0
      rw [ag.1 o (by omega) (by omega) (by rw [hent']; simp; omega), hb1, if_neg (by omega)],
     fun e he => by rw [hentN] at he; cases he⟩
  have agq : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (genA g0 tag body) ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
        (mk Sure.bunt [] [(gc.bo, nq.laz)]) s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      rw [ag.1 o (by rw [boA] at h0; omega) (by have := ED1.2.1; omega) (by rw [hent']; rw [hent] at hn; exact hn),
        ED1.2.2.2 o h1],
     fun e he => by
      obtain ⟨A, B, th', a1, a2, a3⟩ := ag.2 e (by rw [hent']; rw [hent] at he; exact he)
      have l2 := (RG.labs e he).2.1
      exact ⟨A, B, th', by rw [← ED1.2.2.2 e.1 l2]; exact a1, a2, a3.mono (by have := ED1.1; omega)⟩⟩
  refine ⟨?_, by rw [hent']; simp only [jmp0, List.map_cons, List.map_nil, List.mem_singleton]; omega,
    ⟨by simp only [fork_mk], fun e he => by simp only [bond_mk, List.mem_singleton] at he; subst he; exact hq⟩,
    by have hc := Hh.clean (L := ofSure (lazyReg (g0.re + 1))) trivial h6; exact hc,
    fun e he => by
      rw [hent', List.mem_singleton] at he; subst he; exact Hq.clean (L := ofSure (lazyReg g0.re)) trivial h3⟩
  refine ⟨extA.trans EA1, GA.trans (RG.grow.trans (GE.trans (RGh.grow.trans (GG.toU (RGh.grow.up uE))))),
    (condFresh_of_eq (g0 := g0) (g1 := genA g0 tag body) (by rw [reA]; omega) rfl).trans CFA1,
    by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨_, by simp only [jmp0]; rw [hb1, if_pos rfl], rfl, rfl⟩,
    fun r hr => Or.inr ?_, RGh.dist, fun e he => ?_, fun e he => ?_, by rw [hent']; simp, fun s hs hf => ?_,
    fun r hr => by rw [c1]; exact RGh.ncond r hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases RGh.regs r hr with h | h
    · simp only [GMem, lazyReg, NMem] at h; subst h; constructor <;> omega
    · simp only [Gen.emitted, tagged_re] at h; constructor <;> omega
  · have he' := hmem e he
    refine ⟨(RG.eregs e he').1, fun r hr => ?_⟩
    have := (RG.eregs e he').2 r hr
    refine ⟨Or.inr ?_, ?_⟩
    · rcases this.1 with h | h
      · simp only [GMem, lazyReg, NMem] at h; omega
      · rw [reA] at h; omega
    · have := this.2; simp only [tagged_re, Gen.emitted] at this; omega
  · have he' := hmem e he
    obtain ⟨l1, l2, B, th', hB⟩ := RG.labs e he'
    exact ⟨by rw [boA] at l1; omega, by have := ED1.2.1; omega, B, th', by rw [ED1.2.2.2 e.1 l2]; exact hB⟩
  · have hf' : ¬ FitsS nh.laz.sure s := fun hf2 => hf ⟨hf2.1, (looks_uni _ _ _).mpr ⟨hf2.2, looks_empty _⟩⟩
    have NC := RGh.nec s hs hf'
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · cases n with
      | zero => rw [minkF_zero_fuel] at hm; cases hm
      | succ m =>
        rw [minkF_n11d_stop lib gul m tm s hst] at hm
        cases hmh : minkF lib gul m tm s fh with
        | none => rw [hmh] at hm; cases hm
        | some rh =>
          have := badC_lazyReg (NC.1 gul m tm rh hmh); subst this
          rw [hmh] at hm; simp only [tbind] at hm; cases hm
          exact Or.inl rfl
    · obtain ⟨rh, hm, hb⟩ := NC.2 gul tm
      have := badC_lazyReg hb; subst this
      exact ⟨_, mink_n11d_clue hst hm (fun q => by simp), Or.inl rfl⟩
  · have he' := hmem e he
    rw [CF1.get_lt ((RG.eregs e he').2 r hr).2]; exact RG.econd e he' r hr
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hcp, F, hdn⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th := fun st regs => by
      rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop]
    cases n with
    | zero => rw [minkF_zero_fuel] at hm; cases hm
    | succ m =>
      rw [minkF_n11d_stop lib gul m tm s hst] at hm
      cases hmh : minkF lib gul m tm s fh with
      | none => rw [hmh] at hm; cases hm
      | some rh =>
        rw [hmh] at hm
        have Gh := RGh.sem cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O m gul hN hS (oracleFwd_le hF (Nat.le_succ m)) st t tm s0 s rh
          hI htr hs hmh (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
          ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn
        cases rh with
        | zero v =>
          simp only [tbind] at hm
          obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_lazyReg _ v)
          have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
            simp only [GMem, lazyReg, NMem] at hg; have := hned x hx; omega⟩)
          have Gq := RG.sem cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν O m gul hN hS
            (oracleFwd_le hF (Nat.le_succ m)) st1 ((tag, v) :: t) ((tag, v) :: tm) s0 s r hI1
            (Forall2.cons (FrameRel.same hst) (frames_mono hle1 htr)) hs hm (fun st' => agq (ag st' ((tag, v) :: t)))
            (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := returnsC_done hdn (frameOK_goes F (fitsS_lazyReg g0.re) hh1 Gq)
          exact ⟨ton, st2, hI2, Needs.le_trans hle1 hle2, by rw [ecopy, e1]; exact e2, hrel⟩
        | one b =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
        | two tr =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hcp, F, hdn⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th := fun st regs => by
      rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop]
    rw [ecopy] at hres
    obtain ⟨rh, hmh, Gh⟩ := RGh.semB cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O gul hN hS hB
      st t tm s0 s hI htr hs (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn res hres
    cases rh with
    | zero v =>
      obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_lazyReg _ v)
      have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
        simp only [GMem, lazyReg, NMem] at hg; have := hned x hx; omega⟩)
      rw [e1, goJ_push hst F.2.1 st1 regs1 hh1 t] at hres
      obtain ⟨r, hmq, Gq⟩ := RG.semB cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν O gul
        hN hS hB st1 ((tag, v) :: t) ((tag, v) :: tm) s0 s hI1
        (Forall2.cons (FrameRel.same hst) (frames_mono hle1 htr)) hs (fun st' => agq (ag st' ((tag, v) :: t)))
        (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
        res hres
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := returnsC_done hdn (frameOK_goes F (fitsS_lazyReg g0.re) hh1 Gq)
      exact ⟨r, mink_n11d_stop hst hmh hmq, ton, st2, hI2, Needs.le_trans hle1 hle2, by rw [ecopy, e1]; exact e2, hrel⟩
    | one b =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | two tr =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩

end Kept

/-! ## Sequences at the top: `[7 p q]`, `q` with `DoneOKT` -/

section Seq
variable {snd : Nomm → NeedOrd → Bool}

/-- What every run of `nm` under `%done` from a clean state gives. -/
def DoneAllT (lib : Lib) (N : Needs) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLCH env snd true sup nm CGoalL.done region g0 = some (nex, g1) → DoneOKT (S := S) lib N P f g0 g1 nex

/-- Every member of `CallTreeHU` (`callTreeHU_done`). -/
theorem doneAllT_callTreeHU (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun}
    {nm : Nomm} (h : CallTreeHU lib env N P x f nm) : DoneAllT (S := S) (Map := Map) lib N env snd P f nm :=
  fun b0 d0 hu hcl hcb hr => (callTreeHU_done (S := S) (Map := Map) (snd := snd) lib env h b0 d0 hu hcl hcb hr).toT

/-- **A kept dynamic `stopTag` hint** (`n11dKept_doneOK`). -/
theorem doneAllT_n11dKept {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fh fq : Noun} {h q : Nomm}
    (Hq : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fq q) (hcq : sixCount q ≤ 255)
    (hnq : NoBondH (S := S) (Map := Map) snd env q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = true) (body : Noun) :
    DoneAllT (S := S) (Map := Map) lib N env snd P (n3 (A 11) (C (A tag) fh) fq) (Nomm.n11d tag h q body) :=
  fun b0 d0 hu hcl hcb hr => n11dKept_doneOK Hq hcq hnq hsnd Hh hch hnh hs hst body b0 d0 hu hcl hcb hr

/-- **`[7 p q]` under `%done`, `q` with `DoneAllT`** (the `%7` case of
`callTreeHU_done`, `runOKGBT_sevenL`): `p` a member of `CallTreeHU`,
`q` anything whose run under `%done` gives `DoneOKT` (a kept spot,
another sequence). -/
theorem doneAllT_seven (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {b c : Noun} {p q : Nomm}
    (hp : CallTreeHU lib env N P true b p) (Hq : DoneAllT (S := S) (Map := Map) lib N env snd (Img lib P b) c q) :
    DoneAllT (S := S) (Map := Map) lib N env snd P (n3 (A 7) b c) (Nomm.n7 p q) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb h1
  have Rq := D.run
  have Lp := ((lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib (N := N) env hp).2 rfl).1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
    (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · exact e.elim
      · exact e.2, Rq.ncond x hx⟩)
    (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
    D.flat D.clean D.eclean h2
  exact ⟨runOKGBT_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
    Lp.clean (L := nx.laz) D.clean h2, hec⟩

/-- **The contract at the top of anything with `DoneAllT`**, traces included. -/
theorem finishLUCH_contractDoneAllT (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : DoneAllT (S := S) (Map := Map) lib N env snd P f nm) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractGBT lib N (fun hr => (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

end Seq

section NoBond
variable {snd : Nomm → NeedOrd → Bool} {env : CallEnv}

/-- **`NoBondH` of the indirect call**: the parts with `NoBondH`, the
subject not hinted (`+past` of the formula's need over it is the need). -/
theorem noBondH_n2_none {p q : Nomm} (hp : NoBondH (S := S) (Map := Map) snd env p)
    (hq : NoBondH (S := S) (Map := Map) snd env q) (hh : hinted env.cod p ≠ some true) :
    NoBondH (S := S) (Map := Map) snd env (Nomm.n2 p q Option.none) := by
  intro sup sur th region g0 g1 nex hr
  obtain ⟨nex0, ga, out, pro, gb, o, gc, nexF, gd, nexF', ge, nexS, gf, -, -, -, hF, hP, hS, hC⟩ :=
    runLCH_n2_none hr
  obtain ⟨fF, bF⟩ := hq hF
  have eP : nexF' = nexF := by
    unfold pastL at hP
    split at hP
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hP
      exact hP.1.symm
    · cases eh : hinted env.cod p with
      | none => simp [eh] at hP
      | some b =>
        cases b with
        | true => exact absurd eh hh
        | false =>
          simp only [eh, pure_apply, Option.some.injEq, Prod.mk.injEq] at hP
          exact hP.1.symm
  subst eP
  obtain ⟨fS, bS⟩ := hp hS
  exact copyL_noBond fS bS fF bF hC

end NoBond

end Comp
end SkaModel
end Formalization
