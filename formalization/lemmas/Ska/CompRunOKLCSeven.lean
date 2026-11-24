import lemmas.Ska.CompRunOKLC

/-!
# `[7 p q]` for runs that may call: `runOKLC_seven`

README Gaps 12.20.  `runOKL_seven` (`CompLazyGoal.lean`) composes the
call-free relation `RunOKL`; `runOKLC_seven` composes `RunOKLC`: `q` under
the goal `%next L th`, `p` under the goal that `q`'s run returns (which may
have entries: forks of a `%6`, the bonds of `+past` behind a call in `q`),
either part may call.  At run time `p`'s code runs (`GoalSemCMD`: it may
move the oracle's state, and leaves its witness `dp` holding `wp` at `q`'s
code), then `q`'s code with the input need `pair ned dp`, which keeps `dp`
for the lazy blocks that `p` put ops at.  The witness relation of the whole
is `sevenWit`: `p`'s at `s` and `u`, `q`'s at `u` and `v`, for some product
`u` of `p`.  The formula is `[7 b c]` with `q`'s subjects `Img lib P b` (the
products of `b`), as `Annot.n7` gives.

* `minkF_sevenC`, `mink_sevenC_bwd`: `+mink` on `[7 b c]` for any `b`, `c`.
* `sevenWit`, `frontLC_seven`, `frontLC_seven_bunt`, `goalSemCMD_pair`.
* `runOKLC_seven`: both `sem` clauses through one `core`.
* `runOKL_seven` is the call-free case (`RunOKL.toLC` of both parts gives
  `runOKLC_seven`'s hypotheses).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+mink` on `[7 b c]` -/

/-- **`+mink` on `[7 b c]`**: `b` runs with one less fuel; its tone is the
whole's unless it is a product `u`, on which `c` runs with that fuel. -/
theorem minkF_sevenC {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s fb fc : Noun} {r : Tone}
    (h : minkF lib gul n tm s (n3 (A 7) fb fc) = some r) :
    ∃ n', n' < n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧
      (((∀ q, rb ≠ Tone.zero q) ∧ r = rb) ∨ ∃ u, rb = Tone.zero u ∧ minkF lib gul n' tm u fc = some r) := by
  cases n with
  | zero => simp [minkF] at h
  | succ n' =>
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    refine ⟨n', Nat.lt_succ_self n', ?_⟩
    cases eb : minkF lib gul n' tm s fb with
    | none => rw [eb] at h; simp [tbind] at h
    | some rb =>
      rw [eb] at h
      refine ⟨rb, rfl, ?_⟩
      cases rb with
      | zero u => exact Or.inr ⟨u, rfl, h⟩
      | one q =>
        simp only [tbind, Option.some.injEq] at h
        exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
      | two t' =>
        simp only [tbind, Option.some.injEq] at h
        exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩

/-- **`+mink` on `[7 b c]`, backward**: a tone of `b` that is no product is
the whole's, and a product `u` of `b` and a tone of `c` on `u` give the
whole's. -/
theorem mink_sevenC_bwd {lib : Lib} {gul : Noun} {tm : Trace} {s fb fc : Noun} {rb : Tone}
    (hb : Mink lib gul tm s fb rb) :
    ((∀ q, rb ≠ Tone.zero q) → Mink lib gul tm s (n3 (A 7) fb fc) rb) ∧
    (∀ u r, rb = Tone.zero u → Mink lib gul tm u fc r → Mink lib gul tm s (n3 (A 7) fb fc) r) := by
  obtain ⟨n1, e1⟩ := hb
  refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun u r eu hc => ?_⟩
  · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1]
    cases rb with
    | zero q => exact absurd rfl (hn q)
    | one _ => rfl
    | two _ => rfl
  · subst eu
    obtain ⟨n2, e2⟩ := hc
    have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s fb _ e1
    have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm u fc _ e2
    exact ⟨max n1 n2 + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']⟩

/-- A product of `+mink` is one with the empty trace. -/
theorem mink_nil_of_mink_zero {lib : Lib} {gul : Noun} {tm : Trace} {s f u : Noun}
    (h : Mink lib gul tm s f (Tone.zero u)) : Mink lib gul [] s f (Tone.zero u) := by
  obtain ⟨n, e⟩ := h
  exact ⟨n, mink_nil_of_zero e⟩

/-! ## The witness and the fronts -/

/-- **The witness relation of `[7 p q]`**: `p`'s at the subject and a
product `u` of `p`, `q`'s at `u` and the product. -/
def sevenWit (Qp Qq : Wit) : Wit :=
  fun s v d w => ∃ u dp wp dq wq, Qp s u dp wp ∧ Qq u v dq wq ∧ d = Need.pair dp dq ∧ w = C wp wq

/-- **The fronts compose**: `p`'s ops in front of `q`'s at an entry that `q`
kept for `p`. -/
theorem frontLC_seven {Qp Qq : Wit} {lo0 lo1 lo2 : Nat} {Lp Lq M : Sure S} {Fp Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r) (h12 : lo1 ≤ lo2)
    (FP : FrontLC (Map := Map) Qp lo1 lo2 Lp Fp Lq) (FQ : FrontLC (Map := Map) Qq lo0 lo1 Lq Fq M) :
    FrontLC (Map := Map) (sevenWit Qp Qq) lo0 lo2 Lp (Fp ++ Fq) M := by
  intro lib σ O c gul st t ned A0 s0 s v d w hned hq hfill
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have h1 := FP lib σ O c gul st t ned A0 s0 s u dp wp hned hp hfill
  have h2 := FQ lib σ O c gul st t (Need.pair ned dp) (A0 ++ Fp) (C s0 wp) u v dq wq
    (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => hdp s u dp wp r hp h)) hqq h1
  rw [← List.append_assoc]
  exact h2.assoc

/-- **A front of `q` at an entry that `p` does not see.** -/
theorem frontLC_seven_bunt {Qp Qq : Wit} {lo0 lo1 lo2 : Nat} {M : Sure S} {Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r ∧ r < lo2) (h12 : lo1 ≤ lo2)
    (FQ : FrontLC (Map := Map) Qq lo0 lo1 Sure.bunt Fq M) :
    FrontLC (Map := Map) (sevenWit Qp Qq) lo0 lo2 Sure.bunt Fq M := by
  intro lib σ O c gul st t ned A0 s0 s v d w hned hq hfill
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have h1 : FillSem lib O c gul st t (Need.pair ned dp) lo1 (Sure.bunt : Sure S) A0 (C s0 wp) u :=
    ((hfill.pair dp (fun r hr => (hdp s u dp wp r hp hr).2) wp).mono h12).bunt_subj
  have h2 := FQ lib σ O c gul st t (Need.pair ned dp) A0 (C s0 wp) u v dq wq
    (fun r hr => hr.elim (fun h => Nat.le_trans h12 (hned r h)) (fun h => (hdp s u dp wp r hp h).1)) hqq h1
  exact h2.assoc

/-- **A witness kept from before**: registers `dp` holding `wp` that the code
keeps join every witness it gives at its jump. -/
theorem goalSemCMD_pair {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace}
    {je : Jmp} {sur : Sure S} {th : Jmp} {Q Q' : Noun → Need → Noun → Prop} {dp : Need} {wp : Noun}
    (hk : ∀ x, NMem dp x → K x) (hd : HoldsN dp regs wp) (hQ : ∀ p d w, Q p d w → Q' p (Need.pair dp d) (C wp w)) :
    ∀ {r : Tone}, GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q' r
  | Tone.zero _, H => ⟨fun hf => by
      obtain ⟨st'', R, d, w, hI, hle, hq, h1, h2, h3, h4⟩ := H.1 hf
      exact ⟨st'', R, Need.pair dp d, C wp w, hI, hle, hQ _ _ _ hq, h1,
        ⟨HoldsN.agree dp (fun x hx => h3 x (hk x hx)) hd, h2⟩, h3, h4⟩, H.2⟩
  | Tone.one _, H => H
  | Tone.two _, H => H

/-! ## The composition -/

/-- **`[7 p q]` under `%next L th`, for runs that may call**: `RunOKLC` of
`q` under the goal (its subjects the products of `b`) and of `p` under the
goal `q`'s run returns give `RunOKLC` of the whole for `[7 b c]`, with the
witness relation `sevenWit`.  `hle`: `p`'s jump is at or after `q`'s; the
goal's sure part and entries were allocated before the run.  Both `sem`
clauses share `core`: the forward one takes `p`'s tone from `minkF_sevenC`
and `q`'s from its `sem`, the backward one both from the `semB` clauses and
builds the whole's `+mink` run by `mink_sevenC_bwd`. -/
theorem runOKLC_seven {lib : Lib} {P : Noun → Prop} {fb fc : Noun} {L : Lazy S} {th : Jmp} {Qp Qq : Wit}
    {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKLC (Map := Map) lib (Img lib P fb) fc L th Qq g0 g1 nx)
    (Rp : RunOKLC (Map := Map) lib P fb nx.laz nx.th Qp g1 g2 nex)
    (hle : nx.th.there ≤ nex.th.there) (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo) :
    RunOKLC lib P (n3 (A 7) fb fc) L th (sevenWit Qp Qq) g0 g2 nex := by
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
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
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
