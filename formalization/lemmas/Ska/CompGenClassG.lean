import lemmas.Ska.CompGenClassD
import lemmas.Ska.CompGenClassC

/-!
# The general cons: the sure part (`sem`, `semB`, `nec`), the run composed

README Gaps 12.39, item 12.  At run time the cons's code is the copy's block
at `g3.bo` (it fills both parts' result needs from the merged ones), `p`'s
code from `np.th` to `nq.th`, `q`'s code from `nq.th` to the split's block at
`g0.bo` (it builds the goal's sure need from the halves), then `th`.

* `cs_minkEq_cons`: `+mink` of `C fp fq` (head a cell) is the pure
  evaluation of the cons when both parts' are.
* `cs_goal_cons`: the composition of the run at the level of `GoalSemCMD`:
  the copy's step, `p`'s `GoalSemCMD` at its tone, `q`'s at every state and
  registers `p` may leave (its input need `pair ned dp`, so `p`'s witness
  survives `q`), the split's block: the whole's `GoalSemCMD` with
  `consWit` at the cons's tone.  Both `SemG` and `SemGW` of the cons reduce
  to it.
* `nec_consG`: `nec` of the cons from the parts' `nec`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+mink` of a cons whose head is a cell** is the pure evaluation of the
cons when both parts' `+mink` are theirs. -/
theorem cs_minkEq_cons {lib : Lib} {P : Noun → Prop} {fp fq : Noun} {p q : Nomm} (hfh : ∃ a b, fp = C a b)
    (Mp : MinkEq lib P fp p) (Mq : MinkEq lib P fq q) : MinkEq lib P (C fp fq) (Nomm.cons p q) := by
  intro s hs gul tm r
  constructor
  · rintro ⟨n, hm⟩
    obtain ⟨n', _, rh, eh, H⟩ := minkF_consG hfh hm
    have e1 := (Mp s hs gul tm rh).mp ⟨n', eh⟩
    rcases H with ⟨hne, rfl⟩ | ⟨x, rfl, rt, et, H2⟩
    · cases hp : pureEval p s with
      | none => rw [e1, hp]; simp [pureEval, hp]
      | some x => rw [hp] at e1; exact absurd e1 (hne x)
    · have hp : pureEval p s = some x := by
        cases hp : pureEval p s with
        | none => rw [hp] at e1; cases e1
        | some x' => rw [hp] at e1; cases e1; rfl
      have e2 := (Mq s hs gul tm rt).mp ⟨n', et⟩
      rcases H2 with ⟨hne, rfl⟩ | ⟨y, rfl, rfl⟩
      · cases hq : pureEval q s with
        | none => rw [e2, hq]; simp [pureEval, hp, hq]
        | some y => rw [hq] at e2; exact absurd e2 (hne y)
      · have hq : pureEval q s = some y := by
          cases hq : pureEval q s with
          | none => rw [hq] at e2; cases e2
          | some y' => rw [hq] at e2; cases e2; rfl
        simp [pureEval, hp, hq, toneOf]
  · rintro rfl
    have B := mink_consG_bwd (ft := fq) hfh ((Mp s hs gul tm _).mpr rfl)
    cases hp : pureEval p s with
    | none =>
      rw [hp] at B
      have e : toneOf tm (pureEval (Nomm.cons p q) s) = toneOf tm none := by simp [pureEval, hp]
      rw [e]; exact B.1 (fun _ h => by cases h)
    | some x =>
      rw [hp] at B
      have B2 := B.2 x _ rfl ((Mq s hs gul tm _).mpr rfl)
      cases hq : pureEval q s with
      | none =>
        rw [hq] at B2
        have e : toneOf tm (pureEval (Nomm.cons p q) s) = toneOf tm none := by simp [pureEval, hp, hq]
        rw [e]; exact B2.1 (fun _ h => by cases h)
      | some y =>
        rw [hq] at B2
        have e : toneOf tm (pureEval (Nomm.cons p q) s) = Tone.zero (C x y) := by simp [pureEval, hp, hq, toneOf]
        rw [e]; exact B2.2 y _ rfl rfl

section Run
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop}
  {ν : σ → Needs}

theorem cs_returns_move {st st1 : σ} {regs regs1 : Map (Option Noun)} {t : Trace} {je j1 : Jmp} {r : Tone}
    (h : ReturnsC lib O c gul Inv ν st1 regs1 t j1 r) (hle : ν st ≤ ν st1)
    (hj : goJ lib O c gul st regs t je = goJ lib O c gul st1 regs1 t j1) :
    ReturnsC lib O c gul Inv ν st regs t je r := by
  obtain ⟨ton, st', hI', hle', hg, hrel⟩ := h
  exact ⟨ton, st', hI', Needs.le_trans hle hle', by rw [hj]; exact hg, hrel⟩

/-- **The cons's run, composed** (see the header). -/
theorem cs_goal_cons {st : σ} {regs regs1 : Map (Option Noun)} {t tm : Trace} {je jp jq th : Jmp} {os : Nat}
    {p q : Nomm} {s s0 : Noun} {ned : Need} {Lsure Hsure Tsure Qsure : Sure S} {Ps : List Pole}
    {Qp Qq : Wit} {loS lo2 : Nat} {K : Nat → Prop}
    (hj : goJ lib O c gul st regs t je = goJ lib O c gul st regs1 t jp)
    (hQ1 : HoldsS Qsure regs1 s) (hn1 : HoldsN ned regs1 s0)
    (hk1 : ∀ x, K x → SkaModel.read x regs1 = SkaModel.read x regs)
    (HP : GoalSemCMD lib O c gul Inv ν (fun x => (x < lo2 ∨ NMem ned x) ∧ ¬ NMem Hsure.ned x) st regs1 t tm jp
      Hsure jq (Qp s) (toneOf tm (pureEval p s)))
    (HQ : ∀ x (st1 : σ) (regs2 : Map (Option Noun)) dp wp, pureEval p s = some x → Inv st1 → ν st ≤ ν st1 →
      Qp s x dp wp → HoldsS Qsure regs2 s → HoldsN (Need.pair ned dp) regs2 (C s0 wp) →
      goJ lib O c gul st regs1 t jp = goJ lib O c gul st1 regs2 t jq →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < loS ∨ NMem (Need.pair ned dp) x) ∧ ¬ NMem Tsure.ned x) st1 regs2
        t tm jq Tsure (jmp0 os) (Qq s) (toneOf tm (pureEval q s)))
    (hbs : HoonMap.get c.blocks os = some ⟨[], Ps, Termin.hop th⟩)
    (Sfit : ∀ x y, FitsS Lsure (C x y) ↔ FitsS Hsure x ∧ FitsS Tsure y)
    (Srun : ∀ (st' : σ) (R : Map (Option Noun)) (x y : Noun), HoldsN Hsure.ned R x → HoldsN Tsure.ned R y →
      ∃ R', Runs lib O c gul st' t Ps R R' ∧ HoldsN Lsure.ned R' (C x y) ∧
        ∀ z, ¬ NMem Lsure.ned z → SkaModel.read z R' = SkaModel.read z R)
    (hQK : ∀ x, NMem Qsure.ned x → x < lo2 ∧ ¬ NMem Hsure.ned x)
    (hHK : ∀ x, NMem Hsure.ned x → x < loS ∧ ¬ NMem Tsure.ned x)
    (hNH : ∀ x, NMem ned x → ¬ NMem Hsure.ned x)
    (hdp : ∀ v d w x, Qp s v d w → NMem d x → ¬ NMem Tsure.ned x ∧ ¬ NMem Lsure.ned x)
    (hdq : ∀ v d w x, Qq s v d w → NMem d x → ¬ NMem Lsure.ned x)
    (hK : ∀ x, K x → ((x < lo2 ∨ NMem ned x) ∧ ¬ NMem Hsure.ned x) ∧ (x < loS ∨ NMem ned x) ∧
      ¬ NMem Tsure.ned x ∧ ¬ NMem Lsure.ned x) :
    GoalSemCMD lib O c gul Inv ν K st regs t tm je Lsure th (consWit Qp Qq s)
      (toneOf tm (pureEval (Nomm.cons p q) s)) := by
  cases hp : pureEval p s with
  | none =>
    rw [hp] at HP
    have e : pureEval (Nomm.cons p q) s = none := by simp [pureEval, hp]
    rw [e]
    exact cs_returns_move (HP : ReturnsC lib O c gul Inv ν st regs1 t jp (Tone.two tm)) (Needs.le_refl _) hj
  | some x =>
    rw [hp] at HP
    have HP' : GoalSemCMD lib O c gul Inv ν (fun x => (x < lo2 ∨ NMem ned x) ∧ ¬ NMem Hsure.ned x) st regs1 t tm
        jp Hsure jq (Qp s) (Tone.zero x) := HP
    by_cases fx : FitsS Hsure x
    · obtain ⟨st1, regs2, dp, wp, hI1, hle1, hq1, hH2, hD2, hk2, hj2⟩ := HP'.1 fx
      have hQ2 : HoldsS Qsure regs2 s :=
        ⟨HoldsN.agree _ (fun z hz => hk2 z ⟨Or.inl (hQK z hz).1, (hQK z hz).2⟩) hQ1.1, hQ1.2⟩
      have hn2 : HoldsN ned regs2 s0 := HoldsN.agree _ (fun z hz => hk2 z ⟨Or.inr hz, hNH z hz⟩) hn1
      have HQ' := HQ x st1 regs2 dp wp hp hI1 hle1 hq1 hQ2 ⟨hn2, hD2⟩ hj2
      cases hq : pureEval q s with
      | none =>
        rw [hq] at HQ'
        have e : pureEval (Nomm.cons p q) s = none := by simp [pureEval, hp, hq]
        rw [e]
        exact cs_returns_move (HQ' : ReturnsC lib O c gul Inv ν st1 regs2 t jq (Tone.two tm)) hle1 (hj.trans hj2)
      | some y =>
        rw [hq] at HQ'
        have HQ'' : GoalSemCMD lib O c gul Inv ν (fun x => (x < loS ∨ NMem (Need.pair ned dp) x) ∧
            ¬ NMem Tsure.ned x) st1 regs2 t tm jq Tsure (jmp0 os) (Qq s) (Tone.zero y) := HQ'
        have e : toneOf tm (pureEval (Nomm.cons p q) s) = Tone.zero (C x y) := by simp [pureEval, hp, hq, toneOf]
        rw [e]
        refine ⟨fun fL => ?_, fun nfL => ?_⟩
        · have fy := ((Sfit x y).mp fL).2
          obtain ⟨st2, regs3, dq, wq, hI2, hle2, hq2, hT3, hD3, hk3, hj3⟩ := HQ''.1 fy
          have hH3 : HoldsN Hsure.ned regs3 x :=
            HoldsN.agree _ (fun z hz => hk3 z ⟨Or.inl (hHK z hz).1, (hHK z hz).2⟩) hH2
          have hDp3 : HoldsN dp regs3 wp :=
            HoldsN.agree _ (fun z hz => hk3 z ⟨Or.inr (Or.inr hz), (hdp _ _ _ z hq1 hz).1⟩) hD2
          obtain ⟨R4, r4, hL4, k4⟩ := Srun st2 regs3 x y hH3 hT3
          refine ⟨st2, R4, Need.pair dp dq, C wp wq, hI2, Needs.le_trans hle1 hle2,
            ⟨x, y, dp, wp, dq, wq, hq1, hq2, rfl, rfl, rfl⟩, hL4,
            ⟨HoldsN.agree _ (fun z hz => k4 z (hdp _ _ _ z hq1 hz).2) hDp3,
             HoldsN.agree _ (fun z hz => k4 z (hdq _ _ _ z hq2 hz)) hD3⟩, fun z hz => ?_, ?_⟩
          · obtain ⟨h1, h2, h3, h4⟩ := hK z hz
            rw [k4 z h4, hk3 z ⟨h2.imp id Or.inl, h3⟩, hk2 z h1, hk1 z hz]
          · have e4 := r4 [] (Termin.hop th)
            simp only [List.append_nil] at e4
            rw [hj, hj2, hj3, goJ_jmp0 regs3 t os _ hbs, e4, execBlob_hop]
        · have nfy : ¬ FitsS Tsure y := fun fy => nfL ((Sfit x y).mpr ⟨fx, fy⟩)
          exact cs_returns_move (HQ''.2 nfy) hle1 (hj.trans hj2)
    · have R1 := HP'.2 fx
      cases hq : pureEval q s with
      | none =>
        have e : pureEval (Nomm.cons p q) s = none := by simp [pureEval, hp, hq]
        rw [e]
        exact cs_returns_move R1 (Needs.le_refl _) hj
      | some y =>
        have e : toneOf tm (pureEval (Nomm.cons p q) s) = Tone.zero (C x y) := by simp [pureEval, hp, hq, toneOf]
        rw [e]
        exact ⟨fun fL => absurd ((Sfit x y).mp fL).1 fx, fun _ => cs_returns_move R1 (Needs.le_refl _) hj⟩

end Run

/-- **A part's `nec` on a pure part**: its value fails or does not fit. -/
theorem cs_nec_pure {lib : Lib} {P : Noun → Prop} {f : Noun} {nm : Nomm} (M : MinkEq lib P f nm) {s : Noun}
    (hs : P s) {sur : Sure S} {j : Jmp} (h : NecC lib f (CGoal.next sur j) s) :
    pureEval nm s = none ∨ ∃ x, pureEval nm s = some x ∧ ¬ FitsS sur x := by
  obtain ⟨r, hm, hb⟩ := h.2 (A 0) []
  rw [(M s hs (A 0) [] r).mp hm] at hb
  cases hp : pureEval nm s with
  | none => exact Or.inl rfl
  | some x =>
    rw [hp] at hb
    rcases hb with e | ⟨p', e, hn⟩
    · cases e
    · cases e; exact Or.inr ⟨x, rfl, hn⟩

/-- **`nec` of the cons** from the parts' `nec`: the merged sure need fits
iff both parts' do (the copy), the goal's iff both halves do (the split). -/
theorem nec_consG {lib : Lib} {P : Noun → Prop} {fp fq : Noun} {p q : Nomm} (hfh : ∃ a b, fp = C a b)
    (Mp : MinkEq lib P fp p) (Mq : MinkEq lib P fq q) {Msure Psure Qsure Lsure Hsure Tsure : Sure S}
    {th jp jq : Jmp}
    (Np : ∀ s, P s → ¬ FitsS Psure s → NecC lib fp (CGoal.next Hsure jp) s)
    (Nq : ∀ s, P s → ¬ FitsS Qsure s → NecC lib fq (CGoal.next Tsure jq) s)
    (Cfit : ∀ z, FitsS Msure z ↔ FitsS Psure z ∧ FitsS Qsure z)
    (Sfit : ∀ x y, FitsS Lsure (C x y) ↔ FitsS Hsure x ∧ FitsS Tsure y) :
    ∀ s, P s → ¬ FitsS Msure s → NecC lib (C fp fq) (CGoal.next Lsure th) s := by
  intro s hs hnf
  refine necC_of_pure (cs_minkEq_cons hfh Mp Mq) hs ?_
  have hpq : ¬ FitsS Psure s ∨ ¬ FitsS Qsure s := by
    by_cases h1 : FitsS Psure s
    · exact Or.inr fun h2 => hnf ((Cfit s).mpr ⟨h1, h2⟩)
    · exact Or.inl h1
  rcases hpq with h | h
  · rcases cs_nec_pure Mp hs (Np s hs h) with e | ⟨x, e, nx⟩
    · exact Or.inl (by simp [pureEval, e])
    · cases hq : pureEval q s with
      | none => exact Or.inl (by simp [pureEval, e, hq])
      | some y => exact Or.inr ⟨C x y, by simp [pureEval, e, hq], fun f => nx ((Sfit x y).mp f).1⟩
  · rcases cs_nec_pure Mq hs (Nq s hs h) with e | ⟨y, e, ny⟩
    · cases hp : pureEval p s with
      | none => exact Or.inl (by simp [pureEval, hp])
      | some x => exact Or.inl (by simp [pureEval, hp, e])
    · cases hp : pureEval p s with
      | none => exact Or.inl (by simp [pureEval, hp])
      | some x => exact Or.inr ⟨C x y, by simp [pureEval, hp, e], fun f => ny ((Sfit x y).mp f).2⟩

/-- **What the assembly of the cons's sure part reads**, besides the parts'
`RunOKGen`: the copy's root block (from the merged sure need it fills both
parts' sure needs and hops to `np.th`), the split's root block (it builds
`L.sure` from the halves and hops to `th`), the parts' agreement from the
whole's (`q`'s at the input need `pair ned dp`, so `p`'s witness survives
`q`), and where the registers lie. -/
structure ConsSemPre (lib : Lib) (L : Lazy S) (th : Jmp) (hed tel : Lazy S) (g0 gS g2 g3 g1 : Gen Map)
    (nq np nex : NextL S) : Prop where
  copy : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map), (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries nex.laz).map Prod.fst →
      HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cf)) →
    ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (regs : Map (Option Noun)) (s : Noun),
      HoldsS nex.laz.sure regs s →
      ∃ regs1, goJ lib O c gul st regs t nex.th = goJ lib O c gul st regs1 t np.th ∧
        HoldsS np.laz.sure regs1 s ∧ HoldsS nq.laz.sure regs1 s ∧
        ∀ y, ¬ NMem np.laz.sure.ned y → ¬ NMem nq.laz.sure.ned y → SkaModel.read y regs1 = SkaModel.read y regs
  split : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map), (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries nex.laz).map Prod.fst →
      HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cf)) →
    ∃ Ps, HoonMap.get c.blocks g0.bo = some ⟨[], Ps, Termin.hop th⟩ ∧
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st' : σ) (t : Trace) (R : Map (Option Noun)) (x y : Noun),
        HoldsN hed.sure.ned R x → HoldsN tel.sure.ned R y →
        ∃ R', Runs lib O c gul st' t Ps R R' ∧ HoldsN L.sure.ned R' (C x y) ∧
          ∀ z, ¬ NMem L.sure.ned z → SkaModel.read z R' = SkaModel.read z R
  sfit : ∀ x y, FitsS L.sure (C x y) ↔ FitsS hed.sure x ∧ FitsS tel.sure y
  cfit : ∀ z, FitsS nex.laz.sure z ↔ FitsS np.laz.sure z ∧ FitsS nq.laz.sure z
  agP : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (s0 s : Noun),
      (∀ x, NMem ned x → g1.re ≤ x) →
      (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) →
      ∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g2 g3 np.laz s0 s
  agQ : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (s0 s : Noun) (dp : Need) (wp : Noun),
      (∀ x, NMem ned x → g1.re ≤ x) → (∀ x, NMem dp x → g2.re ≤ x ∧ x < g3.re) →
      (∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) →
      ∀ (st' : σ) (t' : Trace), AgreeG lib O c gul st' t' cf (Need.pair ned dp) gS g2 nq.laz (C s0 wp) s
  re0 : g0.re ≤ gS.re
  c3 : ∀ k, k < g3.re → HoonMap.get g1.cond k = HoonMap.get g3.cond k
  c2 : ∀ k, k < g2.re → HoonMap.get g1.cond k = HoonMap.get g2.cond k
  reS : gS.re ≤ g2.re
  re2 : g2.re ≤ g3.re
  re3 : g3.re ≤ g1.re
  qk : ∀ x, NMem nq.laz.sure.ned x → x < g2.re ∧ ¬ NMem hed.sure.ned x
  hk : ∀ x, NMem hed.sure.ned x → x < gS.re ∧ ¬ NMem tel.sure.ned x
  tlo : ∀ x, NMem tel.sure.ned x → x < gS.re
  llo : ∀ x, NMem L.sure.ned x → x < gS.re
  lt1 : ∀ x, (NMem np.laz.sure.ned x ∨ NMem nq.laz.sure.ned x ∨ NMem hed.sure.ned x ∨ NMem tel.sure.ned x) →
    x < g1.re
  orig : ∀ x, x < g0.re →
    (NMem np.laz.sure.ned x ∨ NMem nq.laz.sure.ned x ∨ NMem hed.sure.ned x ∨ NMem tel.sure.ned x) →
    NMem L.sure.ned x

section Asm
variable {lib : Lib} {N : Needs} {P : Noun → Prop} {fp fq : Noun} {p q : Nomm} {L hed tel : Lazy S} {th : Jmp}
  {g0 gS g2 g3 g1 : Gen Map} {nq np nex : NextL S} {Qp Qq : Wit}

theorem cs_hc {cf : Map (Nat × List Nat)} {g : Gen Map} (hcf : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k)
    (hle : g.re ≤ g1.re) (hc : ∀ k, k < g.re → HoonMap.get g1.cond k = HoonMap.get g.cond k) :
    ∀ k, k < g.re → HoonMap.get cf k = HoonMap.get g.cond k := fun k hk => by
  rw [hcf k (by omega), hc k hk]

/-- The registers the whole keeps are kept by every step. -/
theorem cs_keep (X : ConsSemPre (Map := Map) lib L th hed tel g0 gS g2 g3 g1 nq np nex) {ned : Need}
    (hned : ∀ x, NMem ned x → g1.re ≤ x) (x : Nat) (hx : (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) :
    ¬ NMem np.laz.sure.ned x ∧ ¬ NMem nq.laz.sure.ned x ∧ ¬ NMem hed.sure.ned x ∧ ¬ NMem tel.sure.ned x := by
  have h : (NMem np.laz.sure.ned x ∨ NMem nq.laz.sure.ned x ∨ NMem hed.sure.ned x ∨ NMem tel.sure.ned x) →
      False := fun m => by
    rcases hx.1 with h | h
    · exact hx.2 (X.orig x h m)
    · have := X.lt1 x m; have := hned x h; omega
  exact ⟨fun m => h (Or.inl m), fun m => h (Or.inr (Or.inl m)), fun m => h (Or.inr (Or.inr (Or.inl m))),
    fun m => h (Or.inr (Or.inr (Or.inr m)))⟩

/-- **`SemG` of the general cons.** -/
theorem semG_consG (hfh : ∃ a b, fp = C a b) (Mp : MinkEq lib P fp p) (Mq : MinkEq lib P fq q)
    (Sp : SemG lib N P fp hed nq.th Qp g2 g3 np) (Sq : SemG lib N P fq tel (jmp0 g0.bo) Qq gS g2 nq)
    (dp3 : ∀ s v d w r, Qp s v d w → NMem d r → g2.re ≤ r ∧ r < g3.re)
    (dq2 : ∀ s v d w r, Qq s v d w → NMem d r → gS.re ≤ r ∧ r < g2.re)
    (X : ConsSemPre (Map := Map) lib L th hed tel g0 gS g2 g3 g1 nq np nex) :
    SemG lib N P (C fp fq) L th (consWit Qp Qq) g0 g1 nex := by
  intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
  rw [(cs_minkEq_cons hfh Mp Mq s hs gul tm r).mp ⟨n, hm⟩]
  obtain ⟨n', hn', rh, eh, H⟩ := minkF_consG hfh hm
  have erh := (Mp s hs gul tm rh).mp ⟨n', eh⟩
  have hF' := oracleFwd_le hF (Nat.le_of_lt hn')
  have re1 := X.re3; have re2 := X.re2; have reS := X.reS; have re0 := X.re0
  obtain ⟨regs1, hj, hP1, hQ1, hk1⟩ := X.copy cf hcf c (ag st t).1 σ O gul st t regs s hh
  have hn1 : HoldsN ned regs1 s0 := HoldsN.agree _ (fun z hz => hk1 z
    (fun m => by have := X.lt1 z (Or.inl m); have := hned z hz; omega)
    (fun m => by have := X.lt1 z (Or.inr (Or.inl m)); have := hned z hz; omega)) hn
  have HP := Sp cf (cs_hc hcf re1 X.c3) c ned σ Inv ν O n' gul hN hS hF' st t tm s0 s rh hI htr hs eh
    (X.agP cf hcf c ned σ O gul s0 s hned ag) (fun z hz => by have := hned z hz; omega) regs1 hP1 hn1
  rw [erh] at HP
  obtain ⟨Ps, hbs, Srun⟩ := X.split cf hcf c (ag st t).1
  refine cs_goal_cons (loS := gS.re) (lo2 := g2.re) hj hQ1 hn1
    (fun z hz => hk1 z (cs_keep X hned z hz).1 (cs_keep X hned z hz).2.1) HP ?_ hbs X.sfit
    (fun st' => Srun σ O gul st' t) X.qk X.hk (fun z hz m => by have := (X.hk z m).1; have := hned z hz; omega)
    (fun v d w z hq hz => ⟨fun m => by have := X.tlo z m; have := (dp3 s v d w z hq hz).1; omega,
      fun m => by have := X.llo z m; have := (dp3 s v d w z hq hz).1; omega⟩)
    (fun v d w z hq hz m => by have := X.llo z m; have := (dq2 s v d w z hq hz).1; omega) ?_
  · intro x st1 regs2 dp wp hpx hI1 hle1 hq1 hQ2 hN2 hj2
    have ex : rh = Tone.zero x := by rw [erh, hpx]; rfl
    rcases H with ⟨hne, _⟩ | ⟨x', ex', rt, et, _⟩
    · exact absurd ex (hne x)
    · have ert := (Mq s hs gul tm rt).mp ⟨n', et⟩
      have HQ := Sq cf (cs_hc hcf (by omega) X.c2) c (Need.pair ned dp) σ Inv ν O n' gul hN hS hF' st1 t tm
        (C s0 wp) s rt hI1 (htr.imp fun _ _ => FrameRel.mono hle1) hs et
        (X.agQ cf hcf c ned σ O gul s0 s dp wp hned (fun z hz => dp3 s x dp wp z hq1 hz) ag)
        (fun z hz => by
          rcases hz with hz | hz
          · have := hned z hz; omega
          · exact (dp3 s x dp wp z hq1 hz).1) regs2 hQ2 hN2
      rw [ert] at HQ
      exact HQ
  · intro z hz
    obtain ⟨n1, n2, n3, n4⟩ := cs_keep X hned z hz
    exact ⟨⟨hz.1.imp (fun h => by omega) id, n3⟩, hz.1.imp (fun h => by omega) id, n4, hz.2⟩

/-- **`SemGW` of the general cons.** -/
theorem semGW_consG (hfh : ∃ a b, fp = C a b) (Mp : MinkEq lib P fp p) (Mq : MinkEq lib P fq q)
    (Sp : SemGW lib N P fp hed nq.th Qp g2 g3 np) (Sq : SemGW lib N P fq tel (jmp0 g0.bo) Qq gS g2 nq)
    (dp3 : ∀ s v d w r, Qp s v d w → NMem d r → g2.re ≤ r ∧ r < g3.re)
    (dq2 : ∀ s v d w r, Qq s v d w → NMem d r → gS.re ≤ r ∧ r < g2.re)
    (X : ConsSemPre (Map := Map) lib L th hed tel g0 gS g2 g3 g1 nq np nex) :
    SemGW lib N P (C fp fq) L th (consWit Qp Qq) g0 g1 nex := by
  intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
  refine ⟨_, (cs_minkEq_cons hfh Mp Mq s hs gul tm _).mpr rfl, ?_⟩
  have re1 := X.re3; have re2 := X.re2; have reS := X.reS; have re0 := X.re0
  obtain ⟨regs1, hj, hP1, hQ1, hk1⟩ := X.copy cf hcf c (ag st t).1 σ O gul st t regs s hh
  have hn1 : HoldsN ned regs1 s0 := HoldsN.agree _ (fun z hz => hk1 z
    (fun m => by have := X.lt1 z (Or.inl m); have := hned z hz; omega)
    (fun m => by have := X.lt1 z (Or.inr (Or.inl m)); have := hned z hz; omega)) hn
  obtain ⟨rh, mh, HP⟩ := Sp cf (cs_hc hcf re1 X.c3) c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
    (X.agP cf hcf c ned σ O gul s0 s hned ag) (fun z hz => by have := hned z hz; omega) regs1 hP1 hn1 res
    (by rw [← hj]; exact hres)
  rw [(Mp s hs gul tm rh).mp mh] at HP
  obtain ⟨Ps, hbs, Srun⟩ := X.split cf hcf c (ag st t).1
  refine cs_goal_cons (loS := gS.re) (lo2 := g2.re) hj hQ1 hn1
    (fun z hz => hk1 z (cs_keep X hned z hz).1 (cs_keep X hned z hz).2.1) HP ?_ hbs X.sfit
    (fun st' => Srun σ O gul st' t) X.qk X.hk (fun z hz m => by have := (X.hk z m).1; have := hned z hz; omega)
    (fun v d w z hq hz => ⟨fun m => by have := X.tlo z m; have := (dp3 s v d w z hq hz).1; omega,
      fun m => by have := X.llo z m; have := (dp3 s v d w z hq hz).1; omega⟩)
    (fun v d w z hq hz m => by have := X.llo z m; have := (dq2 s v d w z hq hz).1; omega) ?_
  · intro x st1 regs2 dp wp hpx hI1 hle1 hq1 hQ2 hN2 hj2
    obtain ⟨rt, mt, HQ⟩ := Sq cf (cs_hc hcf (by omega) X.c2) c (Need.pair ned dp) σ Inv ν O gul hN hS hB st1 t tm
      (C s0 wp) s hI1 (htr.imp fun _ _ => FrameRel.mono hle1) hs
      (X.agQ cf hcf c ned σ O gul s0 s dp wp hned (fun z hz => dp3 s x dp wp z hq1 hz) ag)
      (fun z hz => by
        rcases hz with hz | hz
        · have := hned z hz; omega
        · exact (dp3 s x dp wp z hq1 hz).1) regs2 hQ2 hN2 res (by rw [← hj2, ← hj]; exact hres)
    rw [(Mq s hs gul tm rt).mp mt] at HQ
    exact HQ
  · intro z hz
    obtain ⟨n1, n2, n3, n4⟩ := cs_keep X hned z hz
    exact ⟨⟨hz.1.imp (fun h => by omega) id, n3⟩, hz.1.imp (fun h => by omega) id, n4, hz.2⟩

/-- **The sure part of the general cons**: `SemG`, `SemGW` and `nec` from the
parts' `RunOKGen` and `ConsSemPre`. -/
theorem semCoreG_consG (hfh : ∃ a b, fp = C a b) (Mp : MinkEq lib P fp p) (Mq : MinkEq lib P fq q)
    {xq xp : Bool} (Rq : RunOKGen (Map := Map) lib N P fq tel (jmp0 g0.bo) Qq xq gS g2 nq)
    (Rp : RunOKGen (Map := Map) lib N P fp hed nq.th Qp xp g2 g3 np)
    (X : ConsSemPre (Map := Map) lib L th hed tel g0 gS g2 g3 g1 nq np nex) :
    SemG lib N P (C fp fq) L th (consWit Qp Qq) g0 g1 nex ∧
    SemGW lib N P (C fp fq) L th (consWit Qp Qq) g0 g1 nex ∧
    ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib (C fp fq) (CGoal.next L.sure th) s :=
  ⟨semG_consG hfh Mp Mq Rp.sem Rq.sem Rp.dreg Rq.dreg X, semGW_consG hfh Mp Mq Rp.semB Rq.semB Rp.dreg Rq.dreg X,
   nec_consG hfh Mp Mq Rp.nec Rq.nec X.cfit X.sfit⟩

end Asm

end Comp
end SkaModel
end Formalization
