import lemmas.Ska.CompConsLSCall
import lemmas.Ska.CompKerfLC

/-!
# The indirect call under a flat lazy goal: `lokS_indirect`

README Gaps 12.26.  The indirect call `[2 p q]` whose parts meet `LOKS`.
Its run under `%next L th` is `+kerf` (block `out`, the product register
`pro`, `+kern`'s ops in front of every entry), the `%nok` block at `bo`,
then the pair of `q` (under `%next (lazy-from-reg re+1) (jmp0 nok)`), `+past`
behind `p`, and `p` (under `%next (lazy-from-reg re)`), then `+copy`.

The pair is `pairLS_ok` with the goal `%next [this re this re+1] (jmp0
nok)` and the formula `[fb fc]`: the phase of `+split` is empty (the block
`o` is the goal's jump itself, so the last step is the identity), and the
product is the cell of the two parts' products held in the two registers.
Then:

* `nokLB`: the `%nok` block behind the pair: `RunOKLB` of the call's inner
  run under `%next (lazy-from-reg pro) (jmp0 out)`, for the formula of the
  call (`MinkC2`), with no witness (`noWit`);
* `kerfLB`: `+kerf` in front (`kerfLC` for `RunOKLB`), with the fronts at the
  state level (`FrontsS`, from `kernPW_fill`);
* `lokS_indirect`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Small facts -/

/-- The pair need of the two registers `a`, `a + 1`. -/
def pairReg (a : Nat) : Sure S := ⟨Need.pair (Need.this a) (Need.this (a + 1)), HoonSet.empty⟩

theorem fitsS_pairReg (a : Nat) (x y : Noun) : FitsS (pairReg a : Sure S) (C x y) := ⟨⟨trivial, trivial⟩, looks_empty _⟩

theorem goalSemCMD_nz {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop}
    {ν : σ → Needs} {K K' : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur sur' : Sure S} {th th' : Jmp} {Q Q' : Noun → Need → Noun → Prop} :
    ∀ {r : Tone}, (∀ q, r ≠ Tone.zero q) → GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r →
      GoalSemCMD lib O c gul Inv ν K' st regs t tm je sur' th' Q' r
  | Tone.zero q, hn, _ => absurd rfl (hn q)
  | Tone.one _, _, h => h
  | Tone.two _, _, h => h

theorem badC_nz {goal goal' : CGoal S} {tm : Trace} {r : Tone} (hn : ∀ q, r ≠ Tone.zero q)
    (h : BadC goal tm r) : BadC goal' tm r := by
  rcases h with e | ⟨p, e, _⟩
  · exact Or.inl e
  · exact absurd e (hn p)

/-- `+mink` on the cons `[fb fc]` from its parts, at one more step. -/
theorem consStep {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s fb fc : Noun} {rb : Tone}
    (hfb : ∃ a b, fb = C a b) (e1 : minkF lib gul n tm s fb = some rb) :
    ((∀ q, rb ≠ Tone.zero q) → minkF lib gul (n + 1) tm s (C fb fc) = some rb) ∧
    ∀ x, rb = Tone.zero x → ∀ rc, minkF lib gul n tm s fc = some rc →
      ((∀ q, rc ≠ Tone.zero q) → minkF lib gul (n + 1) tm s (C fb fc) = some rc) ∧
      ∀ y, rc = Tone.zero y → minkF lib gul (n + 1) tm s (C fb fc) = some (Tone.zero (C x y)) := by
  obtain ⟨a, b, rfl⟩ := hfb
  refine ⟨fun hn => ?_, fun x ex rc e2 => ?_⟩
  · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1]
    cases rb with
    | zero q => exact absurd rfl (hn q)
    | one _ => rfl
    | two _ => rfl
  · subst ex
    refine ⟨fun hn => ?_, fun y ey => ?_⟩
    · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1, tbind_zero, e2]
      cases rc with
      | zero q => exact absurd rfl (hn q)
      | one _ => rfl
      | two _ => rfl
    · subst ey
      rw [minkF_succ_eq]; simp only [minkStep]; rw [e1, tbind_zero, e2]; rfl

/-- `+mink` on `[fb fc]`: a tone that is no product is the call's, or the
product is the cell of the parts' products. -/
theorem consMink_cases {lib : Lib} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC2 lib P f fb fc)
    (hfb : ∃ a b, fb = C a b) {s gul : Noun} {tm : Trace} {r : Tone} (hs : P s)
    (h : Mink lib gul tm s (C fb fc) r) :
    ((∀ q, r ≠ Tone.zero q) ∧ Mink lib gul tm s f r) ∨
      ∃ x y, r = Tone.zero (C x y) ∧ Mink lib gul tm s fb (Tone.zero x) ∧ Mink lib gul tm s fc (Tone.zero y) := by
  obtain ⟨n, e⟩ := h
  obtain ⟨n', _, rh, e1, H⟩ := minkF_consG hfb e
  rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, e2, H⟩
  · exact Or.inl ⟨hnz, (M.bwd hs ⟨n', e1⟩).1 hnz⟩
  · rcases H with ⟨hnz, rfl⟩ | ⟨y, rfl, rfl⟩
    · exact Or.inl ⟨hnz, ((M.bwd hs ⟨n', e1⟩).2 x _ rfl ⟨n', e2⟩).1 hnz⟩
    · exact Or.inr ⟨x, y, rfl, ⟨n', e1⟩, ⟨n', e2⟩⟩

theorem agreeLB_mono {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cf : Map (Nat × List Nat)} {ned : Need} {g0 g0' g1 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeLB lib O c gul st t cf ned g0 g1 laz s0 s) (hb : g0.bo ≤ g0'.bo) :
    AgreeLB lib O c gul st t cf ned g0' g1 laz s0 s :=
  ⟨fun o h0 h1 hn => h.1 o (by omega) h1 hn, fun e he l => h.2 e he (by omega)⟩

/-! ## The `%nok` block behind the pair -/

/-- **The `%nok` block behind the pair of the indirect call**: `RunOKLB` of
the pair for the formula `[fb fc]` under `%next [this re this re+1] (jmp0
nok)` (from the state with the `%nok` block made) is `RunOKLB` of the call's
inner run under `%next (lazy-from-reg pro) (jmp0 out)` for the formula `f`
of the call (`MinkC2`), from the state before. -/
theorem nokLB {lib : Lib} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC2 lib P f fb fc) (hfb : ∃ a b, fb = C a b)
    {g2 g3 g' : Gen Map} {nex : NextL S} {out pro : Nat} {Q : Wit}
    (hpro : pro < g2.re) (hpk : HoonMap.get g2.cond pro = Option.none) (cb2 : CondBelow g2)
    (r3 : g3.re = g2.re + 2) (b3 : g3.bo = g2.bo + 1) (cn3 : g3.cond = g2.cond) (E3 : Ext g2 g3) (G3 : GrowU g2 g3)
    (k3o : HoonMap.get g3.blocks g2.bo = some ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩)
    (R : RunOKLB (Map := Map) lib P (C fb fc) (ofSure (pairReg g2.re)) (jmp0 g2.bo) Q false g3 g' nex) :
    RunOKLB (Map := Map) lib P f (ofSure (lazyReg pro)) (jmp0 out) noWit false g2 g' nex := by
  have e0 : entries (ofSure (pairReg g2.re : Sure S)) = [] := entries_ofSure _
  have e1 : entries (ofSure (lazyReg pro : Sure S)) = [] := entries_ofSure _
  have rl := R.re
  have bl := R.bo
  have nk : ∀ x, g2.re ≤ x → HoonMap.get g2.cond x = Option.none := fun x hx => condBelow_none cb2 hx
  have kN : HoonMap.get g'.blocks g2.bo = some ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩ := by
    rw [R.keep _ (by omega) (by rw [e0]; simp)]; exact k3o
  have lab' : ∀ e ∈ entries nex.laz, g3.bo ≤ e.1 := fun e he => by
    rcases (R.labs e he).1 with h | h
    · rw [e0] at h; cases h
    · exact h.1
  -- the `%nok` block in any code that agrees with the run
  have hbN : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (ned : Need) (s0 s : Noun),
      AgreeLB lib O c gul st t cf ned g2 g' nex.laz s0 s →
      HoonMap.get c.blocks g2.bo = some ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩ := by
    intro cf hcf c σ O gul st t ned s0 s ag
    have hc : ∀ x, x < g3.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun x hx => by
      rw [hcf x (by omega), R.cfr.get_lt hx, cn3]
    rw [ag.1 g2.bo (Nat.le_refl _) (by omega) (fun hm => by
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega), kN]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
      renJmp_nil _ (show (jmp0 out).args = [] from rfl)]
    rw [unproxy_none (by rw [hc _ (by omega)]; exact nk _ (Nat.le_refl _)),
      unproxy_none (by rw [hc _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hc _ (by omega)]; exact hpk)]
  have hK : ∀ (ned : Need) z, ((z < g2.re ∨ NMem ned z) ∧ ¬ NMem (lazyReg pro : Sure S).ned z) → z ≠ pro :=
    fun ned z hz e => hz.2 (by subst e; simp [lazyReg, NMem])
  have hK3 : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ z,
      ((z < g2.re ∨ NMem ned z) ∧ ¬ NMem (lazyReg pro : Sure S).ned z) →
      ((z < g3.re ∨ NMem ned z) ∧ ¬ NMem (ofSure (pairReg g2.re : Sure S)).sure.ned z) := fun ned hned z hz =>
    ⟨hz.1.imp (fun h => by omega) id, fun hm => by
      simp only [ofSure, sure_mk, pairReg, NMem] at hm
      rcases hz.1 with h | h
      · omega
      · have := hned z h; omega⟩
  refine ⟨by omega, by omega, R.drop.trans E3.2.2.1, fun o ho hn => ?_, G3.trans R.grow,
    (condFresh_of_eq (by omega) cn3).trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).1.elim (fun h => (by rw [e0] at h; cases h))
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup,
    fun s v d w r hq hr => (by simp only [noWit] at hq; subst hq; simp [NMem] at hr),
    fun s hs hf => ?_, R.ncond, R.econd, fun e he => (by rw [e1] at he; cases he), ?_, ?_⟩
  · rw [R.keep o (by omega) (by rw [e0]; simp), E3.2.2.2 o ho]
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, kN, rfl, rfl⟩
  · rcases R.regs r hr with h | h
    · simp only [ofSure, sure_mk, pairReg, NMem] at h
      exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · rcases (R.eregs e he).2 r hr with ⟨e0', h0, _⟩ | h | h
    · rw [e0] at h0; cases h0
    · simp only [ofSure, sure_mk, pairReg, NMem] at h
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · have N := R.nec s hs hf
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, e1', H⟩ := M.fwd hs hm
      rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rc, e2, H⟩
      · exact badC_nz hnz (N.1 gul _ tm _ ((consStep hfb e1').1 hnz))
      · rcases H with ⟨hnz, rfl⟩ | ⟨y, rfl, h3⟩
        · exact badC_nz hnz (N.1 gul _ tm _ (((consStep hfb e1').2 x rfl _ e2).1 hnz))
        · rcases N.1 gul _ tm _ (((consStep hfb e1').2 x rfl _ e2).2 y rfl) with e | ⟨p, e, hp⟩
          · cases e
          · cases e; exact absurd (fitsS_pairReg g2.re x y) hp
    · obtain ⟨r, hm, hb⟩ := N.2 gul tm
      rcases consMink_cases M hfb hs hm with ⟨hnz, hmf⟩ | ⟨x, y, rfl, _, _⟩
      · exact ⟨r, hmf, badC_nz hnz hb⟩
      · rcases hb with e | ⟨p, e, hp⟩
        · cases e
        · cases e; exact absurd (fitsS_pairReg g2.re x y) hp
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g3 g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨n', hn', rb, e1', H⟩ := M.fwd hs hm
    have hF' := oracleFwd_le hF (show n' + 1 ≤ n by omega)
    have Gp : ∀ r', minkF lib gul (n' + 1) tm s (C fb fc) = some r' → _ := fun r' e =>
      R.sem cf hcf c ned σ Inv ν O (n' + 1) gul hS hF' st t tm s0 s r' hI htr hs e ag3 hned regs hh hn
    rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rc, e2, H⟩
    · exact goalSemCMD_nz hnz (Gp _ ((consStep hfb e1').1 hnz))
    · rcases H with ⟨hnz, rfl⟩ | ⟨y, rfl, h3⟩
      · exact goalSemCMD_nz hnz (Gp _ (((consStep hfb e1').2 x rfl _ e2).1 hnz))
      · have G := Gp _ (((consStep hfb e1').2 x rfl _ e2).2 y rfl)
        obtain ⟨st1, R1, d, w, hI1, hν1, _, hh1, _, k1, e3⟩ := G.1 (fitsS_pairReg g2.re x y)
        have N := nokStep_fwd hS hF (hbN cf hcf c σ O gul st t ned s0 s (ag st)) (hK ned) (outGoal_self (S := S)) hI1
          (frames_mono hν1 htr) hh1.1 hh1.2 hn' h3
        exact goalSemCM_toCMD (fun p => ⟨p, rfl⟩)
          (goalSemCM_step hν1 (fun z hz => k1 z (hK3 ned hned z hz)) e3 _ _ N)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g3 g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨rp, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag3 hned regs hh hn res hres
    rcases consMink_cases M hfb hs hm with ⟨hnz, hmf⟩ | ⟨x, y, rfl, hx, hy⟩
    · exact ⟨rp, hmf, goalSemCMD_nz hnz G⟩
    · obtain ⟨st1, R1, d, w, hI1, hν1, _, hh1, _, k1, e3⟩ := G.1 (fitsS_pairReg g2.re x y)
      rw [e3] at hres
      obtain ⟨r, hmr, N⟩ := nokStep_bwd hS hB (hbN cf hcf c σ O gul st t ned s0 s (ag st)) (hK ned) (outGoal_self (S := S))
        hI1 (frames_mono hν1 htr) hh1.1 hh1.2 hres
      exact ⟨r, ((M.bwd hs hx).2 x _ rfl hy).2 y r rfl hmr, goalSemCM_toCMD (fun p => ⟨p, rfl⟩)
        (goalSemCM_step hν1 (fun z hz => k1 z (hK3 ned hned z hz)) e3 _ _ N)⟩

/-! ## `+kerf` in front -/

/-- **`+kerf` in front of the call's inner run, under a flat lazy goal**
(`kerfLC` for `RunOKLB`): the inner run's `RunOKLB` under `%next
(lazy-from-reg pro) (jmp0 out)` gives `RunOKLS` under `%next L th` with the
witness `kernWit pro`; the fronts at the state level are the ops of `KernPW`
(`kernPW_fill`), with no result entry at a goal label. -/
theorem kerfLB {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {g0 g2 g' : Gen Map}
    {out pro : Nat} {nex : NextL S} {Q : Wit}
    (hk : kerf (⟨L, th⟩ : NextL S) g0 = some ((out, pro), g2)) (d0 : g0.drop = false) (hcb : CondBelow g0)
    (hu : UpBelow g0) (hth : th.args = []) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (R : RunOKLB (Map := Map) lib P f (ofSure (lazyReg pro : Sure S)) (jmp0 out) Q false g2 g' nex) :
    RunOKLS (Map := Map) lib P f L th (kernWit pro) false g0 g' nex := by
  obtain ⟨rfl, rfl, b2, dr2, l2, PF, G2, ⟨A0, hB0, P0⟩, hE, hO, c0, crng⟩ := kerf_specL hk d0 hcb hu h1 h2 hlab hnd
  have e2 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have Re : Ext g2 g' := ⟨R.re, R.bo, R.drop, fun o ho => R.keep o ho (by rw [e2]; simp)⟩
  have rl := R.re
  have bl := R.bo
  have lab' : ∀ e ∈ entries nex.laz, g2.bo ≤ e.1 := fun e he =>
    (R.labs e he).1.elim (fun h => by rw [e2] at h; cases h) (fun h => h.1)
  -- the later `cond`s
  have hcf2 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun cf hcf x hx =>
    (hcf x (by omega)).trans (R.cfr.get_lt hx)
  have hfill : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ {sur : Sure S} {A : List Pole} {o : Nat}, KernPW (Map := Map) g0.re g2.cond (g0.re + 1) g2.re o sur A →
      Distinct sur.ned → (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
        (R : Map (Option Noun)) (v : Noun), SkaModel.read g0.re R = some v →
      (FitsS sur v → ∃ R', Runs lib O c gul st t (A.map (renPole (unproxy cf))) R R' ∧ HoldsS sur R' v ∧
        ∀ x, (x < g0.re + 1 ∨ (g2.re ≤ x ∧ x ≠ g0.re)) → ¬ NMem sur.ned x →
          SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ FitsS sur v → Crashes lib O c gul st t (A.map (renPole (unproxy cf))) R) :=
    fun cf hcf sur A o KP hd hsl' => kernPW_fill KP (by omega) hd (fun x hx => (hsl' x hx).1)
      (by rw [hcf2 cf hcf _ (by omega)]; exact c0)
      (fun x hx => by rw [hcf2 cf hcf _ (by have := (hsl' x hx).1; omega), PF.get_lt (hsl' x hx).1]; exact (hsl' x hx).2)
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
      GoalSemCM lib O c gul Inv ν (fun x => (x < g2.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg g0.re : Sure S)
        (jmp0 g0.bo)) x) st regs t tm nex.th (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
        L.sure th (kernWit g0.re s) r := by
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
      obtain ⟨F1, F2⟩ := hfill cf hcf P0 hsd hsl lib σ O c gul st1 t R1 p hp1
      refine ⟨fun fp => ?_, fun nf => ?_⟩
      · obtain ⟨R2, r2, hh2, k2⟩ := F1 fp
        have e2 : goJ lib O c gul st1 R1 t (jmp0 g0.bo) = goJ lib O c gul st1 R2 t th := by
          have := r2 [] (Termin.hop th)
          simp only [List.append_nil] at this
          rw [goJ_jmp0 _ _ _ _ hbo, this, execBlob_hop]
        refine ⟨st1, R2, Need.this g0.re, p, hI1, hν1, ⟨rfl, rfl⟩, hh2.1,
          (k2 g0.re (Or.inl (by omega)) (fun hm => by have := (hsl _ hm).1; omega)).trans hp1,
          fun x ⟨x1, x2⟩ => ?_, e1.trans e2⟩
        rw [k2 x (x1.elim (fun h => Or.inl (by omega)) (fun h => Or.inr ⟨by have := hned x h; omega, by
          have := hned x h; omega⟩)) x2]
        exact k1 x ⟨x1.elim (fun h => Or.inl (by omega)) Or.inr, fun e => by
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
      ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g2 g' nex.laz s0 s :=
    fun cf c ned σ O gul t s0 s ag st' => agreeLB_mono (ag st') (by omega)
  -- the fronts at the state level
  have FS : FrontsS (Map := Map) (kernWit g0.re) false g0 g' L nex := by
    intro e he
    obtain ⟨A, hA, KP⟩ := hE e he
    refine ⟨A, fun B fin hb => by rw [Re.2.2.2 _ (by have := (hlab e he).1; omega)]; exact hA B fin hb,
      fun cf hcf => Or.inr ⟨fun hm => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; have := (hlab e he).1; omega, ?_⟩⟩
    refine ⟨fun r hr => by simp [Sure.bunt, NMem] at hr, fun s v d w _ r _ hr => by simp [Sure.bunt, NMem] at hr,
      fun s v d w _ _ => fitsS_bunt s, fun lib σ O c gul st t R0 s v d w hq _ hd _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨F1, F2⟩ := hfill cf hcf KP (hed e he).1 (hed e he).2 lib σ O c gul st t R0 w hd
    refine ⟨fun fv => ?_, F2⟩
    obtain ⟨R2, r2, hh2, k2⟩ := F1 fv
    refine ⟨R2, r2, hh2, fun x hx hn' => k2 x ?_ hn'⟩
    rcases hx with h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
    · simp only [NMem] at h; subst h; exact Or.inl (by omega)
  have dreg : ∀ s v d w r, kernWit g0.re s v d w → NMem d r → g0.re ≤ r ∧ r < g'.re := fun s v d w r hq hr => by
    obtain ⟨rfl, rfl⟩ := hq
    simp only [NMem] at hr; subst hr; exact ⟨Nat.le_refl _, by omega⟩
  refine ⟨⟨by omega, by omega, Re.2.2.1.trans dr2, fun o ho hn' => by rw [Re.2.2.2 o (by omega), hO o ho hn'],
    G2.trans R.grow, PF.1.trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => Or.inr (Or.inr ?_)⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).1.elim (fun h => (by rw [e2] at h; cases h))
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup,
    dreg, fun s hs hf => ?_, R.ncond, R.econd,
    FS.toFront (by omega) (fun r hr => (hsl r hr).1) (fun e he r hr => (by simp [gsE, NMem] at hr)) dreg, ?_, ?_⟩, FS⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, by rw [Re.2.2.2 _ (by simp only [jmp0]; omega)]; exact hB0, rfl, rfl⟩
  · rcases R.regs r hr with h | h
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; subst h; exact Or.inr ⟨Nat.le_refl _, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · rcases (R.eregs e he).2 r hr with ⟨e0, h0, _⟩ | h | h
    · rw [e2] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; subst h; exact ⟨Nat.le_refl _, by omega⟩
    · exact ⟨by omega, h.2⟩
  · obtain ⟨N1, N2⟩ := R.nec s hs hf
    have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) tm r →
        BadC (CGoal.next L.sure th) tm r := fun h => by
      rcases h with e | ⟨q, _, nq⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg _ q) nq
    exact ⟨fun gul n tm r hm => bad (N1 gul n tm r hm), fun gul tm => by
      obtain ⟨r, hm, hb⟩ := N2 gul tm; exact ⟨r, hm, bad hb⟩⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r (goalSemCMD_toCM
      (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm (agR cf c ned σ O gul t s0 s ag) hned
        regs hh hn))
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs (agR cf c ned σ O gul t s0 s ag)
      hned regs hh hn res hres
    exact ⟨r, hm, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r (goalSemCMD_toCM G)⟩


/-! ## The indirect call -/

/-- **The indirect call whose parts meet `LOKS`, under a flat lazy goal**,
from a state as `LOKS.run` asks: `RunOKLS` with the witness `kernWit re`,
the jump a new block at none of the result's entries, the result flat with
clean entries.  The pair of `q` and `p` is `pairLS_ok` under `%next [this re
this re+1] (jmp0 nok)` (`pairReg`), the `%nok` block `nokLB`, `+kerf`
`kerfLB`. -/
theorem lokS_indirect_run (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (M : MinkC2 lib P f fb fc) (hfb : ∃ a b, fb = C a b)
    (Kp : (p.pure = true ∧ MinkEq lib P fb p) ∨ hinted env.cod p = some true)
    (Sp : LOKS (S := S) (Map := Map) false lib env P fb p) (Sq : LOKS (S := S) (Map := Map) false lib env P fc q)
    {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcount : sixCount (Nomm.n2 p q Option.none) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hta : th.args = [])
    (ht : th.there ∉ (entries L).map Prod.fst) (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfl : Flat L) (hcs : Clean L.sure.ned) (hce : ∀ e ∈ entries L, Clean e.2.sure.ned)
    (hr : runLC env sup (Nomm.n2 p q Option.none) (CGoalL.next L th) region g0 = some (nex, g1)) :
    (∃ Q, RunOKLS (Map := Map) lib P f L th Q false g0 g1 nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧ g0.bo ≤ nex.th.there ∧ Flat nex.laz ∧
      (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  obtain ⟨nex0, g1', out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, k1, k2, k3, k4, k5, k6, k7⟩ :=
    runLC_n2_none hr
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at k1
  obtain ⟨rfl, rfl⟩ := k1
  have hlab' : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ :=
    fun e he => ⟨(hlab e he).1, by obtain ⟨_, B, th', hb⟩ := hlab e he; exact ⟨B, _, hb⟩⟩
  have hk2 := k2
  obtain ⟨rfl, rfl, b2, dr2, l2, PF, G2, -, -, -, c0, -⟩ := kerf_specL k2 d0 hcb hu h1 h2 hlab' hnd
  have d2 : g2.drop = false := dr2.trans d0
  have u2 : UpBelow g2 := G2.up hu
  have cl2 : Clear g2 := hcl0.growU G2
  have cb2 : CondBelow g2 := PF.1.below hcb
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  -- the `%nok` block (as `indirectC_inner`)
  rw [emit_apply] at k3
  simp only [Option.some.injEq, Prod.mk.injEq] at k3
  obtain ⟨rfl, rfl⟩ := k3
  have nk : ∀ x, g2.re ≤ x → HoonMap.get g2.cond x = Option.none := fun x hx => condBelow_none cb2 hx
  have eb3 : ∀ k, HoonMap.get ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩).blocks k =
      if k = g2.bo then some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ else
        HoonMap.get g2.blocks k := fun k => by
    simp only [Gen.emitted, d2, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G0 := growU_emit (g := { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 })
    (b := ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩)
    (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; exact ⟨b0, (by omega)⟩) u2
  have G3 : GrowU g2 ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩) := ⟨G0.bo, G0.drop, G0.keep, G0.new⟩
  generalize hg3 : ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ : Gen Map) = g3 at G3 eb3 k4
  have r3 : g3.re = g2.re + 2 := by rw [← hg3]; simp [Gen.emitted]
  have b3 : g3.bo = g2.bo + 1 := by rw [← hg3]; simp [Gen.emitted]
  have d3 : g3.drop = false := by rw [← hg3]; simp [Gen.emitted, d2]
  have cn3 : g3.cond = g2.cond := by rw [← hg3]; simp [Gen.emitted]
  have k3o : HoonMap.get g3.blocks g2.bo = some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ := by
    rw [eb3, if_pos rfl]
  have E3 : Ext g2 g3 := ⟨by omega, by omega, by rw [d3, d2], fun k hk => by rw [eb3, if_neg (by omega)]⟩
  have u3 : UpBelow g3 := G3.up u2
  have cl3 : Clear g3 := cl2.growU G3
  have cb3 : CondBelow g3 := fun k hk => by rw [cn3] at hk; have := cb2 k hk; omega
  have e3 : ∀ (r : Nat), entries (ofSure (lazyReg r : Sure S)) = [] := fun r => entries_ofSure _
  -- the formula part `q`
  obtain ⟨⟨Qt, Rq⟩, -, -, fq, cqE⟩ := Sq.run (sup := sup) (region := region)
    (L := ofSure (lazyReg (g2.re + 1))) (th := jmp0 g2.bo) hc.2 (by omega) d3 u3 cl3 cb3
    (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) rfl (by rw [e3]; simp) trivial
    (fun x hx => by
      simp only [ofSure, sure_mk, lazyReg, NMem] at hx; subst hx
      exact ⟨by omega, by rw [cn3]; exact nk _ (by omega)⟩)
    (fun e he => by rw [e3] at he; cases he) (by rw [e3]; simp) (fun e he => by rw [e3] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e3] at he; cases he) k4
  -- its `+past` behind `p`
  have tcase : (nexF' = nexF ∧ g5 = g4 ∧ ((∀ s, FitsS nexF.laz.sure s) ∨ TotalC lib P fb)) ∨
      (nexF' = ⟨Lazy.mk Sure.bunt [] ((g4.bo, Lazy.mk nexF.laz.sure nexF.laz.fork []) :: nexF.laz.bond),
          jmp0 g4.bo⟩ ∧
        g5 = (g4.emitted ⟨[], [], Termin.hop nexF.th⟩).tagged g4.bo region) := by
    rcases Kp with ⟨pp, Mp⟩ | hp
    · rw [pastL_pure _ _ pp, pure_apply] at k5
      simp only [Option.some.injEq, Prod.mk.injEq] at k5
      exact Or.inl ⟨k5.1.symm, k5.2.symm, Or.inr (totalC_of_minkEq Mp)⟩
    · rcases pastL_hinted hp k5 with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
      · exact Or.inl ⟨x1, x2, Or.inl (fun x => fitsS_trivial en es x)⟩
      · exact Or.inr ⟨x1, x2⟩
  have Rq' : RunOKLS (Map := Map) lib P fc (ofSure (lazyReg (g2.re + 1))) (jmp0 g2.bo) Qt false g3 g5 nexF' := by
    rcases tcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Rq
    · exact Rq.past (fun r hr => by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; omega)
        (fun e he => by rw [e3] at he; cases he) rfl (Rq.drop.trans d3) (Rq.grow.up u3) region
  have fq' : Flat nexF'.laz ∧ (∀ e ∈ entries nexF'.laz, Clean e.2.sure.ned) ∧ Clean nexF'.laz.sure.ned ∧
      ((∀ s, FitsS nexF'.laz.sure s) ∨ TotalC lib P fb) := by
    rcases tcase with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl⟩
    · exact ⟨fq, cqE, Sq.clean (L := ofSure (lazyReg (g2.re + 1))) trivial k4, hf⟩
    · have fl : Flat (Lazy.mk (Sure.bunt : Sure S) [] ((g4.bo, Lazy.mk nexF.laz.sure nexF.laz.fork []) ::
          nexF.laz.bond)) := flat_mk (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · show Lazy.mk nexF.laz.sure nexF.laz.fork [] = ofSure nexF.laz.sure
          rw [fq.1]; rfl
        · exact fq.2 e he)
      refine ⟨fl, fun e he => ?_, trivial, Or.inl (fun s => fitsS_bunt s)⟩
      rw [entries_flat fl] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Sq.clean (L := ofSure (lazyReg (g2.re + 1))) trivial k4
      · exact cqE e (by rw [entries_flat fq]; exact he)
  have d5 : g5.drop = false := Rq'.drop.trans d3
  have u5 : UpBelow g5 := Rq'.grow.up u3
  have cl5 : Clear g5 := cl3.growU Rq'.grow
  have cb5 : CondBelow g5 := Rq'.cfr.below cb3
  have r5 := Rq'.re
  have bo5 := Rq'.bo
  -- the subject part `p`
  obtain ⟨⟨Qh, Rp⟩, -, -, fp, cpE⟩ := Sp.run (sup := sup) (region := region)
    (L := ofSure (lazyReg g2.re)) (th := nexF'.th) hc.1 (by omega) d5 u5 cl5 cb5 Rq'.lo Rq'.hi
    (nextArgs_nil Rq'.ent rfl) (by rw [e3]; simp) trivial
    (fun x hx => by
      simp only [ofSure, sure_mk, lazyReg, NMem] at hx; subst hx
      exact ⟨by omega, by rw [Rq'.cfr.get_lt (by omega), cn3]; exact nk _ (Nat.le_refl _)⟩)
    (fun e he => by rw [e3] at he; cases he) (by rw [e3]; simp) (fun e he => by rw [e3] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e3] at he; cases he) k6
  -- the copy and the pair
  obtain ⟨n, g3', r, hcp, hM, rfl⟩ := copyL_flat' fp fq'.1 k7
  have nfit : ∀ (x y : Noun), ¬ (¬ FitsS (ofSure (lazyReg g2.re : Sure S)).sure x ∨
      ¬ FitsS (ofSure (lazyReg (g2.re + 1) : Sure S)).sure y) :=
    fun x y h => h.elim (fun h => h (fitsS_lazyReg _ x)) (fun h => h (fitsS_lazyReg _ y))
  have hrg : ∀ x, NMem (ofSure (pairReg g2.re : Sure S)).sure.ned x → x = g2.re ∨ x = g2.re + 1 := fun x hx => by
    simpa only [ofSure, sure_mk, pairReg, NMem] using hx
  obtain ⟨R, hth, eth, fR, cR, lR⟩ := pairLS_ok (Fin := fun _ _ _ x y r => r = Tone.zero (C x y))
    (FinB := fun _ _ x y r => r = Tone.zero (C x y)) (L := ofSure (pairReg g2.re)) (th := jmp0 g2.bo)
    (hed := ofSure (lazyReg g2.re)) (tel := ofSure (lazyReg (g2.re + 1))) (o := g2.bo) (PB := fun _ => [])
    (fun _ hm => minkF_consG hfb hm) (fun _ hh => mink_consG_bwd (ft := fc) hfb hh)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (flat_ofSure _) (by simp [ofSure])
    (fun x hx => by rcases hrg x hx with rfl | rfl <;> (rw [cn3]; exact nk _ (by omega)))
    (fun e he => by simp [ofSure] at he)
    ⟨⟨trivial, trivial, fun x a b => by simp only [NMem] at a b; omega⟩,
      fun x hx => by rcases hrg x hx with rfl | rfl <;> omega⟩
    (Ext.refl g3) (GrowU.refl g3) rfl cb3
    (fun r hr => by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; exact Or.inl (Or.inl rfl))
    (fun r hr => by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; exact Or.inl (Or.inr rfl))
    (fun r a b => by simp only [ofSure, sure_mk, lazyReg, NMem] at a b; omega)
    (Pref.refl g3) (fun _ _ => rfl) (flat_ofSure _) (flat_ofSure _) (fun e he => by simp [ofSure] at he)
    (fun e he => by simp [ofSure] at he) (fun e he => by simp [ofSure] at he) (by simp [ofSure]) (by simp [ofSure])
    (Ext.refl g3) (GrowU.refl g3) rfl rfl
    (Or.inl ⟨rfl, rfl, Or.inl (fun x => fitsS_lazyReg _ x)⟩) fq'.2.2.2
    Rq' Rp fq'.1 fp fq'.2.1 cpE fq'.2.2.1 (Sp.clean (L := ofSure (lazyReg g2.re)) trivial k6) hcp hM u3 d3
    (fun cf _ k h0 h1' => absurd h1' (by omega))
    (fun _ _ _ x y r hn hr => absurd hn (nfit x y)) (fun _ _ x y hn => absurd hn (nfit x y))
    (fun c hc σ Inv ν O n gul hS hF st' regs t tm x y n' r _ hI htr fx fy hx hy hr => by
      subst hr
      exact ⟨fun _ => ⟨st', regs, hI, Needs.le_refl _, ⟨hx, hy⟩, fun _ _ => rfl, rfl⟩,
        fun nf => absurd (fitsS_pairReg _ x y) nf⟩)
    (fun c hc σ Inv ν O gul hS hB st' regs t tm x y hI htr fx fy hx hy res _ =>
      ⟨_, rfl, ⟨fun _ => ⟨st', regs, hI, Needs.le_refl _, ⟨hx, hy⟩, fun _ _ => rfl, rfl⟩,
        fun nf => absurd (fitsS_pairReg _ x y) nf⟩⟩)
  -- the `%nok` block and `+kerf`
  have KL := kerfLB hk2 d0 hcb hu hta h1 h2 hsd hsl hlab' hnd hed
    (nokLB M hfb (by omega) c0 cb2 r3 b3 cn3 E3 G3 k3o R.toRunOKLB)
  refine ⟨⟨_, KL⟩, fun hm => ?_, ?_, fR, cR⟩
  · obtain ⟨e', he', ee⟩ := List.mem_map.mp hm
    have := lR e' he'
    have hthe : (pairRes n r nexF'.laz.bond nexS.laz.bond).th = n.th := rfl
    rw [hthe, eth] at ee
    simp only [jmp0] at ee
    omega
  · show g0.bo ≤ n.th.there
    omega


/-- **The indirect call whose parts meet `LOKS` meets `LOKS`** (`[2 p q]`,
the subject part's formula `fb` a cell, the subject part call-free with
`MinkEq` or hinted). -/
theorem lokS_indirect (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (M : MinkC2 lib P f fb fc) (hfb : ∃ a b, fb = C a b)
    (Kp : (p.pure = true ∧ MinkEq lib P fb p) ∨ hinted env.cod p = some true)
    (Sp : LOKS (S := S) (Map := Map) false lib env P fb p) (Sq : LOKS (S := S) (Map := Map) false lib env P fc q) :
    LOKS (S := S) (Map := Map) false lib env P f (Nomm.n2 p q Option.none) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl hlab hnd hed
    hfl hcs hce hr => ?_⟩
  · obtain ⟨nex0, g1', out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, k1, k2, k3, k4, k5, k6, k7⟩ :=
      runLC_n2_none hr
    have cq := Sq.clean (L := ofSure (lazyReg (g2.re + 1))) trivial k4
    have cq' : Clean nexF'.laz.sure.ned := by
      rcases Kp with ⟨pp, _⟩ | hh
      · rw [pastL_pure _ _ pp, pure_apply] at k5
        simp only [Option.some.injEq, Prod.mk.injEq] at k5
        obtain ⟨rfl, rfl⟩ := k5
        exact cq
      · rcases pastL_hinted hh k5 with ⟨x1, x2, _⟩ | ⟨x1, x2⟩
        · subst x1 x2; exact cq
        · subst x1 x2; trivial
    exact clean_copyL k7 (Sp.clean (L := ofSure (lazyReg g2.re)) trivial k6) cq'
  · obtain ⟨A, B, C', D, E⟩ := lokS_indirect_run lib env M hfb Kp Sp Sq hcount b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl
      hlab hnd hed hfl hcs hce hr
    exact ⟨A, B, Or.inr C', D, E⟩

end Comp
end SkaModel
end Formalization
