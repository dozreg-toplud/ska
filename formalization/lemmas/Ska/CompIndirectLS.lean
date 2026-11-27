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

end Comp
end SkaModel
end Formalization
