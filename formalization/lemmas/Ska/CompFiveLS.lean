import lemmas.Ska.CompThreeLS

/-!
# The equality test `[5 p q]`: the `+mink` side

README Gaps 12.29 (next).  `[5 p q]` compiles as the indirect call does:
the inner pair `[p q]` under `%next (pairReg rp)` and a block behind it, here
`[eqq rp rq z o']` (with `+forl` in front, as `[3 p]`'s `[clq arg z o']`), or
`[equ rp rq] hop th` under a goal that asks nothing.  This file has the
`+mink` side.

* `MinkC5`: `+mink` on `f` is the equality test of `+mink` on `fb` and `fc`
  (`MinkC2` with `eqCode` in place of the run of the products).
* `minkC5_five`: `[5 b c]` itself.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- **`+mink` on `f` is the equality test of `+mink` on `fb` and `fc`**:
`fb` runs, then `fc`, with less fuel, and the product is `eqCode` of theirs
(`fwd`); backward, runs of the parts give one of `f` (`bwd`). -/
structure MinkC5 (lib : Lib) (P : Noun → Prop) (f fb fc : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    ∃ n', n' < n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧
      (((∀ q, rb ≠ Tone.zero q) ∧ r = rb) ∨ ∃ x, rb = Tone.zero x ∧ ∃ rc, minkF lib gul n' tm s fc = some rc ∧
        (((∀ q, rc ≠ Tone.zero q) ∧ r = rc) ∨ ∃ y, rc = Tone.zero y ∧ r = Tone.zero (eqCode x y)))
  bwd : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb →
    ((∀ q, rb ≠ Tone.zero q) → Mink lib gul tm s f rb) ∧
    ∀ x rc, rb = Tone.zero x → Mink lib gul tm s fc rc →
      ((∀ q, rc ≠ Tone.zero q) → Mink lib gul tm s f rc) ∧
      ∀ y, rc = Tone.zero y → Mink lib gul tm s f (Tone.zero (eqCode x y))

/-- `[5 b c]` itself. -/
theorem minkC5_five (lib : Lib) (P : Noun → Prop) (b c : Noun) : MinkC5 lib P (n3 (A 5) b c) b c where
  fwd := fun {s gul n tm r} _ h => by
    cases n with
    | zero => simp [minkF] at h
    | succ n' =>
      rw [minkF_succ_eq] at h
      simp only [n3, minkStep] at h
      refine ⟨n', Nat.lt_succ_self n', ?_⟩
      cases eb : minkF lib gul n' tm s b with
      | none => rw [eb] at h; simp [tbind] at h
      | some rb =>
        rw [eb] at h
        refine ⟨rb, rfl, ?_⟩
        cases rb with
        | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
        | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
        | zero x =>
          refine Or.inr ⟨x, rfl, ?_⟩
          simp only [tbind_zero] at h
          cases ec : minkF lib gul n' tm s c with
          | none => rw [ec] at h; simp [tbind] at h
          | some rc =>
            rw [ec] at h
            refine ⟨rc, rfl, ?_⟩
            cases rc with
            | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
            | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
            | zero y =>
              simp only [tbind_zero, Option.some.injEq] at h
              exact Or.inr ⟨y, rfl, h.symm⟩
  bwd := fun {s gul tm rb} _ hb => by
    obtain ⟨n1, e1⟩ := hb
    refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun x rc ex hc => ?_⟩
    · rw [minkF_succ_eq]; simp only [n3, minkStep]; rw [e1]
      cases rb with
      | zero q => exact absurd rfl (hn q)
      | one _ => rfl
      | two _ => rfl
    · subst ex
      obtain ⟨n2, e2⟩ := hc
      have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s b _ e1
      have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s c _ e2
      refine ⟨fun hn => ⟨max n1 n2 + 1, ?_⟩, fun y ey => ?_⟩
      · rw [minkF_succ_eq]; simp only [n3, minkStep]; rw [e1', tbind_zero, e2']
        cases rc with
        | zero q => exact absurd rfl (hn q)
        | one _ => rfl
        | two _ => rfl
      · subst ey
        exact ⟨max n1 n2 + 1, by rw [minkF_succ_eq]; simp only [n3, minkStep]; rw [e1', tbind_zero, e2',
          tbind_zero]⟩

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Small facts -/

/-- `+mink` on `[fb fc]` with `MinkC5` (`consMink_cases`). -/
theorem consMink_cases5 {lib : Lib} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC5 lib P f fb fc)
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

/-- `GrowU` reads the blocks, `bo` and `drop` of its first state only. -/
theorem growU_congrL {g g' h : Gen Map} (hb : g'.bo = g.bo) (hk : g'.blocks = g.blocks) (hd : g'.drop = g.drop)
    (G : GrowU g h) : GrowU g' h := by
  obtain ⟨a, b, c, d⟩ := G
  refine ⟨by rw [hb]; exact a, by rw [hd]; exact b, fun k bl hk' hg => ?_, fun k b' hb' => ?_⟩
  · rw [hb] at hk'; rw [hk] at hg; exact c k bl hk' hg
  · rcases d k b' hb' with ⟨b0, h0, e1, e2⟩ | ⟨l1, l2, l3⟩
    · exact Or.inl ⟨b0, by rw [hk]; exact h0, e1, e2⟩
    · exact Or.inr ⟨by rw [hb]; exact l1, l2, l3⟩

/-- `CondFresh` from a state with fewer registers and the same `cond`. -/
theorem condFresh_low {g gL g' : Gen Map} (h : CondFresh g g') (hc : gL.cond = g.cond) (hl : gL.re ≤ g.re) :
    CondFresh gL g' :=
  ⟨Nat.le_trans hl h.1, fun k => by rw [hc]; exact (h.2 k).imp id (fun ⟨a, b⟩ => ⟨Nat.le_trans hl a, b⟩)⟩

/-- **`CollPre` from a state with more registers** holds from the state
before them (`+collapse-lazy-atom` run after the two `re`s of `%5`). -/
theorem CollPre.lower {L : Lazy S} {th : Jmp} {g0 g2 : Gen Map} {r there k : Nat} (hk : g0.re ≤ k)
    (CP : CollPre L th ({ g0 with re := k } : Gen Map) g2 r there) : CollPre L th g0 g2 r there where
  args := CP.args
  drop := CP.drop
  le := Nat.le_trans hk CP.le
  bo1 := CP.bo1
  grow := (grow_reg g0 k).trans CP.grow
  keeps := (keeps_reg g0 k hk).trans CP.keeps
  pfor := (ProxyFor.of_eq (r := r) (g := g0) (g' := { g0 with re := k }) hk rfl).trans CP.pfor
  rlt := CP.rlt
  rkey := CP.rkey
  rreg := CP.rreg.imp id (fun h => Nat.le_trans hk h)
  other := CP.other
  at_ := CP.at_
  shape := CP.shape

/-! ## `+collapse-lazy-atom` in front of a run from a state with fewer registers -/

/-- **`collLS` with the rest's run from a state `gL` with fewer registers**
than the collapse's end `g2` (its blocks, `bo` and `drop`, at least the
registers of `g0`): the kept registers of the rest are those below `gL.re`.
`[5 p q]` takes `gL` with the registers of `g0`, as its `r-p`, `r-q` are
allocated before the collapse and written by the pair. -/
theorem collLSk {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {g0 g2 g1 gL : Gen Map}
    {r there : Nat} {nex : NextL S} (CP : CollPre L th g0 g2 r there)
    (hu : UpBelow g0) (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re)
    (hec : ∀ e ∈ entries L, ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfr : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → g0.re ≤ x)
    (hLbo : gL.bo = g2.bo) (hLbl : gL.blocks = g2.blocks) (hLd : gL.drop = g2.drop) (hL0 : g0.re ≤ gL.re)
    (hre : g2.re ≤ g1.re) (hcfr : CondFresh g2 g1)
    (R : RunOKLB (Map := Map) lib N P f (ofSure (lazyReg r)) (jmp0 there) atomWit false gL g1 nex) :
    RunOKLS (Map := Map) lib N P f L th (fourWit L r) true g0 g1 nex := by
  have e2 : entries (ofSure (lazyReg r : Sure S)) = [] := entries_ofSure _
  have bl : g2.bo ≤ g1.bo := by rw [← hLbo]; exact R.bo
  have Re : Ext g2 g1 := ⟨hre, bl, by rw [R.drop, hLd], fun o ho => by
    rw [R.keep o (by rw [hLbo]; exact ho) (by rw [e2]; simp), hLbl]⟩
  have rl := hre
  have rL := R.re
  have c1 := CP.le
  have c2 := CP.bo1
  have rlt := CP.rlt
  have hth : th.args = [] := CP.args
  have lab' : ∀ e ∈ entries nex.laz, g2.bo ≤ e.1 := fun e he =>
    (R.labs e he).1.elim (fun h => by rw [e2] at h; cases h) (fun h => by rw [← hLbo]; exact h.1)
  have hcf2 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun cf hcf x hx =>
    (hcf x (by omega)).trans (hcfr.get_lt hx)
  have ur : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      unproxy cf r = r := fun cf hcf => unproxy_none (by rw [hcf2 cf hcf r rlt]; exact CP.rkey)
  have rne : ∀ x, (x < g0.re ∨ g1.re ≤ x) → ¬ NMem L.sure.ned x → x ≠ r := fun x hx hn e => by
    subst e
    rcases CP.rreg with h | h
    · exact hn h
    · rcases hx with hx | hx <;> omega
  -- the conversion of the rest's goal into the goal's
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
      Forall2 (FrameRel lib (ν st)) t tm → ∀ rt,
      GoalSemCMD lib O c gul Inv ν (fun x => (x < gL.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg r : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg r : Sure S)).sure (jmp0 there) (atomWit s) rt →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
        L.sure th (fourWit L r s) rt := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rt G
    cases rt with
    | one q => exact G
    | two t' => exact G
    | zero p =>
      obtain ⟨st1, R1, dd, w, hI1, hν1, ⟨⟨m, rfl⟩, _⟩, hp1, _, k1, e1⟩ := G.1 (fitsS_lazyReg _ _)
      have hr1 : SkaModel.read r R1 = some (A m) := hp1
      have kk : ∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) →
          SkaModel.read x R1 = SkaModel.read x regs := fun x hx =>
        k1 x ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun e =>
          rne x (hx.1.imp id (fun h => hned x h)) hx.2 e⟩
      rcases CP.shape with ⟨eth, -, hfa, hfit⟩ | ⟨eth, ebo, hnf, F, hF, hPF⟩
      · -- every atom fits: the collapse hops to `th`
        subst eth
        refine ⟨fun _ => ?_, fun nf => absurd (hfa m) nf⟩
        by_cases hin : NMem L.sure.ned r
        · exact ⟨st1, R1, Need.none, A 0, hI1, hν1, ⟨⟨m, rfl⟩, Or.inl ⟨hin, rfl⟩⟩, (hfit R1 m hr1).1, trivial, kk,
            by rw [e1, jmp0_of_args hth]⟩
        · exact ⟨st1, R1, Need.this r, A m, hI1, hν1, ⟨⟨m, rfl⟩, Or.inr ⟨hin, rfl, rfl⟩⟩, (hfit R1 m hr1).1, hr1,
            kk, by rw [e1, jmp0_of_args hth]⟩
      · -- no atom fits: the collapse hops to its block `[%bom ~]`
        refine ⟨fun hf => absurd hf (hnf m), fun _ => ?_⟩
        subst eth
        have hcb0 : HoonMap.get c.blocks g0.bo =
            some ⟨[], F.map (renPole (unproxy cf)), Termin.bom Option.none⟩ := by
          rw [(ag st1).1 g0.bo (Nat.le_refl _) (by omega) (fun hm => by
            obtain ⟨e, he', e1⟩ := List.mem_map.mp hm; have := lab' e he'; omega), Re.2.2.2 _ (by omega), hF]
          simp [unproxyBlob, renBlob, renFin]
        have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st1) R1 t _ _ hcb0
        obtain ⟨S1, S2⟩ := hPF (unproxy cf) (ur cf hcf)
          (fun x hx => by simp only [NMem] at hx; rw [hx]; exact ur cf hcf)
          (fun x hx => by simp only [unproxy, hcf2 cf hcf x hx]) lib σ O c gul st1 t R1 m hr1
        refine ⟨Tone.two t, st1, hI1, hν1, ?_, ToneRel.two (frames_mono hν1 htr)⟩
        rw [e1, hj, ← List.append_nil (F.map (renPole (unproxy cf)))]
        by_cases fT : FitsS (⟨Need.this r, L.sure.lok⟩ : Sure S) (A m)
        · obtain ⟨R', hr', -, -⟩ := S1 fT
          rw [hr', execBlob_bom']
        · exact S2 fT [] _
  have agR : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun), (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g1 nex.laz s0 s) →
      ∀ st' : σ, AgreeLB lib O c gul st' t cf ned gL g1 nex.laz s0 s :=
    fun cf c ned σ O gul t s0 s ag st' => agreeLB_mono (ag st') (by omega)
  -- the fronts at the state level: the collapse's ops read `r`
  have FS : FrontsS (Map := Map) (fourWit L r) true g0 g1 L nex := by
    intro e he
    obtain ⟨A0, hA, hP⟩ := CP.at_ e he
    have hlt := hlab e he
    refine ⟨A0, fun B fin hb => by rw [Re.2.2.2 _ (by omega)]; exact hA B fin hb,
      fun cf hcf => Or.inr ⟨fun hm => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; omega, ?_⟩⟩
    refine ⟨fun x hx => by simp [Sure.bunt, NMem] at hx, fun s v d w _ x _ hx => by simp [Sure.bunt, NMem] at hx,
      fun s v d w _ _ => fitsS_bunt s, fun lib σ O c gul st t R0 s v d w hq _ hd hE => ?_⟩
    rw [gsE_true] at hE
    obtain ⟨⟨m, rfl⟩, hw⟩ := hq
    have hr0 : SkaModel.read r R0 = some (A m) := by
      rcases hw with ⟨hin, rfl⟩ | ⟨_, rfl, rfl⟩
      · exact holdsN_atom_mem hE hin
      · exact hd
    obtain ⟨S1, S2⟩ := hP (unproxy cf) (ur cf hcf) (fun x hx => unproxy_none (by
        have hx1 := hec e he x hx
        rw [hcf2 cf hcf x (by omega), CP.pfor.1.get_lt hx1.1]; exact hx1.2))
      (fun x hx => by simp only [unproxy, hcf2 cf hcf x hx]) lib σ O c gul st t R0 m hr0
    refine ⟨fun fv => ?_, S2⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 fv
    exact ⟨R2, r2, hh2, fun x _ hn' => k2 x hn'⟩
  have dreg : ∀ s v d w x, fourWit L r s v d w → NMem d x → g0.re ≤ x ∧ x < g1.re := fun s v d w x hq hx => by
    obtain ⟨_, ⟨_, rfl⟩ | ⟨hin, rfl, _⟩⟩ := hq
    · exact hx.elim
    · simp only [NMem] at hx; subst hx; exact ⟨CP.rreg.resolve_left hin, by omega⟩
  have eup : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → x < g1.re := fun e he x hx => by
    rcases (R.eregs e he).2 x hx with ⟨e0, h0, _⟩ | h | h
    · rw [e2] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; omega
    · exact h.2
  refine ⟨⟨by omega, by omega, Re.2.2.1.trans CP.drop, fun o ho hn' => by rw [Re.2.2.2 o (by omega), CP.other o ho hn'],
    (CP.grow.toU hu).trans (growU_congrL hLbo.symm hLbl.symm hLd.symm R.grow), CP.pfor.1.trans hcfr, R.lo, R.hi, ?_, fun x hx => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun x hx => Or.inr (Or.inr ⟨by have := hfr e he x hx; omega, eup e he x hx⟩)⟩,
    fun e he => ⟨Or.inr ⟨by have := lab' e he; omega, (R.labs e he).1.elim (fun h => by rw [e2] at h; cases h)
      (fun h => h.2)⟩, by obtain ⟨B, th', hb⟩ := (R.labs e he).2; exact ⟨B, th', hb⟩⟩, R.nodup,
    dreg, fun s hs hf => ?_, R.ncond, R.econd,
    FS.toFront (by omega) hsl (fun e he y hy hm => by
      rw [gsE_true] at hy; have := hfr e he y hm; have := hsl y hy; omega) dreg, ?_, ?_⟩, FS⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rcases CP.shape with ⟨eth, -⟩ | ⟨eth, ebo, -, F, hF, -⟩
      · exact Or.inr (by rw [e, eth]; exact jmp0_of_args hth)
      · rw [e, eth]; exact Or.inl ⟨_, (Re.2.2.2 g0.bo (by omega)).trans hF, rfl, rfl⟩
  · rcases R.regs x hx with h | h
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; subst h
      rcases CP.rreg with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · obtain ⟨N1, N2⟩ := R.nec s hs hf
    have bad : ∀ {tm : Trace} {rt : Tone}, BadC (CGoal.next (lazyReg r : Sure S) (jmp0 there)) tm rt →
        BadC (CGoal.next L.sure th) tm rt := fun h => by
      rcases h with e | ⟨q, _, nq⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg _ q) nq
    exact ⟨fun gul n tm rt hm => bad (N1 gul n tm rt hm), fun gul tm => by
      obtain ⟨rt, hm, hb⟩ := N2 gul tm; exact ⟨rt, hm, bad hb⟩⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s rt hI htr hs hm ag hned regs hh hn
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rt
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s rt hI htr hs hm (agR cf c ned σ O gul t s0 s ag) hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rt, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs (agR cf c ned σ O gul t s0 s ag)
      hned regs hh hn res hres
    exact ⟨rt, hm, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rt G⟩

/-! ## `+forl` and the `eqq` block behind the pair -/

/-- **`+forl` and the block `[eqq a a+1 z o']` behind the pair's run**
(`clqLB` with `nokLB`'s pair): `RunOKLB` of the pair for `[fb fc]` under
`%next [this a this a+1] (jmp0 eqq)`, from the state with the blocks of
`+forl r there` and the `eqq` block made, is `RunOKLB` of `[5 fb fc]` under
`%next (lazy-from-reg r) (jmp0 there)` from a state `gL` with the blocks of
the state `g2` before `+forl` and at most the registers below `a` (so the
kept registers do not have `a`, `a+1`, which the pair writes). -/
theorem eqqLB {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC5 lib P f fb fc)
    (hfb : ∃ a b, fb = C a b)
    {g2 g3 gE g' gL : Gen Map} {nex : NextL S} {r there z o' a : Nat} {Q : Wit} {x : Bool}
    (hr : r < g2.re) (hrk : HoonMap.get g2.cond r = Option.none) (cb2 : CondBelow g2) (d2 : g2.drop = false)
    (ha : a + 2 ≤ g2.re) (hak : HoonMap.get g2.cond a = Option.none)
    (hak1 : HoonMap.get g2.cond (a + 1) = Option.none)
    (hLre : gL.re ≤ a) (hLbo : gL.bo = g2.bo) (hLbl : gL.blocks = g2.blocks) (hLc : gL.cond = g2.cond)
    (hLd : gL.drop = g2.drop)
    (hF : (forl r there : CM Map (Nat × Nat)) g2 = some ((z, o'), g3)) (c3 : g3.cond = g2.cond)
    (rE : gE.re = g3.re) (bE : gE.bo = g3.bo + 1) (cE : gE.cond = g3.cond) (E3 : Ext g3 gE)
    (G : GrowU g2 gE) (hth : 1 ≤ there ∧ there < g2.bo)
    (kc : HoonMap.get gE.blocks g3.bo = some ⟨[], [], Termin.eqq a (a + 1) (jmp0 z) (jmp0 o')⟩)
    (R : RunOKLB (Map := Map) lib N P (C fb fc) (ofSure (pairReg a)) (jmp0 g3.bo) Q x gE g' nex) :
    RunOKLB (Map := Map) lib N P f (ofSure (lazyReg r)) (jmp0 there) atomWit false gL g' nex := by
  obtain ⟨E23, r3, b3, FS⟩ := forl_ok hF hr
  have E2E := E23.trans E3
  have e0 : entries (ofSure (pairReg a : Sure S)) = [] := entries_ofSure _
  have e1 : entries (ofSure (lazyReg r : Sure S)) = [] := entries_ofSure _
  have rl := R.re
  have bl := R.bo
  have nk : ∀ x, g2.re ≤ x → HoonMap.get g2.cond x = Option.none := fun x hx => condBelow_none cb2 hx
  have kN : HoonMap.get g'.blocks g3.bo = some ⟨[], [], Termin.eqq a (a + 1) (jmp0 z) (jmp0 o')⟩ := by
    rw [R.keep _ (by omega) (by rw [e0]; simp)]; exact kc
  have lab' : ∀ e ∈ entries nex.laz, gE.bo ≤ e.1 := fun e he => by
    rcases (R.labs e he).1 with h | h
    · rw [e0] at h; cases h
    · exact h.1
  -- the blocks of `+forl` and the `eqq` block in any code that agrees with the run
  have hbN : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (ned : Need) (s0 s : Noun),
      AgreeLB lib O c gul st t cf ned gL g' nex.laz s0 s →
      Agree c g2 g3 ∧ HoonMap.get c.blocks g3.bo = some ⟨[], [], Termin.eqq a (a + 1) (jmp0 z) (jmp0 o')⟩ := by
    intro cf hcf c σ O gul st t ned s0 s ag
    have hc : ∀ x, x < gE.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun x hx => by
      rw [hcf x (by omega), R.cfr.get_lt hx, cE, c3]
    refine ⟨fun o h0 h1 => ?_, ?_⟩
    · rw [ag.1 o (by omega) (by omega) (fun hm => by
        obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega),
        R.keep o (by omega) (by rw [e0]; simp), E3.2.2.2 o h1]
      exact forl_fix hF d2 (by rw [hc _ (by omega)]; exact hrk) (by rw [hc _ (by omega)]; exact nk _ (Nat.le_refl _))
        (by rw [hc _ (by omega)]; exact nk _ (by omega)) o h0 h1
    · rw [ag.1 g3.bo (by omega) (by omega) (fun hm => by
        obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega), kN]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin,
        renJmp_nil _ (show (jmp0 z).args = [] from rfl), renJmp_nil _ (show (jmp0 o').args = [] from rfl)]
      rw [unproxy_none (by rw [hc _ (by omega)]; exact hak), unproxy_none (by rw [hc _ (by omega)]; exact hak1)]
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ z',
      ((z' < gL.re ∨ NMem ned z') ∧ ¬ NMem (lazyReg r : Sure S).ned z') →
      z' ≠ r ∧ z' ≠ g2.re ∧ z' ≠ g2.re + 1 ∧
      ((z' < gE.re ∨ NMem ned z') ∧ ¬ NMem (ofSure (pairReg a : Sure S)).sure.ned z') := fun ned hned z' hz => by
    have nr : z' ≠ r := fun e => hz.2 (by subst e; simp [lazyReg, NMem])
    refine ⟨nr, ?_, ?_, hz.1.imp (fun h => by omega) id, fun hm => ?_⟩
    · rcases hz.1 with h | h
      · omega
      · have := hned z' h; omega
    · rcases hz.1 with h | h
      · omega
      · have := hned z' h; omega
    · simp only [ofSure, sure_mk, pairReg, NMem] at hm
      rcases hz.1 with h | h
      · omega
      · have := hned z' h; omega
  -- the product of the pair through the `eqq` block and `+forl`
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned gL g' nex.laz s0 s) → (∀ x, NMem ned x → g'.re ≤ x) →
      ∀ u v,
      GoalSemCMD lib O c gul Inv ν (fun x => (x < gE.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (pairReg a : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (pairReg a : Sure S)).sure (jmp0 g3.bo) (Q s) (Tone.zero (C u v)) →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < gL.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg r : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg r : Sure S)).sure (jmp0 there) (atomWit s) (Tone.zero (eqCode u v)) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned u v G
    obtain ⟨hag, hb⟩ := hbN cf hcf c σ O gul st t ned s0 s (ag st)
    obtain ⟨st1, R1, d, w, hI1, hν1, _, hh1, _, k1, e3⟩ := G.1 (fitsS_pairReg a u v)
    have hx : SkaModel.read a R1 = some u := hh1.1
    have hy : SkaModel.read (a + 1) R1 = some v := hh1.2
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st1) R1 t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    have F' := FS d2 c hag lib σ O st1 R1 t gul
    by_cases e : u = v
    · rw [if_pos e] at hj
      simp only [eqCode, if_pos e]
      refine ⟨fun _ => ⟨st1, store r (A 0) (store g2.re (A 0) R1), Need.none, A 0, hI1, hν1, ⟨⟨0, rfl⟩, rfl⟩,
        read_store_eq _ _ _, trivial, fun z' hz => ?_, e3.trans (hj.trans F'.1)⟩,
        fun nf => absurd (fitsS_lazyReg _ _) nf⟩
      obtain ⟨n1, n2, -, k⟩ := hK ned hned z' hz
      rw [read_store_ne n1, read_store_ne n2]
      exact k1 z' k
    · rw [if_neg e] at hj
      simp only [eqCode, if_neg e]
      refine ⟨fun _ => ⟨st1, store r (A 1) (store (g2.re + 1) (A 1) R1), Need.none, A 0, hI1, hν1,
        ⟨⟨1, rfl⟩, rfl⟩, read_store_eq _ _ _, trivial, fun z' hz => ?_, e3.trans (hj.trans F'.2)⟩,
        fun nf => absurd (fitsS_lazyReg _ _) nf⟩
      obtain ⟨n1, -, n3, k⟩ := hK ned hned z' hz
      rw [read_store_ne n1, read_store_ne n3]
      exact k1 z' k
  have GL : GrowU gL gE := growU_congrL hLbo hLbl hLd G
  refine ⟨by omega, by omega, R.drop.trans (E2E.2.2.1.trans hLd.symm), fun o ho hn => ?_, GL.trans R.grow,
    condFresh_low ((condFresh_of_eq (by omega) (cE.trans c3)).trans R.cfr) hLc (by omega), R.lo, R.hi, ?_,
    fun r' hr' => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r' hr' => ?_⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).1.elim (fun h => (by rw [e0] at h; cases h))
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup,
    fun s v d w r' hq hr' => (by obtain ⟨_, rfl⟩ := hq; exact hr'.elim),
    fun s hs hf => ?_, R.ncond, R.econd, fun e he => (by rw [e1] at he; cases he), ?_, ?_⟩
  · rw [R.keep o (by omega) (by rw [e0]; simp), E2E.2.2.2 o (by omega), hLbl]
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, kN, rfl, rfl⟩
  · rcases R.regs r' hr' with h | h
    · simp only [ofSure, sure_mk, pairReg, NMem] at h
      exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · rcases (R.eregs e he).2 r' hr' with ⟨e0', h0, _⟩ | h | h
    · rw [e0] at h0; cases h0
    · simp only [ofSure, sure_mk, pairReg, NMem] at h
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · have Nc := R.nec s hs hf
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, e1', H⟩ := M.fwd hs hm
      rcases H with ⟨hnz, rfl⟩ | ⟨u, rfl, rc, e2, H⟩
      · exact badC_nz hnz (Nc.1 gul _ tm _ ((consStep hfb e1').1 hnz))
      · rcases H with ⟨hnz, rfl⟩ | ⟨v, rfl, h3⟩
        · exact badC_nz hnz (Nc.1 gul _ tm _ (((consStep hfb e1').2 u rfl _ e2).1 hnz))
        · rcases Nc.1 gul _ tm _ (((consStep hfb e1').2 u rfl _ e2).2 v rfl) with e | ⟨p, e, hp⟩
          · cases e
          · cases e; exact absurd (fitsS_pairReg a u v) hp
    · obtain ⟨r, hm, hb⟩ := Nc.2 gul tm
      rcases consMink_cases5 M hfb hs hm with ⟨hnz, hmf⟩ | ⟨u, v, rfl, _, _⟩
      · exact ⟨r, hmf, badC_nz hnz hb⟩
      · rcases hb with e | ⟨p, e, hp⟩
        · cases e
        · cases e; exact absurd (fitsS_pairReg a u v) hp
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r' hI htr hs hm ag hned regs hh hn
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned gE g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨n', hn', rb, e1', H⟩ := M.fwd hs hm
    have hF' := oracleFwd_le hF (show n' + 1 ≤ n by omega)
    have Gp : ∀ r', minkF lib gul (n' + 1) tm s (C fb fc) = some r' → _ := fun r' e =>
      R.sem cf hcf c ned σ Inv ν O (n' + 1) gul hN hS hF' st t tm s0 s r' hI htr hs e ag3 hned regs hh hn
    rcases H with ⟨hnz, rfl⟩ | ⟨u, rfl, rc, e2, H⟩
    · exact goalSemCMD_nz hnz (Gp _ ((consStep hfb e1').1 hnz))
    · rcases H with ⟨hnz, rfl⟩ | ⟨v, rfl, rfl⟩
      · exact goalSemCMD_nz hnz (Gp _ (((consStep hfb e1').2 u rfl _ e2).1 hnz))
      · exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned u v
          (Gp _ (((consStep hfb e1').2 u rfl _ e2).2 v rfl))
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned gE g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨rp, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag3 hned regs hh hn
      res hres
    rcases consMink_cases5 M hfb hs hm with ⟨hnz, hmf⟩ | ⟨u, v, rfl, hu, hv⟩
    · exact ⟨rp, hmf, goalSemCMD_nz hnz G⟩
    · exact ⟨_, ((M.bwd hs hu).2 u _ rfl hv).2 v rfl,
        conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned u v G⟩

/-! ## The pair -/

/-- **The pair `[p q]` of `[2 p q]` and `[5 p q]` under `%next [this a
this a+1] (jmp0 o)`** (the pair part of `lokS_indirect_runF`): the run of
`q` under `%next (lazy-from-reg a+1) (jmp0 o)`, `+past` behind `p`, the run
of `p` under `%next (lazy-from-reg a)`, and `+copy` give `RunOKLS` of the
pair for `[fb fc]` with the flag `false`, the jump a new block at none of
the result's entries, the result flat with clean entries. -/
theorem pairRun_ok (lib : Lib) {N : Needs} (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {fb fc : Noun}
    (hfb : ∃ a b, fb = C a b)
    (Kp : (p.pure = true ∧ MinkEq lib P fb p) ∨ hinted env.cod p = some true)
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fb p) (Sq : LOKSF (S := S) (Map := Map) lib N env P fc q)
    {sup : Option Nomm} {region : List Nat} {g3 g4 g5 g6 g' : Gen Map} {nexF nexF' nexS nex : NextL S} {a o : Nat}
    (hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255) (ho1 : 1 ≤ o) (ho : o < g3.bo) (d3 : g3.drop = false)
    (u3 : UpBelow g3) (cl3 : Clear g3) (cb3 : CondBelow g3) (ha : a + 2 ≤ g3.re)
    (hca : HoonMap.get g3.cond a = Option.none) (hca1 : HoonMap.get g3.cond (a + 1) = Option.none)
    (k4 : runLC env sup q (CGoalL.next (ofSure (lazyReg (a + 1))) (jmp0 o)) region g3 = some (nexF, g4))
    (k5 : pastL env.cod nexF p region g4 = some (nexF', g5))
    (k6 : runLC env sup p (CGoalL.next (ofSure (lazyReg a)) nexF'.th) region g5 = some (nexS, g6))
    (k7 : copyL nexS nexF'.laz g6 = some (nex, g')) :
    (∃ Q, RunOKLS (Map := Map) lib N P (C fb fc) (ofSure (pairReg a)) (jmp0 o) Q false g3 g' nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧ g3.bo ≤ nex.th.there ∧ Flat nex.laz ∧
      (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  have e3 : ∀ (r : Nat), entries (ofSure (lazyReg r : Sure S)) = [] := fun r => entries_ofSure _
  -- the formula part `q`
  obtain ⟨⟨Qt, Rq⟩, -, -, fq, cqE⟩ := Sq.run (sup := sup) (region := region)
    (L := ofSure (lazyReg (a + 1))) (th := jmp0 o) (Or.inr (entries_ofSure _)) hc.2 (by omega) d3 u3 cl3 cb3
    (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) rfl (by rw [e3]; simp) trivial
    (fun x hx => by
      simp only [ofSure, sure_mk, lazyReg, NMem] at hx; subst hx
      exact ⟨by omega, hca1⟩)
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
  have Rq' : RunOKLS (Map := Map) lib N P fc (ofSure (lazyReg (a + 1))) (jmp0 o) Qt false g3 g5 nexF' := by
    rcases tcase with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Rq
    · exact Rq.past (fun r hr => by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; omega)
        (fun e he => by rw [e3] at he; cases he) rfl (Rq.drop.trans d3) (Rq.grow.up u3) region
  have fq' : Flat nexF'.laz ∧ (∀ e ∈ entries nexF'.laz, Clean e.2.sure.ned) ∧ Clean nexF'.laz.sure.ned ∧
      ((∀ s, FitsS nexF'.laz.sure s) ∨ TotalC lib P fb) := by
    rcases tcase with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl⟩
    · exact ⟨fq, cqE, Sq.clean (L := ofSure (lazyReg (a + 1))) trivial k4, hf⟩
    · have fl : Flat (Lazy.mk (Sure.bunt : Sure S) [] ((g4.bo, Lazy.mk nexF.laz.sure nexF.laz.fork []) ::
          nexF.laz.bond)) := flat_mk (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · show Lazy.mk nexF.laz.sure nexF.laz.fork [] = ofSure nexF.laz.sure
          rw [fq.1]; rfl
        · exact fq.2 e he)
      refine ⟨fl, fun e he => ?_, trivial, Or.inl (fun s => fitsS_bunt s)⟩
      rw [entries_flat fl] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Sq.clean (L := ofSure (lazyReg (a + 1))) trivial k4
      · exact cqE e (by rw [entries_flat fq]; exact he)
  have d5 : g5.drop = false := Rq'.drop.trans d3
  have u5 : UpBelow g5 := Rq'.grow.up u3
  have cl5 : Clear g5 := cl3.growU Rq'.grow
  have cb5 : CondBelow g5 := Rq'.cfr.below cb3
  have r5 := Rq'.re
  have bo5 := Rq'.bo
  -- the subject part `p`
  obtain ⟨⟨Qh, Rp⟩, -, -, fp, cpE⟩ := Sp.run (sup := sup) (region := region)
    (L := ofSure (lazyReg a)) (th := nexF'.th) (Or.inr (entries_ofSure _)) hc.1 (by omega) d5 u5 cl5 cb5 Rq'.lo Rq'.hi
    (nextArgs_nil Rq'.ent rfl) (by rw [e3]; simp) trivial
    (fun x hx => by
      simp only [ofSure, sure_mk, lazyReg, NMem] at hx; subst hx
      exact ⟨by omega, by rw [Rq'.cfr.get_lt (by omega)]; exact hca⟩)
    (fun e he => by rw [e3] at he; cases he) (by rw [e3]; simp) (fun e he => by rw [e3] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e3] at he; cases he) k6
  -- the copy and the pair
  obtain ⟨n, g3', r, hcp, hM, rfl⟩ := copyL_flat' fp fq'.1 k7
  have nfit : ∀ (x y : Noun), ¬ (¬ FitsS (ofSure (lazyReg a : Sure S)).sure x ∨
      ¬ FitsS (ofSure (lazyReg (a + 1) : Sure S)).sure y) :=
    fun x y h => h.elim (fun h => h (fitsS_lazyReg _ x)) (fun h => h (fitsS_lazyReg _ y))
  have hrg : ∀ x, NMem (ofSure (pairReg a : Sure S)).sure.ned x → x = a ∨ x = a + 1 := fun x hx => by
    simpa only [ofSure, sure_mk, pairReg, NMem] using hx
  obtain ⟨R, hth, eth, fR, cR, lR⟩ := pairLS_ok (Fin := fun _ _ _ x y r => r = Tone.zero (C x y))
    (FinB := fun _ _ x y r => r = Tone.zero (C x y)) (L := ofSure (pairReg a)) (th := jmp0 o)
    (hed := ofSure (lazyReg a)) (tel := ofSure (lazyReg (a + 1))) (o := o) (PB := fun _ => [])
    (fun _ hm => minkF_consG hfb hm) (fun _ hh => mink_consG_bwd (ft := fc) hfb hh)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (flat_ofSure _) (by simp [ofSure])
    (fun x hx => by rcases hrg x hx with rfl | rfl <;> assumption)
    (fun e he => by simp [ofSure] at he)
    ⟨⟨trivial, trivial, fun x h1 h2 => by simp only [NMem] at h1 h2; omega⟩,
      fun x hx => by rcases hrg x hx with rfl | rfl <;> omega⟩
    (Ext.refl g3) (GrowU.refl g3) rfl cb3
    (fun r hr => by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; exact Or.inl (Or.inl rfl))
    (fun r hr => by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; exact Or.inl (Or.inr rfl))
    (fun r h1 h2 => by simp only [ofSure, sure_mk, lazyReg, NMem] at h1 h2; omega)
    (Pref.refl g3) (fun _ _ => rfl) (flat_ofSure _) (flat_ofSure _) (fun e he => by simp [ofSure] at he)
    (fun e he => by simp [ofSure] at he) (fun e he => by simp [ofSure] at he) (by simp [ofSure]) (by simp [ofSure])
    (Ext.refl g3) (GrowU.refl g3) rfl rfl
    (Or.inl ⟨rfl, rfl, Or.inl (fun x => fitsS_lazyReg _ x)⟩) fq'.2.2.2
    Rq' Rp fq'.1 fp fq'.2.1 cpE fq'.2.2.1 (Sp.clean (L := ofSure (lazyReg a)) trivial k6) hcp hM u3 d3
    (fun cf _ k h0 h1' => absurd h1' (by omega))
    (fun _ _ _ x y r hn hr => absurd hn (nfit x y)) (fun _ _ x y hn => absurd hn (nfit x y))
    (fun c hc σ Inv ν O n gul hS hF st' regs t tm x y n' r _ hI htr fx fy hx hy hr => by
      subst hr
      exact ⟨fun _ => ⟨st', regs, hI, Needs.le_refl _, ⟨hx, hy⟩, fun _ _ => rfl, rfl⟩,
        fun nf => absurd (fitsS_pairReg _ x y) nf⟩)
    (fun c hc σ Inv ν O gul hS hB st' regs t tm x y hI htr fx fy hx hy res _ =>
      ⟨_, rfl, ⟨fun _ => ⟨st', regs, hI, Needs.le_refl _, ⟨hx, hy⟩, fun _ _ => rfl, rfl⟩,
        fun nf => absurd (fitsS_pairReg _ x y) nf⟩⟩)
  refine ⟨⟨_, R⟩, fun hm => ?_, ?_, fR, cR⟩
  · obtain ⟨e', he', ee⟩ := List.mem_map.mp hm
    have := lR e' he'
    have hthe : (pairRes n r nexF'.laz.bond nexS.laz.bond).th = n.th := rfl
    rw [hthe, eth] at ee
    simp only [jmp0] at ee
    omega
  · show g3.bo ≤ n.th.there
    omega

/-! ## A goal that asks nothing -/

theorem eqCode_atom (u v : Noun) : ∃ m, eqCode u v = A m := by
  by_cases e : u = v
  · exact ⟨0, by simp only [eqCode, if_pos e]⟩
  · exact ⟨1, by simp only [eqCode, if_neg e]⟩

/-- **`[5 fb fc]` under a goal that asks nothing**: the block `[equ a a+1]
hop th` at `g0.bo` behind the pair's run under `%next [this a this a+1]
(jmp0 g0.bo)`, `a = g0.re`, gives `RunOKLS` under `%next L th` from the state
before the two registers; the goal's entries get no op. -/
theorem equLS {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb fc : Noun} (M : MinkC5 lib P f fb fc)
    (hfb : ∃ a b, fb = C a b) {L : Lazy S} {th : Jmp} {g0 g3 g' : Gen Map} {nex : NextL S} {Q : Wit} {x : Bool}
    (hn : noneEquivalentL L = true) (hta : th.args = []) (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (cb0 : CondBelow g0)
    (r3 : g3.re = g0.re + 2) (b3 : g3.bo = g0.bo + 1) (cn3 : g3.cond = g0.cond) (E3 : Ext g0 g3)
    (G3 : GrowU g0 g3)
    (k3o : HoonMap.get g3.blocks g0.bo = some ⟨[], [Pole.equ g0.re (g0.re + 1)], Termin.hop (jmp0 th.there)⟩)
    (R : RunOKLB (Map := Map) lib N P (C fb fc) (ofSure (pairReg g0.re)) (jmp0 g0.bo) Q x g3 g' nex) :
    RunOKLS (Map := Map) lib N P f L th atomWit true g0 g' nex := by
  obtain ⟨hsn, hsl⟩ := noneEq_sure hn
  have e0 : entries (ofSure (pairReg g0.re : Sure S)) = [] := entries_ofSure _
  have rl := R.re
  have bl := R.bo
  have hfitL : ∀ v, FitsS L.sure v := fun v => ⟨by rw [hsn]; trivial, looks_one hsl v⟩
  have hent : ∀ e ∈ entries L, (∀ v, FitsS e.2.sure v) ∧ ∀ (R : Map (Option Noun)) v, HoldsS e.2.sure R v :=
    fun e he => by
      obtain ⟨a, b⟩ := noneEq_sure (noneEq_entries L hn e he)
      exact ⟨fun v => ⟨by rw [a]; trivial, looks_one b v⟩, fun R v => ⟨by rw [a]; trivial, looks_one b v⟩⟩
  have kN : HoonMap.get g'.blocks g0.bo = some ⟨[], [Pole.equ g0.re (g0.re + 1)], Termin.hop (jmp0 th.there)⟩ := by
    rw [R.keep _ (by omega) (by rw [e0]; simp)]; exact k3o
  have lab' : ∀ e ∈ entries nex.laz, g3.bo ≤ e.1 := fun e he => by
    rcases (R.labs e he).1 with h | h
    · rw [e0] at h; cases h
    · exact h.1
  have hbN : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (ned : Need) (s0 s : Noun),
      AgreeLB lib O c gul st t cf ned g0 g' nex.laz s0 s →
      HoonMap.get c.blocks g0.bo = some ⟨[], [Pole.equ g0.re (g0.re + 1)], Termin.hop (jmp0 th.there)⟩ := by
    intro cf hcf c σ O gul st t ned s0 s ag
    have hc : ∀ x, x < g3.re → HoonMap.get cf x = HoonMap.get g0.cond x := fun x hx => by
      rw [hcf x (by omega), R.cfr.get_lt hx, cn3]
    rw [ag.1 g0.bo (Nat.le_refl _) (by omega) (fun hm => by
      obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega), kN]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
      renJmp_nil _ (show (jmp0 th.there).args = [] from rfl)]
    rw [unproxy_none (by rw [hc _ (by omega)]; exact condBelow_none cb0 (Nat.le_refl _)),
      unproxy_none (by rw [hc _ (by omega)]; exact condBelow_none cb0 (by omega))]
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ z,
      ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) →
      ((z < g3.re ∨ NMem ned z) ∧ ¬ NMem (ofSure (pairReg g0.re : Sure S)).sure.ned z) := fun ned hned z hz =>
    ⟨hz.1.imp (fun h => by omega) id, fun hm => by
      simp only [ofSure, sure_mk, pairReg, NMem] at hm
      rcases hz.1 with h | h
      · omega
      · have := hned z h; omega⟩
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g' nex.laz s0 s) → (∀ x, NMem ned x → g'.re ≤ x) →
      ∀ u v,
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g3.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (pairReg g0.re : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (pairReg g0.re : Sure S)).sure (jmp0 g0.bo) (Q s) (Tone.zero (C u v)) →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x)
        st regs t tm nex.th L.sure th (atomWit s) (Tone.zero (eqCode u v)) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned u v G
    have hb := hbN cf hcf c σ O gul st t ned s0 s (ag st)
    obtain ⟨st1, R1, d, w, hI1, hν1, _, hh1, _, k1, e3⟩ := G.1 (fitsS_pairReg g0.re u v)
    have hx : SkaModel.read g0.re R1 = some u := hh1.1
    have hy : SkaModel.read (g0.re + 1) R1 = some v := hh1.2
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st1) R1 t _ _ hb
    rw [show [Pole.equ g0.re (g0.re + 1)] = [Pole.equ g0.re (g0.re + 1)] ++ [] from rfl, runs_equ hx hy,
      execBlob_hop, jmp0_of_args hta] at hj
    exact ⟨fun _ => ⟨st1, R1, Need.none, A 0, hI1, hν1, ⟨eqCode_atom u v, rfl⟩, by rw [hsn]; trivial, trivial,
      fun z hz => k1 z (hK ned hned z hz), e3.trans hj⟩, fun nf => absurd (hfitL _) nf⟩
  have dreg : ∀ s v d w r, atomWit s v d w → NMem d r → g0.re ≤ r ∧ r < g'.re :=
    fun s v d w r hq hr => by obtain ⟨_, rfl⟩ := hq; exact hr.elim
  have FS : FrontsS (Map := Map) atomWit true g0 g' L nex := by
    intro e he
    have hlt := hlab e he
    obtain ⟨f1, h1⟩ := hent e he
    refine ⟨[], fun B fin hb => ?_, fun cf hcf => Or.inr ⟨fun hm => by
      obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; omega, ?_⟩⟩
    · rw [List.nil_append, R.keep e.1 (by omega) (by rw [e0]; simp), E3.2.2.2 _ hlt]; exact hb
    · refine ⟨fun r hr => by simp [Sure.bunt, NMem] at hr, fun s v d w _ r _ hr => by simp [Sure.bunt, NMem] at hr,
        fun s v d w _ _ => fitsS_bunt s, fun lib σ O c gul st t R0 s v d w hq _ hd hE => ?_⟩
      exact ⟨fun _ => ⟨R0, Runs.nil R0, h1 R0 v, fun _ _ _ => rfl⟩, fun nf => absurd (f1 v) nf⟩
  refine ⟨⟨by omega, by omega, R.drop.trans E3.2.2.1, fun o ho hn' => ?_, G3.trans R.grow,
    (condFresh_of_eq (by omega) cn3).trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).1.elim (fun h => (by rw [e0] at h; cases h))
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup, dreg,
    fun s hs hf => ?_, R.ncond, R.econd,
    FS.toFront (by omega) (fun r hr => by rw [hsn] at hr; exact hr.elim)
      (fun e he r hr => by rw [gsE_true, hsn] at hr; exact hr.elim) dreg, ?_, ?_⟩, FS⟩
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
  · have Nc := R.nec s hs hf
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, e1', H⟩ := M.fwd hs hm
      rcases H with ⟨hnz, rfl⟩ | ⟨u, rfl, rc, e2, H⟩
      · exact badC_nz hnz (Nc.1 gul _ tm _ ((consStep hfb e1').1 hnz))
      · rcases H with ⟨hnz, rfl⟩ | ⟨v, rfl, h3⟩
        · exact badC_nz hnz (Nc.1 gul _ tm _ (((consStep hfb e1').2 u rfl _ e2).1 hnz))
        · rcases Nc.1 gul _ tm _ (((consStep hfb e1').2 u rfl _ e2).2 v rfl) with e | ⟨p, e, hp⟩
          · cases e
          · cases e; exact absurd (fitsS_pairReg g0.re u v) hp
    · obtain ⟨r, hm, hb⟩ := Nc.2 gul tm
      rcases consMink_cases5 M hfb hs hm with ⟨hnz, hmf⟩ | ⟨u, v, rfl, _, _⟩
      · exact ⟨r, hmf, badC_nz hnz hb⟩
      · rcases hb with e | ⟨p, e, hp⟩
        · cases e
        · cases e; exact absurd (fitsS_pairReg g0.re u v) hp
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r' hI htr hs hm ag hned regs hh hn0
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g3 g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨n', hn', rb, e1', H⟩ := M.fwd hs hm
    have hF' := oracleFwd_le hF (show n' + 1 ≤ n by omega)
    have Gp : ∀ r', minkF lib gul (n' + 1) tm s (C fb fc) = some r' → _ := fun r' e =>
      R.sem cf hcf c ned σ Inv ν O (n' + 1) gul hN hS hF' st t tm s0 s r' hI htr hs e ag3 hned regs hh hn0
    rcases H with ⟨hnz, rfl⟩ | ⟨u, rfl, rc, e2, H⟩
    · exact goalSemCMD_nz hnz (Gp _ ((consStep hfb e1').1 hnz))
    · rcases H with ⟨hnz, rfl⟩ | ⟨v, rfl, rfl⟩
      · exact goalSemCMD_nz hnz (Gp _ (((consStep hfb e1').2 u rfl _ e2).1 hnz))
      · exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned u v
          (Gp _ (((consStep hfb e1').2 u rfl _ e2).2 v rfl))
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn0 res hres
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g3 g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨rp, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag3 hned regs hh hn0
      res hres
    rcases consMink_cases5 M hfb hs hm with ⟨hnz, hmf⟩ | ⟨u, v, rfl, hu, hv⟩
    · exact ⟨rp, hmf, goalSemCMD_nz hnz G⟩
    · exact ⟨_, ((M.bwd hs hu).2 u _ rfl hv).2 v rfl,
        conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned u v G⟩

end Comp
end SkaModel
end Formalization
