import lemmas.Ska.CompIndirectFwd

/-!
# The first call theorem: the indirect call `[2 b c]`, backward

README Gaps 12.11 (fifteenth session).  `indirectTop_gen`: the steps of
`indirectTop_fwd` for any property `Φ` that the code of the indirect call
has from the run's jump given `RunOKNV` of the two runs and the blocks before
them.  `indirectTop_bwd`: the backward half (`ContractBwd`), with `Φ` the
backward contract (`bwdPhi`): what the code returns, `+mink` returns on
`[2 b c]` (`mink_n2_of`, `mink_n2_crash1`, `mink_n2_crash2`), the oracle's
`nok` answering as `+mink` (`OracleBwd.nok`).  `indirectTop_contract`: both
halves, the `BellContract` of the whole-subject code.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+mink` on `[2 b c]` from its parts -/

theorem mink_n2_of {lib : Lib} {gul : Noun} {tm : Trace} {s b c x y : Noun} {r : Tone}
    (h1 : Mink lib gul tm s b (Tone.zero x)) (h2 : Mink lib gul tm s c (Tone.zero y))
    (h3 : Mink lib gul tm x y r) : Mink lib gul tm s (n3 (A 2) b c) r := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  obtain ⟨n3', e3⟩ := h3
  refine ⟨max n1 (max n2 n3') + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_le lib gul (by omega : n1 ≤ max n1 (max n2 n3')) tm s b _ e1, tbind_zero,
    minkF_le lib gul (by omega : n2 ≤ max n1 (max n2 n3')) tm s c _ e2, tbind_zero,
    minkF_le lib gul (by omega : n3' ≤ max n1 (max n2 n3')) tm x y _ e3]

theorem mink_n2_crash1 {lib : Lib} {gul : Noun} {tm t' : Trace} {s b c : Noun}
    (h1 : Mink lib gul tm s b (Tone.two t')) : Mink lib gul tm s (n3 (A 2) b c) (Tone.two t') := by
  obtain ⟨n1, e1⟩ := h1
  refine ⟨n1 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [e1, tbind_two]

theorem mink_n2_crash2 {lib : Lib} {gul : Noun} {tm t' : Trace} {s b c x : Noun}
    (h1 : Mink lib gul tm s b (Tone.zero x)) (h2 : Mink lib gul tm s c (Tone.two t')) :
    Mink lib gul tm s (n3 (A 2) b c) (Tone.two t') := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [minkF_le lib gul (by omega : n1 ≤ max n1 n2) tm s b _ e1, tbind_zero,
    minkF_le lib gul (by omega : n2 ≤ max n1 n2) tm s c _ e2, tbind_two]

/-! ## Any property of the code from the run's jump -/

/-- **The whole-subject code of the indirect call meets any `Φ` that the
code from the run's jump meets** (`indirectTop_fwd` with `Φ` abstract). -/
theorem indirectTop_gen {lib : Lib} {p q : Nomm} (hp : FragU (S := S) p) (hq : FragU (S := S) q)
    (hcount : sixCount p + sixCount q ≤ 255)
    (Φ : (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop)
    (H : ∀ (g3 g6 : Gen Map) (nex : NextL S), RunOKNV lib (Nomm.cons p q) (pairSure 2 3 : Sure S) (jmp0 3) g3 g6 nex →
      g3.re = 4 → g3.bo = 4 → (∀ k, HoonMap.get g3.cond k = Option.none) →
      HoonMap.get g3.blocks 1 = some ⟨[], [], Termin.don 0⟩ →
      HoonMap.get g3.blocks 2 = some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩ →
      HoonMap.get g3.blocks 3 = some ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩ →
      (∀ (cf : Map (Nat × List Nat)), (∀ k, k < g6.re → HoonMap.get cf k = HoonMap.get g6.cond k) →
        ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
        AgreeU lib O c gul st t cf ned gen0 g6 nex.laz s s → (∀ r, NMem ned r → g6.re ≤ r) →
        ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
        Φ σ O st t gul s (goJ lib O c gul st regs t nex.th)) ∧
      (∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
        ¬ FitsS nex.laz.sure s → Φ σ O st t gul s (some (Tone.two t, st))))
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c) :
    c.need = NeedOrd.this ∧ ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (t : Trace) (gul : Noun),
      Φ σ O st t gul s (execEntry lib O st c [s] t gul) := by
  unfold finishLUC at h
  obtain ⟨⟨nex, gE⟩, hrun, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none hrun
  obtain ⟨rfl, rfl, rfl, e2, r3, b3, d3, cn3, k1, k2, k3, G3, cl3, k0⟩ := indirect_prefix h1 h2 h3
  have pp := fragU_pure hp
  have qp := fragU_pure hq
  rw [runLC_eq env q (Nomm.noCall_of_pure q qp), e2] at h4
  rw [pastL_pure _ _ pp, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  rw [runLC_eq env p (Nomm.noCall_of_pure p pp), e2] at h6
  have u3 : UpBelow g3 := G3.up upBelow_gen0
  have cb3 : CondBelow g3 := fun k hk => by rw [cn3 k] at hk; simp at hk
  have Rm := indirect_mid (a := 2) (b := 3) (o := 3) lib (runU_uok lib hp) (runU_uok lib hq) (by decide)
    (by omega) (by omega) (by decide) (by omega) hcount d3 u3 cl3 cb3 (cn3 2) (cn3 3) h4 h6 h7
  have T : TopS gE nex :=
    { ext := Ext.trans ⟨Nat.zero_le _, by show 1 ≤ g3.bo; omega, by rw [d3]; rfl, fun o ho => by
        have : o = 0 := by show o = 0; simp [gen0] at ho; omega
        subst this; rw [k0]; exact (HoonMap.get_empty 0).symm⟩ Rm.ext
      grow := G3.trans Rm.grow
      cfr := CondFresh.trans ⟨Nat.zero_le _, fun k => Or.inl (by rw [cn3 k]; exact (HoonMap.get_empty k).symm)⟩
        Rm.cfr
      lo := Rm.lo
      hi := Rm.hi
      args := nextArgs_nil Rm.ent rfl
      regs := fun r hr => ⟨Nat.zero_le _, by
        rcases Rm.regs r hr with e | ⟨_, e⟩
        · simp only [pairSure, NMem] at e; have := Rm.ext.1; omega
        · exact e⟩
      dist := Rm.dist
      eregs := fun e he => ⟨(Rm.eregs e he).1, fun r hr => ⟨Nat.zero_le _, ((Rm.eregs e he).2 r hr).2⟩⟩
      labs := fun e he => ⟨by have := (Rm.labs e he).1; show 1 ≤ e.1; omega, (Rm.labs e he).2⟩
      nodup := Rm.nodup
      ncond := Rm.ncond
      econd := Rm.econd }
  obtain ⟨hs, hn⟩ := H g3 gE nex Rm r3 b3 cn3 k1 k2 k3
  exact finishTop_gen lib T Φ hs hn hk hts

/-! ## The backward half -/

/-- What the code does from a point, for the backward contract on `[s f]`
against the needs `N`. -/
def bwdPhi (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) :
    (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop :=
  fun σ O st t gul s x => ∀ (Inv : σ → Prop) (ν : σ → Needs) (tm : Trace),
    P s → (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    Inv st → Forall2 (FrameRel lib (ν st)) t tm →
    ∀ ton st', x = some (ton, st') → ∃ r, Mink lib gul tm s f r ∧ ToneRel lib (ν st') ton r

/-- **The code of the indirect call from the run's jump meets `bwdPhi`.** -/
theorem indirect_semB {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {fb fc : Noun} {p q : Nomm} (hp : p.pure = true) (hq : q.pure = true) (hAp : Annot lib code P fb p)
    (hAq : Annot lib code P fc q) (N : Needs) {g3 g6 : Gen Map} {nex : NextL S}
    (Rm : RunOKNV lib (Nomm.cons p q) (pairSure 2 3 : Sure S) (jmp0 3) g3 g6 nex)
    (hre : g3.re = 4) (hbo : g3.bo = 4) (hcn : ∀ k, HoonMap.get g3.cond k = Option.none)
    (hb1 : HoonMap.get g3.blocks 1 = some ⟨[], [], Termin.don 0⟩)
    (hb2 : HoonMap.get g3.blocks 2 = some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩)
    (hb3 : HoonMap.get g3.blocks 3 = some ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩) :
    ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g6.re → HoonMap.get cf k = HoonMap.get g6.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      AgreeU lib O c gul st t cf ned gen0 g6 nex.laz s s → (∀ r, NMem ned r → g6.re ≤ r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
      bwdPhi lib N P (n3 (A 2) fb fc) σ O st t gul s (goJ lib O c gul st regs t nex.th) := by
  intro cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx
  -- the blocks 1, 2, 3 of the program
  have u : ∀ k, k < 4 → unproxy cf k = k := fun k hk => unproxy_none (by
    rw [hcf k (by have := Rm.ext.1; omega)]
    rcases Rm.cfr.2 k with e | ⟨l, _⟩
    · rw [e]; exact hcn k
    · omega)
  have cb : ∀ k blk, 1 ≤ k → k < 4 → HoonMap.get g3.blocks k = some blk →
      HoonMap.get c.blocks k = some (unproxyBlob cf blk) := fun k blk k1 k4 hk => by
    rw [ag.1 k (by simp [gen0]; omega) (by have := Rm.ext.2.1; omega) (fun hm => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := (Rm.labs e he).1; omega), Rm.ext.2.2.2 k (by omega), hk]; rfl
  have c1 := cb 1 _ (by omega) (by omega) hb1
  have c2 := cb 2 _ (by omega) (by omega) hb2
  have c3 := cb 3 _ (by omega) (by omega) hb3
  simp only [unproxyBlob, renBlob, List.map_cons, List.map_nil, renPole, renFin, renJmp, jmp0,
    u 0 (by omega), u 1 (by omega), u 2 (by omega), u 3 (by omega)] at c1 c2 c3
  have ag' : AgreeU lib O c gul st t cf ned g3 g6 nex.laz s s :=
    ⟨fun o' l u' hnl => ag.1 o' (by simp [gen0]; omega) u' hnl, ag.2⟩
  have G := Rm.sem cf hcf c ned σ O st t gul s s ag' hned regs hh hn
  rw [pureEval_cons] at G
  have mp : Mink lib gul tm s fb (pureTone tm p s) := (mink_pure hok hp hAp hs gul tm _).mpr rfl
  have mq : Mink lib gul tm s fc (pureTone tm q s) := (mink_pure hok hq hAq hs gul tm _).mpr rfl
  cases ex : pureEval p s with
  | none =>
    rw [ex] at G
    have G' : goJ lib O c gul st regs t nex.th = some (Tone.two t, st) := G
    rw [G'] at hx
    cases hx
    rw [pureTone, ex] at mp
    exact ⟨_, mink_n2_crash1 mp, ToneRel.two htr⟩
  | some x =>
    rw [pureTone, ex] at mp
    cases ey : pureEval q s with
    | none =>
      rw [ex, ey] at G
      have G' : goJ lib O c gul st regs t nex.th = some (Tone.two t, st) := G
      rw [G'] at hx
      cases hx
      rw [pureTone, ey] at mq
      exact ⟨_, mink_n2_crash2 mp mq, ToneRel.two htr⟩
    | some y =>
      rw [pureTone, ey] at mq
      rw [ex, ey] at G
      simp only [Option.bind_some] at G
      obtain ⟨regs', ⟨h2, h3⟩, -, e⟩ := G.1 ⟨⟨trivial, trivial⟩, looks_empty _⟩
      rw [e, goJ_nok (o := 3) (out := 2) c3 st regs' t h2 h3] at hx
      obtain ⟨⟨ton0, st'⟩, hO, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨r0, ⟨k, hM⟩, hrel⟩ := hB.nok st x y gul ton0 st' hI hO
      obtain ⟨_, hν⟩ := hS.nok st x y gul ton0 st' hI hO
      have M : Mink lib gul tm s (n3 (A 2) fb fc) (r0.app tm) :=
        mink_n2_of mp mq ⟨k, by rw [minkF_trace, hM]; rfl⟩
      cases hrel with
      | zero p' =>
        have hz : goJ lib O c gul st' (SkaModel.store 1 p' regs') t (jmp0 2) = some (Tone.zero p', st') := by
          rw [goJ_jmp0 _ _ _ _ c2, execBlob_cons]
          rw [execPole_local lib O gul st' _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
            (by simp)]
          have hm1 : SkaModel.move 1 0 (SkaModel.store 1 p' regs') =
              some (HoonMap.put (SkaModel.store 1 p' regs') 0 (some p')) := by
            simp [SkaModel.move, SkaModel.store, HoonMap.get_put]
          simp only [localPole, hm1, Option.bind_some, Option.map_some]
          rw [execBlob_hop]
          simp [goJ, c1, execBlob_don', SkaModel.read, HoonMap.get_put]
        have hx' : goJ lib O c gul st' (SkaModel.store 1 p' regs') t (jmp0 2) = some (ton, st'') := hx
        rw [hz] at hx'
        cases hx'
        exact ⟨_, M, ToneRel.zero p'⟩
      | one p' =>
        have hx' : some (Tone.one p', st') = some (ton, st'') := hx
        cases hx'
        exact ⟨_, M, ToneRel.one p'⟩
      | two hl =>
        have hx' : some (Tone.two (_ ++ t), st') = some (ton, st'') := hx
        cases hx'
        exact ⟨_, M, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩

/-- Where the run's need does not fit, the code's crash stands for
`+mink`'s on `[2 b c]`. -/
theorem indirect_necB {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {fb fc : Noun} {p q : Nomm} (hp : p.pure = true) (hq : q.pure = true) (hAp : Annot lib code P fb p)
    (hAq : Annot lib code P fc q) (N : Needs) {g3 g6 : Gen Map} {nex : NextL S}
    (Rm : RunOKNV lib (Nomm.cons p q) (pairSure 2 3 : Sure S) (jmp0 3) g3 g6 nex) :
    ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      ¬ FitsS nex.laz.sure s → bwdPhi lib N P (n3 (A 2) fb fc) σ O st t gul s (some (Tone.two t, st)) := by
  intro σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx
  cases hx
  rcases Rm.nec s hfs with e | ⟨v, ev, hv⟩
  · have mp : Mink lib gul tm s fb (pureTone tm p s) := (mink_pure hok hp hAp hs gul tm _).mpr rfl
    have mq : Mink lib gul tm s fc (pureTone tm q s) := (mink_pure hok hq hAq hs gul tm _).mpr rfl
    rw [pureEval_cons] at e
    cases ex : pureEval p s with
    | none => rw [pureTone, ex] at mp; exact ⟨_, mink_n2_crash1 mp, ToneRel.two htr⟩
    | some x =>
      rw [ex] at e; rw [pureTone, ex] at mp
      cases ey : pureEval q s with
      | none => rw [pureTone, ey] at mq; exact ⟨_, mink_n2_crash2 mp mq, ToneRel.two htr⟩
      | some y => rw [ey] at e; simp at e
  · exfalso
    apply hv
    rw [pureEval_cons] at ev
    obtain ⟨x, -, ev⟩ := Option.bind_eq_some_iff.mp ev
    obtain ⟨y, -, ev⟩ := Option.bind_eq_some_iff.mp ev
    cases ev
    exact ⟨⟨trivial, trivial⟩, looks_empty _⟩

/-- **The first call theorem, backward**: the whole-subject code of the
nomm `[2 p q]` of the formula `[2 b c]`, with `p` and `q` in `FragU` and at
most 255 `%6` in all, meets the backward half of the contract on the subject
whole, on every subject that fits the bell, against any needs. -/
theorem indirectTop_bwd {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {fb fc : Noun} {p q : Nomm} (hfol : bl.fol = n3 (A 2) fb fc)
    (hAp : Annot lib code (SkaModel.Fits bl.less) fb p) (hAq : Annot lib code (SkaModel.Fits bl.less) fc q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s → ContractBwd lib N s bl.fol [s] c := by
  have F := indirectTop_gen (lib := lib) hp hq hcount (bwdPhi lib N (SkaModel.Fits bl.less) (n3 (A 2) fb fc))
    (fun _ _ _ Rm r3 b3 cn3 k1 k2 k3 =>
      ⟨indirect_semB hok (fragU_pure hp) (fragU_pure hq) hAp hAq N Rm r3 b3 cn3 k1 k2 k3,
        indirect_necB hok (fragU_pure hp) (fragU_pure hq) hAp hAq N Rm⟩) h
  refine ⟨F.1, fun s hs σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩
  rw [hfol]
  exact F.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The first call theorem**: both halves, the contract of the bell with
the subject whole as the one argument (`BellContract … true`), for the
nomm `[2 p q]` of the formula `[2 b c]` with `p`, `q` in `FragU`. -/
theorem indirectTop_contract {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {fb fc : Noun} {p q : Nomm} (hfol : bl.fol = n3 (A 2) fb fc)
    (hAp : Annot lib code (SkaModel.Fits bl.less) fb p) (hAq : Annot lib code (SkaModel.Fits bl.less) fc q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ BellContract lib N bl true c := by
  refine ⟨(indirectTop_fwd hok hfol hAp hAq hp hq hcount h N).1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact ⟨(indirectTop_fwd hok hfol hAp hAq hp hq hcount h N).2 s hs,
    (indirectTop_bwd hok hfol hAp hAq hp hq hcount h N).2 s hs⟩

end Comp
end SkaModel
end Formalization
