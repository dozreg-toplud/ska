import lemmas.Ska.CompConsLSF
import lemmas.Ska.CompNCThree

/-!
# `[3 p]` under a flat lazy goal, `p` any nomm with `LOKSF`

README Gaps 12.28.  Under `%next L th` the `%3` case runs `p` under `L`
itself when `L` asks nothing (`+none-equivalent`); else it is
`+collapse-lazy-atom` (`CollPre`, the register `r` and the label `there`),
`+forl r there` (two blocks writing `0` or `1` into `r` and hopping to
`there`), the block `[clq arg z o']` and `p` under `%next (lazy-from-reg
arg)` into it.  `clqLB` puts `+forl` and the `clq` block behind `p`'s run
(as `incLB`), and `collLS` puts the collapse in front, unchanged.

* `forl_fix`, `clqLB`, `wutWit`, `RunOKLS.wutNone` (the operand under a goal
  that asks nothing), `runLC_n3_next`, `lokS_three_run`, `lokS_three`
  (`[3 p]` meets `LOKS true`), `jNewLS_three`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The blocks of `+forl` are left alone by unproxying** with a `cond`
that has no entry at `r` and at the two registers `+forl` allocates. -/
theorem forl_fix {r o : Nat} {g g' : Gen Map} {z o' : Nat}
    (h : (forl r o : CM Map (Nat × Nat)) g = some ((z, o'), g')) (hd : g.drop = false)
    {cf : Map (Nat × List Nat)} (h0 : HoonMap.get cf r = Option.none)
    (h1 : HoonMap.get cf g.re = Option.none) (h2 : HoonMap.get cf (g.re + 1) = Option.none) :
    ∀ k, g.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k := by
  simp only [forl, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  intro k hk1 hk2
  simp only [emitted_bo] at hk2
  have : k = g.bo ∨ k = g.bo + 1 ∨ k = g.bo + 2 := by omega
  have a1 : g.bo ≠ g.bo + 1 := by omega
  have a2 : g.bo ≠ g.bo + 1 + 1 := by omega
  have a3 : g.bo + 1 ≠ g.bo + 1 + 1 := by omega
  have a4 : g.bo + 2 = g.bo + 1 + 1 := rfl
  rcases this with rfl | rfl | rfl <;>
    simp [Gen.emitted, hd, HoonMap.get_put, unproxyBlob, renBlob, renPole, renFin, renJmp, jmp0,
      unproxy_none h0, unproxy_none h1, unproxy_none h2, a1, a2, a3, a1.symm, a2.symm, a3.symm, a4]

/-- **`+forl` and the `clq` block behind the operand's run** (`incLB` for
`%3`): `RunOKLB` of the operand for `fb` under `%next (lazy-from-reg arg)
(jmp0 oc)`, from the state with the blocks of `+forl r there` and `[clq arg
z o']` made, is `RunOKLB` of `[3 fb]` under `%next (lazy-from-reg r) (jmp0
there)` from the state before, with products atoms (`atomWit`). -/
theorem clqLB {lib : Lib} {P : Noun → Prop} {f fb : Noun} (M : MinkC3 lib P f fb)
    {g2 g3 gE g' : Gen Map} {nex : NextL S} {r there z o' : Nat} {Q : Wit} {x : Bool}
    (hr : r < g2.re) (hrk : HoonMap.get g2.cond r = Option.none) (cb2 : CondBelow g2) (d2 : g2.drop = false)
    (hF : (forl r there : CM Map (Nat × Nat)) g2 = some ((z, o'), g3)) (c3 : g3.cond = g2.cond)
    (rE : gE.re = g3.re + 1) (bE : gE.bo = g3.bo + 1) (cE : gE.cond = g3.cond) (E3 : Ext g3 gE)
    (G : GrowU g2 gE) (hth : 1 ≤ there ∧ there < g2.bo)
    (kc : HoonMap.get gE.blocks g3.bo = some ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩)
    (R : RunOKLB (Map := Map) lib P fb (ofSure (lazyReg g3.re)) (jmp0 g3.bo) Q x gE g' nex) :
    RunOKLB (Map := Map) lib P f (ofSure (lazyReg r)) (jmp0 there) atomWit false g2 g' nex := by
  obtain ⟨E23, r3, b3, FS⟩ := forl_ok hF hr
  have E2E := E23.trans E3
  have e0 : entries (ofSure (lazyReg g3.re : Sure S)) = [] := entries_ofSure _
  have e1 : entries (ofSure (lazyReg r : Sure S)) = [] := entries_ofSure _
  have rl := R.re
  have bl := R.bo
  have nk : ∀ x, g2.re ≤ x → HoonMap.get g2.cond x = Option.none := fun x hx => condBelow_none cb2 hx
  have kN : HoonMap.get g'.blocks g3.bo = some ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩ := by
    rw [R.keep _ (by omega) (by rw [e0]; simp)]; exact kc
  have lab' : ∀ e ∈ entries nex.laz, gE.bo ≤ e.1 := fun e he => by
    rcases (R.labs e he).1 with h | h
    · rw [e0] at h; cases h
    · exact h.1
  -- the blocks of `+forl` and the `clq` block in any code that agrees with the run
  have hbN : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (ned : Need) (s0 s : Noun),
      AgreeLB lib O c gul st t cf ned g2 g' nex.laz s0 s →
      Agree c g2 g3 ∧ HoonMap.get c.blocks g3.bo = some ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩ := by
    intro cf hcf c σ O gul st t ned s0 s ag
    have hc : ∀ x, x < gE.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun x hx => by
      rw [hcf x (by omega), R.cfr.get_lt hx, cE, c3]
    have nl : ∀ o, gE.bo ≤ o → o ∉ (entries nex.laz).map Prod.fst → True := fun _ _ _ => trivial
    refine ⟨fun o h0 h1 => ?_, ?_⟩
    · rw [ag.1 o h0 (by omega) (fun hm => by
        obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega),
        R.keep o (by omega) (by rw [e0]; simp), E3.2.2.2 o h1]
      exact forl_fix hF d2 (by rw [hc _ (by omega)]; exact hrk) (by rw [hc _ (by omega)]; exact nk _ (Nat.le_refl _))
        (by rw [hc _ (by omega)]; exact nk _ (by omega)) o h0 h1
    · rw [ag.1 g3.bo (by omega) (by omega) (fun hm => by
        obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab' e he; omega), kN]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin,
        renJmp_nil _ (show (jmp0 z).args = [] from rfl), renJmp_nil _ (show (jmp0 o').args = [] from rfl)]
      rw [unproxy_none (by rw [hc _ (by omega)]; exact nk _ (by omega))]
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ z',
      ((z' < g2.re ∨ NMem ned z') ∧ ¬ NMem (lazyReg r : Sure S).ned z') →
      z' ≠ r ∧ z' ≠ g2.re ∧ z' ≠ g2.re + 1 ∧
      ((z' < gE.re ∨ NMem ned z') ∧ ¬ NMem (ofSure (lazyReg g3.re : Sure S)).sure.ned z') := fun ned hned z' hz => by
    have nr : z' ≠ r := fun e => hz.2 (by subst e; simp [lazyReg, NMem])
    refine ⟨nr, ?_, ?_, hz.1.imp (fun h => by omega) id, fun hm => ?_⟩
    · rcases hz.1 with h | h
      · omega
      · have := hned z' h; omega
    · rcases hz.1 with h | h
      · omega
      · have := hned z' h; omega
    · simp only [ofSure, sure_mk, lazyReg, NMem] at hm
      rcases hz.1 with h | h
      · omega
      · have := hned z' h; omega
  -- the shared part of the two `sem` clauses: through the `clq` block and `+forl`
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g2 g' nex.laz s0 s) → (∀ x, NMem ned x → g'.re ≤ x) →
      Forall2 (FrameRel lib (ν st)) t tm → ∀ rb,
      GoalSemCMD lib O c gul Inv ν (fun x => (x < gE.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg g3.re : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg g3.re : Sure S)).sure (jmp0 g3.bo) (Q s) rb →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g2.re ∨ NMem ned x) ∧
          ¬ NMem (ofSure (lazyReg r : Sure S)).sure.ned x)
        st regs t tm nex.th (ofSure (lazyReg r : Sure S)).sure (jmp0 there) (atomWit s) (wutTone rb) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rb G
    obtain ⟨hag, hb⟩ := hbN cf hcf c σ O gul st t ned s0 s (ag st)
    cases rb with
    | one q => exact G
    | two t' => exact G
    | zero x =>
      obtain ⟨st1, R1, d, w, hI1, hν1, _, hh1, _, k1, e3⟩ := G.1 (fitsS_lazyReg _ x)
      have hx : SkaModel.read g3.re R1 = some x := hh1
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st1) R1 t _ _ hb
      rw [execBlob_clq, hx, Option.bind_some] at hj
      have F' := FS d2 c hag lib σ O st1 R1 t gul
      cases x with
      | cell u v =>
        simp only [wutTone, wut]
        refine ⟨fun _ => ⟨st1, store r (A 0) (store g2.re (A 0) R1), Need.none, A 0, hI1, hν1, ⟨⟨0, rfl⟩, rfl⟩,
          read_store_eq _ _ _, trivial, fun z' hz => ?_, e3.trans (hj.trans F'.1)⟩,
          fun nf => absurd (fitsS_lazyReg _ _) nf⟩
        obtain ⟨n1, n2, -, k⟩ := hK ned hned z' hz
        rw [read_store_ne n1, read_store_ne n2]
        exact k1 z' k
      | atom n =>
        simp only [wutTone, wut]
        refine ⟨fun _ => ⟨st1, store r (A 1) (store (g2.re + 1) (A 1) R1), Need.none, A 0, hI1, hν1,
          ⟨⟨1, rfl⟩, rfl⟩, read_store_eq _ _ _, trivial, fun z' hz => ?_, e3.trans (hj.trans F'.2)⟩,
          fun nf => absurd (fitsS_lazyReg _ _) nf⟩
        obtain ⟨n1, -, n3, k⟩ := hK ned hned z' hz
        rw [read_store_ne n1, read_store_ne n3]
        exact k1 z' k
  refine ⟨by omega, by omega, R.drop.trans E2E.2.2.1, fun o ho hn => ?_, G.trans R.grow,
    (condFresh_of_eq (by omega) (cE.trans c3)).trans R.cfr, R.lo, R.hi, ?_, fun r' hr' => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r' hr' => ?_⟩,
    fun e he => ⟨Or.inr ⟨(by have := lab' e he; omega), (R.labs e he).1.elim (fun h => (by rw [e0] at h; cases h))
      (fun h => h.2)⟩, (R.labs e he).2⟩, R.nodup,
    fun s v d w r' hq hr' => (by obtain ⟨_, rfl⟩ := hq; exact hr'.elim),
    fun s hs hf => ?_, R.ncond, R.econd, fun e he => (by rw [e1] at he; cases he), ?_, ?_⟩
  · rw [R.keep o (by omega) (by rw [e0]; simp), E2E.2.2.2 o ho]
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, kN, rfl, rfl⟩
  · rcases R.regs r' hr' with h | h
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h
      exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · rcases (R.eregs e he).2 r' hr' with ⟨e0', h0, _⟩ | h | h
    · rw [e0] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · have N := R.nec s hs hf
    have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg g3.re : Sure S) (jmp0 g3.bo)) tm r →
        r = Tone.two tm := fun hb => by
      rcases hb with e | ⟨q, _, hq⟩
      · exact e
      · exact absurd (fitsS_lazyReg _ q) hq
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
      rw [bad (N.1 gul n' tm rb hb)]
      exact Or.inl rfl
    · obtain ⟨rb, hmb, hbad⟩ := N.2 gul tm
      refine ⟨_, M.bwd hs hmb, ?_⟩
      rw [bad hbad]
      exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned gE g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rb
      (R.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb ag3 hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have ag3 : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned gE g' nex.laz s0 s :=
      fun st' => agreeLB_mono (ag st') (by omega)
    obtain ⟨rb, hmb, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag3 hned regs hh hn
      res hres
    exact ⟨_, M.bwd hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr rb G⟩

/-! ## A goal that asks nothing -/

/-- The witness relation of `[3 p]` run under its goal itself: `p`'s, with
the product's cell test. -/
def wutWit (Q : Wit) : Wit := fun s v' d w => ∃ v, Q s v d w ∧ v' = wut v

/-- **`[3 p]` under a goal that asks nothing** (`three_of_none` for
`RunOKLS`): `p` runs under the goal itself and every product fits it and its
entries, so `p`'s `RunOKLS` for `fb` is one for `[3 fb]` with `wutWit`. -/
theorem RunOKLS.wutNone {lib : Lib} {P : Noun → Prop} {f fb : Noun} {L : Lazy S} {th : Jmp} {Q : Wit} {x : Bool}
    {g0 g1 : Gen Map} {nex : NextL S} (M : MinkC3 lib P f fb) (hn : noneEquivalentL L = true)
    (R : RunOKLS (Map := Map) lib P fb L th Q x g0 g1 nex) :
    RunOKLS (Map := Map) lib P f L th (wutWit Q) x g0 g1 nex := by
  obtain ⟨hsn, hsl⟩ := noneEq_sure hn
  have hE : gsE x L = Need.none := by cases x <;> simp [gsE, hsn]
  have hfitL : ∀ v, FitsS L.sure v := fun v => ⟨by rw [hsn]; trivial, looks_one hsl v⟩
  have hent : ∀ e ∈ entries L, (∀ v, FitsS e.2.sure v) ∧ ∀ (R : Map (Option Noun)) v, HoldsS e.2.sure R v :=
    fun e he => by
      obtain ⟨a, b⟩ := noneEq_sure (noneEq_entries L hn e he)
      exact ⟨fun v => ⟨by rw [a]; trivial, looks_one b v⟩, fun R v => ⟨by rw [a]; trivial, looks_one b v⟩⟩
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next L.sure th) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨q, _, hq⟩
    · exact e
    · exact absurd (hfitL q) hq
  have conv : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}
      {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp} {s : Noun} (rb : Tone),
      GoalSemCMD lib O c gul Inv ν K st regs t tm je L.sure th (Q s) rb →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je L.sure th (wutWit Q s) (wutTone rb) := by
    intro σ O c gul Inv ν K st regs t tm je s rb G
    cases rb with
    | zero v =>
      obtain ⟨st', R', d, w, hI, hle, hq, _, hd, hk, e⟩ := G.1 (hfitL v)
      exact ⟨fun _ => ⟨st', R', d, w, hI, hle, ⟨v, hq, rfl⟩, by rw [hsn]; trivial, hd, hk, e⟩,
        fun hf => absurd (hfitL _) hf⟩
    | one q => exact G
    | two tr => exact G
  have FS : ∀ {E : Need} {lo0 lo : Nat} {L' : Sure S} {F : List Pole} {Le : Sure S}, E = Need.none →
      (∀ v, FitsS Le v) → (∀ (R : Map (Option Noun)) v, HoldsS Le R v) →
      FrontS (Map := Map) Q E lo0 lo L' F Le → FrontS (Map := Map) (wutWit Q) E lo0 lo L' F Le := by
    intro E lo0 lo L' F Le hE0 hfe hhe h
    refine ⟨h.loc, fun s v d w hq => by obtain ⟨u, hq, -⟩ := hq; exact h.dis s u d w hq,
      fun s v d w hq _ => by obtain ⟨u, hq, -⟩ := hq; exact h.fit s u d w hq (hfe u),
      fun lib σ O c gul st t R s v d w hq hs hd _ => ?_⟩
    obtain ⟨u, hq, rfl⟩ := hq
    obtain ⟨H1, -⟩ := h.run lib σ O c gul st t R s u d w hq hs hd (by rw [hE0]; trivial)
    refine ⟨fun _ => ?_, fun nf => absurd (hfe _) nf⟩
    obtain ⟨R', r', -, k⟩ := H1 (hfe u)
    exact ⟨R', r', hhe R' _, k⟩
  have FL : ∀ {E : Need} {lo0 lo : Nat} {L' : Sure S} {F : List Pole} {Le : Sure S}, E = Need.none →
      (∀ v, FitsS Le v) → (∀ (R : Map (Option Noun)) v, HoldsS Le R v) →
      FrontLB (Map := Map) Q E lo0 lo L' F Le → FrontLB (Map := Map) (wutWit Q) E lo0 lo L' F Le := by
    intro E lo0 lo L' F Le hE0 hfe hhe h lib σ O c gul st t ned A s0 s v d w hn hq hf R hR
    obtain ⟨u, hq, rfl⟩ := hq
    have H := h lib σ O c gul st t ned A s0 s u d w hn hq hf R ⟨hR.1, by rw [hE0]; trivial⟩
    refine ⟨fun _ => ?_, fun nf => absurd (hfe _) nf⟩
    obtain ⟨R', r', -, k⟩ := H.1 (hfe u)
    exact ⟨R', r', hhe R' _, k⟩
  refine { toRunOKLB := { R.toRunOKLB with dreg := ?_, nec := ?_, front := ?_, sem := ?_, semB := ?_ }, fs := ?_ }
  · intro s v d w r hq hr
    obtain ⟨u, hq, -⟩ := hq
    exact R.dreg s u d w r hq hr
  · intro s hs hf
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', _, rb, hb, rfl⟩ := M.fwd hs hm
      rw [bad ((R.nec s hs hf).1 gul n' tm rb hb)]
      exact Or.inl rfl
    · obtain ⟨rb, hmb, hbad⟩ := (R.nec s hs hf).2 gul tm
      exact ⟨_, M.bwd hs hmb, by rw [bad hbad]; exact Or.inl rfl⟩
  · intro e he
    obtain ⟨F, hb, hF⟩ := R.front e he
    obtain ⟨f1, h1⟩ := hent e he
    exact ⟨F, hb, fun cf hcf => (hF cf hcf).imp (fun ⟨L', hm, fs⟩ => ⟨L', hm, FL hE f1 h1 fs⟩)
      (fun ⟨hn', fs⟩ => ⟨hn', FL hE f1 h1 fs⟩)⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn'
    obtain ⟨n', hn'', rb, hb, rfl⟩ := M.fwd hs hm
    exact conv rb (R.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hn'') st t tm s0 s rb hI htr hs hb ag
      hned regs hh hn')
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn' res hres
    obtain ⟨rb, hmb, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn' res hres
    exact ⟨_, M.bwd hs hmb, conv rb G⟩
  · intro e he
    obtain ⟨F, hb, hF⟩ := R.fs e he
    obtain ⟨f1, h1⟩ := hent e he
    exact ⟨F, hb, fun cf hcf => (hF cf hcf).imp (fun ⟨L', hm, fs⟩ => ⟨L', hm, FS hE f1 h1 fs⟩)
      (fun ⟨hn', fs⟩ => ⟨hn', FS hE f1 h1 fs⟩)⟩

/-! ## `[3 p]` under a flat lazy goal -/

/-- **The `%3` case of `run` under `%next L th`.** -/
theorem runLC_n3_next (env : CallEnv) (sup : Option Nomm) (p : Nomm) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.n3 p) (CGoalL.next L th) region : CM Map (NextL S)) =
      if noneEquivalentL L then runLC env sup p (CGoalL.next L th) region else (do
        let a ← collapseLazyAtomL ⟨L, th⟩
        match a with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runLC env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
  conv => lhs; unfold runLC
  rfl

/-- **`[3 p]` whose operand meets `LOKSF`, under a flat lazy goal**, from a
state as `LOKS.run` asks: `RunOKLS` with `x = true`, the jump at none of the
result's entries and the goal's or new, the result flat with clean entries.
Under a goal that asks nothing the operand runs there (`RunOKLS.wutNone`);
else `collapsePre_spec`, `+forl`, the `clq` block, the operand under `%next
(lazy-from-reg arg)`, `clqLB`, `collLS`. -/
theorem lokS_three_run (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (M : MinkC3 lib P f fb) (Sp : LOKSF (S := S) (Map := Map) lib env P fb p)
    {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hcount : sixCount (Nomm.n3 p) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hta : th.args = [])
    (ht : th.there ∉ (entries L).map Prod.fst) (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfl : Flat L) (hcs : Clean L.sure.ned) (hce : ∀ e ∈ entries L, Clean e.2.sure.ned)
    (hr : runLC env sup (Nomm.n3 p) (CGoalL.next L th) region g0 = some (nex, g1)) :
    (∃ Q, RunOKLS (Map := Map) lib P f L th Q true g0 g1 nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      ((nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ (noneEquivalentL L = false → g0.bo ≤ nex.th.there)) ∧
      Flat nex.laz ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  have hc : sixCount p ≤ 255 := by simpa only [sixCount] using hcount
  rw [runLC_n3_next] at hr
  by_cases en : noneEquivalentL L = true
  · rw [if_pos en] at hr
    obtain ⟨⟨Q, R⟩, a, b, c, d⟩ := Sp.run (Or.inl (noneEq_sure en).1) hc b0 d0 hu hcl0 hcb h1 h2 hta ht hsd hsl
      hlab hnd hed hfl hcs hce hr
    have R' := R.wutNone M en
    have hE : gsE true L = gsE false L := by simp [gsE, (noneEq_sure en).1]
    have F1 := R'.front
    have F2 := R'.fs
    unfold FrontsS at F2
    rw [← hE] at F1 F2
    exact ⟨⟨_, { toRunOKLB := { R'.toRunOKLB with front := F1 }, fs := F2 }⟩, a,
      ⟨b, fun h => by rw [h] at en; cases en⟩, c, d⟩
  rw [if_neg en] at hr
  obtain ⟨a, gA, hc2, h⟩ := bind_some hr
  rcases a with _ | ⟨r, o⟩
  · cases h
  have CP := collapsePre_spec (r := r) (there := o) hc2 rfl d0 hcb (fun x hx => (hsl x hx).1)
    (fun x hx => (hsl x hx).2) (List.nodup_cons.mpr ⟨ht, hnd⟩)
    (fun e he => ⟨(hlab e he).1, by obtain ⟨B, th'', hb⟩ := (hlab e he).2; exact ⟨B, _, hb⟩⟩)
    (fun e he x hx => ((hed e he).2 x hx).1)
  obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
  have c1 := CP.le
  have c2 := CP.bo1
  have hth' : 1 ≤ o ∧ o < gA.bo := by
    rcases CP.shape with ⟨e, eb, -⟩ | ⟨e, eb, -⟩ <;> (rw [e]; omega)
  obtain ⟨E23, r3, b3, -⟩ := forl_ok h3 CP.rlt
  have Fd := forl_down h3 hth'.1 hth'.2 (by omega)
  have c3 : g3.cond = gA.cond := (kc_forl r o).keep gA _ g3 h3
  have d2 : gA.drop = false := CP.drop.trans d0
  have d3 : g3.drop = false := E23.2.2.1.trans d2
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  obtain ⟨g4, hg4⟩ : ∃ g4 : Gen Map, g4 = { g3 with re := g3.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g4.emitted blk := ⟨_, rfl⟩
  have hbo4 : g4.bo = g3.bo := by rw [hg4]
  have hre4 : g4.re = g3.re + 1 := by rw [hg4]
  have hcn4 : g4.cond = g3.cond := by rw [hg4]
  have hdr4 : g4.drop = false := by rw [hg4]; exact d3
  rw [← hg4, ← hblk, ← hgE] at h
  have hboE : gE.bo = g3.bo + 1 := by rw [hgE, emitted_bo, hbo4]
  have hreE : gE.re = g3.re + 1 := by rw [hgE, emitted_re, hre4]
  have hcnE : gE.cond = g3.cond := by rw [hgE, ← hcn4]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr4
  have hbE : HoonMap.get gE.blocks g3.bo = some blk := by rw [hgE, ← hbo4]; exact emitted_get g4 blk hdr4
  have G3E : Grow g3 gE := by
    have g34 : Grow g3 g4 := by rw [hg4]; exact grow_re g3
    have g4E : Grow g4 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk, hbo4]; exact jumpsBelow_two rfl Fd.2.1 Fd.2.2
    exact g34.trans g4E
  have GUA : GrowU g0 gA := CP.grow.toU hu
  have huA : UpBelow gA := GUA.up hu
  have GU : GrowU gA gE := (Fd.1.trans G3E).toU huA
  have E3E : Ext g3 gE := by rw [hgE, hg4]; exact (ext_re _).trans (ext_emit _ _)
  have cbA : CondBelow gA := CP.pfor.1.below hcb
  have cbE : CondBelow gE := fun x hx => by rw [hcnE, c3] at hx; have := cbA x hx; omega
  have eR : entries (ofSure (lazyReg g3.re : Sure S)) = [] := entries_ofSure _
  obtain ⟨⟨Qp, Rp⟩, pne, pj, pfl, pec⟩ := Sp.run (sup := sup) (L := ofSure (lazyReg g3.re)) (th := jmp0 g3.bo)
    (region := region) (Or.inr eR) hc (by omega) hdE (GU.up huA)
    ((hcl0.growU GUA).growU GU) cbE
    (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) rfl (by rw [eR]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by omega, by rw [hcnE, c3]; exact condBelow_none cbA (by omega)⟩)
    (fun e he => by rw [eR] at he; cases he) (by rw [eR]; simp) (fun e he => by rw [eR] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [eR] at he; cases he) h
  have RA := clqLB (Map := Map) M (g2 := gA) (g3 := g3) (gE := gE) CP.rlt CP.rkey cbA d2 h3 c3 hreE hboE hcnE
    E3E GU hth' (by rw [hbE, hblk]) Rp.toRunOKLB
  have hfr : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → gA.re ≤ x := fun e he x hx => by
    rcases (Rp.eregs e he).2 x hx with ⟨e0, h0, _⟩ | h | h
    · rw [eR] at h0; cases h0
    · simp only [ofSure, sure_mk, lazyReg, NMem] at h; omega
    · omega
  have RS := collLS (Map := Map) CP hu (fun e he => (hlab e he).1) (fun x hx => (hsl x hx).1)
    (fun e he x hx => (hed e he).2 x hx) hfr RA
  have J : g0.bo ≤ nex.th.there := by
    rcases pj with e | e
    · rw [e]; simp only [jmp0]; omega
    · omega
  exact ⟨⟨_, RS⟩, pne, ⟨Or.inr J, fun _ => J⟩, pfl, pec⟩

/-- **`[3 p]` meets `LOKS true`** when its operand meets `LOKSF`, for a
formula `f` whose `+mink` is the cell test of the operand's. -/
theorem lokS_three (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (M : MinkC3 lib P f fb) (Sp : LOKSF (S := S) (Map := Map) lib env P fb p) :
    LOKS (S := S) (Map := Map) true lib env P f (Nomm.n3 p) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun {sup L th region g0 g1 nex} hcount b0 d0 hu hcl hcb
    h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr => ?_⟩
  · rw [runLC_n3_next] at hr
    by_cases en : noneEquivalentL L = true
    · rw [if_pos en] at hr; exact Sp.clean hc hr
    · rw [if_neg en] at hr
      obtain ⟨a, gA, hc2, h⟩ := bind_some hr
      rcases a with _ | ⟨r, o⟩
      · cases h
      obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
      exact Sp.clean (L := ofSure (lazyReg _)) trivial h
  · obtain ⟨H, ne, ⟨j, -⟩, fl, ec⟩ := lokS_three_run lib env M Sp hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl
      hlab hnd hed hfl hcl' hce hr
    exact ⟨H, ne, j, fl, ec⟩

/-- **The jump of a hinted `[3 p]` is a block it made**: under a goal that
asks nothing it is the operand's (`JNewLSF`, the goal flag-free), else it is
always new. -/
theorem jNewLS_three (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (M : MinkC3 lib P f fb) (Sp : LOKSF (S := S) (Map := Map) lib env P fb p)
    (Jp : hinted env.cod p = some true → JNewLSF (S := S) (Map := Map) env p)
    (hh : hinted env.cod (Nomm.n3 p) = some true) : JNewLS (S := S) (Map := Map) env (Nomm.n3 p) := by
  intro sup L th region g0 g1 nex hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr
  by_cases en : noneEquivalentL L = true
  · have hr' := hr
    rw [runLC_n3_next, if_pos en] at hr'
    exact Jp (by simpa only [hinted] using hh) (Or.inl (noneEq_sure en).1) (by simpa only [sixCount] using hcount)
      b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr'
  · exact (lokS_three_run lib env M Sp hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce
      hr).2.2.1.2 (by simpa using en)

end Comp
end SkaModel
end Formalization
