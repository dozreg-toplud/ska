import lemmas.Ska.CompHintReg

/-!
# `RegGBT` closed under `[4 p]` and `[7 p q]` (README Gaps 24.18)

* `collapseL_lazyReg`: `+collapse-lazy-atom` of the goal `lazy-from-reg r`
  is `(r, th.there)` and leaves the state as it was (the sure need is `this
  r` with no look, no entry: the walk visits only `th.there`, where the gate
  does nothing).
* `regGBT_four`: **`[4 p]` under `%next (lazy-from-reg r) th` over a member
  of `RegGBT`** is a member (`unaryGBT_ok` with the goal `%next`: the
  increment block writes `r` and hops to `th`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem toList_emptyR : HoonSet.toList (HoonSet.empty : S) = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x => HoonSet.mem_empty x

/-- **`+collapse-lazy-atom` of the goal `lazy-from-reg r`**: `(r, th.there)`,
the state unchanged. -/
theorem collapseL_lazyReg {rg : Nat} {th : Jmp} (hta : th.args = []) (g : Gen Map) (d0 : g.drop = false) :
    collapseLazyAtomL (S := S) ⟨ofSure (lazyReg rg), th⟩ g = some (some (rg, th.there), g) := by
  have hne : noneEquivalentL (ofSure (lazyReg rg : Sure S)) = false := by
    rw [noneEquivalentL_ofSure]; simp [noneEquivalent, lazyReg]
  unfold collapseLazyAtomL
  simp only [hta, ne_eq, not_true_eq_false, if_false, hne, Bool.false_eq_true]
  simp [sureRequireLook, ofSure, lazyReg, toList_emptyR, bind_apply, pure_apply, walkLazy, collapseGate]
  rfl

theorem jmp0_there {th : Jmp} (hta : th.args = []) : jmp0 th.there = th := by
  cases th; simp_all [jmp0]

section Four
variable {snd : Nomm → NeedOrd → Bool}

/-- **`[4 p]` under `%next (lazy-from-reg r) th` over a member of `RegGBT`
is a member.**  `+collapse-lazy-atom` gives `(r, th.there)` and changes
nothing (`collapseL_lazyReg`); the operand runs under `%next (lazy-from-reg
arg) (jmp0 o)` with `o` the block `[inc arg r] hop th`; `unaryGBT_ok` for
the goal `%next (lazy-from-reg r) th`, whose block writes the increment into
`r` (an atom) or crashes (a cell). -/
theorem regGBT_four {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f fb : Noun} {p : Nomm}
    (Sp : RegGBT (S := S) (Map := Map) snd lib N env P fb p) (M : MinkC4 lib P f fb) :
    RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n4 p) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_n4_next] at hr
  simp only [bind_apply, collapseL_lazyReg hta g0 d0, Option.bind_some, collPick, pure_apply, re_apply,
    emit_apply] at hr
  rw [jmp0_there hta] at hr
  have GU : GrowU g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [Pole.inc g0.re rg], Termin.hop th⟩) :=
    ((grow_re g0).trans (grow_emit (g := { g0 with re := g0.re + 1 }) (jumpsBelow_hop th1 th2))).toU hu
  have RG := Sp (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) (GU.up hu) (hcl.growU GU)
    (CondFresh.below (condFresh_of_eq (g0 := g0)
      (g1 := { g0 with re := g0.re + 1 }.emitted ⟨[], [Pole.inc g0.re rg], Termin.hop th⟩)
      (by simp only [emitted_re]; omega) rfl) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl (by simp [emitted_re])
    (by simp only [Gen.emitted]; exact condBelow_none hcb (Nat.le_refl _)) hr
  have hfin : ∀ P : Nat → Prop, FinIn P (Termin.hop th) := fun P x hx => by rw [hta] at hx; cases hx
  have KA : KeepsA (fun r => HoonMap.get g0.cond r = Option.none) g0
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [Pole.inc g0.re rg], Termin.hop th⟩) :=
    (keepsA_reg _ g0 _ (by romega)).trans (keepsA_emitted d0 (blobIn_one (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact condBelow_none hcb (by romega)
      · exact hc0) (hfin _)))
  have KB : Keeps g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [Pole.inc g0.re rg], Termin.hop th⟩) :=
    (keeps_reg g0 _ (by romega)).trans (keeps_emitted d0 (blobIn_one (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> romega) (hfin _)))
  refine unaryGBT_ok M ((ext_re _).trans (ext_emit _ _)) GU rfl
    ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl) RG
    (fix_of_keeps (gs := g0) rfl KA KB) ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx] at hj
    refine ⟨fun _ => ⟨st, store rg (A (n + 1)) regs, hI, Needs.le_refl _, read_store_eq _ _ _, fun y hy => ?_, ?_⟩,
      fun hf => absurd (fitsS_lazyReg _ _) hf⟩
    · exact read_store_ne (fun e => hy.2 e) _ _
    · rw [hj, execBlob_hop]
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx] at hj
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, hj, ToneRel.two htr⟩

/-- (The text of `unaryGTB_ok`, `CompFourTop.lean`, for `RunOKGBT`.) -/
theorem unaryGTBT_ok {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb : Noun} {T : Trace → Tone → Tone}
    (hT : ∀ tm r, (∀ p, r ≠ Tone.zero p) → T tm r = r)
    (fw : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
      ∃ n', n' ≤ n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧ r = T tm rb)
    (bw : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb → Mink lib gul tm s f (T tm rb))
    {goal : CGoal S} {g0 g' g1 : Gen Map} {a o : Nat} {nexp : NextL S}
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o))
    (hp : RunOKGBT (Map := Map) lib N P fb (CGoal.next (lazyReg a) (jmp0 o)) g' g1 nexp)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x : Noun), Inv st →
      Forall2 (FrameRel lib (ν st)) t tm → SkaModel.read a regs = some x →
      GoalSemCM lib O c gul Inv ν (Keep g0 g' goal) st regs t tm (jmp0 o) goal (T tm (Tone.zero x))) :
    RunOKGBT lib N P f goal g0 g1 nexp := by
  have l1 := hp.ext.1
  have b1 := hp.ext.2.1
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg a : Sure S) (jmp0 o)) tm r → r = Tone.two tm :=
    fun hb => by
      rcases hb with e | ⟨q, _, hq⟩
      · exact e
      · exact absurd (fitsS_lazyReg a q) hq
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm →
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g1 nexp.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
      ∀ regs (rb : Tone),
      GoalSemCM lib O c gul Inv ν (fun x => (x < g'.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg a : Sure S) (jmp0 o)) x)
        st regs t tm nexp.th (CGoal.next (lazyReg a : Sure S) (jmp0 o)) rb →
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nexp.th goal
        (T tm rb) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf k (Nat.lt_of_lt_of_le hk l1)).trans ((hp.cfr.get_lt hk).trans (by rw [hcnd]))
    have agQ : Agree c g0 g' := fun o' h0 h1 => by
      rw [(ag st t).1 o' h0 (Nat.lt_of_lt_of_le h1 b1) (fun hm => ?_)]
      · rw [hp.ext.2.2.2 o' h1]; exact hfix cf hcf0 o' h0 h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (hp.labs e he).1; omega
    cases rb with
    | zero x =>
      obtain ⟨st', R, hI', hle, hR, hk, e1⟩ := G.1 (fitsS_lazyReg a x)
      have hR' : SkaModel.read a R = some x := hR
      have H := hblk c agQ σ Inv ν O gul st' R t tm x hI' (frames_mono hle htr) hR'
      refine goalSemCM_step hle (fun r hr => hk r ⟨?_, ?_⟩) e1 goal _
        (goalSemCM_monoK (fun r hr => ?_) goal _ H)
      · rcases hr.1 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · intro ea
        have ea' : r = a := ea
        subst ea'
        rcases hr.1 with h | h
        · omega
        · have := hned _ h; omega
      · refine ⟨?_, hr.2⟩
        rcases hr.1 with h | h
        · exact Or.inl h
        · have := hned r h; exact Or.inr (by omega)
    | one q =>
      rw [hT tm _ (fun _ e => by cases e)]
      exact goalSemCM_of_returnsC goal _ (fun _ e => by cases e)
        (returnsC_of_goalSemCM _ (Tone.one q) (fun _ e => by cases e) G)
    | two tr =>
      rw [hT tm _ (fun _ e => by cases e)]
      exact goalSemCM_of_returnsC goal _ (fun _ e => by cases e)
        (returnsC_of_goalSemCM _ (Tone.two tr) (fun _ e => by cases e) G)
  have agP : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (st : σ) (t : Trace) (s0 s : Noun), AgreeUB lib O c gul st t cf ned g0 g1 nexp.laz s0 s →
      AgreeUB lib O c gul st t cf ned g' g1 nexp.laz s0 s :=
    fun cf c ned σ O gul st t s0 s ag => ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, (condFresh_of_eq hpre.1 hcnd).trans hp.cfr, hp.lo, hp.hi, ?_,
    fun r hr => ?_, hp.dist, fun e he => ⟨(hp.eregs e he).1, fun r hr => ⟨Or.inr ?_, ((hp.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (hp.labs e he).1; have := hpre.2.1; omega, (hp.labs e he).2⟩, hp.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, hp.ncond, hp.econd, ?_, ?_⟩
  · rcases hp.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]; exact Or.inl (hfr.growU ho hp.grow)
  · rcases hp.regs r hr with h | h
    · have h' : r = a := h
      subst h'; exact Or.inr ⟨ha.1, by omega⟩
    · exact Or.inr ⟨by have := hpre.1; omega, h.2⟩
  · rcases ((hp.eregs e he).2 r hr).1 with h | h
    · have h' : r = a := h
      subst h'; exact ha.1
    · have := hpre.1; omega
  · obtain ⟨n', hn', rb, hb, rfl⟩ := fw hs hm
    rw [bad ((hp.nec s hs hf).1 gul n' tm rb hb), hT tm _ (fun _ e => by cases e)]
    exact Or.inl rfl
  · obtain ⟨rb, hmb, hbad⟩ := (hp.nec s hs hf).2 gul tm
    refine ⟨_, bw hs hmb, ?_⟩
    rw [bad hbad, hT tm _ (fun _ e => by cases e)]
    exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hn', rb, hb, rfl⟩ := fw hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb
      (hp.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb
        (fun st' t' => agP cf c ned σ O gul st' t' s0 s (ag st' t')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rb, hmb, G⟩ := hp.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' t' => agP cf c ned σ O gul st' t' s0 s (ag st' t')) hned regs hh hn res hres
    exact ⟨_, bw hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G⟩

/-! ## The runs of `[3 p]` -/

/-- **`[3 p]` under `%next (lazy-from-reg r) th` over a member of `RegGBT`
is a member.**  `+collapse-lazy-atom` gives `(r, th.there)`, `+forl r
th.there` the two blocks that write `0` or `1` into `r` and hop to `th`,
the `%clq` block at `o` tests the operand's register; `unaryGTBT_ok` with
`wutTone`. -/
theorem regGBT_three {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f fb : Noun} {p : Nomm}
    (Sp : RegGBT (S := S) (Map := Map) snd lib N env P fb p) (M : MinkC3 lib P f fb) :
    RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n3 p) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  have hne : noneEquivalentL (ofSure (lazyReg rg : Sure S)) = false := by
    rw [noneEquivalentL_ofSure]; simp [noneEquivalent, lazyReg]
  rw [runLCH_n3_next, hne] at hr
  simp only [Bool.false_eq_true, if_false, bind_apply, collapseL_lazyReg hta g0 d0, Option.bind_some] at hr
  obtain ⟨⟨⟨z, o'⟩, g2⟩, hf, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨E2, re2, bo2, F⟩ := forl_ok hf hr0
  have Fd := forl_down hf th1 th2 (by omega)
  have c2 : g2.cond = g0.cond := (kc_forl rg th.there).keep g0 _ g2 hf
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  simp only [re_apply, emit_apply, Option.bind_some] at hr
  have G : Grow g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 z) (jmp0 o')⟩) :=
    Fd.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl Fd.2.1 Fd.2.2)))
  have GU := G.toU hu
  have RG := Sp (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) (GU.up hu) (hcl.growU GU)
    (CondFresh.below (condFresh_of_eq (g0 := g0)
      (g1 := { g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 z) (jmp0 o')⟩)
      (by simp only [emitted_re]; omega) c2) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl (by simp [emitted_re])
    (by simp only [Gen.emitted]; rw [c2]; exact condBelow_none hcb (by omega)) hr
  have KA : KeepsA (fun r => HoonMap.get g0.cond r = Option.none) g0
      ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 z) (jmp0 o')⟩) :=
    (keepsA_forl d0 hc0 (fun x hx => condBelow_none hcb hx) hf).trans ((keepsA_reg _ g2 _ (Nat.le_succ _)).trans
      (keepsA_emitted d2 (blobIn_fin ⟨condBelow_none hcb (by omega), jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))
  have KB : Keeps g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 z) (jmp0 o')⟩) :=
    (keeps_forl d0 hr0 hf).trans ((keeps_reg g2 _ (Nat.le_succ _)).trans (keeps_emitted d2
      (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))
  refine unaryGTBT_ok (T := fun _ => wutTone) wutTone_keep M.fwd M.bwd (E2.trans ((ext_re _).trans (ext_emit _ _)))
    GU (by simp only [Gen.emitted]; exact c2) ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d2) rfl rfl) RG (fix_of_keeps (gs := g0) (by omega) KA KB) ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d2) (hc _ (by show g0.bo ≤ g2.bo; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  have F' := F d0 c (hc.left E2 ((ext_re _).trans (ext_emit _ _))) lib σ O st regs t gul
  rw [jmp0_there hta] at F'
  have hk : ∀ y, Keep g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 z) (jmp0 o')⟩)
      (CGoal.next (lazyReg rg : Sure S) th) y → ∀ (k : Nat) (v w : Noun), (k = g0.re ∨ k = g0.re + 1) →
      SkaModel.read y (store rg v (store k w regs)) = SkaModel.read y regs := fun y hy k v w hk' => by
    have h1 : y ≠ rg := fun e => hy.2 e
    have h2 : y ≠ k := fun e => by
      have := hy.1; simp only [emitted_re] at this; rcases hk' with rfl | rfl <;> omega
    rw [read_store_ne h1, read_store_ne h2]
  cases x with
  | atom n =>
    refine ⟨fun _ => ⟨st, _, hI, Needs.le_refl _, read_store_eq _ _ _, fun y hy => hk y hy _ _ _ (Or.inr rfl),
      hj.trans F'.2⟩, fun hf => absurd (fitsS_lazyReg _ _) hf⟩
  | cell u v =>
    refine ⟨fun _ => ⟨st, _, hI, Needs.le_refl _, read_store_eq _ _ _, fun y hy => hk y hy _ _ _ (Or.inl rfl),
      hj.trans F'.1⟩, fun hf => absurd (fitsS_lazyReg _ _) hf⟩

end Four

/-! ## `[7 p q]`: `q` in `RegGBT` with the shape of its result, `p` without a kept hint -/

/-- **A run under `%next (lazy-from-reg r) th` with the shape its parent's
next part needs** (`DoneOKT`'s facts at this goal): `RunOKGBT`, the jump at
no entry, the result flat with clean needs. -/
structure RegOKT (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (rg : Nat) (th : Jmp) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop where
  run : RunOKGBT lib N P f (CGoal.next (lazyReg rg) th) g0 g1 nex
  nent : nex.th.there ∉ (entries nex.laz).map Prod.fst
  flat : Flat nex.laz
  clean : Clean nex.laz.sure.ned
  eclean : ∀ e ∈ entries nex.laz, Clean e.2.sure.ned

/-- **`RegFT`: `RegGBT` with the shape of the result** (`RegOKT`). -/
def RegFT (snd : Nomm → NeedOrd → Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → rg < g0.re → HoonMap.get g0.cond rg = Option.none →
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure (lazyReg rg)) th) region g0 = some (nex, g1) →
    RegOKT lib N P f rg th g0 g1 nex

section Seven
variable {snd : Nomm → NeedOrd → Bool}

theorem RegFT.toReg {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : RegFT (S := S) (Map := Map) snd lib N env P f nm) : RegGBT (S := S) (Map := Map) snd lib N env P f nm :=
  fun b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr => (H b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr).run

/-- **A member of `LOKSFH` is in `RegFT`** (`LOKSH.run`, `LOKSH.clean`). -/
theorem RegFT.of_loksf {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P f nm) (hc : sixCount nm ≤ 255) :
    RegFT (S := S) (Map := Map) snd lib N env P f nm := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  have e0 : entries (ofSure (lazyReg rg : Sure S)) = [] := entries_ofSure _
  obtain ⟨⟨Q, RS⟩, ne, -, fl, ec⟩ := H.run (sup := sup) (L := ofSure (lazyReg rg)) (th := th) (region := region)
    (Or.inr e0) hc b0 d0 hu hcl hcb th1 th2 hta (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨hr0, hc0⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) hr
  exact ⟨(RS.toRunOKLB.toGB (fun x hx => by simp only [lazyReg, NMem] at hx; omega)).toT, ne, fl,
    H.clean (L := ofSure (lazyReg rg)) trivial hr, ec⟩

/-- **`[7 p q]` under `%next (lazy-from-reg r) th`**: `q` in `RegFT` (its
result may have bonds, flat ones), `p` a member of `CallTreeHU` with `x =
true` (no kept hint: `runOKGBT_sevenL` takes `p`'s run as `RunOKLB` under
`q`'s result, the agreement at one trace, from `LOKSH.run` on that flat
lazy goal).  The text of `doneAllT_seven` for this goal. -/
theorem regFT_seven (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {b c : Noun} {p q : Nomm}
    (hp : CallTreeHU lib env N P true b p) (Hq : RegFT (S := S) (Map := Map) snd lib N env (Img lib P b) c q) :
    RegFT (S := S) (Map := Map) snd lib N env P (n3 (A 7) b c) (Nomm.n7 p q) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 h1
  have Rq := D.run
  have Lp := ((lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib (N := N) env hp).2 rfl).1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · simp only [GoalJ] at e; rw [e]; exact hta
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
    (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · have := Rq.ext.1; simp only [GMem, lazyReg, NMem] at e; omega
      · exact e.2, Rq.ncond x hx⟩)
    (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
    (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
    D.flat D.clean D.eclean h2
  exact ⟨runOKGBT_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB
    (fun r hr => by simp only [GMem, lazyReg, NMem] at hr; omega), hne, hfl, Lp.clean (L := nx.laz) D.clean h2, hec⟩

end Seven

end Comp
end SkaModel
end Formalization
