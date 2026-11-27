import lemmas.Ska.CompHintRegOps

/-!
# Kept static hints and quiet dynamic tags in `RegGBT` (README Gaps 24.18)

* `RunOKGBT.minkAs`, `RunOKGBT.quietFront`, `RunOKGBT.quietGoal`: the texts
  of `RunOKGB.minkAs` (`CompHintTop.lean`), `RunOKGB.quietFront`,
  `RunOKGB.quietGoal` (`CompHintKeep.lean`) for `RunOKGBT`.
* `runLCH_n11s_kept_next`, **`regGBT_n11sKept`**: a kept static hint
  (`%bout`, `%xray`) over a member of `RegGBT` is a member (the formula's
  `RunOKGBT` behind the block of `+lazy-bound`, `RunOKGBT.bound`, then the
  quiet prologue and epilogue).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- (The text of `RunOKGB.minkAs` for `RunOKGBT`.) -/
theorem RunOKGBT.minkAs {lib : Lib} {N : Needs} {P : Noun → Prop} {f f' : Noun} {goal : CGoal S}
    {g0 g1 : Gen Map} {nex : NextL S} (M : MinkAs lib f' f) (R : RunOKGBT lib N P f goal g0 g1 nex) :
    RunOKGBT lib N P f' goal g0 g1 nex where
  ext := R.ext
  grow := R.grow
  cfr := R.cfr
  lo := R.lo
  hi := R.hi
  ent := R.ent
  regs := R.regs
  dist := R.dist
  eregs := R.eregs
  labs := R.labs
  nodup := R.nodup
  nec := fun s hs hfit => by
    obtain ⟨h1, h2⟩ := R.nec s hs hfit
    refine ⟨fun gul n tm r h => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', -, h'⟩ := M.fwd h
      exact h1 gul n' tm r h'
    · obtain ⟨r, hm, hb⟩ := h2 gul tm
      exact ⟨r, M.bwd hm, hb⟩
  ncond := R.ncond
  econd := R.econd
  sem := fun cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI ht hP hm => by
    obtain ⟨n', hn, h'⟩ := M.fwd hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn) st t tm s0 s r hI ht hP h'
  semB := fun cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg => by
    obtain ⟨r, hm, hg'⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI ht hP hA hre regs hs hn res hg
    exact ⟨r, M.bwd hm, hg'⟩

section Blocks
variable {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun}

/-- (The text of `RunOKGB.quietFront` for `RunOKGBT`.) -/
theorem RunOKGBT.quietFront {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKGBT lib N P f goal g0 g1 nex) {p : Pole} (hp : QuietP p) (hta : nex.th.args = [])
    (d1 : g1.drop = false) (u1 : UpBelow g1) :
    RunOKGBT lib N P f goal g0 (g1.emitted ⟨[], [p], Termin.hop nex.th⟩) ⟨nex.laz, jmp0 g1.bo⟩ := by
  have hb := hk_emitted_self d1 (⟨[], [p], Termin.hop nex.th⟩ : Blob)
  have lt1 : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => (R.labs e he).2.1
  have agr : ∀ {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
      (cf : Map (Nat × List Nat)) (ned : Need) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g0 (g1.emitted ⟨[], [p], Termin.hop nex.th⟩) nex.laz s0 s →
      AgreeUB lib O c gul st t cf ned g0 g1 nex.laz s0 s ∧
        HoonMap.get c.blocks g1.bo = some ⟨[], [p], Termin.hop nex.th⟩ := by
    intro σ O c gul st t cf ned s0 s ag
    refine ⟨⟨fun o h0 h1 hn => ?_, fun e he => ?_⟩, ?_⟩
    · rw [ag.1 o h0 (by simp only [Gen.emitted]; omega) hn, hk_emitted_ne _ (by omega)]
    · obtain ⟨A, B, th, h1, h2, h3⟩ := ag.2 e he
      rw [hk_emitted_ne _ (Nat.ne_of_lt (lt1 e he))] at h1
      exact ⟨A, B, th, h1, h2, h3⟩
    · rw [ag.1 g1.bo R.ext.2.1 (by simp only [Gen.emitted]; omega) (fun hm => by
        obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
        have := lt1 e he; omega), hb]
      simp only [Option.map_some, unproxyBlob_quiet hp hta]
  refine ⟨R.ext.trans (ext_emit _ _), R.grow.trans (growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨R.lo, R.hi⟩) u1),
    R.cfr.trans (condFresh_of_eq (Nat.le_refl _) rfl), by have := R.lo; have := R.hi; simp only [jmp0]; omega,
    by simp only [jmp0, Gen.emitted]; omega, Or.inl ⟨_, hb, rfl, rfl⟩, R.regs, R.dist, R.eregs,
    fun e he => ⟨(R.labs e he).1, by have := (R.labs e he).2.1; simp only [Gen.emitted]; omega, by
      rw [hk_emitted_ne _ (Nat.ne_of_lt (lt1 e he))]; exact (R.labs e he).2.2⟩,
    R.nodup, R.nec, R.ncond, R.econd, ?_, ?_⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have A := fun st' t' => agr O c gul st' t' cf ned s0 s (ag st' t')
    exact goalSemCM_of_goJ (goJ_quiet hp (A st t).2 st regs t)
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm (fun st' t' => (A st' t').1) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have A := fun st' t' => agr O c gul st' t' cf ned s0 s (ag st' t')
    rw [goJ_quiet hp (A st t).2 st regs t] at hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs (fun st' t' => (A st' t').1)
      hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_of_goJ (goJ_quiet hp (A st t).2 st regs t) G⟩

/-- (The text of `RunOKGB.quietGoal` for `RunOKGBT`.) -/
theorem RunOKGBT.quietGoal {sur : Sure S} {th : Jmp} {g g' : Gen Map} {nex : NextL S} {p : Pole} (hp : QuietP p)
    (hu : UpBelow g) (d : g.drop = false) (h1 : 1 ≤ th.there) (h2 : th.there < g.bo) (hta : th.args = [])
    (R : RunOKGBT lib N P f (CGoal.next sur (jmp0 g.bo)) (g.emitted ⟨[], [p], Termin.hop th⟩) g' nex) :
    RunOKGBT lib N P f (CGoal.next sur th) g g' nex := by
  have hb' : HoonMap.get g'.blocks g.bo = some ⟨[], [p], Termin.hop th⟩ := by
    rw [R.ext.2.2.2 g.bo (by simp only [Gen.emitted]; omega)]; exact hk_emitted_self d _
  have nlab : ∀ e ∈ entries nex.laz, g.bo < e.1 := fun e he => by
    have := (R.labs e he).1; simp only [Gen.emitted] at this; omega
  have blk : ∀ {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
      (cf : Map (Nat × List Nat)) (ned : Need) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g g' nex.laz s0 s →
      HoonMap.get c.blocks g.bo = some ⟨[], [p], Termin.hop th⟩ := by
    intro σ O c gul st t cf ned s0 s ag
    rw [ag.1 _ (Nat.le_refl _) (by have := R.ext.2.1; simp only [Gen.emitted] at this; omega) (fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := nlab e he; omega), hb']
    simp only [Option.map_some, unproxyBlob_quiet hp hta]
  have agp : ∀ {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
      (cf : Map (Nat × List Nat)) (ned : Need) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g g' nex.laz s0 s →
      AgreeUB lib O c gul st t cf ned (g.emitted ⟨[], [p], Termin.hop th⟩) g' nex.laz s0 s :=
    fun O c gul st t cf ned s0 s ag => ⟨fun o h0' h1 hn => ag.1 o (by simp only [Gen.emitted] at h0'; omega) h1 hn, ag.2⟩
  refine ⟨(ext_emit _ _).trans R.ext, (growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨h1, h2⟩) hu).trans R.grow,
    (condFresh_of_eq (Nat.le_refl _) rfl).trans R.cfr, R.lo, R.hi, ?_, R.regs, R.dist, R.eregs,
    fun e he => ⟨by have := nlab e he; omega, (R.labs e he).2⟩, R.nodup, R.nec, R.ncond, R.econd, ?_, ?_⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, hb', rfl, rfl⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact goalSemCM_next_hop (fun st' regs' => goJ_quiet hp (blk O c gul st t cf ned s0 s (ag st t)) st' regs' t)
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
        (fun st' t' => agp O c gul st' t' cf ned s0 s (ag st' t')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' t' => agp O c gul st' t' cf ned s0 s (ag st' t')) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_next_hop
      (fun st' regs' => goJ_quiet hp (blk O c gul st t cf ned s0 s (ag st t)) st' regs' t) G⟩

end Blocks

section Static
variable {snd : Nomm → NeedOrd → Bool}

/-- **The run of a kept static hint under `%next (lazy-from-reg rg) th`**,
when `+sound` of `%this` holds for the formula: the epilogue `[hse tag
body] hop th` at `bo`, the formula under `%next (lazy-from-reg rg) (jmp0
bo)`, the block of `+lazy-bound`, the prologue `[hsp tag body]`. -/
theorem runLCH_n11s_kept_next {env : CallEnv} {tag : Nat} (hs : hintStatic tag = true) {q : Nomm} {body : Noun}
    (hsnd : snd q NeedOrd.this = true) {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S}
    (hr : runLCH env snd true sup (Nomm.n11s tag q body) (CGoalL.next (ofSure (lazyReg rg)) th) region g0 =
      some (nex, g1)) :
    ∃ nq gc, runLCH env snd true sup q (CGoalL.next (ofSure (lazyReg rg)) (jmp0 g0.bo)) region
        (g0.emitted ⟨[], [Pole.hse tag body], Termin.hop th⟩) = some (nq, gc) ∧
      nq.th.args = [] ∧
      nex = ⟨mk Sure.bunt [] [(gc.bo, nq.laz)], jmp0 (gc.bo + 1)⟩ ∧
      g1 = ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hsp tag body], Termin.hop (jmp0 gc.bo)⟩ := by
  simp only [runLCH, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
  obtain ⟨n0, ga, h0, hr⟩ := bind_some hr
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨n1, gb, h1, hr⟩ := bind_some hr
  have hp : HoonSet.small (ofSure (lazyReg rg) : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure (lazyReg rg) : Lazy S).sure.ned) = true :=
    ⟨(HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x), hsnd⟩
  unfold pastIfL at h1
  rw [if_pos hp] at h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨ep, gb', h2, hr⟩ := bind_some hr
  rw [emit_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨nq, gc, h3, hr⟩ := bind_some hr
  obtain ⟨nb, gd, h4, hr⟩ := bind_some hr
  have hta : nq.th.args = [] := by
    cases hne : nq.th.args with
    | nil => rfl
    | cons a l =>
      unfold lazyBound at h4
      simp [bind_apply, emit_apply, setTag_apply, hne] at h4
  rw [lazyBound_apply hta] at h4
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨rfl, rfl⟩ := h4
  obtain ⟨pr, ge, h5, hr⟩ := bind_some hr
  rw [emit_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  refine ⟨nq, gc, h3, hta, ?_, ?_⟩
  · simp [Gen.emitted]
  · rfl

/-- **A kept static hint over a member of `RegGBT` is a member** (`+sound`
of `%this` for the formula, so `+past-if` emits nothing): the formula's
`RunOKGBT` under `%next (lazy-from-reg rg) (jmp0 epil)`, the block of
`+lazy-bound` behind it (`RunOKGBT.bound`, any result), the quiet prologue
(`quietFront`), the quiet epilogue to `th` (`quietGoal`), and `+mink` runs
`[11 tag fq]` as `fq` (`minkAs_n11s`).  Nested at any depth, the formula
may be a kept hint. -/
theorem regGBT_n11sKept {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fq : Noun} {q : Nomm}
    (Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)
    {tag : Nat} (hs : hintStatic tag = true) (body : Noun) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 11) (A tag) fq) (Nomm.n11s tag q body) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  obtain ⟨nq, gc, h3, hqa, rfl, rfl⟩ := runLCH_n11s_kept_next hs hsnd hr
  have GE : GrowU g0 (g0.emitted ⟨[], [Pole.hse tag body], Termin.hop th⟩) :=
    growU_emit (fun j hj => by simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨th1, th2⟩) hu
  have RQ := Hq (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (GE.up hu) (hcl.growU GE)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl (by simp only [Gen.emitted]; omega)
    (by simp only [Gen.emitted]; exact hc0) h3
  have dc : gc.drop = false := RQ.ext.2.2.1.trans d0
  have uc : UpBelow gc := RQ.grow.up (GE.up hu)
  have RG := RQ.bound (fun x hx => by simp only [lazyReg, NMem] at hx; simp only [Gen.emitted]; omega) hqa dc uc region
  have dd : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).drop = false := by
    simp only [tagged_drop, Gen.emitted]; exact dc
  have RF := RG.quietFront (p := Pole.hsp tag body) trivial rfl dd (RG.grow.up (GE.up hu))
  have ebo : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).bo = gc.bo + 1 := by
    simp only [tagged_bo, Gen.emitted]
  rw [ebo] at RF
  exact (RF.quietGoal (p := Pole.hse tag body) trivial hu d0 th1 th2 hta).minkAs (minkAs_n11s lib tag fq)

end Static

/-! ## Kept dynamic tags that push nothing (`%slog`, `%xray`: not `stopTag`) -/

section QuietExec
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
  {Inv : σ → Prop} {ν : σ → Needs}

theorem minkF_n11d_quiet (lib : Lib) (gul : Noun) (n : Nat) (tm : Trace) (s : Noun) {tag : Nat}
    (hst : stopTag tag = false) (fh f : Noun) :
    minkF lib gul (n + 1) tm s (n3 (A 11) (C (A tag) fh) f) =
      tbind (minkF lib gul n tm s fh) fun _ => minkF lib gul n tm s f := by
  rw [minkF_n11d_any]; simp only [hst, Bool.false_eq_true, if_false, tbind_zero_id]

theorem mink_n11d_quiet {lib : Lib} {gul : Noun} {tm : Trace} {s : Noun} {tag : Nat} (hst : stopTag tag = false)
    {fh f : Noun} {v : Noun} {r : Tone} (hh : Mink lib gul tm s fh (Tone.zero v))
    (hf : Mink lib gul tm s f r) : Mink lib gul tm s (n3 (A 11) (C (A tag) fh) f) r := by
  obtain ⟨n1, e1⟩ := hh
  obtain ⟨n2, e2⟩ := hf
  refine ⟨max n1 n2 + 1, ?_⟩
  rw [minkF_n11d_quiet lib gul _ tm s hst, minkF_le lib gul (Nat.le_max_left n1 n2) _ _ _ _ e1]
  exact minkF_le lib gul (Nat.le_max_right n1 n2) _ _ _ _ e2

theorem mink_n11d_clueQ {lib : Lib} {gul : Noun} {tm : Trace} {s : Noun} {tag : Nat} (hst : stopTag tag = false)
    {fh f : Noun} {r : Tone} (hh : Mink lib gul tm s fh r) (hr : ∀ q, r ≠ Tone.zero q) :
    Mink lib gul tm s (n3 (A 11) (C (A tag) fh) f) r := by
  obtain ⟨n1, e1⟩ := hh
  refine ⟨n1 + 1, ?_⟩
  rw [minkF_n11d_quiet lib gul _ tm s hst, e1]
  rcases r with q | b | tr
  · exact absurd rfl (hr q)
  · rfl
  · rfl

/-- The blocks of a kept dynamic tag that is not `stopTag`. -/
def FrameOKQ (c : Straight Map) (tag toke : Nat) (body : Noun) (prol o epil : Nat) (th : Jmp) : Prop :=
  stopTag tag = false ∧
  HoonMap.get c.blocks prol = some ⟨[], [Pole.hdp tag toke body], Termin.hop (jmp0 o)⟩ ∧
  HoonMap.get c.blocks epil = some ⟨[], [Pole.hde tag toke body], Termin.hop th⟩

/-- **The quiet frame**: the prologue and the epilogue are hops at the same
trace (`goJ_hdp_quiet`, `goJ_hde_quiet`). -/
theorem frameOKQ_goes {tag toke : Nat} {body : Noun} {prol o epil : Nat} {th : Jmp}
    (F : FrameOKQ c tag toke body prol o epil th) {sur : Sure S} {K : Nat → Prop} {st : σ}
    {regs : Map (Option Noun)} {t tm : Trace} {r : Tone}
    (G : GoalSemCM lib O c gul Inv ν K st regs t tm (jmp0 o) (CGoal.next sur (jmp0 epil)) r) :
    GoalSemCM lib O c gul Inv ν K st regs t tm (jmp0 prol) (CGoal.next sur th) r :=
  goalSemCM_of_goJ (goJ_hdp_quiet F.1 F.2.1 st regs t)
    (goalSemCM_next_hop (fun st' regs' => goJ_hde_quiet F.1 F.2.2 st' regs' t) G)

end QuietExec

section Quiet
variable {snd : Nomm → NeedOrd → Bool}

/-- **A kept dynamic tag that is not `stopTag` over a member of `RegGBT` is
a member** (the text of `regGBT_n11dKept` with the quiet frame: the formula
runs at the hint's own trace, `frameOKQ_goes`). -/
theorem regGBT_n11dQuiet {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fh fq : Noun} {h q : Nomm}
    (Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = false) (body : Noun) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 11) (C (A tag) fh) fq) (Nomm.n11d tag h q body) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  obtain ⟨nq, gc, nh, gh, h3, hqa, h6, h7⟩ := runLCH_n11d_kept_next hs hsnd hr
  have e0 : ∀ r, entries (ofSure (lazyReg r : Sure S)) = [] := fun r => entries_ofSure _
  -- the state after `toke` and the epilogue
  have dA : (genN g0 tag body th).drop = false := d0
  have reA : (genN g0 tag body th).re = g0.re + 1 := rfl
  have boA : (genN g0 tag body th).bo = g0.bo + 1 := rfl
  have bA : ∀ k, HoonMap.get (genN g0 tag body th).blocks k =
      if k = g0.bo then some ⟨[], [Pole.hde tag g0.re body], Termin.hop th⟩ else HoonMap.get g0.blocks k := by
    intro k; simp only [genN, Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have GA : GrowU g0 (genN g0 tag body th) := (growU_re g0 _).trans
    (growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [Pole.hde tag g0.re body], Termin.hop th⟩)
      (fun j hj => by simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨th1, th2⟩) hu)
  have uA : UpBelow (genN g0 tag body th) := GA.up hu
  have clA : Clear (genN g0 tag body th) := hcl.growU GA
  have cbA : CondBelow (genN g0 tag body th) := fun k hk => by
    have := hcb k hk; simp only [genN, Gen.emitted] at this ⊢; omega
  have extA : Ext g0 (genN g0 tag body th) := ⟨by rw [reA]; omega, by rw [boA]; omega, dA.trans d0.symm,
    fun o ho => by rw [bA, if_neg (by omega)]⟩
  have ctoke : HoonMap.get g0.cond g0.re = Option.none := condBelow_none hcb (Nat.le_refl _)
  -- the formula, its bond
  have RQ := Hq (by rw [boA]; omega) dA uA clA cbA (by simp only [jmp0]; omega) (by simp only [jmp0]; rw [boA]; omega)
    rfl (by rw [reA]; omega) (by simp only [genN, Gen.emitted]; exact hc0) h3
  have dc : gc.drop = false := RQ.ext.2.2.1.trans dA
  have uc : UpBelow gc := RQ.grow.up uA
  have RG := RQ.bound (fun x hx => by simp only [lazyReg, NMem] at hx; rw [reA]; omega) hqa dc uc region
  have nql : ∀ e ∈ entries nq.laz, g0.bo + 1 ≤ e.1 ∧ e.1 < gc.bo := fun e he =>
    ⟨by have := (RQ.labs e he).1; rw [boA] at this; exact this, (RQ.labs e he).2.1⟩
  have boD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).bo = gc.bo + 1 := by
    simp only [tagged_bo, Gen.emitted]
  have dD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).drop = false := by
    simp only [tagged_drop, Gen.emitted]; exact dc
  have rcA : g0.re + 1 ≤ gc.re := by have := RG.ext.1; simp only [reA, tagged_re, Gen.emitted] at this; exact this
  have bcA : g0.bo + 1 ≤ gc.bo := by have := RQ.ext.2.1; rw [boA] at this; exact this
  -- the prologue
  have GE : GrowU ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
      (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, boD]; omega) (RG.grow.up uA)
  have uE := GE.up (RG.grow.up uA)
  have clE := (clA.growU RG.grow).growU GE
  have cbE : CondBelow (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩) := RG.cfr.below cbA
  have ctD : HoonMap.get ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).cond g0.re = Option.none := by
    rw [RG.cfr.get_lt (by rw [reA]; omega)]; exact ctoke
  -- the clue
  obtain ⟨⟨Qh, RSh⟩, -, -, hflh, -⟩ := Hh.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 (gc.bo + 1))
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
      ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩) g1 := RGh.ext.trans E1
  have ED1 : Ext ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 := (ext_emit _ _).trans EE1
  have EA1 : Ext (genN g0 tag body th) g1 := RG.ext.trans ED1
  have CF1 : CondFresh ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 :=
    (condFresh_of_eq (Nat.le_refl _) rfl).trans (RGh.cfr.trans (condFresh_of_eq (by omega) c1))
  have CFA1 : CondFresh (genN g0 tag body th) g1 := RG.cfr.trans CF1
  have GG : Grow gh g1 := Grow.congr_right (grow_emit (g := gh) (b := ⟨[], [], Termin.hop nh.th⟩) (fun j hj => by
    simp [finJumps] at hj; subst hj; exact ⟨RGh.lo, RGh.hi⟩)) b1 (by rw [d1, emitted_drop, dh]) k1
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = (gc.bo, nq.laz) :: entries nq.laz :=
    entries_bound1 _ _ _
  have hent' : entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) = (gc.bo, nq.laz) :: entries nq.laz := entries_bound1 _ _ _
  have hentN : entries nh.laz = [] := by rw [entries_flat hflh, hbh]
  have hmem : ∀ e, e ∈ entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) → e ∈ entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) := fun e he => by
    rw [hent]; rw [hent'] at he; exact he
  have hnot : ∀ o, o ≠ gc.bo → (o < g0.bo + 1 ∨ gc.bo ≤ o) →
      o ∉ (entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ []
        [(gc.bo, nq.laz)] : Lazy S)).map Prod.fst := fun o ho hlt hm => by
    rw [hent', List.map_cons, List.mem_cons] at hm
    rcases hm with hm | hm
    · exact ho hm
    · obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := nql e he; omega
  -- the blocks in the program
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      HoonMap.get c.blocks gh.bo = some ⟨[], [], Termin.hop nh.th⟩ ∧
      FrameOKQ c tag g0.re body (gc.bo + 1) gc.bo g0.bo th := by
    intro cf hcf c ned σ O gul st t s0 s ag
    have ct : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by omega), CFA1.get_lt (by rw [reA]; omega)]; exact ctoke
    have bE : HoonMap.get g1.blocks (gc.bo + 1) =
        some ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩ := by
      rw [EE1.2.2.2 _ (by simp only [Gen.emitted, tagged_bo]; omega), ← boD]; exact hk_emitted_self dD _
    refine ⟨?_, ⟨hst, ?_, ?_⟩⟩
    · rw [ag.1 gh.bo (by omega) (by omega) (hnot _ (by omega) (Or.inr (by omega))), hb1, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp_nil _ hargs]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega) (Or.inr (by omega))), bE]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp, jmp0, unproxy_none ct]
    · rw [ag.1 _ (Nat.le_refl _) (by omega) (hnot _ (by omega) (Or.inl (by omega))),
        EA1.2.2.2 _ (by rw [boA]; omega), bA, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp_nil _ hta, unproxy_none ct]
  have agh : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩) gh nh.laz s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      simp only [Gen.emitted, tagged_bo] at h0
      rw [ag.1 o (by omega) (by omega) (hnot o (by omega) (Or.inr (by omega))), hb1, if_neg (by omega)],
     fun e he => by rw [hentN] at he; cases he⟩
  have agq : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (genN g0 tag body th) ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
        (mk Sure.bunt [] [(gc.bo, nq.laz)]) s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      rw [ag.1 o (by rw [boA] at h0; omega) (by have := ED1.2.1; omega) (by rw [hent']; rw [hent] at hn; exact hn),
        ED1.2.2.2 o h1],
     fun e he => by
      obtain ⟨A, B, th', a1, a2, a3⟩ := ag.2 e (by rw [hent']; rw [hent] at he; exact he)
      have l2 := (RG.labs e he).2.1
      exact ⟨A, B, th', by rw [← ED1.2.2.2 e.1 l2]; exact a1, a2, a3.mono (by have := ED1.1; omega)⟩⟩
  -- the kept registers across the clue
  have hkc : ∀ (ned : Need) (regs regs1 : Map (Option Noun)), (∀ x, NMem ned x → g1.re ≤ x) →
      (∀ x, ((x < (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩).re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next (lazyReg g0.re : Sure S) (jmp0 (gc.bo + 1))) x) →
        SkaModel.read x regs1 = SkaModel.read x regs) →
      ∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg rg : Sure S) th) x) →
        SkaModel.read x regs1 = SkaModel.read x regs := fun ned regs regs1 hned hk1 x ⟨a, b⟩ =>
    hk1 x ⟨a.imp (fun h => by simp only [Gen.emitted, tagged_re]; omega) id, fun hg => by
      simp only [GMem, lazyReg, NMem] at hg
      rcases a with a | a
      · omega
      · have := hned x a; omega⟩
  have hKm : ∀ (ned : Need) x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg rg : Sure S) th) x) →
      ((x < (genN g0 tag body th).re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg rg : Sure S) (jmp0 g0.bo)) x) :=
    fun ned x ⟨a, b⟩ => ⟨a.imp (fun h => by rw [reA]; omega) id, fun hg => b (by simpa [GMem] using hg)⟩
  refine ⟨extA.trans EA1, GA.trans (RG.grow.trans (GE.trans (RGh.grow.trans (GG.toU (RGh.grow.up uE))))),
    (condFresh_of_eq (g0 := g0) (g1 := genN g0 tag body th) (by rw [reA]; omega) rfl).trans CFA1,
    by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨_, by simp only [jmp0]; rw [hb1, if_pos rfl], rfl, rfl⟩,
    fun r hr => Or.inr ?_, RGh.dist, fun e he => ?_, fun e he => ?_, ?_, fun s hs hf => ?_,
    fun r hr => by rw [c1]; exact RGh.ncond r hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases RGh.regs r hr with h | h
    · simp only [GMem, lazyReg, NMem] at h; subst h; constructor <;> omega
    · simp only [Gen.emitted, tagged_re] at h; constructor <;> omega
  · have he' := hmem e he
    refine ⟨(RG.eregs e he').1, fun r hr => ?_⟩
    have := (RG.eregs e he').2 r hr
    refine ⟨this.1.imp (fun h => by simpa [GMem] using h) (fun h => by rw [reA] at h; omega), ?_⟩
    have := this.2; simp only [tagged_re, Gen.emitted] at this; omega
  · have he' := hmem e he
    obtain ⟨l1, l2, B, th', hB⟩ := RG.labs e he'
    exact ⟨by rw [boA] at l1; omega, by have := ED1.2.1; omega, B, th', by rw [ED1.2.2.2 e.1 l2]; exact hB⟩
  · rw [hent', List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := nql e he; simp at ee; omega, RQ.nodup⟩
  · have hf' : ¬ FitsS nh.laz.sure s := fun hf2 => hf ⟨hf2.1, (looks_uni _ _ _).mpr ⟨hf2.2, looks_empty _⟩⟩
    have NC := RGh.nec s hs hf'
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · cases n with
      | zero => rw [minkF_zero_fuel] at hm; cases hm
      | succ m =>
        rw [minkF_n11d_quiet lib gul m tm s hst] at hm
        cases hmh : minkF lib gul m tm s fh with
        | none => rw [hmh] at hm; cases hm
        | some rh =>
          have := badC_lazyReg (NC.1 gul m tm rh hmh); subst this
          rw [hmh] at hm; simp only [tbind] at hm; cases hm
          exact Or.inl rfl
    · obtain ⟨rh, hm, hb⟩ := NC.2 gul tm
      have := badC_lazyReg hb; subst this
      exact ⟨_, mink_n11d_clueQ hst hm (fun q => by simp), Or.inl rfl⟩
  · have he' := hmem e he
    rw [CF1.get_lt ((RG.eregs e he').2 r hr).2]; exact RG.econd e he' r hr
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hcp, F⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th := fun st regs => by
      rw [goJ_jmp0 _ _ _ _ hcp, execBlob_hop]
    cases n with
    | zero => rw [minkF_zero_fuel] at hm; cases hm
    | succ m =>
      rw [minkF_n11d_quiet lib gul m tm s hst] at hm
      cases hmh : minkF lib gul m tm s fh with
      | none => rw [hmh] at hm; cases hm
      | some rh =>
        rw [hmh] at hm
        have Gh := RGh.sem cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O m gul hN hS
          (oracleFwd_le hF (Nat.le_succ m)) st t tm s0 s rh
          hI htr hs hmh (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
          ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn
        cases rh with
        | zero v =>
          simp only [tbind] at hm
          obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_lazyReg _ v)
          have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
            simp only [GMem, lazyReg, NMem] at hg; have := hned x hx; omega⟩)
          have Gq := RG.sem cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν O m gul
            hN hS (oracleFwd_le hF (Nat.le_succ m)) st1 t tm s0 s r hI1
            (frames_mono hle1 htr) hs hm (fun st' t' => agq (ag st' t'))
            (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
          exact goalSemCM_step hle1 (hkc ned regs regs1 hned hk1) (by rw [ecopy, e1]) _ _
            (goalSemCM_monoK (hKm ned) _ _ (frameOKQ_goes F Gq))
        | one b =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
        | two tr =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hcp, F⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
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
      rw [e1, goJ_hdp_quiet hst F.2.1 st1 regs1 t] at hres
      obtain ⟨r, hmq, Gq⟩ := RG.semB cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν
        O gul hN hS hB st1 t tm s0 s hI1
        (frames_mono hle1 htr) hs (fun st' t' => agq (ag st' t'))
        (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
        res hres
      exact ⟨r, mink_n11d_quiet hst hmh hmq, goalSemCM_step hle1 (hkc ned regs regs1 hned hk1) (by rw [ecopy, e1]) _ _
        (goalSemCM_monoK (hKm ned) _ _ (frameOKQ_goes F Gq))⟩
    | one b =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clueQ hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | two tr =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clueQ hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩

end Quiet

section QuietTop
variable {snd : Nomm → NeedOrd → Bool}

/-- **A quiet kept dynamic tag under `%done`** (the text of `n11dKept_doneR`). -/
theorem n11dQuiet_doneR {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fh fq : Noun} {h q : Nomm}
    (Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = false) (body : Noun)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH env snd true sup (Nomm.n11d tag h q body) CGoalL.done region g0 = some (nex, g1)) :
    RunOKGBT lib N P (n3 (A 11) (C (A tag) fh) fq) (CGoal.done : CGoal S) g0 g1 nex := by
  rw [runLCH_n11d_done_next hs] at hr
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have GA := (growU_re g0 _).trans G1
  have R := regGBT_n11dQuiet (S := S) (Map := Map) Hq hsnd Hh hch hnh hs hst body (by simp [Gen.emitted])
    (by simpa [Gen.emitted] using d0) (GA.up hu) (hcl.growU GA)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl (by simp [Gen.emitted])
    (by simp only [Gen.emitted]; exact condBelow_none hcb (Nat.le_refl _)) hr
  exact runOKGBT_done hu hcb (by rw [R.ext.2.2.2 _ (by simp [Gen.emitted])]; exact hk_emitted_self d0 _) R

/-- **The contract of a quiet kept dynamic tag at the top**, both halves,
traces included. -/
theorem finishLUCH_contractN11dQuietR (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {fh fq : Noun}
    {h q : Nomm} (Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = false) (body : Noun) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd (Nomm.n11d tag h q body) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 11) (C (A tag) fh) fq) [s] c ∧
        ContractBwd lib N s (n3 (A 11) (C (A tag) fh) fq) [s] c :=
  finishLUCH_contractGBT lib N (fun hr => n11dQuiet_doneR Hq hsnd Hh hch hnh hs hst body (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc

end QuietTop

end Comp
end SkaModel
end Formalization
