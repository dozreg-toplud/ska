import lemmas.Ska.CompHintSpot

/-!
# Kept hints under `%next (lazy-from-reg r)`, nested (README Gaps 24.17)

* `RunOKGBT.bound`: **the block of `+lazy-bound` behind a run with
  `RunOKGBT`**, for any result `nex` (bonds and forks of `nex.laz` kept
  inside the one new bond).  The entries of `mk bunt [] [(o, L)]` are
  `(o, L) :: entries L` (`entries_bound1`), and the relation reads an entry
  through its label and its sure need only, so no congruence with `+past`'s
  shape is needed.
* `runOKGBT_of_next`, `runOKGBT_done`: the texts of `runOKGB_of_next`,
  `runOKGB_done` (`CompCallTreeTop.lean`) for `RunOKGBT`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The entries of the result of `+lazy-bound`. -/
theorem entries_bound1 (s : Sure S) (o : Nat) (l : Lazy S) :
    entries (mk s [] [(o, l)]) = (o, l) :: entries l := by
  simp [entries, bondEntries, forkEntries]

/-- **The block of `+lazy-bound` behind a run with `RunOKGBT`** under
`%next sur th0` (the goal's registers below `g0.re`): the result `nex` is
parked whole in one bond behind a new block `g1.bo` whose code is
`hop nex.th`; at run time the program's block there is the fill `A` of
`nex.laz.sure`, then the jump.  `nex.laz` may have bonds and forks: they
are entries of the new result too. -/
theorem RunOKGBT.bound {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th0 : Jmp}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKGBT lib N P f (CGoal.next sur th0) g0 g1 nex)
    (hgl : ∀ r, NMem sur.ned r → r < g0.re) (thn : nex.th.args = []) (d1 : g1.drop = false)
    (u1 : UpBelow g1) (region : List Nat) :
    RunOKGBT lib N P f (CGoal.next sur th0) g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
      ⟨Lazy.mk Sure.bunt [] [(g1.bo, nex.laz)], jmp0 g1.bo⟩ := by
  have hb : ∀ k, HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [tagged_blocks, Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G1 : GrowU g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩) (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨R.lo, R.hi⟩) u1).trans (growU_tagged _ _ _)
  have hent := entries_bound1 (Sure.bunt : Sure S) g1.bo nex.laz
  have mem : ∀ e, e ∈ entries (Lazy.mk (Sure.bunt : Sure S) [] [(g1.bo, nex.laz)]) ↔
      e = (g1.bo, nex.laz) ∨ e ∈ entries nex.laz := fun e => by
    rw [hent, List.mem_cons]
  have lt1 : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => (R.labs e he).2.1
  have re1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re = g1.re := by
    simp [Gen.emitted]
  have bo1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).bo = g1.bo + 1 := by
    simp [Gen.emitted]
  have cd1 : ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond = g1.cond := by
    rw [tagged_cond]; rfl
  have E1 : Ext g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (ext_emit _ _).trans (ext_tagged _ _ _)
  have hcfE : ∀ (cf : Map (Nat × List Nat)),
      (∀ k, k < ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re →
        HoonMap.get cf k = HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).cond k) →
      ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun cf hcf k hk => by
    rw [hcf k (by rw [re1]; exact hk), cd1]
  -- the block of `+lazy-bound`, the agreement of the run's result
  have core : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun),
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0
        ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
        (Lazy.mk (Sure.bunt : Sure S) [] [(g1.bo, nex.laz)]) s0 s) →
      (∀ x, NMem ned x → ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).re ≤ x) →
      ∀ (st : σ) (regs : Map (Option Noun)), HoldsN ned regs s0 →
      (∀ (st' : σ) (t' : Trace), AgreeUB lib O c gul st' t' cf ned g0 g1 nex.laz s0 s) ∧ (∀ x, NMem ned x → g1.re ≤ x) ∧
      (FitsS nex.laz.sure s → ∃ R', HoldsS nex.laz.sure R' s ∧ HoldsN ned R' s0 ∧
        (∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th0) x) → SkaModel.read x R' = SkaModel.read x regs) ∧
        goJ lib O c gul st regs t (jmp0 g1.bo) = goJ lib O c gul st R' t nex.th) ∧
      (¬ FitsS nex.laz.sure s → goJ lib O c gul st regs t (jmp0 g1.bo) = some (Tone.two t, st)) := by
    intro cf c ned σ O gul t s0 s ag hned st regs hn
    obtain ⟨A, B, th', h1, h2, F⟩ := (ag st t).2 _ ((mem _).mpr (Or.inl rfl))
    rw [hb, if_pos rfl] at h1
    simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [List.map_nil] at h2
    rw [renJmp_nil _ thn] at h2
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; rwa [re1] at this
    refine ⟨fun st' t' => ⟨fun o h0 h1' hm => ?_, fun e he => ?_⟩, hned1, fun fs => ?_, fun fs => ?_⟩
    · rw [(ag st' t').1 o h0 (by rw [bo1]; omega) (fun hm' => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
          rcases (mem e).mp he with rfl | a
          · simp at h1'
          · exact hm (List.mem_map_of_mem a)), hb, if_neg (by omega)]
    · obtain ⟨A', B', th'', k1, k2, k3⟩ := (ag st' t').2 e ((mem e).mpr (Or.inr he))
      rw [hb, if_neg (by have := lt1 e he; omega)] at k1
      exact ⟨A', B', th'', k1, k2, by rw [re1] at k3; exact k3⟩
    · obtain ⟨F1, F2⟩ := F regs hn
      obtain ⟨R', hr, hh, hk⟩ := F1 fs
      have e1 := hr [] (Termin.hop nex.th)
      have nsur : ∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th0) x) → ¬ NMem nex.laz.sure.ned x :=
        fun x ⟨k1, k2⟩ hm => by
          rcases R.regs x hm with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned1 x k1; omega
      refine ⟨R', hh, HoldsN.agree _ (fun x hx => hk x (Or.inl hx) (fun hm => by
        have := hned1 x hx
        rcases R.regs x hm with b | ⟨_, b⟩
        · have := hgl x b; have := R.ext.1; omega
        · omega)) hn, fun r hr => hk r (hr.1.elim (fun h => Or.inr (by rw [re1]; have := R.ext.1; omega)) Or.inl)
          (nsur r hr), by rw [goJ_jmp0 _ _ _ _ h2, e1, execBlob_hop]⟩
    · have e2 := (F regs hn).2 fs [] (Termin.hop nex.th)
      rw [goJ_jmp0 _ _ _ _ h2, e2]
  refine ⟨R.ext.trans E1, R.grow.trans G1, R.cfr.trans (condFresh_of_eq (by rw [re1]; exact Nat.le_refl _) cd1),
    by simp only [jmp0]; have := R.lo; have := R.hi; omega, by simp [jmp0, Gen.emitted],
    Or.inl ⟨⟨[], [], Termin.hop nex.th⟩, by rw [hb]; simp [jmp0], rfl, rfl⟩,
    fun r hr => by simp [Sure.bunt, NMem] at hr, trivial, fun e he => ?_, fun e he => ?_, ?_,
    fun s _ hs => absurd (fitsS_bunt s) hs, fun r hr => by simp [Sure.bunt, NMem] at hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases (mem e).mp he with rfl | a
    · refine ⟨R.dist, fun r hr => ?_⟩
      rw [re1]
      rcases R.regs r hr with b | b
      · exact ⟨Or.inl b, by have := hgl r b; have := R.ext.1; omega⟩
      · exact ⟨Or.inr b.1, b.2⟩
    · refine ⟨(R.eregs e a).1, fun r hr => ?_⟩
      rw [re1]; exact (R.eregs e a).2 r hr
  · rcases (mem e).mp he with rfl | a
    · exact ⟨R.ext.2.1, by rw [bo1]; omega, [], _, by rw [hb, if_pos rfl]⟩
    · obtain ⟨x1, x2, B, th', z⟩ := R.labs e a
      exact ⟨x1, by rw [bo1]; omega, B, th', by rw [hb, if_neg (by omega)]; exact z⟩
  · rw [hent, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lt1 e he; simp at e1; omega, R.nodup⟩
  · rw [cd1]
    rcases (mem e).mp he with rfl | a
    · exact R.ncond r hr
    · exact R.econd e a r hr
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs _ hn
    obtain ⟨ag1, hned1, F1, F2⟩ := core cf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      exact goalSemCM_step (Needs.le_refl _) hk e1 _ _
        (R.sem cf (hcfE cf hcf) c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag1 hned1 R' hh hn')
    · exact goalSemCM_of_badC ((R.nec s hs fs).1 gul n tm r hm)
        ⟨Tone.two t, st, hI, Needs.le_refl _, F2 fs, ToneRel.two htr⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs _ hn res hres
    obtain ⟨ag1, hned1, F1, F2⟩ := core cf c ned σ O gul t s0 s ag hned st regs hn
    by_cases fs : FitsS nex.laz.sure s
    · obtain ⟨R', hh, hn', hk, e1⟩ := F1 fs
      obtain ⟨r, hm, G⟩ := R.semB cf (hcfE cf hcf) c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag1 hned1 R'
        hh hn' res (by rw [← e1]; exact hres)
      exact ⟨r, hm, goalSemCM_step (Needs.le_refl _) hk e1 _ _ G⟩
    · obtain ⟨r, hm, hbad⟩ := (R.nec s hs fs).2 gul tm
      exact ⟨r, hm, goalSemCM_of_badC hbad ⟨Tone.two t, st, hI, Needs.le_refl _, F2 fs, ToneRel.two htr⟩⟩

/-! ## `%done` from `%next (lazy-from-reg re)`, the agreement at every trace -/

/-- **`runOKGB_of_next` for `RunOKGBT`**: a run for `%done` or `%pick` that
begins with the block `bk` of `+simple-next` at `bo`, the rest a run under
`%next (lazy-from-reg re)` into it meeting `RunOKGB`, meets `RunOKGB` for
the goal.  The text of `runOKGC_of_next`, with `AgreeUB` for `AgreeU`. -/
theorem runOKGBT_of_next {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {goal : CGoal S} (hg : NotNext goal)
    {g0 g' : Gen Map} {nex : NextL S} {bk : Blob} (hu : UpBelow g0) (hcb : CondBelow g0)
    (hjb : JumpsBelow bk.fin g0.bo) (hpar : bk.par = [])
    (hb : HoonMap.get g'.blocks g0.bo = some bk)
    (hbc : ∀ cf : Map (Nat × List Nat), HoonMap.get cf g0.re = Option.none → unproxyBlob cf bk = bk)
    (hconv : ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (Inv : σ → Prop) (ν : σ → Needs)
      (K K' : Nat → Prop) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (je : Jmp) (r : Tone),
      (∀ x, K x → K' x) → Forall2 (FrameRel lib (ν st)) t tm → HoonMap.get c.blocks g0.bo = some bk →
      GoalSemCM lib O c gul Inv ν K' st regs t tm je (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r)
    (R : RunOKGBT lib N P f (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo))
      ({ g0 with re := g0.re + 1 }.emitted bk) g' nex) :
    RunOKGBT lib N P f goal g0 g' nex := by
  have l1 := R.ext.1
  have l2 := R.ext.2.1
  simp only [Gen.emitted] at l1 l2
  have E0 : Ext g0 ({ g0 with re := g0.re + 1 }.emitted bk) := (ext_re _).trans (ext_emit _ _)
  have G0 : GrowU g0 ({ g0 with re := g0.re + 1 }.emitted bk) :=
    ((grow_re g0).trans (grow_emit (g := { g0 with re := g0.re + 1 }) hjb)).toU hu
  have C0 : CondFresh g0 ({ g0 with re := g0.re + 1 }.emitted bk) :=
    condFresh_of_eq (by simp [Gen.emitted]) rfl
  have gm : ∀ r, ¬ GMem goal r := notNext_gmem hg
  have gl : ∀ r, GMem (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r → r = g0.re := fun r h => h
  have bad : ∀ tm r, BadC (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) tm r → BadC goal tm r :=
    fun tm r h => by
      rcases h with e | ⟨p, _, hp⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg g0.re p) hp
  have nlab : ∀ e ∈ entries nex.laz, g0.bo < e.1 := fun e he => by
    have := (R.labs e he).1; simp only [Gen.emitted] at this; omega
  -- the program's block at `bo` and the parts of `AgreeU`
  have blk : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      AgreeUB lib O c gul st t cf ned g0 g' nex.laz s0 s → HoonMap.get c.blocks g0.bo = some bk := by
    intro cf c σ O gul st t ned s0 s hcf ag
    have c0 : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by omega), R.cfr.get_lt (by simp [Gen.emitted])]
      exact condBelow_none hcb (Nat.le_refl _)
    rw [ag.1 _ (Nat.le_refl _) (by omega) (fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := nlab e he; omega), hb]
    simp only [Option.map_some, hbc cf c0]
  have agp : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), AgreeUB lib O c gul st t cf ned g0 g' nex.laz s0 s →
      AgreeUB lib O c gul st t cf ned ({ g0 with re := g0.re + 1 }.emitted bk) g' nex.laz s0 s :=
    fun cf c σ O gul st t ned s0 s ag =>
      ⟨fun o h0' h1 hn => ag.1 o (by simp only [Gen.emitted] at h0'; omega) h1 hn, ag.2⟩
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ x,
      ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) →
      ((x < ({ g0 with re := g0.re + 1 }.emitted bk).re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) x) := fun ned hned x hx => by
    simp only [Gen.emitted]
    rcases hx.1 with e | e
    · exact ⟨Or.inl (by omega), fun h => by have := gl x h; omega⟩
    · exact ⟨Or.inr e, fun h => by have := gl x h; have := hned x e; omega⟩
  refine ⟨E0.trans R.ext, G0.trans R.grow, C0.trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Or.inr ?_, ((R.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := nlab e he; omega, (R.labs e he).2⟩, R.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => bad tm r ((R.nec s hs hf).1 gul n tm r hm), fun gul tm => by
      obtain ⟨r, hm, hb'⟩ := (R.nec s hs hf).2 gul tm
      exact ⟨r, hm, bad tm r hb'⟩⟩, R.ncond, R.econd, ?_, ?_⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨bk, hb, hpar, rfl⟩
  · rcases R.regs r hr with e | ⟨a, b⟩
    · have := gl r e; subst this; exact Or.inr ⟨Nat.le_refl _, by omega⟩
    · simp only [Gen.emitted] at a; exact Or.inr ⟨by omega, b⟩
  · rcases ((R.eregs e he).2 r hr).1 with a | a
    · have := gl r a; omega
    · simp only [Gen.emitted] at a; omega
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact hconv c σ O gul Inv ν _ _ st regs t tm nex.th r (hK ned hned) htr (blk cf c σ O gul st t ned s0 s hcf (ag st t))
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
        (fun st' t' => agp cf c σ O gul st' t' ned s0 s (ag st' t')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' t' => agp cf c σ O gul st' t' ned s0 s (ag st' t')) hned regs hh hn res hres
    exact ⟨r, hm, hconv c σ O gul Inv ν _ _ st regs t tm nex.th r (hK ned hned) htr
      (blk cf c σ O gul st t ned s0 s hcf (ag st t)) G⟩

/-- **`RunOKGBT` under `%done`** from the block `[don re]` and the run
under `%next (lazy-from-reg re)` into it. -/
theorem runOKGBT_done {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {g0 g' : Gen Map} {nex : NextL S}
    (hu : UpBelow g0) (hcb : CondBelow g0) (hb : HoonMap.get g'.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩)
    (R : RunOKGBT lib N P f (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo))
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' nex) :
    RunOKGBT lib N P f (CGoal.done : CGoal S) g0 g' nex :=
  runOKGBT_of_next (goal := CGoal.done) trivial hu hcb (fun j hj => by simp [finJumps] at hj) rfl hb
    (fun cf c0 => by simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0])
    (fun c σ O gul Inv ν K K' st regs t tm je r _ _ hbc H => goalSemCM_done_of_next hbc H) R

/-! ## The clause of a part run under `%next (lazy-from-reg r)` -/

/-- **`RegGBT`: every run of `nm` under `%next (lazy-from-reg r) th`
gives `RunOKGBT` for the goal `%next (lazy-from-reg r) th`.**  The clause
of a part that its parent runs only at such a goal: the operand of
`[4 p]`, the formula of a kept hint (`+past-if` emits nothing when `+sound`
of `%this` holds of it), the run under `%done` behind the block `[don re]`.
A member of `LOKSFH` is in it (`RegGBT.of_loksf`), and so is a kept
dynamic `stopTag` hint over a member (`regGBT_n11dKept`), so nested spots
are, at any depth.  It is not a member of the `LOKSH`-style classes
because those quantify over every flat lazy goal and conclude `RunOKLS`
(the agreement at one trace, the result flat), and a kept hint has
neither: its bond is filled at the pushed trace, and nested results have
bonds inside bonds. -/
def RegGBT (snd : Nomm → NeedOrd → Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → rg < g0.re → HoonMap.get g0.cond rg = Option.none →
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure (lazyReg rg)) th) region g0 = some (nex, g1) →
    RunOKGBT lib N P f (CGoal.next (lazyReg rg) th) g0 g1 nex

section Reg
variable {snd : Nomm → NeedOrd → Bool}

/-- **A member of `LOKSFH` is in `RegGBT`** (`RunOKLB.toGB`, `RunOKGB.toT`). -/
theorem RegGBT.of_loksf {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P f nm) (hc : sixCount nm ≤ 255) :
    RegGBT (S := S) (Map := Map) snd lib N env P f nm := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  have e0 : entries (ofSure (lazyReg rg : Sure S)) = [] := entries_ofSure _
  obtain ⟨⟨Q, RS⟩, -, -, -, -⟩ := H.run (sup := sup) (L := ofSure (lazyReg rg)) (th := th) (region := region)
    (Or.inr e0) hc b0 d0 hu hcl hcb th1 th2 hta (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨hr0, hc0⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) hr
  exact (RS.toRunOKLB.toGB (fun x hx => by simp only [lazyReg, NMem] at hx; omega)).toT

/-- The state after `toke` and the epilogue of a kept dynamic hint under
`%next`. -/
def genN (g0 : Gen Map) (tag : Nat) (body : Noun) (th : Jmp) : Gen Map :=
  ({ g0 with re := g0.re + 1 }).emitted ⟨[], [Pole.hde tag g0.re body], Termin.hop th⟩

/-- **The run of a kept dynamic hint under `%next (lazy-from-reg rg)`, step
by step**, when `+sound` of `%this` holds for the formula. -/
theorem runLCH_n11d_kept_next {env : CallEnv} {tag : Nat} (hs : hintDynamic tag = true) {h q : Nomm} {body : Noun}
    (hsnd : snd q NeedOrd.this = true) {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S}
    (hr : runLCH env snd true sup (Nomm.n11d tag h q body) (CGoalL.next (ofSure (lazyReg rg)) th) region g0 =
      some (nex, g1)) :
    ∃ nq gc nh gh, runLCH env snd true sup q (CGoalL.next (ofSure (lazyReg rg)) (jmp0 g0.bo)) region
        (genN g0 tag body th) = some (nq, gc) ∧
      nq.th.args = [] ∧
      runLCH env snd true sup h (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 (gc.bo + 1))) region
        (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
          ⟨[], [Pole.hdp tag g0.re body], Termin.hop (jmp0 gc.bo)⟩) = some (nh, gh) ∧
      copyL nh (mk Sure.bunt [] [(gc.bo, nq.laz)]) gh = some (nex, g1) := by
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
  obtain ⟨tk, gt, ht, hr⟩ := bind_some hr
  rw [re_apply] at ht
  simp only [Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl⟩ := ht
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
  obtain ⟨nh, gh, h6, hr⟩ := bind_some hr
  refine ⟨nq, gc, nh, gh, ?_, hta, ?_, hr⟩
  · simpa only [genN, Gen.emitted] using h3
  · simpa only [Gen.emitted, tagged_bo] using h6

/-- `+run` of a kept dynamic hint under `%done` is the block `[don re]`,
then the run under `%next (lazy-from-reg re)` into it. -/
theorem runLCH_n11d_done_next {env : CallEnv} {tag : Nat} (hs : hintDynamic tag = true) {h q : Nomm} {body : Noun}
    (sup : Option Nomm) (region : List Nat) (g0 : Gen Map) :
    (runLCH env snd true sup (Nomm.n11d tag h q body) CGoalL.done region g0 : Option (NextL S × Gen Map)) =
      runLCH env snd true sup (Nomm.n11d tag h q body) (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) := by
  simp only [runLCH, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_apply, simpleNextL_done, Option.bind_some]
  simp only [simpleNextL, pure_apply, Option.bind_some]

end Reg

section Kept
variable {snd : Nomm → NeedOrd → Bool}

/-- **A kept dynamic `stopTag` hint over a member of `RegGBT` is in
`RegGBT`** (the clue with `LOKSFH` and `NoBondH`, `+sound` of `%this` for
the formula).  The text of `n11dKept_done` for the goal `%next
(lazy-from-reg rg) th`: no block `[don re]`, the epilogue hops to `th`; the
formula's `RunOKGBT` (any result, bonds inside included) behind the block of
`+lazy-bound` (`RunOKGBT.bound`); the entries of the result are
`(o, nq.laz) :: entries nq.laz`; the end is `frameOK_goes` at the goal's
need, which every product fits, then `goalSemCM_step` over the clue. -/
theorem regGBT_n11dKept {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fh fq : Noun} {h q : Nomm}
    (Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)
    (Hh : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fh h) (hch : sixCount h ≤ 255)
    (hnh : NoBondH (S := S) (Map := Map) snd env h)
    {tag : Nat} (hs : hintDynamic tag = true) (hst : stopTag tag = true) (body : Noun) :
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
      FrameOK c tag g0.re body (gc.bo + 1) gc.bo g0.bo th := by
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
    obtain ⟨hcp, F⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
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
            hN hS (oracleFwd_le hF (Nat.le_succ m)) st1 ((tag, v) :: t) ((tag, v) :: tm) s0 s r hI1
            (Forall2.cons (FrameRel.same hst) (frames_mono hle1 htr)) hs hm (fun st' t' => agq (ag st' t'))
            (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
          exact goalSemCM_step hle1 (hkc ned regs regs1 hned hk1) (by rw [ecopy, e1]) _ _
            (goalSemCM_monoK (hKm ned) _ _ (frameOK_goes F (fitsS_lazyReg rg) hh1 Gq))
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
      rw [e1, goJ_push hst F.2.1 st1 regs1 hh1 t] at hres
      obtain ⟨r, hmq, Gq⟩ := RG.semB cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν
        O gul hN hS hB st1 ((tag, v) :: t) ((tag, v) :: tm) s0 s hI1
        (Forall2.cons (FrameRel.same hst) (frames_mono hle1 htr)) hs (fun st' t' => agq (ag st' t'))
        (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
        res hres
      exact ⟨r, mink_n11d_stop hst hmh hmq, goalSemCM_step hle1 (hkc ned regs regs1 hned hk1) (by rw [ecopy, e1]) _ _
        (goalSemCM_monoK (hKm ned) _ _ (frameOK_goes F (fitsS_lazyReg rg) hh1 Gq))⟩
    | one b =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | two tr =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩

end Kept

end Comp
end SkaModel
end Formalization
