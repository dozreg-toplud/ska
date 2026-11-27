import lemmas.Ska.CompIndirectLS
import lemmas.Ska.CompLBDone

/-!
# The class `CallTree` at the top, and `[7 p q]` of it under `%done`

README Gaps 12.27.  `lokS_callTree` (`CompIndirectLS.lean`) gives `LOKS
false` for every nomm of `CallTree`, with the premises of `LOKS.run` on the
starting goal and state.  Here the goal a compile starts from meets them:
under `%done` the run of a cons, an indirect call or `[0 axe]` (`axe ≥ 1`)
is the block `[don re]` and the run under `%next (lazy-from-reg re)` into
it (`runLC_done_next`), a flat goal with no entry; `[0 0]` is `+bomb`
(`UOKC` through `FragX`).  The result under `%done` is flat with clean
entries (`callTree_done`), so it meets the premises of `LOKS.run` for the
`p` of `[7 p q]`, and `runOKGB_sevenL` composes.

* `RunOKLB.toGB`: `RunOKLB` under `ofSure sur` gives `RunOKGB` under
  `%next sur th` (`RunOKLC.toGC` with bodies).
* `runOKGB_of_next`: `runOKGC_of_next` for `RunOKGB`.
* `runLC_done_next`, `DoneOK`, `callTree_done`: every nomm of `CallTree`
  under `%done` meets `RunOKGB`, its result flat with clean entries and
  its jump at no entry.
* `TopTree` (`CallTree` closed under `[7 p q]` with `p` in `CallTree`),
  `topTree_done`, `finishLUC_contractTopTree`, `finishLUC_bellContractTopTree`:
  both halves of the contract with no hypothesis on the run.
* Examples: `%cc2`, a cons inside an indirect call, `%bc1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## From a lazy goal without entries to `RunOKGB` -/

/-- **A goal without entries, back, with bodies** (`RunOKLC.toGC` for
`RunOKLB`): `RunOKLB` under `ofSure sur` gives `RunOKGB` under `%next sur
th` when the registers of `sur` were allocated before the run. -/
theorem RunOKLB.toGB {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th : Jmp} {Q : Wit} {x : Bool}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKLB (Map := Map) lib N P f (ofSure sur) th Q x g0 g1 nex)
    (hlt : ∀ r, NMem sur.ned r → r < g0.re) : RunOKGB lib N P f (CGoal.next sur th) g0 g1 nex := by
  have e0 : entries (ofSure sur) = [] := entries_ofSure sur
  refine ⟨⟨R.re, R.bo, R.drop, fun o ho => R.keep o ho (by rw [e0]; simp)⟩, R.grow, R.cfr, R.lo, R.hi, R.ent,
    R.regs, R.dist, fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩, fun e he => ?_, R.nodup, R.nec, R.ncond,
    R.econd, ?_, ?_⟩
  · rcases (R.eregs e he).2 r hr with ⟨e0', h0, _⟩ | h | h
    · rw [e0] at h0; cases h0
    · have := hlt r h; have := R.re; exact ⟨Or.inl h, by omega⟩
    · exact ⟨Or.inr h.1, h.2⟩
  · obtain ⟨h1 | h1, hb⟩ := R.labs e he
    · rw [e0] at h1; cases h1
    · exact ⟨h1.1, h1.2, hb⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact goalSemCMD_toCM (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
      (fun st' => ⟨(ag st').1, fun e he _ => (ag st').2 e he⟩) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => ⟨(ag st').1, fun e he _ => (ag st').2 e he⟩) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCMD_toCM G⟩

/-- **`runOKGC_of_next` for `RunOKGB`**: a run for `%done` or `%pick` that
begins with the block `bk` of `+simple-next` at `bo`, the rest a run under
`%next (lazy-from-reg re)` into it meeting `RunOKGB`, meets `RunOKGB` for
the goal.  The text of `runOKGC_of_next`, with `AgreeUB` for `AgreeU`. -/
theorem runOKGB_of_next {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {goal : CGoal S} (hg : NotNext goal)
    {g0 g' : Gen Map} {nex : NextL S} {bk : Blob} (hu : UpBelow g0) (hcb : CondBelow g0)
    (hjb : JumpsBelow bk.fin g0.bo) (hpar : bk.par = [])
    (hb : HoonMap.get g'.blocks g0.bo = some bk)
    (hbc : ∀ cf : Map (Nat × List Nat), HoonMap.get cf g0.re = Option.none → unproxyBlob cf bk = bk)
    (hconv : ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (Inv : σ → Prop) (ν : σ → Needs)
      (K K' : Nat → Prop) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (je : Jmp) (r : Tone),
      (∀ x, K x → K' x) → Forall2 (FrameRel lib (ν st)) t tm → HoonMap.get c.blocks g0.bo = some bk →
      GoalSemCM lib O c gul Inv ν K' st regs t tm je (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r)
    (R : RunOKGB lib N P f (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo))
      ({ g0 with re := g0.re + 1 }.emitted bk) g' nex) :
    RunOKGB lib N P f goal g0 g' nex := by
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
    exact hconv c σ O gul Inv ν _ _ st regs t tm nex.th r (hK ned hned) htr (blk cf c σ O gul st t ned s0 s hcf (ag st))
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
        (fun st' => agp cf c σ O gul st' t ned s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => agp cf c σ O gul st' t ned s0 s (ag st')) hned regs hh hn res hres
    exact ⟨r, hm, hconv c σ O gul Inv ν _ _ st regs t tm nex.th r (hK ned hned) htr
      (blk cf c σ O gul st t ned s0 s hcf (ag st)) G⟩

/-- **`RunOKGB` under `%done`** from the block `[don re]` and the run
under `%next (lazy-from-reg re)` into it. -/
theorem runOKGB_done {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {g0 g' : Gen Map} {nex : NextL S}
    (hu : UpBelow g0) (hcb : CondBelow g0) (hb : HoonMap.get g'.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩)
    (R : RunOKGB lib N P f (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo))
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' nex) :
    RunOKGB lib N P f (CGoal.done : CGoal S) g0 g' nex :=
  runOKGB_of_next (goal := CGoal.done) trivial hu hcb (fun j hj => by simp [finJumps] at hj) rfl hb
    (fun cf c0 => by simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0])
    (fun c σ O gul Inv ν K K' st regs t tm je r _ _ hbc H => goalSemCM_done_of_next hbc H) R

/-! ## The class under `%done` -/

/-- **Under `%done`, the cons, the indirect call and `[0 axe]` (`axe ≥ 1`)
begin with the block `[don re]`**: the rest of the run is the run under
`%next (lazy-from-reg re)` into it. -/
theorem runLC_done_next (env : CallEnv) (sup : Option Nomm) {nm : Nomm}
    (h : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    (region : List Nat) (g0 : Gen Map) :
    (runLC env sup nm CGoalL.done region g0 : Option (NextL S × Gen Map)) =
      runLC env sup nm (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) := by
  rcases h with ⟨p, q, rfl⟩ | ⟨p, q, rfl⟩ | ⟨ax, ha, rfl⟩
  · rw [runLC_cons_done]
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some]
  · simp only [runLC, callL, bind_apply]
    rw [simpleNextL_done]
    simp only [Option.bind_some, simpleNextL, pure_apply]
  · have e : ax ≠ 0 := by omega
    simp only [runLC, e, if_false, bind_apply]
    rw [simpleNextL_done]
    simp only [Option.bind_some, simpleNextL, pure_apply]

/-- **What a run under `%done` gives a later run under its result**:
`RunOKGB`, the jump at no entry, the result flat with clean entries. -/
structure DoneOK (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  run : RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nex
  nent : nex.th.there ∉ (entries nex.laz).map Prod.fst
  flat : Flat nex.laz
  clean : Clean nex.laz.sure.ned
  eclean : ∀ e ∈ entries nex.laz, Clean e.2.sure.ned

/-- **`LOKS` at the goal a compile starts from**: the run under `%next
(lazy-from-reg re)` into the block `[don re]` meets every premise of
`LOKS.run` (a flat goal with no entry), so the run under `%done` that
begins with that block meets `DoneOK`. -/
theorem lokS_done {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS (S := S) (Map := Map) x lib N env P f nm) (hcount : sixCount nm ≤ 255)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup nm (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) = some (nex, g1)) :
    DoneOK lib N P f g0 g1 nex := by
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := H.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 g0.bo)
    (region := region) hcount
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    b0 (by simp only [jmp0, Gen.emitted]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) hr
  have hb : HoonMap.get g1.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    rw [RS.keep _ (by simp only [Gen.emitted]; omega) (by rw [e0]; simp)]
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have RG := RS.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted]; omega)
  exact ⟨runOKGB_done hu hcb hb RG, hne, hfl, H.clean (L := ofSure (lazyReg g0.re)) trivial hr, hec⟩

/-- The nomms of `CallTree` have no `%6`. -/
theorem CallTree.sixCount {f : Noun} {nm : Nomm} (h : CallTree f nm) : sixCount nm = 0 := by
  induction h with
  | n0 axe => rfl
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | ind _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]

/-- **Every nomm of `CallTree` under `%done` meets `DoneOK`**, from any
state as a compile has it: `[0 0]` through `UOKC` (`+bomb`), the others
through `lokS_callTree` at the goal of `runLC_done_next`. -/
theorem callTree_done (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) {f : Noun} {nm : Nomm} (h : CallTree f nm)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup nm CGoalL.done region g0 = some (nex, g1)) :
    DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  by_cases e00 : nm = Nomm.n0 0
  · subst e00
    cases h
    have M : MinkEq lib P (slot 0) (Nomm.n0 0) :=
      ((CallTree.n0 0).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h)
    have U := uokc_of_uok (S := S) (Map := Map) lib env
      (uok_x lib (FragX.frag (S := S) (nm := Nomm.n0 0) fun _ => trivial)) M
    have R := U.run (sup := sup) (goal := CGoal.done) (region := region) trivial trivial trivial trivial trivial
      (by simp [Comp.sixCount]) b0 d0 hu hcl hcb (fun r hr => hr.elim) hr
    have e : (runLC env sup (Nomm.n0 0) CGoalL.done region g0 : Option (NextL S × Gen Map)) =
        bombL Option.none g0 := by simp only [runLC, if_true]
    rw [e] at hr
    simp only [bombL, bind_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨R.toB, by simp [entries_ofSure], flat_ofSure _, trivial, by simp [entries_ofSure]⟩
  · have hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨
        (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax) := by
      cases h with
      | n0 axe => exact Or.inr (Or.inr ⟨axe, by
          rcases Nat.eq_zero_or_pos axe with rfl | ha
          · exact absurd rfl e00
          · exact ha, rfl⟩)
      | cons _ _ => exact Or.inl ⟨_, _, rfl⟩
      | ind _ _ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    rw [runLC_done_next env sup hs region g0] at hr
    exact lokS_done (lokS_callTree lib env P h).1 (by rw [h.sixCount]; omega) b0 d0 hu hcl hcb hr

/-! ## `[7 p q]` under `%done` and the top -/

/-- **`CallTree` closed under `[7 p q]` at the top**: `q` compiled under
`%done` (the class itself), `p` under `q`'s result (`CallTree`). -/
inductive TopTree : Noun → Nomm → Prop
  | tree {f : Noun} {nm : Nomm} : CallTree f nm → TopTree f nm
  | seven {b c : Noun} {p q : Nomm} : CallTree b p → TopTree c q → TopTree (n3 (A 7) b c) (Nomm.n7 p q)

/-- **Every nomm of `TopTree` under `%done` meets `DoneOK`**: for `[7 p
q]`, `q`'s `DoneOK` (on the products of `p`) gives every premise of
`LOKS.run` for `p` at `q`'s result (`RunOKGB`'s fields, the state from
`Ext`, `GrowU`, `CondFresh`, and `Flat`, the clean needs and the jump at no
entry from `DoneOK`), and `runOKGB_sevenL` composes. -/
theorem topTree_done (lib : Lib) {N : Needs} (env : CallEnv) {f : Noun} {nm : Nomm} (h : TopTree f nm) :
    ∀ (P : Noun → Prop) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm CGoalL.done region g0 = some (nex, g1) → DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  induction h with
  | tree hc =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact callTree_done lib env P hc b0 d0 hu hcl hcb hr
  | @seven b c p q hp hq ih =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLC_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ih (Img lib P b) b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := (lokS_callTree (S := S) (Map := Map) lib (N := N) env P hp).1
    have hj : nx.th.args = [] := by
      rcases Rq.ent with ⟨_, _, _, ha⟩ | e
      · exact ha
      · exact e.elim
    obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
      (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
      (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
      (fun x hx => ⟨by
        rcases Rq.regs x hx with e | e
        · exact e.elim
        · exact e.2, Rq.ncond x hx⟩)
      (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
      (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
      D.flat D.clean D.eclean h2
    exact ⟨runOKGB_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
      Lp.clean (L := nx.laz) D.clean h2, hec⟩

/-- **The contract of the class at the top**: the whole-subject code of
every nomm of `TopTree` meets both halves of the contract for its formula,
on every subject, with no hypothesis about the run. -/
theorem finishLUC_contractTopTree (lib : Lib) (env : CallEnv) (P : Noun → Prop) {f : Noun} {nm : Nomm}
    (h : TopTree f nm) {c : Straight Map} (hc : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractGB lib N (fun hr => (topTree_done (S := S) (Map := Map) lib env h P (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of the class** (`finishLUC_contractNC`'s form): a
nomm of `TopTree` for the bell's formula. -/
theorem finishLUC_bellContractTopTree {lib : Lib} {bl : Bell} {nm : Nomm} (h : TopTree bl.fol nm)
    {env : CallEnv} {cd : Straight Map} (hc : finishLUC (S := S) env nm = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractTopTree (S := S) lib env (SkaModel.Fits bl.less) h hc N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-! ## Examples -/

/-- `%cc2`, `[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` (calls in both halves of a
cons): its whole-subject code meets both halves of the contract. -/
theorem cc2_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (C (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 3) (slot 2))) [s] c ∧
      ContractBwd lib N s (C (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 3) (slot 2))) [s] c :=
  have H := finishLUC_contractTopTree lib env (fun _ => True)
    (TopTree.tree (CallTree.cons (CallTree.ind (CallTree.n0 3) (CallTree.n0 2))
      (CallTree.ind (CallTree.n0 3) (CallTree.n0 2)))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- A cons inside an indirect call, `[2 [[0 3] [0 2]] [0 3]]` (the subject
part is the cons): both halves of the contract. -/
theorem consInd_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n2 (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)) (Nomm.n0 3) Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 2) (C (slot 3) (slot 2)) (slot 3)) [s] c ∧
      ContractBwd lib N s (n3 (A 2) (C (slot 3) (slot 2)) (slot 3)) [s] c :=
  have H := finishLUC_contractTopTree lib env (fun _ => True)
    (TopTree.tree (CallTree.ind (CallTree.cons (CallTree.n0 3) (CallTree.n0 2)) (CallTree.n0 3))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `%bc1`, `[7 [[0 2] [0 3]] [[2 [0 2] [0 6]] [0 1]]]` (`q`'s result keeps
`p`'s `[con v6 v7 v2]` in its bond block): both halves of the contract. -/
theorem bc1_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n7 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3))
        (Nomm.cons (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none) (Nomm.n0 1))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 7) (C (slot 2) (slot 3)) (C (n3 (A 2) (slot 2) (slot 6)) (slot 1))) [s] c ∧
      ContractBwd lib N s (n3 (A 7) (C (slot 2) (slot 3)) (C (n3 (A 2) (slot 2) (slot 6)) (slot 1))) [s] c :=
  have H := finishLUC_contractTopTree lib env (fun _ => True)
    (TopTree.seven (CallTree.cons (CallTree.n0 2) (CallTree.n0 3))
      (TopTree.tree (CallTree.cons (CallTree.ind (CallTree.n0 2) (CallTree.n0 6)) (CallTree.n0 1)))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `%bc2`, `[7 [[0 1] [0 1]] [[2 [0 2] [0 6]] [[0 2] [0 3]]]]` (the
tail's bond merged at one label): the class membership. -/
example : TopTree (n3 (A 7) (C (slot 1) (slot 1)) (C (n3 (A 2) (slot 2) (slot 6)) (C (slot 2) (slot 3))))
    (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1))
      (Nomm.cons (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none) (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)))) :=
  TopTree.seven (CallTree.cons (CallTree.n0 1) (CallTree.n0 1))
    (TopTree.tree (CallTree.cons (CallTree.ind (CallTree.n0 2) (CallTree.n0 6))
      (CallTree.cons (CallTree.n0 2) (CallTree.n0 3))))

/-- `%lim`, `[7 [[0 3] [0 1]] [[2 [0 2] [0 6]] [0 3]]]`, and `%s7g`,
`[7 [2 [0 3] [0 2]] [[2 [0 3] [0 2]] [0 1]]]`: the class membership. -/
example : TopTree (n3 (A 7) (C (slot 3) (slot 1)) (C (n3 (A 2) (slot 2) (slot 6)) (slot 3)))
    (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.cons (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none) (Nomm.n0 3))) :=
  TopTree.seven (CallTree.cons (CallTree.n0 3) (CallTree.n0 1))
    (TopTree.tree (CallTree.cons (CallTree.ind (CallTree.n0 2) (CallTree.n0 6)) (CallTree.n0 3)))

example : TopTree (n3 (A 7) (n3 (A 2) (slot 3) (slot 2)) (C (n3 (A 2) (slot 3) (slot 2)) (slot 1)))
    (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))) :=
  TopTree.seven (CallTree.ind (CallTree.n0 3) (CallTree.n0 2))
    (TopTree.tree (CallTree.cons (CallTree.ind (CallTree.n0 3) (CallTree.n0 2)) (CallTree.n0 1)))

end Comp
end SkaModel
end Formalization
