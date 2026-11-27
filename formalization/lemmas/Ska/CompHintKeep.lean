import lemmas.Ska.CompHintTreeU

/-!
# Kept static hints (`%bout`, `%xray`) at the top (README Gaps 24.14)

`+run` on `[11 tag q]` with `hint-static` of `tag` (`runLCH`, the case
`n11s`): `+simple-next` of the goal, `+past-if`, the epilogue `[hse tag f]
hop then`, `q` under `%next` to it, `+lazy-bound` (a block `o` holding `q`'s
lazy need as one bond), the prologue `[hsp tag f] hop o`.

`%hsp` and `%hse` do nothing in `localPole` (`QuietP`), so a block made of one
of them and a hop runs as the hop (`goJ_quiet`): no frame is pushed, and a
crash inside `q` carries the trace `q`'s code gives it, as `+mink` on
`[11 tag f]` (which is `f`, `minkAs_n11s`).

* `goalSemCM_of_goJ`, `goalSemCM_next_hop`: `GoalSemCM` reads its entry
  jump only through `goJ`, and a `%next` goal's jump only through `GoesC`.
* `RunOKGB.quietFront`: a quiet block in front of a run's result (the
  prologue); `RunOKGB.quietGoal`: a quiet block between a run and its goal's
  jump (the epilogue).
* `NoBondH`: the run of a nomm under a goal with no bond has no bond
  (Step 1; the clause the kept case needs, since `+lazy-bound` nests the
  formula's bonds).
* `n11sKept_done`: **`DoneOK` of a kept static hint under `%done`**, for a
  formula with `LOKSFH` and `NoBondH` whose `+sound` of `%this` holds (then
  `+past-if` emits nothing).
* `finishLUCH_contractN11sKept`: both halves of the contract at the top,
  traces included.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The hint ops that do nothing in `localPole`: `%hsp`, `%hse`. -/
def QuietP : Pole → Prop
  | Pole.hsp _ _ => True
  | Pole.hse _ _ => True
  | _ => False

theorem quiet_ren {p : Pole} (hp : QuietP p) (u : Nat → Nat) : renPole u p = p := by
  cases p <;> simp only [QuietP] at hp <;> rfl

theorem unproxyBlob_quiet {p : Pole} (hp : QuietP p) {th : Jmp} (ha : th.args = []) (cf : Map (Nat × List Nat)) :
    unproxyBlob cf ⟨[], [p], Termin.hop th⟩ = ⟨[], [p], Termin.hop th⟩ := by
  rcases th with ⟨args, there⟩
  simp only at ha
  subst ha
  simp only [unproxyBlob, renBlob, List.map_nil, List.map_cons, quiet_ren hp, renFin, renJmp]

section Exec
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **A quiet block and a hop runs as the hop.** -/
theorem goJ_quiet {o : Nat} {p : Pole} {th : Jmp} (hp : QuietP p)
    (hb : HoonMap.get c.blocks o = some ⟨[], [p], Termin.hop th⟩) (st : σ) (regs : Map (Option Noun)) (t : Trace) :
    goJ lib O c gul st regs t (jmp0 o) = goJ lib O c gul st regs t th := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  cases p <;> simp only [QuietP] at hp <;> simp [execPole, localPole, execBlob_hop]

variable {Inv : σ → Prop} {ν : σ → Needs} {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace}

/-- `GoalSemCM` reads its entry jump only through `goJ`. -/
theorem goalSemCM_of_goJ {je je' : Jmp} {goal : CGoal S} {r : Tone}
    (h : goJ lib O c gul st regs t je' = goJ lib O c gul st regs t je)
    (H : GoalSemCM lib O c gul Inv ν K st regs t tm je goal r) : GoalSemCM lib O c gul Inv ν K st regs t tm je' goal r := by
  cases goal <;> cases r <;> simp only [GoalSemCM, ReturnsC, GoesC, h] at H ⊢ <;> exact H

/-- A `%next` goal's jump is read only through `GoesC`: a quiet hop to it is it. -/
theorem goalSemCM_next_hop {je : Jmp} {sur : Sure S} {e : Nat} {th : Jmp} {r : Tone}
    (h : ∀ st regs, goJ lib O c gul st regs t (jmp0 e) = goJ lib O c gul st regs t th)
    (H : GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur (jmp0 e)) r) :
    GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) r := by
  cases r with
  | zero p =>
    refine ⟨fun hf => ?_, H.2⟩
    obtain ⟨st', regs', hI, hle, hh, hk, e⟩ := H.1 hf
    exact ⟨st', regs', hI, hle, hh, hk, e.trans (h st' regs')⟩
  | one b => exact H
  | two tr => exact H

end Exec

section Blocks
variable {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun}

theorem hk_emitted_self {g : Gen Map} (d : g.drop = false) (b : Blob) :
    HoonMap.get (g.emitted b).blocks g.bo = some b := by
  simp only [Gen.emitted, d, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put, if_true]

theorem hk_emitted_ne {g : Gen Map} (b : Blob) {k : Nat} (hk : k ≠ g.bo) :
    HoonMap.get (g.emitted b).blocks k = HoonMap.get g.blocks k := by
  simp only [Gen.emitted]; cases g.drop <;> simp [HoonMap.get_put, hk]

/-- **A quiet block in front of a run's result** (the prologue `[hsp tag f]
hop th`): the result's jump becomes the new block, nothing else changes. -/
theorem RunOKGB.quietFront {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKGB lib N P f goal g0 g1 nex) {p : Pole} (hp : QuietP p) (hta : nex.th.args = [])
    (d1 : g1.drop = false) (u1 : UpBelow g1) :
    RunOKGB lib N P f goal g0 (g1.emitted ⟨[], [p], Termin.hop nex.th⟩) ⟨nex.laz, jmp0 g1.bo⟩ := by
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
    have A := fun st' => agr O c gul st' t cf ned s0 s (ag st')
    exact goalSemCM_of_goJ (goJ_quiet hp (A st).2 st regs t)
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm (fun st' => (A st').1) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have A := fun st' => agr O c gul st' t cf ned s0 s (ag st')
    rw [goJ_quiet hp (A st).2 st regs t] at hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs (fun st' => (A st').1)
      hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_of_goJ (goJ_quiet hp (A st).2 st regs t) G⟩

/-- **A quiet block between a run and its goal's jump** (the epilogue
`[hse tag f] hop th`): a run under `%next sur` to the new block is a run
under `%next sur th`. -/
theorem RunOKGB.quietGoal {sur : Sure S} {th : Jmp} {g g' : Gen Map} {nex : NextL S} {p : Pole} (hp : QuietP p)
    (hu : UpBelow g) (d : g.drop = false) (h1 : 1 ≤ th.there) (h2 : th.there < g.bo) (hta : th.args = [])
    (R : RunOKGB lib N P f (CGoal.next sur (jmp0 g.bo)) (g.emitted ⟨[], [p], Termin.hop th⟩) g' nex) :
    RunOKGB lib N P f (CGoal.next sur th) g g' nex := by
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
    exact goalSemCM_next_hop (fun st' regs' => goJ_quiet hp (blk O c gul st t cf ned s0 s (ag st)) st' regs' t)
      (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
        (fun st' => agp O c gul st' t cf ned s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => agp O c gul st' t cf ned s0 s (ag st')) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_next_hop
      (fun st' regs' => goJ_quiet hp (blk O c gul st t cf ned s0 s (ag st)) st' regs' t) G⟩

end Blocks

/-! ## No bond out of a goal with none (Step 1) -/

/-- **`NoBondH`: the run of `nm` under a `%next` goal with no fork and no
bond has no fork and no bond.**  The clause a kept hint needs of its
formula: under `+lazy-bound` the formula's need is one bond, so a bond of
the formula's result would be a bond inside a bond (`CompHintNest.lean`). -/
def NoBondH (snd : Nomm → NeedOrd → Bool) (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
      nex.laz.fork = [] ∧ nex.laz.bond = []

section NoBond
variable {snd : Nomm → NeedOrd → Bool} {env : CallEnv}

theorem noBondH_n0 (ax : Nat) : NoBondH (S := S) (Map := Map) snd env (Nomm.n0 ax) := by
  intro sup sur th region g0 g1 nex hr
  by_cases h0 : ax = 0
  · subst h0
    simp only [runLCH, if_true, bombL, bind_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩
  · simp only [runLCH, h0, if_false, simpleNextL, bind_apply, pure_apply, Option.bind_some] at hr
    by_cases h1 : ax = 1
    · simp only [h1, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨rfl, rfl⟩
    · have e : fromL ax (ofSure sur) = (fromSure ax sur).map ofSure := by simp [fromL, ofSure]
      simp only [h1, if_false, e] at hr
      cases hf : fromSure ax sur with
      | none => simp [hf] at hr
      | some s' =>
        simp only [hf, Option.map_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨rfl, rfl⟩

theorem noBondH_n1 (k : Noun) : NoBondH (S := S) (Map := Map) snd env (Nomm.n1 k) := by
  intro sup sur th region g0 g1 nex hr
  simp only [runLCH] at hr
  obtain ⟨o, g', -, h2⟩ := bind_some hr
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact ⟨rfl, rfl⟩

theorem noBondH_n4 {p : Nomm} (hp : NoBondH (S := S) (Map := Map) snd env p) :
    NoBondH (S := S) (Map := Map) snd env (Nomm.n4 p) := by
  intro sup sur th region g0 g1 nex hr
  obtain ⟨arg, o, gX, h⟩ := runLCH_n4_last (fun z o => by simp) hr
  exact hp h

theorem noBondH_n7 {p q : Nomm} (hp : NoBondH (S := S) (Map := Map) snd env p)
    (hq : NoBondH (S := S) (Map := Map) snd env q) : NoBondH (S := S) (Map := Map) snd env (Nomm.n7 p q) := by
  intro sup sur th region g0 g1 nex hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  obtain ⟨f1, b1⟩ := hq h1
  have e : nx.goal = CGoalL.next (ofSure nx.laz.sure) nx.th := by
    simp only [NextL.goal]; rw [← Lazy.eta nx.laz, f1, b1]; rfl
  rw [e] at h2
  exact hp h2

theorem noBondH_n11s {tag : Nat} (hs : hintStatic tag = false) {q : Nomm} (body : Noun)
    (hq : NoBondH (S := S) (Map := Map) snd env q) : NoBondH (S := S) (Map := Map) snd env (Nomm.n11s tag q body) := by
  intro sup sur th region g0 g1 nex hr
  rw [runLCH_n11s env snd true hs] at hr
  exact hq hr

theorem noBondH_n11d {tag : Nat} (hs : hintDynamic tag = false) {h q : Nomm} (hh : safeNomm h = true) (body : Noun)
    (hq : NoBondH (S := S) (Map := Map) snd env q) : NoBondH (S := S) (Map := Map) snd env (Nomm.n11d tag h q body) := by
  intro sup sur th region g0 g1 nex hr
  rw [runLCH_n11d_safe env snd true hs hh] at hr
  exact hq hr

end NoBond

/-! ## The kept static hint under `%done` -/

section Kept
variable {snd : Nomm → NeedOrd → Bool}

/-- **The run of a kept static hint under `%done`, step by step**, when
`+sound` of `%this` holds for the formula (then `+past-if` emits nothing). -/
theorem runLCH_n11s_kept_done {env : CallEnv} {tag : Nat} (hs : hintStatic tag = true) {q : Nomm} {body : Noun}
    (hsnd : snd q NeedOrd.this = true) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hr : runLCH env snd true sup (Nomm.n11s tag q body) CGoalL.done region g0 = some (nex, g1)) :
    ∃ nq gc, runLCH env snd true sup q (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 (g0.bo + 1))) region
        (({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩).emitted
          ⟨[], [Pole.hse tag body], Termin.hop (jmp0 g0.bo)⟩) = some (nq, gc) ∧
      nq.th.args = [] ∧
      nex = ⟨mk Sure.bunt [] [(gc.bo, nq.laz)], jmp0 (gc.bo + 1)⟩ ∧
      g1 = ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hsp tag body], Termin.hop (jmp0 gc.bo)⟩ := by
  simp only [runLCH, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
  obtain ⟨n0, ga, h0, hr⟩ := bind_some hr
  rw [simpleNextL_done] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨n1, gb, h1, hr⟩ := bind_some hr
  have hp : HoonSet.small (ofSure (lazyReg g0.re) : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure (lazyReg g0.re) : Lazy S).sure.ned) = true :=
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
  refine ⟨nq, gc, ?_, hta, ?_, ?_⟩
  · simpa only [Gen.emitted] using h3
  · simp [Gen.emitted]
  · rfl

/-- A lazy need with no fork and no bond is its sure part. -/
theorem lazy_eq_ofSure {l : Lazy S} (hf : l.fork = []) (hb : l.bond = []) : l = ofSure l.sure := by
  rw [← Lazy.eta l, hf, hb]; rfl

/-- **`DoneOK` of a kept static hint under `%done`** (`%bout`, `%xray`):
the formula `q` with `LOKSFH` (every member of `CallTreeHU`), `NoBondH` (its
result has no bond, so `+lazy-bound` makes a flat bond) and `+sound` of
`%this` (so `+past-if` emits nothing).  The trace: `%hsp` and `%hse` push
nothing (`QuietP`), so the code's crash inside `q` carries `q`'s trace, as
`+mink` on `[11 tag fq]` (`minkAs_n11s`). -/
theorem n11sKept_done {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fq : Noun} {q : Nomm}
    (H : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fq q) (hcount : sixCount q ≤ 255)
    (hnb : NoBondH (S := S) (Map := Map) snd env q) (hsnd : snd q NeedOrd.this = true)
    {tag : Nat} (hs : hintStatic tag = true) (body : Noun)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH env snd true sup (Nomm.n11s tag q body) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P (n3 (A 11) (A tag) fq) g0 g1 nex := by
  obtain ⟨nq, gc, h3, hta, rfl, rfl⟩ := runLCH_n11s_kept_done hs hsnd hr
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have ua : UpBelow ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩ : Gen Map) := G1.up hu
  have da : ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩ : Gen Map).drop = false := d0
  have G2 : GrowU ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩ : Gen Map)
      (({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩).emitted
        ⟨[], [Pole.hse tag body], Termin.hop (jmp0 g0.bo)⟩) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, Gen.emitted]; omega) ua
  have G12 := G1.trans G2
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := H.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 (g0.bo + 1))
    (region := region) (Or.inr e0) hcount
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G12.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G12)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h3
  have hb0 := (hnb h3).2
  have hq : nq.laz = ofSure nq.laz.sure := lazy_eq_ofSure hfl.1 hb0
  have dc : gc.drop = false := RS.drop.trans d0
  have uc : UpBelow gc := RS.grow.up (G12.up hu)
  have RP := RS.past (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr; simp only [Gen.emitted]; omega)
    (fun e he => by rw [e0] at he; cases he) rfl dc uc region
  have eL : (mk Sure.bunt [] ((gc.bo, mk nq.laz.sure nq.laz.fork []) :: nq.laz.bond) : Lazy S) =
      mk Sure.bunt [] [(gc.bo, nq.laz)] := by
    rw [hb0, hfl.1, ← hfl.1, ← hb0, Lazy.eta]
  rw [eL] at RP
  have RG := RP.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted]; omega)
  have dd : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).drop = false := by
    simp only [tagged_drop, Gen.emitted]; exact dc
  have RF := RG.quietFront (p := Pole.hsp tag body) trivial rfl dd (RG.grow.up (G12.up hu))
  have ebo : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).bo = gc.bo + 1 := by
    simp only [tagged_bo, Gen.emitted]
  rw [ebo] at RF
  have RQ := RF.quietGoal (p := Pole.hse tag body) trivial ua da b0 (by simp only [jmp0, Gen.emitted]; omega) rfl
  have hb : HoonMap.get (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
      ⟨[], [Pole.hsp tag body], Termin.hop (jmp0 gc.bo)⟩).blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    rw [RQ.ext.2.2.2 g0.bo (by simp only [Gen.emitted]; omega)]
    exact hk_emitted_self (g := ({ g0 with re := g0.re + 1 } : Gen Map)) d0 _
  have RD := runOKGB_done hu hcb hb RQ
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = [(gc.bo, nq.laz)] := by
    rw [hq]; simp [entries, bondEntries, forkEntries, ofSure]
  refine ⟨RD.minkAs (minkAs_n11s lib tag fq), ?_, ?_, trivial, ?_⟩
  · rw [hent]; simp [jmp0]
  · refine flat_mk fun e he => ?_
    simp only [List.mem_singleton] at he; subst he; exact hq
  · intro e he
    rw [hent, List.mem_singleton] at he; subst he
    exact H.clean (L := ofSure (lazyReg g0.re)) trivial h3

/-- **The contract of a kept static hint at the top**: both halves for
`[11 tag fq]`, traces included, on every subject of `P`. -/
theorem finishLUCH_contractN11sKept (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {fq : Noun} {q : Nomm}
    (H : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fq q) (hcount : sixCount q ≤ 255)
    (hnb : NoBondH (S := S) (Map := Map) snd env q) (hsnd : snd q NeedOrd.this = true)
    {tag : Nat} (hs : hintStatic tag = true) (body : Noun) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd (Nomm.n11s tag q body) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 11) (A tag) fq) [s] c ∧ ContractBwd lib N s (n3 (A 11) (A tag) fq) [s] c :=
  finishLUCH_contractGB lib N (fun hr => (n11sKept_done H hcount hnb hsnd hs body (by simp [gen0]) rfl upBelow_gen0
    clear_gen0 condBelow_gen0 hr).run) hc

/-- **A kept static hint around a member of `CallTreeHU`** at the top. -/
theorem finishLUCH_contractN11sKeptHU (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {x : Bool} {fq : Noun}
    {q : Nomm} (hq : CallTreeHU lib env N P x fq q) (hnb : NoBondH (S := S) (Map := Map) snd env q)
    (hsnd : snd q NeedOrd.this = true) {tag : Nat} (hs : hintStatic tag = true) (body : Noun) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd (Nomm.n11s tag q body) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 11) (A tag) fq) [s] c ∧ ContractBwd lib N s (n3 (A 11) (A tag) fq) [s] c :=
  finishLUCH_contractN11sKept lib (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env hq).1.1
    (by rw [hq.sixCount]; omega) hnb hsnd hs body hc

end Kept

end Comp
end SkaModel
end Formalization
