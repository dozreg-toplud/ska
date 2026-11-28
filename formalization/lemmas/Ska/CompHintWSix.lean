import lemmas.Ska.CompHintClsSound
import lemmas.Ska.CompSixLSClass
import lemmas.Ska.CompDirectMEq

/-!
# `%6` at the top of hinted code (README Gaps 24)

`+run` on `[6 c a b]` under `%done` (`runLCH`, the case `n6` with a goal
that is not `%next`): both branches run under `%done`, then the blocks `yes`
and `nuh`, `+past-fork` (with a test `+hinted` `|` the fork is left as it
is), the test under `%pick yes nuh`, `+copy` with the fork (the fork not
big: a bound on the branches' entries).

* `SixTopD`: every run under `%done` meets `RunOKGBT` and has at most `k`
  entries; `SixTopD.toDoneG`, `sixTopD_of_doneG` (a bound given), and
  `sixTopD_of_next` (`RegGBT`, `DoneNext`, `ShapeH IsReg k`: the bound of
  the `%next` run behind the block `[don re]`).
* `runLCH_sixTop_apart`: the run taken apart (the text of
  `runLCM_six_done_apartW`, the plain fork only).
* `sixBlk_fwdSixTop`, `sixBlk_bwdSixTop`: `sixBlk_fwd`, `sixBlk_bwd` for a
  branch of `RunOKGBT`.
* **`sixTopD_six`**: `[6 c a b]` under `%done`, the test in `PickD` (no
  hint, no direct call, `+hinted` `|`), the branches in `SixTopD` (the text
  of `six_doneGBWM` with `RunOKGBT` for the branches, the agreement at
  every trace); **`doneG_sixTop`**: its `DoneG`.
* `sixTopLeafB`: a decidable class of pure leaves (`[0 a]`, `[1 k]`, `%3`,
  `%4`, `%5`, a cons), with `sixTopLeafB_sound`; a branch of it is in
  `SixTopD` with the bound `0` (`sixTopD_leaf`), a test of it (no `[0 0]`)
  in `PickD` (`pickD_sixTopLeaf`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Runs under `%done` with a bound on the entries of the result.** -/
abbrev SixTopD (lib : Lib) (N : Needs) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLCH env snd true sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) →
    RunOKGBT lib N P f (CGoal.done : CGoal S) g0 g1 nex ∧ (entries nex.laz).length ≤ k

section
variable {lib : Lib} {N : Needs} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {P : Noun → Prop} {f : Noun}
  {nm : Nomm} {k : Nat}

theorem SixTopD.toDoneG (H : SixTopD (S := S) (Map := Map) lib N env snd P f nm k) :
    DoneG (S := S) (Map := Map) lib N env snd P f nm :=
  fun b0 d0 hu hcl hcb hr => (H b0 d0 hu hcl hcb hr).1

/-- `DoneG` with a bound on the entries of every run under `%done`. -/
theorem sixTopD_of_doneG (H : DoneG (S := S) (Map := Map) lib N env snd P f nm)
    (hk : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}, g0.drop = false →
      runLCH env snd true sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) → (entries nex.laz).length ≤ k) :
    SixTopD (S := S) (Map := Map) lib N env snd P f nm k :=
  fun b0 d0 hu hcl hcb hr => ⟨H b0 d0 hu hcl hcb hr, hk d0 hr⟩

/-- **A run under `%done` that is the block `[don re]` then the run under
`%next (lazy-from-reg re)`**: `RegGBT` gives the run, `ShapeH IsReg k` the
bound. -/
theorem sixTopD_of_next (H : RegGBT (S := S) (Map := Map) snd lib N env P f nm)
    (hD : DoneNext (S := S) (Map := Map) env snd nm) (hS : ShapeH (S := S) (Map := Map) snd env IsReg nm k) :
    SixTopD (S := S) (Map := Map) lib N env snd P f nm k := by
  refine sixTopD_of_doneG (doneG_of_next H hD) (fun {sup region g0 g1 nex} d0 hr => ?_)
  rw [hD] at hr
  exact (hS ⟨g0.re, rfl⟩ (by simpa [Gen.emitted] using d0) rfl hr).2.2

end

/-! ## The run taken apart -/

/-- **`[6 c a b]` under `%done` taken apart**, the test `+hinted` `|` (the
fork left as it is): the text of `runLCM_six_done_apartW`. -/
theorem runLCH_sixTop_apart (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (sup : Option Nomm) {c a b : Nomm}
    (hcfk : hinted env.cod c = some false) {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (h : runLCH env snd true sup (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    ∃ (x1 x0 xc : NextL S) (g1 g2 g3 : Gen Map),
      runLCH env snd true sup b CGoalL.done region g0 = some (x1, g1) ∧
      runLCH env snd true sup a CGoalL.done region g1 = some (x0, g2) ∧
      x0.th.args = [] ∧ x1.th.args = [] ∧
      runLCH env snd true sup c (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region (sixGenL g2 x0.th x1.th region) =
        some (xc, g3) ∧
      (lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false →
        copyL xc (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) g3 = some (nex, g4)) := by
  simp only [runLCH] at h
  obtain ⟨x1, g1, h1, h⟩ := bind_some h
  obtain ⟨x0, g2, h2, h⟩ := bind_some h
  simp only [bind_apply, emit_apply, setTag_apply, Option.bind_some] at h
  by_cases a0' : x0.th.args ≠ []
  · simp [a0'] at h
  have a0 : x0.th.args = [] := by simpa using a0'
  by_cases a1' : x1.th.args ≠ []
  · simp [a0, a1'] at h
  have a1 : x1.th.args = [] := by simpa using a1'
  simp only [a0, a1, ne_eq, not_true_eq_false, if_false] at h
  obtain ⟨lz, gl, hl, h⟩ := bind_some h
  simp only [liftO] at hl
  obtain ⟨lz', hpf, e⟩ := Option.map_eq_some_iff.mp hl
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨xc, g3, h3, h⟩ := bind_some h
  have hlz : lz' = mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] [] := by
    unfold pastFork at hpf
    rw [hcfk] at hpf
    simp only [Option.some.injEq] at hpf
    rw [← hpf]
    simp only [emitted_bo]
  subst hlz
  refine ⟨x1, x0, xc, g1, g2, g3, h1, h2, a0, a1, h3, fun hbig => ?_⟩
  have hcond : (!(lazyBig (softLess noSoft (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] [])))) =
      true := by
    rw [softLess_noSoft, hbig]; rfl
  rw [if_pos hcond] at h
  exact h

/-! ## A block of the fork, for a branch of `RunOKGBT` -/

/-- **A lazy block of the fork, forward** (`sixBlk_fwd` for `RunOKGBT`). -/
theorem sixBlk_fwdSixTop {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S}
    (Rx : RunOKGBT lib N P f (CGoal.done : CGoal S) gA gB x)
    {cf : Map (Nat × List Nat)} {cc : Straight Map} {ned : Need} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs}
    {O : Oracle σ} {n : Nat} {gul : Noun} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hF : OracleFwd lib Inv ν O n) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ (st' : σ) (t' : Trace), AgreeUB lib O cc gul st' t' cf ned gA gB x.laz s0 s)
    {st : σ} {tm : Trace} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {R2 : Map (Option Noun)} (hR2 : HoldsN ned R2 s0) {r : Tone} (hm : minkF lib gul n tm s f = some r) :
    ReturnsC lib O cc gul Inv ν st R2 t (jmp0 o) r := by
  obtain ⟨A, hcb, hFl⟩ := hblk st
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy; have := ((Rx.regs y hy').resolve_left (fun e => e)).2; omega
  by_cases fi : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hFl hR2 x.th).1 fi
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    exact returnsC_step (Needs.le_refl _) (e0.trans e3)
      (Rx.sem cf hcf cc ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag
        (fun y hy => Nat.le_trans hlo (hned y hy)) R3 hh3 hn3)
  · have hb := (Rx.nec s hs fi).1 gul n tm r hm
    have e2 : r = Tone.two tm := by
      rcases hb with e | ⟨p, _, hp⟩
      · exact e
      · exact hp.elim
    subst e2
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, e0.trans ((fillSem_runK hFl hR2 x.th).2 fi), ToneRel.two htr⟩

/-- **A lazy block of the fork, backward** (`sixBlk_bwd` for `RunOKGBT`). -/
theorem sixBlk_bwdSixTop {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S}
    (Rx : RunOKGBT lib N P f (CGoal.done : CGoal S) gA gB x)
    {cf : Map (Nat × List Nat)} {cc : Straight Map} {ned : Need} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs}
    {O : Oracle σ} {gul : Noun} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hB : OracleBwd lib Inv ν O) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ (st' : σ) (t' : Trace), AgreeUB lib O cc gul st' t' cf ned gA gB x.laz s0 s)
    {st : σ} {tm : Trace} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {R2 : Map (Option Noun)} (hR2 : HoldsN ned R2 s0) {res : Tone × σ}
    (hres : goJ lib O cc gul st R2 t (jmp0 o) = some res) :
    ∃ r, Mink lib gul tm s f r ∧ ReturnsC lib O cc gul Inv ν st R2 t (jmp0 o) r := by
  obtain ⟨A, hcb, hFl⟩ := hblk st
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy; have := ((Rx.regs y hy').resolve_left (fun e => e)).2; omega
  by_cases fi : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hFl hR2 x.th).1 fi
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    obtain ⟨r, hr, G⟩ := Rx.semB cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag
      (fun y hy => Nat.le_trans hlo (hned y hy)) R3 hh3 hn3 res ((e0.trans e3).symm.trans hres)
    exact ⟨r, hr, returnsC_step (Needs.le_refl _) (e0.trans e3) G⟩
  · obtain ⟨r, hr, hb⟩ := (Rx.nec s hs fi).2 gul tm
    have e2 : r = Tone.two tm := by
      rcases hb with e | ⟨p, _, hp⟩
      · exact e
      · exact hp.elim
    subst e2
    exact ⟨_, hr, Tone.two t, st, hI, Needs.le_refl _, e0.trans ((fillSem_runK hFl hR2 x.th).2 fi),
      ToneRel.two htr⟩

/-- `omega` after reducing the projections of the states. -/
local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

/-! ## `[6 c a b]` under `%done` -/

/-- **`[6 c a b]` under `%done` in hinted code**: the test in `PickD`
(no hint, no direct call, `+hinted` `|`, so the fork is plain), the
branches in `SixTopD` (any hinted code whose `%done` runs meet `RunOKGBT`,
their entries bounded so that the fork is not big).  The text of
`six_doneGBWM` on the real result, with `sixBlk_fwdSixTop`,
`sixBlk_bwdSixTop` at the branches and the agreement at every trace. -/
theorem sixTopD_six (lib : Lib) {N : Needs} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {P : Noun → Prop}
    {fc fa fb : Noun} {c a b : Nomm} {kc ka kb : Nat}
    (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (hch : c.noHint = true) (hcd : c.noDirect = true) (hcfk : hinted env.cod c = some false)
    (Ha : SixTopD (S := S) (Map := Map) lib N env snd P fa a ka)
    (Hb : SixTopD (S := S) (Map := Map) lib N env snd P fb b kb) (hk : ka + kb + 5 ≤ lazyMax) :
    SixTopD (S := S) (Map := Map) lib N env snd P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (kc + ka + kb + 4) := by
  intro sup region g0 g4 nex b0 d0 hu hcl0 hcb0 h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, hx0a, hx1a, h3, hrest⟩ := runLCH_sixTop_apart env snd sup hcfk h
  rw [runLCH_eq env snd true c hch, runLCM_true env hcd] at h3
  obtain ⟨Rb, sb⟩ := Hb b0 d0 hu hcl0 hcb0 h1
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have cl1 : Clear g1 := hcl0.growU Rb.grow
  have cb1 : CondBelow g1 := Rb.cfr.below hcb0
  obtain ⟨Ra, sa⟩ := Ha b1 d1 u1 cl1 cb1 h2
  have lo0 : 1 ≤ x0.th.there := Ra.lo
  have hi0 : x0.th.there < g2.bo := Ra.hi
  have lo1 : 1 ≤ x1.th.there := Rb.lo
  have hi1 : x1.th.there < g1.bo := Rb.hi
  have cl2 : Clear g2 := cl1.growU Ra.grow
  have cb2 : CondBelow g2 := Ra.cfr.below cb1
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop lo0 hi0)
    (jumpsBelow_hop lo1 (by omega))).toU u2
  have uG : UpBelow (sixGenL g2 x0.th x1.th region) := GU.up u2
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    omega
  -- the test
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  obtain ⟨Rc, sc⟩ := Hc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩
    (by simp only [sixGenL_bo]; omega) dG uG (cl2.growU GU)
    (fun k hk => by simp only [sixGenL_cond, sixGenL_re] at hk ⊢; exact cb2 k hk) h3
  have u3 : UpBelow g3 := Rc.grow.up uG
  have d3 : g3.drop = false := Rc.ext.2.2.1.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Rc.ext.2.1; simpa using this
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ g2.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; simp only [sixGenL_bo] at this; omega
  have hcp' := hrest hbig
  rw [copyL_six_apart xc x0.laz x1.laz g2.bo (g2.bo + 1) g3 hap] at hcp'
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp'
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨A4, r4, bo4, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r4 bo4
  -- the states
  have E2 : Ext g2 (sixGenL g2 x0.th x1.th region) := ext_sixGenL _ _ _ _
  have E4 : Ext g3 g4' := (ext_emit g3 _).trans (ext_addOps_nil hadd)
  have E24 : Ext g2 g4' := E2.trans (Rc.ext.trans E4)
  have E14 : Ext g1 g4' := Ra.ext.trans E24
  have E04 : Ext g0 g4' := Rb.ext.trans E14
  have re01 := Rb.ext.1
  have re12 := Ra.ext.1
  have re2G : g2.re ≤ g3.re := by have := Rc.ext.1; simpa using this
  have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4'.blocks k = HoonMap.get g3.blocks k := fun k hk =>
    (A4 k).trans (get_emitted_ne hk)
  have h4o : HoonMap.get g4'.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A4 g3.bo).trans (emitted_get g3 _ d3)
  have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k =
      HoonMap.get (sixGenL g2 x0.th x1.th region).blocks k := fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
  have h4y : HoonMap.get g4'.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_y _ _ _ d2
  have h4n : HoonMap.get g4'.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_n _ _ _ d2
  have h42 : ∀ k, k < g2.bo → HoonMap.get g4'.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
  have h41 : ∀ k, k < g1.bo → HoonMap.get g4'.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
  -- the registers of the parts
  have raR : ∀ r, NMem x0.laz.sure.ned r → g1.re ≤ r ∧ r < g2.re := fun r hr =>
    (Ra.regs r hr).resolve_left (fun e => e)
  have rbR : ∀ r, NMem x1.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re := fun r hr =>
    (Rb.regs r hr).resolve_left (fun e => e)
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    have := Rc.labs e he; simp only [sixGenL_bo] at this; exact ⟨this.1, this.2.1⟩
  have la : ∀ e ∈ entries x0.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(Ra.labs e he).1, (Ra.labs e he).2.1⟩
  have lb : ∀ e ∈ entries x1.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(Rb.labs e he).1, (Rb.labs e he).2.1⟩
  have lc' := labels_bound (P := fun o => g2.bo + 2 ≤ o ∧ o < g3.bo) lc
  have la' := labels_bound (P := fun o => g1.bo ≤ o ∧ o < g2.bo) la
  have lb' := labels_bound (P := fun o => g0.bo ≤ o ∧ o < g1.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    g2.bo (g2.bo + 1) x0.laz x1.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (g2.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (g2.bo + 1, x1.laz) ∨
        e ∈ entries x1.laz := by
    intro e; rw [en]; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have labAll : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond),
      (g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo ∧ e ∈ entries xc.laz) ∨ e.1 = g2.bo ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo ∧ e ∈ entries x0.laz) ∨ e.1 = g2.bo + 1 ∨
      (g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧ e ∈ entries x1.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have hc43 : g4'.cond = g3.cond := by rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond]
  have cf34 : CondFresh g3 g4' := condFresh_of_eq E4.1 hc43
  have cfG : CondFresh g2 (sixGenL g2 x0.th x1.th region) :=
    condFresh_of_eq (by simp only [sixGenL_re]; omega) (by rw [sixGenL_cond])
  have cf24 : CondFresh g2 g4' := cfG.trans (Rc.cfr.trans cf34)
  have cf14 : CondFresh g1 g4' := Ra.cfr.trans cf24
  have hxca : xc.th.args = [] := by
    rcases Rc.ent with ⟨_, _, _, e⟩ | e
    · exact e
    · simp only [GoalJ] at e; rcases e with e | e <;> rw [e] <;> rfl
  -- what the program gives the parts
  have core : ∀ (cf : Map (Nat × List Nat)) (cc : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ)
      (gul : Noun) (t : Trace) (s0 s : Noun) (st : σ),
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g0 g4'
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) s0 s) →
      HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned (sixGenL g2 x0.th x1.th region) g3 xc.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks g2.bo = some ⟨[], A, Termin.hop x0.th⟩ ∧
        FillSem lib O cc gul st' t ned g4'.re x0.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g1 g2 x0.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks (g2.bo + 1) = some ⟨[], A, Termin.hop x1.th⟩ ∧
        FillSem lib O cc gul st' t ned g4'.re x1.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g0 g1 x1.laz s0 s) := by
    intro cf cc ned σ O gul t s0 s st ag
    have notLab : ∀ o, g0.bo ≤ o → o < g4'.bo → (g3.bo ≤ o ∨
        (g2.bo + 2 ≤ o ∧ o < g3.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (g1.bo ≤ o ∧ o < g2.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < g1.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = (HoonMap.get g4'.blocks o).map (unproxyBlob cf) := by
      intro o h0 h1 hc'
      refine (ag st).1 o h0 h1 fun hm => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases labAll e he with ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩
      · rcases hc' with y | ⟨_, _, y⟩ | y | y
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | ⟨_, _, y⟩ | y
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | y | ⟨_, y⟩
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
    have fork : ∀ (o : Nat) (x : NextL S) (st' : σ), (o, x.laz) ∈ entries
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) →
        HoonMap.get g4'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → x.th.args = [] →
        ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
          FillSem lib O cc gul st' t ned g4'.re x.laz.sure A s0 s := by
      intro o x st' hm hb hxa
      obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 _ hm
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨A, by rw [hcb]; simp [renJmp_nil _ hxa], hF⟩
    refine ⟨?_, fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩,
      fun st' => fork g2.bo x0 st' ((memE _).mpr (Or.inr (Or.inl rfl))) h4y hx0a,
      fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩,
      fun st' => fork (g2.bo + 1) x1 st' ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h4n hx1a,
      fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩⟩
    · rw [notLab g3.bo (by omega) (by omega) (Or.inl (Nat.le_refl _)), h4o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hxca]
    · simp only [sixGenL_bo] at h0
      rw [notLab o (by omega) (by omega) (Or.inr (Or.inl ⟨h0, h1, hnl⟩)), h4k o (by omega)]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inl he))
      exact ⟨A, B, th, (h4k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩))), h42 o h1]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
      exact ⟨A, B, th, (h42 _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩))), h41 o h1]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
      exact ⟨A, B, th, (h41 _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
  refine ⟨⟨E04, ?_, Rb.cfr.trans cf14, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h4o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, fun s hs hfs => ?_,
    fun r hr => by rw [hc43]; exact Rc.ncond r hr, ?_, ?_, ?_⟩, ?_⟩
  · -- grow
    have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) u3
    exact Rb.grow.trans (Ra.grow.trans (GU.trans
      (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up u3))))))
  · -- regs
    have := (Rc.regs r hr).resolve_left (fun e => e); simp only [sixGenL_re] at this
    exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · refine ⟨(Rc.eregs e h).1, fun r hr => ?_⟩
      have := (Rc.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e); simp only [sixGenL_re] at h1'
      exact ⟨Or.inr (by omega), by omega⟩
    · exact ⟨Ra.dist, fun r hr => ⟨Or.inr (by have := raR r hr; omega), by have := raR r hr; omega⟩⟩
    · refine ⟨(Ra.eregs e h).1, fun r hr => ?_⟩
      have := (Ra.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e)
      exact ⟨Or.inr (by omega), by omega⟩
    · exact ⟨Rb.dist, fun r hr => ⟨Or.inr (by have := rbR r hr; omega), by have := rbR r hr; omega⟩⟩
    · refine ⟨(Rb.eregs e h).1, fun r hr => ?_⟩
      have := (Rb.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e)
      exact ⟨Or.inr (by omega), by omega⟩
  · -- labs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · obtain ⟨_, _, B, th, hth⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, B, th, (h4k _ (by omega)).trans hth⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x0.th, h4y⟩
    · obtain ⟨_, _, B, th, hth⟩ := Ra.labs e h
      have := la e h
      exact ⟨by omega, by omega, B, th, (h42 _ this.2).trans hth⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x1.th, h4n⟩
    · obtain ⟨l1, _, B, th, hth⟩ := Rb.labs e h
      have := lb e h
      exact ⟨l1, by omega, B, th, (h41 _ this.2).trans hth⟩
  · -- nodup
    rw [en, List.map_append, List.nodup_append, List.map_append, List.nodup_append]
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_append]
    refine ⟨Rc.nodup, ⟨⟨fun hm => by have := la' _ hm; omega, Ra.nodup⟩,
      ⟨fun hm => by have := lb' _ hm; omega, Rb.nodup⟩, fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · have hx' : g1.bo ≤ x ∧ x ≤ g2.bo := by
        rcases hx with e | e
        · omega
        · have := la' x e; omega
      rcases hy with e | e
      · omega
      · have := lb' y e; omega
    · have := lc' x hx
      rcases hy with (e | e) | (e | e)
      · omega
      · have := la' y e; omega
      · omega
      · have := lb' y e; omega
  · -- nec
    have fo' : ¬ FitsS xc.laz.sure s := fun f => hfs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    obtain ⟨N1, N2⟩ := Rc.nec s hs fo'
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
      have e2 : rb = Tone.two tm := by
        rcases N1 gul n' tm rb hb with e | ⟨p, _, hp⟩
        · exact e
        · exact hp.elim
      subst e2
      rcases hcase with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨p, e, _⟩
      · exact Or.inl e
      · cases e
      · cases e
      · cases e
    · obtain ⟨rb, hb, hbad⟩ := N2 gul tm
      have e2 : rb = Tone.two tm := by
        rcases hbad with e | ⟨p, _, hp⟩
        · exact e
        · exact hp.elim
      subst e2
      exact ⟨_, (mink_sixC_bwd (fc := fa) (fd := fb) hb).1 (fun _ e => by cases e), Or.inl rfl⟩
  · -- econd
    intro e he r hr
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · rw [hc43]; exact Rc.econd e h r hr
    · rw [cf24.get_lt (raR r hr).2]; exact Ra.ncond r hr
    · rw [cf24.get_lt ((Ra.eregs e h).2 r hr).2]; exact Ra.econd e h r hr
    · rw [cf14.get_lt (rbR r hr).2]; exact Rb.ncond r hr
    · rw [cf14.get_lt ((Rb.eregs e h).2 r hr).2]; exact Rb.econd e h r hr
  · -- forward
    intro cf hcf cc ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hc3, agC, yesB, -, nuhB, -⟩ := core cf cc ned σ O gul t s0 s st (fun st' => ag st' t)
    have agA : ∀ (st' : σ) (t' : Trace), AgreeUB lib O cc gul st' t' cf ned g1 g2 x0.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st' (fun st'' => ag st'' t')).2.2.2.1 st'
    have agB : ∀ (st' : σ) (t' : Trace), AgreeUB lib O cc gul st' t' cf ned g0 g1 x1.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st' (fun st'' => ag st'' t')).2.2.2.2.2 st'
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf24.get_lt hk)
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf14.get_lt hk)
    obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
    have Gc := Rc.sem cf hcf3 cc ned σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rb
      hI htr hs hb agC (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    show ReturnsC lib O cc gul Inv ν st regs t (jmp0 g3.bo) r
    rcases hcase with ⟨hnz, hrr⟩ | ⟨rfl, ha⟩ | ⟨rfl, hb'⟩ | ⟨p, rfl, h0, h1, rfl⟩
    · rw [hrr]
      cases rb with
        | zero q => exact absurd rfl (hnz q)
        | one q => exact returnsC_step (Needs.le_refl _) e0 Gc
        | two q => exact returnsC_step (Needs.le_refl _) e0 Gc
    · obtain ⟨G0, -, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwdSixTop Ra hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf2
        (by omega) hned hs yesB agA hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ha)
    · obtain ⟨-, G1, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwdSixTop Rb hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf1
        (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) hb')
    · obtain ⟨-, -, G2⟩ := Gc
      exact returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)
  · -- backward
    intro cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hc3, agC, yesB, -, nuhB, -⟩ := core cf cc ned σ O gul t s0 s st (fun st' => ag st' t)
    have agA : ∀ (st' : σ) (t' : Trace), AgreeUB lib O cc gul st' t' cf ned g1 g2 x0.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st' (fun st'' => ag st'' t')).2.2.2.1 st'
    have agB : ∀ (st' : σ) (t' : Trace), AgreeUB lib O cc gul st' t' cf ned g0 g1 x1.laz s0 s := fun st' t' =>
      (core cf cc ned σ O gul t' s0 s st' (fun st'' => ag st'' t')).2.2.2.2.2 st'
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf24.get_lt hk)
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf14.get_lt hk)
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    obtain ⟨rb, hmb, Gc⟩ := Rc.semB cf hcf3 cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs agC
      (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn res
      (e0.symm.trans hres)
    have MB := mink_sixC_bwd (fc := fa) (fd := fb) hmb
    show ∃ r, Mink lib gul tm s (n4 (A 6) fc fa fb) r ∧ ReturnsC lib O cc gul Inv ν st regs t (jmp0 g3.bo) r
    cases rb with
    | zero p =>
      by_cases h0 : p = A 0
      · subst h0
        obtain ⟨G0, -, -⟩ := Gc
        obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
        obtain ⟨r, hr, G⟩ := sixBlk_bwdSixTop Ra hN hS hB hcf2 (by omega) hned hs yesB agA hI' (frames_mono hν htr)
          (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
        exact ⟨r, MB.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
      · by_cases h1 : p = A 1
        · subst h1
          obtain ⟨-, G1, -⟩ := Gc
          obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
          obtain ⟨r, hr, G⟩ := sixBlk_bwdSixTop Rb hN hS hB hcf1 (by omega) hned hs nuhB agB hI'
            (frames_mono hν htr) (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn)
            ((e0.trans e2).symm.trans hres)
          exact ⟨r, MB.2.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
        · obtain ⟨-, -, G2⟩ := Gc
          exact ⟨_, MB.2.2.2 p rfl h0 h1, returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)⟩
    | one q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
    | two q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
  · -- the bound
    rw [entries_copy_six]; simp only [List.length_append, List.length_cons]
    omega

/-- **`[6 c a b]` under `%done` in `DoneG`** (`sixTopD_six`). -/
theorem doneG_sixTop (lib : Lib) {N : Needs} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {P : Noun → Prop}
    {fc fa fb : Noun} {c a b : Nomm} {kc ka kb : Nat}
    (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (hch : c.noHint = true) (hcd : c.noDirect = true) (hcfk : hinted env.cod c = some false)
    (Ha : SixTopD (S := S) (Map := Map) lib N env snd P fa a ka)
    (Hb : SixTopD (S := S) (Map := Map) lib N env snd P fb b kb) (hk : ka + kb + 5 ≤ lazyMax) :
    DoneG (S := S) (Map := Map) lib N env snd P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) :=
  SixTopD.toDoneG (sixTopD_six lib Hc hch hcd hcfk Ha Hb hk)

/-! ## Pure leaves: branches and tests -/

/-- The formula of a pure leaf (`[0 a]`, `[1 k]`, `%3`, `%4`, `%5`, a cons);
with `t` the axes are not `0` (a test: `FragX`). -/
def sixTopFol (t : Bool) : Nomm → Option Noun
  | Nomm.n0 a => if t = false ∨ 1 ≤ a then some (slot a) else Option.none
  | Nomm.n1 k => some (quote k)
  | Nomm.n3 p => (sixTopFol t p).map (n2 (A 3))
  | Nomm.n4 p => (sixTopFol t p).map (n2 (A 4))
  | Nomm.n5 p q =>
      match sixTopFol t p, sixTopFol t q with
      | some b, some c => some (n3 (A 5) b c)
      | _, _ => Option.none
  | Nomm.cons p q =>
      match sixTopFol t p, sixTopFol t q with
      | some (Noun.cell a1 a2), some c => some (C (C a1 a2) c)
      | _, _ => Option.none
  | _ => Option.none

/-- **The check of a pure leaf**: `f` is the formula of `nm`. -/
def sixTopLeafB (t : Bool) (f : Noun) (nm : Nomm) : Bool := sixTopFol t nm == some f

theorem sixTopFol_sound (t : Bool) : ∀ (nm : Nomm) (f : Noun), sixTopFol t nm = some f →
    (∃ x, CallTreeA x f nm) ∧ nm.pure = true ∧ noSix nm = true ∧ nm.noHint = true ∧ nm.noDirect = true ∧
      (t = true → FragX (S := S) nm)
  | Nomm.n0 a, f, h => by
    simp only [sixTopFol] at h
    split at h
    · rename_i ha
      cases h
      exact ⟨⟨_, CallTreeA.n0 a⟩, rfl, rfl, rfl, rfl, fun ht => fragX_n0 (by subst ht; simpa using ha)⟩
    · cases h
  | Nomm.n1 k, f, h => by
    simp only [sixTopFol, Option.some.injEq] at h
    subst h
    exact ⟨⟨_, CallTreeA.n1 k⟩, rfl, rfl, rfl, rfl, fun _ => FragX.frag (nm := Nomm.n1 k) fun _ => trivial⟩
  | Nomm.n3 p, f, h => by
    simp only [sixTopFol] at h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨⟨x, hx⟩, hp, h6, hh, hd, hf⟩ := sixTopFol_sound t p b hb
    exact ⟨⟨_, CallTreeA.three hx⟩, hp, h6, hh, hd, fun ht => FragX.three (hf ht)⟩
  | Nomm.n4 p, f, h => by
    simp only [sixTopFol] at h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨⟨x, hx⟩, hp, h6, hh, hd, hf⟩ := sixTopFol_sound t p b hb
    exact ⟨⟨_, CallTreeA.four hx⟩, hp, h6, hh, hd, fun ht => FragX.four (hf ht)⟩
  | Nomm.n5 p q, f, h => by
    simp only [sixTopFol] at h
    split at h
    · rename_i b c hb hc
      cases h
      obtain ⟨⟨x, hx⟩, hp, h6, hh, hd, hf⟩ := sixTopFol_sound t p b hb
      obtain ⟨⟨y, hy⟩, hp', h6', hh', hd', hf'⟩ := sixTopFol_sound t q c hc
      exact ⟨⟨_, CallTreeA.five hx hy⟩, by simp [Nomm.pure, hp, hp'], by simp [noSix, h6, h6'],
        by simp [Nomm.noHint, hh, hh'], by simp [Nomm.noDirect, hd, hd'], fun ht => FragX.five (hf ht) (hf' ht)⟩
    · cases h
  | Nomm.cons p q, f, h => by
    simp only [sixTopFol] at h
    split at h
    · rename_i a1 a2 c hb hc
      cases h
      obtain ⟨⟨x, hx⟩, hp, h6, hh, hd, hf⟩ := sixTopFol_sound t p _ hb
      obtain ⟨⟨y, hy⟩, hp', h6', hh', hd', hf'⟩ := sixTopFol_sound t q c hc
      exact ⟨⟨_, CallTreeA.cons hx hy⟩, by simp [Nomm.pure, hp, hp'], by simp [noSix, h6, h6'],
        by simp [Nomm.noHint, hh, hh'], by simp [Nomm.noDirect, hd, hd'], fun ht => FragX.cons (hf ht) (hf' ht)⟩
    · cases h
  | Nomm.n2 _ _ _, f, h => by simp [sixTopFol] at h
  | Nomm.n6 _ _ _, f, h => by simp [sixTopFol] at h
  | Nomm.n7 _ _, f, h => by simp [sixTopFol] at h
  | Nomm.n10 _ _ _, f, h => by simp [sixTopFol] at h
  | Nomm.n11s _ _ _, f, h => by simp [sixTopFol] at h
  | Nomm.n11d _ _ _ _, f, h => by simp [sixTopFol] at h
  | Nomm.n12 _ _, f, h => by simp [sixTopFol] at h
  | Nomm.mean _ _ _ _ _, f, h => by simp [sixTopFol] at h

theorem sixTopLeafB_sound {t : Bool} {f : Noun} {nm : Nomm} (h : sixTopLeafB t f nm = true) :
    (∃ x, CallTreeA x f nm) ∧ nm.pure = true ∧ noSix nm = true ∧ nm.noHint = true ∧ nm.noDirect = true ∧
      (t = true → FragX (S := S) nm) :=
  sixTopFol_sound t nm f (by simpa [sixTopLeafB] using h)

/-- **A pure leaf as a branch**: `SixTopD` with the bound `0`
(`sixD_of_callTreeA` on `runLC`, `runLCH_eq`, `runLCM_true`). -/
theorem sixTopD_leaf (lib : Lib) {N : Needs} (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (P : Noun → Prop)
    {t : Bool} {f : Noun} {nm : Nomm} (h : sixTopLeafB t f nm = true) :
    SixTopD (S := S) (Map := Map) lib N env snd P f nm 0 := by
  obtain ⟨⟨x, hA⟩, hp, h6, hh, hd, -⟩ := sixTopLeafB_sound (S := S) h
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [runLCH_eq env snd true nm hh, runLCM_true env hd] at hr
  obtain ⟨R, hk⟩ := sixD_of_callTreeA (S := S) (Map := Map) lib (N := N) env hA (NoEntF.pure hp h6) P
    b0 d0 hu hcl hcb hr
  exact ⟨R.toT, hk⟩

/-- **A pure leaf with no `[0 0]` as a test**: `PickD` with the bound `0`
(`SixTest.pure`, `sixTest_pickD`), no hint, no direct call, `+hinted` `|`. -/
theorem pickD_sixTopLeaf (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) {fc : Noun} {c : Nomm}
    (h : sixTopLeafB true fc c = true) :
    PickD (S := S) (Map := Map) lib N env P fc c 0 ∧ c.noHint = true ∧ c.noDirect = true ∧
      ∀ cod, hinted cod c = some false := by
  obtain ⟨⟨x, hA⟩, hp, h6, hh, hd, hf⟩ := sixTopLeafB_sound (S := S) h
  exact ⟨sixTest_pickD lib env P (SixTest.pure (hf rfl) hA hp), hh, hd, fun cod => hinted_pure cod c hp⟩

-- the real tests and branches
example : sixTopLeafB true (n3 (A 5) (slot 1) (quote (A 0))) (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 0))) = true := by decide
example : sixTopLeafB true (n3 (A 5) (slot 30) (n2 (A 4) (slot 6)))
    (Nomm.n5 (Nomm.n0 30) (Nomm.n4 (Nomm.n0 6))) = true := by decide
example : sixTopLeafB false (slot 0) (Nomm.n0 0) = true := by decide

end Comp
end SkaModel
end Formalization
