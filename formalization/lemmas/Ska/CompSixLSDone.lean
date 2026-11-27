import lemmas.Ska.CompSixLSPick
import lemmas.Ska.CompSevenA
import lemmas.Ska.CompSixLSCheck

/-!
# `[6 c a b]` under `%done` with calling branches: `six_doneGB`

README Gaps 12.34, step 1.  Under `%done` the branches of a `%6` run under
`%done` themselves (no branch first, then yes), the blocks `yes: [hop a's
jump]` and `nuh: [hop b's jump]` follow, the test runs under `%pick (jmp0 yes)
(jmp0 nuh)`, and `+copy` puts the fork `[bunt [[yes a's need] [nuh b's
need]] ~]` beside the test's need, behind one more block
(`runLC_six_done_apart`).  With a call-free test `+past-fork` is the
identity, so the labels of the entries stay distinct.

`RunOKGB` has no size, so the relations here carry a bound on the number of
entries (`SixD`, `PickD`): `+lazy-shut` fires only when the fork is big,
and the bound of the branches keeps it below `lazyMax`.

* `minkF_sixC`, `mink_sixC_bwd`: `+mink` on `[6 b c d]`, forward and back.
* `SixD`, `PickD`: what a branch under `%done` and a test under `%pick`
  give (`RunOKGB` and a bound on the entries).
* `runLC_six_done_apart`: the run taken apart.
* `six_doneGB`: `[6 c a b]` under `%done` meets `RunOKGB` (the analogue of
  `sixP_okV`, forward and backward, the fills of `yes` and `nuh` by
  `AgreeUB`'s `FillSem` at the fork's labels).
* `pickD_of_uok`, `sixD_of_callTreeA`: a call-free test with `UOK`, a branch
  of `CallTreeA` whose need has no entries (`NoEntF`).
* `finishLUC_contractSixD`: the top.
* `six3_contract`: `[6 [3 [0 2]] [2 [0 6] [0 7]] [0 3]]` meets both halves
  of the contract.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+mink` on `[6 b c d]` -/

/-- **`+mink` on `[6 b c d]`**: `b` runs with one less fuel; a tone of it
that is no product is the whole's, `0` and `1` run `c` and `d` with that
fuel, another product is a crash with the trace. -/
theorem minkF_sixC {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s fb fc fd : Noun} {r : Tone}
    (h : minkF lib gul n tm s (n4 (A 6) fb fc fd) = some r) :
    ∃ n', n' < n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧
      (((∀ q, rb ≠ Tone.zero q) ∧ r = rb) ∨
       (rb = Tone.zero (A 0) ∧ minkF lib gul n' tm s fc = some r) ∨
       (rb = Tone.zero (A 1) ∧ minkF lib gul n' tm s fd = some r) ∨
       (∃ p, rb = Tone.zero p ∧ p ≠ A 0 ∧ p ≠ A 1 ∧ r = Tone.two tm)) := by
  cases n with
  | zero => simp [minkF] at h
  | succ n' =>
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    refine ⟨n', Nat.lt_succ_self n', ?_⟩
    cases eb : minkF lib gul n' tm s fb with
    | none => rw [eb] at h; simp [tbind] at h
    | some rb =>
      rw [eb] at h
      refine ⟨rb, rfl, ?_⟩
      cases rb with
      | zero u =>
        simp only [tbind] at h
        rcases u with ⟨_ | _ | k⟩ | ⟨x, y⟩
        · exact Or.inr (Or.inl ⟨rfl, h⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
        · simp only [Option.some.injEq] at h
          exact Or.inr (Or.inr (Or.inr ⟨_, rfl, (fun e => by cases e), (fun e => by cases e), h.symm⟩))
        · simp only [Option.some.injEq] at h
          exact Or.inr (Or.inr (Or.inr ⟨_, rfl, (fun e => by cases e), (fun e => by cases e), h.symm⟩))
      | one q =>
        simp only [tbind, Option.some.injEq] at h
        exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
      | two t' =>
        simp only [tbind, Option.some.injEq] at h
        exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩

/-- **`+mink` on `[6 b c d]`, backward.** -/
theorem mink_sixC_bwd {lib : Lib} {gul : Noun} {tm : Trace} {s fb fc fd : Noun} {rb : Tone}
    (hb : Mink lib gul tm s fb rb) :
    ((∀ q, rb ≠ Tone.zero q) → Mink lib gul tm s (n4 (A 6) fb fc fd) rb) ∧
    (∀ r, rb = Tone.zero (A 0) → Mink lib gul tm s fc r → Mink lib gul tm s (n4 (A 6) fb fc fd) r) ∧
    (∀ r, rb = Tone.zero (A 1) → Mink lib gul tm s fd r → Mink lib gul tm s (n4 (A 6) fb fc fd) r) ∧
    (∀ p, rb = Tone.zero p → p ≠ A 0 → p ≠ A 1 → Mink lib gul tm s (n4 (A 6) fb fc fd) (Tone.two tm)) := by
  obtain ⟨n1, e1⟩ := hb
  refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun r eu hc => ?_, fun r eu hc => ?_, fun p eu h0 h1 => ⟨n1 + 1, ?_⟩⟩
  · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1]
    cases rb with
    | zero q => exact absurd rfl (hn q)
    | one _ => rfl
    | two _ => rfl
  · subst eu
    obtain ⟨n2, e2⟩ := hc
    have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s fb _ e1
    have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s fc _ e2
    exact ⟨max n1 n2 + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero]; exact e2'⟩
  · subst eu
    obtain ⟨n2, e2⟩ := hc
    have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s fb _ e1
    have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s fd _ e2
    exact ⟨max n1 n2 + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero]; exact e2'⟩
  · subst eu
    rw [minkF_succ_eq]; simp only [minkStep]; rw [e1, tbind_zero]
    rcases p with ⟨_ | _ | k⟩ | ⟨x, y⟩
    · exact absurd rfl h0
    · exact absurd rfl h1
    · rfl
    · rfl

/-! ## What the parts give -/

/-- **What a branch of `%6` gives under `%done`**: every run under `%done`
from a state with the premises of `callTreeA_done` meets `RunOKGB`, and its
need has at most `k` entries. -/
abbrev SixD (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) →
    RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nex ∧ (entries nex.laz).length ≤ k

/-- **What a test of `%6` gives under `%pick z o`** (jumps without
arguments, below the state's labels). -/
abbrev PickD (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (z o : Jmp),
    z.args = [] → o.args = [] → GJ g0.bo (CGoal.pick z o : CGoal S) →
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.pick z o) region g0 = some (nex, g1) →
    RunOKGB lib N P f (CGoal.pick z o : CGoal S) g0 g1 nex ∧ (entries nex.laz).length ≤ k

/-- **A call-free test with `UOK`** whose formula is its pure value meets
`PickD` with the bound `2 * sixCount c` (`RunOKV.size`). -/
theorem pickD_of_uok (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {c : Nomm}
    (u : UOK (S := S) (Map := Map) lib c) (M : MinkEq lib P f c) (hc : sixCount c ≤ 255) :
    PickD (S := S) (Map := Map) lib N env P f c (2 * sixCount c) := by
  intro sup region g0 g1 nex z o hz ho hj b0 d0 hu hcl hcb h
  rw [runLC_eq env c (Nomm.noCall_of_pure c u.pure)] at h
  have R := u.pick z o hz ho (region := region) trivial hj hc b0 d0 hu hcl hcb h
  exact ⟨(RunOKV.toGC (goal := CGoal.pick z o) M trivial R).toB, R.size⟩

/-- **A branch of `CallTreeA` whose need has no entries** (`NoEntF`) meets
`SixD` with the bound `0`. -/
theorem sixD_of_callTreeA (lib : Lib) {N : Needs} (env : CallEnv) {b : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeA b f nm) (hn : NoEntF nm) (P : Noun → Prop) :
    SixD (S := S) (Map := Map) lib N env P f nm 0 := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  refine ⟨(callTreeA_done lib env h P b0 d0 hu hcl hcb hr).run, ?_⟩
  rw [noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.done) trivial hr]
  exact Nat.le_refl _

/-! ## The run taken apart -/

/-- **`[6 c a b]` under `%done` taken apart**, with a call-free test. -/
theorem runLC_six_done_apart (env : CallEnv) (sup : Option Nomm) {c a b : Nomm} (hcp : c.pure = true)
    {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    ∃ (x1 x0 xc : NextL S) (g1 g2 g3 : Gen Map),
      runLC env sup b CGoalL.done region g0 = some (x1, g1) ∧ runLC env sup a CGoalL.done region g1 = some (x0, g2) ∧
      x0.th.args = [] ∧ x1.th.args = [] ∧
      runLC env sup c (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region (sixGenL g2 x0.th x1.th region) =
        some (xc, g3) ∧
      (lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false →
        copyL xc (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) g3 = some (nex, g4)) := by
  simp only [runLC] at h
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
  rw [show liftO (pastFork env.cod (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] []) c) =
      (pure (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] []) : CM Map (Lazy S)) by
    rw [pastFork_pure _ _ hcp]; rfl] at h
  obtain ⟨lz, gl, hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨xc, g3, h3, h⟩ := bind_some h
  refine ⟨x1, x0, xc, g1, g2, g3, h1, h2, a0, a1, h3, fun hbig => ?_⟩
  have hcond : (!(lazyBig (softLess noSoft (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] [])))) = true := by
    rw [softLess_noSoft]; simp only [emitted_bo]; rw [hbig]; rfl
  rw [if_pos hcond] at h
  exact h

/-! ## A lazy block of the fork -/

/-- **A lazy block of the fork, forward**: the block `o` fills the branch's
sure need from the input registers (`FillSem`) and hops to the branch's
jump, so a tone of `+mink` on the branch's formula is returned there (or
the fill crashes where the branch's `nec` says `+mink` crashes). -/
theorem sixBlk_fwd {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S}
    (Rx : RunOKGB lib N P f (CGoal.done : CGoal S) gA gB x)
    {cf : Map (Nat × List Nat)} {cc : Straight Map} {ned : Need} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs}
    {O : Oracle σ} {n : Nat} {gul : Noun} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hF : OracleFwd lib Inv ν O n) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ st' : σ, AgreeUB lib O cc gul st' t cf ned gA gB x.laz s0 s)
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

/-- **A lazy block of the fork, backward.** -/
theorem sixBlk_bwd {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S}
    (Rx : RunOKGB lib N P f (CGoal.done : CGoal S) gA gB x)
    {cf : Map (Nat × List Nat)} {cc : Straight Map} {ned : Need} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs}
    {O : Oracle σ} {gul : Noun} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hB : OracleBwd lib Inv ν O) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ st' : σ, AgreeUB lib O cc gul st' t cf ned gA gB x.laz s0 s)
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

/-! ## `[6 c a b]` under `%done` -/

/-- **`[6 c a b]` under `%done` with a call-free test and branches that may
call**: from `RunOKGB` of the test under `%pick` and of the branches under
`%done`, each with a bound on its entries (`PickD`, `SixD`), whose sum for
the branches keeps the fork small (`+lazy-shut` does not fire), the whole
meets `RunOKGB` under `%done` for `[6 fc fa fb]`, with the bound of the sum.
Forward: the test's tone picks the block `yes` or `nuh`, whose ops fill the
branch's sure need from the input registers (`AgreeUB`'s `FillSem` at the
fork's labels) and hop into the branch (`sixBlk_fwd`); backward the same
with `semB` (`sixBlk_bwd`). -/
theorem six_doneGB (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fc fa fb : Noun} {c a b : Nomm}
    {kc ka kb : Nat} (hcp : c.pure = true) (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (Ha : SixD (S := S) (Map := Map) lib N env P fa a ka) (Hb : SixD (S := S) (Map := Map) lib N env P fb b kb)
    (hk : ka + kb + 3 ≤ lazyMax) :
    SixD (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (kc + ka + kb + 2) := by
  intro sup region g0 g4 nex b0 d0 hu hcl0 hcb0 h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, hx0a, hx1a, h3, hrest⟩ := runLC_six_done_apart env sup hcp h
  obtain ⟨Rb, sb⟩ := Hb b0 d0 hu hcl0 hcb0 h1
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have cl1 : Clear g1 := hcl0.growU Rb.grow
  have cb1 : CondBelow g1 := Rb.cfr.below hcb0
  obtain ⟨Ra, sa⟩ := Ha b1 d1 u1 cl1 cb1 h2
  have cl2 : Clear g2 := cl1.growU Ra.grow
  have cb2 : CondBelow g2 := Ra.cfr.below cb1
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop Ra.lo Ra.hi)
    (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).toU u2
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
  have raR : ∀ r, NMem x0.laz.sure.ned r → g1.re ≤ r ∧ r < g2.re := fun r hr => (Ra.regs r hr).resolve_left (fun e => e)
  have rbR : ∀ r, NMem x1.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re := fun r hr => (Rb.regs r hr).resolve_left (fun e => e)
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
    obtain ⟨hc3, agC, yesB, agA, nuhB, agB⟩ := core cf cc ned σ O gul t s0 s st ag
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
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwd Ra hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf2
        (by omega) hned hs yesB agA hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ha)
    · obtain ⟨-, G1, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwd Rb hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf1
        (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) hb')
    · obtain ⟨-, -, G2⟩ := Gc
      exact returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)
  · -- backward
    intro cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hc3, agC, yesB, agA, nuhB, agB⟩ := core cf cc ned σ O gul t s0 s st ag
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
        obtain ⟨r, hr, G⟩ := sixBlk_bwd Ra hN hS hB hcf2 (by omega) hned hs yesB agA hI' (frames_mono hν htr)
          (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
        exact ⟨r, MB.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
      · by_cases h1 : p = A 1
        · subst h1
          obtain ⟨-, G1, -⟩ := Gc
          obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
          obtain ⟨r, hr, G⟩ := sixBlk_bwd Rb hN hS hB hcf1 (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
            (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
          exact ⟨r, MB.2.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
        · obtain ⟨-, -, G2⟩ := Gc
          exact ⟨_, MB.2.2.2 p rfl h0 h1, returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)⟩
    | one q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
    | two q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
  · -- the bound
    rw [en]; simp only [List.length_append, List.length_cons]
    omega

/-! ## The top -/

/-- **The contract from `SixD`**: the whole-subject code of a nomm whose runs
under `%done` meet `SixD` meets both halves of the contract
(`finishLUC_contractGB`, the bound unused). -/
theorem finishLUC_contractSixD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    {k : Nat} (H : SixD (S := S) (Map := Map) lib N env P f nm k) {c : Straight Map}
    (hc : finishLUC (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractGB lib N (fun hr => (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) hc

/-- `[3 [0 2]]`, the cell test of the head, as a test: `PickD` with the bound `0`. -/
theorem pickD_three2 (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    PickD (S := S) (Map := Map) lib N env P (n2 (A 3) (slot 2)) (Nomm.n3 (Nomm.n0 2)) 0 :=
  pickD_of_uok lib env (uok_x lib (FragX.three (FragX.frag (nm := Nomm.n0 2) fun _ => trivial)))
    (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.three (CallTreeA.n0 2)).annot P) hs gul tm r)
    (by decide)

/-- **`[6 [3 [0 2]] [2 [0 6] [0 7]] [0 3]]` meets both halves of the
contract**: if the head of the subject is a cell, the indirect call of the
head's tail on the head's head, else the tail. -/
theorem six3_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n4 (A 6) (n2 (A 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3)) [s] c ∧
      ContractBwd lib N s (n4 (A 6) (n2 (A 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3)) [s] c :=
  have H := finishLUC_contractSixD (S := S) (Map := Map) lib (N := N) env (P := fun _ => True)
    (six_doneGB lib env rfl (pickD_three2 lib env _)
      (sixD_of_callTreeA lib env (CallTreeA.ind (CallTreeA.n0 6) (CallTreeA.n0 7))
        (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)) _)
      (sixD_of_callTreeA lib env (CallTreeA.n0 3) (NoEntF.pure rfl rfl) _) (by decide)) hc
  ⟨H.1, fun s => H.2 s trivial⟩

-- The whole-subject code of that nomm exists and agrees with `+mink` on
-- the 24 subjects of `CompSixLSCheck.lean`.
#guard SixCheck.sem [Nomm.n6 (Nomm.n3 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3)] ==
  (1, 1, 24, 24)

end Comp
end SkaModel
end Formalization
