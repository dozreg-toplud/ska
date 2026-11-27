import lemmas.Ska.CompSixNxWrap
import lemmas.Ska.CompSixNextV
import lemmas.Ska.CompSixLSDone

/-!
# `[6 c a b]` under `%next`, phase S: the relation proved

README Gaps 12.36, step 2.  At a goal with no entry a `%6` is phase S
(`runLC_six_nextE`), whose result unwraps to `+copy` of the test's result
with the plain fork of `+sect` (`sixNextSimpleC_plain`).  Here that copy
meets `RunOKGB` under `%next sur th`, so the whole meets `RunOKLT`.  The
text is `sixNext_okNV`'s (`CompSixNextV.lean`) with the semantic clauses of
`six_doneGB` (`CompSixLSDone.lean`): the test under `%pick` of `PickD`, the
branches under `%next` of `SixN`, each lazy block of the fork filled by
`AgreeUB`'s `FillSem` and then the branch's `sem`, whose `%next` goal at the
fork block `ob` goes on through the join `barg` to `th` (`goalSemCM_forkN`).

* `goalSemCM_forkN`, `sixBlkN_fwd`, `sixBlkN_bwd`: a lazy block of the fork.
* `SixN` (a branch: `RunOKGB` under `%next` at goals with no entry, a bound
  on the entries, a flat result, the tag clause), `sixN_of_uok`,
  `TagLSP`, `EntLS`, `sixN_of_lokSE`.
* `PickF` (the test's result under `%pick` is flat), `pickF_pure`.
* `RunOKGB.toLS`, `pastFork_six_big`.
* `RunTE` (every run at a goal with no entry meets `RunOKLT`),
  `six_nextT` (the `%6` meets `RunTE`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## A lazy block of the fork -/

section Blk
variable {lib : Lib} {σ : Type} {O : Oracle σ} {cc : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}

/-- **The fork block and the join**: a `%next` goal at the fork block `ob`
(which copies `u` into the join's arguments, `goJ_fork`) is the `%next`
goal `sur th`. -/
theorem goalSemCM_forkN {sur u : Sure S} {th : Jmp} (hth : th.args = []) (dsur : Distinct sur.ned) {barg ob : Nat}
    (hbarg : HoonMap.get cc.blocks barg = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
    (hob : HoonMap.get cc.blocks ob = some ⟨[], [], Termin.hop ⟨(flattenNeed u.ned).map some, barg⟩⟩)
    (hl : u.lok = sur.lok) (hcp : NCopy sur.ned u.ned) (ujs : ∀ y, NMem u.ned y → ¬ NMem sur.ned y)
    {K K' : Nat → Prop} (hK : ∀ y, K y → K' y ∧ ¬ NMem sur.ned y) {st : σ} {regs : Map (Option Noun)}
    {t tm : Trace} {je : Jmp} :
    ∀ {r : Tone}, GoalSemCM lib O cc gul Inv ν K' st regs t tm je (CGoal.next u (jmp0 ob)) r →
      GoalSemCM lib O cc gul Inv ν K st regs t tm je (CGoal.next sur th) r
  | Tone.zero p, G => by
    have fitsIff : FitsS u p ↔ FitsS sur p := by simp only [FitsS, hl, hcp.fits p]
    refine ⟨fun fp => ?_, fun nf => G.2 (fun fu => nf (fitsIff.mp fu))⟩
    obtain ⟨st', R4, hI, hle, hh4, k4, e4⟩ := G.1 (fitsIff.mpr fp)
    obtain ⟨R5, hh5, k5, e5⟩ := goJ_fork (lib := lib) (O := O) (gul := gul) (st := st') hth hob hbarg hcp dsur
      ujs hh4 t
    exact ⟨st', R5, hI, hle, hh5, fun y hy => (k5 y (hK y hy).2).trans (k4 y (hK y hy).1), e4.trans e5⟩
  | Tone.one _, G => G
  | Tone.two _, G => G

/-- **A lazy block of the fork, forward**: the block `o` fills the
branch's sure need (`FillSem`) and hops into the branch, whose result goes
on through the fork block `ob` and the join to `th`. -/
theorem sixBlkN_fwd {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S} {u : Sure S} {ob : Nat}
    (Rx : RunOKGB lib N P f (CGoal.next u (jmp0 ob)) gA gB x) (hu : ∀ y, NMem u.ned y → y < gA.re)
    {cf : Map (Nat × List Nat)} {ned : Need} {n : Nat} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hF : OracleFwd lib Inv ν O n) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ st' : σ, AgreeUB lib O cc gul st' t cf ned gA gB x.laz s0 s)
    {sur : Sure S} {th : Jmp} (hth : th.args = []) (dsur : Distinct sur.ned) {barg : Nat}
    (hbarg : HoonMap.get cc.blocks barg = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
    (hob : HoonMap.get cc.blocks ob = some ⟨[], [], Termin.hop ⟨(flattenNeed u.ned).map some, barg⟩⟩)
    (hl : u.lok = sur.lok) (hcp : NCopy sur.ned u.ned) (ujs : ∀ y, NMem u.ned y → ¬ NMem sur.ned y)
    {K : Nat → Prop} (hK : ∀ y, K y → (NMem ned y ∨ y < lo) ∧ ¬ NMem x.laz.sure.ned y ∧
      (y < gA.re ∨ NMem ned y) ∧ ¬ NMem u.ned y ∧ ¬ NMem sur.ned y)
    {st : σ} {tm : Trace} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {R2 : Map (Option Noun)} (hR2 : HoldsN ned R2 s0) {r : Tone} (hm : minkF lib gul n tm s f = some r) :
    GoalSemCM lib O cc gul Inv ν K st R2 t tm (jmp0 o) (CGoal.next sur th) r := by
  obtain ⟨A, hcb, hFl⟩ := hblk st
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy; have := Rx.ext.1
    rcases Rx.regs y hy' with e | e
    · have := hu y e; omega
    · omega
  have fitsIff : ∀ p, FitsS u p ↔ FitsS sur p := fun p => by simp only [FitsS, hl, hcp.fits p]
  by_cases fi : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hFl hR2 x.th).1 fi
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    have G := Rx.sem cf hcf cc ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag
      (fun y hy => Nat.le_trans hlo (hned y hy)) R3 hh3 hn3
    exact goalSemCM_step (Needs.le_refl _) (fun y hy => k3 y (hK y hy).1 (hK y hy).2.1) (e0.trans e3) _ r
      (goalSemCM_forkN hth dsur hbarg hob hl hcp ujs
        (K' := fun y => (y < gA.re ∨ NMem ned y) ∧ ¬ GMem (CGoal.next u (jmp0 ob)) y)
        (fun y hy => ⟨⟨(hK y hy).2.2.1, (hK y hy).2.2.2.1⟩, (hK y hy).2.2.2.2⟩) G)
  · have crash := e0.trans ((fillSem_runK hFl hR2 x.th).2 fi)
    rcases (Rx.nec s hs fi).1 gul n tm r hm with rfl | ⟨p, rfl, hp⟩
    · exact ⟨Tone.two t, st, hI, Needs.le_refl _, crash, ToneRel.two htr⟩
    · exact ⟨fun fp => absurd ((fitsIff p).mpr fp) hp,
        fun _ => ⟨Tone.two t, st, hI, Needs.le_refl _, crash, ToneRel.two htr⟩⟩

/-- **A lazy block of the fork, backward.** -/
theorem sixBlkN_bwd {N : Needs} {P : Noun → Prop} {f : Noun} {gA gB : Gen Map} {x : NextL S} {u : Sure S} {ob : Nat}
    (Rx : RunOKGB lib N P f (CGoal.next u (jmp0 ob)) gA gB x) (hu : ∀ y, NMem u.ned y → y < gA.re)
    {cf : Map (Nat × List Nat)} {ned : Need} (hN : ∀ st, Inv st → N ≤ ν st) (hS : OracleSteps Inv ν O)
    (hB : OracleBwd lib Inv ν O) (hcf : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    {lo : Nat} (hlo : gB.re ≤ lo) (hned : ∀ y, NMem ned y → lo ≤ y) {t : Trace} {s0 s : Noun} (hs : P s)
    {o : Nat}
    (hblk : ∀ st' : σ, ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
      FillSem lib O cc gul st' t ned lo x.laz.sure A s0 s)
    (ag : ∀ st' : σ, AgreeUB lib O cc gul st' t cf ned gA gB x.laz s0 s)
    {sur : Sure S} {th : Jmp} (hth : th.args = []) (dsur : Distinct sur.ned) {barg : Nat}
    (hbarg : HoonMap.get cc.blocks barg = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
    (hob : HoonMap.get cc.blocks ob = some ⟨[], [], Termin.hop ⟨(flattenNeed u.ned).map some, barg⟩⟩)
    (hl : u.lok = sur.lok) (hcp : NCopy sur.ned u.ned) (ujs : ∀ y, NMem u.ned y → ¬ NMem sur.ned y)
    {K : Nat → Prop} (hK : ∀ y, K y → (NMem ned y ∨ y < lo) ∧ ¬ NMem x.laz.sure.ned y ∧
      (y < gA.re ∨ NMem ned y) ∧ ¬ NMem u.ned y ∧ ¬ NMem sur.ned y)
    {st : σ} {tm : Trace} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {R2 : Map (Option Noun)} (hR2 : HoldsN ned R2 s0) {res : Tone × σ}
    (hres : goJ lib O cc gul st R2 t (jmp0 o) = some res) :
    ∃ r, Mink lib gul tm s f r ∧ GoalSemCM lib O cc gul Inv ν K st R2 t tm (jmp0 o) (CGoal.next sur th) r := by
  obtain ⟨A, hcb, hFl⟩ := hblk st
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy; have := Rx.ext.1
    rcases Rx.regs y hy' with e | e
    · have := hu y e; omega
    · omega
  have fitsIff : ∀ p, FitsS u p ↔ FitsS sur p := fun p => by simp only [FitsS, hl, hcp.fits p]
  by_cases fi : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hFl hR2 x.th).1 fi
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    obtain ⟨r, hr, G⟩ := Rx.semB cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag
      (fun y hy => Nat.le_trans hlo (hned y hy)) R3 hh3 hn3 res ((e0.trans e3).symm.trans hres)
    exact ⟨r, hr, goalSemCM_step (Needs.le_refl _) (fun y hy => k3 y (hK y hy).1 (hK y hy).2.1) (e0.trans e3) _ r
      (goalSemCM_forkN hth dsur hbarg hob hl hcp ujs
        (K' := fun y => (y < gA.re ∨ NMem ned y) ∧ ¬ GMem (CGoal.next u (jmp0 ob)) y)
        (fun y hy => ⟨⟨(hK y hy).2.2.1, (hK y hy).2.2.2.1⟩, (hK y hy).2.2.2.2⟩) G)⟩
  · have crash := e0.trans ((fillSem_runK hFl hR2 x.th).2 fi)
    obtain ⟨r, hr, hb⟩ := (Rx.nec s hs fi).2 gul tm
    refine ⟨r, hr, ?_⟩
    rcases hb with rfl | ⟨p, rfl, hp⟩
    · exact ⟨Tone.two t, st, hI, Needs.le_refl _, crash, ToneRel.two htr⟩
    · exact ⟨fun fp => absurd ((fitsIff p).mpr fp) hp,
        fun _ => ⟨Tone.two t, st, hI, Needs.le_refl _, crash, ToneRel.two htr⟩⟩

end Blk

/-! ## What the parts give -/

/-- **What a branch of phase S gives**: every run under `%next sur th` (a
goal with no entry) from a state with the premises of `LOKSE.run` meets
`RunOKGB`, has at most `k` entries and a flat need, and adds to `cond` only
keys whose tags have its region as a suffix. -/
abbrev SixN (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct sur.ned →
    (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) → Clean sur.ned →
    runLC env sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    RunOKGB lib N P f (CGoal.next sur th) g0 g1 nex ∧ (entries nex.laz).length ≤ k ∧ Flat nex.laz ∧
      CondTag region g0.cond g1.cond

/-- **A call-free branch with `UOK` and no `%6`** meets `SixN` with the
bound `0` (`UOK.next`, `RunOKNV.toGC`, `UOK.tagN`). -/
theorem sixN_of_uok (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (u : UOK (S := S) (Map := Map) lib nm) (M : MinkEq lib P f nm) (h6 : sixCount nm = 0) :
    SixN (S := S) (Map := Map) lib N env P f nm 0 := by
  intro sup sur th region g0 g1 nex hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hr
  rw [runLC_eq env nm (Nomm.noCall_of_pure nm u.pure)] at hr
  have R := u.next (sur := sur) (th := th) (region := region) ⟨h1, h2⟩ hta ⟨hsd, fun r hr => (hsl r hr).1⟩ hcs
    hcount b0 d0 hu hcl hcb (fun r hr => (hsl r hr).2) hr
  have e1 : entries nex.laz = [] := by
    have := R.size; rw [h6] at this; exact List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨(RunOKNV.toGC M R).toB, by rw [e1]; simp, entries_nil_flat e1, ?_⟩
  exact u.tagN (sur := sur) (th := th) (region := region) ⟨h1, h2⟩ hta ⟨hsd, fun r hr => (hsl r hr).1⟩ hcs
    hcount b0 d0 hu hcl hcb (fun r hr => (hsl r hr).2) hr

/-- **The tag clause with the premises a branch of phase S gets** (the
goal's registers below the start, the goal's jump without arguments). -/
abbrev TagLSP (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    th.args = [] → (∀ x, NMem L.sure.ned x → x < g0.re) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → CondTag region g0.cond g1.cond

theorem TagLS.toP {env : CallEnv} {nm : Nomm} (h : TagLS (S := S) (Map := Map) env nm) :
    TagLSP (S := S) (Map := Map) env nm :=
  fun hE hc b0 d0 hu hcl hcb _ _ hr => h hE hc b0 d0 hu hcl hcb hr

/-- **A bound on the entries of the runs at goals with no entry.** -/
abbrev EntLS (env : CallEnv) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → (entries nex.laz).length ≤ k

/-- **A branch that may call**: `LOKSE`, the tag clause and a bound give
`SixN`. -/
theorem sixN_of_lokSE {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    {k : Nat} (H : LOKSE (S := S) (Map := Map) x lib N env P f nm) (T : TagLSP (S := S) (Map := Map) env nm)
    (K : EntLS (S := S) (Map := Map) env nm k) : SixN (S := S) (Map := Map) lib N env P f nm k := by
  intro sup sur th region g0 g1 nex hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hr
  have e0 : entries (ofSure sur : Lazy S) = [] := entries_ofSure sur
  obtain ⟨⟨Q, R⟩, -, hfl, -⟩ := H.run e0 hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hr
  exact ⟨R.toRunOKLB.toGB (fun r hr => (hsl r hr).1), K e0 hr, hfl,
    T e0 hcount b0 d0 hu hcl hcb hta (fun r hr => (hsl r hr).1) hr⟩

/-- **The test's result under `%pick` is flat.** -/
abbrev PickF (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {z o : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    runLC env sup nm (CGoalL.pick z o : CGoalL S) region g0 = some (nex, g1) → Flat nex.laz

/-- **A call-free test without `%6`** meets `PickF` (the text of
`noEnt_pure` at `%pick`). -/
theorem pickF_pure (env : CallEnv) {nm : Nomm} (hp : nm.pure = true) (h6 : noSix nm = true) :
    PickF (S := S) (Map := Map) env nm := by
  intro sup z o region g0 g1 nex h
  rw [show (CGoalL.pick z o : CGoalL S) = CGoal.toL (CGoal.pick z o) from rfl,
    runLC_eq env nm (Nomm.noCall_of_pure nm hp), runL_toL nm hp h6 _ region, map_apply] at h
  obtain ⟨⟨n, g'⟩, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact flat_ofSure _

/-! ## Two small pieces -/

/-- **`RunOKGB` under `%next sur th` is `RunOKLS` under `ofSure sur`**
(the text of `RunOKGC.toLC` with bodies; the goal has no entry). -/
theorem RunOKGB.toLS {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {sur : Sure S} {th : Jmp}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKGB (Map := Map) lib N P f (CGoal.next sur th) g0 g1 nex) :
    RunOKLS (Map := Map) lib N P f (ofSure sur) th noWit false g0 g1 nex := by
  have e0 : entries (ofSure sur) = [] := entries_ofSure sur
  refine ⟨⟨R.ext.1, R.ext.2.1, R.ext.2.2.1, fun o ho _ => R.ext.2.2.2 o ho, R.grow, R.cfr, R.lo, R.hi,
    R.ent, R.regs, R.dist, fun e he => ⟨(R.eregs e he).1, fun r hr => ?_⟩,
    fun e he => ⟨Or.inr ⟨(R.labs e he).1, (R.labs e he).2.1⟩, (R.labs e he).2.2⟩, R.nodup,
    fun s v d w r hq hr => ?_, R.nec, R.ncond, R.econd, fun e he => absurd he (by simp [e0]), ?_, ?_⟩,
    fun e he => absurd he (by simp [e0])⟩
  · obtain ⟨h1 | h1, h2⟩ := (R.eregs e he).2 r hr
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · simp only [noWit] at hq; subst hq; exact hr.elim
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact goalSemCM_toCMD (fun _ => ⟨A 0, rfl⟩) (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI
      htr hs hm (fun st' => ⟨(ag st').1, fun e he => (ag st').2 e he (R.labs e he).1⟩) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => ⟨(ag st').1, fun e he => (ag st').2 e he (R.labs e he).1⟩) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_toCMD (fun _ => ⟨A 0, rfl⟩) G⟩

/-- **`+past-fork` of the fork of phase S is small** when the branches'
entries are few (the wrapping adds two entries per side). -/
theorem pastFork_six_big {cod : Bell → Option Bool} {p : Nomm} {y n : Nat} {l0 l1 lw : Lazy S}
    (h : pastFork cod (mk Sure.bunt [((y, l0), (n, l1))] []) p = some lw)
    (hk : 5 + (entries l0).length + (entries l1).length ≤ lazyMax) : lazyBig lw = false := by
  apply lazyBig_entries
  unfold pastFork at h
  split at h
  · cases h
  · cases h; rw [entries_six]; simp only [List.length_append, List.length_cons]; omega
  · cases h
    simp [entries, forkEntries, bondEntries]
    omega

/-! ## Phase S -/

/-- **`[6 c a b]` at a goal with no entry meets `RunOKGB` of the unwrapped
need**, from `PickD` and `PickF` of the test and `SixN` of the branches,
whose bounds keep the fork small (`+lazy-shut` off).  The text of
`sixNext_okNV` with the semantic clauses of `six_doneGB`. -/
theorem six_nextGB (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fc fa fb : Noun} {c a b : Nomm}
    {kc ka kb : Nat} (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc) (Fc : PickF (S := S) (Map := Map) env c)
    (Ha : SixN (S := S) (Map := Map) lib N env P fa a ka) (Hb : SixN (S := S) (Map := Map) lib N env P fb b kb)
    (hk : 5 + ka + kb ≤ lazyMax)
    {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hcount : sixCount (Nomm.n6 c a b) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb0 : CondBelow g0) (hj1 : 1 ≤ th.there) (hj2 : th.there < g0.bo) (hth : th.args = [])
    (hsd : Distinct sur.ned) (hsl : ∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hcl : Clean sur.ned)
    (h : runLC env sup (Nomm.n6 c a b) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g9)) :
    ∃ nexU : NextL S, nexU.th = nex.th ∧ Unwraps nex.laz nexU.laz ∧ Tree1 nexU.laz ∧
      RunOKGB lib N P (n4 (A 6) fc fa fb) (CGoal.next sur th) g0 g9 nexU := by
  rw [runLC_six_nextE env sup c a b (entries_ofSure sur) th region] at h
  obtain ⟨u0, u1, x1, x0, xc, lz, lw, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hw, hC, hrest⟩ :=
    sixNextSimpleC_plain h
  have hj : GJ g0.bo (CGoal.next sur th : CGoal S) := ⟨hj1, hj2⟩
  have hok : GoalOK g0 (CGoal.next sur th : CGoal S) := ⟨hsd, fun r hr => (hsl r hr).1⟩
  have hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none := fun r hr => (hsl r hr).2
  have hF' : forkSure sur th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 2 } = some ((u0, u1), gF) := hF
  obtain ⟨l0, l1, cp0, cp1, du0, du1, j01, r01, reF, boF, drF, cnF, idF, bk0, bk1, bk2, keepF⟩ :=
    forkSure_spec hF' d0
  simp only [sixCount] at hcount
  have dF : gF.drop = false := drF.trans d0
  have GF : GrowU g0 gF := growU_forkSure hF' d0 hj.1 hj.2 hu
  have uF : UpBelow { gF with id := gF.id + 1 } := GF.up hu
  have GF' : GrowU g0 { gF with id := gF.id + 1 } :=
    GF.trans (growU_same (g := gF) (g' := { gF with id := gF.id + 1 }) rfl rfl (fun _ => rfl))
  have clF : Clear { gF with id := gF.id + 1 } := hcl0.growU GF'
  have cbF : CondBelow { gF with id := gF.id + 1 } := fun k hk => by
    simp only at hk ⊢; rw [cnF] at hk; have := hcb0 k hk; omega
  have nkF : ∀ r, g0.re ≤ r → HoonMap.get gF.cond r = Option.none := fun r hr => by
    rw [cnF]; exact condBelow_none hcb0 hr
  -- the no branch
  obtain ⟨Rb, sb, flb, Tb⟩ := Hb (sur := u1) (th := jmp0 (g0.bo + 1)) (region := gF.id :: region)
    (g0 := { gF with id := gF.id + 1 }) (by omega) (by simp; omega) dF uF clF cbF (by simp [jmp0])
    (by simp [jmp0]; omega) rfl du1 (fun r hr => ⟨(r01 r (Or.inr hr)).2, nkF r (r01 r (Or.inr hr)).1⟩)
    (cp1.clean hcl) hR
  have clR : Clear gR := clF.growU Rb.grow
  have cbR : CondBelow gR := Rb.cfr.below cbF
  have dR : gR.drop = false := Rb.ext.2.2.1.trans dF
  have bFR : gF.bo ≤ gR.bo := Rb.ext.2.1
  have rFR : gF.re ≤ gR.re := Rb.ext.1
  have uR : UpBelow gR := Rb.grow.up uF
  -- the yes branch
  obtain ⟨Ra, sa, fla, Ta⟩ := Ha (sur := u0) (th := jmp0 g0.bo) (region := gF.id :: region) (g0 := gR)
    (by omega) (by omega) dR uR clR cbR (by simp [jmp0]; omega) (by simp [jmp0]; omega) rfl du0
    (fun r hr => ⟨by have := (r01 r (Or.inl hr)).2; omega, by
      rw [Rb.cfr.get_lt (show r < ({ gF with id := gF.id + 1 } : Gen Map).re from (r01 r (Or.inl hr)).2)]
      exact nkF r (r01 r (Or.inl hr)).1⟩) (cp0.clean hcl) hQ
  have dQ : gQ.drop = false := Ra.ext.2.2.1.trans dR
  have bRQ : gR.bo ≤ gQ.bo := Ra.ext.2.1
  have rRQ : gR.re ≤ gQ.re := Ra.ext.1
  -- `+sect`
  obtain ⟨rfl, rfl, a0, a1, rfl, SB⟩ := sect_specS dQ Tb Ta hS
  have dS : gS.drop = false := SB.2.2.2.1.trans (by simp [dQ])
  have boS : gS.bo = gQ.bo + 2 := SB.2.1.trans (sixGenL_bo _ _ _ _)
  have reS : gS.re = gQ.re := SB.1.trans (sixGenL_re _ _ _ _)
  have cS : gS.cond = gQ.cond := SB.2.2.2.2.2.1.trans (sixGenL_cond _ _ _ _)
  have blkS := SB.2.2.2.2.2.2
  have uQ : UpBelow gQ := Ra.grow.up uR
  have GQS : GrowU gQ gS := ((grow_sixGenL (gF.id :: region) (jumpsBelow_hop Ra.lo Ra.hi)
    (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).toU uQ).trans
    (growU_same SB.2.1 SB.2.2.2.1 SB.2.2.2.2.2.2)
  have uS : UpBelow gS := GQS.up uQ
  have clS : Clear gS := (clR.growU Ra.grow).growU GQS
  have cbS : CondBelow gS := fun k hk => by
    rw [cS] at hk; rw [reS]; exact Ra.cfr.below cbR k hk
  -- the test
  obtain ⟨Rc, sc⟩ := Hc (region := region) (jmp0 gQ.bo) (jmp0 (gQ.bo + 1)) rfl rfl
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩, by simp only [jmp0]; omega,
      by simp only [jmp0]; omega⟩ (by omega) dS uS clS cbS hC
  have flc := Fc hC
  have uC : UpBelow gC := Rc.grow.up uS
  have dC : gC.drop = false := Rc.ext.2.2.1.trans dS
  have bSC : gQ.bo + 2 ≤ gC.bo := by have := Rc.ext.2.1; omega
  have rSC : gQ.re ≤ gC.re := by have := Rc.ext.1; omega
  -- `+copy`
  obtain ⟨nexU, hcpy, eth, unw⟩ := hrest (pastFork_six_big hw (by omega)) flc.1 rfl
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ gQ.bo := fun e he => by rw [flc.1] at he; cases he
  rw [copyL_six_apart xc x0.laz x1.laz gQ.bo (gQ.bo + 1) gC hap] at hcpy
  obtain ⟨⟨u, g9'⟩, hadd, e9⟩ := Option.map_eq_some_iff.mp hcpy
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  refine ⟨_, eth, unw, ⟨fun e he => ?_, flc.2⟩, ?_⟩
  · simp only [fork_mk, flc.1, List.nil_append, List.mem_singleton] at he
    subst he; exact ⟨fla, flb⟩
  obtain ⟨A9, r9, bo9, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r9 bo9
  have hc9 : g9'.cond = gC.cond := by rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond]
  have cfF : CondFresh g0 { gF with id := gF.id + 1 } := condFresh_of_eq (by simp only; omega) cnF
  have cfC9 : CondFresh gC g9' := condFresh_of_eq (by omega) hc9
  have cfS9 : CondFresh gS g9' := Rc.cfr.trans cfC9
  have cfQ9 : CondFresh gQ g9' := (condFresh_of_eq (by omega) cS).trans cfS9
  have cfR9 : CondFresh gR g9' := Ra.cfr.trans cfQ9
  have cfF9 : CondFresh { gF with id := gF.id + 1 } g9' := Rb.cfr.trans cfR9
  have cf09 : CondFresh g0 g9' := cfF.trans cfF9
  -- the states
  have EF : Ext g0 gF := ⟨reF, by omega, drF, keepF⟩
  have EF' : Ext gF { gF with id := gF.id + 1 } := ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  have EQS : Ext gQ gS := ⟨by omega, by omega, dS.trans dQ.symm, fun o ho =>
    (blkS o).trans ((ext_sixGenL gQ x0.th x1.th (gF.id :: region)).2.2.2 o ho)⟩
  have E9 : Ext gC g9' := (ext_emit gC _).trans (ext_addOps_nil hadd)
  have EQ9 : Ext gQ g9' := EQS.trans (Rc.ext.trans E9)
  have ER9 : Ext gR g9' := Ra.ext.trans EQ9
  have EF9 : Ext gF g9' := EF'.trans (Rb.ext.trans ER9)
  have E09 : Ext g0 g9' := EF.trans EF9
  have h9k : ∀ k, k ≠ gC.bo → HoonMap.get g9'.blocks k = HoonMap.get gC.blocks k := fun k hk =>
    (A9 k).trans (get_emitted_ne hk)
  have h9o : HoonMap.get g9'.blocks gC.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A9 gC.bo).trans (emitted_get gC _ dC)
  have hGC : ∀ k, k < gQ.bo + 2 → HoonMap.get gC.blocks k =
      HoonMap.get (sixGenL gQ x0.th x1.th (gF.id :: region)).blocks k := fun k hk =>
    (Rc.ext.2.2.2 k (by omega)).trans (blkS k)
  have h9y : HoonMap.get g9'.blocks gQ.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h9k _ (by omega), hGC _ (by omega)]; exact sixGenL_get_y _ _ _ dQ
  have h9n : HoonMap.get g9'.blocks (gQ.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h9k _ (by omega), hGC _ (by omega)]; exact sixGenL_get_n _ _ _ dQ
  have h9Q : ∀ k, k < gQ.bo → HoonMap.get g9'.blocks k = HoonMap.get gQ.blocks k := EQ9.2.2.2
  have h9R : ∀ k, k < gR.bo → HoonMap.get g9'.blocks k = HoonMap.get gR.blocks k := ER9.2.2.2
  have h9F : ∀ k, k < gF.bo → HoonMap.get g9'.blocks k = HoonMap.get gF.blocks k := EF9.2.2.2
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, gQ.bo + 2 ≤ e.1 ∧ e.1 < gC.bo := fun e he => by
    have := Rc.labs e he; omega
  have la : ∀ e ∈ entries x0.laz, gR.bo ≤ e.1 ∧ e.1 < gQ.bo := fun e he =>
    ⟨(Ra.labs e he).1, (Ra.labs e he).2.1⟩
  have lb : ∀ e ∈ entries x1.laz, gF.bo ≤ e.1 ∧ e.1 < gR.bo := fun e he =>
    ⟨(Rb.labs e he).1, (Rb.labs e he).2.1⟩
  have lc' := labels_bound (P := fun o => gQ.bo + 2 ≤ o ∧ o < gC.bo) lc
  have la' := labels_bound (P := fun o => gR.bo ≤ o ∧ o < gQ.bo) la
  have lb' := labels_bound (P := fun o => gF.bo ≤ o ∧ o < gR.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    gQ.bo (gQ.bo + 1) x0.laz x1.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (gQ.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (gQ.bo + 1, x1.laz) ∨
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
      (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) xc.laz.bond),
      (gQ.bo + 2 ≤ e.1 ∧ e.1 < gC.bo ∧ e ∈ entries xc.laz) ∨ e.1 = gQ.bo ∨
      (gR.bo ≤ e.1 ∧ e.1 < gQ.bo ∧ e ∈ entries x0.laz) ∨ e.1 = gQ.bo + 1 ∨
      (gF.bo ≤ e.1 ∧ e.1 < gR.bo ∧ e ∈ entries x1.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) uC
  have G09 : GrowU g0 g9' := GF.trans ((growU_same (g := gF) (g' := { gF with id := gF.id + 1 }) rfl rfl
    (fun _ => rfl)).trans (Rb.grow.trans (Ra.grow.trans (GQS.trans (Rc.grow.trans (GE.trans
    (growU_addOps hadd (GE.up uC))))))))
  have hxca : xc.th.args = [] := by
    rcases Rc.ent with ⟨_, _, _, e⟩ | e
    · exact e
    · simp only [GoalJ] at e; rcases e with e | e <;> rw [e] <;> rfl
  have ujs0 : ∀ y, NMem u0.ned y → ¬ NMem sur.ned y := fun y h1 h2 => by
    have := (r01 y (Or.inl h1)).1; have := hok.2 y h2; omega
  have ujs1 : ∀ y, NMem u1.ned y → ¬ NMem sur.ned y := fun y h1 h2 => by
    have := (r01 y (Or.inr h1)).1; have := hok.2 y h2; omega
  -- what the program gives the parts
  have core : ∀ (cf : Map (Nat × List Nat)) (cc : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ)
      (gul : Noun) (t : Trace) (s0 s : Noun) (st : σ),
      (∀ k, k < g9'.re → HoonMap.get cf k = HoonMap.get g9'.cond k) →
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g0 g9'
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) xc.laz.bond) s0 s) →
      HoonMap.get cc.blocks gC.bo = some ⟨[], [], Termin.hop xc.th⟩ ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned gS gC xc.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks gQ.bo = some ⟨[], A, Termin.hop x0.th⟩ ∧
        FillSem lib O cc gul st' t ned g9'.re x0.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned gR gQ x0.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks (gQ.bo + 1) = some ⟨[], A, Termin.hop x1.th⟩ ∧
        FillSem lib O cc gul st' t ned g9'.re x1.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned { gF with id := gF.id + 1 } gR x1.laz s0 s) ∧
      HoonMap.get cc.blocks g0.bo = some ⟨[], [], Termin.hop ⟨(flattenNeed u0.ned).map some, g0.bo + 2⟩⟩ ∧
      HoonMap.get cc.blocks (g0.bo + 1) = some ⟨[], [], Termin.hop ⟨(flattenNeed u1.ned).map some, g0.bo + 2⟩⟩ ∧
      HoonMap.get cc.blocks (g0.bo + 2) = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩ := by
    intro cf cc ned σ O gul t s0 s st hcf ag
    have hcfB : ∀ (gB : Gen Map), CondFresh gB g9' → ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k :=
      fun gB cfB k hk => (hcf k (Nat.lt_of_lt_of_le hk cfB.1)).trans (cfB.get_lt hk)
    have notLab : ∀ o, g0.bo ≤ o → o < g9'.bo → (gC.bo ≤ o ∨ o < gF.bo ∨
        (gQ.bo + 2 ≤ o ∧ o < gC.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (gR.bo ≤ o ∧ o < gQ.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < gR.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = (HoonMap.get g9'.blocks o).map (unproxyBlob cf) := by
      intro o h0 h1 hc'
      refine (ag st).1 o h0 h1 fun hm => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases labAll e he with ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩
      · rcases hc' with y | y | ⟨_, _, y⟩ | y | y
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
        · omega
      · rcases hc' with y | y | y | y | y <;> omega
      · rcases hc' with y | y | y | ⟨_, _, y⟩ | y
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
      · rcases hc' with y | y | y | y | y <;> omega
      · rcases hc' with y | y | y | y | ⟨_, y⟩
        · omega
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
    have fork : ∀ (o : Nat) (x : NextL S) (st' : σ), (o, x.laz) ∈ entries
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) xc.laz.bond) →
        HoonMap.get g9'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → x.th.args = [] →
        ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
          FillSem lib O cc gul st' t ned g9'.re x.laz.sure A s0 s := by
      intro o x st' hm hb hxa
      obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 _ hm
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨A, by rw [hcb]; simp [renJmp_nil _ hxa], hF⟩
    have hcF : ∀ k, g0.bo ≤ k → k < gF.bo →
        HoonMap.get cc.blocks k = (HoonMap.get gF.blocks k).map (unproxyBlob cf) := fun k h0 h1 =>
      (notLab k h0 (by omega) (Or.inr (Or.inl h1))).trans (by rw [h9F k h1])
    have fixF : ∀ x, (g0.re ≤ x ∧ x < gF.re) → HoonMap.get cf x = Option.none := fun x hx =>
      (hcfB _ cfF9 x hx.2).trans (nkF x hx.1)
    refine ⟨?_, fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩,
      fun st' => fork gQ.bo x0 st' ((memE _).mpr (Or.inr (Or.inl rfl))) h9y a0,
      fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩,
      fun st' => fork (gQ.bo + 1) x1 st' ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h9n a1,
      fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩, ?_, ?_, ?_⟩
    · rw [notLab gC.bo (by omega) (by omega) (Or.inl (Nat.le_refl _)), h9o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hxca]
    · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, h1, hnl⟩))), h9k o (by omega)]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inl he))
      exact ⟨A, B, th, (h9k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩)))), h9Q o h1]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
      exact ⟨A, B, th, (h9Q _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    · simp only at h0
      rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩)))), h9R o h1]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
      exact ⟨A, B, th, (h9R _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    · rw [hcF _ (Nat.le_refl _) (by omega), bk0, Option.map_some,
        unproxyBlob_fix fixF (blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => r01 x (Or.inl hx)))]
    · rw [hcF _ (by omega) (by omega), bk1, Option.map_some,
        unproxyBlob_fix fixF (blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => r01 x (Or.inr hx)))]
    · rw [hcF _ (by omega) (by omega), bk2, Option.map_some,
        unproxyBlob_fix (P := fun x => NMem sur.ned x) (b := ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
          (fun x hx => (hcfB g0 cf09 x (hok.2 x hx)).trans (hkg x hx))
          ⟨fun x hx => (mem_flatten _ x).mp hx, RegsIn.nil _, jmpIn_jmp0 _ _⟩]
  -- the keeps of the lazy blocks
  have kA : ∀ (ned : Need), (∀ y, NMem ned y → g9'.re ≤ y) → ∀ y,
      ((y < g0.re ∨ NMem ned y) ∧ ¬ GMem (CGoal.next sur th : CGoal S) y) →
      (NMem ned y ∨ y < g9'.re) ∧ ¬ NMem x0.laz.sure.ned y ∧ (y < gR.re ∨ NMem ned y) ∧ ¬ NMem u0.ned y ∧
        ¬ NMem sur.ned y := by
    intro ned hned y ⟨hy, hns⟩
    have hx0 : ∀ z, NMem x0.laz.sure.ned z → g0.re ≤ z ∧ z < gQ.re := fun z hz => by
      rcases Ra.regs z hz with e | e
      · have := r01 z (Or.inl e); omega
      · omega
    rcases hy with hy | hy
    · exact ⟨Or.inr (by omega), fun hm => by have := hx0 y hm; omega, Or.inl (by omega),
        fun hm => by have := (r01 y (Or.inl hm)).1; omega, hns⟩
    · have := hned y hy
      exact ⟨Or.inl hy, fun hm => by have := hx0 y hm; omega, Or.inr hy,
        fun hm => by have := (r01 y (Or.inl hm)).2; omega, hns⟩
  have kB : ∀ (ned : Need), (∀ y, NMem ned y → g9'.re ≤ y) → ∀ y,
      ((y < g0.re ∨ NMem ned y) ∧ ¬ GMem (CGoal.next sur th : CGoal S) y) →
      (NMem ned y ∨ y < g9'.re) ∧ ¬ NMem x1.laz.sure.ned y ∧
        (y < ({ gF with id := gF.id + 1 } : Gen Map).re ∨ NMem ned y) ∧ ¬ NMem u1.ned y ∧ ¬ NMem sur.ned y := by
    intro ned hned y ⟨hy, hns⟩
    have hx1 : ∀ z, NMem x1.laz.sure.ned z → g0.re ≤ z ∧ z < gR.re := fun z hz => by
      rcases Rb.regs z hz with e | e
      · have := r01 z (Or.inr e); omega
      · simp only at e; omega
    rcases hy with hy | hy
    · exact ⟨Or.inr (by omega), fun hm => by have := hx1 y hm; omega, Or.inl (by simp only; omega),
        fun hm => by have := (r01 y (Or.inr hm)).1; omega, hns⟩
    · have := hned y hy
      exact ⟨Or.inl hy, fun hm => by have := hx1 y hm; omega, Or.inr hy,
        fun hm => by have := (r01 y (Or.inr hm)).2; omega, hns⟩
  refine ⟨E09, G09, cf09, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h9o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, fun s hs hfs => ?_,
    fun r hr => by rw [hc9]; exact Rc.ncond r hr, ?_, ?_, ?_⟩
  · -- regs
    have := (Rc.regs r hr).resolve_left (fun e => e); exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · refine ⟨(Rc.eregs e h).1, fun r hr => ?_⟩
      have := (Rc.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e)
      exact ⟨Or.inr (by omega), by omega⟩
    · refine ⟨Ra.dist, fun r hr => ?_⟩
      rcases Ra.regs r hr with e | e
      · have := r01 r (Or.inl e); exact ⟨Or.inr (by omega), by omega⟩
      · exact ⟨Or.inr (by omega), by omega⟩
    · refine ⟨(Ra.eregs e h).1, fun r hr => ?_⟩
      obtain ⟨e1 | e1, e2⟩ := (Ra.eregs e h).2 r hr
      · have := r01 r (Or.inl e1); exact ⟨Or.inr (by omega), by omega⟩
      · exact ⟨Or.inr (by omega), by omega⟩
    · refine ⟨Rb.dist, fun r hr => ?_⟩
      rcases Rb.regs r hr with e | e
      · have := r01 r (Or.inr e); exact ⟨Or.inr (by omega), by omega⟩
      · simp only at e; exact ⟨Or.inr (by omega), by omega⟩
    · refine ⟨(Rb.eregs e h).1, fun r hr => ?_⟩
      obtain ⟨e1 | e1, e2⟩ := (Rb.eregs e h).2 r hr
      · have := r01 r (Or.inr e1); exact ⟨Or.inr (by omega), by omega⟩
      · simp only at e1 e2; exact ⟨Or.inr (by omega), by omega⟩
  · -- labs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · obtain ⟨_, _, B, th', hth'⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, B, th', (h9k _ (by omega)).trans hth'⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x0.th, h9y⟩
    · obtain ⟨_, _, B, th', hth'⟩ := Ra.labs e h
      have := la e h
      exact ⟨by omega, by omega, B, th', (h9Q _ this.2).trans hth'⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x1.th, h9n⟩
    · obtain ⟨_, _, B, th', hth'⟩ := Rb.labs e h
      have := lb e h
      exact ⟨by omega, by omega, B, th', (h9R _ this.2).trans hth'⟩
  · -- nodup
    rw [en, List.map_append, List.nodup_append, List.map_append, List.nodup_append]
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_append]
    refine ⟨Rc.nodup, ⟨⟨fun hm => by have := la' _ hm; omega, Ra.nodup⟩,
      ⟨fun hm => by have := lb' _ hm; omega, Rb.nodup⟩, fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · have hx' : gR.bo ≤ x ∧ x ≤ gQ.bo := by
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
    · rw [hc9]; exact Rc.econd e h r hr
    · have hr' : r < gQ.re := by
        rcases Ra.regs r hr with e | e
        · have := (r01 r (Or.inl e)).2; omega
        · omega
      rw [cfQ9.get_lt hr']; exact Ra.ncond r hr
    · rw [cfQ9.get_lt ((Ra.eregs e h).2 r hr).2]; exact Ra.econd e h r hr
    · have hr' : r < gR.re := by
        rcases Rb.regs r hr with e | e
        · have := (r01 r (Or.inr e)).2; omega
        · simp only at e; omega
      rw [cfR9.get_lt hr']; exact Rb.ncond r hr
    · rw [cfR9.get_lt ((Rb.eregs e h).2 r hr).2]; exact Rb.econd e h r hr
  · -- forward
    intro cf hcf cc ned σ Inv ν O n gul hN hSt hFw st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hc3, agC, yesB, agA, nuhB, agB, hob0, hob1, hbarg⟩ := core cf cc ned σ O gul t s0 s st hcf ag
    have hcf3 : ∀ k, k < gC.re → HoonMap.get cf k = HoonMap.get gC.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc9])
    have hcfQ : ∀ k, k < gQ.re → HoonMap.get cf k = HoonMap.get gQ.cond k := fun k hk =>
      (hcf k (by omega)).trans (cfQ9.get_lt hk)
    have hcfR : ∀ k, k < gR.re → HoonMap.get cf k = HoonMap.get gR.cond k := fun k hk =>
      (hcf k (by omega)).trans (cfR9.get_lt hk)
    obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
    have Gc := Rc.sem cf hcf3 cc ned σ Inv ν O n' gul hN hSt (oracleFwd_le hFw (Nat.le_of_lt hn')) st t tm s0 s rb
      hI htr hs hb agC (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 gC.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kc : ∀ (regs' : Map (Option Noun)), (∀ x, ((x < gS.re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.pick (jmp0 gQ.bo) (jmp0 (gQ.bo + 1)) : CGoal S) x) →
        SkaModel.read x regs' = SkaModel.read x regs) → ∀ x, ((x < g0.re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next sur th : CGoal S) x) → SkaModel.read x regs' = SkaModel.read x regs :=
      fun regs' k2 x hx => k2 x ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun e => e⟩
    rcases hcase with ⟨hnz, hrr⟩ | ⟨rfl, ha⟩ | ⟨rfl, hb'⟩ | ⟨p, rfl, h0, h1, rfl⟩
    · rw [hrr]
      cases rb with
      | zero q => exact absurd rfl (hnz q)
      | one q => exact returnsC_step (Needs.le_refl _) e0 Gc
      | two q => exact returnsC_step (Needs.le_refl _) e0 Gc
    · obtain ⟨G0, -, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
      exact goalSemCM_step hν (kc regs' k2) (e0.trans e2) _ r
        (sixBlkN_fwd Ra (fun y hy => by have := (r01 y (Or.inl hy)).2; omega) hN hSt
          (oracleFwd_le hFw (Nat.le_of_lt hn')) hcfQ (by omega) hned hs yesB agA hth hok.1 hbarg hob0 l0 cp0 ujs0
          (kA ned hned) hI' (frames_mono hν htr) (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn)
          ha)
    · obtain ⟨-, G1, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
      exact goalSemCM_step hν (kc regs' k2) (e0.trans e2) _ r
        (sixBlkN_fwd Rb (fun y hy => (r01 y (Or.inr hy)).2) hN hSt
          (oracleFwd_le hFw (Nat.le_of_lt hn')) hcfR (by omega) hned hs nuhB agB hth hok.1 hbarg hob1 l1 cp1 ujs1
          (kB ned hned) hI' (frames_mono hν htr) (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn)
          hb')
    · obtain ⟨-, -, G2⟩ := Gc
      exact returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)
  · -- backward
    intro cf hcf cc ned σ Inv ν O gul hN hSt hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hc3, agC, yesB, agA, nuhB, agB, hob0, hob1, hbarg⟩ := core cf cc ned σ O gul t s0 s st hcf ag
    have hcf3 : ∀ k, k < gC.re → HoonMap.get cf k = HoonMap.get gC.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc9])
    have hcfQ : ∀ k, k < gQ.re → HoonMap.get cf k = HoonMap.get gQ.cond k := fun k hk =>
      (hcf k (by omega)).trans (cfQ9.get_lt hk)
    have hcfR : ∀ k, k < gR.re → HoonMap.get cf k = HoonMap.get gR.cond k := fun k hk =>
      (hcf k (by omega)).trans (cfR9.get_lt hk)
    have e0 : goJ lib O cc gul st regs t (jmp0 gC.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kc : ∀ (regs' : Map (Option Noun)), (∀ x, ((x < gS.re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.pick (jmp0 gQ.bo) (jmp0 (gQ.bo + 1)) : CGoal S) x) →
        SkaModel.read x regs' = SkaModel.read x regs) → ∀ x, ((x < g0.re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next sur th : CGoal S) x) → SkaModel.read x regs' = SkaModel.read x regs :=
      fun regs' k2 x hx => k2 x ⟨hx.1.elim (fun h => Or.inl (by omega)) Or.inr, fun e => e⟩
    obtain ⟨rb, hmb, Gc⟩ := Rc.semB cf hcf3 cc ned σ Inv ν O gul hN hSt hB st t tm s0 s hI htr hs agC
      (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn res
      (e0.symm.trans hres)
    have MB := mink_sixC_bwd (fc := fa) (fd := fb) hmb
    cases rb with
    | zero p =>
      by_cases h0 : p = A 0
      · subst h0
        obtain ⟨G0, -, -⟩ := Gc
        obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
        obtain ⟨r, hr, G⟩ := sixBlkN_bwd Ra (fun y hy => by have := (r01 y (Or.inl hy)).2; omega) hN hSt hB hcfQ
          (by omega) hned hs yesB agA hth hok.1 hbarg hob0 l0 cp0 ujs0 (kA ned hned) hI' (frames_mono hν htr)
          (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
        exact ⟨r, MB.2.1 r rfl hr, goalSemCM_step hν (kc regs' k2) (e0.trans e2) _ r G⟩
      · by_cases h1 : p = A 1
        · subst h1
          obtain ⟨-, G1, -⟩ := Gc
          obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
          obtain ⟨r, hr, G⟩ := sixBlkN_bwd Rb (fun y hy => (r01 y (Or.inr hy)).2) hN hSt hB hcfR
            (by omega) hned hs nuhB agB hth hok.1 hbarg hob1 l1 cp1 ujs1 (kB ned hned) hI' (frames_mono hν htr)
            (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
          exact ⟨r, MB.2.2.1 r rfl hr, goalSemCM_step hν (kc regs' k2) (e0.trans e2) _ r G⟩
        · obtain ⟨-, -, G2⟩ := Gc
          exact ⟨_, MB.2.2.2 p rfl h0 h1, returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)⟩
    | one q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
    | two q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩

end Comp
end SkaModel
end Formalization
