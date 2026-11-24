import lemmas.Ska.CompTagU
import lemmas.Ska.CompFragUN

/-!
# `%6` under a fork-free `%next` with branches that make proxies

README Gaps 12.2 (ninth session), step 3: `sixNext_okN` with `RunOKNV`
branches (`sixNext_okNV`), as `sixP_okV` copied `sixP_ok`.  `+sect` threads
nothing, since every key the branches add to `cond` has a tag that names
their region id (`TagNV`, `sect_specV` through `sect_h0`, `sect_h1`); each
part's `sem` is taken at the later `cond` `cf` through `CondFresh.get_lt`;
the fork blocks and the join pass registers allocated by `+fork-sure` and
the goal's registers, no key of `cf` (`unproxyBlob_fix`).  Generated from the
text of `sixNext_okN` and `lazyBlkN` (`lazyBlkNV`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The tag clause of a run under a fork-free `%next`**, with the
hypotheses of `OKNV`: every key it adds to `cond` has a tag with its region
as a suffix. -/
abbrev TagNV (nm : Nomm) : Prop :=
  ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    (∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none) →
    runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    CondTag region g0.cond g1.cond

/-- **Unproxying leaves a block alone** whose registers are no key of the
`cond` it unproxies by. -/
theorem unproxyBlob_fix {cf : Map (Nat × List Nat)} {P : Nat → Prop} (hP : ∀ x, P x → HoonMap.get cf x = Option.none)
    {b : Blob} (hb : BlobIn P b) : unproxyBlob cf b = b := by
  have e : renBlob (unproxy cf) b = renBlob id b := renBlob_congr (fun x hx => unproxy_none (hP x hx)) hb
  rw [unproxyBlob, e, renBlob_id]

/-- **A lazy block of `%6` under `%next`** (`lazyBlkN` with a part that
makes proxies, its `sem` taken at a later `cond` `cf`): entering it does for the goal
`%next sur th` what its branch does, through the fork block `ob` and the
join `barg`. -/
theorem lazyBlkNV {lib : Lib} {σ : Type} {O : Oracle σ} {cc : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {sur : Sure S} {th : Jmp} (hth : th.args = []) (dsur : Distinct sur.ned)
    {g0 g9 : Gen Map} (hsur : ∀ r, NMem sur.ned r → r < g0.re) (hned : ∀ r, NMem ned r → g9.re ≤ r)
    {barg : Nat} (hbarg : HoonMap.get cc.blocks barg = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
    {o ob : Nat} {x : NextL S} {nm' : Nomm} {u : Sure S} {gA gB : Gen Map} {A : List Pole} {s0 s : Noun}
    (hcb : HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩)
    (hF : FillSem lib O cc gul st t ned g9.re x.laz.sure A s0 s)
    {cf : Map (Nat × List Nat)} (R : RunOKNV (Map := Map) lib nm' u (jmp0 ob) gA gB x)
    (hcfB : ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k)
    (agX : AgreeU lib O cc gul st t cf ned gA gB x.laz s0 s)
    (hre : gB.re ≤ g9.re) (hlo : g0.re ≤ gA.re)
    (hl : u.lok = sur.lok) (hcp : NCopy sur.ned u.ned) (hu : ∀ r, NMem u.ned r → g0.re ≤ r ∧ r < gA.re)
    (hob : HoonMap.get cc.blocks ob = some ⟨[], [], Termin.hop ⟨(flattenNeed u.ned).map some, barg⟩⟩)
    (R2 : Map (Option Noun)) (hR2 : HoldsN ned R2 s0) :
    GoalSem lib O cc gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) R2 t (jmp0 o)
      (CGoal.next sur th) (pureEval nm' s) := by
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have fitsIff : ∀ p, FitsS u p ↔ FitsS sur p := fun p => by
    simp only [FitsS, hl, hcp.fits p]
  have ujs : ∀ y, NMem u.ned y → ¬ NMem sur.ned y := fun y h1 h2 => by
    have := (hu y h1).1; have := hsur y h2; omega
  have eAB := R.ext.1
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy
    rcases R.regs y hy' with e | e
    · have := (hu y e).2; omega
    · omega
  by_cases f : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hF hR2 x.th).1 f
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    have S3 := R.sem cf hcfB cc ned σ O st t gul s0 s agX (fun r hr => Nat.le_trans hre (hned r hr)) R3 hh3 hn3
    have keep3 : ∀ r, ((r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) →
        SkaModel.read r R3 = SkaModel.read r R2 := by
      intro r hr
      refine k3 r (hr.1.elim (fun h => Or.inr (by omega)) Or.inl) (fun hx => ?_)
      rcases R.regs r hx with e | e
      · rcases hr.1 with h | h
        · have := (hu r e).1; omega
        · have := hned r h; have := (hu r e).2; omega
      · rcases hr.1 with h | h
        · omega
        · have := hned r h; omega
    cases ev : pureEval nm' s with
    | none =>
      rw [ev] at S3
      exact goalSem_none (CGoal.next sur th) ((e0.trans e3).trans S3)
    | some p =>
      rw [ev] at S3
      refine ⟨fun fp => ?_, fun fp => (e0.trans e3).trans (S3.2 fun fu => fp ((fitsIff p).mp fu))⟩
      obtain ⟨R4, hh4, k4, e4⟩ := S3.1 ((fitsIff p).mpr fp)
      obtain ⟨R5, hh5, k5, e5⟩ := goJ_fork (lib := lib) (O := O) (gul := gul) (st := st) hth hob hbarg hcp dsur
        ujs hh4 t
      refine ⟨R5, hh5, fun r hr => ?_, (e0.trans e3).trans (e4.trans e5)⟩
      rw [k5 r hr.2, k4 r ⟨hr.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hu' => ?_⟩, keep3 r hr]
      rcases hr.1 with h | h
      · have := (hu r hu').1; omega
      · have := hned r h; have := (hu r hu').2; omega
  · have crash := e0.trans ((fillSem_runK hF hR2 x.th).2 f)
    rcases R.nec s f with ev | ⟨p, ev, nf⟩
    · rw [ev]; exact goalSem_none _ crash
    · rw [ev]
      exact ⟨fun fp => absurd ((fitsIff p).mpr fp) nf, fun _ => crash⟩

/-- **`%6` under a fork-free `%next` meets `RunOKNV`**, from `RunOKV` of
its test for `%pick` and `RunOKNV` of its branches, when every key the
branches add to `cond` has a tag with their region `rid :: region` as a
suffix (`TagNV`, so `+sect` threads nothing, `sect_specV`). -/
theorem sixNext_okNV (lib : Lib) {c a b : Nomm} (hcp : c.pure = true)
    (ihc : ∀ z o : Jmp, z.args = [] → o.args = [] → OKV (Map := Map) lib (CGoal.pick z o : CGoal S) c)
    (iha : OKNV (S := S) (Map := Map) lib a) (ihb : OKNV (S := S) (Map := Map) lib b)
    (tga : TagNV (S := S) (Map := Map) a) (tgb : TagNV (S := S) (Map := Map) b)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (hcount : sixCount (Nomm.n6 c a b) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb0 : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runL (Nomm.n6 c a b) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g9)) :
    RunOKNV (Map := Map) lib (Nomm.n6 c a b) sur th g0 g9 nex := by
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨u0, u1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
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
  have Rb := ihb (sur := u1) (th := jmp0 (g0.bo + 1)) (region := gF.id :: region)
    (g0 := { gF with id := gF.id + 1 }) ⟨by simp [jmp0], by simp [jmp0]; omega⟩ rfl
    ⟨du1, fun r hr => (r01 r (Or.inr hr)).2⟩ (cp1.clean hcl) (by omega) (by simp; omega) dF uF clF cbF
    (fun r hr => nkF r (r01 r (Or.inr hr)).1) hR
  have Tb := tgb (sur := u1) (th := jmp0 (g0.bo + 1)) (region := gF.id :: region)
    (g0 := { gF with id := gF.id + 1 }) ⟨by simp [jmp0], by simp [jmp0]; omega⟩ rfl
    ⟨du1, fun r hr => (r01 r (Or.inr hr)).2⟩ (cp1.clean hcl) (by omega) (by simp; omega) dF uF clF cbF
    (fun r hr => nkF r (r01 r (Or.inr hr)).1) hR
  have clR : Clear gR := clF.growU Rb.grow
  have cbR : CondBelow gR := Rb.cfr.below cbF
  have dR : gR.drop = false := Rb.ext.2.2.1.trans dF
  have bFR : gF.bo ≤ gR.bo := Rb.ext.2.1
  have rFR : gF.re ≤ gR.re := Rb.ext.1
  have uR : UpBelow gR := Rb.grow.up uF
  -- the yes branch
  have Ra := iha (sur := u0) (th := jmp0 g0.bo) (region := gF.id :: region) (g0 := gR)
    ⟨by simp [jmp0]; omega, by simp [jmp0]; omega⟩ rfl
    ⟨du0, fun r hr => by have := (r01 r (Or.inl hr)).2; omega⟩ (cp0.clean hcl) (by omega) (by omega) dR uR clR cbR
    (fun r hr => by
      rw [Rb.cfr.get_lt (show r < ({ gF with id := gF.id + 1 } : Gen Map).re from (r01 r (Or.inl hr)).2)]
      exact nkF r (r01 r (Or.inl hr)).1) hQ
  have Ta := tga (sur := u0) (th := jmp0 g0.bo) (region := gF.id :: region) (g0 := gR)
    ⟨by simp [jmp0]; omega, by simp [jmp0]; omega⟩ rfl
    ⟨du0, fun r hr => by have := (r01 r (Or.inl hr)).2; omega⟩ (cp0.clean hcl) (by omega) (by omega) dR uR clR cbR
    (fun r hr => by
      rw [Rb.cfr.get_lt (show r < ({ gF with id := gF.id + 1 } : Gen Map).re from (r01 r (Or.inl hr)).2)]
      exact nkF r (r01 r (Or.inl hr)).1) hQ
  have dQ : gQ.drop = false := Ra.ext.2.2.1.trans dR
  have bRQ : gR.bo ≤ gQ.bo := Ra.ext.2.1
  have rRQ : gR.re ≤ gQ.re := Ra.ext.1
  -- `+sect`
  obtain ⟨rfl, rfl, a0, a1, rfl, SB⟩ := sect_specV dQ (sect_h0 Ta) (sect_h1 (cb := gF.cond) Tb) hS
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
  have Rc := ihc (jmp0 gQ.bo) (jmp0 (gQ.bo + 1)) rfl rfl (region := region)
    trivial ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩, by simp only [jmp0]; omega,
      by simp only [jmp0]; omega⟩ (by omega) (by omega) dS uS clS cbS hC
  have uC : UpBelow gC := Rc.grow.up uS
  have dC : gC.drop = false := Rc.ext.2.2.1.trans dS
  have bSC : gQ.bo + 2 ≤ gC.bo := by have := Rc.ext.2.1; omega
  have rSC : gQ.re ≤ gC.re := by have := Rc.ext.1; omega
  -- `+copy`
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ gQ.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; omega
  have hcpy := hrest hbig
  rw [copyL_six_apart xc x0.laz x1.laz gQ.bo (gQ.bo + 1) gC hap] at hcpy
  obtain ⟨⟨u, g9'⟩, hadd, e9⟩ := Option.map_eq_some_iff.mp hcpy
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
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
    have := Rc.labs e he; have := Rc.hi; simp only [jmp0] at *; omega
  have la : ∀ e ∈ entries x0.laz, gR.bo ≤ e.1 ∧ e.1 < gQ.bo := fun e he =>
    ⟨(Ra.labs e he).1, Nat.lt_trans (Ra.labs e he).2.1 Ra.hi⟩
  have lb : ∀ e ∈ entries x1.laz, gF.bo ≤ e.1 ∧ e.1 < gR.bo := fun e he =>
    ⟨(Rb.labs e he).1, Nat.lt_trans (Rb.labs e he).2.1 Rb.hi⟩
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
  have G09 : GrowU g0 g9' := GF.trans ((growU_same (g := gF) (g' := { gF with id := gF.id + 1 }) rfl rfl (fun _ => rfl)).trans (Rb.grow.trans
    (Ra.grow.trans (GQS.trans (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up uC))))))))
  refine ⟨E09, G09, cf09, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h9o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, ?_, fun s hs => ?_,
    fun r hr => by rw [hc9]; exact Rc.ncond r hr, ?_, ?_⟩
  · -- regs
    have := Rc.regs r hr; exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · exact ⟨(Rc.eregs e h).1, fun r hr => by have := (Rc.eregs e h).2 r hr; omega⟩
    · refine ⟨Ra.dist, fun r hr => ?_⟩
      rcases Ra.regs r hr with e | e
      · have := r01 r (Or.inl e); omega
      · omega
    · exact ⟨(Ra.eregs e h).1, fun r hr => by have := (Ra.eregs e h).2 r hr; omega⟩
    · refine ⟨Rb.dist, fun r hr => ?_⟩
      rcases Rb.regs r hr with e | e
      · have := r01 r (Or.inr e); omega
      · simp only at e; omega
    · exact ⟨(Rb.eregs e h).1, fun r hr => by have := (Rb.eregs e h).2 r hr; simp only at this; omega⟩
  · -- labs
    intro e he
    simp only [jmp0]
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · obtain ⟨_, _, th', hth'⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, th', (h9k _ (by omega)).trans hth'⟩
    · exact ⟨by omega, by omega, x0.th, h9y⟩
    · obtain ⟨_, _, th', hth'⟩ := Ra.labs e h
      have := la e h
      exact ⟨by omega, by omega, th', (h9Q _ this.2).trans hth'⟩
    · exact ⟨by omega, by omega, x1.th, h9n⟩
    · obtain ⟨_, _, th', hth'⟩ := Rb.labs e h
      have := lb e h
      exact ⟨by omega, by omega, th', (h9R _ this.2).trans hth'⟩
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
  · -- size
    rw [en]; simp only [List.length_append, List.length_cons, sixCount]
    have := Ra.size; have := Rb.size; have := Rc.size; omega
  · -- nec
    have fo' : ¬ FitsS xc.laz.sure s := fun f => hs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    left; rw [pureEval_n6, Rc.nec s fo']; rfl
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
  · -- sem
    intro cf hcf cc ned σ O st t gul s0 s ag hned regs hh hn
    have hcfB : ∀ (gB : Gen Map), CondFresh gB g9' → ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k :=
      fun gB cfB k hk => (hcf k (Nat.lt_of_lt_of_le hk cfB.1)).trans (cfB.get_lt hk)
    have notLab : ∀ o, g0.bo ≤ o → o < g9'.bo → (gC.bo ≤ o ∨ o < gF.bo ∨
        (gQ.bo + 2 ≤ o ∧ o < gC.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (gR.bo ≤ o ∧ o < gQ.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < gR.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = (HoonMap.get g9'.blocks o).map (unproxyBlob cf) := by
      intro o h0 h1 hc'
      refine ag.1 o h0 h1 fun hm => ?_
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
    have hxca : xc.th.args = [] := by
      rcases Rc.ent with ⟨_, _, _, e⟩ | e
      · exact e
      · simp only [GoalJ] at e; rcases e with e | e <;> rw [e] <;> rfl
    have hc3 : HoonMap.get cc.blocks gC.bo = some ⟨[], [], Termin.hop xc.th⟩ := by
      rw [notLab gC.bo (by omega) (by omega) (Or.inl (Nat.le_refl _)), h9o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hxca]
    have hcF : ∀ k, g0.bo ≤ k → k < gF.bo →
        HoonMap.get cc.blocks k = (HoonMap.get gF.blocks k).map (unproxyBlob cf) := fun k h0 h1 =>
      (notLab k h0 (by omega) (Or.inr (Or.inl h1))).trans (by rw [h9F k h1])
    have fixF : ∀ x, (g0.re ≤ x ∧ x < gF.re) → HoonMap.get cf x = Option.none := fun x hx =>
      (hcfB _ cfF9 x hx.2).trans (nkF x hx.1)
    have hob0 : HoonMap.get cc.blocks g0.bo =
        some ⟨[], [], Termin.hop ⟨(flattenNeed u0.ned).map some, g0.bo + 2⟩⟩ := by
      rw [hcF _ (Nat.le_refl _) (by omega), bk0, Option.map_some,
        unproxyBlob_fix fixF (blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => r01 x (Or.inl hx)))]
    have hob1 : HoonMap.get cc.blocks (g0.bo + 1) =
        some ⟨[], [], Termin.hop ⟨(flattenNeed u1.ned).map some, g0.bo + 2⟩⟩ := by
      rw [hcF _ (by omega) (by omega), bk1, Option.map_some,
        unproxyBlob_fix fixF (blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => r01 x (Or.inr hx)))]
    have hbarg : HoonMap.get cc.blocks (g0.bo + 2) = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩ := by
      rw [hcF _ (by omega) (by omega), bk2, Option.map_some,
        unproxyBlob_fix (P := fun x => NMem sur.ned x) (b := ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
          (fun x hx => (hcfB g0 cf09 x (hok.2 x hx)).trans (hkg x hx))
          ⟨fun x hx => (mem_flatten _ x).mp hx, RegsIn.nil _, jmpIn_jmp0 _ _⟩]
    have agC : AgreeU lib O cc gul st t cf ned gS gC xc.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, h1, hnl⟩))), h9k o (by omega)]
      · obtain ⟨A, th', hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inl he))
        exact ⟨A, th', (h9k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agA : AgreeU lib O cc gul st t cf ned gR gQ x0.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩)))), h9Q o h1]
      · obtain ⟨A, th', hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
        exact ⟨A, th', (h9Q _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agB : AgreeU lib O cc gul st t cf ned { gF with id := gF.id + 1 } gR x1.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · simp only at h0
        rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩)))), h9R o h1]
      · obtain ⟨A, th', hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
        exact ⟨A, th', (h9R _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have hsur : ∀ r, NMem sur.ned r → r < g0.re := hok.2
    have hcf3 : ∀ k, k < gC.re → HoonMap.get cf k = HoonMap.get gC.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc9])
    have Hc := Rc.sem cf hcf3 cc ned σ O st t gul s0 s agC (fun r hr => by have := hned r hr; omega) regs
      ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 gC.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kk : ∀ R2 : Map (Option Noun), (∀ r, (r < gS.re ∨ NMem ned r) → SkaModel.read r R2 = SkaModel.read r regs) →
        ∀ r, ((r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) → SkaModel.read r R2 = SkaModel.read r regs :=
      fun R2 k2 r hr => k2 r (hr.1.elim (fun h => Or.inl (by omega)) Or.inr)
    show GoalSem lib O cc gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) regs t (jmp0 gC.bo)
      (CGoal.next sur th) (pureEval (Nomm.n6 c a b) s)
    rw [pureEval_n6]
    cases ec : pureEval c s with
    | none => rw [ec] at Hc; exact goalSem_none _ (e0.trans Hc)
    | some v =>
      rw [ec] at Hc
      rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
      · obtain ⟨R2, k2, e2⟩ := Hc
        obtain ⟨A, th', hg, hcb, hFl⟩ := ag.2 _ ((memE _).mpr (Or.inr (Or.inl rfl)))
        rw [h9y] at hg; simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
        subst hg
        rw [renJmp_nil _ a0] at hcb
        exact goalSem_pre (kk R2 k2) (e0.trans e2) _ _
          (lazyBlkNV hth hok.1 hsur hned hbarg hcb hFl Ra (hcfB gQ cfQ9) agA (by omega) (by omega) l0 cp0
            (fun r hr => ⟨(r01 r (Or.inl hr)).1, by have := (r01 r (Or.inl hr)).2; omega⟩) hob0 R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · obtain ⟨R2, k2, e2⟩ := Hc
        obtain ⟨A, th', hg, hcb, hFl⟩ := ag.2 _ ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        rw [h9n] at hg; simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
        subst hg
        rw [renJmp_nil _ a1] at hcb
        exact goalSem_pre (kk R2 k2) (e0.trans e2) _ _
          (lazyBlkNV hth hok.1 hsur hned hbarg hcb hFl Rb (hcfB gR cfR9) agB (by omega) (by simp; omega) l1 cp1
            (fun r hr => ⟨(r01 r (Or.inr hr)).1, (r01 r (Or.inr hr)).2⟩) hob1 R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · exact goalSem_none _ (e0.trans Hc)
      · exact goalSem_none _ (e0.trans Hc)

end Comp
end SkaModel
end Formalization
