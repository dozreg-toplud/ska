import lemmas.Ska.CompWalk
import lemmas.Ska.CompMede

/-!
# `[1 k]` for a goal whose need has entries

`+mede` emits a block that hops to the goal's jump and walks the goal's lazy
need: at its own block and at every entry it puts ops that write the
constant into the registers of the need (after `+sure-require-look`), or
crash when the constant has not the need's shape.  Those ops read no
register, so no proxy is made.  The result has no entry: every entry of the
goal is consumed, and the ops `F` at it alone fill its need (`runOKE_n1`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- What the ops of `+mede` at one block do: write `som` into the registers
of the sure need, keeping every register outside it and outside the
registers `[lo, hi)` of the walk, or crash. -/
def MedeP (som : Noun) (lo hi : Nat) (_o : Nat) (sur : Sure S) (A : List Pole) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (regs : Map (Option Noun)), Distinct sur.ned → (∀ r, NMem sur.ned r → r < lo) →
    (FitsS sur som → ∃ regs', Runs lib O c gul st t A regs regs' ∧ HoldsS sur regs' som ∧
      ∀ r, ¬ NMem sur.ned r → ¬ (lo ≤ r ∧ r < hi) → SkaModel.read r regs' = SkaModel.read r regs) ∧
    (¬ FitsS sur som → Crashes lib O c gul st t A regs)

theorem medeP_mono (som : Noun) : PMono (MedeP (S := S) (Map := Map) som) := by
  intro lo hi lo' hi' o s A h h1 h2 lib σ O c gul st t regs hd hr
  obtain ⟨F, C⟩ := h lib σ O c gul st t regs hd (fun r hm => Nat.lt_of_lt_of_le (hr r hm) h1)
  exact ⟨fun f => by
    obtain ⟨R, a, b, k⟩ := F f
    exact ⟨R, a, b, fun r hn hl => k r hn (fun ⟨x, y⟩ => hl ⟨Nat.le_trans h1 x, Nat.lt_of_lt_of_le y h2⟩)⟩, C⟩

/-- The gate of `+mede`. -/
def medeGate (som : Noun) : Nat → Sure S → CM Map Unit := fun o sur => do
  let ned ← sureRequireLook sur
  medeLoop o som ned

theorem medeGate_ok (som : Noun) : GateOK (MedeP (S := S) (Map := Map) som) (medeGate (S := S) (Map := Map) som) := by
  intro o l g g' h hd
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  obtain ⟨A, F, SP⟩ := medeLoop_spec som ned _ _ () h2 hd
  have kc := (kc_medeLoop o som ned).keep _ _ _ h2
  refine ⟨F.bo, F.drop, Nat.le_trans L.le F.le, kc, fun o' ho => F.other o' (fun e => ho (by simp [e])),
    fun e he => ?_⟩
  simp only [List.mem_singleton] at he; subst he
  refine ⟨A, fun B fin hb => F.blk B fin hb, fun lib σ O c gul st t regs hdis hlt => ?_⟩
  have dn := L.dist hdis hlt
  obtain ⟨S1, S2⟩ := SP lib σ O c gul st t regs dn
  have fit : ∀ n, Fits ned n ↔ FitsS l.sure n := fun n => (L.fits n).trans Iff.rfl
  refine ⟨fun f => ?_, fun nf => S2 fun f' => nf ((fit som).mp f')⟩
  obtain ⟨R, r1, r2, r3⟩ := S1 ((fit som).mpr f)
  refine ⟨R, r1, holdsS_of_sure L r2, fun r hn hl => r3 r fun hm => ?_⟩
  rcases L.mem r hm with h' | h'
  · exact hn h'
  · exact hl ⟨h'.1, Nat.lt_of_lt_of_le h'.2 F.le⟩

theorem medeL_eq (th : Jmp) (som : Noun) (laz : Lazy S) :
    (medeL th som laz : CM Map Nat) = (do
      let o ← emit ⟨[], [], Termin.hop th⟩
      let g ← get
      if g.drop then pure o else do
        walkLazy (medeGate som) o laz
        pure o) := rfl

/-- **`[1 k]` for a goal with entries.** -/
theorem runOKE_n1 (lib : Lib) {k : Noun} {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (h : runL (Nomm.n1 k) (CGoalL.next laz th) region g0 = some (nex, g1))
    (d0 : g0.drop = false) (hu : UpBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hd : Distinct laz.sure.ned) (hreg : ∀ r, NMem laz.sure.ned r → r < g0.re)
    (hed : ∀ e ∈ entries laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → r < g0.re)
    (hnd : ((entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩) :
    RunOKE (Map := Map) lib (Nomm.n1 k) laz th g0 g1 nex := by
  simp only [runL, medeL_eq, bind_apply, emit_apply, Option.bind_some, get_apply] at h
  simp only [emitted_drop, d0, Bool.false_eq_true, if_false] at h
  obtain ⟨⟨o', gW⟩, hX, hP⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, g3, hW, h5⟩ := bind_some hX
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5 hP
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g0.emitted ⟨[], [], Termin.hop th⟩ := ⟨_, rfl⟩
  rw [← hgE] at hW
  have dE : gE.drop = false := by simp [hgE, emitted_drop, d0]
  have bE : HoonMap.get gE.blocks g0.bo = some ⟨[], [], Termin.hop th⟩ := by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put]
  have oE : ∀ o, o ≠ g0.bo → HoonMap.get gE.blocks o = HoonMap.get g0.blocks o := fun o ho => by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put, ho]
  have nlab : g0.bo ∉ (entries laz).map Prod.fst := fun hm => by
    obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (hlab e he).1; omega
  have W := walkLazy_ok (medeP_mono k) (medeGate_ok k) g0.bo laz gE g3 hW dE
    (by simp only [List.map_cons, List.nodup_cons]; exact ⟨nlab, hnd⟩)
  have reE : gE.re = g0.re := by rw [hgE]; rfl
  have boE : gE.bo = g0.bo + 1 := by rw [hgE]; rfl
  -- the block of `+mede`
  obtain ⟨Ao, hAo, PAo⟩ := W.at_ (g0.bo, laz) List.mem_cons_self
  have bo3 : HoonMap.get g3.blocks g0.bo = some ⟨[], Ao ++ [], Termin.hop th⟩ := hAo [] _ bE
  have other3 : ∀ o, o ≠ g0.bo → o ∉ (entries laz).map Prod.fst →
      HoonMap.get g3.blocks o = HoonMap.get g0.blocks o := fun o h1' h2' =>
    (W.other o (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨h1', h2'⟩)).trans (oE o h1')
  have ent3 : ∀ e ∈ entries laz, ∃ A, (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ →
      HoonMap.get g3.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧ MedeP (Map := Map) k g0.re g3.re e.1 e.2.sure A :=
    fun e he => by
      obtain ⟨A, hA, hPA⟩ := W.at_ e (List.mem_cons_of_mem _ he)
      exact ⟨A, fun B fin hb => hA B fin (by rw [oE _ (by have := (hlab e he).1; omega)]; exact hb), reE ▸ hPA⟩
  have bo3' : g3.bo = g0.bo + 1 := W.bo.trans boE
  have hgrow : Grow g0 g3 := by
    refine ⟨by omega, W.drop.trans (dE.trans d0.symm), fun kk b hk hb => ?_, fun kk b' hb' => ?_⟩
    · by_cases hm : kk ∈ (entries laz).map Prod.fst
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        obtain ⟨B, fin, hB⟩ := (hlab e he).2
        obtain ⟨A, hA, _⟩ := ent3 e he
        rw [hB] at hb; cases hb
        exact ⟨_, hA B fin hB, rfl, rfl⟩
      · exact ⟨b, (other3 kk (by omega) hm).trans hb, rfl, rfl⟩
    · by_cases e0 : kk = g0.bo
      · subst e0; rw [bo3] at hb'; cases hb'
        refine Or.inr ⟨Nat.le_refl _, by omega, fun j hj => ?_⟩
        simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨h1, h2⟩
      · by_cases hm : kk ∈ (entries laz).map Prod.fst
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          obtain ⟨B, fin, hB⟩ := (hlab e he).2
          obtain ⟨A, hA, _⟩ := ent3 e he
          rw [hA B fin hB] at hb'; cases hb'
          exact Or.inl ⟨_, hB, rfl, rfl⟩
        · rw [other3 kk e0 hm] at hb'
          exact Or.inl ⟨b', hb', rfl, rfl⟩
  have kE : gE.cond = g0.cond := by rw [hgE]; rfl
  refine ⟨reE ▸ W.le, by omega, W.drop.trans (dE.trans d0.symm), fun o ho hn => other3 o (by omega) hn, hgrow.toU hu,
    W.cnd.trans kE, by simp [jmp0]; omega, by simp [jmp0]; omega, by simp [jmp0]; omega,
    Or.inl ⟨_, bo3, rfl, rfl⟩, fun r hr => by simp [ofSure, Sure.bunt, NMem] at hr, trivial,
    fun e he => by simp [entries_ofSure] at he, fun e he => by simp [entries_ofSure] at he,
    by simp [entries_ofSure], by simp [entries_ofSure], fun e he => ?_, fun s hs => absurd (fitsS_bunt s) hs, ?_⟩
  · obtain ⟨A, hA, hPA⟩ := ent3 e he
    refine ⟨A, hA, Or.inr ⟨by simp [entries_ofSure], ?_⟩⟩
    intro lib σ O c gul st t ned A0 s0 s v hned hev hfill R hR
    simp only [pureEval, Option.some.injEq] at hev; subst hev
    obtain ⟨R1, r1, _, k1⟩ := (hfill R hR).1 (fitsS_bunt s)
    obtain ⟨S1, S2⟩ := hPA lib σ O c gul st t R1 (hed e he).1 (hed e he).2
    refine ⟨fun f => ?_, fun nf => Crashes.append_right r1 (S2 nf)⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, Runs.append r1 r2, hh2, fun x hx hn => (k2 x hn ?_).trans (k1 x ?_ (by simp [Sure.bunt, NMem]))⟩
    · rintro ⟨a, _⟩
      rcases hx with hx | hx
      · have := hned x hx; omega
      · omega
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by have := W.le; omega)
  · intro c ned σ O st t gul s0 s ag hned regs _ _
    have hc : HoonMap.get c.blocks g0.bo = some ⟨[], Ao ++ [], Termin.hop th⟩ := by
      rw [ag.1 g0.bo (Nat.le_refl _) (by omega) (by simp [entries_ofSure]), bo3]
    show GoalSem lib O c gul st _ regs t (jmp0 g0.bo) (CGoal.next laz.sure th) (pureEval (Nomm.n1 k) s)
    simp only [pureEval, GoalSem]
    obtain ⟨S1, S2⟩ := PAo lib σ O c gul st t regs hd (fun r hr => reE ▸ hreg r hr)
    rw [goJ_jmp0 _ _ _ _ hc]
    refine ⟨fun f => ?_, fun nf => S2 nf [] _⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, hh2.1, fun r hr => k2 r hr.2 ?_, by rw [r2 [] _, execBlob_hop]⟩
    rintro ⟨a, _⟩
    rcases hr.1 with x | x
    · omega
    · have := hned r x; omega
