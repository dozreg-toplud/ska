import lemmas.Ska.RawInvCLRunLD
import lemmas.Ska.RawInvCLCallDM
import lemmas.Ska.RawInvCLTopN
import lemmas.Ska.RawInvCLKdmBlocks

/-!
# The liveness of the n-ary runs with direct calls (`runLCM env false` on `PlainD`)

README Gaps 14 (b), track D (fork `kxl`).  The run of `+run` with `mono` `|`
(`runLC`, `finishLFC`) on `PlainD`: a direct call goes through `callL`'s
branch with a bell (the drop, or the `%cal` block of `+kerf`, a `%jmp` under
`%done`).

* `KxlFL`: the frame and the labels of every run of `runLCM env false` on
  `PlainD` (proved in `RawInvCLRunLN.lean`), as a class so that the arms
  copied from `RawInvCLRunLD.lean` take it silently.
* The arms: a script copy of the liveness section of `RawInvCLRunLD.lean`
  (`env true` → `env false`, `kdl_` → `kxl_`).
* The direct call: `kxl_il_sure_after`, `kxl_il_glue` (`il_lazyReg_after`,
  `il_glue` for a sure need with several registers), `kxl_tailN` (the chain
  `q`, `+past`, `p` for "`sub-ned` at the continuation", `+copy`),
  `kxl_callBlock` (`+need-ord-alloc-regs` and the call block), `kxl_callL`.
* **`liveRunF_plainD_of`**, **`optIn_finishLFC_ofD`**,
  **`readsIn_finishLFC_ofD`**: from the frame and the labels.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The frame and the labels of every run of `runLCM env false` on
`PlainD`.** -/
class KxlFL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv) :
    Prop where
  fr : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env false sup nm)
  lb : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), HRL (Map := Map) (runLCM (S := S) env false sup nm)

/-! ## The liveness with direct calls -/

/-- **`LRL` for `runLCM env false`.** -/
abbrev kxlLRLF (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (sup : Option Nomm) (nm : Nomm) : Prop :=
  ∀ (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S),
    IL K goal g0 → LG goal g0 → runLCM env false sup nm goal region g0 = some (nex, g1) →
      JL K nex g1 ∧ LiveC K goal g0 g1 nex

theorem kxl_lrl_of_lr {env : CallEnv} [KxlFL S Map env] {sup : Option Nomm} {nm : Nomm}
    (h : LiveRun (Map := Map) IL JL (runLCM (S := S) env false sup nm)) : kxlLRLF S Map env sup nm :=
  fun K goal region g0 g1 nex hI _ hr => h K goal region g0 g1 nex hI hr

/-- **`%0`, both halves** (the run of `runLC`). -/
theorem kxl_liveRun_n0 (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) (ax : Nat) :
    LiveRun (Map := Map) IL JL (runLCM (S := S) env false sup (Nomm.n0 ax)) := by
  intro K goal region g0 g1 nex hI h
  rw [runLCM_false env (Nomm.n0 ax) sup goal region] at h
  exact liveRun_n0 env sup ax K goal region g0 g1 nex hI h

/-- **`%1`, both halves** (the run of `runLC`). -/
theorem kxl_liveRun_n1 (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) (k : Noun) :
    LiveRun (Map := Map) IL JL (runLCM (S := S) env false sup (Nomm.n1 k)) := by
  intro K goal region g0 g1 nex hI h
  rw [runLCM_false env (Nomm.n1 k) sup goal region] at h
  exact liveRun_n1 env sup k K goal region g0 g1 nex hI h

theorem kxl_cons_tail (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {hT tel : Lazy S} {thq : Jmp} {g2 g3 g4 g5 g6 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hIq : IL (fun x y => K x y ∨ lazK thq.there hT x y) (CGoalL.next tel thq) g2)
    (hIh : IL K (CGoalL.next hT thq) g2) (hap : ∀ y, LReg hT y → ¬ LReg tel y)
    (lh : LabUniq hT) (lt : LabUniq tel) (lhb : ∀ e ∈ entries hT, e.1 < g2.bo)
    (ltb : ∀ e ∈ entries tel, e.1 < g2.bo)
    (h1 : runLCM env false sup q (CGoalL.next tel thq) region g2 = some (nq, g3))
    (h2 : pastL env.cod nq p region g3 = some (nq', g4))
    (h3 : runLCM env false sup p (CGoalL.next hT nq'.th) region g4 = some (np, g5))
    (h4 : copyL np nq'.laz g5 = some (nex, g6)) :
    JL K nex g6 ∧ ∀ r, LiveK (unpM g6) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      GLiveKL (unpM g2) (fun x y => K x y ∨ lazK thq.there hT x y) (CGoalL.next tel thq) r := by
  obtain ⟨Jq, Lq⟩ := ihq _ _ region g2 g3 nq hIq ⟨lt, ltb⟩ h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := (KxlFL.fr (S := S) (Map := Map) (env := env)) q hq sup _ region g2 g3 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, KP23, -, lq1, lq2⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) q hq sup
    (CGoalL.next tel thq) region).run g2 nq g3 hIq.ats ⟨hIq.goal.1, lt, ltb⟩ h1
  obtain ⟨-, KP34, -⟩ := (ht_pastL env.cod nq p region).run g3 nq' g4 Jq.ats Jq.goal.1 h2
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g4 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hTlt : ∀ y, LReg hT y → y < g2.re := fun y hy => (hIh.greg_lt (gregL_next.mpr hy)).1
  have hrs : ∀ y, LReg second y → ¬ LReg hT y := by
    intro y hy hh
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact hap y hh (gregL_next.mp h)
    · have := hTlt y hh; omega
  have FL : FrL (CGoalL.next tel thq) g2 g4 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Is : IL (fun x y => K x y ∨ lazK s2 second x y) (CGoalL.next second (⟨[], s2⟩ : Jmp)) g4 :=
    (il_addKills Ip).monoK fun x y h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr
  have KP24 := KP23.trans KP34
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y) (CGoalL.next hT (⟨[], s2⟩ : Jmp)) g4 :=
    il_glueT hIh Is (frL_iff.mp FL) KP24
      (fun y hy hq' => hq'.elim (fun h => by have := hTlt y hy; omega) fun h => hap y hy (gregL_next.mp h))
      Ip.goal.1
  have lhb' : ∀ e ∈ entries hT, e.1 < g4.bo := fun e he => Nat.lt_of_lt_of_le (lhb e he) KP24.2.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g4 g5 np Ip' ⟨lh, lhb'⟩ h3
  have Fp := (KxlFL.fr (S := S) (Map := Map) (env := env)) p hp sup _ region g4 g5 np h3
  obtain ⟨-, KP45, -, LU1, -⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) p hp sup
    (CGoalL.next hT (⟨[], s2⟩ : Jmp)) region).run g4 np g5 Ip'.ats ⟨Ip'.goal.1, lh, lhb'⟩ h3
  have hslt : ∀ y, LReg second y → y < g4.re := fun y hy => (Ip.greg_lt (gregL_next.mpr hy)).1
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g5 :=
    il_glueT (Ip.monoK fun x y h => Or.inl h) (Jp.monoK fun x y h => Or.inl h) (frL_iff.mp Fp.1) KP45
      (fun y hy hq' => hq'.elim (fun h => by have := hslt y hy; omega) fun h => hrs y hy (gregL_next.mp h))
      (fresh_kp Ip.goal.1 KP45)
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hs : LReg second y := (gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩
    rcases Fp.2 y hg with h | h
    · exact hrs y hs (gregL_next.mp h)
    · have := hslt y hs; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g5 g6 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g4) (fun x y => (K x y ∨ lazK s2 second x y) ∨ lazK s2 hT x y) s2 r := Lp r (Lc r hl)
  have hns : ¬ NMem hT.sure.ned r := fun hm => h5.nk (Or.inr ⟨(s2, hT), List.mem_cons_self, rfl, hm⟩)
  have h5' : LiveK (unpM g4) (fun x y => (K x y ∨ lazK thq.there hT x y) ∨ lazK s2 second x y) s2 r := by
    refine h5.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hns hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  exact Lq r (Lpast r h5')

/-! ## The three goals -/

/-- **The cons under `%pick`**: a `bom` block, then the tail for `bunt`
goals; nothing is live at the `bom` block. -/
theorem kxl_liveRun_cons_pick (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {z o0 : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o0 : CGoalL S) g0)
    (h : (do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      let nex2 ← runLCM env false sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLCM env false sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o0) g0 g1 nex := by
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨nq, gc, h1, h⟩ := bind_some h
  obtain ⟨nq', gd, h2, h⟩ := bind_some h
  obtain ⟨np, ge, h3, h4⟩ := bind_some h
  have I0 : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g0.bo))
      (g0.emitted ⟨[], [], Termin.bom Option.none⟩) :=
    il_emitGoal (R := g0.re) hI (Nat.le_refl _) rfl (batc_fresh fun j hj => by simp [finJumps] at hj)
      (blobIn_nil_fin trivial) (fun r hr => by simp [blockDefs] at hr) (fun r hr => hr.elim) trivial
  have nk : ∀ x y, ¬ lazK (S := S) g0.bo (ofSure Sure.bunt) x y := fun x y hk => (lazK_ofSure.mp hk).2.elim
  have I1 : IL (fun x y => K x y ∨ lazK (jmp0 g0.bo).there (ofSure (Sure.bunt : Sure S)) x y)
      (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g0.bo)) (g0.emitted ⟨[], [], Termin.bom Option.none⟩) :=
    I0.monoK fun x y h => h.elim id fun hk => (nk x y hk).elim
  have hnb : ∀ y, ¬ LReg (ofSure (Sure.bunt : Sure S)) y := fun y hy => (lReg_ofSure.mp hy).elim
  have hent : ∀ e ∈ entries (ofSure (Sure.bunt : Sure S)), e.1 < (g0.emitted ⟨[], [], Termin.bom Option.none⟩).bo :=
    fun e he => by rw [entries_ofSure] at he; exact absurd he List.not_mem_nil
  obtain ⟨J, L⟩ := kxl_cons_tail env sup hp hq ihp ihq I1 I0 (fun y hy _ => hnb y hy) (labUniq_ofSure _)
    (labUniq_ofSure _) hent hent h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  have A := L r hl
  have hget := unpM_emitted_self (g := g0) hI.ats.1 ⟨[], [], Termin.bom Option.none⟩
  exfalso
  cases A with
  | here hb' hr _ =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨-, hy | ⟨-, hy⟩⟩ := hr
    · simp [renBlob, OpsRF] at hy
    · simp [renBlob, renFin, finRegs] at hy
  | next hb' hj _ _ _ =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    simp [renBlob, renFin, getJmps] at hj

/-- **The cons under `%next`**, from the spec of `+split`. -/
theorem kxl_liveRun_cons_next (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) (hS : SplitSpecL S Map) {K : Nat → Nat → Prop}
    {region : List Nat} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.next laz th) g0) (hL : LG (CGoalL.next laz th) g0)
    (h : (do
      let (hed, tel, o) ← splitL ⟨laz, th⟩
      let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
      let nex2 ← runLCM env false sup q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLCM env false sup p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.next laz th) g0 g1 nex := by
  obtain ⟨⟨hed, tel, o⟩, ga, hsp, h⟩ := bind_some h
  obtain ⟨nexh, gb, hph, h⟩ := bind_some h
  obtain ⟨nq, gc, h1, h⟩ := bind_some h
  obtain ⟨nq', gd, h2, h⟩ := bind_some h
  obtain ⟨np, ge, h3, h4⟩ := bind_some h
  obtain ⟨Ih, It, TA, Ls⟩ := hS K laz th g0 ga hed tel o hI hsp
  obtain ⟨LUh, LUt, Bh, Bt⟩ := lab_splitL (Q := (· < g0.bo)) hsp hL.1 hL.2
  obtain ⟨-, KP0a, -⟩ := (ht_splitL ⟨laz, th⟩).run g0 _ ga hI.ats hI.goal.1 hsp
  have Ih' : IL (fun x y => K x y ∨ lazK (jmp0 o).there tel x y) (CGoalL.next hed (jmp0 o)) ga := il_killsOf Ih It
  obtain ⟨Ih2, Lh⟩ := pastL_spec (nex := ⟨hed, jmp0 o⟩) Ih' hph
  obtain ⟨-, KPab, -⟩ := (ht_pastL env.cod ⟨hed, jmp0 o⟩ q region).run ga nexh gb Ih.ats Ih.goal.1 hph
  have Dh := frame_pastL hph
  have IhK : IL K (CGoalL.next nexh.laz nexh.th) gb := Ih2.monoK fun x y h => Or.inl h
  have hIq : IL (fun x y => K x y ∨ lazK nexh.th.there nexh.laz x y) (CGoalL.next tel nexh.th) gb :=
    il_glueT (It.monoK fun x y h => Or.inl h) (il_addKills IhK) Dh.1 KPab (fun _ _ h => h) Ih2.goal.1
  have hap : ∀ y, LReg nexh.laz y → ¬ LReg tel y := fun y hy ht => by
    obtain ⟨e, he, hm⟩ := lreg_mem o (Dh.2 y hy)
    obtain ⟨e', he', hm'⟩ := lreg_mem o ht
    exact TA e he e' he' y hm hm'
  obtain ⟨LUH, LBH⟩ := lab_pastL hph LUh (fun e he => Nat.lt_of_lt_of_le (Bh e he) KP0a.2.1)
  have ltb : ∀ e ∈ entries tel, e.1 < gb.bo := fun e he => Nat.lt_of_lt_of_le (Bt e he) (KP0a.trans KPab).2.1
  obtain ⟨J, L⟩ := kxl_cons_tail env sup hp hq ihp ihq hIq IhK hap LUH LUt LBH ltb h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  have A := L r hl
  have hnt : ¬ NMem tel.sure.ned r := fun hm => A.nk (Or.inr ⟨(nexh.th.there, tel), List.mem_cons_self, rfl, hm⟩)
  have B : LiveK (unpM gb) (fun x y => (K x y ∨ lazK o tel x y) ∨ lazK nexh.th.there nexh.laz x y)
      nexh.th.there r := by
    refine A.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hnt hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  have C := Lh r B
  exact Ls r (C.mono_r fun x hx => by
    rcases hx with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h))

/-- **The cons, every goal**, from `LRL` of its parts and the spec of
`+split`. -/
theorem kxl_liveRun_consL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) (hS : SplitSpecL S Map) :
    kxlLRLF S Map env sup (Nomm.cons p q) := by
  intro K goal region g0 g1 nex hI hL h
  simp only [runLCM] at h
  obtain ⟨goal', ga, hga, h⟩ := bind_some h
  cases goal with
  | pick z o0 =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    exact kxl_liveRun_cons_pick env sup hp hq ihp ihq hI h
  | next laz th =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    exact kxl_liveRun_cons_next env sup hp hq ihp ihq hS hI hL h
  | done =>
    obtain ⟨r, gx, hx, hga⟩ := bind_some hga
    obtain ⟨o, gy, hy, hga⟩ := bind_some hga
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    have hsn : (simpleNextL (CGoalL.done : CGoalL S) : CM Map (NextL S)) g0 =
        some (⟨ofSure (lazyReg (S := S) r), jmp0 o⟩, gy) := by
      simp only [simpleNextL, bind_apply, hx, Option.bind_some, hy, pure_apply]
      rfl
    have I1 : IL K (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 o)) gy := il_simpleNextL hI hsn
    obtain ⟨J, L⟩ := kxl_liveRun_cons_next env sup hp hq ihp ihq hS I1 (lg_ofSure _ _ _) h
    exact ⟨J, LiveC.trans (liveC_simpleNextL_done hI.ats.1 (hI.cond_ge (Nat.le_refl _)) hsn) L⟩


theorem kxl_ten_tail (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {v q : Nomm} (hv : PlainD v) (hq : PlainD q)
    (ihv : kxlLRLF S Map env sup v) (ihq : kxlLRLF S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {d rec : Lazy S} {o : Nat} {g2 g3 g4 g5 g6 g7 : Comp.Gen Map} {nR nD nD' nQ nex : NextL S}
    (Id : IL K (CGoalL.next d (jmp0 o)) g2) (Ir : IL K (CGoalL.next rec (jmp0 o)) g2)
    (hap : ∀ y, LReg d y → ¬ LReg rec y) (ld : LabUniq d ∧ ∀ e ∈ entries d, e.1 < g2.bo)
    (lr : LabUniq rec ∧ ∀ e ∈ entries rec, e.1 < g2.bo)
    (h2 : pastL env.cod ⟨rec, jmp0 o⟩ v region g2 = some (nR, g3))
    (h3 : runLCM env false sup v (CGoalL.next d nR.th) region g3 = some (nD, g4))
    (h4 : pastL env.cod nD q region g4 = some (nD', g5))
    (h5 : runLCM env false sup q (CGoalL.next nR.laz nD'.th) region g5 = some (nQ, g6))
    (h6 : copyL nQ nD'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ y, LiveK (unpM g7) (fun x z => K x z ∨ lazK nex.th.there nex.laz x z) nex.th.there y →
      LiveK (unpM g2) (fun x z => (K x z ∨ lazK o d x z) ∨ lazK o rec x z) o y := by
  -- `+past` of the recipient, with the donor's kills
  have Ir2 : IL (fun x y => K x y ∨ lazK o d x y) (CGoalL.next rec (jmp0 o)) g2 := il_addKillsOf Ir Id
  obtain ⟨IR3, LpR⟩ := pastL_spec Ir2 h2
  have DpR := frame_pastL h2
  obtain ⟨A3, KP23, -, lR1, lR2⟩ := (htl_pastL (S := S) (Map := Map) labSteps env.cod ⟨rec, jmp0 o⟩ v region).run
    g2 nR g3 Ir.ats ⟨Ir.goal.1, lr⟩ h2
  rcases nR with ⟨R, ⟨aR, sR⟩⟩
  obtain ⟨_, _, _, haR⟩ := (IR3.goal : GoalL g3 (CGoalL.next R ⟨aR, sR⟩)).1
  simp only at haR
  subst haR
  have hRrec : ∀ y, LReg R y → LReg rec y := DpR.2
  have hRlt : ∀ y, LReg R y → y < g3.re := fun y hy => (IR3.greg_lt (gregL_next.mpr hy)).1
  -- `v` for "`d` at `sR`", with the recipient's kills
  have Iv : IL (fun x y => K x y ∨ lazK sR R x y) (CGoalL.next d (⟨[], sR⟩ : Jmp)) g3 :=
    il_carry Id ((il_addKills IR3).monoK fun x y h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr) KP23
      DpR.1.1 DpR.1.2.1 (fun y _ hd => (DpR.1.2.2 y hd).elim id False.elim) IR3.goal.1
  obtain ⟨Jv, Lv⟩ := ihv _ _ region g3 g4 nD Iv ⟨ld.1, fun e he => Nat.lt_of_lt_of_le (ld.2 e he) KP23.2.1⟩ h3
  have Fv := (KxlFL.fr (S := S) (Map := Map) (env := env)) v hv sup _ region g3 g4 nD h3
  obtain ⟨A4, KP34, -, lD1, lD2⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) v hv sup
    (CGoalL.next d (⟨[], sR⟩ : Jmp)) region).run g3 nD g4 A3
    ⟨Iv.goal.1, ld.1, fun e he => Nat.lt_of_lt_of_le (ld.2 e he) KP23.2.1⟩ h3
  -- `+past` over `q`
  obtain ⟨Ip5, Lp5⟩ := pastL_spec Jv h4
  have Dp5 := frame_pastL h4
  obtain ⟨LU2, -⟩ := lab_pastL h4 lD1 lD2
  obtain ⟨-, KP45, -⟩ := (ht_pastL (S := S) (Map := Map) env.cod nD q region).run g4 nD' g5 A4 Jv.goal.1 h4
  rcases nD' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip5.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have FL35 : DF (FG g3 (CGoalL.next d (⟨[], sR⟩ : Jmp))) g3 g5 :=
    (frL_iff.mp Fv.1).trans (Dp5.1.mono fun y h => h.elim)
  have hsec : ∀ y, LReg second y → ¬ LReg R y := by
    intro y hy hR
    rcases Fv.2 y (gregL_goal.mpr (Dp5.2 y hy)) with h | h
    · exact hap y (gregL_next.mp h) (hRrec y hR)
    · have := hRlt y hR; omega
  -- `q` for "`R` at `s2`", with `second`'s kills
  have IQ : IL (fun x y => K x y ∨ lazK s2 second x y) (CGoalL.next R (⟨[], s2⟩ : Jmp)) g5 :=
    il_carry IR3 ((il_addKills Ip5).monoK fun x y h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr)
      (KP34.trans KP45) FL35.1 FL35.2.1 (fun y hy hd => by
        rcases FL35.2.2 y hd with h | h | h
        · exact h
        · have := hRlt y hy; omega
        · exact (hap y (gregL_next.mp h) (hRrec y hy)).elim) Ip5.goal.1
  have LGq : LG (CGoalL.next R (⟨[], s2⟩ : Jmp)) g5 :=
    ⟨lR1, fun e he => Nat.lt_of_lt_of_le (lR2 e he) (KP34.trans KP45).2.1⟩
  obtain ⟨Jq, Lq⟩ := ihq _ _ region g5 g6 nQ IQ LGq h5
  have Fq := (KxlFL.fr (S := S) (Map := Map) (env := env)) q hq sup _ region g5 g6 nQ h5
  obtain ⟨-, KP56, -, LU1, -⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) q hq sup
    (CGoalL.next R (⟨[], s2⟩ : Jmp)) region).run g5 nQ g6 Ip5.ats ⟨IQ.goal.1, LGq⟩ h5
  -- the copy
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glueL (Ip5.monoK fun x y h => Or.inl h) Jq (fun x y h => Or.inl h) Fq KP56 hsec
  have TA : TreesApart nQ.th.there nQ.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next nQ.laz nQ.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip5.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fq.2 y hg with h | h
    · exact hsec y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_next.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K nQ second s2 g6 g7 nex
    (Jq.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h6
  refine ⟨Inex, fun y hl => ?_⟩
  -- q's run
  have l5 : LiveK (unpM g5) (fun x z => (K x z ∨ lazK s2 second x z) ∨ lazK s2 R x z) s2 y := Lq y (Lc y hl)
  have nR0 : ¬ NMem R.sure.ned y := fun hm => l5.nk (Or.inr ⟨(s2, R), List.mem_cons_self, rfl, hm⟩)
  have l5' : LiveK (unpM g5) (fun x z => (K x z ∨ lazK sR R x z) ∨ lazK s2 second x z) s2 y := by
    refine l5.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (nR0 hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  -- `+past` over `q`, then `v`'s run
  have l3 : LiveK (unpM g3) (fun x z => (K x z ∨ lazK sR R x z) ∨ lazK sR d x z) sR y := Lv y (Lp5 y l5')
  have nd0 : ¬ NMem d.sure.ned y := fun hm => l3.nk (Or.inr ⟨(sR, d), List.mem_cons_self, rfl, hm⟩)
  have l3' : LiveK (unpM g3) (fun x z => (K x z ∨ lazK o d x z) ∨ lazK sR R x z) sR y := by
    refine l3.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (nd0 hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  exact LpR y l3'

/-! ## The arm -/

/-- **The arm `%10`** in the form `LRL`, from the spec of `+into`. -/
theorem kxl_liveRun_n10L (hInto : IntoSpecL S Map) (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {a : Nat} {v q : Nomm}
    (hv : PlainD v) (hq : PlainD q) (ihv : kxlLRLF S Map env sup v) (ihq : kxlLRLF S Map env sup q) :
    kxlLRLF S Map env sup (Nomm.n10 a v q) := by
  intro K goal region g0 g7 nex hI hG h
  simp only [runLCM] at h
  obtain ⟨next, g1, h0, h⟩ := bind_some h
  obtain ⟨⟨d, rec, o⟩, g2, h1, h⟩ := bind_some h
  obtain ⟨nR, g3, h2, h⟩ := bind_some h
  obtain ⟨nD, g4, h3, h⟩ := bind_some h
  obtain ⟨nD', g5, h4, h⟩ := bind_some h
  obtain ⟨nQ, g6, h5, h6⟩ := bind_some h
  have I1 : IL K next.goal g1 := il_simpleNextL hI h0
  have L1 : LiveC K goal g0 g1 next := by
    cases goal with
    | next laz th =>
      simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      exact liveC_refl
    | done => exact liveC_simpleNextL_done hI.ats.1 (hI.cond_ge (Nat.le_refl _)) h0
    | pick z o => exact liveC_simpleNextL_pick hI h0
  obtain ⟨A1, -, -, LG1⟩ := (htl_simpleNextL (S := S) (Map := Map) goal).run g0 next g1 hI.ats
    ⟨gfl_of_il hI, hG⟩ h0
  rcases next with ⟨L, th⟩
  obtain ⟨Id, Ir, hap, Lin⟩ := hInto K L th a g1 g2 d rec o I1 h1
  obtain ⟨-, -, -, ld, lr⟩ := (htl_intoL (S := S) (Map := Map) labSteps ⟨L, th⟩ a).run g1 _ g2 A1
    ⟨I1.goal.1, LG1⟩ h1
  obtain ⟨J, Lt⟩ := kxl_ten_tail env sup hv hq ihv ihq Id Ir hap ld lr h2 h3 h4 h5 h6
  exact ⟨J, fun y hl => L1 y (Lin y (Lt y hl))⟩

/-- The field `n10` in the form `LRL`, from the spec of `+into`. -/
theorem kxl_armsL_n10L (hInto : IntoSpecL S Map) (env : CallEnv) [KxlFL S Map env] :
    ∀ sup a v q, PlainD v → PlainD q → kxlLRLF S Map env sup v → kxlLRLF S Map env sup q →
      kxlLRLF S Map env sup (Nomm.n10 a v q) :=
  fun sup _ _ _ hv hq ihv ihq => kxl_liveRun_n10L hInto env sup hv hq ihv ihq


theorem kxl_liveRun_n4_doneL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm}
    (ih : kxlLRLF S Map env sup p) {K : Nat → Nat → Prop} {region : List Nat}
    {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.done : CGoalL S) g0)
    (h : runLCM env false sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K CGoalL.done g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  simp only [runLCM] at h
  obtain ⟨pro, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨arg, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g0.cond (g0.re + 1) = g0.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1 + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by simp [finJumps] at hj)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, show g0.re < g0.re + 1 + 1 by omega⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega)
      (fun r hr => by
        have e : r = g0.re + 1 := hr
        subst e; exact ⟨Nat.le_succ _, by omega, by simp [blockDefs, aliasDst]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => hn ?_) (fun j hj => by simp [renBlob, renFin, getJmps] at hj)
    obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
    · have e : r = g0.re + 1 := by
        simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u0, u1] using hr
      exact e
    · exact (hnd (by simpa [renBlob, renPole, renFin, finRegs, defsOf, aliasDst, u0, u1] using hr)).elim

/-- **`%4` under `%pick`, both halves.** -/
theorem kxl_liveRun_n4_pickL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm}
    (ih : kxlLRLF S Map env sup p) {K : Nat → Nat → Prop} {z o : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : runLCM env false sup (Nomm.n4 p) (CGoalL.pick z o : CGoalL S) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  simp only [runLCM] at h
  obtain ⟨pro, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨arg, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o', gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g0.cond (g0.re + 1) = g0.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1 + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hI.goal.1
        · exact hI.goal.2)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, ⟨show g0.re < g0.re + 1 + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega)
      (fun r hr => by
        have e : r = g0.re + 1 := hr
        subst e; exact ⟨Nat.le_succ _, by omega, by simp [blockDefs, aliasDst]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
      · have e : r = g0.re + 1 := by
          simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u0, u1] using hr
        exact e
      · exact (hnd (by simpa [renBlob, renPole, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao,
          defsOf, aliasDst, u0, u1, az, ao] using hr)).elim
    · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨hI.lab hbz, fun r hl _ _ => Or.inl hl⟩
      · exact ⟨hI.lab hbo, fun r hl _ _ => Or.inr hl⟩

/-- **The tail of `%4` under `%next`**: the `%inc` block into `pro`, hopping
to `there`, then the operand for its argument. -/
theorem kxl_liveRun_n4_tailL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm}
    (ih : kxlLRLF S Map env sup p) {K : Nat → Nat → Prop} {region : List Nat}
    {pro there : Nat} {g1 g2 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) g1)
    (h : (do
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 there)⟩
      runLCM env false sup p (CGoalL.next (ofSure (lazyReg (S := S) arg)) (jmp0 o)) region : CM Map (NextL S)) g1 =
        some (nex, g2)) :
    JL K nex g2 ∧ LiveC K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) g1 g2 nex := by
  have hd : g1.drop = false := hI.ats.1
  obtain ⟨arg, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨hF, -, hE⟩ := (hI.goal : GoalL g1 (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)))
  obtain ⟨bt, hbt, -, -⟩ := hF
  have hpro : pro < g1.re ∧ ¬ Defd g1.blocks pro :=
    (hE _ (List.mem_cons_self ..)).2.2 pro (show pro = pro from rfl)
  have hkey : HoonMap.get g1.cond pro = Option.none := by
    cases e : HoonMap.get g1.cond pro with
    | none => rfl
    | some v => exact ((hI.cond _ v e).2.2.1 (gregL_ofSure.mpr rfl)).elim
  have upro : unproxy g1.cond pro = pro := unproxy_none hkey
  have u1 : unproxy g1.cond g1.re = g1.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (S := S) g1.re), jmp0 g1.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal' (R := g1.re + 1) hI (by omega) rfl (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj
        subst hj; exact hI.goal.1)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, fun x hx => by simp [jmp0] at hx⟩
      (fun r hr => by
        simp [blockDefs, aliasDst] at hr
        subst hr; exact hkey)
      (fun r hr => by
        have e : r = g1.re := hr
        subst e; refine ⟨Nat.le_refl _, by omega, ?_⟩
        simp only [blockDefs, aliasDst, List.nil_append, List.filterMap_cons, List.filterMap_nil,
          List.mem_singleton]
        omega) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
      · have hne : g1.re ≠ pro := by omega
        have e : r = g1.re := by
          simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u1, upro, List.erase_cons, hne]
            using hr
        exact e
      · simp [renBlob, renFin, finRegs, jmpRegs, jmp0, renJmp] at hr
    · simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
      subst hj
      refine ⟨hI.lab hbt, fun r hl hnd _ => ?_⟩
      have hr : r ≠ pro := fun e => hnd (by
        subst e; simp [renBlob, renPole, blockDefs, aliasDst, upro])
      exact hl.mono_r fun x hk => hk.elim id fun hz => (hr ((lazK_ofSure.mp hz).2)).elim

/-- **`%4` under `%next`, both halves**, from the spec of `+collapse-lazy-atom`. -/
theorem kxl_liveRun_n4_nextL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : kxlLRLF S Map env sup p) {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.next laz th) g0)
    (h : runLCM env false sup (Nomm.n4 p) (CGoalL.next laz th) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.next laz th) g0 g1 nex := by
  simp only [runLCM] at h
  obtain ⟨a, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨pro, there⟩, gb, hb, h⟩ := bind_some h
  have T : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) gb ∧
      LiveC K (CGoalL.next laz th) g0 gb ⟨ofSure (lazyReg (S := S) pro), jmp0 there⟩ := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact hC K laz th g0 ga pro there hI ha
    | none =>
      obtain ⟨hn, hargs, rfl⟩ := collapseL_none ha
      obtain ⟨r, gc, hc, hb⟩ := bind_some hb
      rw [re_apply] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [hargs, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      exact il_live_none hI hn hargs
  obtain ⟨J, L⟩ := kxl_liveRun_n4_tailL env sup ih T.1 h
  exact ⟨J, T.2.trans L⟩

/-- **`%4` under every goal, both halves**, from the spec of
`+collapse-lazy-atom`. -/
theorem kxl_liveRun_n4L (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : kxlLRLF S Map env sup p) :
    kxlLRLF S Map env sup (Nomm.n4 p) := by
  intro K goal region g0 g1 nex hI hG h
  cases goal with
  | done => exact kxl_liveRun_n4_doneL env sup ih hI h
  | pick z o => exact kxl_liveRun_n4_pickL env sup ih hI h
  | next laz th => exact kxl_liveRun_n4_nextL env sup hC ih hI h

/-- **The `%clq` block for a `%pick` goal**, then the operand for its
register: `%3` under `%pick`, and the tail of `%3` under `%done` and
`%next`. -/
theorem kxl_liveRun_clqL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm}
    (ih : kxlLRLF S Map env sup p) {K : Nat → Nat → Prop} {z o : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runLCM env false sup p (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 oc)) region : CM Map (NextL S)) g0 =
        some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  obtain ⟨r, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o', gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (S := S) g0.re), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hI.goal.1
        · exact hI.goal.2)
      ⟨fun x hx => by simp at hx, RegsIn.nil _, ⟨show g0.re < g0.re + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩⟩
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨-, hr⟩⟩ := hr
      · simp [renBlob, OpsRF] at hr
      · exact (show r = g0.re by
          simpa [renBlob, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao, u0, az, ao] using hr)
    · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨hI.lab hbz, fun r hl _ _ => Or.inl hl⟩
      · exact ⟨hI.lab hbo, fun r hl _ _ => Or.inr hl⟩

/-- **`%3` under every goal, both halves**, from the specs of
`+collapse-lazy-atom` and `+forl`. -/
theorem kxl_liveRun_n3L (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (hF : ForlSpecL S Map) (ih : kxlLRLF S Map env sup p) :
    kxlLRLF S Map env sup (Nomm.n3 p) := by
  intro K goal region g0 g1 nex hI hG h
  cases goal with
  | pick z o =>
    simp only [runLCM] at h
    exact kxl_liveRun_clqL env sup ih hI h
  | done =>
    simp only [runLCM] at h
    obtain ⟨⟨o0, o1⟩, ga, ha, h⟩ := bind_some h
    obtain ⟨I, D⟩ := doneBlocks_spec hI ha
    obtain ⟨J, L⟩ := kxl_liveRun_clqL env sup ih I h
    exact ⟨J, fun r hl => (D r (L r hl)).elim⟩
  | next laz th =>
    simp only [runLCM] at h
    by_cases hn : noneEquivalentL laz = true
    · rw [if_pos hn] at h; exact ih K _ region g0 g1 nex hI hG h
    · rw [if_neg hn] at h
      obtain ⟨a, ga, ha, h⟩ := bind_some h
      cases a with
      | none => cases h
      | some x =>
        obtain ⟨r, there⟩ := x
        obtain ⟨I1, L1⟩ := hC K laz th g0 ga r there hI ha
        obtain ⟨⟨z, o'⟩, gb, hb, h⟩ := bind_some h
        obtain ⟨I2, L2⟩ := hF K r there ga gb z o' I1 hb
        obtain ⟨J, L⟩ := kxl_liveRun_clqL env sup ih I2 h
        exact ⟨J, fun y hl => L1 y (L2 y (L y hl))⟩

/-- **The tail of `%5`** from the goal "`rq` at `o`": `JL` of the result,
and a register live at its entry is not `rp` and is live for that goal. -/
theorem kxl_five_tailL (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {rp rq o : Nat} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3)
    (hrp : rp < g3.re) (hdp : ¬ Defd g3.blocks rp) (hkp : HoonMap.get g3.cond rp = Option.none) (hne : rp ≠ rq)
    (h1 : runLCM env false sup q (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region g3 = some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLCM env false sup p (CGoalL.next (ofSure (lazyReg (S := S) rp)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      r ≠ rp ∧ GLiveKL (unpM g3) K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) r := by
  obtain ⟨Jq, Lq⟩ := ihq K _ region g3 g4 nq hI (lg_ofSure _ _ _) h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := (KxlFL.fr (S := S) (Map := Map) (env := env)) q hq sup _ region g3 g4 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, -, -, lq1, lq2⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) q hq sup
    (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hrs : ∀ y, LReg second y → y ≠ rp := by
    intro y hy e
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact hne (e.symm.trans (gregL_ofSure.mp h))
    · omega
  have FL : FrL (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3 g5 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) g5 :=
    il_lazyReg_after (il_addKills Ip) FL hrp hdp hkp (fun hg => hne (gregL_ofSure.mp hg)) Ip.goal.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := (KxlFL.fr (S := S) (Map := Map) (env := env)) p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) p hp sup
    (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glue Ip Jp (fun x y h => Or.inl h) Fp KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact hrs y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_ofSure.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure (lazyReg (S := S) rp)) x y) s2 r := Lp r (Lc r hl)
  have hne' : r ≠ rp := fun e => h5.nk (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩))
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact ⟨hne', Lq r (Lpast r h5')⟩

/-- **The arm `%5`, both halves**, from `LR` of its parts. -/
theorem kxl_liveRun_n5L (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) : kxlLRLF S Map env sup (Nomm.n5 p q) := by
  intro K goal region g0 g1 nex hI hG h
  simp only [runLCM] at h
  obtain ⟨rp, ga, ha, h⟩ := bind_some h
  obtain ⟨erp, ar, abl, acd, abo, adr⟩ := re_state ha
  obtain ⟨rq, gb, hb, h⟩ := bind_some h
  obtain ⟨erq, br, bbl, bcd, bbo, bdr⟩ := re_state hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  obtain ⟨nq, gd, h1, h⟩ := bind_some h
  obtain ⟨nq', ge, h2, h⟩ := bind_some h
  obtain ⟨np, gf, h3, h4⟩ := bind_some h
  subst erp erq
  have Ib : IL K goal gb := il_re_up hI (by omega) (bbl.trans abl) (bcd.trans acd) (bbo.trans abo) (bdr.trans adr)
  have hU : unpM gb = unpM g0 := by simp only [unpM, bbl, abl, bcd, acd]
  have hpl : g0.re < gb.re := by omega
  have hql : ga.re < gb.re := by omega
  have hne : g0.re ≠ ga.re := by omega
  have hdp : ¬ Defd gb.blocks g0.re := by
    rw [bbl, abl]; intro hd; have := defd_lt hI.regs hd; omega
  have hdq : ¬ Defd gb.blocks ga.re := by
    rw [bbl, abl]; intro hd; have := defd_lt hI.regs hd; omega
  have hkp : HoonMap.get gb.cond g0.re = Option.none := by rw [bcd, acd]; exact hI.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gb.cond ga.re = Option.none := by rw [bcd, acd]; exact hI.cond_ge (by omega)
  have hgp : ¬ GRegL goal g0.re := fun hg => by have := (hI.greg_lt hg).1; omega
  have hgq : ¬ GRegL goal ga.re := fun hg => by have := (hI.greg_lt hg).1; omega
  have O : OPh K goal gb gc g0.re ga.re o := by
    cases goal with
    | pick z o0 => exact oph_eqq Ib hpl hql hne hdp hdq hkp hkq hc
    | done =>
      obtain ⟨⟨o0, o1⟩, gx, hx, hc'⟩ := bind_some hc
      obtain ⟨Ix, Dead⟩ := doneBlocks_spec Ib hx
      have dx := frame_doneBlocks hx
      obtain ⟨p1, p2, p3⟩ := df_keep dx hpl (by omega) hdp hkp
      obtain ⟨q1, q2, q3⟩ := df_keep dx hql (by omega) hdq hkq
      obtain ⟨O1, O2, O3⟩ := oph_eqq Ix p1 q1 hne p2 q2 p3 q3 hc'
      exact ⟨O1, fun r hr hl => (Dead r (O2 r hr hl)).elim, O3⟩
    | next laz th =>
      obtain ⟨a, gx, hx, hc'⟩ := bind_some hc
      obtain ⟨dA, rA⟩ := frame_collapseL hx
      have nlp : ¬ (gb.re ≤ g0.re ∨ LReg laz g0.re) := fun h => h.elim (fun h => by omega)
        fun h => hgp (gregL_next.mpr h)
      have nlq : ¬ (gb.re ≤ ga.re ∨ LReg laz ga.re) := fun h => h.elim (fun h => by omega)
        fun h => hgq (gregL_next.mpr h)
      obtain ⟨p1, p2, p3⟩ := df_keep dA hpl nlp hdp hkp
      obtain ⟨q1, q2, q3⟩ := df_keep dA hql nlq hdq hkq
      cases a with
      | none =>
        obtain ⟨hn, hargs, rfl⟩ := collapseL_none hx
        dsimp only at hc'
        rw [if_pos hargs] at hc'
        exact oph_equ Ib hn hargs hpl hql hdp hdq hkp hkq hc'
      | some x =>
        obtain ⟨r0, o0⟩ := x
        dsimp only at hc'
        obtain ⟨⟨z, o1⟩, gy, hy, hc''⟩ := bind_some hc'
        obtain ⟨I1, L1⟩ := collapseSpecL K laz th gb gx r0 o0 Ib hx
        obtain ⟨I2, L2⟩ := forlSpecL K r0 o0 gx gy z o1 I1 hy
        have dB := frame_forl hy
        have r0f := rA r0 o0 rfl
        have xr : gb.re ≤ gx.re := dA.1
        obtain ⟨p1', p2', p3'⟩ := df_keep dB p1 (fun h => h.elim (fun e => nlp (e ▸ r0f)) fun h => by omega)
          p2 p3
        obtain ⟨q1', q2', q3'⟩ := df_keep dB q1 (fun h => h.elim (fun e => nlq (e ▸ r0f)) fun h => by omega)
          q2 q3
        obtain ⟨O1, O2, O3⟩ := oph_eqq I2 p1' q1' hne p2' q2' p3' q3' hc''
        exact ⟨O1, fun r hr hl => L1 r (L2 r (O2 r hr hl)), O3⟩
  obtain ⟨O1, O2, O3, O4, O5⟩ := O
  obtain ⟨J, L⟩ := kxl_five_tailL env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have := O2 r hr hg
  rw [hU] at this
  exact this

/-- **The arm `%2` (the indirect call), both halves**, from `LR` of its
parts. -/
theorem kxl_liveRun_n2L (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) : kxlLRLF S Map env sup (Nomm.n2 p q Option.none) := by
  intro K goal region g0 g1 nex hI hG h
  simp only [runLCM, callLM, callL] at h
  obtain ⟨ns, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, gb, hb, h⟩ := bind_some h
  obtain ⟨rSub, gc, hc, h⟩ := bind_some h
  obtain ⟨erS, cr, cbl, ccd, cbo, cdr⟩ := re_state hc
  obtain ⟨rFol, gd, hd, h⟩ := bind_some h
  obtain ⟨erF, dr, dbl, dcd, dbo, ddr⟩ := re_state hd
  obtain ⟨o, ge, he, h⟩ := bind_some h
  obtain ⟨nq, gf, h1, h⟩ := bind_some h
  obtain ⟨nq', gg, h2, h⟩ := bind_some h
  obtain ⟨np, gh, h3, h4⟩ := bind_some h
  subst erS erF
  have Ia : IL K ns.goal ga := il_simpleNextL hI ha
  have La : LiveC K goal g0 ga ns := liveC_simpleNextL hI ha
  obtain ⟨Ib, Lb⟩ := kerfSpecL K ns ga gb out pro Ia hb
  have Id : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) gd :=
    il_re_up Ib (by omega) (dbl.trans cbl) (dcd.trans ccd) (dbo.trans cbo) (ddr.trans cdr)
  have hU : unpM gd = unpM gb := by simp only [unpM, dbl, cbl, dcd, ccd]
  have hpro : pro < gb.re := (Ib.entry_regs (o := out) _ List.mem_cons_self pro rfl).1
  have hpl : gb.re < gd.re := by omega
  have hql : gc.re < gd.re := by omega
  have hne : gb.re ≠ gc.re := by omega
  have hdp : ¬ Defd gd.blocks gb.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hdq : ¬ Defd gd.blocks gc.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hkp : HoonMap.get gd.cond gb.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gd.cond gc.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (by omega)
  obtain ⟨O1, O2, O3, O4, O5⟩ := oph_nok Id hpl hql hne (by omega) (by omega) hdp hdq hkp hkq he
  obtain ⟨J, L⟩ := kxl_five_tailL env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have h5 := O2 r hr hg
  rw [hU] at h5
  exact La r (Lb r h5)

/-- **`%7` with the label clause**: `q` for the goal, then `p` for `q`'s
result, whose `LG` comes from `labRun_plain`. -/
theorem kxl_liveRun_n7L (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hq : PlainD q)
    (ihq : kxlLRLF S Map env (some p) q) (ihp : kxlLRLF S Map env sup p) : kxlLRLF S Map env sup (Nomm.n7 p q) := by
  intro K goal region g0 g2 nex hI hG h
  simp only [runLCM] at h
  obtain ⟨nex1, g1, h1, h2⟩ := bind_some h
  obtain ⟨J1, L1⟩ := ihq K goal region g0 g1 nex1 hI hG h1
  have G1 : LG nex1.goal g1 :=
    (((KxlFL.lb (S := S) (Map := Map) (env := env)) q hq (some p) goal region).run g0 nex1 g1 hI.ats
      ⟨gfl_of_il hI, hG⟩ h1).2.2.2
  obtain ⟨J2, L2⟩ := ihp K nex1.goal region g1 g2 nex (jl_il J1) G1 h2
  exact ⟨J2, L1.trans L2⟩

/-- **The arms not closed yet, in the `LRL` form.** -/
structure kxlArmsLL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv) :
    Prop where
  cons : ∀ sup p q, PlainD p → PlainD q → kxlLRLF S Map env sup p → kxlLRLF S Map env sup q →
    kxlLRLF S Map env sup (Nomm.cons p q)
  n10 : ∀ sup a v q, PlainD v → PlainD q → kxlLRLF S Map env sup v → kxlLRLF S Map env sup q →
    kxlLRLF S Map env sup (Nomm.n10 a v q)
  dm : ∀ sup p q b key, PlainD p → PlainD q → kxlLRLF S Map env sup p → kxlLRLF S Map env sup q →
    kxlLRLF S Map env sup (Nomm.n2 p q (some (b, key)))

/-- **The run-level liveness with calls on all of `PlainD`**, with the label
clause, from the arms not closed yet. -/
theorem kxl_liveRun_plainOfL (env : CallEnv) [KxlFL S Map env] (A : kxlArmsLL S Map env) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kxlLRLF S Map env sup nm
  | Nomm.n0 ax, _, sup => kxl_lrl_of_lr (kxl_liveRun_n0 env sup ax)
  | Nomm.n1 k, _, sup => kxl_lrl_of_lr (kxl_liveRun_n1 env sup k)
  | Nomm.n3 p, h, sup => kxl_liveRun_n3L env sup collapseSpecL forlSpecL (kxl_liveRun_plainOfL env A p h sup)
  | Nomm.n4 p, h, sup => kxl_liveRun_n4L env sup collapseSpecL (kxl_liveRun_plainOfL env A p h sup)
  | Nomm.n5 p q, h, sup =>
    kxl_liveRun_n5L env sup h.1 h.2 (kxl_liveRun_plainOfL env A p h.1 sup) (kxl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.cons p q, h, sup =>
    A.cons sup p q h.1 h.2 (kxl_liveRun_plainOfL env A p h.1 sup) (kxl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    kxl_liveRun_n7L env sup h.2 (kxl_liveRun_plainOfL env A q h.2 (some p)) (kxl_liveRun_plainOfL env A p h.1 sup)
  | Nomm.n10 a v q, h, sup =>
    A.n10 sup a v q h.1 h.2 (kxl_liveRun_plainOfL env A v h.1 sup) (kxl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup =>
    kxl_liveRun_n2L env sup h.1 h.2 (kxl_liveRun_plainOfL env A p h.1 sup) (kxl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n2 p q (some (b, key)), h, sup =>
    A.dm sup p q b key h.1 h.2 (kxl_liveRun_plainOfL env A p h.1 sup) (kxl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim


/-- The cons and `%10` arms in the `kxlLRLF` form, from the specs of
`+split` and `+into`. -/
theorem kxl_armsLL_of (env : CallEnv) [KxlFL S Map env] (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) :
    (∀ sup p q, PlainD p → PlainD q → kxlLRLF S Map env sup p → kxlLRLF S Map env sup q →
      kxlLRLF S Map env sup (Nomm.cons p q)) ∧
    (∀ sup a v q, PlainD v → PlainD q → kxlLRLF S Map env sup v → kxlLRLF S Map env sup q →
      kxlLRLF S Map env sup (Nomm.n10 a v q)) :=
  ⟨fun sup _ _ hp hq ihp ihq => kxl_liveRun_consL env sup hp hq ihp ihq hS, kxl_armsL_n10L hI env⟩


/-! ## The direct call (`callL` with a bell) -/

/-- **The goal "`s` at `j`" after a run with the frame** (`il_lazyReg_after`
for a sure need with several registers). -/
theorem kxl_il_sure_after {K : Nat → Nat → Prop} {goal goal' : CGoalL S} {g0 g1 : Comp.Gen Map} {s : Sure S}
    {j : Jmp} (hI : IL K goal' g1) (hF : FrL goal g0 g1) (hds : Distinct s.ned)
    (hr : ∀ y, NMem s.ned y → y < g0.re ∧ ¬ Defd g0.blocks y ∧ HoonMap.get g0.cond y = Option.none ∧ ¬ GRegL goal y)
    (hj : Fresh g1 j) :
    IL K (CGoalL.next (ofSure s) j) g1 := by
  obtain ⟨hre, hc, hD⟩ := hF
  have hk1 : ∀ y, NMem s.ned y → HoonMap.get g1.cond y = Option.none := by
    intro y hy
    cases e : HoonMap.get g1.cond y with
    | none => rfl
    | some v =>
      rcases hc y v e with h | h
      · rw [(hr y hy).2.2.1] at h; cases h
      · have := (hr y hy).1; omega
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, hj, ?_, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    refine ⟨k1, k2, fun hg => ?_, k4, k5⟩
    have e := gregL_ofSure.mp hg
    rw [hk1 k e] at hk; cases hk
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hj
    refine ⟨⟨b, hb, hp⟩, hds, fun y hy => ?_⟩
    obtain ⟨h1, h2, -, h4⟩ := hr y hy
    refine ⟨Nat.lt_of_lt_of_le h1 hre, fun hdy => ?_⟩
    rcases hD y hdy with h | h | h
    · exact h2 h
    · omega
    · exact h4 h

/-- **The glue** (`il_glue` for a sure need with several registers). -/
theorem kxl_il_glue {K K' : Nat → Nat → Prop} {second : Lazy S} {th : Jmp} {s : Sure S} {g5 g6 : Comp.Gen Map}
    {np : NextL S} (hI : IL K (CGoalL.next second th) g5) (hJ : IL K' np.goal g6) (hK : ∀ x y, K x y → K' x y)
    (hF : FrX (CGoalL.next (ofSure s) th) g5 g6 np) (hKP : KP g5 g6)
    (hrs : ∀ y, LReg second y → ¬ NMem s.ned y) : IL K (CGoalL.next second th) g6 := by
  obtain ⟨hD, -⟩ := hF
  obtain ⟨hre, hc, hdf⟩ := frL_iff.mp hD
  obtain ⟨hfr, hna, hent⟩ := (hI.goal : GoalL g5 (CGoalL.next second th))
  refine ⟨hJ.ats, hJ.regs, fun k v hk => ?_, ⟨fun k r hk h => hJ.kvan.van k r hk (hK _ _ h)⟩,
    fresh_kp hfr hKP, hna, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hJ.cond k v hk
    refine ⟨k1, k2, fun hg => ?_, k4, k5⟩
    rcases hc k v hk with h | h
    · exact (hI.cond k v h).2.2.1 hg
    · have := (hI.greg_lt hg).1; omega
  · obtain ⟨⟨b, hb, hp⟩, hds, hr⟩ := hent e he
    obtain ⟨b', hb', hp', -⟩ := hKP.2.2 _ b hb
    refine ⟨⟨b', hb', hp'.trans hp⟩, hds, fun r hm => ⟨Nat.lt_of_lt_of_le (hr r hm).1 hre, fun hd => ?_⟩⟩
    rcases hdf r hd with h | h | h
    · exact (hr r hm).2 h
    · have := (hr r hm).1; omega
    · exact hrs r (gregL_next.mp ⟨e, he, hm⟩) (gregL_ofSure.mp h)

/-- **The first run of the chain** from the goal "nothing at `j`". -/
theorem kxl_lrl_fol (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {q : Nomm} (ihq : kxlLRLF S Map env sup q)
    {K : Nat → Nat → Prop} {j : Jmp} {region : List Nat} {g3 g4 : Comp.Gen Map} {nq : NextL S}
    (hI : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3)
    (h : kdlFol q (runLCM (S := S) (Map := Map) env false sup q) (CGoalL.next (ofSure Sure.bunt) j) region g3 =
      some (nq, g4)) :
    JL K nq g4 ∧ LiveC K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3 g4 nq := by
  simp only [kdlFol] at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, liveC_refl⟩
  · exact ihq K _ region g3 g4 nq hI (lg_ofSure _ _ _) h

/-- **The chain of the drop path**: `kdlFol` from "nothing at `j`",
`+past`, `p` for "nothing at the continuation", `+copy`. -/
theorem kxl_tailB (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {j : Jmp} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3)
    (h1 : kdlFol q (runLCM (S := S) (Map := Map) env false sup q) (CGoalL.next (ofSure Sure.bunt) j) region g3 =
      some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLCM env false sup p (CGoalL.next (ofSure (Sure.bunt : Sure S)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      GLiveKL (unpM g3) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) r := by
  obtain ⟨Jq, Lq⟩ := kxl_lrl_fol env sup ihq hI h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (kdl_hrl_fol q ((KxlFL.lb (S := S) (Map := Map) (env := env)) q hq sup)
    (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hsl : ∀ y, LReg second y → y < g5.re := by
    intro y hy
    rcases hy with hy | ⟨e, he, hy⟩
    · exact (((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 _ List.mem_cons_self).2.2 y hy).1
    · exact (((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e
        (List.mem_cons_of_mem _ he)).2.2 y hy).1
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure (Sure.bunt : Sure S)) (⟨[], s2⟩ : Jmp)) g5 := kdm_il_bunt (il_addKills Ip)
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := (KxlFL.fr (S := S) (Map := Map) (env := env)) p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) p hp sup
    (CGoalL.next (ofSure (Sure.bunt : Sure S)) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have hrs : ∀ y, LReg second y → y ≠ g5.re := fun y hy e => by have := hsl y hy; omega
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glue (rp := g5.re) Ip Jp (fun x y h => Or.inl h) (kdm_frX_bunt Fp) KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact lReg_bunt (gregL_next.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure (Sure.bunt : Sure S)) x y) s2 r := Lp r (Lc r hl)
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact Lq r (Lpast r h5')

/-- **The chain of the `monoBlocks` path**: `kdlFol` from "nothing at `j`",
`+past`, `p` for "`rp` at the continuation", `+copy`. -/
theorem kxl_tailN (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {s : Sure S} {j : Jmp} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3)
    (hds : Distinct s.ned)
    (hrp : ∀ y, NMem s.ned y → y < g3.re ∧ ¬ Defd g3.blocks y ∧ HoonMap.get g3.cond y = Option.none)
    (h1 : kdlFol q (runLCM (S := S) (Map := Map) env false sup q) (CGoalL.next (ofSure Sure.bunt) j) region g3 =
      some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLCM env false sup p (CGoalL.next (ofSure s) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      ¬ NMem s.ned r ∧ GLiveKL (unpM g3) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) r := by
  obtain ⟨Jq, Lq⟩ := kxl_lrl_fol env sup ihq hI h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := kdl_frame_fol q ((KxlFL.fr (S := S) (Map := Map) (env := env)) q hq sup) _ region g3 g4 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (kdl_hrl_fol q ((KxlFL.lb (S := S) (Map := Map) (env := env)) q hq sup)
    (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hrs : ∀ y, LReg second y → ¬ NMem s.ned y := by
    intro y hy e
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact lReg_bunt (gregL_next.mp h)
    · have := (hrp y e).1; omega
  have FL : FrL (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g3 g5 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure s) (⟨[], s2⟩ : Jmp)) g5 :=
    kxl_il_sure_after (il_addKills Ip) FL hds
      (fun y hy => ⟨(hrp y hy).1, (hrp y hy).2.1, (hrp y hy).2.2, fun hg => lReg_bunt (gregL_next.mp hg)⟩) Ip.goal.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := (KxlFL.fr (S := S) (Map := Map) (env := env)) p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := ((KxlFL.lb (S := S) (Map := Map) (env := env)) p hp sup
    (CGoalL.next (ofSure s) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    kxl_il_glue Ip Jp (fun x y h => Or.inl h) Fp KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact hrs y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_ofSure.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure s) x y) s2 r := Lp r (Lc r hl)
  have hne' : ¬ NMem s.ned r := fun e => h5.nk (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩))
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact ⟨hne', Lq r (Lpast r h5')⟩


/-! ## The call block -/

/-- **The `%cal` block after `+kerf`** (`%next`, `%pick`): the goal
"nothing at the block" holds `IL`; a register live there that is no register
of the callee's need is one the goal may leave live; the need's registers
stay below `re`, undefined and no key. -/
theorem kxl_cb_kerf {K : Nat → Nat → Prop} {goal : CGoalL S} {b : Bell} {subNed : Need} {g1 g2 : Comp.Gen Map}
    {cb : Nat} (hI : IL K goal g1)
    (hN : ∀ y, NMem subNed y → y < g1.re ∧ ¬ Defd g1.blocks y ∧ HoonMap.get g1.cond y = Option.none ∧ ¬ GRegL goal y)
    (h : (do
        let nex ← simpleNextL goal
        let (out, pro) ← kerf nex
        emit ⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : CM Map Nat) g1 = some (cb, g2)) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 cb)) g2 ∧
    (∀ r, ¬ NMem subNed r → GLiveKL (unpM g2) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 cb)) r →
      GLiveKL (unpM g1) K goal r) ∧
    ∀ y, NMem subNed y → y < g2.re ∧ ¬ Defd g2.blocks y ∧ HoonMap.get g2.cond y = Option.none := by
  obtain ⟨nex, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, gb, hb, he⟩ := bind_some h
  have Ia : IL K nex.goal ga := il_simpleNextL hI ha
  have La : LiveC K goal g1 ga nex := liveC_simpleNextL hI ha
  obtain ⟨Ib, Lb⟩ := kerfSpecL K nex ga gb out pro Ia hb
  have Fa := frame_simpleNextL ha
  have Fb := frame_kerf hb
  have hd : gb.drop = false := Ib.ats.1
  obtain ⟨hF, -, -⟩ := (Ib.goal : GoalL gb (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)))
  obtain ⟨bt, hbt, -, -⟩ := hF
  obtain ⟨hpl, hkpro⟩ := Ib.entry_regs (o := out) _ List.mem_cons_self pro rfl
  have hNb : ∀ y, NMem subNed y →
      y < gb.re ∧ ¬ Defd gb.blocks y ∧ HoonMap.get gb.cond y = Option.none ∧ y ≠ pro := by
    intro y hy
    obtain ⟨n1, n2, n3, n4⟩ := hN y hy
    obtain ⟨a1, a2, a3⟩ := df_keep Fa.1 n1 (fun h => h) n2 n3
    have hlr : ¬ (ga.re ≤ y ∨ LReg nex.laz y) := by
      rintro (h | h)
      · omega
      · rcases Fa.2 y (gregL_goal.mpr h) with h' | h'
        · exact n4 h'
        · omega
    obtain ⟨b1, b2, b3⟩ := df_keep Fb.1 a1 hlr a2 a3
    refine ⟨b1, b2, b3, fun e => ?_⟩
    subst e
    rcases Fb.2 with h' | h'
    · exact hlr (Or.inl h')
    · exact hlr (Or.inr h')
  simp only [emit_apply, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hdefs : blockDefs (⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : Blob) = [pro] := by
    simp [blockDefs, aliasDst]
  have hin : BlobIn (fun r => r < gb.re ∧ HoonMap.get gb.cond r = Option.none)
      (⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : Blob) := by
    refine ⟨fun x hx => by simp at hx, ?_, fun x hx => by simp [jmp0] at hx⟩
    intro q hq' x hx
    simp only [List.mem_singleton] at hq'
    subst hq'
    simp only [Comp.poleRegs, List.mem_cons] at hx
    rcases hx with hx | hx
    · subst hx; exact ⟨hpl, hkpro⟩
    · exact ⟨(hNb x (kmb_mem_flatten _ _ hx)).1, (hNb x (kmb_mem_flatten _ _ hx)).2.2.1⟩
  have hren := kmb_ren_self hin
  refine ⟨il_emitGoal' (R := gb.re) Ib (Nat.le_refl _) rfl (batc_fresh fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj
      subst hj; exact Ib.goal.1) (hin.mono fun _ h => h.1)
      (fun r hr => by rw [hdefs, List.mem_singleton] at hr; subst hr; exact hkpro)
      (fun r hr => hr.elim) trivial, fun r hr hl => ?_, fun y hy => ?_⟩
  · refine La r (Lb r ?_)
    refine liveC_emitX Ib _ (Sure.bunt : Sure S) (NMem subNed) (fun y hy hn' hx => ?_) (fun j hj => ?_) r hr hl
    · rw [hren] at hy
      obtain ⟨-, hy | ⟨-, hy⟩⟩ := hy
      · simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs] at hy
        exact (hx (kmb_mem_flatten _ _ hy)).elim
      · simp [finRegs, jmpRegs, jmp0] at hy
    · rw [hren] at hj
      simp only [getJmps, List.mem_singleton] at hj
      subst hj
      refine ⟨Ib.lab hbt, fun y hl hdf _ _ => ?_⟩
      have hyp : y ≠ pro := by
        intro e; apply hdf
        rw [hren, hdefs, e, List.mem_singleton]
      exact hl.mono_r fun x hx => hx.elim id fun hz => (hyp (lazK_ofSure.mp hz).2).elim
  · obtain ⟨n1, n2, n3, n4⟩ := hNb y hy
    refine ⟨n1, fun hd' => ?_, n3⟩
    have e := (defd_put (b := (⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : Blob))
      Ib.ats.free (r := y)).mp (by simpa [Gen.emitted, hd] using hd')
    rcases e with e | e
    · exact n2 e
    · rw [hdefs, List.mem_singleton] at e; exact n4 e

/-- **The `%jmp` block under `%done`**: the goal "nothing at the block"
holds `IL`; only the callee's need's registers are live there. -/
theorem kxl_cb_done {K : Nat → Nat → Prop} {b : Bell} {subNed : Need} {g1 g2 : Comp.Gen Map}
    {cb : Nat} (hI : IL K (CGoalL.done : CGoalL S) g1)
    (hN : ∀ y, NMem subNed y → y < g1.re ∧ ¬ Defd g1.blocks y ∧ HoonMap.get g1.cond y = Option.none)
    (h : (emit ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ : CM Map Nat) g1 = some (cb, g2)) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 cb)) g2 ∧
    (∀ r, ¬ NMem subNed r → GLiveKL (unpM g2) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 cb)) r →
      GLiveKL (unpM g1) K (CGoalL.done : CGoalL S) r) ∧
    ∀ y, NMem subNed y → y < g2.re ∧ ¬ Defd g2.blocks y ∧ HoonMap.get g2.cond y = Option.none := by
  have hd : g1.drop = false := hI.ats.1
  simp only [emit_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hdefs : blockDefs (⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ : Blob) = [] := by simp [blockDefs]
  have hin : BlobIn (fun r => r < g1.re ∧ HoonMap.get g1.cond r = Option.none)
      (⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ : Blob) :=
    blobIn_nil_fin fun x hx => ⟨(hN x (kmb_mem_flatten _ _ hx)).1, (hN x (kmb_mem_flatten _ _ hx)).2.2⟩
  have hren := kmb_ren_self hin
  refine ⟨il_emitGoal' (R := g1.re) hI (Nat.le_refl _) rfl (batc_fresh fun j hj => by simp [finJumps] at hj)
      (hin.mono fun _ h => h.1) (fun r hr => by rw [hdefs] at hr; exact absurd hr List.not_mem_nil)
      (fun r hr => hr.elim) trivial, fun r hr hl => ?_, fun y hy => ?_⟩
  · have hget := unpM_emitted_self (g := g1) hd (⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ : Blob)
    rw [hren] at hget
    rcases kmb_live_at hget hl with h | ⟨j, hj, -⟩
    · obtain ⟨-, h | ⟨-, h⟩⟩ := h
      · exact h.elim
      · exact (hr (kmb_mem_flatten _ _ h)).elim
    · simp [getJmps] at hj
  · obtain ⟨n1, n2, n3⟩ := hN y hy
    exact ⟨n1, fun hd' => n2 ((defd_emitted_nil hI.ats hdefs).mp hd'), n3⟩


/-! ## The arm -/

/-- **The chain after the call block** (`kdm_dmPath` for `callL`). -/
theorem kxl_calRest (env : CallEnv) [KxlFL S Map env] (sup : Option Nomm) {p q : Nomm}
    (hp : PlainD p) (hq : PlainD q) (ihp : kxlLRLF S Map env sup p) (ihq : kxlLRLF S Map env sup q)
    {K : Nat → Nat → Prop} (goal : CGoalL S) (region : List Nat) {subNed : Need} {cb : Nat}
    {g0 gb g' : Comp.Gen Map} {nex : NextL S}
    (O1 : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 cb)) gb)
    (O2 : ∀ r, ¬ NMem subNed r → GLiveKL (unpM gb) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 cb)) r →
      GLiveKL (unpM g0) K goal r)
    (O3 : Distinct subNed)
    (O4 : ∀ y, NMem subNed y → y < gb.re ∧ ¬ Defd gb.blocks y ∧ HoonMap.get gb.cond y = Option.none)
    (h : ((if safeFolFol q = true then pure ⟨ofSure Sure.bunt, jmp0 cb⟩
          else runLCM env false sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 cb)) region : CM Map (NextL S))
          >>= fun nexFol =>
        pastL env.cod nexFol p region >>= fun nexFol =>
        runLCM env false sup p (CGoalL.next (ofSure ⟨subNed, HoonSet.empty⟩) nexFol.th) region >>= fun nexSub =>
        copyL nexSub nexFol.laz : CM Map (NextL S)) gb = some (nex, g')) :
    JL K nex g' ∧ LiveC K goal g0 g' nex := by
  obtain ⟨nq, gc, h3, h⟩ := bind_some h
  obtain ⟨nq', gd, h4, h⟩ := bind_some h
  obtain ⟨np, ge, h5, h6⟩ := bind_some h
  have h3' : kdlFol q (runLCM (S := S) (Map := Map) env false sup q) (CGoalL.next (ofSure Sure.bunt) (jmp0 cb))
      region gb = some (nq, gc) := h3
  obtain ⟨J, L⟩ := kxl_tailN (s := ⟨subNed, HoonSet.empty⟩) env sup hp hq ihp ihq O1 O3 O4 h3' h4 h5 h6
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  exact O2 r hr hg

/-- The callee's need's registers after `+need-ord-alloc-regs`: distinct,
fresh, so undefined, no key and no goal register. -/
theorem kxl_needOrd {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {bNed : NeedOrd}
    {subNed : Need} (hI : IL K goal g0) (h : needOrdAllocRegs bNed g0 = some (subNed, g1)) :
    IL K goal g1 ∧ unpM g1 = unpM g0 ∧ Distinct subNed ∧
    ∀ y, NMem subNed y → y < g1.re ∧ ¬ Defd g1.blocks y ∧ HoonMap.get g1.cond y = Option.none ∧ ¬ GRegL goal y := by
  obtain ⟨⟨k, rfl⟩, hle, hds, hm⟩ := needOrdAllocRegs_spec bNed g0 _ subNed h
  refine ⟨il_re_up hI hle rfl rfl rfl rfl, rfl, hds, fun y hy => ?_⟩
  obtain ⟨m1, m2⟩ := hm y hy
  refine ⟨m2, fun hd => ?_, hI.cond_ge m1, fun hg => ?_⟩
  · have := defd_lt hI.regs hd; omega
  · have := (hI.greg_lt hg).1; omega

/-- **The arm of the direct call with `mono` `|`** (callL with a bell):
the drop, and the `%cal` / `%jmp` call block. -/
theorem kxl_liveRun_callL (env : CallEnv) [KxlFL S Map env] :
    ∀ sup p q b key, PlainD p → PlainD q → kxlLRLF S Map env sup p → kxlLRLF S Map env sup q →
      kxlLRLF S Map env sup (Nomm.n2 p q (some (b, key))) := by
  intro sup p q b key hp hq ihp ihq K goal region g0 g1 nex hI hG h
  simp only [runLCM, callLM] at h
  cases goal with
  | next laz th =>
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [callL, hd, if_true] at h
      obtain ⟨nq, ga, h1, h⟩ := bind_some h
      obtain ⟨nq', gb, h2, h⟩ := bind_some h
      obtain ⟨np, gc, h3, h4⟩ := bind_some h
      have h1' : kdlFol q (runLCM (S := S) (Map := Map) env false sup q) (CGoalL.next (ofSure Sure.bunt) th) region g0 =
          some (nq, ga) := h1
      have hn : noneEquivalentL laz = true := ((Bool.and_eq_true _ _).mp hd).2
      obtain ⟨J, L⟩ := kxl_tailB env sup hp hq ihp ihq (kdm_il_bunt hI) h1' h2 h3 h4
      refine ⟨J, fun r hl => ?_⟩
      exact (L r hl).mono fun x y hxy => hxy.elim Or.inl fun hz => absurd hz (lazK_none hn)
    · simp only [callL, hd, Bool.false_eq_true, if_false] at h
      cases key with
      | some k => simp only at h <;> cases h
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr] at h <;> cases h
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn] at h <;> cases h
          | some bNed =>
            simp only [hr, hn] at h
            by_cases hs : env.sof (made p sup) p q b bNed = true
            · simp only [hs, if_true] at h; cases h
            · simp only [hs, Bool.false_eq_true, if_false] at h
              obtain ⟨subNed, ga, h1, h⟩ := bind_some h
              obtain ⟨cb, gb, h2, h⟩ := bind_some h
              obtain ⟨Ia, Ua, Da, Na⟩ := kxl_needOrd hI h1
              obtain ⟨O1, O2, O4⟩ := kxl_cb_kerf Ia Na h2
              exact kxl_calRest env sup hp hq ihp ihq _ region O1 (fun r hr hl => Ua ▸ O2 r hr hl) Da O4 h
  | pick z o =>
    simp only [callL] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          by_cases hs : env.sof (made p sup) p q b bNed = true
          · simp only [hs, if_true] at h; cases h
          · simp only [hs, Bool.false_eq_true, if_false] at h
            obtain ⟨subNed, ga, h1, h⟩ := bind_some h
            obtain ⟨cb, gb, h2, h⟩ := bind_some h
            obtain ⟨Ia, Ua, Da, Na⟩ := kxl_needOrd hI h1
            obtain ⟨O1, O2, O4⟩ := kxl_cb_kerf Ia Na h2
            exact kxl_calRest env sup hp hq ihp ihq _ region O1 (fun r hr hl => Ua ▸ O2 r hr hl) Da O4 h
  | done =>
    simp only [callL] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          by_cases hs : env.sof (made p sup) p q b bNed = true
          · simp only [hs, if_true] at h; cases h
          · simp only [hs, Bool.false_eq_true, if_false] at h
            obtain ⟨subNed, ga, h1, h⟩ := bind_some h
            obtain ⟨cb, gb, h2, h⟩ := bind_some h
            obtain ⟨Ia, Ua, Da, Na⟩ := kxl_needOrd hI h1
            obtain ⟨O1, O2, O4⟩ := kxl_cb_done Ia (fun y hy => ⟨(Na y hy).1, (Na y hy).2.1, (Na y hy).2.2.1⟩) h2
            exact kxl_calRest env sup hp hq ihp ihq _ region O1 (fun r hr hl => Ua ▸ O2 r hr hl) Da O4 h

/-! ## The targets -/

/-- **The liveness of every run of `runLCM env false` on `PlainD`**
(direct calls included), from the frame and the labels. -/
theorem liveRunF_plainD_of (env : CallEnv)
    (hFr : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env false sup nm))
    (hLb : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), HRL (Map := Map) (runLCM (S := S) env false sup nm)) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kxlLRLF S Map env sup nm :=
  haveI : KxlFL S Map env := ⟨hFr, hLb⟩
  kxl_liveRun_plainOfL env ⟨(kxl_armsLL_of env splitSpecL intoSpecL).1, (kxl_armsLL_of env splitSpecL intoSpecL).2,
    kxl_liveRun_callL env⟩


section
variable [MapKeys Map]

/-- **The n-ary pass with calls on `PlainD` (direct calls included)**: `OptIn`, `ReadsIn` at the
argument count, which is that of the need. -/
theorem kxl_all (env : CallEnv)
    (hFr : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env false sup nm))
    (hLb : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), HRL (Map := Map) (runLCM (S := S) env false sup nm))
    {nm : Nomm} (hp : PlainD nm)
    (hsa : TopSAR S Map env nm) {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) :
    OptIn c.blocks ∧ Compiler.ReadsIn c.nargs c.blocks ∧ c.nargs = countArgs c.need := by
  unfold finishLFC at h
  obtain ⟨⟨nex, g1⟩, h1, hA⟩ := Option.bind_eq_some_iff.mp h
  simp only at hA
  split at hA
  · cases hA
  obtain ⟨⟨nedF, g2⟩, h2, hB⟩ := Option.bind_eq_some_iff.mp hA
  rw [hbake] at hB
  simp only [List.map_nil] at hB
  obtain ⟨⟨u3, g3⟩, h3, hC⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨⟨u4, g4⟩, h4, hT⟩ := Option.bind_eq_some_iff.mp hC
  obtain ⟨J1, L1⟩ := liveRunF_plainD_of env hFr hLb nm hp Option.none _ _ _ _ _ _ il_gen0 trivial
    (by rw [runLCM_false]; exact h1)
  have I1 : IL (fun _ _ => False) (CGoalL.next nex.laz nex.th) g1 := J1
  have SA1 := hsa nex g1 h1
  have S1 := tn_sip I1 SA1
  obtain ⟨-, hap, hent⟩ := (I1.goal : GoalL g1 (CGoalL.next nex.laz nex.th))
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  subst e2
  have l2' : g1.re ≤ k2 := l2
  -- `+coerce-lazy`
  have I0 : CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 nedF k2
      ((nex.th.there, nex.laz) :: entries nex.laz) { g1 with re := k2 } := by
    refine ⟨sip_reg S1 l2', Nat.le_refl _, fun r hr => ⟨(mF r hr).2, fun d => ?_⟩, hap, fun e he => ?_⟩
    · have := S1.defd_lt d; have := (mF r hr).1; omega
    · obtain ⟨⟨b, hb, -⟩, ds, hr⟩ := hent e he
      exact ⟨⟨b, hb⟩, ds, fun r hm => ⟨by have := (hr r hm).1; omega,
        fun m => by have := (hr r hm).1; have := (mF r m).1; omega, (hr r hm).2⟩⟩
  obtain ⟨⟨I3, D3⟩, P, pP, kP, rP, -⟩ := coerceLazyL_prepI (S := S) (Map := Map)
    (fun rest g => CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 nedF k2 rest g ∧
      CoD g1.re ((nex.th.there, nex.laz) :: entries nex.laz) g1.blocks rest g)
    (fun _ _ _ _ _ _ hI hs => tn_step l2' hI hs) ⟨I0, fun e he => he, fun y d => Or.inl d⟩ h3
  -- the empty bake
  have hd3 : g3.drop = false := I3.1.drop
  obtain ⟨S4, b4, hb4, e4, -, -⟩ := sip_addOps I3.1 (opsOK_nil g3) h4
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k => by
    rw [e4]
    by_cases e : k = nex.th.there
    · subst e; rw [get_put_self, hb4, pre_nil]
    · rw [get_put_ne e]
  have c4 : g4.cond = g1.cond := by
    obtain ⟨b4', -, e4'⟩ := addOps_spec h4 hd3
    have k3 : g3.cond = g1.cond := (kc_coerceLazyL nedF less _ _).keep { g1 with re := k2 } _ _ h3
    rw [e4']
    exact k3
  have pP4 : Prep P g1.blocks g4.blocks := fun k => by rw [get4 k]; exact pP k
  have dd4 : ∀ y, Defd g4.blocks y → Defd g3.blocks y := fun y d => by
    obtain ⟨o, b, hb, m⟩ := defd_iff.mp d
    exact defd_iff.mpr ⟨o, b, by rw [← get4]; exact hb, m⟩
  -- keys of `cond`
  have uD : ∀ x, Defd g4.blocks x → unproxy g4.cond x = x := fun x d => by
    rw [c4]
    apply unproxy_none
    cases e : HoonMap.get g1.cond x with
    | none => rfl
    | some v =>
      obtain ⟨k1, k2', k3, -, -⟩ := I1.cond x v e
      rcases D3.2 x (dd4 x d) with d1 | ⟨e', he', m⟩ | hx
      · exact absurd d1 k2'
      · exact absurd ⟨e', he', m⟩ k3
      · omega
  have uG : ∀ x, ((∃ e ∈ (nex.th.there, nex.laz) :: entries nex.laz, NMem e.2.sure.ned x) ∨ g1.re ≤ x) →
      unproxy g1.cond x = x := fun x hx => by
    apply unproxy_none
    cases e : HoonMap.get g1.cond x with
    | none => rfl
    | some v =>
      obtain ⟨k1, -, k3, -, -⟩ := I1.cond x v e
      rcases hx with hx | hx
      · exact absurd hx k3
      · omega
  -- the final pass
  rw [toStraightF_run _ _ _ (isRun_needOrdAllocRegs h2)] at hT
  obtain ⟨start, hst, hT⟩ := Option.bind_eq_some_iff.mp hT
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hT
  rw [tu_proxRen] at hnew
  have D1 : Down g1.blocks := down_of_ats I1.ats
  have D4 : Down g4.blocks := downRk_prep pP4 (Down.rank D1)
  obtain ⟨-, R1, W1⟩ := stIn_of_ats I1.ats
  have args4 : ∀ k b j a, HoonMap.get g4.blocks k = some b → j ∈ getJmps b.fin → some a ∈ j.args →
      a ∈ blockDefs b := by
    intro k b j a hb hj ha
    obtain ⟨b0, hb0, rfl⟩ := get_prep pP4 hb
    exact mem_blockDefs_pre.mpr (Or.inl (SA1.args k b0 j a hb0 hj ha))
  have o1 : 1 ≤ nex.th.there := (D4 _ start hst).1
  have o0 : nex.th.there ≠ 0 := by omega
  have RD := rankDown_start (Down.rank D4) hst
  have gs8 := get_mapVals (renBlob (unproxy g4.cond)) (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)
  have hnew8 : ∀ k b', HoonMap.get new k = some b' →
      ∃ b, HoonMap.get (mapVals (renBlob (unproxy g4.cond))
          (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) k = some b ∧
        keepBlock (mapVals (renBlob (unproxy g4.cond)) (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start))
          (renReg ((flattenNeed nedF).headD 0) (flattenNeed nedF).length) k b = some (some b') := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := renameBlocks_get hnew hk
    refine ⟨renBlob (unproxy g4.cond) b, by rw [gs8, hb]; rfl, ?_⟩
    rw [keepBlock_ren RD gs8]; exact hkb
  have hst8 : HoonMap.get (unpM g4) nex.th.there = some (renBlob (unproxy g4.cond) start) := by
    simp only [unpM]; rw [get_mapVals, hst]; rfl
  have hbs0 : HoonMap.get (mapVals (renBlob (unproxy g4.cond))
      (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) 0 = some (renBlob (unproxy g4.cond) start) := by
    rw [gs8]; simp [HoonMap.get_put]
  have hbso : HoonMap.get (mapVals (renBlob (unproxy g4.cond))
      (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) nex.th.there = Option.none := by
    rw [gs8]; simp [HoonMap.get_put, HoonMap.get_del, o0]
  have hbsk : ∀ k, k ≠ 0 → k ≠ nex.th.there →
      HoonMap.get (mapVals (renBlob (unproxy g4.cond)) (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) k =
        HoonMap.get (unpM g4) k := fun k k0 ko => by
    simp only [unpM]; rw [gs8, get_mapVals]; simp [HoonMap.get_put, HoonMap.get_del, k0, ko]
  have hdB : DownRk id (unpM g4) := Down.rank (tu_down D4 _)
  -- the liveness at the entry
  have PP : Prep (fun k => (P k).map (renPole (unproxy g1.cond))) (unpM g1) (unpM g4) := by
    unfold unpM; rw [c4]; exact prep_mapVals pP4 _
  have hl : ∀ r, Live (unpM g4) nex.th.there r → NMem nedF r := fun r hr =>
    live_entry_of_prep PP (K := fun x y => (fun _ _ => False) x y ∨ lazK nex.th.there nex.laz x y)
      (fun k r hk => by
        rcases hk with hk | ⟨e, he, rfl, hm⟩
        · exact hk.elim
        · rw [defsOf_ren]
          exact List.mem_map.mpr ⟨r, kP e he r hm, uG r (Or.inl ⟨e, he, hm⟩)⟩)
      (fun r hk => L1 r hk)
      (fun k y hy => by
        obtain ⟨x, rfl, hx⟩ := opsRF_ren_back _ hy
        have hx' := rP k x hx
        rw [uG x (Or.inr (mF x hx').1)]
        exact hx') hr
  have hin : ∀ r, NMem nedF r → ¬ Defd (unpM g4) r := fun r hr d =>
    (I3.2.2.1 r hr).2 (dd4 r (tu_defd uD d))
  refine ⟨optIn_renOutR hst8 hbs0 hbso hbsk (renReg_inj _ _) (renReg_surj _ _) hnew8 hdB
    (tu_nodup uD S4.nd) (tu_cross uD S4.cr) (tu_noTr S4.tr _) (tu_downPar uD D4 S4.cr args4) hl hin, ?_, rfl⟩
  obtain ⟨-, -, -, -, c5⟩ := stOut_ren hst8 hbs0 hbso hbsk (renReg_inj _ _) (renReg_surj _ _) hnew8
    (renameBlocks_ren RD gs8 hnew) hdB (tu_arity (arityOK_prep pP4 R1) _) (tu_twoNA (twoNA_prep pP4 W1) _) hl
  refine readsIn_of_live fun r' hlv _ => ?_
  obtain ⟨r, rfl, hr⟩ := c5 r' hlv
  have hf : flattenNeed nedF = List.range' g1.re (k2 - g1.re) := flatten_needOrdAllocRegs ord g1 _ nedF h2
  have hm := (mem_flatten nedF r).mpr hr
  rw [hf, List.mem_range'_1] at hm
  show renReg ((flattenNeed nedF).headD 0) (flattenNeed nedF).length r < countArgs (needToOrd nedF)
  rw [countArgs_flatten, hf, List.length_range']
  obtain ⟨n, hn⟩ : ∃ n, k2 - g1.re = n + 1 := ⟨k2 - g1.re - 1, by omega⟩
  rw [hn, List.range'_succ, List.headD_cons]
  unfold renReg
  split <;> (try split) <;> omega


/-- **`OptIn` of the n-ary code with direct calls on `PlainD`**, nothing
baked, from the frame, the labels and `TopSAR`. -/
theorem optIn_finishLFC_ofD (env : CallEnv)
    (hFr : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env false sup nm))
    (hLb : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), HRL (Map := Map) (runLCM (S := S) env false sup nm))
    {nm : Nomm} (hp : PlainD nm) (hsa : TopSAR S Map env nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) : OptIn c.blocks :=
  (kxl_all env hFr hLb hp hsa hbake h).1

/-- **`ReadsIn` of the n-ary code with direct calls on `PlainD`**, and its
argument count is that of its need. -/
theorem readsIn_finishLFC_ofD (env : CallEnv)
    (hFr : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env false sup nm))
    (hLb : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), HRL (Map := Map) (runLCM (S := S) env false sup nm))
    {nm : Nomm} (hp : PlainD nm) (hsa : TopSAR S Map env nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) :
    Compiler.ReadsIn c.nargs c.blocks ∧ c.nargs = countArgs c.need :=
  (kxl_all env hFr hLb hp hsa hbake h).2

end

end Raw
end SkaModel
end Formalization
