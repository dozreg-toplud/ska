import lemmas.Ska.RawInvCLTen

/-!
# The run-level liveness with calls: the cons arm

README Gaps 14 (b), track D.  The cons `[p q]`: under `%pick` a `bom`
block, then `q`, `+past`, `p`, `+copy` for `bunt` goals; under `%next laz
th` the `+split` of the goal into `hed` and `tel` at a block `o`, `+past` of
`hed` over `q`, `q` for `tel`, `+past`, `p` for `hed`'s parked tree, `+copy`;
under `%done` the block of `+simple-next`, then the `%next` case.

**Finding: the field `cons` of `ArmsL` is false as stated.**  `LR` asks
`JL` and `LiveC` from every goal with `IL`, but `IL` does not ask `LabUniq`
of the goal's tree, and the cons splits the goal's tree into the two goals
of its parts, so `+copy` meets two trees with bonds at one label and drops
one (`gD`).  Under `goalDup` (`RawInvCLCheckIJ.lean`: two bonds at label
`1`, `IL` holds), 144 of the 2,856 `PlainN` top runs fail `JL ∧ LiveC` (8
fail `JL`); `liveRun_plainOf` would give `LR` of them, so `ArmsL` has no
member: `n5` is proved (`armsL_n5`), `n2` too (`armsL_n2`), and the cons and
`%10` split the goal (`RawInvCLTen.lean`: `[10 [2 [0 1]] [0 1]]`).  The true statement adds the label clause `LG` of the goal
(`LabUniq`, entries below `bo`) to the precondition: `LiveRunL`, `LRL` of
`RawInvCLTen.lean` (`lrl_iff`, `LR.toL`; the result's `LG` comes from `labRun_plain`).

* `SplitSpecL`: the `IL`/`LiveC` spec of `+split` (checked first at every
  split of the 2,856 `PlainN` runs under the seven goals: 0 failures; without
  `tel`'s kills 900, 900, 336, 900 runs fail, without `hed`'s the same):
  `IL` of `hed` at `o`, of `tel` at `o` with `hed`'s tree as outer kills, the
  two trees apart, and a register live at `o` with both trees' kills is one
  the goal may leave live.  Not proved here.
* `il_glueT` (a goal kept across a step whose footprint misses its
  registers, rooted at any `Fresh` jump), `il_killsOf`, `lreg_mem`.
* **`cons_tail`**: `q`, `+past`, `p`, `+copy` for tree goals.
* `liveRun_cons_pick`, `liveRun_cons_next` (from `SplitSpecL`),
  **`liveRun_consL`**: `LRL` of the cons from `LRL` of its parts and
  `SplitSpecL`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The statement with the label clause -/

/-- `LiveRun IL JL` from goals that also meet the label clause `LG`. -/
def LiveRunL (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S),
    IL K goal g0 → LG goal g0 → rp goal region g0 = some (nex, g1) → JL K nex g1 ∧ LiveC K goal g0 g1 nex

/-- `LRL` (`RawInvCLTen.lean`) is `LiveRunL` of one run of `runLC`. -/
theorem lrl_iff {env : CallEnv} {sup : Option Nomm} {nm : Nomm} :
    LRL S Map env sup nm ↔ LiveRunL (Map := Map) (runLC (S := S) env sup nm) := Iff.rfl

theorem LR.toL {env : CallEnv} {sup : Option Nomm} {nm : Nomm} (h : LR S Map env sup nm) : LRL S Map env sup nm :=
  lrl_of_lr h

/-- **The spec of `+split`** (checked at every split of `PlainN`). -/
def SplitSpecL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (laz : Lazy S) (th : Jmp) (g0 g1 : Comp.Gen Map) (hed tel : Lazy S) (o : Nat),
    IL K (CGoalL.next laz th) g0 → splitL ⟨laz, th⟩ g0 = some ((hed, tel, o), g1) →
    IL K (CGoalL.next hed (jmp0 o)) g1 ∧ IL (fun x y => K x y ∨ lazK o hed x y) (CGoalL.next tel (jmp0 o)) g1 ∧
    TreesApart o hed o tel ∧
    ∀ r, LiveK (unpM g1) (fun x y => (K x y ∨ lazK o hed x y) ∨ lazK o tel x y) o r →
      GLiveKL (unpM g0) K (CGoalL.next laz th) r

/-! ## Helpers -/

theorem lreg_mem {l : Lazy S} {y : Nat} (o : Nat) (h : LReg l y) :
    ∃ e ∈ (o, l) :: entries l, NMem e.2.sure.ned y := by
  rcases h with h | ⟨e, he, h⟩
  · exact ⟨(o, l), List.mem_cons_self, h⟩
  · exact ⟨e, List.mem_cons_of_mem _ he, h⟩

/-- **A goal kept across a step** whose footprint `Q` misses its registers,
rooted at any `Fresh` jump of the new state. -/
theorem il_glueT {K K' : Nat → Nat → Prop} {l : Lazy S} {th th' : Jmp} {Q : Nat → Prop} {g g' : Comp.Gen Map}
    {goal' : CGoalL S} (hI : IL K (CGoalL.next l th) g) (hJ : IL K' goal' g') (hD : DF Q g g') (hKP : KP g g')
    (hQ : ∀ y, LReg l y → ¬ Q y) (hf : Fresh g' th') : IL K' (CGoalL.next l th') g' := by
  obtain ⟨hre, hc, hdf⟩ := hD
  obtain ⟨-, hna, hent⟩ := (hI.goal : GoalL g (CGoalL.next l th))
  refine ⟨hJ.ats, hJ.regs, fun k v hk => ?_, hJ.kvan, hf, ?_, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hJ.cond k v hk
    refine ⟨k1, k2, fun hg => ?_, k4, k5⟩
    have hg' : GRegL (CGoalL.next l th) k := gregL_next.mpr (gregL_next.mp hg)
    rcases hc k v hk with h | h
    · exact (hI.cond k v h).2.2.1 hg'
    · have := (hI.greg_lt hg').1; omega
  · rw [NeedsApart, List.pairwise_cons] at hna ⊢
    exact hna
  · rcases List.mem_cons.mp he with rfl | he'
    · obtain ⟨-, hds, hr⟩ := hent (th.there, l) List.mem_cons_self
      obtain ⟨b, hb, hp, -⟩ := hf
      refine ⟨⟨b, hb, hp⟩, hds, fun r hm => ⟨Nat.lt_of_lt_of_le (hr r hm).1 hre, fun hd => ?_⟩⟩
      rcases hdf r hd with h | h
      · exact (hr r hm).2 h
      · exact hQ r (Or.inl hm) h
    · obtain ⟨⟨b, hb, hp⟩, hds, hr⟩ := hent e (List.mem_cons_of_mem _ he')
      obtain ⟨b', hb', hp', -⟩ := hKP.2.2 _ b hb
      refine ⟨⟨b', hb', hp'.trans hp⟩, hds, fun r hm => ⟨Nat.lt_of_lt_of_le (hr r hm).1 hre, fun hd => ?_⟩⟩
      rcases hdf r hd with h | h
      · exact (hr r hm).2 h
      · exact hQ r (Or.inr ⟨e, he', hm⟩) h

/-- **Another goal's tree as outer kills**: its labels lie below `bo`. -/
theorem il_killsOf {K K2 : Nat → Nat → Prop} {goal : CGoalL S} {l : Lazy S} {j : Jmp} {g : Comp.Gen Map}
    (hI : IL K goal g) (hJ : IL K2 (CGoalL.next l j) g) :
    IL (fun x y => K x y ∨ lazK j.there l x y) goal g := by
  refine ⟨hI.ats, hI.regs, hI.cond, ⟨fun k r hk hh => ?_⟩, hI.goal⟩
  rcases hh with hh | ⟨e, he, ex, -⟩
  · exact hI.kvan.van k r hk hh
  · obtain ⟨⟨b, hb, -⟩, -, -⟩ := (hJ.goal : GoalL g (CGoalL.next l j)).2.2 e he
    have := hJ.lab hb
    omega

/-! ## `q`, `+past`, `p`, `+copy` for tree goals -/

/-- **The tail of the cons** from the goals "`tel` at `thq`" (with `hT`'s
tree as outer kills) and "`hT` at `thq`": `JL` of the result, and a register
live at its entry is live for the first goal. -/
theorem cons_tail (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {hT tel : Lazy S} {thq : Jmp} {g2 g3 g4 g5 g6 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hIq : IL (fun x y => K x y ∨ lazK thq.there hT x y) (CGoalL.next tel thq) g2)
    (hIh : IL K (CGoalL.next hT thq) g2) (hap : ∀ y, LReg hT y → ¬ LReg tel y)
    (lh : LabUniq hT) (lt : LabUniq tel) (lhb : ∀ e ∈ entries hT, e.1 < g2.bo)
    (ltb : ∀ e ∈ entries tel, e.1 < g2.bo)
    (h1 : runLC env sup q (CGoalL.next tel thq) region g2 = some (nq, g3))
    (h2 : pastL env.cod nq p region g3 = some (nq', g4))
    (h3 : runLC env sup p (CGoalL.next hT nq'.th) region g4 = some (np, g5))
    (h4 : copyL np nq'.laz g5 = some (nex, g6)) :
    JL K nex g6 ∧ ∀ r, LiveK (unpM g6) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      GLiveKL (unpM g2) (fun x y => K x y ∨ lazK thq.there hT x y) (CGoalL.next tel thq) r := by
  obtain ⟨Jq, Lq⟩ := ihq _ _ region g2 g3 nq hIq ⟨lt, ltb⟩ h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := frameRun_plain env q hq sup _ region g2 g3 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, KP23, -, lq1, lq2⟩ := (labRun_plain (S := S) (Map := Map) env q hq sup
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
  have Fp := frameRun_plain env p hp sup _ region g4 g5 np h3
  obtain ⟨-, KP45, -, LU1, -⟩ := (labRun_plain (S := S) (Map := Map) env p hp sup
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
theorem liveRun_cons_pick (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {z o0 : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o0 : CGoalL S) g0)
    (h : (do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      let nex2 ← runLC env sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLC env sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
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
  obtain ⟨J, L⟩ := cons_tail env sup hp hq ihp ihq I1 I0 (fun y hy _ => hnb y hy) (labUniq_ofSure _)
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
theorem liveRun_cons_next (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) (hS : SplitSpecL S Map) {K : Nat → Nat → Prop}
    {region : List Nat} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.next laz th) g0) (hL : LG (CGoalL.next laz th) g0)
    (h : (do
      let (hed, tel, o) ← splitL ⟨laz, th⟩
      let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
      let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
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
  obtain ⟨J, L⟩ := cons_tail env sup hp hq ihp ihq hIq IhK hap LUH LUt LBH ltb h1 h2 h3 h4
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
theorem liveRun_consL (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) (hS : SplitSpecL S Map) :
    LRL S Map env sup (Nomm.cons p q) := by
  intro K goal region g0 g1 nex hI hL h
  simp only [runLC] at h
  obtain ⟨goal', ga, hga, h⟩ := bind_some h
  cases goal with
  | pick z o0 =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    exact liveRun_cons_pick env sup hp hq ihp ihq hI h
  | next laz th =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    exact liveRun_cons_next env sup hp hq ihp ihq hS hI hL h
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
    obtain ⟨J, L⟩ := liveRun_cons_next env sup hp hq ihp ihq hS I1 (lg_ofSure _ _ _) h
    exact ⟨J, LiveC.trans (liveC_simpleNextL_done hI.ats.1 (hI.cond_ge (Nat.le_refl _)) hsn) L⟩

end Raw
end SkaModel
end Formalization
