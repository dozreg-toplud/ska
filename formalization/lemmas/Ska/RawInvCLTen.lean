import lemmas.Ska.RawInvCLFive

/-!
# The run-level liveness with calls: the arm `%10`

README Gaps 14 (b), track D.  The run of `[10 [a v] q]`: `+simple-next`,
`+into` (donor `d`, recipient `rec`, block `o`), `+past` of the recipient
over `v` (`⟨R, sR⟩`), `v` for "`d` at `sR`", `+past` over `q`
(`⟨second, s2⟩`), `q` for "`R` at `s2`", `+copy`.

* **`LRL`**: `LR` with the label clause `LG` of the goal in the
  precondition.  `LR` itself is FALSE for `%10` and cons: from the goal
  `goalDup` of `RawInvCLCheckIJ.lean` (two bonds at label `1`; it meets
  `IL`), the liveness spec fails on `[10 [2 [0 1]] [0 1]]` and
  `[[0 1] [0 1]]` (`live1K`), whose parts meet `LR` (`liveRun_n0`): the
  halves of the goal both hold the two bonds, and `+copy` merges both of the
  first with one of the second and drops the other (`gD`).  So the field
  `n10` (and `cons`) of `ArmsL` is false as stated; `lrl_of_lr` gives `LRL`
  from `LR`.
* `IntoSpecL`: the spec of `+into` (checked at every `+into` of the 664
  `PlainN` nomms of `enumCX` with a `%10`, under the seven goals of
  `RawInvCLCheckCopy.lean`: 0 failures): `IL` of both halves as goals at
  `o`, their registers apart, and a register live at `o` with both halves'
  kills is one the goal may leave live.  Not proved here.
* `il_addKillsOf`, `il_carry` (a goal kept across steps that write none of
  its registers, re-rooted at a fresh jump), `il_glueL` (`il_glue` for a
  tree goal).
* **`ten_tail`**, **`liveRun_n10L`**, **`armsL_n10L`**: the arm in the form
  `LRL v → LRL q → LRL (%10 a v q)`, from `IntoSpecL`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`LR` with the label clause in the precondition.** -/
abbrev LRL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (sup : Option Nomm) (nm : Nomm) : Prop :=
  ∀ (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S),
    IL K goal g0 → LG goal g0 → runLC env sup nm goal region g0 = some (nex, g1) →
      JL K nex g1 ∧ LiveC K goal g0 g1 nex

theorem lrl_of_lr {env : CallEnv} {sup : Option Nomm} {nm : Nomm} (h : LR S Map env sup nm) :
    LRL S Map env sup nm :=
  fun K goal region g0 g1 nex hI _ hr => h K goal region g0 g1 nex hI hr

/-- **The spec of `+into`** (checked, not proved). -/
def IntoSpecL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (laz : Lazy S) (th : Jmp) (axe : Nat) (g g' : Comp.Gen Map) (d r : Lazy S) (o : Nat),
    IL K (CGoalL.next laz th) g → intoL ⟨laz, th⟩ axe g = some ((d, r, o), g') →
    IL K (CGoalL.next d (jmp0 o)) g' ∧ IL K (CGoalL.next r (jmp0 o)) g' ∧ (∀ y, LReg d y → ¬ LReg r y) ∧
    ∀ y, LiveK (unpM g') (fun x z => (K x z ∨ lazK o d x z) ∨ lazK o r x z) o y →
      GLiveKL (unpM g) K (CGoalL.next laz th) y

/-! ## Goals carried along -/

/-- **Another goal's tree as outer kills**: its labels lie below `bo`. -/
theorem il_addKillsOf {K : Nat → Nat → Prop} {goal : CGoalL S} {l : Lazy S} {th : Jmp} {g : Comp.Gen Map}
    (hI : IL K goal g) (hL : IL K (CGoalL.next l th) g) :
    IL (fun x y => K x y ∨ lazK th.there l x y) goal g := by
  refine ⟨hI.ats, hI.regs, hI.cond, ⟨fun k r hk hh => ?_⟩, hI.goal⟩
  rcases hh with hh | ⟨e, he, ex, -⟩
  · exact hI.kvan.van k r hk hh
  · obtain ⟨⟨b, hb, -⟩, -, -⟩ := (hL.goal : GoalL g (CGoalL.next l th)).2.2 e he
    have := hL.lab hb
    omega

/-- **A goal kept across steps that write none of its registers**, asked at a
fresh jump of the later state. -/
theorem il_carry {K0 K : Nat → Nat → Prop} {l : Lazy S} {th th' : Jmp} {goal' : CGoalL S} {g g' : Comp.Gen Map}
    (hI : IL K0 (CGoalL.next l th) g) (hJ : IL K goal' g') (hKP : KP g g') (hre : g.re ≤ g'.re)
    (hc : ∀ k v, HoonMap.get g'.cond k = some v → HoonMap.get g.cond k = some v ∨ g.re ≤ k)
    (hdf : ∀ y, LReg l y → Defd g'.blocks y → Defd g.blocks y) (hfr : Fresh g' th') :
    IL K (CGoalL.next l th') g' := by
  obtain ⟨-, hna, hent⟩ := (hI.goal : GoalL g (CGoalL.next l th))
  refine ⟨hJ.ats, hJ.regs, fun k v hk => ?_, hJ.kvan, hfr, ?_, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hJ.cond k v hk
    refine ⟨k1, k2, fun hg => ?_, k4, k5⟩
    have hg' : GRegL (CGoalL.next l th) k := gregL_next.mpr (gregL_next.mp hg)
    rcases hc k v hk with h | h
    · exact (hI.cond k v h).2.2.1 hg'
    · have := (hI.greg_lt hg').1; omega
  · obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hna
    exact List.pairwise_cons.mpr ⟨fun e he r hr => h1 e he r hr, h2⟩
  · rcases List.mem_cons.mp he with rfl | he
    · obtain ⟨b, hb, hp, -⟩ := hfr
      obtain ⟨-, hds, hr⟩ := hent _ List.mem_cons_self
      exact ⟨⟨b, hb, hp⟩, hds, fun r hm => ⟨Nat.lt_of_lt_of_le (hr r hm).1 hre,
        fun hd => (hr r hm).2 (hdf r (Or.inl hm) hd)⟩⟩
    · obtain ⟨⟨b, hb, hp⟩, hds, hr⟩ := hent e (List.mem_cons_of_mem _ he)
      obtain ⟨b', hb', hp', -⟩ := hKP.2.2 _ b hb
      exact ⟨⟨b', hb', hp'.trans hp⟩, hds, fun r hm => ⟨Nat.lt_of_lt_of_le (hr r hm).1 hre,
        fun hd => (hr r hm).2 (hdf r (Or.inr ⟨e, he, hm⟩) hd)⟩⟩

/-- **`il_glue` for a tree goal**: `second` keeps `IL` across a run from it
for "`R` at the same jump", when the two trees' registers are apart. -/
theorem il_glueL {K K' : Nat → Nat → Prop} {second R : Lazy S} {th : Jmp} {g5 g6 : Comp.Gen Map}
    {np : NextL S} (hI : IL K (CGoalL.next second th) g5) (hJ : IL K' np.goal g6) (hK : ∀ x y, K x y → K' x y)
    (hF : FrX (CGoalL.next R th) g5 g6 np) (hKP : KP g5 g6)
    (hrs : ∀ y, LReg second y → ¬ LReg R y) : IL K (CGoalL.next second th) g6 := by
  obtain ⟨hD, -⟩ := hF
  obtain ⟨hre, hc, hdf⟩ := frL_iff.mp hD
  exact il_carry hI (hJ.monoK hK) hKP hre hc (fun y hy hd => by
    rcases hdf y hd with h | h | h
    · exact h
    · have := (hI.greg_lt (gregL_next.mpr hy)).1; omega
    · exact (hrs y hy (gregL_next.mp h)).elim) (fresh_kp (hI.goal : GoalL g5 (CGoalL.next second th)).1 hKP)

theorem gfl_of_il {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) :
    GFL (Map := Map) goal g := by
  cases goal with
  | next laz th => exact hI.goal.1
  | pick z o => exact hI.goal
  | done => trivial

/-! ## The tail -/

/-- **The tail of `%10`** from the two halves of `+into` at `o`: `JL` of the
result, and a register live at its entry is live at `o` with both halves'
kills. -/
theorem ten_tail (env : CallEnv) (sup : Option Nomm) {v q : Nomm} (hv : PlainN v) (hq : PlainN q)
    (ihv : LRL S Map env sup v) (ihq : LRL S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {d rec : Lazy S} {o : Nat} {g2 g3 g4 g5 g6 g7 : Comp.Gen Map} {nR nD nD' nQ nex : NextL S}
    (Id : IL K (CGoalL.next d (jmp0 o)) g2) (Ir : IL K (CGoalL.next rec (jmp0 o)) g2)
    (hap : ∀ y, LReg d y → ¬ LReg rec y) (ld : LabUniq d ∧ ∀ e ∈ entries d, e.1 < g2.bo)
    (lr : LabUniq rec ∧ ∀ e ∈ entries rec, e.1 < g2.bo)
    (h2 : pastL env.cod ⟨rec, jmp0 o⟩ v region g2 = some (nR, g3))
    (h3 : runLC env sup v (CGoalL.next d nR.th) region g3 = some (nD, g4))
    (h4 : pastL env.cod nD q region g4 = some (nD', g5))
    (h5 : runLC env sup q (CGoalL.next nR.laz nD'.th) region g5 = some (nQ, g6))
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
  have Fv := frameRun_plain env v hv sup _ region g3 g4 nD h3
  obtain ⟨A4, KP34, -, lD1, lD2⟩ := (labRun_plain (S := S) (Map := Map) env v hv sup
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
  have Fq := frameRun_plain env q hq sup _ region g5 g6 nQ h5
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRun_plain (S := S) (Map := Map) env q hq sup
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
theorem liveRun_n10L (hInto : IntoSpecL S Map) (env : CallEnv) (sup : Option Nomm) {a : Nat} {v q : Nomm}
    (hv : PlainN v) (hq : PlainN q) (ihv : LRL S Map env sup v) (ihq : LRL S Map env sup q) :
    LRL S Map env sup (Nomm.n10 a v q) := by
  intro K goal region g0 g7 nex hI hG h
  simp only [runLC] at h
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
  obtain ⟨J, Lt⟩ := ten_tail env sup hv hq ihv ihq Id Ir hap ld lr h2 h3 h4 h5 h6
  exact ⟨J, fun y hl => L1 y (Lin y (Lt y hl))⟩

/-- The field `n10` in the form `LRL`, from the spec of `+into`. -/
theorem armsL_n10L (hInto : IntoSpecL S Map) (env : CallEnv) :
    ∀ sup a v q, PlainN v → PlainN q → LRL S Map env sup v → LRL S Map env sup q →
      LRL S Map env sup (Nomm.n10 a v q) :=
  fun sup _ _ _ hv hq ihv ihq => liveRun_n10L hInto env sup hv hq ihv ihq

end Raw
end SkaModel
end Formalization
