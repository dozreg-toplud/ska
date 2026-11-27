import lemmas.Ska.RawInvCLRun
import lemmas.Ska.RawInvCLLabAll
import lemmas.Ska.RawInvCLCopyIL
import lemmas.Ska.RawInvCLFrameRun

/-!
# The run-level liveness with calls: the arm `%5`

README Gaps 14 (b), track D.  The field `n5` of `ArmsL`.  After `re` (`rp`),
`re` (`rq`) and the block `o` that compares them, `q` runs for "`rq` at
`o`", `+past`, `p` runs for "`rp` at the continuation" with the outer kills
of `+past`'s result `second` added, and `+copy` merges `p`'s result with
`second`.

* `liveC_emitX`: `liveC_emitG` for a block emitted at the current state,
  with registers `X` excluded (the block reads `rp`, which `p` defines).
* `il_re_up`, `IL.monoK`, `il_addKills` (a goal's own tree as outer kills),
  `IL.greg_lt`, `df_keep` (a register outside a step's footprint stays
  undefined and no key).
* `OPh`: what the block `o` leaves; `oph_eqq` (the `%eqq` block for a
  `%pick` goal, with old registers), `oph_equ` (the `[equ rp rq]` hop for a
  none-equivalent `%next` goal).
* `il_glue`: `IL` of `second` kept across `p`'s run (frame, `KP`, `rp` not a
  register of `second`).
* **`five_tail`**: `q`, `+past`, `p`, `+copy` from the goal "`rq` at `o`":
  `JL` of the result, and a register live at its entry is not `rp` and is
  live for that goal (`copyL_spec`, `labRun_plain`, `frameRun_plain`,
  `pastL_spec`).
* **`liveRun_n5`**: `LR` of `%5` from `LR` of its parts.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Helpers -/

/-- `liveC_emitG` for a block emitted at the current state, the registers
`X` excluded. -/
theorem liveC_emitX {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 : Comp.Gen Map} (hI : IL K goal g0)
    (b : Blob) (s : Sure S) (X : Nat → Prop)
    (hb : ∀ r, BlockRF (renBlob (unproxy g0.cond) b) r → ¬ NMem s.ned r → ¬ X r → GLiveKL (unpM g0) K goal r)
    (hj : ∀ j ∈ getJmps (renBlob (unproxy g0.cond) b).fin, j.there < g0.bo ∧
      ∀ r, LiveK (unpM g0) K j.there r → r ∉ blockDefs (renBlob (unproxy g0.cond) b) → ¬ NMem s.ned r →
        ¬ X r → GLiveKL (unpM g0) K goal r) (y : Nat) (hy : ¬ X y)
    (hl : LiveK (unpM (g0.emitted b)) (fun x y => K x y ∨ lazK g0.bo (ofSure s) x y) g0.bo y) :
    GLiveKL (unpM g0) K goal y := by
  have hd : g0.drop = false := hI.ats.1
  have hget := unpM_emitted_self (g := g0) hd b
  cases hl with
  | here hb' hr hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    exact hb y hr (fun hm => hk' (Or.inr (lazK_ofSure.mpr ⟨rfl, hm⟩))) hy
  | next hb' hjj hl hdf hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨hlt, hJ⟩ := hj _ hjj
    refine hJ y ?_ hdf (fun hm => hk' (Or.inr (lazK_ofSure.mpr ⟨rfl, hm⟩))) hy
    exact (liveK_frameP hI.downU (fun x hx => (unpM_emitted_ne (g := g0) hd _
      (Nat.ne_of_lt hx)).trans rfl) hlt).mp (hl.mono fun _ _ hk => Or.inl hk)

/-- `IL` at a state with a larger `re` and the same blocks, `cond`, `bo`
and `drop`. -/
theorem il_re_up {K : Nat → Nat → Prop} {goal : CGoalL S} {g g' : Comp.Gen Map} (hI : IL K goal g)
    (hR : g.re ≤ g'.re) (hb : g'.blocks = g.blocks) (hc : g'.cond = g.cond) (hbo : g'.bo = g.bo)
    (hd : g'.drop = g.drop) : IL K goal g' := by
  have A : ATS g' := by
    obtain ⟨a1, a2, a3⟩ := hI.ats
    refine ⟨hd.trans a1, hbo ▸ a2, fun k b h => ?_⟩
    rw [hb] at h
    obtain ⟨b1, b2, b3, b4⟩ := a3 k b h
    exact ⟨hbo ▸ b1, hb ▸ b2, b3, b4⟩
  refine ⟨A, fun k b h => ?_, fun k v h => ?_, hbo ▸ hI.kvan, ?_⟩
  · rw [hb] at h; exact (hI.regs k b h).mono fun x hx => Nat.lt_of_lt_of_le hx hR
  · rw [hc] at h
    obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v h
    exact ⟨Nat.lt_of_lt_of_le k1 hR, hb ▸ k2, k3, Nat.lt_of_lt_of_le k4 hR, hc ▸ k5⟩
  · have G := hI.goal
    cases goal with
    | next laz th =>
      obtain ⟨⟨b, h1, h2, h3⟩, h4, h5⟩ := G
      refine ⟨⟨b, hb ▸ h1, h2, h3⟩, h4, fun e he => ?_⟩
      obtain ⟨⟨b', e1, e2⟩, e3, e4⟩ := h5 e he
      exact ⟨⟨b', hb ▸ e1, e2⟩, e3, fun r hr => ⟨Nat.lt_of_lt_of_le (e4 r hr).1 hR, hb ▸ (e4 r hr).2⟩⟩
    | pick z o =>
      obtain ⟨⟨b, h1, h2, h3⟩, ⟨b', h1', h2', h3'⟩⟩ := G
      exact ⟨⟨b, hb ▸ h1, h2, h3⟩, ⟨b', hb ▸ h1', h2', h3'⟩⟩
    | done => trivial

/-- Fewer outer kills. -/
theorem IL.monoK {K K' : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K' goal g)
    (hK : ∀ x y, K x y → K' x y) : IL K goal g :=
  ⟨h.ats, h.regs, h.cond, ⟨fun k r hk hh => h.kvan.van k r hk (hK _ _ hh)⟩, h.goal⟩

/-- **A goal's own tree as outer kills**: its labels lie below `bo`. -/
theorem il_addKills {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g : Comp.Gen Map}
    (hI : IL K (CGoalL.next laz th) g) :
    IL (fun x y => K x y ∨ lazK th.there laz x y) (CGoalL.next laz th) g := by
  refine ⟨hI.ats, hI.regs, hI.cond, ⟨fun k r hk hh => ?_⟩, hI.goal⟩
  rcases hh with hh | ⟨e, he, ex, -⟩
  · exact hI.kvan.van k r hk hh
  · obtain ⟨⟨b, hb, -⟩, -, -⟩ := (hI.goal : GoalL g (CGoalL.next laz th)).2.2 e he
    have := hI.lab hb
    omega

/-- A register of an `IL` goal lies below `re` and is not defined. -/
theorem IL.greg_lt {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {r : Nat}
    (hr : GRegL goal r) : r < g.re ∧ ¬ Defd g.blocks r := by
  cases goal with
  | next laz th =>
    obtain ⟨e, he, hm⟩ := hr
    exact ((hI.goal : GoalL g (CGoalL.next laz th)).2.2 e he).2.2 r hm
  | pick _ _ => exact hr.elim
  | done => exact hr.elim

/-- A register outside a step's footprint stays undefined and no key. -/
theorem df_keep {Q : Nat → Prop} {g g' : Comp.Gen Map} (d : DF Q g g') {r : Nat} (hr : r < g.re) (hq : ¬ Q r)
    (hd : ¬ Defd g.blocks r) (hk : HoonMap.get g.cond r = Option.none) :
    r < g'.re ∧ ¬ Defd g'.blocks r ∧ HoonMap.get g'.cond r = Option.none := by
  obtain ⟨d1, d2, d3⟩ := d
  refine ⟨Nat.lt_of_lt_of_le hr d1, fun h => (d3 r h).elim hd hq, ?_⟩
  cases e : HoonMap.get g'.cond r with
  | none => rfl
  | some v =>
    rcases d2 r v e with h | h
    · rw [hk] at h; cases h
    · omega

/-- An emitted block that defines nothing. -/
theorem defd_emitted_nil {g : Comp.Gen Map} {b : Blob} (A : ATS g) (hb : blockDefs b = []) {r : Nat} :
    Defd (g.emitted b).blocks r ↔ Defd g.blocks r := by
  have hd : g.drop = false := A.1
  show Defd (if g.drop then g.blocks else HoonMap.put g.blocks g.bo b) r ↔ _
  simp only [hd, Bool.false_eq_true, if_false]
  rw [defd_put A.free, hb]
  simp

/-! ## The block `o` -/

/-- **What the block `o` of `%5` leaves**: the goal "`rq` at `o`" with
`IL`, a register other than `rp` live for it is one the outer goal may leave
live, and `rp` still below `re`, undefined and no key. -/
def OPh (K : Nat → Nat → Prop) (goal : CGoalL S) (g0 g3 : Comp.Gen Map) (rp rq o : Nat) : Prop :=
  IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3 ∧
  (∀ r, r ≠ rp → GLiveKL (unpM g3) K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) r →
    GLiveKL (unpM g0) K goal r) ∧
  rp < g3.re ∧ ¬ Defd g3.blocks rp ∧ HoonMap.get g3.cond rp = Option.none

/-- The goal "`rq` at the block just emitted", `rq` old, undefined, no key. -/
theorem il_old_at {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {b : Blob}
    (hp : b.par = []) (hbat : BATC g.blocks b) (hin : BlobIn (· < g.re) b) (hdefs : blockDefs b = [])
    {rq : Nat} (hq : rq < g.re) (hdq : ¬ Defd g.blocks rq) (hkq : HoonMap.get g.cond rq = Option.none) :
    IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 g.bo)) (g.emitted b) := by
  have I0 : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g.bo)) (g.emitted b) :=
    il_emitGoal' (R := g.re) hI (Nat.le_refl _) hp hbat hin (fun r hr => by rw [hdefs] at hr; cases hr)
      (fun r hr => hr.elim) trivial
  exact il_lazyReg_after (goal := CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g.bo)) I0
    (frL_iff.mpr (DF.refl _ _)) hq (fun h => hdq ((defd_emitted_nil hI.ats hdefs).mp h)) hkq
    (fun h => (gregL_ofSure.mp h).elim) I0.goal.1

/-- **The `%eqq` block for a `%pick` goal**, with old registers. -/
theorem oph_eqq {K : Nat → Nat → Prop} {z o : Jmp} {g g' : Comp.Gen Map} {rp rq o' : Nat}
    (hI : IL K (CGoalL.pick z o : CGoalL S) g) (hp : rp < g.re) (hq : rq < g.re) (hne : rp ≠ rq)
    (hdp : ¬ Defd g.blocks rp) (hdq : ¬ Defd g.blocks rq) (hkp : HoonMap.get g.cond rp = Option.none)
    (hkq : HoonMap.get g.cond rq = Option.none)
    (h : (emit ⟨[], [], Termin.eqq rp rq z o⟩ : CM Map Nat) g = some (o', g')) :
    OPh K (CGoalL.pick z o : CGoalL S) g g' rp rq o' := by
  rw [emit_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  have hdefs : blockDefs (⟨[], [], Termin.eqq rp rq z o⟩ : Blob) = [] := by simp [blockDefs]
  have up : unproxy g.cond rp = rp := Raw.unproxy_none hkp
  have uq : unproxy g.cond rq = rq := Raw.unproxy_none hkq
  have hin : BlobIn (· < g.re) (⟨[], [], Termin.eqq rp rq z o⟩ : Blob) :=
    ⟨fun x hx => by simp at hx, RegsIn.nil _, ⟨hp, hq, jmpIn_nil az, jmpIn_nil ao⟩⟩
  refine ⟨il_old_at hI rfl (batc_fresh fun j hj => by
      simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hI.goal.1
      · exact hI.goal.2)
    hin hdefs hq hdq hkq,
    fun r hr hl => ?_, hp, fun h => hdp ((defd_emitted_nil hI.ats hdefs).mp h), hkp⟩
  refine liveC_emitX hI _ _ (· = rp) (fun y hy hn hx => ?_) (fun j hj => ?_) r hr hl
  · obtain ⟨-, hy | ⟨-, hy⟩⟩ := hy
    · simp [renBlob, OpsRF] at hy
    · have e : y = rp ∨ y = rq := by
        simpa [renBlob, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao, up, uq, az, ao] using hy
      rcases e with e | e
      · exact (hx e).elim
      · exact (hn e).elim
  · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
      or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨hI.lab hbz, fun r hl _ _ _ => Or.inl hl⟩
    · exact ⟨hI.lab hbo, fun r hl _ _ _ => Or.inr hl⟩

/-- **The `[equ rp rq]` hop for a none-equivalent `%next` goal.** -/
theorem oph_equ {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g g' : Comp.Gen Map} {rp rq o' : Nat}
    (hI : IL K (CGoalL.next laz th) g) (hn : noneEquivalentL laz = true) (ha : th.args = [])
    (hp : rp < g.re) (hq : rq < g.re)
    (hdp : ¬ Defd g.blocks rp) (hdq : ¬ Defd g.blocks rq) (hkp : HoonMap.get g.cond rp = Option.none)
    (hkq : HoonMap.get g.cond rq = Option.none)
    (h : (emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩ : CM Map Nat) g = some (o', g')) :
    OPh K (CGoalL.next laz th) g g' rp rq o' := by
  rw [emit_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hF, -, -⟩ := (hI.goal : GoalL g (CGoalL.next laz th))
  obtain ⟨bt, hbt, -, -⟩ := hF
  have hdefs : blockDefs (⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩ : Blob) = [] := by
    simp [blockDefs, aliasDst]
  have up : unproxy g.cond rp = rp := Raw.unproxy_none hkp
  have uq : unproxy g.cond rq = rq := Raw.unproxy_none hkq
  have hin : BlobIn (· < g.re) (⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩ : Blob) := by
    refine ⟨fun x hx => by simp at hx, ?_, fun x hx => by simp [jmp0] at hx⟩
    intro q hq' x hx
    simp only [List.mem_singleton] at hq'
    subst hq'
    simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  refine ⟨il_old_at hI rfl (batc_fresh fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj
      subst hj; exact fresh_jmp0 hI.goal.1) hin hdefs hq hdq hkq,
    fun r hr hl => ?_, hp, fun h => hdp ((defd_emitted_nil hI.ats hdefs).mp h), hkp⟩
  refine liveC_emitX hI _ _ (· = rp) (fun y hy hn' hx => ?_) (fun j hj => ?_) r hr hl
  · obtain ⟨-, hy | ⟨-, hy⟩⟩ := hy
    · have e : y = rp ∨ y = rq := by
        simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, up, uq] using hy
      rcases e with e | e
      · exact (hx e).elim
      · exact (hn' e).elim
    · simp [renBlob, renFin, finRegs, jmpRegs, jmp0, renJmp] at hy
  · simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
    subst hj
    refine ⟨hI.lab hbt, fun r hl _ _ _ => ?_⟩
    exact hl.mono fun x z hk => hk.elim id fun hz => (lazK_none hn hz).elim

/-! ## `IL` of `second` across `p`'s run -/

/-- **The glue**: the goal `second` keeps `IL` across a run from it for
"`rp` at the same jump", when `rp` is not a register of `second`. -/
theorem il_glue {K K' : Nat → Nat → Prop} {second : Lazy S} {th : Jmp} {rp : Nat} {g5 g6 : Comp.Gen Map}
    {np : NextL S} (hI : IL K (CGoalL.next second th) g5) (hJ : IL K' np.goal g6) (hK : ∀ x y, K x y → K' x y)
    (hF : FrX (CGoalL.next (ofSure (lazyReg (S := S) rp)) th) g5 g6 np) (hKP : KP g5 g6)
    (hrs : ∀ y, LReg second y → y ≠ rp) : IL K (CGoalL.next second th) g6 := by
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

/-! ## `q`, `+past`, `p`, `+copy` -/

/-- **The tail of `%5`** from the goal "`rq` at `o`": `JL` of the result,
and a register live at its entry is not `rp` and is live for that goal. -/
theorem five_tail (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LR S Map env sup p) (ihq : LR S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {rp rq o : Nat} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3)
    (hrp : rp < g3.re) (hdp : ¬ Defd g3.blocks rp) (hkp : HoonMap.get g3.cond rp = Option.none) (hne : rp ≠ rq)
    (h1 : runLC env sup q (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region g3 = some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLC env sup p (CGoalL.next (ofSure (lazyReg (S := S) rp)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      r ≠ rp ∧ GLiveKL (unpM g3) K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) r := by
  obtain ⟨Jq, Lq⟩ := ihq K _ region g3 g4 nq hI h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := frameRun_plain env q hq sup _ region g3 g4 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (labRun_plain (S := S) (Map := Map) env q hq sup
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
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' h3
  have Fp := frameRun_plain env p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRun_plain (S := S) (Map := Map) env p hp sup
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

/-! ## The arm -/

/-- The state after `re`: the same but `re`. -/
theorem re_state {g g' : Comp.Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    r = g.re ∧ g'.re = g.re + 1 ∧ g'.blocks = g.blocks ∧ g'.cond = g.cond ∧ g'.bo = g.bo ∧ g'.drop = g.drop := by
  rw [re_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The arm `%5`, both halves**, from `LR` of its parts. -/
theorem liveRun_n5 (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LR S Map env sup p) (ihq : LR S Map env sup q) : LR S Map env sup (Nomm.n5 p q) := by
  intro K goal region g0 g1 nex hI h
  simp only [runLC] at h
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
  obtain ⟨J, L⟩ := five_tail env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have := O2 r hr hg
  rw [hU] at this
  exact this

/-- `ArmsL` with the field `n5` filled: the three fields left. -/
theorem armsL_n5 (env : CallEnv) :
    ∀ sup p q, PlainN p → PlainN q → LR S Map env sup p → LR S Map env sup q →
      LR S Map env sup (Nomm.n5 p q) :=
  fun sup _ _ hp hq ihp ihq => liveRun_n5 env sup hp hq ihp ihq

end Raw
end SkaModel
end Formalization
