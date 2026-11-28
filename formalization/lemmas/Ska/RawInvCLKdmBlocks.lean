import lemmas.Ska.RawInvCLKdmLoopSpec

/-!
# The call blocks of a direct call (`monoBlocks`): `KdmMonoSpec` from the loop

README Gaps 14 (b), track D (fork `kmb`).  `KdmMonoSpec` (`RawInvCLCallDM.lean`)
from `KmlLoopSpec` (`RawInvCLKdmLoopSpec.lean`, the loop of `+mono-try-call`).

* `kmb_il_done`, `kmb_il_emit`, `kmb_il_pick`, `kmb_il_bunt`: `IL` with no
  goal (`%done`) as the state part, kept by an `+emit` of a block whose
  registers are below `re` and whose definitions are no key; with two
  `Fresh` targets it is `IL` of `%pick`, and of "nothing at" one of them.
* `kmb_done`: the blocks `opt` `[%jmp b sub-v]` and `pes` `[%jsp b sub-pes]`
  under `%done`: `IL` of "`opt` or `pes`", a register live at `opt` is in
  the callee's need, one live at `pes` is `sub-pes`.
* `kmbRest`, `kmb_rest`: the same for the other goals: `+simple-next`,
  `+kerf`, the blocks `merge` (with a parameter), `opt` (`%cal`) and `pes`
  (`%csl`): a register live at `opt` is in the need or one the goal may
  leave live, one live at `pes` is `sub-pes` or one the goal may leave live.
* **`kmb_monoSpec_of`**: `KdmMonoSpec` from `KmlLoopSpec`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Small facts -/

theorem kmb_mem_flatten : ∀ (n : Need) (y : Nat), y ∈ flattenNeed n → NMem n y
  | Need.none, y, h => by simp [flattenNeed] at h
  | Need.this r, y, h => by simp only [flattenNeed, List.mem_singleton] at h; exact h
  | Need.pair p q, y, h => by
    simp only [flattenNeed, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (kmb_mem_flatten p y h)
    · exact Or.inr (kmb_mem_flatten q y h)
  | Need.both r p q, y, h => by
    simp only [flattenNeed, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (kmb_mem_flatten p y h))
    · exact Or.inr (Or.inr (kmb_mem_flatten q y h))

theorem kmb_flatten_mem : ∀ (n : Need) (y : Nat), NMem n y → y ∈ flattenNeed n
  | Need.none, y, h => h.elim
  | Need.this r, y, h => by simp only [flattenNeed, List.mem_singleton]; exact h
  | Need.pair p q, y, h => by
    simp only [flattenNeed, List.mem_append]
    rcases h with h | h
    · exact Or.inl (kmb_flatten_mem p y h)
    · exact Or.inr (kmb_flatten_mem q y h)
  | Need.both r p q, y, h => by
    simp only [flattenNeed, List.mem_cons, List.mem_append]
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (kmb_flatten_mem p y h))
    · exact Or.inr (Or.inr (kmb_flatten_mem q y h))

/-- A list of registers with no key is unchanged by `unproxy`. -/
theorem kmb_map_unproxy {cond : Map (Nat × List Nat)} {v : List Nat}
    (h : ∀ y ∈ v, HoonMap.get cond y = Option.none) : v.map (unproxy cond) = v := by
  calc v.map (unproxy cond) = v.map id := List.map_congr_left fun y hy => unproxy_none (h y hy)
    _ = v := List.map_id v

/-- The definitions after an `+emit`. -/
theorem kmb_defd_emit {g : Comp.Gen Map} {b : Blob} (A : ATS g) {r : Nat} :
    Defd (g.emitted b).blocks r ↔ Defd g.blocks r ∨ r ∈ blockDefs b := by
  have hd : g.drop = false := A.1
  show Defd (if g.drop then g.blocks else HoonMap.put g.blocks g.bo b) r ↔ _
  simp only [hd, Bool.false_eq_true, if_false]
  exact defd_put A.free

/-! ## `IL` with no goal -/

/-- The state part of `IL`. -/
theorem kmb_il_done {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K goal g) :
    IL K (CGoalL.done : CGoalL S) g := by
  refine ⟨h.ats, h.regs, fun k v hk => ?_, h.kvan, trivial⟩
  obtain ⟨k1, k2, -, k4, k5⟩ := h.cond k v hk
  exact ⟨k1, k2, fun h => h, k4, k5⟩

/-- **An `+emit` keeps the state part of `IL`.** -/
theorem kmb_il_emit {K : Nat → Nat → Prop} {g : Comp.Gen Map} {b : Blob} (hI : IL K (CGoalL.done : CGoalL S) g)
    (hbat : BATC g.blocks b) (hin : BlobIn (· < g.re) b)
    (hdef : ∀ r ∈ blockDefs b, HoonMap.get g.cond r = Option.none) :
    IL K (CGoalL.done : CGoalL S) (g.emitted b) := by
  have hd : g.drop = false := hI.ats.1
  obtain ⟨A1, -, hget⟩ := ats_emit hI.ats hbat
  refine ⟨A1, fun k b' hb' => ?_, fun k v hk => ?_, hI.kvan.mono (Nat.le_succ _), trivial⟩
  · rw [em_get hd] at hb'
    split at hb'
    · cases hb'; exact hin
    · exact hI.regs k b' hb'
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    refine ⟨k1, fun hdk => ?_, fun h => h, k4, k5⟩
    rcases (kmb_defd_emit hI.ats).mp hdk with h | h
    · exact k2 h
    · have e := hdef k h
      have hk' : HoonMap.get g.cond k = some v := hk
      rw [e] at hk'; cases hk'

/-- **`IL` of `%pick`** from the state part and two `Fresh` targets. -/
theorem kmb_il_pick {K : Nat → Nat → Prop} {g : Comp.Gen Map} {z o : Jmp} (hI : IL K (CGoalL.done : CGoalL S) g)
    (hz : Fresh g z) (ho : Fresh g o) : IL K (CGoalL.pick z o : CGoalL S) g := by
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, ⟨hz, ho⟩⟩
  obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
  exact ⟨k1, k2, fun h => h, k4, k5⟩

/-- **`IL` of "nothing at `z`"** from `IL` of "`z` or `o`". -/
theorem kmb_il_bunt {K : Nat → Nat → Prop} {g : Comp.Gen Map} {z o : Jmp} (hI : IL K (CGoalL.pick z o : CGoalL S) g) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) z) g := by
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, goalL_bunt (hI.goal : GoalL g (CGoalL.pick z o)).1⟩
  obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
  exact ⟨k1, k2, fun hg => lReg_bunt (gregL_next.mp hg), k4, k5⟩

/-- `Fresh` at a state with the same blocks. -/
theorem kmb_fresh_eq {g g' : Comp.Gen Map} {j : Jmp} (h : Fresh g j) (hb : g'.blocks = g.blocks) : Fresh g' j := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, hb ▸ h1, h2, h3⟩

/-- A block whose registers are no key is unchanged by `unproxy`. -/
theorem kmb_ren_self {cond : Map (Nat × List Nat)} {b : Blob} {R : Nat}
    (h : BlobIn (fun r => r < R ∧ HoonMap.get cond r = Option.none) b) : renBlob (unproxy cond) b = b :=
  (renBlob_congr (v := id) (fun x hx => Raw.unproxy_none hx.2) h).trans (renBlob_id b)

/-- The unproxied blocks of a state with the same blocks and `cond`. -/
theorem kmb_unpM_eq {g g' : Comp.Gen Map} (hb : g'.blocks = g.blocks) (hc : g'.cond = g.cond) : unpM g' = unpM g := by
  unfold unpM; rw [hb, hc]

/-- A register live at a known block. -/
theorem kmb_live_at {bl : Map Blob} {K : Nat → Nat → Prop} {k y : Nat} {b : Blob} (hb : HoonMap.get bl k = some b)
    (hl : LiveK bl K k y) : BlockRF b y ∨ ∃ j ∈ getJmps b.fin, LiveK bl K j.there y ∧ y ∉ blockDefs b := by
  cases hl with
  | here hb' hr _ => rw [hb] at hb'; cases hb'; exact Or.inl hr
  | next hb' hj hl hd _ => rw [hb] at hb'; cases hb'; exact Or.inr ⟨_, hj, hl, hd⟩

/-- **One `+emit`** of a block whose registers are below `re` and no key,
whose definitions are no key: the state part of `IL`, the block at the old
`bo`, the old blocks kept, the unproxied blocks, the definitions. -/
theorem kmb_emit {K : Nat → Nat → Prop} {g g' : Comp.Gen Map} {b : Blob} {o : Nat}
    (hI : IL K (CGoalL.done : CGoalL S) g) (hbat : BATC g.blocks b)
    (hin : BlobIn (fun r => r < g.re ∧ HoonMap.get g.cond r = Option.none) b)
    (hdef : ∀ r ∈ blockDefs b, HoonMap.get g.cond r = Option.none)
    (h : (emit b : CM Map Nat) g = some (o, g')) :
    o = g.bo ∧ IL K (CGoalL.done : CGoalL S) g' ∧ HoonMap.get g'.blocks g.bo = some b ∧ KP g g' ∧
    (∀ k, k ≠ g.bo → HoonMap.get (unpM g') k = HoonMap.get (unpM g) k) ∧
    HoonMap.get (unpM g') g.bo = some b ∧
    g'.re = g.re ∧ g'.cond = g.cond ∧ g'.bo = g.bo + 1 ∧
    (∀ r, Defd g'.blocks r ↔ Defd g.blocks r ∨ r ∈ blockDefs b) := by
  rw [emit_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hd : g.drop = false := hI.ats.1
  obtain ⟨-, KP1, hget⟩ := ats_emit hI.ats hbat
  refine ⟨rfl, kmb_il_emit hI hbat (hin.mono fun _ h => h.1) hdef, hget, KP1,
    fun k hk => unpM_emitted_ne hd b hk, ?_, rfl, rfl, rfl, fun r => kmb_defd_emit hI.ats⟩
  rw [unpM_emitted_self hd, kmb_ren_self hin]

/-! ## The end: the loop -/

/-- **From the blocks `opt`, `pes` to the result**, by the loop's spec. -/
theorem kmb_finish (hL : KmlLoopSpec S Map) {K : Nat → Nat → Prop} {subNed : Need} {gi g2 : Comp.Gen Map}
    {sp opt pes o' : Nat} {X : Nat → Prop}
    (hI : IL K (CGoalL.pick (jmp0 opt) (jmp0 pes) : CGoalL S) gi) (hD : Distinct subNed)
    (hN : ∀ y, NMem subNed y → y < gi.re ∧ ¬ Defd gi.blocks y ∧ HoonMap.get gi.cond y = Option.none)
    (hs : sp < gi.re) (hds : ¬ Defd gi.blocks sp) (hks : HoonMap.get gi.cond sp = Option.none)
    (hns : ¬ NMem subNed sp)
    (hopt : ∀ y, LiveK (unpM gi) K opt y → NMem subNed y ∨ X y)
    (hpes : ∀ y, LiveK (unpM gi) K pes y → y = sp ∨ X y)
    (h : (monoTryCall subNed opt sp pes : CM Map Nat) gi = some (o', g2)) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 o')) g2 ∧
    (∀ r, r ≠ sp → GLiveKL (unpM g2) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 o')) r → X r) ∧
    sp < g2.re ∧ ¬ Defd g2.blocks sp ∧ HoonMap.get g2.cond sp = Option.none := by
  have h' : (monoTryLoop pes subNed sp opt : CM Map Nat) gi = some (o', g2) := h
  obtain ⟨I2, L2⟩ := hL K pes subNed sp opt gi g2 o' hI hD hN hs hds hks hns h'
  refine ⟨kmb_il_bunt I2, fun r hr hl => ?_, ?_⟩
  · have hl' : LiveK (unpM g2) K o' r := LiveK.mono (fun x y h => Or.inl h) hl
    rcases L2 r hl' with e | ⟨h1, h2⟩ | h3
    · exact absurd e hr
    · rcases hopt r h1 with e | e
      · exact absurd e h2
      · exact e
    · rcases hpes r h3 with e | e
      · exact absurd e hr
      · exact e
  · have d := kdl_df_monoTryLoop pes subNed sp opt gi g2 o' h'
    exact df_keep d hs (fun h => h.elim (fun h => by omega) hns) hds hks

/-! ## Under `%done` -/

/-- **The call blocks under `%done`**: the result, nothing the goal may
leave live. -/
theorem kmb_done (hL : KmlLoopSpec S Map) {K : Nat → Nat → Prop} {b : Bell} {subNed : Need} {g1 g2 : Comp.Gen Map}
    {x : Nat × Nat} (hI : IL K (CGoalL.done : CGoalL S) g1) (hD : Distinct subNed)
    (hN : ∀ y, NMem subNed y → y < g1.re ∧ ¬ Defd g1.blocks y ∧ HoonMap.get g1.cond y = Option.none)
    (h : (monoBlocks b subNed (CGoalL.done : CGoalL S) : CM Map (Nat × Nat)) g1 = some (x, g2)) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 x.2)) g2 ∧
    (∀ r, r ≠ x.1 → GLiveKL (unpM g2) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 x.2)) r → False) ∧
    x.1 < g2.re ∧ ¬ Defd g2.blocks x.1 ∧ HoonMap.get g2.cond x.1 = Option.none := by
  simp only [monoBlocks] at h
  obtain ⟨sp, gc, hc, h⟩ := bind_some h
  obtain ⟨esp, rc, bc, cc, oc, dc⟩ := re_state hc
  have Ic : IL K (CGoalL.done : CGoalL S) gc := il_re_up hI (by omega) bc cc oc dc
  have hkn : ∀ y, NMem subNed y → y < gc.re ∧ HoonMap.get gc.cond y = Option.none := fun y hy =>
    ⟨by have := (hN y hy).1; omega, by rw [cc]; exact (hN y hy).2.2⟩
  have hks : HoonMap.get gc.cond sp = Option.none := by rw [cc, esp]; exact hI.cond_ge (Nat.le_refl _)
  obtain ⟨opt, gd, hd, h⟩ := bind_some h
  obtain ⟨eo, Id, gdo, KPd, Ud, Sd, rd, cd, bod, Dd⟩ := kmb_emit Ic
    (by refine batc_fresh fun j hj => ?_; simp [finJumps] at hj)
    (by
      refine ⟨fun y hy => by simp at hy, fun p hp => by simp at hp, ?_⟩
      intro y hy
      exact hkn y (kmb_mem_flatten _ _ hy))
    (fun r hr => by simp [blockDefs] at hr) hd
  obtain ⟨pes, ge, he, h⟩ := bind_some h
  obtain ⟨ep, Ie, gep, KPe, Ue, Se, re, ce, boe, De⟩ := kmb_emit Id
    (by refine batc_fresh fun j hj => ?_; simp [finJumps] at hj)
    (by
      refine ⟨fun y hy => by simp at hy, fun p hp => by simp at hp, ?_⟩
      show sp < gd.re ∧ HoonMap.get gd.cond sp = Option.none
      rw [rd, cd]; exact ⟨by omega, hks⟩)
    (fun r hr => by simp [blockDefs] at hr) he
  obtain ⟨o', g', hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst eo ep
  have hfo : Fresh ge (jmp0 gc.bo) := fresh_kp ⟨_, gdo, rfl, rfl⟩ KPe
  have hfp : Fresh ge (jmp0 gd.bo) := ⟨_, gep, rfl, rfl⟩
  have Ip := kmb_il_pick Ie hfo hfp
  have hUo : HoonMap.get (unpM ge) gc.bo = some ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ := by
    rw [Ue _ (by omega), Sd]
  have hdc : ∀ y, Defd ge.blocks y → Defd g1.blocks y := fun y hy => by
    rcases (De y).mp hy with hy | hy
    · rcases (Dd y).mp hy with hy | hy
      · rw [bc] at hy; exact hy
      · simp [blockDefs] at hy
    · simp [blockDefs] at hy
  refine kmb_finish (X := fun _ => False) hL Ip hD (fun y hy => ⟨?_, fun hd => (hN y hy).2.1 (hdc y hd), ?_⟩)
    (by rw [re, rd]; omega) (fun hd => ?_) (by rw [ce, cd]; exact hks) (fun hy => ?_) (fun y hl => ?_)
    (fun y hl => ?_) hl
  · rw [re, rd]; have := (hN y hy).1; omega
  · rw [ce, cd, cc]; exact (hN y hy).2.2
  · have := defd_lt hI.regs (hdc sp hd); omega
  · have := (hN sp hy).1; omega
  · rcases kmb_live_at hUo hl with ⟨-, hr | ⟨-, hr⟩⟩ | ⟨j, hj, -⟩
    · exact hr.elim
    · exact Or.inl (kmb_mem_flatten _ _ hr)
    · simp [getJmps] at hj
  · rcases kmb_live_at Se hl with ⟨-, hr | ⟨-, hr⟩⟩ | ⟨j, hj, -⟩
    · exact hr.elim
    · simp only [finRegs, List.mem_singleton] at hr; exact Or.inl hr
    · simp [getJmps] at hj

/-! ## Under `%next` and `%pick` -/

/-- **The call blocks under a goal other than `%done`** (the second branch
of `monoBlocks`). -/
def kmbRest (b : Bell) (subNed : Need) (goal : CGoalL S) : CM Map (Nat × Nat) := do
  let nex ← simpleNextL goal
  let (out, pro) ← kerf nex
  let merged ← re
  let subPes ← re
  let merge ← emit ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩
  let proOpt ← re
  let proPes ← re
  let opt ← emit ⟨[], [Pole.cal b (flattenNeed subNed) proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
  let pes ← emit ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], merge⟩⟩
  let o ← monoTryCall subNed opt subPes pes
  pure (subPes, o)

theorem kmb_rest_next (b : Bell) (subNed : Need) (laz : Lazy S) (th : Jmp) :
    (monoBlocks b subNed (CGoalL.next laz th) : CM Map (Nat × Nat)) = kmbRest b subNed (CGoalL.next laz th) := rfl

theorem kmb_rest_pick (b : Bell) (subNed : Need) (z o : Jmp) :
    (monoBlocks b subNed (CGoalL.pick z o : CGoalL S) : CM Map (Nat × Nat)) =
      kmbRest b subNed (CGoalL.pick z o : CGoalL S) := rfl

/-- **The call blocks under a goal other than `%done`**: the result, and a
register other than `sub-pes` live at its entry is one the goal may leave
live. -/
theorem kmb_rest (hL : KmlLoopSpec S Map) {K : Nat → Nat → Prop} {b : Bell} {subNed : Need} {goal : CGoalL S}
    {g1 g2 : Comp.Gen Map} {x : Nat × Nat} (hI : IL K goal g1) (hD : Distinct subNed)
    (hN : ∀ y, NMem subNed y → y < g1.re ∧ ¬ Defd g1.blocks y ∧ HoonMap.get g1.cond y = Option.none ∧
      ¬ GRegL goal y)
    (h : (kmbRest b subNed goal : CM Map (Nat × Nat)) g1 = some (x, g2)) :
    IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 x.2)) g2 ∧
    (∀ r, r ≠ x.1 → GLiveKL (unpM g2) K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 x.2)) r →
      GLiveKL (unpM g1) K goal r) ∧
    x.1 < g2.re ∧ ¬ Defd g2.blocks x.1 ∧ HoonMap.get g2.cond x.1 = Option.none := by
  unfold kmbRest at h
  obtain ⟨nx, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, gb, hb, h⟩ := bind_some h
  have Ia : IL K nx.goal ga := il_simpleNextL hI ha
  have La : LiveC K goal g1 ga nx := liveC_simpleNextL hI ha
  obtain ⟨Ib, Lb⟩ := kerfSpecL K nx ga gb out pro Ia hb
  have L1 : LiveC K goal g1 gb ⟨ofSure (lazyReg (S := S) pro), jmp0 out⟩ := La.trans Lb
  obtain ⟨Fa, Ga⟩ := frame_simpleNextL ha
  obtain ⟨Fb, Pb⟩ := frame_kerf hb
  obtain ⟨hpl, hkp⟩ := Ib.entry_regs (o := out) _ List.mem_cons_self pro rfl
  have r1 : g1.re ≤ ga.re := Fa.1
  have r2 : ga.re ≤ gb.re := Fb.1
  have I0 : IL K (CGoalL.done : CGoalL S) gb := kmb_il_done Ib
  obtain ⟨⟨bt, hbt, -, -⟩, -, -⟩ := (Ib.goal : GoalL gb (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)))
  have hob : out < gb.bo := Ib.lab hbt
  -- the need's registers at `gb`
  have hNb : ∀ y, NMem subNed y → ¬ Defd gb.blocks y ∧ HoonMap.get gb.cond y = Option.none ∧ y ≠ pro := by
    intro y hy
    obtain ⟨y1, y2, y3, y4⟩ := hN y hy
    have hlr : ¬ LReg nx.laz y := fun hl => by
      rcases Ga y (gregL_goal.mpr hl) with e | e
      · exact y4 e
      · omega
    refine ⟨fun hd => ?_, ?_, fun e => ?_⟩
    · rcases Fb.2.2 y hd with hd | hd | hd
      · rcases Fa.2.2 y hd with hd | hd
        · exact y2 hd
        · exact hd
      · omega
      · exact hlr hd
    · cases e : HoonMap.get gb.cond y with
      | none => rfl
      | some v =>
        rcases Fb.2.1 y v e with e' | e'
        · rcases Fa.2.1 y v e' with e'' | e''
          · rw [y3] at e''; cases e''
          · omega
        · omega
    · subst e
      rcases Pb with e | e
      · omega
      · exact hlr e
  -- `merged`, `sub-pes`
  obtain ⟨mg, gc, hc, h⟩ := bind_some h
  obtain ⟨emg, rc, bc, cc, oc, dc⟩ := re_state hc
  obtain ⟨sp, gd, hd, h⟩ := bind_some h
  obtain ⟨esp, rd, bd, cd, od, dd⟩ := re_state hd
  have Id : IL K (CGoalL.done : CGoalL S) gd :=
    il_re_up I0 (by omega) (bd.trans bc) (cd.trans cc) (od.trans oc) (dd.trans dc)
  have hcd : gd.cond = gb.cond := cd.trans cc
  have hfo : Fresh gd (jmp0 out) := kmb_fresh_eq (Ib.goal : GoalL gb (CGoalL.next (ofSure (lazyReg (S := S) pro))
    (jmp0 out))).1 (bd.trans bc)
  have hkg : ∀ y, gb.re ≤ y → HoonMap.get gb.cond y = Option.none := fun y hy => I0.cond_ge hy
  -- `merge`
  obtain ⟨om, ge, he, h⟩ := bind_some h
  obtain ⟨eom, Ie, gem, KPe, Ue, Se, rce, ce, boe, De⟩ := kmb_emit Id
    (by
      refine batc_fresh fun j hj => ?_
      simp only [finJumps, List.mem_singleton] at hj
      subst hj; exact hfo)
    (by
      refine ⟨fun y hy => ?_, fun p hp y hy => ?_, jmpIn_jmp0 _ _⟩
      · simp only [List.mem_singleton] at hy
        subst hy; rw [hcd]; exact ⟨by omega, hkg _ (by omega)⟩
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · rw [hcd]; exact ⟨by omega, hkg _ (by omega)⟩
        · rw [hcd]; exact ⟨by omega, hkp⟩)
    (by
      intro r hr
      simp only [blockDefs, List.filterMap, aliasDst, List.mem_append, List.mem_singleton,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcd]; exact hkg _ (by omega)
      · rw [hcd]; exact hkp) he
  subst eom
  -- `pro-opt`, `pro-pes`
  obtain ⟨po, gf, hf, h⟩ := bind_some h
  obtain ⟨epo, rf, bf, cf, of, df⟩ := re_state hf
  obtain ⟨pp, gg, hg, h⟩ := bind_some h
  obtain ⟨epp, rg, bg, cg, og, dg⟩ := re_state hg
  have Ig : IL K (CGoalL.done : CGoalL S) gg :=
    il_re_up Ie (by omega) (bg.trans bf) (cg.trans cf) (og.trans of) (dg.trans df)
  have hcg : gg.cond = gb.cond := (cg.trans cf).trans (ce.trans hcd)
  have hpar : HasPar gd.bo [mg] gg := ⟨_, by rw [bg, bf]; exact gem, rfl⟩
  -- `opt`
  obtain ⟨opt, gh, hh, h⟩ := bind_some h
  obtain ⟨eopt, Ih, ghm, KPh, Uh, Sh, rch, ch, boh, Dh⟩ := kmb_emit Ig (kdl_batc1 hpar)
    (by
      refine ⟨fun y hy => by simp at hy, fun p hp y hy => ?_, fun y hy => ?_⟩
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only [Comp.poleRegs, List.mem_cons] at hy
        rcases hy with rfl | hy
        · rw [hcg]; exact ⟨by omega, hkg _ (by omega)⟩
        · have hy' := kmb_mem_flatten _ _ hy
          rw [hcg]; exact ⟨by have := (hN y hy').1; omega, (hNb y hy').2.1⟩
      · simp only [List.mem_singleton, Option.some.injEq] at hy
        subst hy; rw [hcg]; exact ⟨by omega, hkg _ (by omega)⟩)
    (by
      intro r hr
      simp only [blockDefs, List.filterMap, aliasDst, List.mem_append, List.mem_singleton,
        List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at hr
      subst hr; rw [hcg]; exact hkg _ (by omega)) hh
  subst eopt
  -- `pes`
  obtain ⟨pes, gi, hi, h⟩ := bind_some h
  have hpar' : HasPar gd.bo [mg] gh := stab_hasPar _ _ gg gh KPh hpar
  have hch : gh.cond = gb.cond := ch.trans hcg
  obtain ⟨epes, Ii, gim, KPi, Ui, Si, rci, ci, boi, Di⟩ := kmb_emit Ih (kdl_batc1 hpar')
    (by
      refine ⟨fun y hy => by simp at hy, fun p hp y hy => ?_, fun y hy => ?_⟩
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · rw [hch]; exact ⟨by omega, hkg _ (by omega)⟩
        · rw [hch]; exact ⟨by omega, hkg _ (by omega)⟩
      · simp only [List.mem_singleton, Option.some.injEq] at hy
        subst hy; rw [hch]; exact ⟨by omega, hkg _ (by omega)⟩)
    (by
      intro r hr
      simp only [blockDefs, List.filterMap, aliasDst, List.mem_append, List.mem_singleton,
        List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at hr
      subst hr; rw [hch]; exact hkg _ (by omega)) hi
  subst epes
  -- the loop
  obtain ⟨o', g', hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hci : gi.cond = gb.cond := ci.trans hch
  have hfo' : Fresh gi (jmp0 gg.bo) := fresh_kp ⟨_, ghm, rfl, rfl⟩ KPi
  have hfp' : Fresh gi (jmp0 gh.bo) := ⟨_, gim, rfl, rfl⟩
  have Ip := kmb_il_pick Ii hfo' hfp'
  -- the definitions at `gi`
  have hDi : ∀ y, Defd gi.blocks y → Defd gb.blocks y ∨ y = mg ∨ y = pro ∨ y = po ∨ y = pp := by
    intro y hy
    rcases (Di y).mp hy with hy | hy
    · rcases (Dh y).mp hy with hy | hy
      · rw [bg, bf] at hy
        rcases (De y).mp hy with hy | hy
        · rw [bd, bc] at hy; exact Or.inl hy
        · simp only [blockDefs, List.filterMap, aliasDst, List.mem_append, List.mem_singleton,
            List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with hy | hy
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr (Or.inl hy))
      · simp only [blockDefs, List.filterMap, aliasDst, List.mem_append, List.mem_singleton,
          List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at hy
        exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · simp only [blockDefs, List.filterMap, aliasDst, List.mem_append, List.mem_singleton,
        List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at hy
      exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
  -- the unproxied blocks
  have hUge : unpM gg = unpM ge := kmb_unpM_eq (bg.trans bf) (cg.trans cf)
  have hUgd : unpM gd = unpM gb := kmb_unpM_eq (bd.trans bc) hcd
  have hUb : ∀ k, k < gb.bo → HoonMap.get (unpM gi) k = HoonMap.get (unpM gb) k := by
    intro k hk
    rw [Ui _ (by omega), Uh _ (by omega), hUge, Ue _ (by omega), hUgd]
  have hUm : HoonMap.get (unpM gi) gd.bo = some ⟨[mg], [Pole.mov mg pro], Termin.hop (jmp0 out)⟩ := by
    rw [Ui _ (by omega), Uh _ (by omega), hUge, Se]
  have hUo : HoonMap.get (unpM gi) gg.bo =
      some ⟨[], [Pole.cal b (flattenNeed subNed) po], Termin.hop ⟨[some po], gd.bo⟩⟩ := by
    rw [Ui _ (by omega), Sh]
  -- liveness at `out`, `merge`, `opt`, `pes`
  have Lout : ∀ y, y ≠ pro → LiveK (unpM gi) K out y → GLiveKL (unpM g1) K goal y := by
    intro y hy hl
    have h1 : LiveK (unpM gb) K out y := (liveK_frameP Ib.downU hUb hob).mp hl
    exact L1 y (h1.mono_r fun x hx => hx.elim id fun hz => (hy (lazK_ofSure.mp hz).2).elim)
  have hmp : mg ≠ pro := by omega
  have Lm : ∀ y, LiveK (unpM gi) K gd.bo y → GLiveKL (unpM g1) K goal y := by
    intro y hl
    rcases kmb_live_at hUm hl with ⟨hnp, hr⟩ | ⟨j, hj, hl', hnd⟩
    · exfalso
      simp only [List.mem_singleton] at hnp
      rcases hr with hr | ⟨-, hr⟩
      · simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, hmp] at hr
        exact hnp hr
      · simp [finRegs, jmpRegs, jmp0] at hr
    · simp only [getJmps, List.mem_singleton] at hj
      subst hj
      refine Lout y (fun e => hnd ?_) hl'
      simp [blockDefs, aliasDst, e]
  have Lopt : ∀ y, LiveK (unpM gi) K gg.bo y → NMem subNed y ∨ GLiveKL (unpM g1) K goal y := by
    intro y hl
    rcases kmb_live_at hUo hl with ⟨-, hr⟩ | ⟨j, hj, hl', -⟩
    · rcases hr with hr | ⟨hd, hr⟩
      · simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs] at hr
        exact Or.inl (kmb_mem_flatten _ _ hr)
      · simp [finRegs, jmpRegs, defsOf, aliasDst] at hr hd
        exact absurd hr hd
    · simp only [getJmps, List.mem_singleton] at hj
      subst hj
      exact Or.inr (Lm y hl')
  have hsp' : sp ≠ pp := by omega
  have Lpes : ∀ y, LiveK (unpM gi) K gh.bo y → y = sp ∨ GLiveKL (unpM g1) K goal y := by
    intro y hl
    rcases kmb_live_at Si hl with ⟨-, hr⟩ | ⟨j, hj, hl', -⟩
    · rcases hr with hr | ⟨hd, hr⟩
      · simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, hsp'] at hr
        exact Or.inl hr
      · simp [finRegs, jmpRegs, defsOf, aliasDst] at hr hd
        exact absurd hr hd
    · simp only [getJmps, List.mem_singleton] at hj
      subst hj
      exact Or.inr (Lm y hl')
  refine kmb_finish hL Ip hD (fun y hy => ⟨?_, fun hd => ?_, ?_⟩) (by omega) (fun hd => ?_)
    (by rw [hci]; exact hkg _ (by omega)) (fun hy => ?_) Lopt Lpes hl
  · have := (hN y hy).1; omega
  · have := (hN y hy).1
    rcases hDi y hd with hd | e | e | e | e
    · exact (hNb y hy).1 hd
    · omega
    · exact (hNb y hy).2.2 e
    · omega
    · omega
  · rw [hci]; exact (hNb y hy).2.1
  · rcases hDi sp hd with hd | e | e | e | e
    · have := defd_lt I0.regs hd; omega
    · omega
    · omega
    · omega
    · omega
  · have := (hN sp hy).1; omega

/-! ## The spec -/

/-- **`KdmMonoSpec` from the spec of the loop of `+mono-try-call`.** -/
theorem kmb_monoSpec_of (hL : KmlLoopSpec S Map) : KdmMonoSpec S Map := by
  intro K goal bNed b g0 g1 g2 subNed x hI h1 h2
  obtain ⟨⟨k, rfl⟩, hle, hD, hm⟩ := needOrdAllocRegs_spec bNed g0 _ subNed h1
  have I1 : IL K goal { g0 with re := k } := il_re_up hI hle rfl rfl rfl rfl
  have hN : ∀ y, NMem subNed y → y < ({ g0 with re := k } : Comp.Gen Map).re ∧
      ¬ Defd ({ g0 with re := k } : Comp.Gen Map).blocks y ∧
      HoonMap.get ({ g0 with re := k } : Comp.Gen Map).cond y = Option.none ∧ ¬ GRegL goal y := by
    intro y hy
    obtain ⟨y1, y2⟩ := hm y hy
    refine ⟨y2, fun hd => ?_, hI.cond_ge y1, fun hg => ?_⟩
    · have := defd_lt hI.regs hd; omega
    · have := (hI.greg_lt hg).1; omega
  have hU : unpM ({ g0 with re := k } : Comp.Gen Map) = unpM g0 := kmb_unpM_eq rfl rfl
  cases goal with
  | done =>
    obtain ⟨O1, O2, O3⟩ := kmb_done hL I1 hD (fun y hy => ⟨(hN y hy).1, (hN y hy).2.1, (hN y hy).2.2.1⟩) h2
    exact ⟨O1, fun r hr hl => (O2 r hr hl).elim, O3⟩
  | next laz th =>
    rw [kmb_rest_next] at h2
    obtain ⟨O1, O2, O3⟩ := kmb_rest hL I1 hD hN h2
    exact ⟨O1, fun r hr hl => hU ▸ O2 r hr hl, O3⟩
  | pick z o =>
    rw [kmb_rest_pick] at h2
    obtain ⟨O1, O2, O3⟩ := kmb_rest hL I1 hD hN h2
    exact ⟨O1, fun r hr hl => hU ▸ O2 r hr hl, O3⟩

end Raw
end SkaModel
end Formalization
