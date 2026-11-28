import lemmas.Ska.RawInvCLKdmLoopSpec

/-!
# The loop of `+mono-try-call`: `IL` and liveness (`KmlLoopSpec`)

README Gaps 14 (b), track D (fork `kml`).  **`kml_loop : KmlLoopSpec S Map`**
(`RawInvCLKdmLoopSpec.lean`): a run of `monoTryLoop fail ned r o` from a
state where "`o` or `fail`" holds `IL` ends at a block `o'` where "`o'` or
`fail`" holds `IL`, and a register live at `o'` is `r`, or live at `o` and
not in `ned`, or live at `fail`.

* `KmlKeep`: same `drop` and `cond`, `bo` grows, the blocks below the old
  `bo` unchanged (`kml_keep_re`, `kml_keep_emit`, `kml_keep_loop`);
  `kml_live_frame`: liveness at an old label is then unchanged.
* `kml_il_emit`: a block emitted with no parameter, registers below `re`,
  definitions no keys and `Fresh` jumps keeps `IL` of "the new block or
  `fail`".
* `kml_hop`: the block `[A] %hop o` (a `mov`, or the split ops);
  `kml_clq`: the block `%clq r os fail`.
* `kml_loopN`: the induction on the need.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The frame -/

/-- Same `drop` and `cond`, `bo` grows, the blocks below the old `bo`
unchanged. -/
def KmlKeep (g g' : Comp.Gen Map) : Prop :=
  g'.drop = g.drop ∧ g'.cond = g.cond ∧ g.bo ≤ g'.bo ∧
    ∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k

theorem kml_keep_refl (g : Comp.Gen Map) : KmlKeep g g := ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem kml_keep_trans {a b c : Comp.Gen Map} (h1 : KmlKeep a b) (h2 : KmlKeep b c) : KmlKeep a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, Nat.le_trans h1.2.2.1 h2.2.2.1, fun k hk =>
    (h2.2.2.2 k (Nat.lt_of_lt_of_le hk h1.2.2.1)).trans (h1.2.2.2 k hk)⟩

theorem kml_keep_re {g g' : Comp.Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    KmlKeep g g' := by
  obtain ⟨-, -, hb, hc, hbo, hd⟩ := re_state h
  exact ⟨hd, hc, by omega, fun k _ => by rw [hb]⟩

theorem kml_keep_emit (g : Comp.Gen Map) (b : Blob) : KmlKeep g (g.emitted b) := by
  refine ⟨rfl, rfl, Nat.le_succ _, fun k hk => ?_⟩
  simp only [Gen.emitted]
  cases g.drop
  · simp only [Bool.false_eq_true, if_false]
    exact get_put_ne (Nat.ne_of_lt hk)
  · rfl

theorem kml_keep_loop (fail : Nat) : ∀ (ned : Need) (r o : Nat) (g g' : Comp.Gen Map) (x : Nat),
    (monoTryLoop fail ned r o : CM Map Nat) g = some (x, g') → KmlKeep g g'
  | Need.none, r, o, g, g', x, h => by
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact kml_keep_refl _
  | Need.this rn, r, o, g, g', x, h => by
    simp only [monoTryLoop] at h
    split at h
    · cases h
    · rw [emit_apply] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact kml_keep_emit _ _
  | Need.pair hn tn, r, o, g, g', x, h => by
    simp only [monoTryLoop] at h
    obtain ⟨rt, g1, h1, h⟩ := bind_some h
    obtain ⟨rh, g2, h2, h⟩ := bind_some h
    obtain ⟨ot, g3, h3, h⟩ := bind_some h
    obtain ⟨oh, g4, h4, h⟩ := bind_some h
    obtain ⟨os, g5, h5, h⟩ := bind_some h
    rw [emit_apply] at h5 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h5 h
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨rfl, rfl⟩ := h
    exact kml_keep_trans (kml_keep_re h1) (kml_keep_trans (kml_keep_re h2) (kml_keep_trans
      (kml_keep_loop fail tn rt o g2 g3 ot h3) (kml_keep_trans (kml_keep_loop fail hn rh ot g3 g4 oh h4)
      (kml_keep_trans (kml_keep_emit _ _) (kml_keep_emit _ _)))))
  | Need.both rn hn tn, r, o, g, g', x, h => by
    simp only [monoTryLoop] at h
    obtain ⟨rt, g1, h1, h⟩ := bind_some h
    obtain ⟨rh, g2, h2, h⟩ := bind_some h
    obtain ⟨ot, g3, h3, h⟩ := bind_some h
    obtain ⟨oh, g4, h4, h⟩ := bind_some h
    split at h
    · cases h
    obtain ⟨os, g5, h5, h⟩ := bind_some h
    rw [emit_apply] at h5 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h5 h
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨rfl, rfl⟩ := h
    exact kml_keep_trans (kml_keep_re h1) (kml_keep_trans (kml_keep_re h2) (kml_keep_trans
      (kml_keep_loop fail tn rt o g2 g3 ot h3) (kml_keep_trans (kml_keep_loop fail hn rh ot g3 g4 oh h4)
      (kml_keep_trans (kml_keep_emit _ _) (kml_keep_emit _ _)))))

/-- **Liveness at an old label is unchanged** by a step that keeps the old
blocks and `cond`. -/
theorem kml_live_frame {K : Nat → Nat → Prop} {goal : CGoalL S} {g g' : Comp.Gen Map} (hI : IL K goal g)
    (hk : KmlKeep g g') {k y : Nat} (hl : k < g.bo) :
    LiveK (unpM g') K k y ↔ LiveK (unpM g) K k y :=
  liveK_frameP hI.downU (fun x hx => by
    unfold unpM
    rw [get_mapVals, get_mapVals, hk.2.1, hk.2.2.2 x hx]) hl

/-! ## One block -/

/-- **An emitted block keeps `IL` of "the new block or `fail`".** -/
theorem kml_il_emit {K : Nat → Nat → Prop} {o fail : Nat} {g : Comp.Gen Map}
    (hI : IL K (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S) g) {b : Blob} (hp : b.par = [])
    (hbat : BATC g.blocks b) (hin : BlobIn (· < g.re) b)
    (hdef : ∀ r ∈ blockDefs b, HoonMap.get g.cond r = Option.none) :
    IL K (CGoalL.pick (jmp0 g.bo) (jmp0 fail) : CGoalL S) (g.emitted b) := by
  have I : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g.bo)) (g.emitted b) :=
    il_emitGoal' (s := (Sure.bunt : Sure S)) hI (Nat.le_refl g.re) hp hbat hin hdef (fun r hr => hr.elim) trivial
  obtain ⟨-, KP1, -⟩ := ats_emit hI.ats hbat
  obtain ⟨-, hf⟩ := (hI.goal : GoalL g (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S))
  refine ⟨I.ats, I.regs, fun k v hk => ?_, I.kvan, ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := I.cond k v hk
    exact ⟨k1, k2, fun h => h, k4, k5⟩
  · exact ⟨(I.goal : GoalL (g.emitted b) (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g.bo))).1,
      fresh_kp hf KP1⟩

/-- **The block `[A] %hop oh`**: `IL` of "the new block or `fail`", and a
register live there is `r` (the only register `A` reads first) or live at
`oh` and not written by `A`. -/
theorem kml_hop {K : Nat → Nat → Prop} {oh fail r : Nat} {g : Comp.Gen Map}
    (hI : IL K (CGoalL.pick (jmp0 oh) (jmp0 fail) : CGoalL S) g) {A : List Pole}
    (hA : RegsIn (· < g.re) A) (hdA : ∀ y ∈ defsOf A, HoonMap.get g.cond y = Option.none)
    (hren : A.map (renPole (unproxy g.cond)) = A) (hrA : ∀ y, OpsRF A y → y = r) :
    IL K (CGoalL.pick (jmp0 g.bo) (jmp0 fail) : CGoalL S) (g.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩) ∧
    ∀ y, LiveK (unpM (g.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩)) K g.bo y →
      y = r ∨ (LiveK (unpM g) K oh y ∧ y ∉ defsOf A) := by
  have hd : g.drop = false := hI.ats.1
  obtain ⟨⟨bo', hbo, -, -⟩, -⟩ := (hI.goal : GoalL g (CGoalL.pick (jmp0 oh) (jmp0 fail) : CGoalL S))
  have hol : oh < g.bo := hI.lab hbo
  have hbat : BATC g.blocks (⟨[], A, Termin.hop (jmp0 oh)⟩ : Blob) := batc_fresh fun j hj => by
    simp only [finJumps, List.mem_singleton] at hj
    subst hj; exact hI.goal.1
  have hdefs : blockDefs (⟨[], A, Termin.hop (jmp0 oh)⟩ : Blob) = defsOf A := by
    simp [blockDefs, defsOf]
  have hrb : renBlob (unproxy g.cond) (⟨[], A, Termin.hop (jmp0 oh)⟩ : Blob) = ⟨[], A, Termin.hop (jmp0 oh)⟩ := by
    simp only [renBlob, List.map_nil, hren, renFin]
    rw [renJmp_nil _ rfl]
  refine ⟨kml_il_emit hI rfl hbat ⟨fun x hx => absurd hx List.not_mem_nil, hA, jmpIn_nil rfl⟩
    (fun y hy => hdA y (by rw [hdefs] at hy; exact hy)), fun y hl => ?_⟩
  have hget := unpM_emitted_self (g := g) hd (⟨[], A, Termin.hop (jmp0 oh)⟩ : Blob)
  rw [hrb] at hget
  cases hl with
  | here hb' hrf hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨-, hrf | ⟨-, hrf⟩⟩ := hrf
    · exact Or.inl (hrA y hrf)
    · simp [finRegs, jmpRegs, jmp0] at hrf
  | next hb' hj hl' hdf hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    simp only [getJmps, List.mem_singleton] at hj
    subst hj
    refine Or.inr ⟨(kml_live_frame hI (kml_keep_emit g _) hol).mp hl', fun hm => hdf ?_⟩
    rw [hdefs]; exact hm

/-- **The block `%clq r os fail`**: `IL` of "the new block or `fail`", and a
register live there is `r`, or live at `os` or at `fail`. -/
theorem kml_clq {K : Nat → Nat → Prop} {os fail r : Nat} {g : Comp.Gen Map}
    (hI : IL K (CGoalL.pick (jmp0 os) (jmp0 fail) : CGoalL S) g) (hr : r < g.re)
    (hkr : HoonMap.get g.cond r = Option.none) :
    IL K (CGoalL.pick (jmp0 g.bo) (jmp0 fail) : CGoalL S)
      (g.emitted ⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩) ∧
    ∀ y, LiveK (unpM (g.emitted ⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩)) K g.bo y →
      y = r ∨ LiveK (unpM g) K os y ∨ LiveK (unpM g) K fail y := by
  have hd : g.drop = false := hI.ats.1
  obtain ⟨⟨bs, hbs, -, -⟩, ⟨bf, hbf, -, -⟩⟩ :=
    (hI.goal : GoalL g (CGoalL.pick (jmp0 os) (jmp0 fail) : CGoalL S))
  have hsl : os < g.bo := hI.lab hbs
  have hfl : fail < g.bo := hI.lab hbf
  have hbat : BATC g.blocks (⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩ : Blob) := batc_fresh fun j hj => by
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hI.goal.1
    · exact hI.goal.2
  have ur : unproxy g.cond r = r := Raw.unproxy_none hkr
  have hrb : renBlob (unproxy g.cond) (⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩ : Blob) =
      ⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩ := by
    simp only [renBlob, List.map_nil, renFin, ur]
    rw [renJmp_nil _ rfl, renJmp_nil _ rfl]
  refine ⟨kml_il_emit hI rfl hbat ⟨fun x hx => absurd hx List.not_mem_nil, fun p hp => absurd hp List.not_mem_nil,
    hr, jmpIn_nil rfl, jmpIn_nil rfl⟩ (fun y hy => by simp [blockDefs] at hy), fun y hl => ?_⟩
  have hget := unpM_emitted_self (g := g) hd (⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩ : Blob)
  rw [hrb] at hget
  cases hl with
  | here hb' hrf hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨-, hrf | ⟨-, hrf⟩⟩ := hrf
    · exact hrf.elim
    · simp [finRegs, jmpRegs, jmp0] at hrf
      exact Or.inl hrf
  | next hb' hj hl' hdf hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Or.inr (Or.inl ((kml_live_frame hI (kml_keep_emit g _) hsl).mp hl'))
    · exact Or.inr (Or.inr ((kml_live_frame hI (kml_keep_emit g _) hfl).mp hl'))

/-! ## The induction -/

/-- `KmlLoopSpec` for one need. -/
def KmlFor (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map]
    (K : Nat → Nat → Prop) (fail : Nat) (ned : Need) : Prop :=
  ∀ (r o : Nat) (g g' : Comp.Gen Map) (o' : Nat),
    IL K (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S) g →
    Distinct ned →
    (∀ y, NMem ned y → y < g.re ∧ ¬ Defd g.blocks y ∧ HoonMap.get g.cond y = Option.none) →
    r < g.re → ¬ Defd g.blocks r → HoonMap.get g.cond r = Option.none → ¬ NMem ned r →
    (monoTryLoop fail ned r o : CM Map Nat) g = some (o', g') →
    IL K (CGoalL.pick (jmp0 o') (jmp0 fail) : CGoalL S) g' ∧
    ∀ y, LiveK (unpM g') K o' y →
      y = r ∨ (LiveK (unpM g) K o y ∧ ¬ NMem ned y) ∨ LiveK (unpM g) K fail y

/-- **The split of a cell need** (`%pair`, `%both`): the two loops from the
fresh registers `rt = re`, `rh = re + 1`, the block `[A] %hop oh`, the block
`%clq r os fail`. -/
theorem kml_two {K : Nat → Nat → Prop} {fail : Nat} {hn tn : Need}
    (ihh : KmlFor S Map K fail hn) (iht : KmlFor S Map K fail tn)
    {r o : Nat} {g g2 g3 g4 : Comp.Gen Map} {ot oh : Nat} {A : List Pole}
    (hI : IL K (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S) g)
    (Dh : Distinct hn) (Dt : Distinct tn) (Dht : ∀ x, NMem hn x → ¬ NMem tn x)
    (hNh : ∀ y, NMem hn y → y < g.re ∧ ¬ Defd g.blocks y ∧ HoonMap.get g.cond y = Option.none)
    (hNt : ∀ y, NMem tn y → y < g.re ∧ ¬ Defd g.blocks y ∧ HoonMap.get g.cond y = Option.none)
    (hr : r < g.re) (hkr : HoonMap.get g.cond r = Option.none)
    (r2 : g2.re = g.re + 2) (b2 : g2.blocks = g.blocks) (c2 : g2.cond = g.cond) (bo2 : g2.bo = g.bo)
    (d2 : g2.drop = g.drop)
    (h3 : (monoTryLoop fail tn g.re o : CM Map Nat) g2 = some (ot, g3))
    (h4 : (monoTryLoop fail hn (g.re + 1) ot : CM Map Nat) g3 = some (oh, g4))
    (hA : RegsIn (· < g.re + 2) A) (hdA : ∀ y ∈ defsOf A, HoonMap.get g.cond y = Option.none)
    (hren : A.map (renPole (unproxy g.cond)) = A) (hrA : ∀ y, OpsRF A y → y = r)
    (hdt : g.re ∈ defsOf A) (hdh : g.re + 1 ∈ defsOf A) :
    IL K (CGoalL.pick (jmp0 (g4.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩).bo) (jmp0 fail) : CGoalL S)
      ((g4.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩).emitted ⟨[], [], Termin.clq r (jmp0 g4.bo) (jmp0 fail)⟩) ∧
    ∀ y, LiveK (unpM ((g4.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩).emitted
        ⟨[], [], Termin.clq r (jmp0 g4.bo) (jmp0 fail)⟩)) K (g4.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩).bo y →
      y = r ∨ (LiveK (unpM g) K o y ∧ ¬ NMem hn y ∧ ¬ NMem tn y ∧ y ∉ defsOf A) ∨ LiveK (unpM g) K fail y := by
  have I2 : IL K (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S) g2 := il_re_up hI (by omega) b2 c2 bo2 d2
  have K02 : KmlKeep g g2 := ⟨d2, c2, by omega, fun k _ => by rw [b2]⟩
  have hdl : ∀ y, Defd g.blocks y → y < g.re := fun y hy => defd_lt hI.regs hy
  obtain ⟨I3, L3⟩ := iht g.re o g2 g3 ot I2 Dt
    (fun y hy => by obtain ⟨a, b, c⟩ := hNt y hy; exact ⟨by omega, by rw [b2]; exact b, by rw [c2]; exact c⟩)
    (by omega) (by rw [b2]; intro hd'; have := hdl _ hd'; omega) (by rw [c2]; exact hI.cond_ge (Nat.le_refl _))
    (fun hm => by have := (hNt _ hm).1; omega) h3
  have K23 := kml_keep_loop fail tn g.re o g2 g3 ot h3
  have DF3 := kdl_df_monoTryLoop fail tn g.re o g2 g3 ot h3
  have c3 : g3.cond = g.cond := K23.2.1.trans c2
  have re3 : g2.re ≤ g3.re := DF3.1
  obtain ⟨I4, L4⟩ := ihh (g.re + 1) ot g3 g4 oh I3 Dh
    (fun y hy => by
      obtain ⟨a, b, c⟩ := hNh y hy
      refine ⟨by omega, fun hd' => ?_, by rw [c3]; exact c⟩
      rcases DF3.2.2 y hd' with e | e | e
      · rw [b2] at e; exact b e
      · omega
      · exact Dht y hy e)
    (by omega)
    (fun hd' => by
      rcases DF3.2.2 _ hd' with e | e | e
      · rw [b2] at e; have := hdl _ e; omega
      · omega
      · have := (hNt _ e).1; omega)
    (by rw [c3]; exact hI.cond_ge (by omega))
    (fun hm => by have := (hNh _ hm).1; omega) h4
  have K34 := kml_keep_loop fail hn (g.re + 1) ot g3 g4 oh h4
  have DF4 := kdl_df_monoTryLoop fail hn (g.re + 1) ot g3 g4 oh h4
  have c4 : g4.cond = g.cond := K34.2.1.trans c3
  have re4 : g.re + 2 ≤ g4.re := by have := DF4.1; omega
  obtain ⟨I5, L5⟩ := kml_hop (r := r) I4 (A := A) (fun p hp x hx => Nat.lt_of_lt_of_le (hA p hp x hx) re4)
    (fun y hy => by rw [c4]; exact hdA y hy) (by rw [c4]; exact hren) (fun y hy => hrA y hy)
  obtain ⟨I6, L6⟩ := kml_clq (r := r) I5 (by show r < g4.re; omega)
    (by show HoonMap.get g4.cond r = _; rw [c4]; exact hkr)
  refine ⟨I6, fun y hl => ?_⟩
  have K04 : KmlKeep g g4 := kml_keep_trans K02 (kml_keep_trans K23 K34)
  have K05 : KmlKeep g (g4.emitted ⟨[], A, Termin.hop (jmp0 oh)⟩) := kml_keep_trans K04 (kml_keep_emit _ _)
  obtain ⟨-, ⟨bf, hbf, -, -⟩⟩ := (hI.goal : GoalL g (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S))
  have hfl : fail < g.bo := hI.lab hbf
  have U2 : unpM g2 = unpM g := by simp only [unpM, b2, c2]
  have fr : ∀ {gx : Comp.Gen Map}, KmlKeep g gx → LiveK (unpM gx) K fail y → LiveK (unpM g) K fail y :=
    fun hk hl' => (kml_live_frame hI hk hfl).mp hl'
  rcases L6 y hl with e | hl5 | hl5
  · exact Or.inl e
  · rcases L5 y hl5 with e | ⟨hl4, hd4⟩
    · exact Or.inl e
    · rcases L4 y hl4 with e | ⟨hl3, hn3⟩ | hl3
      · exact (hd4 (by rw [e]; exact hdh)).elim
      · rcases L3 y hl3 with e | ⟨hl2, hn2⟩ | hl2
        · exact (hd4 (by rw [e]; exact hdt)).elim
        · rw [U2] at hl2; exact Or.inr (Or.inl ⟨hl2, hn3, hn2, hd4⟩)
        · rw [U2] at hl2; exact Or.inr (Or.inr hl2)
      · exact Or.inr (Or.inr (fr (kml_keep_trans K02 K23) hl3))
  · exact Or.inr (Or.inr (fr K05 hl5))

/-- **The induction on the need.** -/
theorem kml_loopN (K : Nat → Nat → Prop) (fail : Nat) : ∀ (ned : Need), KmlFor S Map K fail ned
  | Need.none => by
    intro r o g g' o' hI hD hN hr hdr hkr hnr h
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, fun y hl => Or.inr (Or.inl ⟨hl, fun hm => hm⟩)⟩
  | Need.this rn => by
    intro r o g g' o' hI hD hN hr hdr hkr hnr h
    simp only [monoTryLoop] at h
    split at h
    · cases h
    · rename_i hne
      rw [emit_apply] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hrn, -, hkn⟩ := hN rn rfl
      have ur : unproxy g.cond r = r := Raw.unproxy_none hkr
      have un : unproxy g.cond rn = rn := Raw.unproxy_none hkn
      have hne' : rn ≠ r := fun e => hne e.symm
      obtain ⟨I1, L1⟩ := kml_hop (r := r) hI (A := [Pole.mov r rn])
        (fun p hp x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          subst hp
          simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
          omega)
        (fun y hy => by simp [defsOf, aliasDst] at hy; subst hy; exact hkn)
        (by simp [renPole, ur, un])
        (fun y hy => by
          simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, hne, hne'] at hy
          omega)
      refine ⟨I1, fun y hl => ?_⟩
      rcases L1 y hl with e | ⟨hl', hd'⟩
      · exact Or.inl e
      · refine Or.inr (Or.inl ⟨hl', fun e => hd' ?_⟩)
        simp only [NMem] at e
        subst e
        simp [defsOf, aliasDst]
  | Need.pair hn tn => by
    intro r o g g' o' hI hD hN hr hdr hkr hnr h
    simp only [monoTryLoop] at h
    obtain ⟨rt, g1, h1, h⟩ := bind_some h
    obtain ⟨rh, g2, h2, h⟩ := bind_some h
    obtain ⟨ot, g3, h3, h⟩ := bind_some h
    obtain ⟨oh, g4, h4, h⟩ := bind_some h
    obtain ⟨os, g5, h5, h⟩ := bind_some h
    rw [emit_apply] at h5 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h5 h
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ert, r1, b1, c1, bo1, d1⟩ := re_state h1
    obtain ⟨erh, r2, b2, c2, bo2, d2⟩ := re_state h2
    subst ert erh
    rw [r1] at h4 ⊢
    obtain ⟨Dh, Dt, Dht⟩ := hD
    have hkt : HoonMap.get g.cond g.re = Option.none := hI.cond_ge (Nat.le_refl _)
    have hkh : HoonMap.get g.cond (g.re + 1) = Option.none := hI.cond_ge (by omega)
    have ur := Raw.unproxy_none hkr
    have ut := Raw.unproxy_none hkt
    have uh := Raw.unproxy_none hkh
    have n1 : r ≠ g.re := by omega
    have n2 : r ≠ g.re + 1 := by omega
    have n1' : g.re ≠ r := by omega
    have n2' : g.re + 1 ≠ r := by omega
    obtain ⟨I, L⟩ := kml_two (A := [Pole.hed r (g.re + 1), Pole.tal r g.re]) (kml_loopN K fail hn)
      (kml_loopN K fail tn) hI Dh Dt Dht (fun y hy => hN y (Or.inl hy)) (fun y hy => hN y (Or.inr hy)) hr hkr
      (by omega) (b2.trans b1) (c2.trans c1) (bo2.trans bo1) (d2.trans d1) h3 h4
      (fun p hp x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
          omega)
      (fun y hy => by simp [defsOf, aliasDst] at hy; rcases hy with rfl | rfl <;> assumption)
      (by simp [renPole, ur, ut, uh])
      (fun y hy => by
        simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, n1, n2, n1', n2'] at hy
        omega)
      (by simp [defsOf, aliasDst]) (by simp [defsOf, aliasDst])
    refine ⟨I, fun y hl => ?_⟩
    rcases L y hl with e | ⟨a, b, c, -⟩ | e
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨a, fun hm => hm.elim b c⟩)
    · exact Or.inr (Or.inr e)
  | Need.both rn hn tn => by
    intro r o g g' o' hI hD hN hr hdr hkr hnr h
    simp only [monoTryLoop] at h
    obtain ⟨rt, g1, h1, h⟩ := bind_some h
    obtain ⟨rh, g2, h2, h⟩ := bind_some h
    obtain ⟨ot, g3, h3, h⟩ := bind_some h
    obtain ⟨oh, g4, h4, h⟩ := bind_some h
    split at h
    · cases h
    rename_i hne
    obtain ⟨os, g5, h5, h⟩ := bind_some h
    rw [emit_apply] at h5 h
    simp only [Option.some.injEq, Prod.mk.injEq] at h5 h
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ert, r1, b1, c1, bo1, d1⟩ := re_state h1
    obtain ⟨erh, r2, b2, c2, bo2, d2⟩ := re_state h2
    subst ert erh
    rw [r1] at h4 ⊢
    obtain ⟨Dh, Dt, Dht, -, -⟩ := hD
    obtain ⟨hrn, -, hkn⟩ := hN rn (Or.inl rfl)
    have hkt : HoonMap.get g.cond g.re = Option.none := hI.cond_ge (Nat.le_refl _)
    have hkh : HoonMap.get g.cond (g.re + 1) = Option.none := hI.cond_ge (by omega)
    have ur := Raw.unproxy_none hkr
    have ut := Raw.unproxy_none hkt
    have uh := Raw.unproxy_none hkh
    have un := Raw.unproxy_none hkn
    have n1 : r ≠ g.re := by omega
    have n2 : r ≠ g.re + 1 := by omega
    have n1' : g.re ≠ r := by omega
    have n2' : g.re + 1 ≠ r := by omega
    have hne' : rn ≠ r := fun e => hne e.symm
    obtain ⟨I, L⟩ := kml_two (A := [Pole.hed r (g.re + 1), Pole.tal r g.re, Pole.mov r rn]) (kml_loopN K fail hn)
      (kml_loopN K fail tn) hI Dh Dt Dht (fun y hy => hN y (Or.inr (Or.inl hy)))
      (fun y hy => hN y (Or.inr (Or.inr hy))) hr hkr
      (by omega) (b2.trans b1) (c2.trans c1) (bo2.trans bo1) (d2.trans d1) h3 h4
      (fun p hp x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
          omega)
      (fun y hy => by simp [defsOf, aliasDst] at hy; rcases hy with rfl | rfl | rfl <;> assumption)
      (by simp [renPole, ur, ut, uh, un])
      (fun y hy => by
        simp [OpsRF, aliasReads, aliasDst, Opt.poleRegs, List.erase_cons, n1, n2, n1', n2', hne, hne'] at hy
        omega)
      (by simp [defsOf, aliasDst]) (by simp [defsOf, aliasDst])
    refine ⟨I, fun y hl => ?_⟩
    rcases L y hl with e | ⟨a, b, c, d⟩ | e
    · exact Or.inl e
    · refine Or.inr (Or.inl ⟨a, fun hm => ?_⟩)
      rcases hm with e | e | e
      · exact d (by rw [e]; simp [defsOf, aliasDst])
      · exact b e
      · exact c e
    · exact Or.inr (Or.inr e)

/-- **`KmlLoopSpec`**: the loop of `+mono-try-call` keeps `IL` of "the
result block or `fail`" and leaves live only `r`, what is live at `o` and
not in the need, and what is live at `fail`. -/
theorem kml_loop : KmlLoopSpec S Map :=
  fun K fail ned r o g g' o' => kml_loopN K fail ned r o g g' o'

end Raw
end SkaModel
end Formalization
