import lemmas.Ska.CompLazyFinal

/-!
# `[6 c a b]` under `%done`

The case `%6` of `runL` for the goal `%done`, with its test `c` on the
fragment `Frag` for `%pick` and its branches `a`, `b` on the fragment for
`%done`, and the final pass `finishL` over it.

`runL_six_done` takes the model apart: the no branch is compiled, then the
yes branch, the two lazy blocks `yes` and `nuh` hop to their code, the test
is compiled for `%pick` into them, and `+copy` puts the fork of the two
branches' needs into the lazy need of the whole, behind one more block.  The
fork's lazy need has size 3, so `+lazy-shut` never fires here.

`finishL_six_compDone`: then `+coerce-lazy` fills the entry block from the
input registers for the test's need, and each lazy block for its branch's
need, also from the input registers.  The code reads the input registers in
the lazy block after the test ran, which is right because the test's code
keeps every register allocated after it (`Keep` of `CompSem.lean`).  So the
compiled code of `[6 c a b]` returns what `+mink` returns, on every subject,
and in particular it does not take apart a part of the subject that only
the branch not taken reads.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- The state after `(set-tag o region)`. -/
def Gen.tagged (g : Gen Map) (o : Nat) (region : List Nat) : Gen Map :=
  if g.drop then g else { g with tags := HoonMap.put g.tags o region }

theorem setTag_apply (o : Nat) (region : List Nat) (g : Gen Map) :
    (setTag o region : CM Map Unit) g = some ((), g.tagged o region) := rfl

@[simp] theorem tagged_re (g : Gen Map) o region : (g.tagged o region).re = g.re := by
  unfold Gen.tagged; split <;> rfl
@[simp] theorem tagged_bo (g : Gen Map) o region : (g.tagged o region).bo = g.bo := by
  unfold Gen.tagged; split <;> rfl
@[simp] theorem tagged_drop (g : Gen Map) o region : (g.tagged o region).drop = g.drop := by
  unfold Gen.tagged; split <;> rfl
@[simp] theorem tagged_blocks (g : Gen Map) o region : (g.tagged o region).blocks = g.blocks := by
  unfold Gen.tagged; split <;> rfl

/-- On the fragment, `runL` on a fork-free goal is `run`. -/
theorem runL_frag {nm : Nomm} {goal : CGoal S} (hf : Frag nm goal) (region : List Nat) (g : Gen Map) :
    (runL nm (CGoal.toL goal) region g : Option (NextL S × Gen Map)) =
      (run nm goal g).map fun p => (Next.toL p.1, p.2) := by
  rw [runL_toL nm (frag_pure_noSix nm goal hf).1 (frag_pure_noSix nm goal hf).2 goal region, map_apply]

theorem copyNeed_none (x : Need) (g : Gen Map) :
    (copyNeed x Need.none [] : CM Map (Need × List Pole)) g = some ((x, []), g) := by
  cases x <;> rfl

theorem ite_app {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (x : α) :
    (if c then f else g) x = if c then f x else g x := by
  split <;> rfl

/-- The two lazy blocks and the state after them. -/
def sixGen (g2 : Gen Map) (n0 n1 : Next S) : Gen Map :=
  (((g2.emitted ⟨[], [], Termin.hop n0.th⟩).emitted ⟨[], [], Termin.hop n1.th⟩).tagged g2.bo []).tagged
    (g2.bo + 1) []

/-- `+copy` of the test's `next` with the fork of the two branches. -/
theorem copyL_six (nc : Next S) (L0 L1 : Sure S) (y n : Nat) (g : Gen Map) :
    (copyL (Next.toL nc) (mk Sure.bunt [((y, ofSure L0), (n, ofSure L1))] []) g : Option (NextL S × Gen Map)) =
      (addOps g.bo [] (g.emitted ⟨[], [], Termin.hop nc.th⟩)).map fun p =>
        (⟨mk ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩ [((y, ofSure L0), (n, ofSure L1))] [], jmp0 g.bo⟩,
          p.2) := by
  unfold copyL
  rw [bind_apply, emit_apply, Option.bind_some]
  simp only [Next.toL_laz, Next.toL_th, ofSure, copyLazyL, sure_mk, fork_mk, bond_mk, Sure.bunt]
  rw [bind_apply, bind_apply, copyNeed_none, Option.bind_some, bind_apply]
  simp only [List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, if_false, if_true]
  cases addOps g.bo [] (g.emitted ⟨[], [], Termin.hop nc.th⟩) with
  | none => rfl
  | some p => rfl

/-- **The model of `[6 c a b]` under `%done`, taken apart.** -/
theorem runL_six_done {c a b : Nomm} (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S))
    (ha : Frag a (CGoal.done : CGoal S)) (hb : Frag b (CGoal.done : CGoal S)) {g0 g4 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n6 c a b) (CGoalL.done : CGoalL S) [] g0 = some (nex, g4)) :
    ∃ (n1 n0 nc : Next S) (g1 g2 g3 : Gen Map),
      run b CGoal.done g0 = some (n1, g1) ∧ run a CGoal.done g1 = some (n0, g2) ∧
      n0.th.args = [] ∧ n1.th.args = [] ∧
      run c (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (sixGen g2 n0 n1) = some (nc, g3) ∧
      addOps g3.bo [] (g3.emitted ⟨[], [], Termin.hop nc.th⟩) = some ((), g4) ∧
      nex = ⟨mk ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩
        [((g2.bo, ofSure n0.laz), (g2.bo + 1, ofSure n1.laz))] [], jmp0 g3.bo⟩ := by
  simp only [runL] at h
  obtain ⟨nex1, g1x, h1, h⟩ := bind_some h
  rw [show (CGoalL.done : CGoalL S) = CGoal.toL CGoal.done from rfl, runL_frag hb] at h1
  obtain ⟨⟨n1, g1⟩, h1', e1⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨nex0, g2x, h2, h⟩ := bind_some h
  rw [show (CGoalL.done : CGoalL S) = CGoal.toL CGoal.done from rfl, runL_frag ha] at h2
  obtain ⟨⟨n0, g2⟩, h2', e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  simp only [bind_apply, emit_apply, setTag_apply, Option.bind_some, Next.toL_th, Next.toL_laz] at h
  by_cases a0' : n0.th.args ≠ []
  · simp [a0'] at h
  have a0 : n0.th.args = [] := by simpa using a0'
  by_cases a1' : n1.th.args ≠ []
  · simp [a0, a1'] at h
  have a1 : n1.th.args = [] := by simpa using a1'
  simp only [a0, a1, ne_eq, not_true_eq_false, if_false] at h
  simp only [a0, not_true_eq_false, ↓reduceIte, ite_not, if_true] at h
  rw [show liftO (pastFork noCode (mk (Sure.bunt : Sure S)
      [((g2.bo, ofSure n0.laz), ((g2.emitted ⟨[], [], Termin.hop n0.th⟩).bo, ofSure n1.laz))] []) c) =
      (pure (mk (Sure.bunt : Sure S)
      [((g2.bo, ofSure n0.laz), ((g2.emitted ⟨[], [], Termin.hop n0.th⟩).bo, ofSure n1.laz))] []) : CM Map (Lazy S)) by
    rw [pastFork_pure _ _ (frag_pure_noSix c _ (hc (jmp0 0) (jmp0 0))).1]; rfl] at h
  obtain ⟨lz, gl, hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨nexC, g3x, h3, h⟩ := bind_some h
  rw [show (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.emitted ⟨[], [], Termin.hop n0.th⟩).bo) : CGoalL S) =
    CGoal.toL (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.emitted ⟨[], [], Termin.hop n0.th⟩).bo)) from rfl,
    runL_frag (hc _ _)] at h3
  obtain ⟨⟨nc, g3⟩, h3', e3⟩ := Option.map_eq_some_iff.mp h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl⟩ := e3
  have hcond : (!(lazyBig (softLess noSoft (mk (Sure.bunt : Sure S)
      [((g2.bo, ofSure n0.laz), ((g2.emitted ⟨[], [], Termin.hop n0.th⟩).bo, ofSure n1.laz))] [])))) = true := by
    rw [softLess_noSoft]
    simp [lazyBig, lazySize, lazySizeGo, sizeForks, sizeBonds, lazyMax, ofSure]
  rw [if_pos hcond, copyL_six] at h
  obtain ⟨⟨u, g4'⟩, h4, h⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨n1, n0, nc, g1, g2, g3, h1', h2', a0, a1, h3', h4, rfl⟩

/-! ## The final pass -/

theorem grow_tagged (g : Gen Map) (o : Nat) (region : List Nat) : Grow g (g.tagged o region) := by
  unfold Gen.tagged; split
  · exact Grow.refl g
  · exact ⟨Nat.le_refl _, rfl, fun _ b _ hb => ⟨b, hb, rfl, rfl⟩, fun _ b hb => Or.inl ⟨b, hb, rfl, rfl⟩⟩

/-- `(add-ops o ~)` changes no block. -/
theorem addOps_nil {o : Nat} {g g' : Gen Map} {u : Unit} (h : addOps o [] g = some (u, g')) :
    (∀ k, HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧ g'.re = g.re ∧ g'.bo = g.bo ∧ g'.drop = g.drop := by
  cases hd : g.drop
  · obtain ⟨b, hb, rfl⟩ := addOps_spec h hd
    refine ⟨fun k => ?_, rfl, rfl, hd⟩
    by_cases e : k = o
    · subst e; simp [HoonMap.get_put, hb]
    · simp [HoonMap.get_put, e]
  · unfold addOps at h
    simp only [hd, if_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨fun _ => rfl, rfl, rfl, hd⟩

theorem looks_uni_empty (l : S) (s : Noun) : Looks (HoonSet.uni l HoonSet.empty) s ↔ Looks l s := by
  simp only [Looks, HoonSet.mem_uni]
  exact ⟨fun h a ha => h a (Or.inl ha), fun h a ha => ha.elim (h a) (fun e => absurd e (HoonSet.mem_empty a))⟩

/-- The final pass on `[6 c a b]`, taken apart. -/
theorem finishL_six_parts [HoonMapKeys Map] {c a b : Nomm} (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S))
    (ha : Frag a (CGoal.done : CGoal S)) (hb : Frag b (CGoal.done : CGoal S)) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishL (S := S) (Nomm.n6 c a b) ord less bake = some c') :
    ∃ (n1 n0 nc : Next S) (g1 g2 g3 g4 g5 g6 g7 g8 g9 : Gen Map) (nedF : Need),
      run b CGoal.done gen0 = some (n1, g1) ∧ run a CGoal.done g1 = some (n0, g2) ∧
      n0.th.args = [] ∧ n1.th.args = [] ∧
      run c (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (sixGen g2 n0 n1) = some (nc, g3) ∧
      addOps g3.bo [] (g3.emitted ⟨[], [], Termin.hop nc.th⟩) = some ((), g4) ∧
      needOrdAllocRegs ord g4 = some (nedF, g5) ∧
      coerceLazy nedF g3.bo ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩ less g5 = some ((), g6) ∧
      coerceLazy nedF g2.bo n0.laz less g6 = some ((), g7) ∧
      coerceLazy nedF (g2.bo + 1) n1.laz less g7 = some ((), g8) ∧
      addOps g3.bo [] g8 = some ((), g9) ∧
      toStraight g9.blocks nedF g3.bo = some c' := by
  unfold finishL at h
  obtain ⟨⟨nex, g4⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨n1, n0, nc, g1, g2, g3, hrb, hra, a0, a1, hrc, hadd, rfl⟩ := runL_six_done hc ha hb h1
  simp only [jmp0, ne_eq, not_true_eq_false, if_false, hbake, List.map_nil] at h
  obtain ⟨⟨nedF, g5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u8, g8⟩, h8, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  obtain ⟨⟨u9, g9⟩, h9, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  simp only [coerceLazyL, bind_apply] at h8
  obtain ⟨⟨u6, g6⟩, h6, h8⟩ := Option.bind_eq_some_iff.mp h8
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, coerceBonds, coerceForks,
    coerceLazyL_ofSure, bind_apply, pure_apply, Option.bind_some] at h8
  obtain ⟨⟨u7, g7⟩, h7, h8⟩ := Option.bind_eq_some_iff.mp h8
  obtain ⟨⟨u8', g8'⟩, h8', h8⟩ := Option.bind_eq_some_iff.mp h8
  simp only [Option.some.injEq, Prod.mk.injEq] at h8
  obtain ⟨_, rfl⟩ := h8
  exact ⟨n1, n0, nc, g1, g2, g3, g4, g5, g6, g7, g8', g9, nedF, hrb, hra, a0, a1, hrc, hadd, h5, h6, h7, h8', h9, hts⟩

theorem get_emitted_ne {g : Gen Map} {b : Blob} {k : Nat} (h : k ≠ g.bo) :
    HoonMap.get (g.emitted b).blocks k = HoonMap.get g.blocks k := by
  simp only [Gen.emitted]; split <;> simp [HoonMap.get_put, h]

@[simp] theorem sixGen_bo (g2 : Gen Map) (n0 n1 : Next S) : (sixGen g2 n0 n1).bo = g2.bo + 2 := by
  simp [sixGen, emitted_bo]
@[simp] theorem sixGen_re (g2 : Gen Map) (n0 n1 : Next S) : (sixGen g2 n0 n1).re = g2.re := by
  simp [sixGen, emitted_re]
@[simp] theorem sixGen_drop (g2 : Gen Map) (n0 n1 : Next S) : (sixGen g2 n0 n1).drop = g2.drop := by
  simp [sixGen, emitted_drop]

theorem jumpsBelow_hop {j : Jmp} {k : Nat} (h1 : 1 ≤ j.there) (h2 : j.there < k) :
    JumpsBelow (Termin.hop j) k := by
  intro j' hj; simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨h1, h2⟩

/-- **The final pass on `[6 c a b]` meets the relation at the entry**: the
compiled code returns what the nomm returns, and crashes where it crashes. -/
theorem finishL_six_compDone [HoonMapKeys Map] (lib : Lib) {c a b : Nomm}
    (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S)) (ha : Frag a (CGoal.done : CGoal S))
    (hb : Frag b (CGoal.done : CGoal S)) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishL (S := S) (Nomm.n6 c a b) ord less bake = some c') :
    CompDoneOn lib c' (Nomm.n6 c a b) (CapeAxes less) := by
  obtain ⟨n1, n0, nc, g1, g2, g3, g4, g5, g6, g7, g8, g9, nedF, hrb, hra, a0, a1, hrc, hadd, h5, h6, h7, h8, h9,
    hts⟩ := finishL_six_parts hc ha hb hbake h
  have Rb := run_ok lib b CGoal.done gen0 g1 n1 hb trivial trivial hrb
  have Ra := run_ok lib a CGoal.done g1 g2 n0 ha trivial trivial hra
  have Rc := run_ok lib c _ _ g3 nc (hc _ _) trivial trivial hrc
  -- the labels
  have Db := run_down (S := S) (Map := Map) b CGoal.done gen0 g1 n1 trivial (by simp [gen0]) rfl hrb
  have d1 : g1.drop = false := Db.grow.drop
  have b1 : 1 ≤ g1.bo := by have := Db.grow.bo; simp [gen0] at this; omega
  have Da := run_down (S := S) (Map := Map) a CGoal.done g1 g2 n0 trivial b1 d1 hra
  have d2 : g2.drop = false := Da.grow.drop.trans d1
  have b12 : g1.bo ≤ g2.bo := Da.grow.bo
  have dG : (sixGen g2 n0 n1).drop = false := by simp [d2]
  have Dc := run_down (S := S) (Map := Map) c (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (sixGen g2 n0 n1) g3 nc
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGen_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGen_bo]; omega⟩ (by simp only [sixGen_bo]; omega) dG hrc
  have d3 : g3.drop = false := Dc.grow.drop.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Dc.grow.bo; simpa using this
  -- the states after the run
  obtain ⟨A4, r4, bo4, dr4⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo, emitted_drop] at r4 bo4 dr4
  obtain ⟨⟨k5, rfl⟩, l5, dist5, mem5⟩ := needOrdAllocRegs_spec ord g4 _ nedF h5
  have d5 : ({ g4 with re := k5 } : Gen Map).drop = false := dr4.trans d3
  -- the registers
  have lc : ∀ r, NMem nc.laz.ned r → r < g3.re := fun r hr =>
    (Rc.regs r hr).elim (fun e => e.elim) (fun e => e.2)
  have la : ∀ r, NMem n0.laz.ned r → r < g2.re := fun r hr =>
    (Ra.regs r hr).elim (fun e => e.elim) (fun e => e.2)
  have lb : ∀ r, NMem n1.laz.ned r → r < g1.re := fun r hr =>
    (Rb.regs r hr).elim (fun e => e.elim) (fun e => e.2)
  have r12 : g1.re ≤ g2.re := Ra.ext.1
  have r23 : g2.re ≤ g3.re := by have := Rc.ext.1; simpa using this
  have mem5' : ∀ r, NMem nedF r → g3.re ≤ r ∧ r < k5 := fun r hr => by
    have := mem5 r hr; simp only at this; omega
  have r45 : g3.re ≤ k5 := by have h1 := l5; simp only at h1; omega
  -- `+coerce-lazy` at the entry and at the two lazy blocks
  obtain ⟨Ao, F6, So⟩ := coerceSpec nedF g3.bo ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩ less _ g6 h6 d5
    dist5 Rc.dist (fun r hr => by have := lc r hr; show r < k5; omega) (fun r hr => (mem5' r hr).2)
    (fun r hr hl => by have := lc r hl; have := mem5' r hr; omega)
  have d6 : g6.drop = false := F6.drop.trans d5
  have l6 : k5 ≤ g6.re := F6.le
  obtain ⟨Ay, F7, Sy⟩ := coerceSpec nedF g2.bo n0.laz less g6 g7 h7 d6 dist5 Ra.dist
    (fun r hr => by have := la r hr; omega) (fun r hr => by have := (mem5' r hr).2; omega)
    (fun r hr hl => by have := la r hl; have := mem5' r hr; omega)
  have d7 : g7.drop = false := F7.drop.trans d6
  have l7 := F7.le
  obtain ⟨An, F8, Sn⟩ := coerceSpec nedF (g2.bo + 1) n1.laz less g7 g8 h8 d7 dist5 Rb.dist
    (fun r hr => by have := lb r hr; omega) (fun r hr => by have := (mem5' r hr).2; omega)
    (fun r hr hl => by have := lb r hl; have := mem5' r hr; omega)
  have d8 : g8.drop = false := F8.drop.trans d7
  have F9 := front_addOps h9 d8
  -- the blocks
  have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k = HoonMap.get (sixGen g2 n0 n1).blocks k :=
    fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
  have hGy : HoonMap.get (sixGen g2 n0 n1).blocks g2.bo = some ⟨[], [], Termin.hop n0.th⟩ := by
    simp only [sixGen, tagged_blocks]
    rw [get_emitted_ne (by simp [emitted_bo])]; exact emitted_get g2 _ d2
  have hGn : HoonMap.get (sixGen g2 n0 n1).blocks (g2.bo + 1) = some ⟨[], [], Termin.hop n1.th⟩ := by
    simp only [sixGen, tagged_blocks]
    exact emitted_get (g2.emitted _) _ (by simp [emitted_drop, d2])
  have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k hk =>
    (A4 k).trans (get_emitted_ne hk)
  have h4o : HoonMap.get ({ g4 with re := k5 } : Gen Map).blocks g3.bo = some ⟨[], [], Termin.hop nc.th⟩ :=
    (A4 g3.bo).trans (emitted_get g3 _ d3)
  have h4y : HoonMap.get ({ g4 with re := k5 } : Gen Map).blocks g2.bo = some ⟨[], [], Termin.hop n0.th⟩ := by
    show HoonMap.get g4.blocks g2.bo = _
    rw [h4k _ (by omega), hG3 _ (by omega), hGy]
  have h4n : HoonMap.get ({ g4 with re := k5 } : Gen Map).blocks (g2.bo + 1) =
      some ⟨[], [], Termin.hop n1.th⟩ := by
    show HoonMap.get g4.blocks (g2.bo + 1) = _
    rw [h4k _ (by omega), hG3 _ (by omega), hGn]
  have h6o := F6.blk _ _ h4o
  have h7y := F7.blk _ _ ((F6.other _ (by omega)).trans h4y)
  have h8n := F8.blk _ _ (((F7.other _ (by omega)).trans (F6.other _ (by omega))).trans h4n)
  have h9o := F9.blk _ _ ((F8.other _ (by omega)).trans ((F7.other _ (by omega)).trans h6o))
  have h9y : HoonMap.get g9.blocks g2.bo = some ⟨[], Ay ++ [], Termin.hop n0.th⟩ :=
    (F9.other _ (by omega)).trans ((F8.other _ (by omega)).trans h7y)
  have h9n : HoonMap.get g9.blocks (g2.bo + 1) = some ⟨[], An ++ [], Termin.hop n1.th⟩ :=
    (F9.other _ (by omega)).trans h8n
  have h9k : ∀ k, k < g2.bo → HoonMap.get g9.blocks k = HoonMap.get g2.blocks k := fun k hk => by
    rw [F9.other _ (by omega), F8.other _ (by omega), F7.other _ (by omega), F6.other _ (by omega)]
    show HoonMap.get g4.blocks k = _
    rw [h4k _ (by omega), hG3 _ (by omega)]
    simp only [sixGen, tagged_blocks]
    rw [get_emitted_ne (by simp [emitted_bo]; omega), get_emitted_ne (by omega)]
  -- every block goes down
  have Gr : Grow (gen0 : Gen Map) g4 :=
    Db.grow.trans (Da.grow.trans (((grow_emit (jumpsBelow_hop Da.lo Da.hi)).trans
      ((grow_emit (jumpsBelow_hop Db.lo (by have := Db.hi; simp only [emitted_bo]; omega))).trans
        ((grow_tagged _ _ _).trans (grow_tagged _ _ _)))).trans
      (Dc.grow.trans ((grow_emit (jumpsBelow_hop Dc.lo Dc.hi)).trans (grow_addOps hadd)))))
  have D4 : Down g4.blocks := Gr.down (fun k b hb => by simp [gen0, HoonMap.get_empty] at hb) (by simp [gen0])
  have D6 := down_front (g := { g4 with re := k5 }) D4 h4o F6
  have D7 := down_front D6 ((F6.other _ (by omega)).trans h4y) F7
  have D8 := down_front D7 (((F7.other _ (by omega)).trans (F6.other _ (by omega))).trans h4n) F8
  have D9 := down_front D8 ((F8.other _ (by omega)).trans ((F7.other _ (by omega)).trans h6o)) F9
  -- the program and its entry
  let cF : Straight Map := ⟨NeedOrd.none, 0, g9.blocks⟩
  obtain ⟨_, start, hst, hent⟩ := toStraight_entry (c := cF) hts D9 D9 (fun _ _ => rfl)
  rw [h9o] at hst; cases hst
  have agC : Agree cF (sixGen g2 n0 n1) g3 := fun k hk1 hk2 => by
    simp only [sixGen_bo] at hk1
    show HoonMap.get g9.blocks k = _
    rw [F9.other _ (by omega), F8.other _ (by omega), F7.other _ (by omega), F6.other _ (by omega)]
    exact h4k _ (by omega)
  have agA : Agree cF g1 g2 := fun k hk1 hk2 => h9k k hk2
  have agB : Agree cF gen0 g1 := fun k hk1 hk2 => (h9k k (by omega)).trans (Ra.ext.2.2.2 k hk2)
  intro σ O st s args t gul hP hsp
  obtain ⟨R, hR, he⟩ := hent lib O st s args t gul hsp
  rw [he]
  simp only [List.nil_append, List.append_nil]
  have pe : pureEval (Nomm.n6 c a b) s = (pureEval c s).bind fun v => match v with
      | Noun.atom 0 => pureEval a s
      | Noun.atom 1 => pureEval b s
      | _ => none := rfl
  -- a lazy block entered with the input registers holding the subject
  have lazyBlk : ∀ (o : Nat) (A : List Pole) (L : Sure S) (th : Jmp) (nm : Nomm) (g g' : Gen Map),
      HoonMap.get cF.blocks o = some ⟨[], A ++ [], Termin.hop th⟩ →
      RunOK lib nm (CGoal.done : CGoal S) g g' ⟨L, th⟩ → Agree cF g g' → g.drop = false →
      (∀ (R : Map Noun), HoldsN nedF R s → CapeAxes less s →
        (FitsS L s → ∃ R', Runs lib O cF gul st t A R R' ∧ HoldsS L R' s ∧
          ∀ x, NMem nedF x → SkaModel.read x R' = SkaModel.read x R) ∧
        (¬ FitsS L s → Crashes lib O cF gul st t A R)) →
      ∀ (R2 : Map Noun), HoldsN nedF R2 s →
        goJ lib O cF gul st R2 t (jmp0 o) = some (toneOf t (pureEval nm s), st) := by
    intro o A L th nm g g' hbk RO ag dg SA R2 hR2
    rw [goJ_jmp0 _ _ _ _ hbk]
    by_cases fl : FitsS L s
    · obtain ⟨R3, hr3, hh3, _⟩ := (SA R2 hR2 hP).1 fl
      rw [hr3, execBlob_hop]
      exact RO.sem dg cF ag σ O st s R3 t gul hh3
    · rw [(SA R2 hR2 hP).2 fl]
      rcases RO.nec s fl with e | ⟨_, _, e⟩
      · rw [e]; rfl
      · exact e.elim
  have hy : ∀ R2, HoldsN nedF R2 s → goJ lib O cF gul st R2 t (jmp0 g2.bo) = some (toneOf t (pureEval a s), st) :=
    lazyBlk g2.bo Ay n0.laz n0.th a g1 g2 h9y Ra agA d1 (fun R2 hR2 hP' => Sy lib σ O cF gul st t R2 s hR2 hP')
  have hn : ∀ R2, HoldsN nedF R2 s →
      goJ lib O cF gul st R2 t (jmp0 (g2.bo + 1)) = some (toneOf t (pureEval b s), st) :=
    lazyBlk (g2.bo + 1) An n1.laz n1.th b gen0 g1 h9n Rb agB rfl
      (fun R2 hR2 hP' => Sn lib σ O cF gul st t R2 s hR2 hP')
  obtain ⟨SoF, SoC⟩ := So lib σ O cF gul st t R s hR hP
  rw [show Ao = Ao ++ [] by simp]
  by_cases fo : FitsS (⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩ : Sure S) s
  · obtain ⟨R1, hr1, hh1, kr1⟩ := SoF fo
    rw [hr1, execBlob_hop]
    have Hc := Rc.sem dG cF agC σ O st s R1 t gul ⟨hh1.1, (looks_uni_empty _ _).mp hh1.2⟩
    have hR1 : HoldsN nedF R1 s := HoldsN.agree nedF (fun x hx => kr1 x hx) hR
    have keepF : ∀ R2, (∀ r, Keep (sixGen g2 n0 n1) g3 (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) r →
        SkaModel.read r R2 = SkaModel.read r R1) → HoldsN nedF R2 s :=
      fun R2 k2 => HoldsN.agree nedF (fun x hx => k2 x ⟨Or.inr (mem5' x hx).1, fun e => e⟩) hR1
    rw [pureTone, pe]
    cases ec : pureEval c s with
    | none => rw [ec] at Hc; exact Hc
    | some v =>
      rw [ec] at Hc
      rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
      · obtain ⟨R2, k2, e2⟩ := Hc; rw [e2]; exact hy R2 (keepF R2 k2)
      · obtain ⟨R2, k2, e2⟩ := Hc; rw [e2]; exact hn R2 (keepF R2 k2)
      · exact Hc
      · exact Hc
  · rw [SoC fo]
    have fo' : ¬ FitsS nc.laz s := fun f => fo ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    rcases Rc.nec s fo' with e | ⟨_, _, e⟩
    · rw [pureTone, pe, e]; rfl
    · exact e.elim

/-- **The final pass on `[6 c a b]` meets the contract** of its bell, when
nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishL_six_bellContract [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {c a b : Nomm} (hp : (Nomm.n6 c a b).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n6 c a b))
    (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S)) (ha : Frag a (CGoal.done : CGoal S))
    (hb : Frag b (CGoal.done : CGoal S)) {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishL (S := S) (Nomm.n6 c a b) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' := by
  have hc' := finishL_six_compDone lib hc ha hb hbake h
  refine bellContract_of_compDoneOn hok hp hA (fun σ O st s args t gul hs hsp => ?_) N
  rw [hbl] at hs
  exact hc' σ O st s args t gul (fun axe h1 ha => capeAxes_of_fits axe h1 cape data s hn hs ha) hsp

/-- The fragment with one `%6` at the top: a nomm of `Frag` for `%done`, or
`[6 c a b]` with its test on `Frag` for `%pick` and its branches on `Frag`
for `%done`. -/
def Frag6 (nm : Nomm) : Prop :=
  Frag nm (CGoal.done : CGoal S) ∨ ∃ c a b, nm = Nomm.n6 c a b ∧ (∀ z o, Frag c (CGoal.pick z o : CGoal S)) ∧
    Frag a (CGoal.done : CGoal S) ∧ Frag b (CGoal.done : CGoal S)

/-- **The final pass over full lazy needs meets the contract on `Frag6`.** -/
theorem finishL_bellContract6 [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : Frag6 (S := S) nm) {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishL (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' := by
  rcases hf with hf | ⟨c, a, b, rfl, hc, ha, hb⟩
  · exact finishL_bellContract hok hp hA hf hbl hn hbake h N
  · exact finishL_six_bellContract hok hp hA hc ha hb hbl hn hbake h N

/-- **The compiled `[6 c a b]` crashes exactly when the nomm does**, on
every subject that has the axes the cape says it has, whatever the shape
`ord` of the inputs: a subject that lacks a part that only the branch not
taken reads does not make it crash. -/
theorem six_crash_iff [HoonMapKeys Map] (lib : Lib) {c a b : Nomm}
    (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S)) (ha : Frag a (CGoal.done : CGoal S))
    (hb : Frag b (CGoal.done : CGoal S)) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishL (S := S) (Nomm.n6 c a b) ord less bake = some c') {σ : Type} (O : Oracle σ) (st : σ)
    (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval (Nomm.n6 c a b) s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval (Nomm.n6 c a b) s = some v := by
  rw [finishL_six_compDone lib hc ha hb hbake h σ O st s args t gul hP hsp, pureTone]
  constructor
  · cases pureEval (Nomm.n6 c a b) s <;> simp [toneOf]
  · intro v; cases pureEval (Nomm.n6 c a b) s <;> simp [toneOf]

theorem capeAxes_no (s : Noun) : CapeAxes Cape.no s := by
  intro axe h1 hax
  by_cases h : axe ≤ 1
  · have : axe = 1 := by omega
    subst this; simp [slot?_one]
  · rw [axeInCape_no (by omega)] at hax; cases hax

/-- **The example**: `[6 [0 2] [0 6] [0 14]]` on `[0 1 2]`, whose test is `0`
and whose no branch reads the axis `14` that the subject lacks, returns `1`,
for every shape of the inputs for which the final pass returns a program. -/
theorem six_example [HoonMapKeys Map] (lib : Lib) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishL (S := S) (Nomm.n6 (Nomm.n0 2) (Nomm.n0 6) (Nomm.n0 14)) ord Cape.no bake = some c')
    {σ : Type} (O : Oracle σ) (st : σ) (args : List Noun) (t : Trace) (gul : Noun)
    (hsp : SkaModel.split c'.need (C (A 0) (C (A 1) (A 2))) = some args) :
    execEntry lib O st c' args t gul = some (Tone.zero (A 1), st) := by
  rw [finishL_six_compDone (c := Nomm.n0 2) (a := Nomm.n0 6) (b := Nomm.n0 14) lib
    (fun _ _ => (trivial : True)) (trivial : True) (trivial : True) hbake h σ O st _ args t gul (capeAxes_no _) hsp]
  rfl

end Comp
end SkaModel
end Formalization
