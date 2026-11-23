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

end Comp
end SkaModel
end Formalization
