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

end Comp
end SkaModel
end Formalization
