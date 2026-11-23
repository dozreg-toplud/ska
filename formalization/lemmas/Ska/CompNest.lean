import lemmas.Ska.CompNestCoerce

/-!
# Nested `[6 c a b]` under `%done`: the model taken apart

`sixCount` counts the `%6` of a nomm.

The lazy need that `runL` returns for such a nomm has at most two entries
per `%6` (`entries` of `CompNestCoerce.lean`), and `+lazy-size` is one more
than the number of entries as long as that stays under `+lazy-max`
(`lazySizeGo_eq`).  So when the nomm has at most 255 `%6`, `+lazy-shut`
never fires (`lazyBig_entries`), and no proxy register is made.

`runL_six_doneL` takes the case `%6` of `runL` for `%done` apart, with
branches of any shape, in the case where the fork is not big.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Counting `%6` -/

/-- The number of `%6` in a nomm. -/
def sixCount : Nomm → Nat
  | Nomm.cons p q => sixCount p + sixCount q
  | Nomm.n0 _ => 0
  | Nomm.n1 _ => 0
  | Nomm.n2 p q _ => sixCount p + sixCount q
  | Nomm.n3 p => sixCount p
  | Nomm.n4 p => sixCount p
  | Nomm.n5 p q => sixCount p + sixCount q
  | Nomm.n6 p q r => sixCount p + sixCount q + sixCount r + 1
  | Nomm.n7 p q => sixCount p + sixCount q
  | Nomm.n10 _ v q => sixCount v + sixCount q
  | Nomm.n11s _ q _ => sixCount q
  | Nomm.n11d _ h q _ => sixCount h + sixCount q
  | Nomm.n12 p q => sixCount p + sixCount q
  | Nomm.mean p _ q _ _ => sixCount p + sixCount q

theorem sixCount_pure_noSix : ∀ (nm : Nomm), nm.pure = true → noSix nm = true → sixCount nm = 0
  | Nomm.cons p q, hp, h6 => by
    simp only [Nomm.pure, noSix, Bool.and_eq_true] at hp h6
    simp [sixCount, sixCount_pure_noSix p hp.1 h6.1, sixCount_pure_noSix q hp.2 h6.2]
  | Nomm.n0 _, _, _ => rfl
  | Nomm.n1 _, _, _ => rfl
  | Nomm.n3 p, hp, h6 => by
    simp only [Nomm.pure, noSix] at hp h6; simp [sixCount, sixCount_pure_noSix p hp h6]
  | Nomm.n4 p, hp, h6 => by
    simp only [Nomm.pure, noSix] at hp h6; simp [sixCount, sixCount_pure_noSix p hp h6]
  | Nomm.n5 p q, hp, h6 => by
    simp only [Nomm.pure, noSix, Bool.and_eq_true] at hp h6
    simp [sixCount, sixCount_pure_noSix p hp.1 h6.1, sixCount_pure_noSix q hp.2 h6.2]
  | Nomm.n6 _ _ _, _, h6 => by simp [noSix] at h6
  | Nomm.n7 p q, hp, h6 => by
    simp only [Nomm.pure, noSix, Bool.and_eq_true] at hp h6
    simp [sixCount, sixCount_pure_noSix p hp.1 h6.1, sixCount_pure_noSix q hp.2 h6.2]
  | Nomm.n10 _ p q, hp, h6 => by
    simp only [Nomm.pure, noSix, Bool.and_eq_true] at hp h6
    simp [sixCount, sixCount_pure_noSix p hp.1 h6.1, sixCount_pure_noSix q hp.2 h6.2]
  | Nomm.n2 _ _ _, hp, _ => by simp [Nomm.pure] at hp
  | Nomm.n11s _ _ _, hp, _ => by simp [Nomm.pure] at hp
  | Nomm.n11d _ _ _ _, hp, _ => by simp [Nomm.pure] at hp
  | Nomm.n12 _ _, hp, _ => by simp [Nomm.pure] at hp
  | Nomm.mean _ _ _ _ _, hp, _ => by simp [Nomm.pure] at hp

theorem sixCount_frag {nm : Nomm} {goal : CGoal S} (hf : Frag nm goal) : sixCount nm = 0 :=
  sixCount_pure_noSix nm (frag_pure_noSix nm goal hf).1 (frag_pure_noSix nm goal hf).2

/-! ## `+lazy-size` -/

mutual
/-- Under `+lazy-max`, `+lazy-size` counts the need and its entries. -/
theorem lazySizeGo_eq : ∀ (l : Lazy S) (c : Nat), c + 1 + (entries l).length ≤ lazyMax + 1 →
    lazySizeGo c l = c + 1 + (entries l).length
  | mk _ f b, c, h => by
    simp only [entries, List.length_append] at h ⊢
    unfold lazySizeGo
    rw [if_neg (by omega), sizeForks_eq f (c + 1) (by omega), sizeBonds_eq b _ (by omega)]
    omega

theorem sizeForks_eq : ∀ (f : List (ForkE S)) (c : Nat), c + (forkEntries f).length ≤ lazyMax + 1 →
    sizeForks c f = c + (forkEntries f).length
  | [], c, _ => by simp [sizeForks, forkEntries]
  | ((oy, y), (on, n)) :: rest, c, h => by
    simp only [forkEntries, List.length_append, List.length_cons] at h ⊢
    unfold sizeForks
    rw [lazySizeGo_eq y c (by omega), lazySizeGo_eq n _ (by omega), sizeForks_eq rest _ (by omega)]
    omega

theorem sizeBonds_eq : ∀ (b : List (Nat × Lazy S)) (c : Nat), c + (bondEntries b).length ≤ lazyMax + 1 →
    sizeBonds c b = c + (bondEntries b).length
  | [], c, _ => by simp [sizeBonds, bondEntries]
  | (o, l) :: rest, c, h => by
    simp only [bondEntries, List.length_append, List.length_cons] at h ⊢
    unfold sizeBonds
    rw [lazySizeGo_eq l c (by omega), sizeBonds_eq rest _ (by omega)]
    omega
end

/-- **A lazy need with at most 511 entries is not big.** -/
theorem lazyBig_entries {l : Lazy S} (h : 1 + (entries l).length ≤ lazyMax) : lazyBig l = false := by
  unfold lazyBig lazySize
  rw [lazySizeGo_eq l 0 (by omega)]
  simp only [decide_eq_false_iff_not]; omega

/-! ## The case `%6` taken apart -/

/-- The two lazy blocks of a `%6` and the state after them. -/
def sixGenL (g2 : Gen Map) (th0 th1 : Jmp) (region : List Nat) : Gen Map :=
  (((g2.emitted ⟨[], [], Termin.hop th0⟩).emitted ⟨[], [], Termin.hop th1⟩).tagged g2.bo region).tagged
    (g2.bo + 1) region

@[simp] theorem sixGenL_bo (g2 : Gen Map) th0 th1 region : (sixGenL g2 th0 th1 region).bo = g2.bo + 2 := by
  simp [sixGenL, emitted_bo]
@[simp] theorem sixGenL_re (g2 : Gen Map) th0 th1 region : (sixGenL g2 th0 th1 region).re = g2.re := by
  simp [sixGenL, emitted_re]
@[simp] theorem sixGenL_drop (g2 : Gen Map) th0 th1 region : (sixGenL g2 th0 th1 region).drop = g2.drop := by
  simp [sixGenL, emitted_drop]
theorem sixGenL_cond (g2 : Gen Map) th0 th1 region : (sixGenL g2 th0 th1 region).cond = g2.cond := by
  simp [sixGenL, tagged_cond, emitted_cond]

/-- `+copy` of the test's `next` with the fork of the two branches. -/
theorem copyL_sixL (nc : Next S) (l0 l1 : Lazy S) (y n : Nat) (g : Gen Map) :
    (copyL (Next.toL nc) (mk Sure.bunt [((y, l0), (n, l1))] []) g : Option (NextL S × Gen Map)) =
      (addOps g.bo [] (g.emitted ⟨[], [], Termin.hop nc.th⟩)).map fun p =>
        (⟨mk ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩ [((y, l0), (n, l1))] [], jmp0 g.bo⟩, p.2) := by
  unfold copyL
  rw [bind_apply, emit_apply, Option.bind_some]
  simp only [Next.toL_laz, Next.toL_th, ofSure, copyLazyL, sure_mk, fork_mk, bond_mk, Sure.bunt]
  rw [bind_apply, bind_apply, copyNeed_none, Option.bind_some, bind_apply]
  simp only [List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true, if_false, if_true]
  cases addOps g.bo [] (g.emitted ⟨[], [], Termin.hop nc.th⟩) with
  | none => rfl
  | some p => rfl

/-- **The model of `[6 c a b]` under `%done`, taken apart**, with branches
of any shape, when the fork is not big. -/
theorem runL_six_doneL {c a b : Nomm} (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S)) {region : List Nat}
    {g0 g4 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    ∃ (x1 x0 : NextL S) (nc : Next S) (g1 g2 g3 : Gen Map),
      runL b (CGoalL.done : CGoalL S) region g0 = some (x1, g1) ∧
      runL a (CGoalL.done : CGoalL S) region g1 = some (x0, g2) ∧
      x0.th.args = [] ∧ x1.th.args = [] ∧
      run c (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (sixGenL g2 x0.th x1.th region) = some (nc, g3) ∧
      (lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false →
        addOps g3.bo [] (g3.emitted ⟨[], [], Termin.hop nc.th⟩) = some ((), g4) ∧
        nex = ⟨mk ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩
          [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] [], jmp0 g3.bo⟩) := by
  simp only [runL] at h
  obtain ⟨x1, g1, h1, h⟩ := bind_some h
  obtain ⟨x0, g2, h2, h⟩ := bind_some h
  simp only [bind_apply, emit_apply, setTag_apply, Option.bind_some] at h
  by_cases a0' : x0.th.args ≠ []
  · simp [a0'] at h
  have a0 : x0.th.args = [] := by simpa using a0'
  by_cases a1' : x1.th.args ≠ []
  · simp [a0, a1'] at h
  have a1 : x1.th.args = [] := by simpa using a1'
  simp only [a0, a1, ne_eq, not_true_eq_false, if_false] at h
  rw [show liftO (pastFork noCode (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] []) c) =
      (pure (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] []) : CM Map (Lazy S)) by
    rw [pastFork_pure _ _ (frag_pure_noSix c _ (hc (jmp0 0) (jmp0 0))).1]; rfl] at h
  obtain ⟨lz, gl, hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨nexC, g3x, h3, h⟩ := bind_some h
  rw [show (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo) : CGoalL S) =
    CGoal.toL (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo)) from rfl,
    runL_frag (hc _ _)] at h3
  obtain ⟨⟨nc, g3⟩, h3', e3⟩ := Option.map_eq_some_iff.mp h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl⟩ := e3
  refine ⟨x1, x0, nc, g1, g2, g3, h1, h2, a0, a1, h3', fun hbig => ?_⟩
  have hcond : (!(lazyBig (softLess noSoft (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] [])))) = true := by
    rw [softLess_noSoft]; simp only [emitted_bo]; rw [hbig]; rfl
  rw [if_pos hcond, copyL_sixL] at h
  obtain ⟨⟨u, g4'⟩, h4, h⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨h4, rfl⟩

end Comp
end SkaModel
end Formalization
