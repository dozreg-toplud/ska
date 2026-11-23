import lemmas.Ska.CompNest

/-!
# Helpers for nested `[6 c a b]`

The two lazy blocks of a `%6` grow the state and hold hops
(`ext_sixGenL`, `grow_sixGenL`, `sixGenL_get_y`, `sixGenL_get_n`), the
entries of the lazy need of a `%6` (`entries_six`), `pureEval` of a `%6`
(`pureEval_n6`), and bounds on labels (`labels_bound`).  `CompNestPick.lean`
uses them.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Helpers -/

theorem ext_tagged (g : Gen Map) (o : Nat) (region : List Nat) : Ext g (g.tagged o region) := by
  unfold Gen.tagged; split
  · exact Ext.refl g
  · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ => rfl⟩

theorem ext_sixGenL (g2 : Gen Map) th0 th1 region : Ext g2 (sixGenL g2 th0 th1 region) :=
  ((ext_emit _ _).trans (ext_emit _ _)).trans ((ext_tagged _ _ _).trans (ext_tagged _ _ _))

theorem grow_sixGenL {g2 : Gen Map} {th0 th1 : Jmp} (region : List Nat) (h0 : JumpsBelow (Termin.hop th0) g2.bo)
    (h1 : JumpsBelow (Termin.hop th1) (g2.bo + 1)) : Grow g2 (sixGenL g2 th0 th1 region) :=
  ((grow_emit h0).trans (grow_emit (by simpa [emitted_bo] using h1))).trans
    ((grow_tagged _ _ _).trans (grow_tagged _ _ _))

theorem sixGenL_get_y {g2 : Gen Map} (th0 th1 : Jmp) (region : List Nat) (hd : g2.drop = false) :
    HoonMap.get (sixGenL g2 th0 th1 region).blocks g2.bo = some ⟨[], [], Termin.hop th0⟩ := by
  simp only [sixGenL, tagged_blocks]
  rw [get_emitted_ne (by simp [emitted_bo])]; exact emitted_get g2 _ hd

theorem sixGenL_get_n {g2 : Gen Map} (th0 th1 : Jmp) (region : List Nat) (hd : g2.drop = false) :
    HoonMap.get (sixGenL g2 th0 th1 region).blocks (g2.bo + 1) = some ⟨[], [], Termin.hop th1⟩ := by
  simp only [sixGenL, tagged_blocks]
  exact emitted_get (g2.emitted _) _ (by simp [emitted_drop, hd])

theorem ext_addOps_nil {o : Nat} {g g' : Gen Map} {u : Unit} (h : addOps o [] g = some (u, g')) : Ext g g' := by
  obtain ⟨A, r, b, d⟩ := addOps_nil h
  exact ⟨Nat.le_of_eq r.symm, Nat.le_of_eq b.symm, d, fun k _ => A k⟩

theorem entries_six (s : Sure S) (y n : Nat) (l0 l1 : Lazy S) :
    entries (mk s [((y, l0), (n, l1))] []) = (y, l0) :: entries l0 ++ ((n, l1) :: entries l1) := by
  simp [entries, bondEntries, forkEntries]

theorem pureEval_n6 (c a b : Nomm) (s : Noun) : pureEval (Nomm.n6 c a b) s = (pureEval c s).bind fun v =>
    match v with
    | Noun.atom 0 => pureEval a s
    | Noun.atom 1 => pureEval b s
    | _ => none := rfl

theorem labels_bound {es : List (Nat × Lazy S)} {P : Nat → Prop} (h : ∀ e ∈ es, P e.1) :
    ∀ o ∈ es.map Prod.fst, P o := by
  intro o ho
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
  exact h e he

end Comp
end SkaModel
end Formalization
