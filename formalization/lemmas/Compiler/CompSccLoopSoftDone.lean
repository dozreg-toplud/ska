import lemmas.Compiler.CompSccIn

/-! # `+soft-done` on any soft map (README Gaps 21.16)

`+soft-done` (line 5292, `sdArm`, 57 cells) is `?: dropping gen`, then the trap over
`~(tap by soft.gen)` that sets `gen` to `(soft-emit i.lis)` at each entry.  Here it is linked
for any soft map that is a tree, with `+soft-emit` a hypothesis: `seCall e` is the formula
`(~(soft-emit comp gen) e)` on the core, and `hE` says it computes `F g e` on the state `g`
(the rest `x` kept). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The trap of `+soft-done`. -/
def sdTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 30)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 0x555c) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))))

theorem sdArm_eq : sdArm =
    (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 1)))) (C (C (A 0) (A 6)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 7678))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) sdTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))) := rfl

/-- `(~(soft-emit comp gen) e)`: the gate of `+soft-emit` (core axis `0x555c`), its sample `e`. -/
def seCall (e : Noun) : Noun :=
  C (A 8) (C (C (A 9) (C (A 0x555c) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 1) e))
    (C (A 0) (A 2)))))))

/-- **The trap of `+soft-done`** over a list `l` of entries: `soft-emit` at each, in order. -/
theorem sd_trap (x : GenRest) (ctx : Noun) (F : Gen (TreapMap mugF) → Noun → Option (Gen (TreapMap mugF)))
    (l0 : List Noun)
    (hE : ∀ g e, e ∈ l0 → nock (compCore g x ctx) (seCall e) = (F g e).map (genNoun · x)) :
    ∀ (l : List Noun), (∀ e ∈ l, e ∈ l0) → ∀ g,
    nock (C sdTrap (C (listN l) (C comp.door (C (genNoun g x) ctx)))) sdTrap = (l.foldlM F g).map (genNoun · x)
  | [], _, g => by
    generalize comp.door = Dr
    simp [sdTrap, nock_exec, listN]
  | e :: l, hl, g => by
    have h1 := hE g e (hl e (List.mem_cons_self ..))
    have ih := fun g' => sd_trap x ctx F l0 hE l (fun e' h' => hl e' (List.mem_cons_of_mem _ h')) g'
    simp only [seCall, compCore] at h1
    generalize comp.door = Dr at h1 ih
    conv => { lhs; arg 2; unfold sdTrap }
    simp [nock_exec] at h1
    simp only [listN] at ih
    have h2 : ∀ a b : Noun, slot? 2 (Noun.cell a b) = some a := fun a b => by
      have : slot? 2 (C a b) = some a := by simp [nock_exec]
      exact this
    simp [nock_exec, listN, h1]
    cases hF : F g e with
    | none => simp [hF, List.foldlM]
    | some g' => simp [hF, List.foldlM, h2, ih]

/-- **`+soft-done` on any soft map**: on a state that is not dropping, with `soft` a tree, the
fold of `+soft-emit` (`hE`) over `~(tap by soft.gen)` (`tapList`, the nodes in reverse order of
the keys). -/
theorem sd_tree (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest)
    (hT : Tree x.soft) (hd : g.drop = false)
    (F : Gen (TreapMap mugF) → Noun → Option (Gen (TreapMap mugF)))
    (hE : ∀ g e, e ∈ tapList x.soft → nock (compCore g x ctx) (seCall e) = (F g e).map (genNoun · x)) :
    nock (compCore g x ctx) sdArm = ((tapList x.soft).foldlM F g).map (genNoun · x) := by
  have hD := comp_drop_at
  have htr := sd_trap x ctx F (tapList x.soft) hE (tapList x.soft) (fun _ h => h)
  have htap := tapF_list hT []
  simp only [List.append_nil] at htap
  have htap' : tapF x.soft (A 0) = some (listN (tapList x.soft)) := htap
  rw [sdArm_eq]
  obtain ⟨c, s, sofs⟩ := x
  simp only at hT htap htap' htr ⊢
  simp only [compCore, genNoun] at htr ⊢
  generalize comp.door = Dr at hD htr
  simp [nock_exec, hd, cgModeNoun, hD, dropArm, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
    by.tap.arm_at, tap_arm, tap_loop]
  rw [htap']
  simpa [cgModeNoun, hd] using htr g

end Compiler
end Formalization
