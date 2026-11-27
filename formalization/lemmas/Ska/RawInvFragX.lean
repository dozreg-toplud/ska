import lemmas.Ska.RawInvInto

/-!
# Raw `+comp` output: runs of the first fragment inside `FragX`

README Gaps 14, track D, step 1 of the class `FragX`.  In a nomm of `FragX`
a run of the first fragment (`run`, through `runL_frag`) may start after a
`%6` under `%next` has emitted its code: fork blocks that hop up to the
join, and a join with several parameters, so the start state has no `SI`.

* `SIP X (upRk g.blocks) g.bo g`: the state invariant in the rank `upRk`
  of the state's own blocks (`3 t + 1` at a block that hops up to `t`, `3 k`
  elsewhere), with every label from `g.bo` on ranked `3 k` and every block
  that hops up hopping below `g.bo` (`rlo`).  It holds of a state whose
  blocks hop up as `%6` makes them, and it asks nothing of the parameters.
* **`run_rawU`**: a run of the first fragment from such a state keeps it,
  in the rank of the end state's blocks, and leaves live at its entry only
  its result's need and what its goal's continuation needs beyond the goal
  (`run_rawP` with `ρ := upRk g0.blocks`, `lo := g0.bo`; the ranks of the
  end state are those of the start, `upRk_congr`, since the run keeps the
  terminators of the old blocks, `run_down`, and its new blocks do not hop
  up, as they go down in a rank that is `3 k` on them).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X]

/-- `upRk` at a label depends only on the terminator of its block. -/
theorem upRk_congr {bl bl' : Map Blob} {k : Nat}
    (h : (HoonMap.get bl k).map Blob.fin = (HoonMap.get bl' k).map Blob.fin) : upRk bl k = upRk bl' k := by
  unfold upRk
  cases e : HoonMap.get bl k with
  | none =>
    cases e' : HoonMap.get bl' k with
    | none => rfl
    | some b' => rw [e, e'] at h; cases h
  | some b =>
    cases e' : HoonMap.get bl' k with
    | none => rw [e, e'] at h; cases h
    | some b' =>
      rw [e, e'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨p, bd, f⟩ := b
      obtain ⟨p', bd', f'⟩ := b'
      simp only at h
      subst h
      cases f <;> rfl

/-- **A run of the first fragment from a state whose blocks may hop up**,
with liveness over kills `K` at the old labels (below `g0.bo`). -/
theorem run_rawUK {K : Nat → Nat → Prop} {nm : Nomm} {goal : CGoal S} {g0 g1 : Comp.Gen Map} {nex : Next S}
    [KVan K g0.bo]
    (h : SIP X (upRk g0.blocks) g0.bo g0) (hg : GoalIn g0.re goal) (hD : GDist goal) (hj : GJ g0.bo goal)
    (ha : GArgs goal) (hf : ∀ r, Defd g0.blocks r → ¬ GMem goal r) (hr : run nm goal g0 = some (nex, g1)) :
    SIP X (upRk g1.blocks) g1.bo g1 ∧
      ∀ r, LiveK g1.blocks K nex.th.there r → NMem nex.laz.ned r ∨ GLiveK g0.blocks K goal r := by
  obtain ⟨S1, L1⟩ := run_rawPK (K := K) nm goal g0 g1 nex h hg hD hj ha hf hr
  have G := (run_down nm goal g0 g1 nex hj h.bo1 h.drop hr).grow
  have hbo := G.bo
  have E : ∀ k, upRk g1.blocks k = upRk g0.blocks k := by
    intro k
    by_cases hk : k < g0.bo
    · apply upRk_congr
      cases e1 : HoonMap.get g1.blocks k with
      | none =>
        cases e0 : HoonMap.get g0.blocks k with
        | none => rfl
        | some b => obtain ⟨b', h', -, -⟩ := G.keep k b hk e0; rw [e1] at h'; cases h'
      | some b' =>
        rcases G.new k b' e1 with ⟨b, e0, -, hf'⟩ | ⟨hlo, -, -⟩
        · rw [e0]; simp [hf']
        · omega
    · have n0 := h.none (Nat.le_of_not_lt hk)
      have r0 : upRk g0.blocks k = 3 * k := by unfold upRk; rw [n0]
      rw [r0]
      unfold upRk
      cases e1 : HoonMap.get g1.blocks k with
      | none => rfl
      | some b =>
        obtain ⟨p, bd, f⟩ := b
        cases f with
        | hop j =>
          simp only
          split
          · rename_i hlt
            have := S1.jr k _ e1 j (by simp [getJmps])
            rw [h.rk k (by omega), h.rk j.there (by omega)] at this
            omega
          · rfl
        | _ => rfl
  refine ⟨⟨S1.drop, S1.bo1, S1.lab, S1.regs, S1.nd, S1.cr, S1.tr, fun k b hb j hj => by
      rw [E, E]; exact S1.jr k b hb j hj, Nat.le_refl _, fun k hk => ?_, fun x hx => ?_, S1.x⟩, L1⟩
  · rw [E]; exact h.rk k (by omega)
  · rw [E]
    by_cases e : x < g0.bo
    · have := h.rlo x e; omega
    · rw [h.rk x (by omega)]; omega

/-- **A run of the first fragment from a state whose blocks may hop up.** -/
theorem run_rawU {nm : Nomm} {goal : CGoal S} {g0 g1 : Comp.Gen Map} {nex : Next S}
    (h : SIP X (upRk g0.blocks) g0.bo g0) (hg : GoalIn g0.re goal) (hD : GDist goal) (hj : GJ g0.bo goal)
    (ha : GArgs goal) (hf : ∀ r, Defd g0.blocks r → ¬ GMem goal r) (hr : run nm goal g0 = some (nex, g1)) :
    SIP X (upRk g1.blocks) g1.bo g1 ∧
      ∀ r, Live g1.blocks nex.th.there r → NMem nex.laz.ned r ∨ GLive g0.blocks goal r := by
  obtain ⟨S1, L1⟩ := run_rawUK (K := fun _ _ => False) h hg hD hj ha hf hr
  exact ⟨S1, fun r hl => (L1 r (liveK_of_live hl)).imp id gLiveK_none.mp⟩

end Raw
end SkaModel
end Formalization
