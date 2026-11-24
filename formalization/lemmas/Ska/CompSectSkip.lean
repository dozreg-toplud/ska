import lemmas.Ska.CompSixNextCond
import lemmas.Ska.CompSixNextRun

/-!
# The threading of `+sect` when every proxy of the branches stays inside

README Gaps 12.2 (eighth session), a first piece of `%6` under a fork-free
`%next` with branches that make proxies.  `sectThread` folds `sectStep`
over the keys the branches made (`made-0`, `made-1`); a step skips a key
whose tag names the branches' region id `rid`.  When every step skips, the
accumulator is the start one, so the join keeps its parameters and the two
ends their arguments, and the threading puts every block back as it was and
leaves `cond` (`sectThread_skip`).

* `sectStep_skip`, `foldlM_sectStep_skip`: steps that skip.
* `sectThread_skip`: `SameBlocks` of the threading when every key the
  branches made has a tag that names `rid`.
* `sect_specV`: `sect_spec` under that hypothesis in place of an unchanged
  `cond`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- A step of `+sect` over a key that is no key of `made`, or whose tag
names `rid`, changes nothing. -/
theorem sectStep_skip {rid : Nat} {yes : Bool} {made : Map (Nat × List Nat)} {acc : SectAcc Map} {k : Nat}
    (h : ∀ df tag, HoonMap.get made k = some (df, tag) → rid ∈ tag) (g : Gen Map) :
    sectStep rid yes made acc k g = some (acc, g) := by
  unfold sectStep
  cases e : HoonMap.get made k with
  | none => rfl
  | some v =>
    obtain ⟨df, tag⟩ := v
    have ht : tag.any (· == rid) = true := List.any_eq_true.mpr ⟨rid, h df tag e, by simp⟩
    simp only [ht, if_true]

/-- **A fold of steps of `+sect` that all skip** returns the start
accumulator and state. -/
theorem foldlM_sectStep_skip {rid : Nat} {yes : Bool} {made : Map (Nat × List Nat)} :
    ∀ (ks : List Nat) (acc : SectAcc Map) (g : Gen Map),
    (∀ k ∈ ks, ∀ df tag, HoonMap.get made k = some (df, tag) → rid ∈ tag) →
    (ks.foldlM (sectStep rid yes made) acc : CM Map (SectAcc Map)) g = some (acc, g)
  | [], acc, g, _ => rfl
  | k :: ks, acc, g, h => by
    rw [List.foldlM_cons, bind_apply, sectStep_skip (fun df tag e => h k (List.mem_cons_self ..) df tag e) g]
    exact foldlM_sectStep_skip ks acc g (fun k' hk => h k' (List.mem_cons_of_mem _ hk))

/-- **The threading of `+sect` keeps the blocks and `cond`** when every key
the branches made (`made-0` and `made-1`) has a tag that names the
branches' region id `rid`. -/
theorem sectThread_skip {rid o0 o1 : Nat} {cb cw : Map (Nat × List Nat)} {g g' : Gen Map} {u : Unit}
    (h0 : ∀ k df tag, HoonMap.get (difM g.cond cw) k = some (df, tag) → rid ∈ tag)
    (h1 : ∀ k df tag, HoonMap.get (difM cw cb) k = some (df, tag) → rid ∈ tag)
    (h : sectThread rid o0 o1 cb cw g = some (u, g')) : SameBlocks g g' := by
  unfold sectThread at h
  obtain ⟨b0, e0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b1, e1, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i t0 t1 f0 f1
    split at h
    · cases h
    · obtain ⟨bt, et, h⟩ := Option.bind_eq_some_iff.mp h
      rw [bind_apply, foldlM_sectStep_skip _ _ _ (fun k _ => h0 k)] at h
      simp only [Option.bind_some] at h
      rw [bind_apply, foldlM_sectStep_skip _ _ _ (fun k _ => h1 k)] at h
      simp only [Option.bind_some] at h
      obtain ⟨_, g1, j1, h⟩ := bind_some h
      obtain ⟨_, g2, j2, j3⟩ := bind_some h
      have S1 := jabBlock_same (fun b hb => by rw [et] at hb; cases hb; rfl) j1
      have L0 : lensHop t0.args b0 = some b0 := by
        rcases b0 with ⟨p0, bd0, fn0⟩
        simp only at f0
        subst f0
        rfl
      have L1 : lensHop t1.args b1 = some b1 := by
        rcases b1 with ⟨p1, bd1, fn1⟩
        simp only at f1
        subst f1
        rfl
      have S2 := jabBlock_same (fun b hb => by rw [S1.2.2.2.2.2.2 o0, e0] at hb; cases hb; exact L0) j2
      have S3 := jabBlock_same (fun b hb => by
        rw [S2.2.2.2.2.2.2 o1, S1.2.2.2.2.2.2 o1, e1] at hb; cases hb; exact L1) j3
      exact S1.trans (S2.trans S3)
  · cases h

/-- **`+sect` when every proxy the branches made stays inside**: every key
they made (`made-0`, `made-1`) has a tag that names the region id `rid`
of `rb`; then, as in `sect_spec`, the two lazy blocks at the next labels,
tagged, and the blocks otherwise and `cond` as they were. -/
theorem sect_specV {nex0 nex1 : NextL S} {o0 o1 : Nat} {rb : List Nat} {cb cw : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat} (hd : g.drop = false)
    (h0 : ∀ rid rest, rb = rid :: rest → ∀ k df tag, HoonMap.get (difM g.cond cw) k = some (df, tag) → rid ∈ tag)
    (h1 : ∀ rid rest, rb = rid :: rest → ∀ k df tag, HoonMap.get (difM cw cb) k = some (df, tag) → rid ∈ tag)
    (h : sect nex0 nex1 o0 o1 rb cb cw g = some ((lz, yes, nuh), g')) :
    yes = g.bo ∧ nuh = g.bo + 1 ∧ nex0.th.args = [] ∧ nex1.th.args = [] ∧
    lz = mk Sure.bunt [((g.bo, nex0.laz), (g.bo + 1, nex1.laz))] [] ∧
    SameBlocks (sixGenL g nex0.th nex1.th rb) g' := by
  unfold sect at h
  split at h
  · cases h
  · rename_i rid rest
    obtain ⟨o0b, g1, h1, h⟩ := bind_some h
    obtain ⟨o1b, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    obtain ⟨_, g4, h4, h⟩ := bind_some h
    obtain ⟨g5, g5', h5, h⟩ := bind_some h
    simp only [get, Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    rw [emit_apply] at h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    rw [setTag_apply] at h3 h4
    simp only [Option.some.injEq, Prod.mk.injEq] at h3 h4
    obtain ⟨_, rfl⟩ := h3
    obtain ⟨_, rfl⟩ := h4
    have e4 : (((g.emitted ⟨[], [], Termin.hop nex0.th⟩).emitted ⟨[], [], Termin.hop nex1.th⟩).tagged
        g.bo (rid :: rest)).tagged (g.emitted ⟨[], [], Termin.hop nex0.th⟩).bo (rid :: rest) =
        sixGenL g nex0.th nex1.th (rid :: rest) := rfl
    rw [e4] at h
    dsimp only at h
    have d4 : (sixGenL g nex0.th nex1.th (rid :: rest)).drop = false := by simp [hd]
    rw [if_neg (by rw [d4]; simp)] at h
    obtain ⟨u, g6, h6, h⟩ := bind_some h
    have S6 := sectThread_skip (fun k df tag e => h0 rid rest rfl k df tag (by rwa [sixGenL_cond] at e))
      (h1 rid rest rfl) h6
    revert h; split
    · intro h; cases h
    · rename_i a0
      split
      · intro h; cases h
      · rename_i a1
        intro h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        simp only [ne_eq, Decidable.not_not] at a0 a1
        exact ⟨rfl, rfl, a0, a1, rfl, S6⟩

end Comp
end SkaModel
end Formalization
