import lemmas.Ska.RawInvCLSpec
import lemmas.Ska.RawInvKernX

/-!
# The run-level liveness with calls: the pre- and postcondition, the walks

README Gaps 14 (b), track D.  The pair `I` / `J` of `LiveRun` (checked at
every sub-run of every run of `PlainN` in `enumCX` by `RawInvCLCheckIJ.lean`)
and the parts every arm that walks a goal's lazy need uses.

* `GRegL goal r`: `r` is a register of a sure need of the goal's lazy tree.
* `GoalL g goal`: the goal's jumps are `Fresh`; every entry of its lazy tree
  (the root included) has a block with no parameter, and its sure need's
  registers are below `re` and defined by no block; the sure needs of the
  tree are pairwise apart (`NeedsApart`) and each is `Distinct`.
* **`IL K goal g`**: `ATS g`, every block's registers below `re`, every key
  of `cond` below `re`, defined by no block, no goal register, standing for
  a register below `re` that is no key; `KVan K g.bo`; `GoalL g goal`.
  **`JL K nex g`** is `IL K nex.goal g`, so `JL` gives `IL` of the next run
  (`jl_il`, the hypothesis `hJ` of `liveRun_seven`).
* `AddSt g g'`: a step that only adds ops and proxies (same `bo`, `drop`,
  `tags`; `re` grows; `cond` grows by keys from `g.re` on).
* **`walkLazy_prepG`**: a walk whose gate only puts ops in front of the
  entry's block (`GStep`: ops that define the entry's sure need and read
  first only what `R` allows) puts ops `P` in front of the blocks
  (`WalkP`), nonempty only at entries, under any `cond`: the form of
  `kernList_prep` without `KI`.
* **`unpM_prepG`**: the unproxied blocks after such a walk are the old
  unproxied ones with the ops, unproxied by the NEW `cond`, in front (old
  blocks mention only registers below the old `re`, under which `cond` did
  not change).
* `medeLoop_step`, `medeGate_step`, `medeL_walk`: `+mede` as such a walk
  with ops that read nothing; **`liveC_medeL`**: the case `%1` under
  `%next` of the liveness spec.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The pair -/

/-- `r` is a register of a sure need of the goal's lazy tree. -/
def GRegL : CGoalL S → Nat → Prop
  | CGoalL.next laz th, r => ∃ e ∈ (th.there, laz) :: entries laz, NMem e.2.sure.ned r
  | _, _ => False

/-- What the goal asks of the state. -/
def GoalL (g : Comp.Gen Map) : CGoalL S → Prop
  | CGoalL.next laz th => Fresh g th ∧ NeedsApart ((th.there, laz) :: entries laz) ∧
      ∀ e ∈ (th.there, laz) :: entries laz, (∃ b, HoonMap.get g.blocks e.1 = some b ∧ b.par = []) ∧
        Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → r < g.re ∧ ¬ Defd g.blocks r
  | CGoalL.pick z o => Fresh g z ∧ Fresh g o
  | CGoalL.done => True

/-- **The precondition of a run with calls.** -/
structure IL (K : Nat → Nat → Prop) (goal : CGoalL S) (g : Comp.Gen Map) : Prop where
  ats : ATS g
  regs : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b
  cond : ∀ k v, HoonMap.get g.cond k = some v →
    k < g.re ∧ ¬ Defd g.blocks k ∧ ¬ GRegL goal k ∧ v.1 < g.re ∧ HoonMap.get g.cond v.1 = Option.none
  kvan : KVan K g.bo
  goal : GoalL g goal

/-- **The postcondition**: the precondition of a run for the result. -/
def JL (K : Nat → Nat → Prop) (nex : NextL S) (g : Comp.Gen Map) : Prop := IL K nex.goal g

theorem jl_il {K : Nat → Nat → Prop} {nex : NextL S} {g : Comp.Gen Map} (h : JL K nex g) : IL K nex.goal g := h

/-! ## Steps that only add ops and proxies -/

/-- Same `bo`, `drop`, `tags`; `re` grows; `cond` grows by keys from `g.re` on. -/
def AddSt (g g' : Comp.Gen Map) : Prop :=
  g'.bo = g.bo ∧ g'.drop = g.drop ∧ g'.tags = g.tags ∧ g.re ≤ g'.re ∧
    (∀ k v, HoonMap.get g.cond k = some v → HoonMap.get g'.cond k = some v) ∧
    ∀ k v, HoonMap.get g'.cond k = some v → HoonMap.get g.cond k = some v ∨ g.re ≤ k

theorem AddSt.refl (g : Comp.Gen Map) : AddSt g g :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, fun _ _ h => h, fun _ _ h => Or.inl h⟩

theorem AddSt.trans {a b c : Comp.Gen Map} (h1 : AddSt a b) (h2 : AddSt b c) : AddSt a c := by
  obtain ⟨b1, d1, t1, r1, c1, n1⟩ := h1
  obtain ⟨b2, d2, t2, r2, c2, n2⟩ := h2
  refine ⟨b2.trans b1, d2.trans d1, t2.trans t1, Nat.le_trans r1 r2, fun k v h => c2 k v (c1 k v h),
    fun k v h => ?_⟩
  rcases n2 k v h with h | h
  · rcases n1 k v h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inr (Nat.le_trans r1 h)

/-- **`cond` below the old `re` is the old one** after an `AddSt` step. -/
theorem AddSt.cond_below {g g' : Comp.Gen Map} (h : AddSt g g') {x : Nat} (hx : x < g.re) :
    HoonMap.get g'.cond x = HoonMap.get g.cond x := by
  obtain ⟨-, -, -, -, c, n⟩ := h
  cases e : HoonMap.get g.cond x with
  | some v => exact c x v e
  | none =>
    cases e' : HoonMap.get g'.cond x with
    | none => rfl
    | some v =>
      rcases n x v e' with h | h
      · rw [e] at h; cases h
      · omega

/-! ## Walks whose gate only puts ops in front -/

/-- What one gate does at `x` for the sure need `s`: ops `A` in front of the
block at `x` that define the need and read first only what `R` allows. -/
def GStep (R : Comp.Gen Map → Nat → Prop) (x : Nat) (s : Sure S) (g g' : Comp.Gen Map) : Prop :=
  ∃ A, Prep (fun k => if k = x then A else []) g.blocks g'.blocks ∧ (∀ r, NMem s.ned r → r ∈ defsOf A) ∧
    ∀ y, OpsRF A y → R g' y

/-- What a walk over the entries `es` does. -/
def WalkP (R : Comp.Gen Map → Nat → Prop) (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map) : Prop :=
  ∃ P, Prep P g.blocks g'.blocks ∧ (∀ e ∈ es, ∀ r, NMem e.2.sure.ned r → r ∈ defsOf (P e.1)) ∧
    (∀ k y, OpsRF (P k) y → R g' y) ∧ ∀ k, P k ≠ [] → ∃ e ∈ es, e.1 = k

/-- **A walk over a list of entries whose gate only puts ops in front.** -/
theorem walkList_prepG {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {g0 : Comp.Gen Map}
    (hf : ∀ x s g g', St g0 g → f x s g = some ((), g') → St g g' ∧ GStep R x s g g') :
    ∀ (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map), St g0 g → walkList f es g = some ((), g') →
      St g g' ∧ WalkP R es g g'
  | [], g, g', _, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hrf g, fun _ => [], prep_nil _, fun e he => absurd he List.not_mem_nil, fun _ _ h => h.elim,
      fun _ h => absurd rfl h⟩
  | (x, l) :: rest, g, g', h0, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨s1, A, pA, kA, rA⟩ := hf x l.sure g g1 h0 h1
    obtain ⟨s2, Q, pQ, kQ, rQ, eQ⟩ := walkList_prepG hrf htr hR hf rest g1 g' (htr _ _ _ h0 s1) h2
    refine ⟨htr _ _ _ s1 s2, _, prep_trans pA pQ, fun e he r hr => ?_, fun k y hy => ?_, fun k hk => ?_⟩
    · rw [defsOf_append, List.mem_append]
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr (by simp only [if_pos rfl]; exact kA r hr)
      · exact Or.inl (kQ e he r hr)
    · rcases opsRF_append.mp hy with h | ⟨-, h⟩
      · exact rQ k y h
      · by_cases e : k = x
        · rw [if_pos e] at h
          exact hR _ _ _ s2 (rA y h)
        · rw [if_neg e] at h; exact h.elim
    · by_cases e : k = x
      · exact ⟨(x, l), List.mem_cons_self, e.symm⟩
      · have : Q k ≠ [] := by
          intro hq; apply hk; simp [hq, e]
        obtain ⟨e', he', ee⟩ := eQ k this
        exact ⟨e', List.mem_cons_of_mem _ he', ee⟩

/-- **A walk of the lazy tree whose gate only puts ops in front**: ops in
front of the root's and the entries' blocks, each defining the sure needs
of the entries at its label, nonempty only at the tree's labels. -/
theorem walkLazy_prepG {f : Nat → Sure S → CM Map Unit} {St : Comp.Gen Map → Comp.Gen Map → Prop}
    (hrf : ∀ a, St a a) (htr : ∀ a b c, St a b → St b c → St a c) {R : Comp.Gen Map → Nat → Prop}
    (hR : ∀ a b y, St a b → R a y → R b y) {g0 : Comp.Gen Map}
    (hf : ∀ x s g g', St g0 g → f x s g = some ((), g') → St g g' ∧ GStep R x s g g')
    {o : Nat} {l : Lazy S} {g' : Comp.Gen Map} (h : walkLazy f o l g0 = some ((), g')) :
    St g0 g' ∧ WalkP R ((o, l) :: entries l) g0 g' := by
  have e : (walkLazy f o l : CM Map Unit) = walkList f ((o, l) :: wentries l) := by
    rw [walkLazy_flat]; rfl
  rw [e] at h
  obtain ⟨s, P, pP, kP, rP, eP⟩ := walkList_prepG hrf htr hR hf _ g0 g' (hrf g0) h
  have hm : ∀ e, e ∈ (o, l) :: entries l ↔ e ∈ (o, l) :: wentries l := fun e =>
    ((wentries_perm l).cons (o, l)).mem_iff.symm
  refine ⟨s, P, pP, fun e he => kP e ((hm e).mp he), rP, fun k hk => ?_⟩
  obtain ⟨e, he, ee⟩ := eP k hk
  exact ⟨e, (hm e).mpr he, ee⟩

end Raw
end SkaModel
end Formalization
