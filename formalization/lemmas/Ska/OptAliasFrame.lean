import lemmas.Ska.OptAliasEdge

/-!
# What a step of the walk of `+alias` leaves alone

The walk invariant over executions compares the state when a block `o` is
walked with the state at the end of the predecessor `q` the execution came
from; the blocks walked in between change `old` only at the destinations of
their ops, and the stored facts, immediates and new blocks only at their own
labels.  **`awk_op_old`**, **`awk_body_old`**: an op (a body) changes `old`
only at its destination (their destinations); **`awk_block`** and
**`awk_walk`**: a block (a part of `topo`) changes `old` only at the
destinations of its ops (of their ops), and `info`, `imms`, `new` only at its
label (their labels).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- **An op changes `old` only at its destination.** -/
theorem awk_op_old {pick : List Nat → Nat} {st st2 : ABody} {op : Pole} {res : Option Pole}
    (h : aliasOp pick st op = some (res, st2)) (x : Nat) (hx : aliasDst op ≠ some x) : st2.old x = st.old x := by
  have drop : ∀ d y, aliasDst op = some d → st2.old = updA st.old d y → st2.old x = st.old x :=
    fun d y hd e => by rw [e]; exact as_upd_other _ _ (fun e' => hx (by rw [hd, e']))
  have same : st2.old = st.old → st2.old x = st.old x := fun e => by rw [e]
  cases op
  case imm n d =>
    simp only [aliasOp] at h
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h)
    · exact drop d _ rfl rfl
    · exact same rfl
  case mov s d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact drop d _ rfl rfl
  case inc s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact drop d _ rfl rfl
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
  case con h0 t0 d =>
    simp only [aliasOp] at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact drop d _ rfl rfl
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
  case hed s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact drop d _ rfl rfl
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
  case tal s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact drop d _ rfl rfl
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
  case cel p =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
  case lob p =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl
  case equ l r =>
    simp only [aliasOp] at h
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl)
  all_goals (simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact same rfl)

/-- **A body changes `old` only at the destinations of its ops.** -/
theorem awk_body_old {pick : List Nat → Nat} : ∀ (ops : List Pole) (st : ABody) (out : List Pole) (st' : ABody),
    aliasBody pick ops st = some (out, st') → ∀ x, x ∉ ops.filterMap aliasDst → st'.old x = st.old x
  | [], st, out, st', h, x, _ => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | op :: l, st, out, st', h, x, hx => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have hx1 : aliasDst op ≠ some x := fun e => hx (by simp [e])
    have hx2 : x ∉ l.filterMap aliasDst := fun hm => hx (by
      rw [List.filterMap_cons]; split
      · exact hm
      · exact List.mem_cons_of_mem _ hm)
    rw [awk_body_old l st1 out2 st2 h2 x hx2, awk_op_old h1 x hx1]

/-- **A block of the walk changes `old` only at the destinations of its ops,
and the stored facts, immediates and new blocks only at its label.** -/
theorem awk_block {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') :
    (∀ x, (∀ b, HoonMap.get bl o = some b → x ∉ b.body.filterMap aliasDst) → g'.old x = g.old x) ∧
    (∀ k, k ≠ o → g'.info k = g.info k ∧ g'.imms k = g.imms k ∧ HoonMap.get g'.new k = HoonMap.get g.new k) := by
  unfold aliasBlock at h
  dsimp only at h
  split at h
  · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  · obtain ⟨info, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨imms, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨edges, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨loc0, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rb, hrb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rf, -, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨fun x hx => awk_body_old b.body _ rb.1 rb.2 hrb x (hx b hb), fun k hk => ⟨?_, ?_, ?_⟩⟩
    · exact as_upd_other _ _ hk
    · exact as_upd_other _ _ hk
    · simp only [HoonMap.get_put, hk, if_false]

/-- **A part of `topo` walked changes `old` only at the destinations of the
ops of its blocks, and the stored facts, immediates and new blocks only at its
labels.** -/
theorem awk_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} : ∀ (l : List Nat) (g g' : AGen Map),
    aliasWalk pick nargs bl l g = some g' →
    (∀ x, (∀ o ∈ l, ∀ b, HoonMap.get bl o = some b → x ∉ b.body.filterMap aliasDst) → g'.old x = g.old x) ∧
    (∀ k, k ∉ l → g'.info k = g.info k ∧ g'.imms k = g.imms k ∧ HoonMap.get g'.new k = HoonMap.get g.new k)
  | [], g, g', h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  | o :: l, g, g', h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a1, a2⟩ := awk_block h1
    obtain ⟨w1, w2⟩ := awk_walk l g1 g' h
    refine ⟨fun x hx => ?_, fun k hk => ?_⟩
    · rw [w1 x (fun o' ho' => hx o' (List.mem_cons_of_mem _ ho')), a1 x (hx o List.mem_cons_self)]
    · have hko : k ≠ o := fun e => hk (by rw [e]; exact List.mem_cons_self)
      have hkl : k ∉ l := fun e => hk (List.mem_cons_of_mem _ e)
      obtain ⟨b1, b2, b3⟩ := w2 k hkl
      obtain ⟨c1, c2, c3⟩ := a2 k hko
      exact ⟨b1.trans c1, b2.trans c2, b3.trans c3⟩

/-- The real reads of an end are among its registers. -/
theorem awk_finReads_sub {fin : Termin} {x : Nat} (h : x ∈ Path.finReads fin) : x ∈ finRegs fin := by
  cases fin <;> simp only [Path.finReads, finRegs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  all_goals first | exact h | (rcases h with h | h <;> simp [h]) | (exact Or.inl h) | (cases h)

section
variable [MapKeys Map]

/-- **The registers an end reads are defined before it** on a path from `0`:
in `PathDef` or by an op of the block, read somewhere reachable (so in
`ClR`), with every dead fill in the block itself (from `DefFirst` at the place
`|body|`), which is what `afn_jump` and `afn_end` need of `Done` at a block's
end. -/
theorem awk_fin_ssa {bl : Map Blob} (hS : AliasSSAB bl) {o : Nat} {p : List Nat} {b : Blob}
    (hπ : BPath bl (o :: p)) (hb : HoonMap.get bl o = some b) {x : Nat} (hx : x ∈ finRegs b.fin) :
    (PathDef bl p b x ∨ x ∈ b.body.filterMap aliasDst) ∧ ClR bl x ∧ ∀ o' i, DeadFill bl x o' i → o' = o := by
  have hR : Reach bl o := ssk_bpath_reach hπ o (List.mem_cons_self ..)
  have hread : ReadAt b b.body.length x := Or.inr ⟨rfl, hx⟩
  refine ⟨?_, Or.inr ⟨o, b, _, hR, hb, hread⟩, fun o' i ⟨_, _, _, _, _, hreads⟩ =>
    (hreads o b _ hR hb hread).1.symm⟩
  by_cases hx' : x ∈ allDefs bl
  · rcases hS.2 o p b hπ hb b.body.length x (Or.inr ⟨rfl, hx⟩) hx' with h | h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · rw [List.take_length] at h; exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inl (Or.inl hx')

end

end Opt
end SkaModel
end Formalization
