import lemmas.Ska.PassStab

/-!
# Candidate measures of the pass loop, stated and tested (track F, Gaps 16)

The measure of `Ska/PassMeasureP.lean` (`B - next`, then the members' entries
pointwise) needs a bound on `next`.  The candidates here compare the members of
a component by their DFS numbers (`order`), the oldest dominating, so that the
fresh pushes of a pass (numbered from `next` on, above every member of its
start) do not count against a fall of an older member.  `passOn_old` gives the
part that holds of every pass: no member present at two starts rises, a culled
one falls to `none`.

* `valE` with `StabLtA`: the oldest member whose entry differs falls.  On the
  compiler (`tools/hoon/passmeasure-stab.py`) it fails at the passes where no
  member of the start falls or is culled but a member reruns with the same
  entry and resolves a site to a new identity: the push follows the fall that
  caused it by one pass (the member read its callee's entry from before that
  callee's change).  In every such pass a member's callee set changed.
* `stabVal` with `StabLt` (candidate D): the value is the entry and whether
  the member is `+dirty`; a rerun with the same entry that leaves the member
  clean is a fall.  README Gaps 16 gives the counts on the traces.

Neither order is well founded by itself: the DFS numbers are not bounded (a
re-push takes a fresh one), and a sequence that falls at ever later numbers
can be infinite.  What a fall at every pass gives is that the value at each DFS
number changes finitely often, so along an infinite chain of passes the first
number that changes tends to infinity; ruling that out needs the finitely many
identities of (i) and the callee sets of the members that stop changing.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **Candidate A**: at the oldest DFS number of the start `st` whose member's
value differs in `st'`, it falls (a member culled falls to `none`). -/
def StabLtA (st' st : SkaState M R) : Prop :=
  ∃ i t, Treap.get st.order i = some t ∧ SkaModel.OLt (valE st' i) (valE st i) ∧
    ∀ j u, Treap.get st.order j = some u → u < t → valE st' j = valE st j

/-- The value of an identity in candidate D: off the stack `none`, else the
tuple of its entry and whether it is `+dirty`. -/
def stabVal (st : SkaState M R) (i : Ident) : Option (M8 × Bool) :=
  if i ∈ st.stk then (gCore st.g i).map (fun d => (entryM i.1 d, dirty i st)) else none

/-- The order of a value of candidate D: `none` lowest, then the entry's tuple,
then a dirty member above a clean one with the same entry. -/
def SvLt : Option (M8 × Bool) → Option (M8 × Bool) → Prop
  | none, some _ => True
  | some (e', b'), some (e, b) => lexM8.rel e' e ∨ (e' = e ∧ b' = false ∧ b = true)
  | _, _ => False

/-- **Candidate D**: at the oldest DFS number of the start `st` whose member's
value (entry, dirty) differs in `st'`, it falls. -/
def StabLt (st' st : SkaState M R) : Prop :=
  ∃ i t, Treap.get st.order i = some t ∧ SvLt (stabVal st' i) (stabVal st i) ∧
    ∀ j u, Treap.get st.order j = some u → u < t → stabVal st' j = stabVal st j

theorem svLt_of_olt {st st' : SkaState M R} {i : Ident} (h : SkaModel.OLt (valE st' i) (valE st i)) :
    SvLt (stabVal st' i) (stabVal st i) := by
  unfold valE at h; unfold stabVal
  by_cases h1 : i ∈ st'.stk <;> by_cases h2 : i ∈ st.stk <;> simp only [h1, h2, if_true, if_false] at h ⊢
  · cases e1 : gCore st'.g i <;> cases e2 : gCore st.g i <;> rw [e1, e2] at h <;>
      simp only [Option.map_none, Option.map_some, SkaModel.OLt, SvLt] at h ⊢
    exact Or.inl h
  · cases e1 : gCore st'.g i <;> rw [e1] at h <;> simp [SkaModel.OLt] at h
  · cases e2 : gCore st.g i <;> rw [e2] at h <;> simp [SkaModel.OLt, SvLt] at h ⊢
  · simp [SkaModel.OLt] at h

/-- A pass that is a fall of candidate A at a member whose entry falls is a
fall of candidate D when the older members keep their dirty flags too. -/
theorem stabLt_of_A {st st' : SkaState M R} {i : Ident} {t : Nat} (ho : Treap.get st.order i = some t)
    (h : SkaModel.OLt (valE st' i) (valE st i))
    (hk : ∀ j u, Treap.get st.order j = some u → u < t → stabVal st' j = stabVal st j) : StabLt st' st :=
  ⟨i, t, ho, svLt_of_olt h, hk⟩

end Ana

end SkaModel
end Formalization
