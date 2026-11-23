import lemmas.Ska.CompModel

/-!
# Lazy needs with forks and bonds

The type `$need-lazy` of `desk/lib/nock-compilation.hoon` in full:

    +$  need-lazy
      $;  |-
      $:  =sure
          fork=(list [y=[o=@uwoo laz=$] n=[o=@uwoo laz=$]])
          bond=(list [o=@uwoo laz=$])
      ==

`CompModel.lean` models a fork-free `need-lazy` by its `sure`.  Here is the
whole type, `Lazy`, with the embedding `Lazy.ofSure` of the fork-free ones
and the predicate `Lazy.forkFree` that says a lazy need is one.  The arms of
`+comp` that walk forks and bonds are modelled over `Lazy` in
`CompLazyArms.lean`, each with a lemma that on `ofSure s` it is the
fork-free model of `CompModel.lean`, so that the theorems about the
fork-free model are corollaries and not a second truth.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

/-- `$need-lazy`: the sure need, the forks (the yes and the no branch, each a
lazy block and the lazy need taken there) and the bonds (a lazy block and the
lazy need taken there). -/
inductive Lazy (S : Type) where
  | mk (sure : Sure S) (fork : List ((Nat × Lazy S) × (Nat × Lazy S))) (bond : List (Nat × Lazy S))

namespace Lazy

variable {S : Type}

def sure : Lazy S → Sure S
  | mk s _ _ => s

def fork : Lazy S → List ((Nat × Lazy S) × (Nat × Lazy S))
  | mk _ f _ => f

def bond : Lazy S → List (Nat × Lazy S)
  | mk _ _ b => b

@[simp] theorem sure_mk (s : Sure S) f b : (mk s f b).sure = s := rfl
@[simp] theorem fork_mk (s : Sure S) f b : (mk s f b).fork = f := rfl
@[simp] theorem bond_mk (s : Sure S) f b : (mk s f b).bond = b := rfl

theorem eta (l : Lazy S) : mk l.sure l.fork l.bond = l := by cases l; rfl

/-- `(lazy-from-need ned)` with looks: `[sure ~ ~]`. -/
def ofSure (s : Sure S) : Lazy S := mk s [] []

/-- No fork and no bond. -/
def forkFree (l : Lazy S) : Prop := l.fork = [] ∧ l.bond = []

theorem forkFree_ofSure (s : Sure S) : forkFree (ofSure s) := ⟨rfl, rfl⟩

theorem eq_ofSure {l : Lazy S} (h : forkFree l) : l = ofSure l.sure := by
  cases l with
  | mk s f b => simp only [forkFree, fork_mk, bond_mk] at h; simp [ofSure, h]

variable [HoonSet S]

mutual
/-- The noun of a `need-lazy`. -/
def toNoun : Lazy S → Noun
  | mk s f b => C s.toNoun (C (forksNoun f) (bondsNoun b))

/-- The noun of its list of forks. -/
def forksNoun : List ((Nat × Lazy S) × (Nat × Lazy S)) → Noun
  | [] => A 0
  | ((oy, ly), (on, ln)) :: rest =>
      C (C (C (A oy) (toNoun ly)) (C (A on) (toNoun ln))) (forksNoun rest)

/-- The noun of its list of bonds. -/
def bondsNoun : List (Nat × Lazy S) → Noun
  | [] => A 0
  | (o, l) :: rest => C (C (A o) (toNoun l)) (bondsNoun rest)
end

/-- On a fork-free need the noun is that of `CompModel.lean`. -/
theorem toNoun_ofSure (s : Sure S) : toNoun (ofSure s) = lazyNoun s := by
  simp [ofSure, toNoun, forksNoun, bondsNoun, lazyNoun]

end Lazy

end Comp
end SkaModel
end Formalization
