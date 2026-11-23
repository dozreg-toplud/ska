import lemmas.Compiler.EvalRend

/-!
# The list mold of layer 1

`;;((list) n)` of `+eval-rend` slams the mold that `+list` (axis `1407` of
layer 1) builds with its default item, the mold `*`.  The mold is a loop over
the list that slams the item mold on each head and builds the mold again for
the tail by pulling `+list` from layer 1; it ends on `~` and crashes on any
other atom.  So it returns `n` on a list and crashes otherwise
(`listMoldIs`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- The battery of the default item mold, `*`: it returns its sample. -/
def itemBat : Noun :=
  C (A 8) (C (C (A 0) (A 6)) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6)))))

/-- The battery of the mold `(list item)`. -/
def moldBat : Noun :=
  C (A 8) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (C (A 8) (C (C (A 0) (A 30)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 8) (C (C (A 9) (C (A 1407) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 0) (A 0)))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6)))))

/-- The battery of the mold builder `+list`. -/
def builderBat : Noun :=
  C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) moldBat) (C (A 0) (A 1))))

/-- The arm `+list`: the default item, then the builder. -/
def listArm : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) itemBat) (C (A 0) (A 1)))))
    (C (C (A 1) builderBat) (C (A 0) (A 1))))

theorem layer1_list : slot? 1407 layer1 = some listArm := by kernel_rfl

/-- The builder over the default item, in layer 1. -/
abbrev listB : Noun := C builderBat (C (C itemBat (C (A 0) layer1)) layer1)

theorem item_run (h c : Noun) : nock (C itemBat (C h c)) itemBat = some h := by
  nock_open itemBat; simp [nock_exec]

theorem builder_run (s c : Noun) :
    nock (C builderBat (C s c)) builderBat = some (C moldBat (C (A 0) (C builderBat (C s c)))) := by
  nock_open builderBat; simp [nock_exec]

theorem list_arm_run : nock layer1 listArm = some listB := by
  unfold listArm; simp [nock_exec]

theorem mold_run : ∀ n, nock (C moldBat (C n listB)) moldBat = (nounList? n).map (listNoun id)
  | Noun.atom a => by
    nock_open moldBat
    by_cases h : a = 0
    · subst h; simp [nock_exec, nounList?, listNoun]
    · have h' : ¬ (0 = a) := fun e => h e.symm
      simp [nock_exec, nounList?, h, h']
  | Noun.cell h t => by
    have ih := mold_run t
    nock_open moldBat
    simp only [nock_exec, item_run, layer1_list, list_arm_run, builder_run, Option.bind_some]
    rw [ih]
    cases e : nounList? t <;> simp [nounList?, listNoun, e]

theorem listMoldIs : ListMoldIs := by
  intro n
  have := mold_run n
  simp [listMoldF, nock_exec, layer1_list, list_arm_run, builder_run, this]

end Compiler
end Formalization
