import lemmas.Ska.CompLazy
import lemmas.Ska.CompSem

/-!
# The arms of `+comp` that walk forks and bonds

Each arm of `desk/lib/nock-compilation.hoon` that reads or rebuilds the forks
and bonds of a `need-lazy`, over `Lazy`, with the arm's name, its case
order and its order of allocations.  The recursion of the Hoon through the
lists of forks and bonds (`turn`, `roll`, `levy`, `murn`, `spin`,
`spin-split`) is a mutual recursion over the lists here, in the same order.

Each arm has a lemma `*_ofSure`: on a fork-free need it is the arm of
`CompModel.lean`.

The soft map.  `+soft-less` drops the bonds at blocks of `soft.gen`, which
only the compilation of direct calls fills.  `Gen` has no `soft`; the arm
takes the membership test as a parameter `soft`, and `run` hands it
`noSoft`, the test of the empty map.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

namespace Lazy

/-! ## Tests and sizes -/

/-- `+lazy-empty`. -/
def lazyEmpty (l : Lazy S) : Bool :=
  decide (l.sure.ned = Need.none) && HoonSet.small l.sure.lok && l.fork.isEmpty && l.bond.isEmpty

/-- `+lazy-prune`: the forks whose two needs are empty and the empty bonds
are dropped. -/
def lazyPrune (l : Lazy S) : Lazy S :=
  mk l.sure (l.fork.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2))
    (l.bond.filter fun e => !(lazyEmpty e.2))

theorem lazyPrune_ofSure (s : Sure S) : lazyPrune (ofSure s) = ofSure s := rfl

mutual
/-- `+none-equivalent`. -/
def noneEquivalentL : Lazy S → Bool
  | mk s f b => decide (s.ned = Need.none) && HoonSet.small s.lok && noneForks f && noneBonds b

/-- The `levy` over the forks. -/
def noneForks : List ((Nat × Lazy S) × (Nat × Lazy S)) → Bool
  | [] => true
  | ((_, a), (_, b)) :: rest => (noneEquivalentL a && noneEquivalentL b) && noneForks rest

/-- The `levy` over the bonds. -/
def noneBonds : List (Nat × Lazy S) → Bool
  | [] => true
  | (_, n) :: rest => noneEquivalentL n && noneBonds rest
end

theorem noneEquivalentL_ofSure (s : Sure S) : noneEquivalentL (ofSure s) = noneEquivalent s := by
  simp [ofSure, noneEquivalentL, noneForks, noneBonds, noneEquivalent]

/-- `+lazy-max`. -/
def lazyMax : Nat := 512

mutual
/-- The trap of `+lazy-size` from the count `c`. -/
def lazySizeGo (c : Nat) : Lazy S → Nat
  | mk _ f b => if c > lazyMax then c else sizeBonds (sizeForks (c + 1) f) b

/-- Its loop over the forks. -/
def sizeForks (c : Nat) : List ((Nat × Lazy S) × (Nat × Lazy S)) → Nat
  | [] => c
  | ((_, y), (_, n)) :: rest => sizeForks (lazySizeGo (lazySizeGo c y) n) rest

/-- Its loop over the bonds. -/
def sizeBonds (c : Nat) : List (Nat × Lazy S) → Nat
  | [] => c
  | (_, l) :: rest => sizeBonds (lazySizeGo c l) rest
end

/-- `+lazy-size`. -/
def lazySize (l : Lazy S) : Nat := lazySizeGo 0 l

/-- `+lazy-big`. -/
def lazyBig (l : Lazy S) : Bool := decide (lazySize l > lazyMax)

/-- A fork-free need is not big. -/
theorem lazyBig_ofSure (s : Sure S) : lazyBig (ofSure s) = false := by
  simp [lazyBig, lazySize, ofSure, lazySizeGo, sizeForks, sizeBonds, lazyMax]

mutual
/-- `+soft-less`, with `(~(has by soft.gen) o)` as `soft o`. -/
def softLess (soft : Nat → Bool) : Lazy S → Lazy S
  | mk s f b => if f.isEmpty && b.isEmpty then mk s f b else mk s (softForks soft f) (softBonds soft b)

/-- Its `turn` over the forks. -/
def softForks (soft : Nat → Bool) : List ((Nat × Lazy S) × (Nat × Lazy S)) →
    List ((Nat × Lazy S) × (Nat × Lazy S))
  | [] => []
  | ((oy, y), (on, n)) :: rest => ((oy, softLess soft y), (on, softLess soft n)) :: softForks soft rest

/-- Its `murn` over the bonds. -/
def softBonds (soft : Nat → Bool) : List (Nat × Lazy S) → List (Nat × Lazy S)
  | [] => []
  | (o, l) :: rest => if soft o then softBonds soft rest else (o, softLess soft l) :: softBonds soft rest
end

/-- The test of an empty `soft.gen`. -/
def noSoft : Nat → Bool := fun _ => false

mutual
theorem softLess_noSoft : ∀ (l : Lazy S), softLess noSoft l = l
  | mk s f b => by
    unfold softLess
    split
    · rfl
    · rw [softForks_noSoft f, softBonds_noSoft b]

theorem softForks_noSoft : ∀ (f : List ((Nat × Lazy S) × (Nat × Lazy S))), softForks noSoft f = f
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [softForks]; rw [softLess_noSoft y, softLess_noSoft n, softForks_noSoft rest]

theorem softBonds_noSoft : ∀ (b : List (Nat × Lazy S)), softBonds noSoft b = b
  | [] => rfl
  | (o, l) :: rest => by
    simp only [softBonds, noSoft, Bool.false_eq_true, if_false]
    rw [softLess_noSoft l, softBonds_noSoft rest]
end

/-- `+past-fork`: when the test `nom` is hinted, each branch's need is bound
where the branch begins.  `none` where `+hinted` crashes. -/
def pastFork (cod : Bell → Option Bool) (laz : Lazy S) (nom : Nomm) : Option (Lazy S) :=
  match hinted cod nom with
  | Option.none => Option.none
  | some false => some laz
  | some true => some (mk laz.sure
      (laz.fork.map fun e => ((e.1.1, mk Sure.bunt [] [(e.1.1, e.1.2)]), (e.2.1, mk Sure.bunt [] [(e.2.1, e.2.2)])))
      laz.bond)

theorem pastFork_pure (cod : Bell → Option Bool) (laz : Lazy S) {nom : Nomm} (h : nom.pure = true) :
    pastFork cod laz nom = some laz := by
  simp [pastFork, hinted_pure cod nom h]

/-! ## `+walk-lazy` -/

mutual
/-- `+walk-lazy`: the gate `f` on the sure need of `laz` at block `o`, then
on every fork's two needs at their blocks, then on every bond's. -/
def walkLazy (f : Nat → Sure S → CM Map Unit) : Nat → Lazy S → CM Map Unit
  | o, mk s fk bd => do
    f o s
    if fk.isEmpty && bd.isEmpty then pure () else do
    walkForks f fk
    walkBonds f bd

/-- The `roll` over the forks. -/
def walkForks (f : Nat → Sure S → CM Map Unit) : List ((Nat × Lazy S) × (Nat × Lazy S)) → CM Map Unit
  | [] => pure ()
  | ((oy, y), (on, n)) :: rest => do
    walkLazy f oy y
    walkLazy f on n
    walkForks f rest

/-- The `roll` over the bonds. -/
def walkBonds (f : Nat → Sure S → CM Map Unit) : List (Nat × Lazy S) → CM Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    walkLazy f o l
    walkBonds f rest
end

theorem walkLazy_ofSure (f : Nat → Sure S → CM Map Unit) (o : Nat) (s : Sure S) :
    (walkLazy f o (ofSure s) : CM Map Unit) = (do f o s; pure ()) := by
  simp [walkLazy, ofSure]

/-! ## `+from` -/

mutual
/-- `+from`. -/
def fromL (axe : Nat) : Lazy S → Option (Lazy S)
  | mk s f b =>
    if f.isEmpty && b.isEmpty then (fromSure axe s).map ofSure else
    (fromSure axe s).bind fun s' => (fromForks axe f).bind fun f' => (fromBonds axe b).map fun b' => mk s' f' b'

/-- Its `turn` over the forks. -/
def fromForks (axe : Nat) : List ((Nat × Lazy S) × (Nat × Lazy S)) →
    Option (List ((Nat × Lazy S) × (Nat × Lazy S)))
  | [] => some []
  | ((oy, y), (on, n)) :: rest =>
    (fromL axe y).bind fun y' => (fromL axe n).bind fun n' =>
      (fromForks axe rest).map fun r => ((oy, y'), (on, n')) :: r

/-- Its `turn` over the bonds. -/
def fromBonds (axe : Nat) : List (Nat × Lazy S) → Option (List (Nat × Lazy S))
  | [] => some []
  | (o, l) :: rest => (fromL axe l).bind fun l' => (fromBonds axe rest).map fun r => (o, l') :: r
end

theorem fromL_ofSure (axe : Nat) (s : Sure S) : fromL axe (ofSure s) = («from» axe s).map ofSure := by
  simp [fromL, ofSure, «from»]

end Lazy

end Comp
end SkaModel
end Formalization
