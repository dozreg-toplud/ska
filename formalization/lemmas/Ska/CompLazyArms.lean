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

/-! ## `+split` and `+into` -/

/-- A fork: the yes branch and the no branch, each a lazy block and a need. -/
abbrev ForkE (S : Type) := (Nat × Lazy S) × (Nat × Lazy S)

mutual
/-- The loop `split-loop` of `+split`: the sure need is split by
`+split-sure` into block `o`, each fork's and bond's needs into their own
blocks, and the two halves are pruned. -/
def splitLoop : Lazy S → Nat → CM Map (Lazy S × Lazy S)
  | mk s f b, o => do
    let (sh, st) ← splitSure s o
    if f.isEmpty && b.isEmpty then pure (ofSure sh, ofSure st) else do
    let (fh, ft) ← splitForks f
    let (bh, bt) ← splitBonds b
    pure (lazyPrune (mk sh fh bh), lazyPrune (mk st ft bt))

/-- Its `spin-split` over the forks. -/
def splitForks : List (ForkE S) → CM Map (List (ForkE S) × List (ForkE S))
  | [] => pure ([], [])
  | ((oy, y), (on, n)) :: rest => do
    let (yh, yt) ← splitLoop y oy
    let (nh, nt) ← splitLoop n on
    let (rh, rt) ← splitForks rest
    pure (((oy, yh), (on, nh)) :: rh, ((oy, yt), (on, nt)) :: rt)

/-- Its `spin-split` over the bonds. -/
def splitBonds : List (Nat × Lazy S) → CM Map (List (Nat × Lazy S) × List (Nat × Lazy S))
  | [] => pure ([], [])
  | (o, l) :: rest => do
    let (lh, lt) ← splitLoop l o
    let (rh, rt) ← splitBonds rest
    pure ((o, lh) :: rh, (o, lt) :: rt)
end

theorem splitLoop_ofSure (s : Sure S) (o : Nat) :
    (splitLoop (ofSure s) o : CM Map (Lazy S × Lazy S)) =
      (do let (h, t) ← splitSure s o; pure (ofSure h, ofSure t)) := by
  simp [splitLoop, ofSure]

mutual
/-- The loop `split-loop` of `+into`: the same walk as `splitLoop` with
`+into-sure`, the donor's half first. -/
def intoLoopL (axe : Nat) : Lazy S → Nat → CM Map (Lazy S × Lazy S)
  | mk s f b, o => do
    let (sd, sr) ← intoSure axe s o
    if f.isEmpty && b.isEmpty then pure (ofSure sd, ofSure sr) else do
    let (fd, fr) ← intoForks axe f
    let (bd, br) ← intoBonds axe b
    pure (lazyPrune (mk sd fd bd), lazyPrune (mk sr fr br))

/-- Its `spin-split` over the forks. -/
def intoForks (axe : Nat) : List (ForkE S) → CM Map (List (ForkE S) × List (ForkE S))
  | [] => pure ([], [])
  | ((oy, y), (on, n)) :: rest => do
    let (yd, yr) ← intoLoopL axe y oy
    let (nd, nr) ← intoLoopL axe n on
    let (rd, rr) ← intoForks axe rest
    pure (((oy, yd), (on, nd)) :: rd, ((oy, yr), (on, nr)) :: rr)

/-- Its `spin-split` over the bonds. -/
def intoBonds (axe : Nat) : List (Nat × Lazy S) → CM Map (List (Nat × Lazy S) × List (Nat × Lazy S))
  | [] => pure ([], [])
  | (o, l) :: rest => do
    let (ld, lr) ← intoLoopL axe l o
    let (rd, rr) ← intoBonds axe rest
    pure ((o, ld) :: rd, (o, lr) :: rr)
end

theorem intoLoopL_ofSure (axe : Nat) (s : Sure S) (o : Nat) :
    (intoLoopL axe (ofSure s) o : CM Map (Lazy S × Lazy S)) =
      (do let (d, r) ← intoSure axe s o; pure (ofSure d, ofSure r)) := by
  simp [intoLoopL, ofSure]

/-! ## `+copy-lazy` -/

/-- `(malt (turn l |=(e [key e])))` and `get` on it: the last entry of `l`
under the key, through the map laws. -/
def index {α : Type} (key : α → Nat) (l : List α) : Map α :=
  l.foldl (fun m e => HoonMap.put m (key e) e) HoonMap.empty

/-- `(silt (turn l key))` and `has` on it. -/
def seen {α : Type} (key : α → Nat) (l : List α) (k : Nat) : Bool :=
  decide (k ∈ HoonSet.toList ((l.map key).foldl HoonSet.put (HoonSet.empty : S)))

mutual
/-- `+copy-lazy`: the sure needs are merged by `+copy-need-make-ops` with
the moves into block `o`; forks and bonds of the two needs that name the
same lazy block are merged the same way into that block, the others are
kept, those of `first` first. -/
def copyLazyL (o : Nat) : Lazy S → Lazy S → CM Map (Lazy S)
  | mk s1 f1 b1, second => do
    let (ned, ops) ← copyNeed s1.ned second.sure.ned []
    addOps o ops
    let fork ← (if second.fork.isEmpty then pure f1 else if f1.isEmpty then pure second.fork else do
      let merged ← mergeForks (index (Map := Map) (fun e : ForkE S => e.1.1) second.fork) f1
      pure (merged ++ second.fork.filter fun e => !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1)) :
        CM Map (List (ForkE S)))
    let bond ← (if second.bond.isEmpty then pure b1 else if b1.isEmpty then pure second.bond else do
      let merged ← mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1
      pure (merged ++ second.bond.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)) :
        CM Map (List (Nat × Lazy S)))
    pure (mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ fork bond)

/-- The `spin` over the forks of `first`. -/
def mergeForks (idx : Map (ForkE S)) : List (ForkE S) → CM Map (List (ForkE S))
  | [] => pure []
  | ((oy, y), (on, n)) :: rest => do
    let e ← (match HoonMap.get idx oy with
      | Option.none => pure ((oy, y), (on, n))
      | some ((_, my), (mon, mn)) =>
        if on = mon then do
          let y' ← copyLazyL oy y my
          let n' ← copyLazyL on n mn
          pure ((oy, y'), (on, n'))
        else fun _ => Option.none : CM Map (ForkE S))
    let r ← mergeForks idx rest
    pure (e :: r)

/-- The `spin` over the bonds of `first`. -/
def mergeBonds (idx : Map (Nat × Lazy S)) : List (Nat × Lazy S) → CM Map (List (Nat × Lazy S))
  | [] => pure []
  | (ob, l) :: rest => do
    let e ← (match HoonMap.get idx ob with
      | Option.none => pure (ob, l)
      | some (_, m) => do
        let l' ← copyLazyL ob l m
        pure (ob, l') : CM Map (Nat × Lazy S))
    let r ← mergeBonds idx rest
    pure (e :: r)
end

theorem copyLazyL_ofSure (o : Nat) (s1 s2 : Sure S) :
    (copyLazyL o (ofSure s1) (ofSure s2) : CM Map (Lazy S)) = (copyLazy o s1 s2 >>= fun s => pure (ofSure s)) := by
  simp [copyLazyL, ofSure, copyLazy]

end Lazy


end Comp
end SkaModel
end Formalization
