import lemmas.Ska.CompLazyArms

/-!
# The arms that `%6` reads for a goal `%next`, without the state

`+pass` (with `+pass-both`, `+pass-bomb`, `+pass-then`, `+pass-edit`): the
parts of the product of a formula that are parts of its subject as they
stand.  `+whole`: whether the product of a formula is always in one
register.  `+need-cut`, `+need-from`, `+lazy-leap`, `+leap`: what the lazy
blocks of a goal need of a part that both branches of a fork take from one
place of the subject.  `+this-only`, and `+soft-fork` with the soft map and
the test `+sound` as parameters.

`none` is a crash: `+gep` on a zero axis, `+cap` of a zero axis.  `+peg` is
`Hoon.pegF`, which is total; the Hoon crashes on a zero axis there, which
these arms never pass (the axes come from `[0 a]` with `a` not zero and from
`+peg` and `+gep` of such axes).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S]

/-! ## `+pass` -/

/-- `+pass-bomb`: a crash, under hints or not. -/
def passBomb : Nomm → Bool
  | Nomm.n0 a => a == 0
  | Nomm.n11s _ q _ => passBomb q
  | Nomm.n11d _ _ q _ => passBomb q
  | _ => false

/-- The `murn` of `+pass-both` for one part `(p, s)` of the first branch
against one part `(q, t)` of the second. -/
def passBothOne (p s q t : Nat) : Option (Option (Nat × Nat)) :=
  (gep p q).bind fun d1 =>
  match d1 with
  | some d => some (if t = Hoon.pegF s d then some (q, t) else Option.none)
  | Option.none => (gep q p).map fun d2 =>
    match d2 with
    | some d => if s = Hoon.pegF t d then some (p, s) else Option.none
    | Option.none => Option.none

/-- A `murn` that may crash. -/
def murnO {α β : Type} (f : α → Option (Option β)) : List α → Option (List β)
  | [] => some []
  | x :: xs => (f x).bind fun y => (murnO f xs).map fun ys => match y with
    | some b => b :: ys
    | Option.none => ys

/-- A `turn` that may crash. -/
def turnO {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => (f x).bind fun y => (turnO f xs).map fun ys => y :: ys

/-- `+pass-both` on the `+pass-bomb` and `+pass` of the two branches: the
parts both take from one place of the subject.  `pr` is read only where the
Hoon computes `(pass r)`. -/
def passBothW (bq br : Bool) (pq pr : Option (List (Nat × Nat))) : Option (List (Nat × Nat)) :=
  if bq then pr else if br then pq else
  pq.bind fun a => if a.isEmpty then some [] else
  pr.bind fun b => if b.isEmpty then some [] else
  (turnO (fun (ps : Nat × Nat) => murnO (fun (qt : Nat × Nat) => passBothOne ps.1 ps.2 qt.1 qt.2) b) a).map
    List.flatten

/-- `+pass-then`: `+pass` of `[7 p q]` from those of `p` (`a`) and of `q` (`b`). -/
def passThen (a b : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  if a.isEmpty then some [] else
  (turnO (fun (x : Nat × Nat) => murnO (fun (y : Nat × Nat) =>
    (gep y.1 x.2).bind fun d1 => match d1 with
    | some d => some (some (x.1, Hoon.pegF y.2 d))
    | Option.none => (gep x.2 y.1).map fun d2 => match d2 with
      | some d => some (Hoon.pegF x.1 d, y.2)
      | Option.none => Option.none) a) b).map List.flatten

/-- The loop of `+pass-edit`: the parts beside the path `d` from `p`. -/
def editLoop (p s d : Nat) : List (Nat × Nat) :=
  if _h : d ≤ 1 then [] else
  let k := cap d
  let o := if k = 2 then 3 else 2
  (Hoon.pegF p o, Hoon.pegF s o) :: editLoop (Hoon.pegF p k) (Hoon.pegF s k) (mas d)
termination_by d
decreasing_by exact mas_lt d (by omega)

/-- `+pass-edit`: `+pass` of an edit at `axe`. -/
def passEdit (axe : Nat) (don rec : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  (turnO (fun (x : Nat × Nat) => (gep axe x.1).bind fun d1 => match d1 with
    | some _ => some []
    | Option.none => (gep x.1 axe).map fun d2 => match d2 with
      | Option.none => [x]
      | some d => editLoop x.1 x.2 d) rec).map fun r =>
    don.map (fun x => (Hoon.pegF axe x.1, x.2)) ++ r.flatten

/-- `+pass`. -/
def passN : Nomm → Option (List (Nat × Nat))
  | Nomm.cons a b => (passN a).bind fun x => (passN b).map fun y =>
      x.map (fun e => (Hoon.pegF 2 e.1, e.2)) ++ y.map (fun e => (Hoon.pegF 3 e.1, e.2))
  | Nomm.n0 a => if a = 0 then some [] else some [(1, a)]
  | Nomm.n6 _ q r => passBothW (passBomb q) (passBomb r) (passN q) (passN r)
  | Nomm.n7 p q => (passN p).bind fun a => (passN q).bind fun b => passThen a b
  | Nomm.n10 a v q => (passN v).bind fun d => (passN q).bind fun r => passEdit a d r
  | Nomm.n11s _ q _ => passN q
  | Nomm.n11d _ _ q _ => passN q
  | _ => some []

/-- `+pass-both`. -/
def passBoth (q r : Nomm) : Option (List (Nat × Nat)) :=
  passBothW (passBomb q) (passBomb r) (passN q) (passN r)

/-! ## `+whole` -/

/-- `+whole`: the product is always in one register. -/
def whole : Nomm → Bool
  | Nomm.n1 (Noun.atom _) => true
  | Nomm.n2 _ _ _ => true
  | Nomm.n3 _ => true
  | Nomm.n4 _ => true
  | Nomm.n5 _ _ => true
  | Nomm.n12 _ _ => true
  | Nomm.n6 _ q r => whole q && whole r
  | Nomm.n7 _ q => whole q
  | Nomm.n11s _ q _ => whole q
  | Nomm.n11d _ _ q _ => whole q
  | Nomm.mean _ _ q _ _ => whole q
  | _ => false

/-! ## `+need-cut`, `+need-from` -/

/-- `+need-cut`: the part of a need at an axis and the need without it;
`some none` (`~`) when a noun that holds the part is wanted in a register. -/
def needCut : Nat → Need → Option (Option (Need × Need))
  | axe, Need.none => if axe = 1 then some (some (Need.none, Need.none)) else some (some (Need.none, Need.none))
  | axe, Need.this r => if axe = 1 then some (some (Need.this r, Need.none)) else some Option.none
  | axe, Need.both r h t => if axe = 1 then some (some (Need.both r h t, Need.none)) else some Option.none
  | axe, Need.pair p q =>
    if axe = 1 then some (some (Need.pair p q, Need.none)) else
    if axe = 0 then Option.none else
    if cap axe = 2 then
      (needCut (mas axe) p).map fun k => k.map fun e => (e.1, consNeed e.2 q)
    else
      (needCut (mas axe) q).map fun k => k.map fun e => (e.1, consNeed p e.2)

/-- `+need-from`: a need of a noun as the need of the noun that holds it at
`axe`. -/
def needFrom (axe : Nat) (ned : Need) : Option Need :=
  if ned = Need.none then some ned else
  if axe = 0 then Option.none else some (fromPath ned axe)

/-! ## `+lazy-leap`, `+leap` -/

/-- The `rep` of `+lazy-leap` over the looked-at axes: an axis under `p`
goes to the looks of `by` as an axis under `s`, any other stays. -/
def leapLok (p s : Nat) (lok : S) : Option (S × S) :=
  (HoonSet.toList lok).foldl (fun acc a => acc.bind fun (lb, lr) =>
    (gep p a).map fun d => match d with
      | Option.none => (lb, HoonSet.put lr a)
      | some d => (HoonSet.put lb (Hoon.pegF s d), lr)) (some (HoonSet.empty, HoonSet.empty))

mutual
/-- `+lazy-leap`: what the blocks of a lazy need want of the part at `p`, as
a need of the axis `s` of another noun (`by`), and the need without it
(`rec`). -/
def lazyLeap (p s : Nat) : Lazy S → Option (Lazy S × Lazy S)
  | mk sur fk bd =>
    (needCut p sur.ned).bind fun cut =>
    (match cut with
      | Option.none => some ((Sure.bunt : Sure S), sur)
      | some (don, rec) => (leapLok p s sur.lok).bind fun (lb, lr) =>
          (needFrom s don).map fun nf => ((⟨nf, lb⟩ : Sure S), (⟨rec, lr⟩ : Sure S))).bind fun (sb, sr) =>
    (leapForks p s fk).bind fun fs =>
    (leapBonds p s bd).map fun (bs : List ((Nat × Lazy S) × (Nat × Lazy S))) =>
      (lazyPrune (mk sb (fs.map Prod.fst) (bs.map Prod.fst)), lazyPrune (mk sr (fs.map Prod.snd) (bs.map Prod.snd)))

/-- Its `turn` over the forks. -/
def leapForks (p s : Nat) : List ((Nat × Lazy S) × (Nat × Lazy S)) →
    Option (List (((Nat × Lazy S) × (Nat × Lazy S)) × ((Nat × Lazy S) × (Nat × Lazy S))))
  | [] => some []
  | ((oy, y), (on, n)) :: rest =>
    (lazyLeap p s y).bind fun (yb, yr) => (lazyLeap p s n).bind fun (nb, nr) =>
      (leapForks p s rest).map fun r => (((oy, yb), (on, nb)), ((oy, yr), (on, nr))) :: r

/-- Its `turn` over the bonds. -/
def leapBonds (p s : Nat) : List (Nat × Lazy S) → Option (List ((Nat × Lazy S) × (Nat × Lazy S)))
  | [] => some []
  | (o, l) :: rest =>
    (lazyLeap p s l).bind fun (b, r) => (leapBonds p s rest).map fun rs => ((o, b), (o, r)) :: rs
end

/-- The loop of `+leap` over the parts. -/
def leapLoop (sur : Sure S) : List (Nat × Nat) → Lazy S → List (Lazy S) →
    Option (Option (Lazy S × List (Lazy S)))
  | [], lab, bys => if bys.isEmpty then some Option.none else some (some (mk sur lab.fork lab.bond, bys))
  | (p, s) :: rest, lab, bys => (lazyLeap p s lab).bind fun (b, r) =>
      if lazyEmpty b then leapLoop sur rest lab bys else leapLoop sur rest r (b :: bys)

/-- `+leap`: the need of the goal without the parts that both branches take
from one place of the subject (`rest`), and the needs of those parts as
needs of the subject (`bys`, the last found first). -/
def leap (laz : Lazy S) (q r : Nomm) : Option (Option (Lazy S × List (Lazy S))) :=
  if laz.fork.isEmpty && laz.bond.isEmpty then some Option.none else
  (passBoth q r).bind fun pas => leapLoop laz.sure pas (mk Sure.bunt laz.fork laz.bond) []

/-! ## `+this-only`, `+soft-fork` -/

mutual
/-- `+this-only`: the lazy need wants its noun whole or not at all, in
every block. -/
def thisOnly : Lazy S → Bool
  | mk s f b => (match s.ned with | Need.this _ => true | Need.none => true | _ => false) &&
      HoonSet.small s.lok && thisOnlyForks f && thisOnlyBonds b

def thisOnlyForks : List ((Nat × Lazy S) × (Nat × Lazy S)) → Bool
  | [] => true
  | ((_, a), (_, b)) :: rest => (thisOnly a && thisOnly b) && thisOnlyForks rest

def thisOnlyBonds : List (Nat × Lazy S) → Bool
  | [] => true
  | (_, l) :: rest => thisOnly l && thisOnlyBonds rest
end

mutual
/-- `+soft-fork`, with the soft map `soft` and `unsound ned`, which is
`!&((sound q ned) (sound r ned))` on the ordered need. -/
def softFork (soft : Nat → Bool) (unsound : Need → Bool) : Lazy S → Bool
  | mk _ f b => softForkBonds soft unsound b || softForkForks soft unsound f

def softForkBonds (soft : Nat → Bool) (unsound : Need → Bool) : List (Nat × Lazy S) → Bool
  | [] => false
  | (o, l) :: rest => ((soft o && unsound l.sure.ned) || softFork soft unsound l) ||
      softForkBonds soft unsound rest

def softForkForks (soft : Nat → Bool) (unsound : Need → Bool) : List ((Nat × Lazy S) × (Nat × Lazy S)) → Bool
  | [] => false
  | ((_, a), (_, b)) :: rest => (softFork soft unsound a || softFork soft unsound b) ||
      softForkForks soft unsound rest
end

end Comp
end SkaModel
end Formalization
