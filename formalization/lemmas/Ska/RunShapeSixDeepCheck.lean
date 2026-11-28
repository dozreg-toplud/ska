import lemmas.Ska.RunShape
import lemmas.Ska.CompLeapTwiceCheck

/-!
# `+laze-leaps` never leaps twice, on the executable model (track A, 2026-11-28)

The hypothesis of `sixDeep_of_idem` (`Compiler/CompRunShapeSixN.lean`): a `rest` that
`lazeLeaps` returns does not leap again.  Run before it was proved (`lazeLeaps_idem`,
`RunShapeSixDeep.lean`), as `CompLeapTwiceCheck.lean` did for `+leap`: random `laze`s (the set type
`TL` of that file, `need-ordered`s with `%both`, pairs, `consOrd`, looks at small axes, up to three
levels of nested forks and bonds) and pass lists from `passBoth` of pairs of its 20 branches, or
random lists of up to four passes with nonzero axes.  `checkS` runs `lazeLeaps`' loop, and on a
rest runs it again: it must give `~`.
-/

namespace Formalization
namespace SkaModel
namespace Comp
open Nock Laze

instance : Inhabited NeedOrd := ⟨NeedOrd.none⟩
instance : Inhabited (Laze TL) := ⟨mk ⟨NeedOrd.none, ⟨[]⟩⟩ [] []⟩

partial def genOrd (d : Nat) (x : Nat) : NeedOrd × Nat :=
  let x := lcg x
  let c := (x / 65536) % (if d = 0 then 2 else 6)
  match c with
  | 0 => (NeedOrd.none, x)
  | 1 => (NeedOrd.this, x)
  | 2 | 4 => let (a, x) := genOrd (d - 1) x; let (b, x) := genOrd (d - 1) x;
      (if a = NeedOrd.none ∧ b = NeedOrd.none then NeedOrd.none else NeedOrd.pair a b, x)
  | 5 => let (a, x) := genOrd (d - 1) x; let (b, x) := genOrd (d - 1) x; (NeedOrd.pair a b, x)
  | _ => let (a, x) := genOrd (d - 1) x; let (b, x) := genOrd (d - 1) x; (NeedOrd.both a b, x)

partial def genLaze (d : Nat) (x : Nat) : Laze TL × Nat :=
  let (ned, x) := genOrd 3 x
  let (lok, x) := genLok x
  let x := lcg x
  let nf := if d = 0 then 0 else (x / 65536) % 3
  let x := lcg x
  let nb := if d = 0 then 0 else (x / 65536) % 3
  let rec forks : Nat → Nat → List ((Nat × Laze TL) × (Nat × Laze TL)) × Nat
    | 0, x => ([], x)
    | k + 1, x =>
      let (a, x) := genLaze (d - 1) x
      let (b, x) := genLaze (d - 1) x
      let (r, x) := forks k x
      (((k, a), (k + 10, b)) :: r, x)
  let rec bonds : Nat → Nat → List (Nat × Laze TL) × Nat
    | 0, x => ([], x)
    | k + 1, x =>
      let (a, x) := genLaze (d - 1) x
      let (r, x) := bonds k x
      ((k + 20, a) :: r, x)
  let (fk, x) := forks nf x
  let (bd, x) := bonds nb x
  (mk ⟨ned, lok⟩ fk bd, x)

/-- One case: `some true` when the first loop gave a rest and the second `~`, `some false` when
the first gave none, `none` on a failure. -/
def checkS (laz : Laze TL) (pas : List (Nat × Nat)) : Option Bool :=
  match leapsLoop laz.sure pas (mk SureO.bunt laz.fork laz.bond) [] with
  | some (some (rest, _)) =>
    let second : Option (Option (Laze TL × List (Laze TL))) :=
      if rest.fork.isEmpty && rest.bond.isEmpty then some Option.none
      else leapsLoop rest.sure pas (mk SureO.bunt rest.fork rest.bond) []
    match second with
    | some Option.none => some true
    | _ => Option.none
  | _ => some false

def runTestsS (n : Nat) (seed : Nat) : Nat × Nat × Nat × Nat × Option Nat :=
  Id.run do
    let mut x := seed
    let mut leapt := 0
    let mut forky := 0
    let mut fails := 0
    let mut firstFail : Option Nat := Option.none
    for i in [0:n] do
      let (laz, x1) := genLaze 3 x
      let (pas, x2) := genPas x1
      x := x2
      let laz := if laz.fork.isEmpty && laz.bond.isEmpty then mk laz.sure [((0, laz), (1, laz))] [] else laz
      match checkS laz pas with
      | some true =>
        leapt := leapt + 1
        match leapsLoop laz.sure pas (mk SureO.bunt laz.fork laz.bond) [] with
        | some (some (rest, _)) => if !(rest.fork.isEmpty && rest.bond.isEmpty) then forky := forky + 1
        | _ => pure ()
      | some false => pure ()
      | Option.none =>
        fails := fails + 1
        if firstFail.isNone then firstFail := some i
    return (n, leapt, forky, fails, firstFail)

/- 3000 cases: no failure, and the second loop ran on many rests that still fork or bond. -/
#guard let r := runTestsS 3000 99; r.2.2.2.1 == 0 && r.2.1 > 2000 && r.2.2.1 > 1000

end Comp
end SkaModel
end Formalization
