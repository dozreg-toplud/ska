import lemmas.Ska.CompLeap

/-!
# `LeapTwice` on the executable model

The test run before `leap_twice` was proved (`CompLeapTwice.lean`), kept
small: a computable set type `TL`, random lazy needs with up to three
levels of nested forks and bonds (needs with `%both`, pairs, `consNeed`,
looks at small axes), and pass lists from `passBoth` of pairs of 20
branches (parts passed twice, under a cons, nested, under `%7`, `%10`,
`%11`) or random lists of up to four passes with nonzero axes.  `check`
runs the loop of `+leap`, and when it gives a rest runs it again on the
rest: it must give `~`.  The session's run: 200,000 cases (seeds `7` and
`12345`), 182,001 first leaps with a rest, 139,361 rests with forks or bonds
left, no failure.
-/

namespace Formalization
namespace SkaModel
namespace Comp
open Nock Lazy

structure TL where
  l : List Nat
deriving Repr, Inhabited

instance : HoonSet TL where
  empty := ⟨[]⟩
  toList s := s.l
  put s x := if x ∈ s.l then s else ⟨s.l ++ [x]⟩
  uni a b := ⟨a.l ++ b.l.filter (fun x => x ∉ a.l)⟩
  isEmpty s := s.l.isEmpty
  small s := s.l.all (· == 1)
  toNoun _ := A 0
  mem_empty x := by simp
  mem_put s x y := by
    show y ∈ (if x ∈ s.l then s else (⟨s.l ++ [x]⟩ : TL)).l ↔ y = x ∨ y ∈ s.l
    by_cases h : x ∈ s.l
    · simp only [h, if_true]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact h
        · exact h'
    · simp only [h, if_false, List.mem_append, List.mem_singleton]
      exact Or.comm
  mem_uni a b y := by
    show y ∈ a.l ++ b.l.filter (fun x => x ∉ a.l) ↔ _
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    by_cases h : y ∈ a.l <;> simp [h]
  isEmpty_iff s := by simp [List.isEmpty_iff]
  small_iff s := by simp
  toNoun_empty := rfl

instance : Inhabited Need := ⟨Need.none⟩
instance : Inhabited (Lazy TL) := ⟨mk ⟨Need.none, ⟨[]⟩⟩ [] []⟩

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
def pk {α} [Inhabited α] (l : List α) (x : Nat) : α := l[(x / 65536) % l.length]!

def axes : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 27]

partial def genNeed (d : Nat) (x : Nat) : Need × Nat :=
  let x := lcg x
  let c := (x / 65536) % (if d = 0 then 2 else 6)
  match c with
  | 0 => (Need.none, x)
  | 1 => (Need.this ((x / 7) % 50), x)
  | 2 | 4 => let (a, x) := genNeed (d - 1) x; let (b, x) := genNeed (d - 1) x; (consNeed a b, x)
  | 5 => let (a, x) := genNeed (d - 1) x; let (b, x) := genNeed (d - 1) x; (Need.pair a b, x)
  | _ => let (a, x) := genNeed (d - 1) x; let (b, x) := genNeed (d - 1) x; (Need.both ((x / 7) % 50) a b, x)

def genLok (x : Nat) : TL × Nat :=
  let x := lcg x
  let n := (x / 65536) % 3
  let x1 := lcg x
  let x2 := lcg x1
  let l := (if n ≥ 1 then [pk axes x1] else []) ++ (if n ≥ 2 then [pk axes x2] else [])
  (⟨l.eraseDups⟩, x2)

partial def genLazy (d : Nat) (x : Nat) : Lazy TL × Nat :=
  let (ned, x) := genNeed 3 x
  let (lok, x) := genLok x
  let x := lcg x
  let nf := if d = 0 then 0 else (x / 65536) % 3
  let x := lcg x
  let nb := if d = 0 then 0 else (x / 65536) % 3
  let rec forks : Nat → Nat → List ((Nat × Lazy TL) × (Nat × Lazy TL)) × Nat
    | 0, x => ([], x)
    | k + 1, x =>
      let (a, x) := genLazy (d - 1) x
      let (b, x) := genLazy (d - 1) x
      let (r, x) := forks k x
      (((k, a), (k + 10, b)) :: r, x)
  let rec bonds : Nat → Nat → List (Nat × Lazy TL) × Nat
    | 0, x => ([], x)
    | k + 1, x =>
      let (a, x) := genLazy (d - 1) x
      let (r, x) := bonds k x
      ((k + 20, a) :: r, x)
  let (fk, x) := forks nf x
  let (bd, x) := bonds nb x
  (mk ⟨ned, lok⟩ fk bd, x)

def branches : List Nomm :=
  [Nomm.n0 1, Nomm.n0 2, Nomm.n0 3, Nomm.n0 6, Nomm.n0 7,
   Nomm.cons (Nomm.n0 2) (Nomm.n0 2), Nomm.cons (Nomm.n0 6) (Nomm.n0 7),
   Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (Nomm.n0 2),
   Nomm.n7 (Nomm.n0 2) (Nomm.n0 3), Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)) (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)),
   Nomm.n10 2 (Nomm.n0 3) (Nomm.n0 1), Nomm.n10 6 (Nomm.n0 2) (Nomm.n0 1),
   Nomm.n11s 0 (Nomm.n0 2) (A 0), Nomm.n1 (A 0),
   Nomm.n6 (Nomm.n1 (A 0)) (Nomm.n0 2) (Nomm.n0 2), Nomm.cons (Nomm.n1 (A 0)) (Nomm.n0 2),
   Nomm.cons (Nomm.n0 2) (Nomm.cons (Nomm.n0 2) (Nomm.n0 6)),
   Nomm.cons (Nomm.n0 2) (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)),
   Nomm.cons (Nomm.cons (Nomm.n0 4) (Nomm.n0 4)) (Nomm.n0 2),
   Nomm.n0 0]

def passLists : List (List (Nat × Nat)) :=
  (branches.flatMap fun q => branches.filterMap fun r => passBoth q r).eraseDups

def genPas (x : Nat) : List (Nat × Nat) × Nat :=
  let x := lcg x
  if (x / 65536) % 3 = 0 then (pk passLists (lcg x), lcg x) else
  let x := lcg x
  let n := 1 + (x / 65536) % 4
  let rec go : Nat → Nat → List (Nat × Nat) × Nat
    | 0, x => ([], x)
    | k + 1, x => let x1 := lcg x; let x2 := lcg x1; let (r, x) := go k x2; ((pk axes x1, pk [1, 2, 3, 6, 7] x2) :: r, x)
  go n x

/-- One case: `some true` when the first loop gave a rest and the second
`~`, `some false` when the first gave none, `none` on a failure. -/
def check (laz : Lazy TL) (pas : List (Nat × Nat)) : Option Bool :=
  match leapLoop laz.sure pas (mk Sure.bunt laz.fork laz.bond) [] with
  | some (some (rest, _)) =>
    let second : Option (Option (Lazy TL × List (Lazy TL))) :=
      if rest.fork.isEmpty && rest.bond.isEmpty then some Option.none
      else leapLoop rest.sure pas (mk Sure.bunt rest.fork rest.bond) []
    match second with
    | some Option.none => some true
    | _ => Option.none
  | _ => some false

def runTests (n : Nat) (seed : Nat) : Nat × Nat × Nat × Nat × Option (Nat) :=
  Id.run do
    let mut x := seed
    let mut leapt := 0
    let mut forky := 0
    let mut fails := 0
    let mut firstFail : Option Nat := Option.none
    for i in [0:n] do
      let (laz, x1) := genLazy 3 x
      let (pas, x2) := genPas x1
      x := x2
      let laz := if laz.fork.isEmpty && laz.bond.isEmpty then mk laz.sure [((0, laz), (1, laz))] [] else laz
      match check laz pas with
      | some true =>
        leapt := leapt + 1
        match leapLoop laz.sure pas (mk Sure.bunt laz.fork laz.bond) [] with
        | some (some (rest, _)) => if !(rest.fork.isEmpty && rest.bond.isEmpty) then forky := forky + 1
        | _ => pure ()
      | some false => pure ()
      | Option.none =>
        fails := fails + 1
        if firstFail.isNone then firstFail := some i
    return (n, leapt, forky, fails, firstFail)

/- 3000 cases: no failure, and the second loop ran on many rests that
still fork or bond. -/
#guard let r := runTests 3000 99; r.2.2.2.1 == 0 && r.2.1 > 2500 && r.2.2.1 > 1800

end Comp
end SkaModel
end Formalization
