import lemmas.Ska.CompRunLC
import lemmas.Ska.CompCall

/-!
# The checks of `LOKSX` on the executable model

README Gaps 12.32 and 12.33.  The conclusions that `LOKSX` adds to `LOKS`
(`CompLOKSX.lean`), run on the executable model of `CompCall.lean` (`envR`,
`genAt`) before any proof:

* (G) the goal's entries apart from its sure registers gives the result's
  entries apart from the result's sure registers;
* (P2) under (G), a result entry at a goal label is apart from the goal's
  sure registers;
* (P3) a result entry at a goal label reads only registers of the goal's
  entry at that label or registers from the run's start `re` to its end
  `re` (P3 and (G) give (P2), since the goal's registers are below `re`).

(P2) at every label is false: the park entry of a cons with a hinted tail
holds the head's half of the goal (`p2all`, 108 failures).  The nomms are
the 75 of the old scratch checker (`[0 1]`, `[0 2]`, `[0 3]`, `[4 [0 2]]`,
`[3 [0 3]]`, `[4 [0 1]]`, `[1 5]`, `[2 [0 3] [0 2]]` and their cons) and
the shapes `[5 p q]` and `[7 p q]` alone and under a cons, each under 30
flat lazy goals, 2 jumps, 2 states.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace LSXCheck

open Nock Lazy

def regsOf : Need → List Nat
  | Need.none => []
  | Need.this r => [r]
  | Need.pair p q => regsOf p ++ regsOf q
  | Need.both r p q => r :: (regsOf p ++ regsOf q)

def ind : Nomm := Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none

def leaves : List Nomm := [Nomm.n0 1, Nomm.n0 2, Nomm.n0 3, Nomm.n4 (Nomm.n0 2), Nomm.n3 (Nomm.n0 3),
  Nomm.n4 (Nomm.n0 1), Nomm.n1 (A 5), ind]

def grow (xs : List Nomm) : List Nomm :=
  xs ++ xs.flatMap fun p => xs.flatMap fun q => [Nomm.cons p q]

/-- The 75 nomms of the old checker. -/
def cls : List Nomm := (grow leaves) ++ [Nomm.n4 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)),
  Nomm.cons (Nomm.cons (Nomm.n4 (Nomm.n0 2)) (Nomm.n0 3)) (Nomm.n4 (Nomm.n0 3)),
  Nomm.cons (Nomm.n4 (Nomm.n0 2)) (Nomm.cons (Nomm.n3 (Nomm.n0 3)) (Nomm.n4 (Nomm.n0 1)))]

def parkC : Nomm := Nomm.cons (Nomm.n0 1) ind

/-- `[5 p q]` and `[7 p q]`, alone and as a part of a cons. -/
def cls57 : List Nomm :=
  let fives := [Nomm.n5 (Nomm.n0 2) (Nomm.n0 3), Nomm.n5 (Nomm.n4 (Nomm.n0 2)) (Nomm.n0 3),
    Nomm.n5 ind (Nomm.n0 1), Nomm.n5 (Nomm.n0 1) parkC]
  let sevens := [Nomm.n0 1, Nomm.n0 3, Nomm.n4 (Nomm.n0 2), Nomm.cons (Nomm.n0 2) (Nomm.n0 3), Nomm.n1 (A 5),
      Nomm.cons (Nomm.n4 (Nomm.n0 2)) (Nomm.n3 (Nomm.n0 3))].flatMap fun p =>
    [Nomm.n0 2, parkC, ind, Nomm.cons (Nomm.n0 3) (Nomm.n0 2), Nomm.n4 (Nomm.n0 3)].map fun q => Nomm.n7 p q
  let parts := fives.take 2 ++ [Nomm.n7 (Nomm.n0 2) parkC, Nomm.n7 (Nomm.n4 (Nomm.n0 2)) ind,
    Nomm.n7 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (Nomm.cons (Nomm.n0 3) (Nomm.n0 2))]
  fives ++ sevens ++ parts.flatMap fun p => [Nomm.cons p (Nomm.n0 2), Nomm.cons (Nomm.n0 3) p, Nomm.cons p ind]

def sures : List (Sure LS) :=
  [Sure.bunt, lazyReg 0, ⟨Need.pair (Need.this 0) (Need.this 1), HoonSet.empty⟩,
   ⟨Need.pair Need.none (Need.this 1), HoonSet.empty⟩, ⟨Need.both 0 (Need.this 1) Need.none, HoonSet.empty⟩,
   ⟨Need.pair (Need.pair (Need.this 0) Need.none) (Need.this 1), HoonSet.empty⟩]

def bonds : List (List (Nat × Lazy LS)) :=
  [[], [(1, ofSure (lazyReg 2))],
   [(1, ofSure ⟨Need.pair (Need.this 2) Need.none, HoonSet.empty⟩), (2, ofSure (lazyReg 3))],
   [(1, ofSure ⟨Need.pair (Need.this 2) (Need.this 3), HoonSet.empty⟩)],
   [(2, ofSure ⟨Need.pair Need.none (Need.pair (Need.this 3) (Need.this 2)), HoonSet.empty⟩)]]

def lazies : List (Lazy LS) := sures.flatMap fun s => bonds.map fun b => Lazy.mk s [] b

def jumps : List Jmp := [jmp0 1, jmp0 3]

def states : List (Gen FM) := [genAt 4 4, genAt 10 3]

def apart (a b : List Nat) : Bool := a.all fun r => !(b.contains r)

/-- The goal's entries apart from its sure registers (G). -/
def gApart (L : Lazy LS) : Bool := (entries L).all fun e => apart (regsOf L.sure.ned) (regsOf e.2.sure.ned)

/-- One run: `(G of the goal, G of the result, P2 at goal labels, P3, P2 at every label)`. -/
def one (nm : Nomm) (L : Lazy LS) (th : Jmp) (g : Gen FM) : Option (Bool × Bool × Bool × Bool × Bool) :=
  match runLC envR Option.none nm (CGoalL.next L th) [] g with
  | some (nex, g1) =>
    let es := entries nex.laz
    let gl := (entries L).map Prod.fst
    let atGoal := es.filter fun e => gl.contains e.1
    some (gApart L, gApart nex.laz,
      atGoal.all (fun e => apart (regsOf L.sure.ned) (regsOf e.2.sure.ned)),
      atGoal.all (fun e => (regsOf e.2.sure.ned).all fun r =>
        ((entries L).any fun e0 => e0.1 == e.1 && (regsOf e0.2.sure.ned).contains r) || (g.re ≤ r && r < g1.re)),
      es.all (fun e => apart (regsOf L.sure.ned) (regsOf e.2.sure.ned)))
  | Option.none => Option.none

/-- `(runs, runs under G, G fails, P2 fails, P3 fails, P2-at-every-label fails)`. -/
def check (nms : List Nomm) : Nat × Nat × Nat × Nat × Nat × Nat :=
  nms.foldl (fun acc nm => lazies.foldl (fun acc L => jumps.foldl (fun acc th => states.foldl (fun acc g =>
    match one nm L th g with
    | some (gi, go, p2, p3, pa) =>
      let (n, ng, a, b, c, d) := acc
      (n + 1, if gi then ng + 1 else ng, if gi && !go then a + 1 else a, if gi && !p2 then b + 1 else b,
        if p3 then c else c + 1, if gi && !pa then d + 1 else d)
    | Option.none => acc) acc) acc) acc) (0, 0, 0, 0, 0, 0)

-- 4,136 runs of the old nomms: (G), (P2) and (P3) hold on every one, (P2)
-- at every label fails on 108 (the park entries).
#guard check cls == (4136, 4136, 0, 0, 0, 108)

-- 2,312 runs of `[5 p q]` and `[7 p q]`, alone and under a cons: the same.
#guard check cls57 == (2312, 2312, 0, 0, 0, 108)

end LSXCheck
end Comp
end SkaModel
end Formalization
