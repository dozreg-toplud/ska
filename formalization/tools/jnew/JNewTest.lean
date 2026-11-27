import lemmas.Ska.CompRunLC

/-! Test of `JNewL` on the executable model: for hinted nomms built from
`[0 axe]`, cons and the indirect call, under lazy goals (flat and with
forks), from several states: whenever `runLC` succeeds, its jump is at or
above the start state's `bo`.  Run from `formalization/` under the memory
cap: `systemd-run --user --scope -q -p MemoryMax=3G -p MemorySwapMax=0 --
timeout 900 lake env lean tools/jnew/JNewTest.lean` (2026-11-27: 5175 nomms,
967600 runs, 0 failures; README Gaps 12.26). -/

open Formalization SkaModel Comp Nock Lazy

def leaves : List Nomm := [Nomm.n0 0, Nomm.n0 1, Nomm.n0 2, Nomm.n0 3, Nomm.n0 6]

def grow (xs : List Nomm) : List Nomm :=
  xs ++ xs.flatMap fun p => xs.flatMap fun q => [Nomm.cons p q, Nomm.n2 p q Option.none]

def cls1 : List Nomm := grow leaves
def cls2 : List Nomm := (grow cls1).filter fun nm => hinted envR.cod nm == some true

def sures : List (Sure LS) :=
  [Sure.bunt, lazyReg 0, ⟨Need.pair (Need.this 0) (Need.this 1), HoonSet.empty⟩,
   ⟨Need.pair Need.none (Need.this 1), HoonSet.empty⟩, ⟨Need.none, ⟨[2]⟩⟩]

def bonds : List (List (Nat × Lazy LS)) :=
  [[], [(1, ofSure (lazyReg 2))],
   [(1, ofSure ⟨Need.pair (Need.this 2) Need.none, HoonSet.empty⟩), (2, ofSure (lazyReg 3))]]

def forks : List (List ((Nat × Lazy LS) × (Nat × Lazy LS))) :=
  [[], [((1, ofSure (lazyReg 2)), (2, ofSure (lazyReg 3)))]]

def lazies : List (Lazy LS) :=
  sures.flatMap fun s => bonds.flatMap fun b => forks.map fun f => Lazy.mk s f b

def jumps : List Jmp := [jmp0 1, jmp0 3, jmp0 5, jmp0 9]

def states : List (Gen FM) := [genAt 4 4, genAt 10 3, { genAt 4 4 with drop := true }, genAt 0 1]

/-- `(runs that succeed, failures of the claim, a witness)`. -/
def check (nms : List Nomm) : Nat × Nat × Option (Nomm × Nat × Nat) :=
  nms.foldl (fun acc nm => lazies.foldl (fun acc L => jumps.foldl (fun acc th => states.foldl (fun acc g =>
    match runLC envR Option.none nm (CGoalL.next L th) [] g with
    | some (nex, _) =>
      if g.bo ≤ nex.th.there then (acc.1 + 1, acc.2.1, acc.2.2)
      else (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some (nm, g.bo, nex.th.there))
    | Option.none => acc) acc) acc) acc) (0, 0, Option.none)

#eval cls2.length
#eval (check cls2).1
#eval (check cls2).2.1
