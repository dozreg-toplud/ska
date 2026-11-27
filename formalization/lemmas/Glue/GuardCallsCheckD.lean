import lemmas.Glue.GuardCallsCheck

/-!
# `KIMid` at the end of the run: executable checks (track G, tenth pass)

The `run` clause of the named hypothesis `KIMid` (`Glue/GuardCallsB.lean`)
at the top run of `finishLUCM envD`: the result's lazy has distinct
registers in each of its sure needs (root, forks and bonds), all below the
end's `re` (`lzsB`, the Boolean form of `LzS (DN re)`).  On the seven direct
calls (7 of 7) and one nomm in 40 of `enumDX` (198 of 198).
-/

namespace Formalization
namespace SkaModel
namespace Glue
namespace GuardCallsCheckD

open Nock Opt Comp Raw Path EntryCheck EntryPathCheck GuardCallsCheck

def nregs : Need → List Nat
  | Need.none => []
  | Need.this r => [r]
  | Need.pair p q => nregs p ++ nregs q
  | Need.both r p q => r :: (nregs p ++ nregs q)

def dnB (r : Nat) (s : Sure LS) : Bool := decide (nregs s.ned).Nodup && (nregs s.ned).all (· < r)

partial def lzsB (r : Nat) : Lazy LS → Bool
  | Lazy.mk s f b => dnB r s && f.all (fun e => lzsB r e.1.2 && lzsB r e.2.2) && b.all (fun e => lzsB r e.2)

/-- `some true`: the run ends with a `DN` lazy; `none`: no code. -/
def endDN (nm : Nomm) : Option Bool :=
  (runLCM (S := LS) (Map := FM) envD true Option.none nm CGoalL.done [] gen0).map fun (nex, g1) => lzsB g1.re nex.laz

def tallyD (l : List Nomm) : List Nat :=
  let rs := l.map endDN
  [rs.countP (·.isNone), rs.countP (· == some true), rs.countP (· == some false)]

def enumDX40 : List Nomm := (enumDX.zipIdx.filter fun (_, i) => i % 40 == 0).map (·.1)

#guard tallyD dmNomms == [0, 7, 0]
#guard tallyD enumDX40 == [0, 198, 0]

end GuardCallsCheckD
end Glue
end SkaModel
end Formalization
