import lemmas.Ska.CompDirectMClose
import lemmas.Ska.CompDirectMCheck

/-!
# The closed theorems of `CompDirectMClose.lean` are not vacuous

README Gaps 18.15.  A bell `bellZ` for `[0 3]` on any subject, with the
n-ary need `[~ this]` that `finishLFC` gives it, and its two entries in the
table.  The `#guard`s check that every code the theorems take exists, that
the need `+callee-need` reads is the need of the n-ary entry (the hypothesis
`hneed`), and that the caller's whole-subject code, run by the interpreter
model on the table's oracle (`tableOracle`, so the callee's code runs too,
not an oracle that runs `+mink`), agrees with `+mink` on a cell (the
optimistic `%jmp`/`%cal` to the n-ary entry) and on an atom (the pessimistic
`%jsp`/`%csl` to the whole-subject entry, which crashes as `+mink` does).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `[0 3]` on any subject. -/
def bellZ : Bell := ⟨Sock.mk Cape.no (A 0), slot 3⟩

/-- `bellZ` needs `[~ this]`, is impure, no jet, hinted. -/
def envZ : CallEnv :=
  ⟨fun b => if b = bellZ then some (NeedOrd.pair NeedOrd.none NeedOrd.this) else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false,
   fun _ _ _ _ _ => false⟩

/-- The n-ary entry of `bellZ`. -/
def zN : Option (Straight FM) :=
  finishLFC (S := LS) envZ (Nomm.n0 3) (NeedOrd.pair NeedOrd.none NeedOrd.this) Cape.no (fun ned => (ned, []))

/-- The whole-subject entry of `bellZ`. -/
def zW : Option (Straight FM) := finishLUCM (S := LS) envZ (Nomm.n0 3)

/-- The caller's whole-subject code of `nm`, run on the table of `bellZ`
with ten levels, against `+mink` on `f`. -/
def zRun (nm : Nomm) (f s : Noun) : Bool :=
  match zN, zW, (finishLUCM (S := LS) envZ nm : Option (Straight FM)) with
  | some cN, some cW, some c =>
      (execEntry libT (tableOracle libT (table2 bellZ cN cW) 10) () c [s] [] (A 0)).map Prod.fst ==
        minkF libT (A 0) 500 [] s f
  | _, _, _ => false

-- the entries exist, and the need read is the n-ary entry's (`hneed`)
#guard zN.map (·.need) == envZ.need bellZ
#guard zW.isSome
#guard (finishLUCM (S := LS) (Map := FM) envZ (slotCall bellZ)).isSome
#guard (finishLUCM (S := LS) (Map := FM) envZ (Nomm.n4 (slotCall bellZ))).isSome

-- `closed_slotCall`: on a cell (the `%jmp`) and on an atom (the `%jsp`)
#guard zRun (slotCall bellZ) (slotCallFol bellZ) (C (A 5) (A 7))
#guard zRun (slotCall bellZ) (slotCallFol bellZ) (A 5)
-- `closed_slotCallFour`: the `%cal` and the `%csl`, through the merge block
#guard zRun (Nomm.n4 (slotCall bellZ)) (n2 (A 4) (slotCallFol bellZ)) (C (A 5) (A 7))
#guard zRun (Nomm.n4 (slotCall bellZ)) (n2 (A 4) (slotCallFol bellZ)) (A 5)
#guard minkF libT (A 0) 500 [] (C (A 5) (A 7)) (n2 (A 4) (slotCallFol bellZ)) == some (Tone.zero (A 8))

end Comp
end SkaModel
end Formalization
