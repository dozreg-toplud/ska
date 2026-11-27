import lemmas.Ska.RawInvCheckX
import lemmas.Ska.RawInvCheckCX
import lemmas.Ska.ShapeColAlgFix

/-!
# `NormRun` by enumeration (the evidence for the one hypothesis left on `+shape-collapse`)

`NormRun` of `Compiler/CompShapeColFuel.lean`: every sure need of the lazy
need of the final pass is normal (no `[%pair [%none ~] [%none ~]]` in
`needToOrd` of it).  Checked here on the model's run (`runC`: `runLC envR`
over `LS`/`FM` for `%done` from `gen0`) of every nomm of the enumerations of
tracks C and D (`enum6`, `enumC`, `sixes`, `enumX`, `enumCX`: 8,910 nomms with
`%6` anywhere, indirect calls and their contexts; every run succeeds), and that the model's
`+shape-collapse` then returns at the fuel `fixFuel` of its first tree under
the caps `|`, `&` and `[& |]`.  No nomm breaks it.  The loop takes at most
`4` rounds on them (fuel `4`, the last round the one that changes nothing),
where the bound `fixFuel` is at most `139`.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

mutual
/-- Every sure need of a lazy need is normal. -/
def lazNormB : Lazy LS → Bool
  | Lazy.mk s f b => ordNormal (needToOrd s.ned) && lazNormF f && lazNormBs b
def lazNormF : List ((Nat × Lazy LS) × (Nat × Lazy LS)) → Bool
  | [] => true
  | ((_, y), (_, n)) :: r => lazNormB y && lazNormB n && lazNormF r
def lazNormBs : List (Nat × Lazy LS) → Bool
  | [] => true
  | (_, l) :: r => lazNormB l && lazNormBs r
end

/-- The model's `+shape-collapse` at the fuel of the bound. -/
def scBound (laz : Lazy LS) (cape : Cape) : Bool :=
  match i12 cape (l2i laz) with
  | some t => (shapeCol (fixFuel t) laz cape).isSome
  | Option.none => false

/-- The check on one nomm: the run succeeds, its needs are normal, and the
model's `+shape-collapse` returns at the bound under three caps. -/
def normOk (nm : Nomm) : Bool :=
  match runC nm with
  | some (nex, _) => lazNormB nex.laz && scBound nex.laz Cape.no && scBound nex.laz Cape.yes &&
      scBound nex.laz (Cape.cell Cape.yes Cape.no)
  | Option.none => true

def normAll : List Nomm := enum6 ++ enumC ++ sixes ++ enumX ++ enumCX

/-- The least fuel at which the loop returns (up to `64`), and the bound. -/
def roundsOf (laz : Lazy LS) (cape : Cape) : Nat × Nat :=
  match i12 cape (l2i laz) with
  | some t => (((List.range 64).find? fun k => (fixLoop cape k t).isSome).getD 99, fixFuel t)
  | Option.none => (0, 0)

#guard normAll.length == 8910
#guard (normAll.filter fun nm => (runC nm).isSome).length == 8910
#guard normAll.all normOk

/- The nomms of the examples of the tops: `sixBare` (`[6 [0 2] [0 3] [1 0]]`) and `sixHead`
(`[6 [0 2] [0 6] [0 7]]`). -/
#guard normOk (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n1 (A 0)))
#guard normOk (Nomm.n6 (Nomm.n0 2) (Nomm.n0 6) (Nomm.n0 7))

/- The most rounds any of them takes (under `|`) is `4`, the greatest bound `139`. -/
#guard (normAll.filterMap fun nm => (runC nm).map fun (nex, _) => roundsOf nex.laz Cape.no).foldl
  (fun (a, b) (x, y) => (max a x, max b y)) (0, 0) == (4, 139)

end Raw
end SkaModel
end Formalization
