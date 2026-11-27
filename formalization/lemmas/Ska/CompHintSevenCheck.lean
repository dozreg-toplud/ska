import lemmas.Ska.CompHintRegCheck
import lemmas.Ska.CompHintFrameCheck

/-!
# The fit premise of a kept hint under a general goal, checked on the model (README Gaps 24.19)

A kept hint `[11 [tag h] q]` run under `%next laz th` (the `p` of a `[7 p q']`,
`laz` the result of `q'`) runs `q` under `%next laz epil` when `+past-if`
emits nothing, that is when the lock of `laz.sure` is small and `+sound` of
`q` holds of `laz.sure.ned` (`pastIfL`).  `frameOK_goes` then needs every
product of `q` to fit `laz.sure`: a product that does not fit crashes inside
the frame, with the frame on the interpreter's trace, where `+mink` crashes
after the hint, without it.  When `+sound` is false, `+past-if` parks
`laz.sure` in a bond behind a block of its own (checked outside the frame),
and `q` runs under `Sure.bunt`, which every product fits.

The check `sevenFit`: for `[7 p q']` with `p` a kept hint, or a `%10` whose
value is one, under a goal, the run of `q'`, the lazy need the hint is run
under (`intoL` at the axis for the `%10`), and on a list of subjects:
`(sound, fits, emits, noEnt)`, where `sound` is the test of `+past-if`,
`fits` that every product of the hint's formula on the subjects fits the
need, `emits` that `pastIfL` returns a new bond, `noEnt` that the need has
no entries.  `#guard`s on `d12`, `d13`, the `%7` of `spotArm`'s `S3` (the
direct call of `d22` in place of the recursion), and shapes around them:
* where `sound` holds, `fits` holds on every subject (`d13`, `S3`, and 68
  of the 128 shapes `shapes7`, under `%done` and under `%next (lazy-from-reg 0)`);
* where it fails (`d12`, the formula `[0 3]` under a need that asks a cell),
  `pastIfL` emits the block (60 shapes), and in 50 of them some products do
  not fit (so the premise
  `∀ p, FitsS sur p` would be false there: the bond is what makes the case
  sound).
In every case the need of `q'` has no entries.  So the clause takes the fit as a premise on the formula's products (the
promise of `+sound`), and only in the branch where `+past-if` emits nothing.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintSeven
open HintNest HintKeep HintSpot

/-- `Fits` as a test. -/
def fitsNB : Need → Noun → Bool
  | Need.none, _ => true
  | Need.this _, _ => true
  | Need.pair p q, Noun.cell h t => fitsNB p h && fitsNB q t
  | Need.both _ p q, Noun.cell h t => fitsNB p h && fitsNB q t
  | _, _ => false

def looksSB (lok : LS) (n : Noun) : Bool := (HoonSet.toList lok).all fun a => (slot? a n).isSome

/-- `FitsS` as a test. -/
def fitsSB (s : Sure LS) (n : Noun) : Bool := fitsNB s.ned n && looksSB s.lok n

/-- The products of `f` on the subjects (`+mink`, no scry). -/
def prods (f : Noun) (ss : List Noun) : List Noun :=
  ss.filterMap fun s => match minkF libT (A 0) 500 [] s f with
    | some (Tone.zero p) => some p
    | _ => Option.none

/-- The kept hint inside `p`: its formula, the formula's Nock (the body),
and the axis of the `%10` it is the value of (`none` when `p` is the hint). -/
def keptIn : Nomm → Option (Nomm × Noun × Option Nat)
  | Nomm.n11d _ _ q body => some (q, body, Option.none)
  | Nomm.n11s _ q body => some (q, body, Option.none)
  | Nomm.n10 a (Nomm.n11d _ _ q body) _ => some (q, body, some a)
  | Nomm.n10 a (Nomm.n11s _ q body) _ => some (q, body, some a)
  | _ => Option.none

/-- **The check**: `(sound, fits, emits, noEnt)` for `[7 p q']` under `G`. -/
def sevenFit (nm : Nomm) (G : CGoalL LS) (ss : List Noun) : Option (Bool × Bool × Bool × Bool) :=
  match nm with
  | Nomm.n7 p q' => do
      let (fq, body, ax) ← keptIn p
      let (nx, g) ← runLCH (S := LS) (Map := FM) envH sndH true (some p) q' G [] gS
      let (laz, th, g) ← (match ax with
        | Option.none => some (nx.laz, nx.th, g)
        | some a => (intoL (S := LS) (Map := FM) ⟨nx.laz, nx.th⟩ a g).map fun ((don, _, o), g') => (don, jmp0 o, g'))
      let sound := HoonSet.small laz.sure.lok && sndH fq (needToOrd laz.sure.ned)
      let fits := (prods body ss).all (fitsSB laz.sure)
      let (n2, _) ← pastIfL (Map := FM) sndH ⟨laz, th⟩ fq [] g
      pure (sound, fits, n2.laz.bond.length != laz.bond.length, (entries laz).isEmpty)
  | _ => Option.none

/-- The subjects of the dump and a few more. -/
def subs : List Noun := [C (A 1) (A 2), C (A 1) (C (A 2) (A 3)), C (C (A 1) (A 2)) (A 3), C (A 0) (A 1),
  C (C (A 0) (A 1)) (A 0), A 7, C (C (A 1) (A 2)) (C (A 3) (A 4)), C (A 5) (C (C (A 1) (A 2)) (A 9)),
  C (A 1) (C (A 2) (C (C (A 3) (A 4)) (A 5))), C (C (A 1) (A 2)) (C (C (A 3) (C (A 6) (A 7))) (A 5))]

def gReg : CGoalL LS := CGoalL.next (ofSure (lazyReg 0)) (jmp0 1)

/-- The direct call of `d22` (`[2 [0 1] [1 F] b]`, `F` the arm of `R`). -/
def callOf : Nomm → Option Nomm
  | Nomm.n2 p q (some i) => some (Nomm.n2 p q (some i))
  | Nomm.n7 p q => (callOf q).orElse fun _ => callOf p
  | Nomm.n11d _ _ q _ => callOf q
  | _ => Option.none
def call22 : Nomm := (callOf (nmOf "d22")).getD (Nomm.n0 0)

/-- `spotArm`'s `S3` formula with the call of `d22`: `[7 [10 6 [spot [0 13]] [0 1]] call]`. -/
def s3c : Nomm := Nomm.n7 (Nomm.n10 6 (Nomm.n11d tagSpot (Nomm.n1 (A 0)) (z 13) (C (A 0) (A 13))) (z 1)) call22

-- `d12` (`[7 [spot [0 3]] [4 [0 2]]]`) and `d13` (`[7 [spot [[0 2] [0 3]]] [4 [0 2]]]`)
#guard (nmOf "d12" matches Nomm.n7 _ _) && (nmOf "d13" matches Nomm.n7 _ _)
#guard sevenFit (nmOf "d12") CGoalL.done subs == some (false, false, true, true)
#guard sevenFit (nmOf "d13") CGoalL.done subs == some (true, true, false, true)
#guard sevenFit (nmOf "d12") gReg subs == some (false, false, true, true)
#guard sevenFit (nmOf "d13") gReg subs == some (true, true, false, true)
-- `S3`: the spot's need is the `don` of the `%10` at `6`, from the callee's need
#guard call22 matches Nomm.n2 _ _ (some _)
#guard sevenFit s3c CGoalL.done subs == some (true, true, false, true)
#guard sevenFit s3c gReg subs == some (true, true, false, true)

/-- Shapes around them: kept spots and `%bout`s whose formula is `[0 a]`, a
cons, `[4 ..]`, `[1 k]`, under `q'` that asks a cell or an atom or nothing. -/
def shapes7 : List Nomm :=
  let ks : List Nomm := [z 1, z 2, z 3, Nomm.cons (z 2) (z 3), Nomm.n4 (z 3), Nomm.n1 (A 5), Nomm.n1 (C (A 1) (A 2)),
    Nomm.cons (Nomm.n1 (A 0)) (z 1)]
  let qs : List Nomm := [Nomm.n4 (z 2), z 2, z 3, z 1, Nomm.n4 (z 1), Nomm.cons (z 3) (z 2), Nomm.n1 (A 0),
    Nomm.n3 (z 2)]
  ks.flatMap fun k => qs.flatMap fun q =>
    [Nomm.n7 (Nomm.n11d tagSpot (Nomm.n1 (A 0)) k k.toNoun) q, Nomm.n7 (Nomm.n11s HintTag.bout k k.toNoun) q]

/-- `+sound` gives the fit; without it `+past-if` emits. -/
def soundFits (r : Option (Bool × Bool × Bool × Bool)) : Bool :=
  match r with
  | some (true, fits, emits, _) => fits && !emits
  | some (false, _, emits, _) => emits
  | Option.none => false

#guard shapes7.length == 128
#guard shapes7.all fun nm => soundFits (sevenFit nm CGoalL.done subs)
#guard shapes7.all fun nm => soundFits (sevenFit nm gReg subs)
-- the misfit where `+sound` fails is real: some shapes have products that do not fit
#guard (shapes7.filter fun nm => (sevenFit nm CGoalL.done subs).map (fun r => !r.2.1) == some true).length > 0
-- and `+sound` holds somewhere with a need that asks something (not only `this`/`none`)
#guard (shapes7.filter fun nm => (sevenFit nm CGoalL.done subs).map (fun r => r.1) == some true).length > 0

/-- The counts: `+sound` true, false, a misfit among the products, `q'`'s
need without entries, the run failing. -/
def counts (G : CGoalL LS) : List Nat :=
  [(shapes7.filter fun nm => (sevenFit nm G subs).map (·.1) == some true).length,
   (shapes7.filter fun nm => (sevenFit nm G subs).map (·.1) == some false).length,
   (shapes7.filter fun nm => (sevenFit nm G subs).map (·.2.1) == some false).length,
   (shapes7.filter fun nm => (sevenFit nm G subs).map (·.2.2.2) == some true).length,
   (shapes7.filter fun nm => (sevenFit nm G subs).isNone).length]
#guard counts CGoalL.done == [68, 60, 50, 128, 0]
#guard counts gReg == [68, 60, 50, 128, 0]

end HintSeven

end Comp
end SkaModel
end Formalization
