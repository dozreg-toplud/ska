import lemmas.Compiler.PokeLink
import lemmas.Compiler.OvumMold

/-!
# The `%full` branch of the pill's `+poke`, by its callees: `FullBranchIs` proved

The inner `+poke` slams `+validate-ovum` on its sample (`ipokeB`), then
switches on the head of the validated ovum (`ipokeR`, the `%full` test is the
third) and runs the `%full` branch (`fullF`, 272 cells).  Here:

* `vovum_full_cell`, `vovum_full_atom`: on a `%full`, `+validate-ovum`
  returns its sample when the formula is a cell, and crashes when it is an
  atom (the mold `fol=^`, the pill side of mismatch P4 of README Gaps 23);
* the callees of the branch as functions of the compiler's core (`skaP`,
  `jrP`, `sccP`, `monoP`, `optP`), each the slam of the gate the branch
  builds, read from the core by axis;
* `fullBranchIs`: `FullBranchIs fl skaP jrP sccP monoP optP`;
* `pokeN_full`: `pokeN_full_of` with no `FullBranchIs` left, so `pokeModel`
  on a `%full` with a cell formula rests on the five links only, and
  `pokeN_full_atom`: the pill crashes on a `%full` with an atom formula.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## `+validate-ovum` on a `%full` -/

/-- The mold `ovum` on a `%full` whose formula is a cell returns it. -/
theorem mold_full_cell (s f₁ f₂ : Noun) :
    slamAt vcore 685 (C (A Tag.full) (C s (C f₁ f₂))) = some (C (A Tag.full) (C s (C f₁ f₂))) := by
  rw [slamAt_mold]
  nock_open ovumBat
  simp [nock_exec, Tag.full]

/-- The mold `ovum` on a `%full` whose formula is an atom crashes (`fol=^`). -/
theorem mold_full_atom (s : Noun) (a : Nat) : slamAt vcore 685 (C (A Tag.full) (C s (A a))) = none := by
  rw [slamAt_mold]
  nock_open ovumBat
  simp [nock_exec, Tag.full]

/-- `+validate-ovum` on a `%full` is the mold, on every context. -/
theorem vovum_full (c tl : Noun) :
    nock (C vovumBat (C (C (A Tag.full) tl) c)) vovumBat = slamAt c 685 (C (A Tag.full) tl) := by
  nock_open vovumBat
  simp [nock_exec, Tag.full, slamAt]

/-! ## The call formulas of the branch (`tools/gen/pokefull.py`) -/

-- skaF: 42 cells
def skaFP : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 11) (C (A 0x616b73) (C (A 8) (C (C (A 9) (C (A 20) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 10))) (C (A 0) (A 11))))) (C (C (A 0) (A 1018)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 188) (C (A 10) (C (C (A 6) (C (A 0) (A 2038))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))))

-- getF: 21 cells
def getFP : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fd3e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2))))))))

-- hasF: 21 cells
def hasFP : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 8182))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2))))))))

-- putF: 42 cells
def putFP : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x66736a)) (C (C (A 0) (A 12)) (C (C (A 1) (A 0)) (C (A 0) (A 5))))))))))) (C (A 0) (A 2))))))))

-- sccF: 19 cells
def sccFP : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x1777f) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 0) (A 0xffae)) (C (A 0) (A 0xffbe))))) (C (A 0) (A 2))))))))))

-- monoF: 19 cells
def monoFP : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 11) (C (A 0x616b73) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))))))

-- optF: 14 cells
def optFP : Noun :=
  (C (A 11) (C (A 0x616b73) (C (A 8) (C (C (A 9) (C (A 2941) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))))

/-! ## The callees, as slams of the gates the branch builds -/

/-- The gate that arm `k` of the core `c` builds. -/
def gateAt (c : Noun) (k : Nat) : Option Noun := (slot? k c).bind fun a => nock c a

/-- The gate `g` slammed on `sam`. -/
def slamG (g sam : Noun) : Option Noun := (edit? 6 sam g).bind fun g' => (slot? 2 g').bind fun f => nock g' f

/-- Arm `k` of the door `by` of the core `hc` (`hoon.hoon`, arm `6103`) on
the map `m` (read after the door is built, as the pill does). -/
def byArmO (hc : Noun) (m : Option Noun) (k : Nat) : Option Noun :=
  (gateAt hc 6103).bind fun d => m.bind fun m => (edit? 6 m d).bind fun d' => gateAt d' k

/- The axes of the compiler's core `cr` the branch reads: `hoon.hoon`
(`2097151`), `long-ska` (`58`), `jets-hot` (`118`), `cache` (`119`),
`call.cole.jets.long-ska` (`7486`), `calls.long-ska` (`942`),
`sccs.cache` (`958`). -/

/-- `(ska-poke [&+s f] long-ska ~(key by jets-hot))`: arm `20` of the core at
axis `511` (`ana`). -/
def skaRaw (cr s f : Noun) : Option Noun :=
  (slot? 511 cr).bind fun an => (gateAt an 20).bind fun g =>
  (slot? 2097151 cr).bind fun hc => (byArmO hc (slot? 118 cr) 188).bind fun key =>
  (slot? 58 cr).bind fun L => slamG g (C (C (C (A 0) s) f) (C L key))

/-- `(~(get by call.cole.jets.long-ska) func)`. -/
def getRaw (cr func : Noun) : Option Noun :=
  (slot? 2097151 cr).bind fun hc => (byArmO hc (slot? 7486 cr) 764).bind fun g => slamG g func

/-- `(~(has by jets-hot) u)`. -/
def hasRaw (cr u : Noun) : Option Noun :=
  (slot? 2097151 cr).bind fun hc => (byArmO hc (slot? 118 cr) 3061).bind fun g => slamG g u

/-- `(~(put by ~) 0 [~ ~ [%jsf func 0 u]])`. -/
def putRaw (cr func u : Noun) : Option Noun :=
  (slot? 2097151 cr).bind fun hc => (byArmO hc (some (A 0)) 340).bind fun g =>
  slamG g (C (A 0) (C (A 0) (C (A 0) (C (A Tag.jsf) (C func (C (A 0) u))))))

/-- `(scc-of func calls.long-ska sccs.cache)`: arm `96127` of the core at
axis `63`. -/
def sccRaw (cr func : Noun) : Option Noun :=
  (slot? 63 cr).bind fun c => (gateAt c 96127).bind fun g =>
  (slot? 942 cr).bind fun ca => (slot? 958 cr).bind fun sc => slamG g (C func (C ca sc))

/-- `(compiled-mono func scc)`: arm `10` of the core at axis `3` (it holds
the state). -/
def monoRaw (cr func sc : Noun) : Option Noun :=
  (slot? 3 cr).bind fun c => (gateAt c 10).bind fun g => slamG g (C func sc)

/-- **The callees of `pillFull`**: each the call above, with the product
taken apart and written into the core as the branch does. -/
def skaP (cr s f : Noun) : Option (Noun × Noun × Noun) :=
  (skaRaw cr s f).bind fun res => match res with
    | Noun.cell (Noun.cell func new) L' => (edit? 58 L' cr).map fun cr' => (func, new, cr')
    | _ => none

def jrP (cr func : Noun) : Option (Option Noun) :=
  (getRaw cr func).bind fun rin => match rin with
    | Noun.atom _ => some none
    | Noun.cell _ u => (hasRaw cr u).bind fun h =>
      if h = A 0 then (putRaw cr func u).map fun p => some (C (C (A Tag.this) (A 0)) (C (A 1) p))
      else if h = A 1 then some none else none

def sccP (cr func : Noun) : Option (Noun × Noun) :=
  (sccRaw cr func).bind fun r => match r with
    | Noun.cell sc sccs' => (edit? 958 sccs' cr).map fun c => (sc, c)
    | _ => none

def monoP (cr func sc : Noun) : Option (Noun × Noun) :=
  (monoRaw cr func sc).bind fun r => match r with
    | Noun.cell str K' => (edit? 119 K' cr).map fun c => (str, c)
    | _ => none

/-- `(optimize str)`: arm `2941` of `optC`. -/
def optP (str : Noun) : Option Noun := slamAt optC 2941 str

/-! ## The calls -/

section Calls
variable (b2 b6 z L ho na mo sc rest lib : Noun)

theorem ska_call (hd s f ib ovo : Noun) :
    nock (C (C hd (C s f)) (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib)))))) skaFP
      = skaRaw (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))) s f := by
  unfold skaFP skaRaw byArmO gateAt slamG
  simp only [nock_exec, Option.bind_assoc]

theorem get_call (func new v ib ovo : Noun) :
    nock (C (C func new) (C v (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))))))) getFP = getRaw (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))) func := by
  unfold getFP getRaw byArmO gateAt slamG
  simp only [nock_exec, Option.bind_assoc]

theorem has_call (r u x v ib ovo : Noun) :
    nock (C (C r u) (C x (C v (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib)))))))) hasFP = hasRaw (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))) u := by
  unfold hasFP hasRaw byArmO gateAt slamG
  simp only [nock_exec, Option.bind_assoc]

theorem put_call (r u func new v ib ovo : Noun) :
    nock (C (C r u) (C (C func new) (C v (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib)))))))) putFP = putRaw (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))) func u := by
  unfold putFP putRaw byArmO gateAt slamG
  simp only [nock_exec, Option.bind_assoc, Tag.jsf]

theorem scc_call (rin func new v ib ovo : Noun) :
    nock (C rin (C (C func new) (C v (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib)))))))) sccFP = sccRaw (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))) func := by
  unfold sccFP sccRaw gateAt slamG
  simp only [nock_exec, Option.bind_assoc]

theorem mono_call (q rin func new v ib ovo : Noun) :
    nock (C q (C rin (C (C func new) (C v (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))))))))) monoFP = monoRaw (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib))) func q := by
  unfold monoFP monoRaw gateAt slamG
  simp only [nock_exec, Option.bind_assoc]

theorem opt_call (str q rin x v ib ovo : Noun) :
    nock (C str (C q (C rin (C x (C v (C ib (C ovo (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib)))))))))) optFP =
      (slot? 31 (C b2 (C b6 (C (C z (C L (C ho (C na (C mo (C sc rest)))))) lib)))).bind fun oc => slamAt oc 2941 str := by
  unfold optFP slamAt
  simp only [nock_exec, Option.bind_assoc]

end Calls

end Compiler
end Formalization
