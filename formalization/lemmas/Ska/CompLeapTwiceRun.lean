import lemmas.Ska.CompLeapTwice
import lemmas.Compiler.CompRunSixL

/-!
# `LeapTwice` discharged: the fuel `3` and phase L without it

`leapTwice_noAx0`: on branches with `Bake.NoAx0` (every `%10` axis not `0`)
`+pass-both` gives parts with nonzero axes (`pbt_gate`), so `leap_twice`
applies: `LeapTwice laz q r` holds for every lazy need `laz`.

The theorems that took `LeapTwice` as a hypothesis, restated without it
(the originals are unchanged):
- `sixNextLC_fuel_tw` (`sixNextLC_fuel` of `Ska/CompSixFuel.lean`): the fuel
  `3` of the model is as good as any larger fuel, so it is the Hoon's
  unbounded recursion of `%6`;
- `comp_run_n6_l_tw`, `res_n6_l_tw`, `comp_run_n6_l_nf_tw`,
  `comp_run_n6_l_k_tw` (`Compiler/CompRunSixL.lean`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- **`LeapTwice` holds** on branches with `Bake.NoAx0`, for every lazy need. -/
theorem leapTwice_noAx0 {S : Type} [HoonSet S] {laz : Lazy S} {q r : Nomm} (hq : Bake.NoAx0 q)
    (hr : Bake.NoAx0 r) : LeapTwice laz q r := by
  obtain ⟨l, el, pl, -⟩ := pbt_gate passIn_compK q r hq hr
  refine leap_twice fun pas ep e he => ?_
  rw [el, Option.some.injEq] at ep
  subst ep
  exact (pl e he).1

/-- **The fuel `3` is as good as any larger one**, on branches with
`Bake.NoAx0`. -/
theorem sixNextLC_fuel_tw {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
    (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm)
    (k : Nat) (laz : Lazy S) (th : Jmp) (region : List Nat) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) :
    sixNextLC cod rp rq rr p q r (k + 3) laz th region = sixNextLC cod rp rq rr p q r 3 laz th region :=
  sixNextLC_fuel cod rp rq rr p q r k laz th region (leapTwice_noAx0 hq hr)

variable {ctx : Noun}

/-- **Phase L** (`comp_run_n6_l`) without `LeapTwice`. -/
theorem comp_run_n6_l_tw (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p q r : Nomm)
    (region : List Nat) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (hRe : CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next rest th) region g)
    (hReR : ∀ nex g', runLC env msup (Nomm.n6 p q r) (CGoalL.next rest th) region g = some (nex, g') →
      GRes g (CGoalL.next rest th) g' nex) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g :=
  comp_run_n6_l h7 env msup p q r region hq hr laz th g hinv rest bys hlp (leapTwice_noAx0 hq hr) hRe hReR

/-- **What phase L returns** (`res_n6_l`) without `LeapTwice`. -/
theorem res_n6_l_tw {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (laz : Lazy CSet) (th : Jmp) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet)
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (hi : GInv g (CGoalL.next laz th)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (hReR : ∀ nex g', runLC env msup (Nomm.n6 p q r) (CGoalL.next rest th) region g = some (nex, g') →
      GRes g (CGoalL.next rest th) g' nex)
    (h : runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex :=
  res_n6_l laz th g g' nex rest bys hlp (leapTwice_noAx0 hq hr) hi hq hr hReR h

/-- **Phase L, then phase S** on a fork-free rest (`comp_run_n6_l_nf`)
without `LeapTwice`. -/
theorem comp_run_n6_l_nf_tw (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (s : Sure CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (Lazy.mk s [] [], bys))) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g :=
  comp_run_n6_l_nf h7 hcode env msup p q r region P Q R hq hr laz th g hinv s bys hlp
    (leapTwice_noAx0 hq hr)

/-- **Phase L, then phase K** on the rest (`comp_run_n6_l_k`) without
`LeapTwice`. -/
theorem comp_run_n6_l_k_tw (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt rest.fork rest.bond) = false)
    (hkt : kerfTest q r rest = true) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g :=
  comp_run_n6_l_k h7 hcode env msup p q r region P Q R hq hr laz th g hinv rest bys hlp
    (leapTwice_noAx0 hq hr) hne hkt

end Compiler
end Formalization
