import lemmas.Compiler.CompSixKerf
import lemmas.Compiler.CompLeapGate
import lemmas.Ska.CompSixFuel

/-!
# Phase L of the case `%6`: `+leap` returned a rest

Under a `%next` goal, the case `%6` of `+run` pushes

    =/  lep=(unit [gol=next bys=(list need-lazy)])
      ?.  ?=(%next -.goal)  ~
      =/  l  (leap laz.goal q.nomm r.nomm)
      ?~  l  ~
      `[[%next rest.u.l then.goal] bys.u.l]

(`cr6Lep`) and on `?^  lep` runs phase L (`cr6L0`):

    =^  nex  gen  $(goal gol.u.lep)
    =/  bys=(list need-lazy)  bys.u.lep
    |-  ^-  [next _gen]
    ?~  bys  [nex gen]
    =^  nex-new  gen  (copy nex i.bys)
    $(bys t.bys, nex nex-new)

The parts, with the cells of the Nock (`CompRunSixN.lean`):

* `cr6Lep` (475 characters): `+leap` (door arm `441179`, `lp6Bat`, linked by
  `lp6_leap`), then `[0 [[%next rest then.goal] bys]]`; `cr6l_head` takes the
  head of the case to `cr6L0` with that `lep` pushed.
* `cr6L0`: `$` on the subject of the case with the goal (axis `118`) edited
  to `gol.u.lep`, the state put back (axis `254`), `bys` pushed (`cr6L1`),
  the trap (`cr6L2`, `cr6L3`, its battery `cr6LB`).  `cr6l_eq`.
* The trap `cr6LB`: on `~` the pair `[nex gen]`, else `+copy` (door arm
  `220590`, `comp_copy_all`) of `nex` and `i.bys`, the state put back
  (axis `2046`), `bys` and `nex` edited, the trap again.  `cr6l_loop`: it is
  `copyAll`, given the side conditions of each `+copy` (`CopyChain`).

The model (`sixNextLC` at fuel `3`) is `sixNextLC` at fuel `2` on the rest,
then `copyAll`; under `LeapTwice` the fuel `2` is the fuel `3`
(`sixNextLC_leap_none`), so the model is `runLC` of `%6` on the goal
`[%next rest then]` then `copyAll` (`runLC_n6_l`).  No departure: the Hoon
runs `$` on `gol.u.lep` in the same region with the same state, then copies
the `bys` in list order, as `copyAll` does.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The battery of the trap of phase L (the formula that `cr6LA2` quotes). -/
def cr6LB : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 0) (A 14)) (C (A 0) (A 1022))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 2))) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3)))))))))))))))))))

theorem cr6la2_eq : cr6LA2 = C (A 1) cr6LB := rfl

/-! ## The loop of `+copy` over `bys` -/

/-- The side conditions of the `+copy` of each `by` in turn: `CopyH` at the
state of that `+copy`. -/
def CopyChain : Gen (TreapMap mugF) → NextL CSet → List (Lazy CSet) → Prop
  | _, _, [] => True
  | g, nex, b :: rest => CopyH g.re nex.laz b ∧
      ∀ nex' g', copyL nex b g = some (nex', g') → CopyChain g' nex' rest

theorem listN_lazy_nil : listN (([] : List (Lazy CSet)).map Lazy.toNoun) = A 0 := rfl

/-- **The trap of phase L is `copyAll`**, given the side conditions of each
`+copy` (`CopyChain`). -/
theorem cr6l_loop (h7 : slot? 7 ctx = some compK) (x : GenRest) (mono nomm goal region sup LEP : Noun) :
    ∀ (bys : List (Lazy CSet)) (nex : NextL CSet) (g : Gen (TreapMap mugF)), CopyChain g nex bys →
    nock (C cr6LB (C (listN (bys.map Lazy.toNoun)) (C nex.goal.toNoun (C LEP
      (crSubj mono nomm goal region sup (compCore g x ctx)))))) cr6LB
      = (copyAll nex bys g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hD := comp_cp_at
  intro bys
  induction bys with
  | nil =>
    intro nex g _
    rw [listN_lazy_nil]
    simp only [crSubj, compCore]
    nock_open cr6LB
    simp [nock_exec, copyAll, pure, StateT.pure]
  | cons b bs ih =>
    intro nex g hc
    obtain ⟨hH, hk⟩ := hc
    have hcp := comp_copy_all h7 x g nex b hH
    rw [listN_lazy_cons]
    simp only [copyAll]
    rw [bind_apply]
    cases ec : copyL nex b g with
    | none =>
      rw [ec] at hcp
      simp only [crSubj, compCore] at hcp ⊢
      generalize comp.door = Dr at hD hcp ⊢
      nock_open cr6LB
      simp [nock_exec, hD, cr_cp_arm, hcp]
    | some v =>
      obtain ⟨nex', g'⟩ := v
      rw [ec] at hcp
      have ih1 := ih nex' g' (hk nex' g' ec)
      simp only [Option.map_some, Option.bind_some] at hcp ⊢
      simp only [crSubj, compCore] at hcp ih1 ⊢
      generalize comp.door = Dr at hD hcp ih1 ⊢
      nock_open cr6LB
      simp [nock_exec, hD, cr_cp_arm, hcp, ih1]

/-! ## The head: `lep` is `[~ [%next rest then] bys]` -/

/-- **The head of `%6` on the way to phase L**: `+leap` gives `[~ rest bys]`
(given the Nock of `+leap`), so `lep` is `[~ [%next rest then.goal] bys]` and
`?^  lep` holds: `cr6L0` runs with `lep` pushed. -/
theorem cr6l_head (p q r : Nomm) (laz rest : Lazy CSet) (th : Jmp) (bys : List (Lazy CSet))
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (hLp : nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat
      = some (leapN (some (rest, bys)))) :
    nock (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crDol
      = nock (C (C (A 0) (C (CGoalL.next rest th).toNoun (listN (bys.map Lazy.toNoun))))
          (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
            (compCore g x ctx))) cr6L0 := by
  have hD := lp6_at
  simp only [leapN, unitNoun] at hLp
  rw [Nomm.toNoun, cr_disp_n6, cr6_eq]
  simp only [crSubj, compCore, CGoalL.toNoun, Nomm.toNoun] at hLp ⊢
  generalize comp.door = Dr at hD hLp ⊢
  generalize laz.toNoun = LN at hLp ⊢
  generalize rest.toNoun = RN at hLp ⊢
  generalize listN (bys.map Lazy.toNoun) = BN at hLp ⊢
  unfold cr6Head cr6Lep
  simp [nock_exec, hD, lp6_arm, hLp]

/-! ## Phase L: `$` on the rest, then the loop -/

/-- **Phase L** (`cr6L0` ... `cr6L3`): `$` on the subject with the goal
`gol.u.lep` (given its link `hRe`, a model `R` of the run on the rest), the
state put back, then the loop of `+copy` over `bys` (`cr6l_loop`), given the
side conditions of the copies after every result of `R`. -/
theorem cr6l_eq (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (mono nomm goal region sup GR : Noun) (bys : List (Lazy CSet)) (R : CM (TreapMap mugF) (NextL CSet))
    (hRe : nock (crSubj mono nomm GR region sup (compCore g x ctx)) crDol
      = (R g).map fun p => C p.1.goal.toNoun (genNoun p.2 x))
    (hC : ∀ nex g', R g = some (nex, g') → CopyChain g' nex bys) :
    nock (C (C (A 0) (C GR (listN (bys.map Lazy.toNoun)))) (crSubj mono nomm goal region sup (compCore g x ctx)))
      cr6L0
      = ((do let nex ← R; copyAll nex bys : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  rw [bind_apply]
  cases eR : R g with
  | none =>
    rw [eR] at hRe
    simp only [crSubj, compCore] at hRe ⊢
    generalize comp.door = Dr at hRe ⊢
    unfold cr6L0
    simp [nock_exec, cr_bat_dol, hRe]
  | some v =>
    obtain ⟨nex, g'⟩ := v
    rw [eR] at hRe
    have hl := cr6l_loop h7 x mono nomm goal region sup (C (A 0) (C GR (listN (bys.map Lazy.toNoun)))) bys nex g'
      (hC nex g' eR)
    simp only [Option.map_some, Option.bind_some] at hRe ⊢
    simp only [crSubj, compCore] at hRe hl ⊢
    generalize comp.door = Dr at hRe hl ⊢
    generalize listN (bys.map Lazy.toNoun) = BN at hl ⊢
    unfold cr6L0 cr6L1 cr6L2 cr6L3
    rw [cr6la2_eq]
    simp [nock_exec, cr_bat_dol, hRe, hl]

/-! ## The model -/

/-- **The model of phase L**: where `+leap` gives `[~ rest bys]` and, on the
rest, `~` (`LeapTwice`), the case is the case on `[%next rest then]`, then
`copyAll` of `bys`. -/
theorem runLC_n6_l (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (laz rest : Lazy CSet) (th : Jmp)
    (bys : List (Lazy CSet)) (region : List Nat) (hlp : leap laz q r = some (some (rest, bys)))
    (h2 : leap rest q r = some Option.none) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = (do
          let nex ← runLC env msup (Nomm.n6 p q r) (CGoalL.next rest th) region
          copyAll nex bys) := by
  have e : ∀ L J, (runLC env msup (Nomm.n6 p q r) (CGoalL.next L J) region : CM (TreapMap mugF) (NextL CSet))
      = sixNextLC env.cod (runLC env msup p) (runLC env msup q) (runLC env msup r) p q r 3 L J region :=
    fun _ _ => rfl
  rw [e, e, sixNextLC.eq_2]
  simp only [hlp]
  rw [sixNextLC_leap_none env.cod _ _ _ p q r 0 1 rest th region h2]

end Compiler
end Formalization
