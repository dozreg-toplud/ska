import lemmas.Compiler.CompRunHintTab

/-!
# The run link with hints inside direct calls: examples (README Gaps 25)

Against `runLCH env (sfSnd cod) true msup`, on every goal with `GInv`, with
no `HintSound` hypothesis (`comp_run_hint_tab`, `comp_run_hint_ana`):

* a direct call whose subject part holds a `!:` spot and whose callee's body
  is `[11 [%spot [1 s]] ..]`, itself under a kept spot (so `+sound` reads the
  callee's entry);
* `spotArm`: the arm of the `!:` gate `|=(a=* ?@(a 0 +($(a +.a))))` as the
  analysis made it (`tools/hoon/hinttab.hoon`, poke 0, the entry of the
  callee; output `tools/hoon/hinttab.txt`): four kept dynamic spots, nested,
  a `%6`, a `%4`, a `%10` whose value is hinted, and the recursive direct
  call under three of the spots.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ctx : Noun}

/-- The clue of a `!:` spot with path `~`: `[~ [l c] l' c']`. -/
def spotK (l c l' c' : Nat) : Noun := C (A 0) (C (C (A l) (A c)) (C (A l') (A c')))

/-- **A hint inside a direct call whose callee's body is a spot**, under a
kept spot: `[11 [%spot [1 s]] [2 [11 [%spot [1 s]] [0 1]] [1 k] [~ b ~]]]`,
the entry of `b` being `[11 [%spot [1 s']] q']`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (ht : SfTable (nommOf cod)) (env : CallEnv) (E : GenRest → Prop) (msup : Option Nomm)
    (s s' k body body' : Noun) (q' : Nomm) (b : Bell)
    (hm : nommOf cod b = some (Nomm.n11d 0x746f7073 (Nomm.n1 s') q' body'))
    (hb : CallOk env cod ctx E msup (Nomm.n11d 0x746f7073 (Nomm.n1 s) (Nomm.n0 1) body) (Nomm.n1 k) b)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup)
      (Nomm.n11d 0x746f7073 (Nomm.n1 s)
        (Nomm.n2 (Nomm.n11d 0x746f7073 (Nomm.n1 s) (Nomm.n0 1) body) (Nomm.n1 k) (some (b, Option.none))) body)
      goal region g :=
  (comp_run_hint_tab h7 hcode ht env E _ rfl msup region (by simp [HintCallsC, hb])
    (by intro b' m; simp [hintBells] at m; subst m; exact ⟨_, hm⟩)).link goal g hi

/-- **The arm of a `!:` gate**, `|=(a=* ?@(a 0 +($(a +.a))))`, as the
analysis made it (`tools/hoon/hinttab.hoon`, poke 0): `F` is the arm's
formula, `b` its bell (the recursion), `B0`, `B2`, `B3` the hinted formulas
the nomm keeps. -/
def spotArm (F : Noun) (b : Bell) (B0 B2 B3 : Noun) : Nomm :=
  Nomm.n11d 0x746f7073 (Nomm.n1 (spotK 108 29 108 48))
    (Nomm.n6 (Nomm.n6 (Nomm.n3 (Nomm.n0 6)) (Nomm.n1 (A 1)) (Nomm.n1 (A 0))) (Nomm.n1 (A 0))
      (Nomm.n11d 0x746f7073 (Nomm.n1 (spotK 108 36 108 47))
        (Nomm.n4 (Nomm.n11d 0x746f7073 (Nomm.n1 (spotK 108 38 108 46))
          (Nomm.n7 (Nomm.n10 6 (Nomm.n11d 0x746f7073 (Nomm.n1 (spotK 108 42 108 45)) (Nomm.n0 13) (C (A 0) (A 13)))
              (Nomm.n0 1))
            (Nomm.n2 (Nomm.n0 1) (Nomm.n1 F) (some (b, Option.none))))
          B3))
        B2))
    B0

/-- The subject formula of the recursive call in `spotArm`. -/
def spotArmSub : Nomm :=
  Nomm.n10 6 (Nomm.n11d 0x746f7073 (Nomm.n1 (spotK 108 42 108 45)) (Nomm.n0 13) (C (A 0) (A 13))) (Nomm.n0 1)

/-- **The `!:` gate's arm**, on every goal with `GInv`, from the facts of
the analysis on the code table (`CodeAna`) and the `CallOk` of its
recursive call (at `msup` the call's subject formula). -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (hana : CodeAna cod) (env : CallEnv) (E : GenRest → Prop) (msup : Option Nomm)
    (F B0 B2 B3 : Noun) (b : Bell) (hb : CallOk env cod ctx E (some spotArmSub) (Nomm.n0 1) (Nomm.n1 F) b)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup) (spotArm F b B0 B2 B3) goal region g :=
  comp_run_hint_anaX h7 hcode hana env E _ rfl msup region
    (by simp only [spotArm, HintCallsC, and_true, true_and]; exact hb) goal g hi

end Compiler
end Formalization
