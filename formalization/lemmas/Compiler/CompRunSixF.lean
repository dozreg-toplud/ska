import lemmas.Compiler.CompForkLoop
import lemmas.Compiler.CompSixKerf

/-!
# Phase F of `%6`: its head

Phase F (the branch of `%6` under a `%next` goal whose `+leap` is `~`, whose
need with the bunt sure is not `+none-equivalent`, and whose `+kerf` test
says no) is the chain `cr6F0` ... of `CompRunSixN.lean`:

    =^  r-cond  gen  re                        :: cr6F0
    =^  [nex-0 nex-1]  gen  (fork nex r-cond)  :: cr6F1
    =^  region-id  gen  id                     :: cr6F2
    =/  region-branch  [region-id region]      :: cr6F3
    ... the reads of `cond`, the runs of `r` and `q`, `+sect`, `+past-fork`,
    the `%brn` block, `+lazy-shut`, the run of `p`, `+copy`

The model is `sixNextForkC` of `Ska/CompRunLC.lean`, in the same order
(`re`, `forkL`, `idM`, `rid :: region`, `getCond`, the run of `r`, `getCond`,
the run of `q`, `sect`, `pastFork`, `emit` of the `%brn` block, `lazyShut`,
the run of `p` on `[%next [[%this r-cond] ~] ~ ~] ~ o]`, `copyL`).  No
departure.

`cr6f_s03`: the first four pushes (`+re`, `+fork` by `comp_fork_all`, `+id`,
the region), then a continuation from `cr6F4` on.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The state after `+re`. -/
def reG (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) := { g with re := g.re + 1 }

theorem re_ap (g : Gen (TreapMap mugF)) : (re : CM (TreapMap mugF) Nat) g = some (g.re, reG g) := rfl

/-- **The head of phase F** (`cr6F0` ... `cr6F3`): `+re` (the register of
the test), `+fork` of the goal on it (`comp_fork_all`), `+id` and the region
`[region-id region]` of the branches, then a continuation `K` from `cr6F4`
on, given its link on every result of `+fork`. -/
theorem cr6f_s03 (h7 : slot? 7 ctx = some compK) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (K : NextL CSet → NextL CSet → Nat → Nat → CM (TreapMap mugF) (NextL CSet))
    (hK : ∀ n0 n1 g3, forkL ⟨laz, th⟩ g.re (reG g) = some ((n0, n1), g3) →
      nock (C (listNoun A (g3.id :: region)) (C (A g3.id) (C (C n0.goal.toNoun n1.goal.toNoun)
          (C (A g.re) (C (A 0)
            (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
              (compCore (idG g3) x ctx))))))) cr6F4
        = (K n0 n1 g.re g3.id (idG g3)).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun
        (listNoun A region) sup (compCore g x ctx))) cr6F0
      = ((do
          let rc ← re
          let (n0, n1) ← forkL ⟨laz, th⟩ rc
          let rid ← idM
          K n0 n1 rc rid : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hfk := comp_fork_all h7 x (reG g) laz th g.re
  have hD1 := comp_re_at
  have hD2 := fk_at
  have hD3 := comp_id_at
  have hr := comp_re' ctx x g
  simp only [bind_apply, re_ap, Option.bind_some]
  cases ef : forkL ⟨laz, th⟩ g.re (reG g) with
  | none =>
    rw [ef] at hfk
    simp only [Option.bind_none, Option.map_none]
    simp only [crSubj, compCore, reG] at hfk hr ⊢
    generalize comp.door = Dr at hD1 hD2 hD3 hfk hr ⊢
    unfold cr6F0 cr6F1
    simp [nock_exec, hD1, hr, hD2, fk_arm, hfk]
  | some v =>
    obtain ⟨⟨n0, n1⟩, g3⟩ := v
    rw [ef] at hfk
    have hk := hK n0 n1 g3 ef
    have hi := comp_id' (ctx := ctx) x g3
    simp only [Option.bind_some, Option.map_some, idM_ap] at hfk ⊢
    simp only [listNoun, crSubj, compCore, reG] at hk hfk hr ⊢
    generalize comp.door = Dr at hD1 hD2 hD3 hfk hk hr hi ⊢
    unfold cr6F0 cr6F1 cr6F2 cr6F3
    simp [nock_exec, hD1, hr, hD2, fk_arm, hfk, hD3, hi, hk]

end Compiler
end Formalization
