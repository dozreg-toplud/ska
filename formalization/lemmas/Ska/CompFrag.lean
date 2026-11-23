import lemmas.Ska.CompCons

/-!
# The relation for a fragment of nomm, by induction

`run_ok`: for every nomm and goal of `Frag` (`%0` and `%1` for every goal,
`[7 p q]`, `[3 p]`, `[4 p]`, `[5 p q]` and cons for every goal), what the
model of `run` returns satisfies `RunOK`, from any state, for any goal whose
registers are allocated and distinct.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- The nomm and goals the relation is proved for. -/
def Frag : Nomm → CGoal S → Prop
  | Nomm.n0 _, _ => True
  | Nomm.n1 _, _ => True
  | Nomm.n7 p q, g => Frag q g ∧ ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n4 p, CGoal.done => ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n4 p, CGoal.pick _ _ => ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n4 p, CGoal.next _ _ => ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n3 p, CGoal.pick _ _ => ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n3 p, CGoal.done => ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n3 p, CGoal.next _ _ => ∀ laz th, Frag p (CGoal.next laz th)
  | Nomm.n5 p q, _ => (∀ laz th, Frag p (CGoal.next laz th)) ∧ ∀ laz th, Frag q (CGoal.next laz th)
  | Nomm.cons p q, _ => (∀ laz th, Frag p (CGoal.next laz th)) ∧ ∀ laz th, Frag q (CGoal.next laz th)
  | _, _ => False

/-- **`run` meets the relation on the fragment**, for a goal whose need has
no subterm `pair none none` (`run_clean`: every goal that `run` makes is such). -/
theorem run_ok (lib : Lib) : ∀ (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : Next S),
    Frag nm goal → GoalOK g0 goal → GClean goal → run nm goal g0 = some (nex, g1) →
    RunOK lib nm goal g0 g1 nex := by
  intro nm
  induction nm with
  | n0 ax => intro goal g0 g1 nex _ hg _ h; exact run_n0_ok h hg
  | n1 k =>
    intro goal g0 g1 nex _ hg _ h
    cases goal with
    | done => exact run_n1_done_ok h
    | pick z o => exact run_n1_pick_ok h
    | next laz th => exact run_n1_next_ok h hg
  | n7 p q ihp ihq =>
    intro goal g0 g1 nex hf hg hc h
    simp only [run] at h
    obtain ⟨nexq, g', h1, h2⟩ := bind_some h
    have hq := ihq goal g0 g' nexq hf.1 hg hc h1
    exact run_n7_ok hq (ihp _ _ _ _ (hf.2 _ _) (goalOK_of_runOK hg hq) (run_clean q goal g0 g' nexq hc h1) h2)
  | n4 p ihp =>
    intro goal g0 g1 nex hf hg _ h
    cases goal with
    | done => exact run_n4_done_ok h fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf laz th) hg' hc' h'
    | pick z o => exact run_n4_pick_ok h fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf laz th) hg' hc' h'
    | next laz th => exact run_n4_next_ok h fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf laz th) hg' hc' h'
  | n3 p ihp =>
    intro goal g0 g1 nex hf hg hc h
    cases goal with
    | pick z o => exact run_n3_pick_ok h fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf laz th) hg' hc' h'
    | done => exact run_n3_done_ok h fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf laz th) hg' hc' h'
    | next laz th =>
      exact run_n3_next_ok h hg hc fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf laz th) hg' hc' h'
  | cons p q ihp ihq =>
    intro goal g0 g1 nex hf hg hc h
    exact run_cons_ok h hg hc (fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf.1 laz th) hg' hc' h')
      (fun laz th g g' n hg' hc' h' => ihq _ g g' n (hf.2 laz th) hg' hc' h')
  | n5 p q ihp ihq =>
    intro goal g0 g1 nex hf hg _ h
    exact run_n5_ok h hg (fun laz th g g' n hg' hc' h' => ihp _ g g' n (hf.1 laz th) hg' hc' h')
      (fun laz th g g' n hg' hc' h' => ihq _ g g' n (hf.2 laz th) hg' hc' h')
  | n2 => intro _ _ _ _ hf; exact hf.elim
  | n6 => intro _ _ _ _ hf; exact hf.elim
  | n10 => intro _ _ _ _ hf; exact hf.elim
  | n11s => intro _ _ _ _ hf; exact hf.elim
  | n11d => intro _ _ _ _ hf; exact hf.elim
  | n12 => intro _ _ _ _ hf; exact hf.elim
  | mean => intro _ _ _ _ hf; exact hf.elim

end Comp
end SkaModel
end Formalization
