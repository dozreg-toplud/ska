import lemmas.Ska.CompLazyRun
import lemmas.Ska.CompFrag

/-!
# On fork-free needs, the model over `Lazy` is the fork-free model

Each arm of `CompLazyRun.lean` that takes or returns a `next`, on a
fork-free goal, is the arm of `CompModel.lean` with its result embedded by
`ofSure` (`*_toL`).  `runL_toL`: on a nomm that is pure and has no `%6`,
`runL` on a fork-free goal is `run`, whatever the region; so every theorem
about `run` on the fragment `Frag` holds of `runL` (`runL_ok`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem simpleNextL_toL (goal : CGoal S) :
    (simpleNextL (CGoal.toL goal) : CM Map (NextL S)) = Next.toL <$> simpleNext goal := by
  cases goal <;> simp [simpleNextL, simpleNext, CGoal.toL, Next.toL]

theorem bombL_toL (miss : Option Nat) : (bombL miss : CM Map (NextL S)) = Next.toL <$> bomb miss := by
  simp [bombL, bomb, Next.toL]

theorem splitL_toL (nex : Next S) :
    (splitL (Next.toL nex) : CM Map (Lazy S × Lazy S × Nat)) =
      (fun x => (ofSure x.1, ofSure x.2.1, x.2.2)) <$> split nex := by
  simp [splitL, split, Next.toL, splitLoop_ofSure]

theorem intoL_toL (nex : Next S) (axe : Nat) :
    (intoL (Next.toL nex) axe : CM Map (Lazy S × Lazy S × Nat)) =
      (fun x => (ofSure x.1, ofSure x.2.1, x.2.2)) <$> into nex axe := by
  simp [intoL, into, Next.toL, intoLoopL_ofSure]

theorem copyL_toL (first : Next S) (second : Sure S) :
    (copyL (Next.toL first) (ofSure second) : CM Map (NextL S)) = Next.toL <$> copy first second := by
  simp [copyL, copy, Next.toL, copyLazyL_ofSure]

theorem pastL_pure (cod : Bell → Option Bool) (nex : NextL S) {nom : Nomm} (h : nom.pure = true)
    (region : List Nat) : (pastL cod nex nom region : CM Map (NextL S)) = pure nex := by
  unfold pastL
  simp only [hinted_pure cod nom h]
  split <;> rfl

theorem medeL_toL (th : Jmp) (som : Noun) (s : Sure S) :
    (medeL th som (ofSure s) : CM Map Nat) = mede th som s := by
  simp [medeL, mede, walkLazy_ofSure]

theorem collapseLazyAtomL_toL (nex : Next S) :
    (collapseLazyAtomL (Next.toL nex) : CM Map (Option (Nat × Nat))) = collapseLazyAtom nex := by
  simp only [collapseLazyAtomL, collapseLazyAtom, Next.toL, noneEquivalentL_ofSure]
  split
  · rfl
  split
  · rfl
  refine congrArg (fun k => _ >>= k) (funext fun ned => ?_)
  refine congrArg (fun k => _ >>= k) (funext fun x => ?_)
  refine congrArg (fun k => _ >>= k) (funext fun g => ?_)
  split
  · rfl
  have : (mk ⟨Need.this x.1, (ofSure nex.laz).sure.lok⟩ (ofSure nex.laz).fork (ofSure nex.laz).bond : Lazy S) =
      ofSure ⟨Need.this x.1, nex.laz.lok⟩ := rfl
  rw [this, walkLazy_ofSure]
  simp only [collapseGate, if_true, bind_assoc]
  refine congrArg (fun k => _ >>= k) (funext fun ned' => ?_)
  cases ned' with
  | none => simp
  | this r' => by_cases e : x.1 = r' <;> simp [e]
  | pair p q => simp
  | both r h t => simp

@[simp] theorem Next.toL_laz (n : Next S) : (Next.toL n).laz = ofSure n.laz := rfl
@[simp] theorem Next.toL_th (n : Next S) : (Next.toL n).th = n.th := rfl

theorem collapseLazyAtomL_mk (laz : Sure S) (th : Jmp) :
    (collapseLazyAtomL ⟨ofSure laz, th⟩ : CM Map (Option (Nat × Nat))) = collapseLazyAtom ⟨laz, th⟩ :=
  collapseLazyAtomL_toL ⟨laz, th⟩

theorem splitL_mk (laz : Sure S) (th : Jmp) :
    (splitL ⟨ofSure laz, th⟩ : CM Map (Lazy S × Lazy S × Nat)) =
      (fun x => (ofSure x.1, ofSure x.2.1, x.2.2)) <$> split ⟨laz, th⟩ := splitL_toL ⟨laz, th⟩

theorem intoL_mk (laz : Sure S) (th : Jmp) (axe : Nat) :
    (intoL ⟨ofSure laz, th⟩ axe : CM Map (Lazy S × Lazy S × Nat)) =
      (fun x => (ofSure x.1, ofSure x.2.1, x.2.2)) <$> into ⟨laz, th⟩ axe := intoL_toL ⟨laz, th⟩ axe

theorem pastL_mk (cod : Bell → Option Bool) (laz : Lazy S) (th : Jmp) {nom : Nomm} (h : nom.pure = true)
    (region : List Nat) : (pastL cod ⟨laz, th⟩ nom region : CM Map (NextL S)) = pure ⟨laz, th⟩ :=
  pastL_pure cod _ h region

/-- No `%6` in the nomm. -/
def noSix : Nomm → Bool
  | Nomm.n6 _ _ _ => false
  | Nomm.cons p q => noSix p && noSix q
  | Nomm.n5 p q => noSix p && noSix q
  | Nomm.n7 p q => noSix p && noSix q
  | Nomm.n10 _ v q => noSix v && noSix q
  | Nomm.n3 p => noSix p
  | Nomm.n4 p => noSix p
  | _ => true

/-- **On a pure nomm with no `%6`, `runL` on a fork-free goal is `run`**,
in every region. -/
theorem runL_toL : ∀ (nm : Nomm), nm.pure = true → noSix nm = true → ∀ (goal : CGoal S) (region : List Nat),
    (runL nm (CGoal.toL goal) region : CM Map (NextL S)) = Next.toL <$> run nm goal := by
  intro nm
  induction nm with
  | n0 ax =>
    intro _ _ goal region
    by_cases h0 : ax = 0
    · cases goal <;> simp [runL, run, h0, bombL_toL, CGoal.toL]
    · by_cases h1 : ax = 1
      · simp [runL, run, h0, h1, simpleNextL_toL]
      · simp only [runL, run, h0, h1, if_false, simpleNextL_toL, bind_map_left, map_bind]
        refine congrArg (fun k => _ >>= k) (funext fun nex => ?_)
        simp only [Next.toL, fromL_ofSure]
        cases «from» ax nex.laz <;> rfl
  | n1 k =>
    intro _ _ goal region
    cases goal with
    | done => simp [runL, run, CGoal.toL, Next.toL]
    | pick z o =>
      by_cases e0 : k = A 0
      · simp [runL, run, CGoal.toL, Next.toL, e0]
      · by_cases e1 : k = A 1
        · simp [runL, run, CGoal.toL, Next.toL, e1]
        · simp [runL, run, CGoal.toL, e0, e1, bombL_toL]
    | next laz th => simp [runL, run, CGoal.toL, Next.toL, medeL_toL]
  | n7 p q ihp ihq =>
    intro hp h6 goal region
    simp only [Nomm.pure, noSix, Bool.and_eq_true] at hp h6
    simp only [runL, run, ihq hp.2 h6.2, bind_map_left, map_bind]
    refine congrArg (fun k => _ >>= k) (funext fun nex => ?_)
    rw [Next.goal_toL, ihp hp.1 h6.1]
  | n3 p ihp =>
    intro hp h6 goal region
    simp only [Nomm.pure] at hp
    simp only [noSix] at h6
    have ih' : ∀ laz th, (runL p (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run p (CGoal.next laz th) := fun laz th => ihp hp h6 (CGoal.next laz th) region
    cases goal with
    | next laz th =>
      simp only [runL, run, CGoal.toL, noneEquivalentL_ofSure]
      split
      · exact ih' laz th
      · simp only [collapseLazyAtomL_mk, map_bind]
        refine congrArg (fun k => _ >>= k) (funext fun a => ?_)
        cases a with
        | none => rfl
        | some x => simp [ih', map_bind]
    | pick z o => simp [runL, run, CGoal.toL, ih', map_bind]
    | done => simp [runL, run, CGoal.toL, ih', map_bind]
  | n4 p ihp =>
    intro hp h6 goal region
    simp only [Nomm.pure] at hp
    simp only [noSix] at h6
    have ih' : ∀ laz th, (runL p (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run p (CGoal.next laz th) := fun laz th => ihp hp h6 (CGoal.next laz th) region
    cases goal with
    | next laz th =>
      simp only [runL, run, CGoal.toL, collapseLazyAtomL_mk, map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun a => ?_)
      simp only [ih', map_bind]
      cases a <;> rfl
    | pick z o => simp [runL, run, CGoal.toL, ih', map_bind]
    | done => simp [runL, run, CGoal.toL, ih', map_bind]
  | n5 p q ihp ihq =>
    intro hp h6 goal region
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp' : ∀ laz th, (runL p (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run p (CGoal.next laz th) := fun laz th => ihp hp.1 h6.1 (CGoal.next laz th) region
    have ihq' : ∀ laz th, (runL q (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run q (CGoal.next laz th) := fun laz th => ihq hp.2 h6.2 (CGoal.next laz th) region
    have E : ∀ (o o' : CM Map Nat), o = o' → ∀ (rp rq : Nat), (do
        let o ← o
        let nexq ← runL q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
        let nexq ← pastL noCode nexq p region
        let nexp ← runL p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
        copyL nexp nexq.laz : CM Map (NextL S)) = Next.toL <$> (do
        let o ← o
        let nexq ← run q (CGoal.next (lazyReg rq) (jmp0 o))
        let nexq ← past noCode nexq p
        let nexp ← run p (CGoal.next (lazyReg rp) nexq.th)
        copy nexp nexq.laz) := fun o o' eo rp rq => by
      subst eo
      simp [ihq', ihp', map_bind, pastL_pure noCode _ hp.1, past_pure noCode _ hp.1, copyL_toL]
    cases goal with
    | next laz th =>
      simp only [runL, run, CGoal.toL, collapseLazyAtomL_mk]
      rw [map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun rp => ?_)
      rw [map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun rq => ?_)
      exact E _ _ rfl rp rq
    | pick z o =>
      simp only [runL, run, CGoal.toL]
      rw [map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun rp => ?_)
      rw [map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun rq => ?_)
      exact E _ _ rfl rp rq
    | done =>
      simp only [runL, run, CGoal.toL]
      rw [map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun rp => ?_)
      rw [map_bind]
      refine congrArg (fun k => _ >>= k) (funext fun rq => ?_)
      exact E _ _ rfl rp rq
  | cons p q ihp ihq =>
    intro hp h6 goal region
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp' : ∀ laz th, (runL p (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run p (CGoal.next laz th) := fun laz th => ihp hp.1 h6.1 (CGoal.next laz th) region
    have ihq' : ∀ laz th, (runL q (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run q (CGoal.next laz th) := fun laz th => ihq hp.2 h6.2 (CGoal.next laz th) region
    cases goal <;> simp [runL, run, CGoal.toL, splitL_mk, pastL_pure noCode _ hp.1 region,
      pastL_pure noCode _ hp.2 region, past_pure noCode _ hp.1, past_pure noCode _ hp.2, ihp', ihq',
      copyL_toL, map_bind, bind_map_left, lazyReg]
  | n10 a v q ihv ihq =>
    intro hp h6 goal region
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [noSix, Bool.and_eq_true] at h6
    have ihv' : ∀ laz th, (runL v (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run v (CGoal.next laz th) := fun laz th => ihv hp.1 h6.1 (CGoal.next laz th) region
    have ihq' : ∀ laz th, (runL q (CGoalL.next (ofSure laz) th) region : CM Map (NextL S)) =
        Next.toL <$> run q (CGoal.next laz th) := fun laz th => ihq hp.2 h6.2 (CGoal.next laz th) region
    simp only [runL, run, simpleNextL_toL, bind_map_left, map_bind]
    refine congrArg (fun k => _ >>= k) (funext fun nex => ?_)
    simp [intoL_toL, pastL_pure noCode _ hp.1 region,
      pastL_pure noCode _ hp.2 region, past_pure noCode _ hp.1, past_pure noCode _ hp.2, ihv', ihq',
      copyL_toL, map_bind, bind_map_left]
  | n6 p q r => intro _ h6; simp [noSix] at h6
  | n2 => intro hp; simp [Nomm.pure] at hp
  | n11s => intro hp; simp [Nomm.pure] at hp
  | n11d => intro hp; simp [Nomm.pure] at hp
  | n12 => intro hp; simp [Nomm.pure] at hp
  | mean => intro hp; simp [Nomm.pure] at hp

theorem map_apply {α β : Type} (f : α → β) (x : CM Map α) (g : Gen Map) :
    (f <$> x) g = (x g).map fun p => (f p.1, p.2) := by
  show (x g >>= fun p => pure (f p.1, p.2)) = _
  cases x g <;> rfl

/-- The fragment `Frag` is pure and has no `%6`. -/
theorem frag_pure_noSix : ∀ (nm : Nomm) (goal : CGoal S), Frag nm goal → nm.pure = true ∧ noSix nm = true := by
  intro nm
  induction nm with
  | n0 => intro _ _; exact ⟨rfl, rfl⟩
  | n1 => intro _ _; exact ⟨rfl, rfl⟩
  | n7 p q ihp ihq =>
    intro goal hf
    have a := ihq goal hf.1
    have b := ihp _ (hf.2 Sure.bunt (jmp0 0))
    simp [Nomm.pure, noSix, a, b]
  | n3 p ihp =>
    intro goal hf
    have b : Frag p (CGoal.next (Sure.bunt : Sure S) (jmp0 0)) := by cases goal <;> exact hf _ _
    have b := ihp _ b
    simp [Nomm.pure, noSix, b]
  | n4 p ihp =>
    intro goal hf
    have b : Frag p (CGoal.next (Sure.bunt : Sure S) (jmp0 0)) := by cases goal <;> exact hf _ _
    have b := ihp _ b
    simp [Nomm.pure, noSix, b]
  | n5 p q ihp ihq =>
    intro goal hf
    have a := ihp _ (hf.1 Sure.bunt (jmp0 0))
    have b := ihq _ (hf.2 Sure.bunt (jmp0 0))
    simp [Nomm.pure, noSix, a, b]
  | cons p q ihp ihq =>
    intro goal hf
    have a := ihp _ (hf.1 Sure.bunt (jmp0 0))
    have b := ihq _ (hf.2 Sure.bunt (jmp0 0))
    simp [Nomm.pure, noSix, a, b]
  | n10 x v q ihv ihq =>
    intro goal hf
    have a := ihv _ (hf.1 Sure.bunt (jmp0 0))
    have b := ihq _ (hf.2 Sure.bunt (jmp0 0))
    simp [Nomm.pure, noSix, a, b]
  | n6 => intro _ hf; exact hf.elim
  | n2 => intro _ hf; exact hf.elim
  | n11s => intro _ hf; exact hf.elim
  | n11d => intro _ hf; exact hf.elim
  | n12 => intro _ hf; exact hf.elim
  | mean => intro _ hf; exact hf.elim

/-- **`runL` meets the relation on the fragment**: on a fork-free goal of
`Frag`, what `runL` returns is the embedding of what `run` returns, which
meets `RunOK`. -/
theorem runL_ok (lib : Lib) {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {region : List Nat} {nexL : NextL S}
    (hf : Frag nm goal) (hg : GoalOK g0 goal) (hc : GClean goal)
    (h : runL nm (CGoal.toL goal) region g0 = some (nexL, g1)) :
    ∃ nex, nexL = Next.toL nex ∧ run nm goal g0 = some (nex, g1) ∧ RunOK lib nm goal g0 g1 nex := by
  obtain ⟨hp, h6⟩ := frag_pure_noSix nm goal hf
  rw [runL_toL nm hp h6 goal region, map_apply] at h
  obtain ⟨⟨nex, g1'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨nex, rfl, hr, run_ok lib nm goal g0 g1' nex hf hg hc hr⟩

end Comp
end SkaModel
end Formalization
