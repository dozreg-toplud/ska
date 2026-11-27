import lemmas.Ska.RawInvCLSARunBase
import lemmas.Ska.RawInvCLIntoSpec

/-!
# Single assignment with calls: the count of `+into`

README Gaps 14 (b), track D.  The field `into` of `SarStepsW`
(`RawInvCLSARun.lean`): `+into` meets the count `SCR` of
`RawInvCLSARunBase.lean` from the goal's tree to the two halves.

* `+into-need`'s loop (`scit_loop`, by strong induction on the axis) with
  the potential "the need, the registers on the tack, the definitions of the
  pending ops": a `%this` step allocates two fresh registers and pends a
  `%con` defining the old one, a `%both` step takes the halves by `+must`
  (`scit_must`: a fresh register when the half is a `pair` or `none`) and
  pends a `%con` defining the old root, a `pair` step moves a half to the
  tack; at the axis the pending ops are added and the tack rolled up with
  `+cons-need`, which keeps the registers (`scit_side`, `scit_roll`).
* `scit_need`, `scit_sure`: `+into-need`, `+into-sure`.
* `scit_prune`: `+lazy-prune` drops whole entries (`its_pruneSub`).
* **`scit_loopL`** (mutual with `scit_forks`, `scit_bonds`): the walk.
* **`scit_into`**: the field.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-! ## Helpers -/

/-- The registers on a tack. -/
def scitT (tack : List (Bool × Need)) : List Nat := tack.flatMap fun e => flattenNeed e.2

theorem scit_frame {α : Type} {ri : List Nat} {m : CM Map α} {ro : α → List Nat} (X : List Nat)
    (h : SCR (Map := Map) ri m ro) : SCR (Map := Map) (ri ++ X) m (fun x => ro x ++ X) := by
  intro g x g' s e
  obtain ⟨s1, l1, c1⟩ := h g x g' s e
  exact ⟨s1, l1, fun y => by have := c1 y; simp only [List.count_append]; omega⟩

theorem scit_fn : flattenNeed Need.none = [] := rfl
theorem scit_ft (r : Nat) : flattenNeed (Need.this r) = [r] := rfl
theorem scit_fp (p q : Need) : flattenNeed (Need.pair p q) = flattenNeed p ++ flattenNeed q := rfl
theorem scit_fb (r : Nat) (h t : Need) :
    flattenNeed (Need.both r h t) = [r] ++ (flattenNeed h ++ flattenNeed t) := rfl

theorem scit_side (h : Bool) (a b : Need) (y : Nat) :
    (flattenNeed (side h a b)).count y = (flattenNeed a).count y + (flattenNeed b).count y := by
  by_cases e : a = Need.none ∧ b = Need.none
  · obtain ⟨rfl, rfl⟩ := e
    cases h <;> simp [side, consNeed, flattenNeed]
  · cases h
    · simp only [side, Bool.false_eq_true, ↓reduceIte]
      rw [consNeed, if_neg (fun e' => e ⟨e'.2, e'.1⟩), scit_fp, List.count_append]; omega
    · simp only [side, ↓reduceIte]
      rw [consNeed, if_neg e, scit_fp, List.count_append]

theorem scit_roll (y : Nat) : ∀ (tack : List (Bool × Need)) (acc : Need),
    (flattenNeed (tack.foldl (fun acc e => side e.1 acc e.2) acc)).count y =
      (flattenNeed acc).count y + (scitT tack).count y
  | [], acc => by simp [scitT]
  | e :: tack, acc => by
    rw [List.foldl_cons, scit_roll y tack, scit_side]
    simp only [scitT, List.flatMap_cons, List.count_append]
    omega

theorem scit_trOp_cons {a b d : Nat} {ops : List Pole} (htr : ∀ op ∈ ops, trOp op = false) :
    ∀ op ∈ Pole.con a b d :: ops, trOp op = false := fun op hop => by
  rcases List.mem_cons.mp hop with rfl | hop
  · rfl
  · exact htr op hop

theorem scit_defs_cons (a b d : Nat) (ops : List Pole) : defsOf (Pole.con a b d :: ops) = [d] ++ defsOf ops := rfl

/-! ## `+must` and the loop of `+into-need` -/

theorem scit_must (ned : Need) : SCR (Map := Map) (flattenNeed ned) (must ned) (fun x => flattenNeed x.2) := by
  cases ned with
  | none =>
    exact sc_bind (sc_re _) fun r => sc_pure fun y => by simp only [scit_fn, scit_ft, List.nil_append]; exact Nat.le_refl _
  | this r => exact sc_pure fun y => Nat.le_refl _
  | pair p q =>
    exact sc_bind (sc_re _) fun r => sc_pure fun y => by
      simp only [scit_fb, scit_fp, List.count_append]; omega
  | both r h t => exact sc_pure fun y => Nat.le_refl _

/-- **The loop of `+into-need`** with its potential. -/
theorem scit_loop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    (∀ op ∈ ops, trOp op = false) →
    SCR (Map := Map) (flattenNeed ned ++ scitT tack ++ defsOf ops) (intoLoop o axe ned tack ops)
      (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned tack ops htr
  rw [intoLoop]
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1]
    refine sc_bind (sc_addOps (o := o) (A := ops) (ro := flattenNeed ned ++ scitT tack) htr fun y => ?_)
      fun _ => sc_pure fun y => ?_
    · simp only [List.count_append]; omega
    · have e := scit_roll y tack Need.none
      rw [List.count_append, List.count_append, rollTack, e]
      simp [flattenNeed]
  rw [dif_neg h1]
  have lt := mas_lt axe (by omega)
  cases ned with
  | none =>
    refine sc_mono (ih (mas axe) lt Need.none ((decide (cap axe = 2), Need.none) :: tack) ops htr)
      (fun y => ?_) (fun _ _ => Nat.le_refl _)
    simp only [scitT, List.flatMap_cons, scit_fn, List.nil_append, List.count_append]
    exact Nat.le_refl _
  | this r =>
    dsimp only
    refine sc_bind (sc_re _) fun l => sc_bind (sc_re _) fun r' => ?_
    refine sc_mono (ih (mas axe) lt _ _ _ (scit_trOp_cons htr)) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    generalize decide (cap axe = 2) = c
    cases c <;>
      simp only [Bool.false_eq_true, if_true, if_false, scitT, List.flatMap_cons, scit_ft, scit_defs_cons,
        List.count_append] <;> omega
  | pair p q =>
    dsimp only
    refine sc_mono (ih (mas axe) lt _ _ _ htr) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    generalize decide (cap axe = 2) = c
    cases c <;>
      simp only [Bool.false_eq_true, if_true, if_false, scitT, List.flatMap_cons, scit_fp,
        List.count_append] <;> omega
  | both r hh t =>
    dsimp only
    refine sc_bind (r1 := fun l => flattenNeed l.2 ++ ([r] ++ flattenNeed t ++ scitT tack ++ defsOf ops))
      (sc_mono (scit_frame _ (scit_must hh)) (fun y => ?_) (fun _ _ => Nat.le_refl _)) fun l => ?_
    · simp only [scit_fb, List.count_append]; omega
    refine sc_bind (r1 := fun r' => flattenNeed r'.2 ++ (flattenNeed l.2 ++ [r] ++ scitT tack ++ defsOf ops))
      (sc_mono (scit_frame _ (scit_must t)) (fun y => ?_) (fun _ _ => Nat.le_refl _)) fun r' => ?_
    · simp only [List.count_append]; omega
    refine sc_mono (ih (mas axe) lt _ _ _ (scit_trOp_cons htr)) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    generalize decide (cap axe = 2) = c
    cases c <;>
      simp only [Bool.false_eq_true, if_true, if_false, scitT, List.flatMap_cons, scit_defs_cons,
        List.count_append] <;> omega

theorem scit_need (axe : Nat) (ned : Need) (o : Nat) :
    SCR (Map := Map) (flattenNeed ned) (intoNeed axe ned o) (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  unfold intoNeed
  split
  · exact sc_fail
  · split
    · exact sc_pure fun y => by simp [flattenNeed]
    · exact sc_mono (scit_loop o axe ned [] [] (fun op h => absurd h List.not_mem_nil))
        (fun y => by simp [scitT, defsOf]) (fun _ _ => Nat.le_refl _)

theorem scit_sure (axe : Nat) (s : Sure S) (o : Nat) :
    SCR (Map := Map) (flattenNeed s.ned) (intoSure axe s o)
      (fun x => flattenNeed x.1.ned ++ flattenNeed x.2.ned) := by
  intro g x g' st e
  unfold intoSure at e
  obtain ⟨⟨ld, lr⟩, -, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, e1, e2⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact scit_need axe s.ned o g (nd, nr) g2 st e1

/-! ## Pruning -/

theorem scit_regsL_sub {L1 L2 : List (Nat × Lazy S)} (h : L1.Sublist L2) (y : Nat) :
    (regsL L1).count y ≤ (regsL L2).count y := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => rw [regsL_cons, List.count_append]; omega
  | cons_cons a _ ih => rw [regsL_cons, regsL_cons, List.count_append, List.count_append]; omega

theorem scit_prune (l : Lazy S) (y : Nat) : (sarR (lazyPrune l)).count y ≤ (sarR l).count y := by
  unfold sarR
  rw [List.count_append, List.count_append]
  have := scit_regsL_sub (its_pruneSub l) y
  have e : (lazyPrune l).sure = l.sure := rfl
  rw [e]; omega

theorem scit_cons (o : Nat) (l : Lazy S) : regsL ((o, l) :: entries l) = sarR l := by
  rw [regsL_cons]; rfl

theorem scit_sarR_mk (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    sarR (mk s f b) = flattenNeed s.ned ++ (regsL (bondEntries b) ++ regsL (forkEntries f)) := by
  show flattenNeed s.ned ++ regsL (bondEntries b ++ forkEntries f) = _
  rw [regsL_append]

/-! ## The walk -/

mutual
/-- **The count of `intoLoopL`.** -/
theorem scit_loopL (axe : Nat) : ∀ (l : Lazy S) (o : Nat),
    SCR (Map := Map) (sarR l) (intoLoopL axe l o) (fun x => sarR x.1 ++ sarR x.2)
  | mk s f b, o => by
    rw [intoLoopL, scit_sarR_mk]
    refine sc_bind (scit_frame _ (scit_sure axe s o)) fun p => ?_
    obtain ⟨sd, sr⟩ := p
    dsimp only
    refine sc_ite _ ?_ ?_
    · exact sc_pure fun y => by simp only [sarR_ofSure, List.count_append]; omega
    · refine sc_bind (r1 := fun q => regsL (forkEntries q.1) ++ regsL (forkEntries q.2) ++
          (flattenNeed sd.ned ++ flattenNeed sr.ned ++ regsL (bondEntries b)))
        (sc_mono (scit_frame _ (scit_forks axe f)) (fun y => by simp only [List.count_append]; omega)
          (fun _ _ => Nat.le_refl _)) fun q => ?_
      obtain ⟨fd, fr'⟩ := q
      dsimp only
      refine sc_bind (r1 := fun q => regsL (bondEntries q.1) ++ regsL (bondEntries q.2) ++
          (flattenNeed sd.ned ++ flattenNeed sr.ned ++ regsL (forkEntries fd) ++ regsL (forkEntries fr')))
        (sc_mono (scit_frame _ (scit_bonds axe b)) (fun y => by simp only [List.count_append]; omega)
          (fun _ _ => Nat.le_refl _)) fun q => ?_
      obtain ⟨bd, br⟩ := q
      dsimp only
      refine sc_pure fun y => ?_
      have p1 := scit_prune (mk sd fd bd) y
      have p2 := scit_prune (mk sr fr' br) y
      rw [scit_sarR_mk] at p1 p2
      simp only [List.count_append] at p1 p2 ⊢
      omega

/-- Its count over the forks. -/
theorem scit_forks (axe : Nat) : ∀ (f : List (ForkE S)),
    SCR (Map := Map) (regsL (forkEntries f)) (intoForks axe f)
      (fun q => regsL (forkEntries q.1) ++ regsL (forkEntries q.2))
  | [] => by
    rw [intoForks]
    exact sc_pure fun z => by simp [forkEntries, regsL]
  | ((oy, y), (on, n)) :: rest => by
    rw [intoForks]
    have hE : regsL (forkEntries (((oy, y), (on, n)) :: rest)) =
        sarR y ++ sarR n ++ regsL (forkEntries rest) := by
      simp only [forkEntries, regsL_append, scit_cons]
    rw [hE]
    refine sc_bind (r1 := fun p => sarR p.1 ++ sarR p.2 ++ (sarR n ++ regsL (forkEntries rest)))
      (sc_mono (scit_frame _ (scit_loopL axe y oy)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨yd, yr⟩ := p
    dsimp only
    refine sc_bind (r1 := fun p => sarR p.1 ++ sarR p.2 ++ (sarR yd ++ sarR yr ++ regsL (forkEntries rest)))
      (sc_mono (scit_frame _ (scit_loopL axe n on)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨nd, nr⟩ := p
    dsimp only
    refine sc_bind (r1 := fun p => regsL (forkEntries p.1) ++ regsL (forkEntries p.2) ++
        (sarR yd ++ sarR yr ++ sarR nd ++ sarR nr))
      (sc_mono (scit_frame _ (scit_forks axe rest)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨rd, rr⟩ := p
    dsimp only
    refine sc_pure fun z => ?_
    simp only [forkEntries, regsL_append, scit_cons, List.count_append]
    omega

/-- Its count over the bonds. -/
theorem scit_bonds (axe : Nat) : ∀ (b : List (Nat × Lazy S)),
    SCR (Map := Map) (regsL (bondEntries b)) (intoBonds axe b)
      (fun q => regsL (bondEntries q.1) ++ regsL (bondEntries q.2))
  | [] => by
    rw [intoBonds]
    exact sc_pure fun z => by simp [bondEntries, regsL]
  | (o, l) :: rest => by
    rw [intoBonds]
    have hE : regsL (bondEntries ((o, l) :: rest)) = sarR l ++ regsL (bondEntries rest) := by
      simp only [bondEntries, regsL_append, scit_cons]
    rw [hE]
    refine sc_bind (r1 := fun p => sarR p.1 ++ sarR p.2 ++ regsL (bondEntries rest))
      (scit_frame _ (scit_loopL axe l o)) fun p => ?_
    obtain ⟨ld, lr⟩ := p
    dsimp only
    refine sc_bind (r1 := fun p => regsL (bondEntries p.1) ++ regsL (bondEntries p.2) ++ (sarR ld ++ sarR lr))
      (sc_mono (scit_frame _ (scit_bonds axe rest)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨rd, rr⟩ := p
    dsimp only
    refine sc_pure fun z => ?_
    simp only [bondEntries, regsL_append, scit_cons, List.count_append]
    omega
end

/-- **The field `into` of `SarStepsW`.** -/
theorem scit_into : ∀ (nex : NextL S) (axe : Nat), nex.th.args = [] →
    SCR (Map := Map) (sarR nex.laz) (intoL nex axe) (fun x => sarR x.1 ++ sarR x.2.1) := by
  intro nex axe ha
  unfold intoL
  refine sc_bind (r1 := fun _ => sarR nex.laz)
    (sc_emit (fun op h => absurd h List.not_mem_nil) (fun j hj a hm => ?_) (fun z => ?_)) fun o => ?_
  · simp only [getJmps, List.mem_singleton] at hj
    subst hj
    rw [ha] at hm
    exact absurd hm List.not_mem_nil
  · simp [blockDefs]
  · refine sc_bind (r1 := fun p => sarR p.1 ++ sarR p.2) (scit_loopL axe nex.laz o) fun p => ?_
    obtain ⟨d, r⟩ := p
    exact sc_pure fun z => Nat.le_refl _

end Raw
end SkaModel
end Formalization
