import lemmas.Ska.RawInvCLKUBase
import lemmas.Ska.RawInvCLSACountSplit
import lemmas.Ska.RawInvCLSACountInto
import lemmas.Ska.RawInvCLPair

/-!
# The state-free count of `+split` and `+into`, and steps that grow `re` and `bo`

README Gaps 14 (b), track D.  The fields `split`, `into`, `mede`, `forl`,
`doneBlocks` of `KUSteps` (`RawInvCLKUBase.lean`): the proofs of
`RawInvCLSACountSplit.lean` and `RawInvCLSACountInto.lean` with the count
`KUC` (no state, no definitions) in place of `SCR`.

* `kus_fr`, `kus_frame` (a count with a frame list), `kus_must`, `kus_need`
  (`+split-need`), `kus_sure` (`+split-sure`).
* **`kusLoop`** (mutual with `kusForks`, `kusBonds`), **`kus_split`**.
* `kus_loop` (the loop of `+into-need`, the potential: the need and the
  registers on the tack), `kus_intoNeed`, `kus_intoSure`.
* **`kus_loopL`** (mutual with `kus_forks`, `kus_bonds`), **`kus_into`**.
* `RB`: `kus_crashNeed`, `kus_medeLoop`, `kus_sureRequireLook`,
  `kus_walkLazy` (by `walkLazy_inv`), **`kus_mede`**, **`kus_forl`**,
  **`kus_doneBlocks`**.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Frames -/

/-- A count with a frame list `X` on both sides. -/
theorem kus_fr {α : Type} {ri : List Nat} {m : CM Map α} {ro : α → List Nat} (h : KUC (Map := Map) ri m ro)
    (X : List Nat) {ri' : List Nat} {ro' : α → List Nat} (hi : ∀ y, ri.count y + X.count y ≤ ri'.count y)
    (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y + X.count y) : KUC (Map := Map) ri' m ro' := by
  intro g x g' e
  obtain ⟨l1, b1, c1⟩ := h g x g' e
  exact ⟨l1, b1, fun y => by have := c1 y; have := hi y; have := ho x y; omega⟩

theorem kus_frame {α : Type} {ri : List Nat} {m : CM Map α} {ro : α → List Nat} (X : List Nat)
    (h : KUC (Map := Map) ri m ro) : KUC (Map := Map) (ri ++ X) m (fun x => ro x ++ X) := by
  intro g x g' e
  obtain ⟨l1, b1, c1⟩ := h g x g' e
  exact ⟨l1, b1, fun y => by have := c1 y; simp only [List.count_append]; omega⟩

/-! ## `+split` -/

/-- **`+must`**: the need's registers, and one fresh register for a `pair` or a `none`. -/
theorem kus_must (ned : Need) : KUC (Map := Map) (flattenNeed ned) (must ned) (fun x => flattenNeed x.2) := by
  cases ned with
  | both r h t => exact ku_pure fun _ => Nat.le_refl _
  | this r => exact ku_pure fun _ => Nat.le_refl _
  | pair p q =>
    simp only [must]
    refine ku_bind (ku_re _) fun r => ku_pure fun y => ?_
    have e : flattenNeed (Need.both r p q) = r :: (flattenNeed (Need.pair p q)) := rfl
    rw [e]
    exact Nat.le_of_eq ((List.perm_append_singleton r _).count_eq y).symm
  | none =>
    simp only [must]
    refine ku_bind (ku_re _) fun r => ku_pure fun y => ?_
    simp [flattenNeed]

/-- **`+split-need`**: the entry's register leaves the tree, the halves are
its parts or fresh. -/
theorem kus_need (ned : Need) (o : Nat) :
    KUC (Map := Map) (flattenNeed ned) (splitNeed ned o) (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  cases ned with
  | pair p q => exact ku_pure fun _ => Nat.le_refl _
  | none => exact ku_pure fun _ => by simp [flattenNeed]
  | this r =>
    simp only [splitNeed]
    refine ku_bind (ku_re _) fun h => ku_bind (ku_re _) fun t => ?_
    refine ku_bind (ku_addOps _ _ _) fun _ => ku_pure fun y => ?_
    simp only [flattenNeed, List.count_append]; omega
  | both r h t =>
    have e : flattenNeed (Need.both r h t) = [r] ++ (flattenNeed h ++ flattenNeed t) := rfl
    simp only [splitNeed]
    rw [e]
    refine ku_bind (kus_fr (kus_must h) ([r] ++ flattenNeed t)
      (ro' := fun x => [r] ++ (flattenNeed x.2 ++ flattenNeed t))
      (fun y => by simp only [List.count_append]; omega) (fun x y => by simp only [List.count_append]; omega))
      fun hed => ?_
    refine ku_bind (kus_fr (kus_must t) ([r] ++ flattenNeed hed.2)
      (ro' := fun x => [r] ++ (flattenNeed hed.2 ++ flattenNeed x.2))
      (fun y => by simp only [List.count_append]; omega) (fun x y => by simp only [List.count_append]; omega))
      fun tel => ?_
    exact ku_bind (ku_addOps _ _ _) fun _ => ku_pure fun y => by simp only [List.count_append]; omega

/-- **`+split-sure`**: the count of `+split-need`. -/
theorem kus_sure (sur : Sure S) (o : Nat) :
    KUC (Map := Map) (flattenNeed sur.ned) (splitSure sur o) (fun x => flattenNeed x.1.ned ++ flattenNeed x.2.ned) := by
  intro g x g' e
  unfold splitSure at e
  obtain ⟨⟨lh, lt⟩, -, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨⟨nh, nt⟩, g1⟩, e1, e2⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact kus_need sur.ned o g _ g1 e1

mutual
/-- **The count of `split-loop`.** -/
theorem kusLoop : ∀ (l : Lazy S) (o : Nat),
    KUC (Map := Map) (sarR l) (splitLoop l o) (fun x => sarR x.1 ++ sarR x.2)
  | mk s f b, o => by
    rw [splitLoop, scsp_sarR_mk]
    refine ku_bind (kus_fr (kus_sure s o) (regsL (bondEntries b) ++ regsL (forkEntries f))
      (ro' := fun p => flattenNeed p.1.ned ++ flattenNeed p.2.ned ++ (regsL (bondEntries b) ++ regsL (forkEntries f)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨sh, st⟩ := p
    refine ku_ite _ (ku_pure fun z => ?_) ?_
    · simp only [sarR_ofSure, List.count_append]; omega
    · refine ku_bind (kus_fr (kusForks f) (flattenNeed sh.ned ++ flattenNeed st.ned ++ regsL (bondEntries b))
        (ro' := fun p => flattenNeed sh.ned ++ flattenNeed st.ned ++ regsL (bondEntries b) ++
          (regsL (forkEntries p.1) ++ regsL (forkEntries p.2)))
        (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
        fun p => ?_
      obtain ⟨fh, ft⟩ := p
      refine ku_bind (kus_fr (kusBonds b)
        (flattenNeed sh.ned ++ flattenNeed st.ned ++ (regsL (forkEntries fh) ++ regsL (forkEntries ft)))
        (ro' := fun p => flattenNeed sh.ned ++ flattenNeed st.ned ++
          (regsL (bondEntries p.1) ++ regsL (bondEntries p.2)) ++ (regsL (forkEntries fh) ++ regsL (forkEntries ft)))
        (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
        fun p => ?_
      obtain ⟨bh, bt⟩ := p
      refine ku_pure fun z => ?_
      have h1 := scsp_prune sh fh bh z
      have h2 := scsp_prune st ft bt z
      simp only [List.count_append] at h1 h2 ⊢
      omega

/-- Its count over the forks. -/
theorem kusForks : ∀ (f : List (ForkE S)),
    KUC (Map := Map) (regsL (forkEntries f)) (splitForks f)
      (fun x => regsL (forkEntries x.1) ++ regsL (forkEntries x.2))
  | [] => by
    rw [splitForks]
    exact ku_pure fun z => by simp [forkEntries, regsL_nil]
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks, scsp_fe_cons]
    refine ku_bind (kus_fr (kusLoop y oy) (sarR n ++ regsL (forkEntries rest))
      (ro' := fun p => sarR p.1 ++ sarR p.2 ++ (sarR n ++ regsL (forkEntries rest)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨yh, yt⟩ := p
    refine ku_bind (kus_fr (kusLoop n on) (sarR yh ++ sarR yt ++ regsL (forkEntries rest))
      (ro' := fun p => sarR yh ++ sarR yt ++ (sarR p.1 ++ sarR p.2) ++ regsL (forkEntries rest))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨nh, nt⟩ := p
    refine ku_bind (kus_fr (kusForks rest) (sarR yh ++ sarR yt ++ (sarR nh ++ sarR nt))
      (ro' := fun p => sarR yh ++ sarR yt ++ (sarR nh ++ sarR nt) ++
        (regsL (forkEntries p.1) ++ regsL (forkEntries p.2)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨rh, rt⟩ := p
    refine ku_pure fun z => ?_
    rw [scsp_fe_cons, scsp_fe_cons]
    simp only [List.count_append]
    omega

/-- Its count over the bonds. -/
theorem kusBonds : ∀ (b : List (Nat × Lazy S)),
    KUC (Map := Map) (regsL (bondEntries b)) (splitBonds b)
      (fun x => regsL (bondEntries x.1) ++ regsL (bondEntries x.2))
  | [] => by
    rw [splitBonds]
    exact ku_pure fun z => by simp [bondEntries, regsL_nil]
  | (o, l) :: rest => by
    rw [splitBonds, scsp_be_cons]
    refine ku_bind (kus_fr (kusLoop l o) (regsL (bondEntries rest))
      (ro' := fun p => sarR p.1 ++ sarR p.2 ++ regsL (bondEntries rest))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨lh, lt⟩ := p
    refine ku_bind (kus_fr (kusBonds rest) (sarR lh ++ sarR lt)
      (ro' := fun p => sarR lh ++ sarR lt ++ (regsL (bondEntries p.1) ++ regsL (bondEntries p.2)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨rh, rt⟩ := p
    refine ku_pure fun z => ?_
    rw [scsp_be_cons, scsp_be_cons]
    simp only [List.count_append]
    omega
end

/-- **`+split` with no state**: the field `split` of `KUSteps`. -/
theorem kus_split : ∀ (nex : NextL S),
    KUC (Map := Map) (sarR nex.laz) (splitL nex) (fun x => sarR x.1 ++ sarR x.2.1) := by
  intro nex
  unfold splitL
  refine ku_bind (ku_emit (sarR nex.laz) _) fun o => ?_
  refine ku_bind (kusLoop nex.laz o) fun p => ?_
  obtain ⟨h, t⟩ := p
  exact ku_pure fun y => Nat.le_refl _

/-! ## `+into` -/

/-- **The loop of `+into-need`** with the potential "the need and the
registers on the tack". -/
theorem kus_loop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    KUC (Map := Map) (flattenNeed ned ++ scitT tack) (intoLoop o axe ned tack ops)
      (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned tack ops
  rw [intoLoop]
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1]
    refine ku_bind (ku_addOps _ _ _) fun _ => ku_pure fun y => ?_
    have e := scit_roll y tack Need.none
    rw [List.count_append, List.count_append, rollTack, e]
    simp [flattenNeed]
  rw [dif_neg h1]
  have lt := mas_lt axe (by omega)
  cases ned with
  | none =>
    refine ku_mono (ih (mas axe) lt Need.none ((decide (cap axe = 2), Need.none) :: tack) ops)
      (fun y => ?_) (fun _ _ => Nat.le_refl _)
    simp only [scitT, List.flatMap_cons, scit_fn, List.nil_append, List.count_append]
    exact Nat.le_refl _
  | this r =>
    dsimp only
    refine ku_bind (ku_re _) fun l => ku_bind (ku_re _) fun r' => ?_
    refine ku_mono (ih (mas axe) lt _ _ _) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    generalize decide (cap axe = 2) = c
    cases c <;>
      simp only [Bool.false_eq_true, if_true, if_false, scitT, List.flatMap_cons, scit_ft,
        List.count_append] <;> omega
  | pair p q =>
    dsimp only
    refine ku_mono (ih (mas axe) lt _ _ _) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    generalize decide (cap axe = 2) = c
    cases c <;>
      simp only [Bool.false_eq_true, if_true, if_false, scitT, List.flatMap_cons, scit_fp,
        List.count_append] <;> omega
  | both r hh t =>
    dsimp only
    refine ku_bind (r1 := fun l => flattenNeed l.2 ++ ([r] ++ flattenNeed t ++ scitT tack))
      (ku_mono (kus_frame _ (kus_must hh)) (fun y => ?_) (fun _ _ => Nat.le_refl _)) fun l => ?_
    · simp only [scit_fb, List.count_append]; omega
    refine ku_bind (r1 := fun r' => flattenNeed r'.2 ++ (flattenNeed l.2 ++ [r] ++ scitT tack))
      (ku_mono (kus_frame _ (kus_must t)) (fun y => ?_) (fun _ _ => Nat.le_refl _)) fun r' => ?_
    · simp only [List.count_append]; omega
    refine ku_mono (ih (mas axe) lt _ _ _) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    generalize decide (cap axe = 2) = c
    cases c <;>
      simp only [Bool.false_eq_true, if_true, if_false, scitT, List.flatMap_cons,
        List.count_append] <;> omega

theorem kus_intoNeed (axe : Nat) (ned : Need) (o : Nat) :
    KUC (Map := Map) (flattenNeed ned) (intoNeed axe ned o) (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  unfold intoNeed
  split
  · exact ku_fail
  · split
    · exact ku_pure fun y => by simp [flattenNeed]
    · exact ku_mono (kus_loop o axe ned [] []) (fun y => by simp [scitT]) (fun _ _ => Nat.le_refl _)

theorem kus_intoSure (axe : Nat) (s : Sure S) (o : Nat) :
    KUC (Map := Map) (flattenNeed s.ned) (intoSure axe s o)
      (fun x => flattenNeed x.1.ned ++ flattenNeed x.2.ned) := by
  intro g x g' e
  unfold intoSure at e
  obtain ⟨⟨ld, lr⟩, -, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, e1, e2⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact kus_intoNeed axe s.ned o g (nd, nr) g2 e1

mutual
/-- **The count of `intoLoopL`.** -/
theorem kus_loopL (axe : Nat) : ∀ (l : Lazy S) (o : Nat),
    KUC (Map := Map) (sarR l) (intoLoopL axe l o) (fun x => sarR x.1 ++ sarR x.2)
  | mk s f b, o => by
    rw [intoLoopL, scit_sarR_mk]
    refine ku_bind (kus_frame _ (kus_intoSure axe s o)) fun p => ?_
    obtain ⟨sd, sr⟩ := p
    dsimp only
    refine ku_ite _ ?_ ?_
    · exact ku_pure fun y => by simp only [sarR_ofSure, List.count_append]; omega
    · refine ku_bind (r1 := fun q => regsL (forkEntries q.1) ++ regsL (forkEntries q.2) ++
          (flattenNeed sd.ned ++ flattenNeed sr.ned ++ regsL (bondEntries b)))
        (ku_mono (kus_frame _ (kus_forks axe f)) (fun y => by simp only [List.count_append]; omega)
          (fun _ _ => Nat.le_refl _)) fun q => ?_
      obtain ⟨fd, fr'⟩ := q
      dsimp only
      refine ku_bind (r1 := fun q => regsL (bondEntries q.1) ++ regsL (bondEntries q.2) ++
          (flattenNeed sd.ned ++ flattenNeed sr.ned ++ regsL (forkEntries fd) ++ regsL (forkEntries fr')))
        (ku_mono (kus_frame _ (kus_bonds axe b)) (fun y => by simp only [List.count_append]; omega)
          (fun _ _ => Nat.le_refl _)) fun q => ?_
      obtain ⟨bd, br⟩ := q
      dsimp only
      refine ku_pure fun y => ?_
      have p1 := scit_prune (mk sd fd bd) y
      have p2 := scit_prune (mk sr fr' br) y
      rw [scit_sarR_mk] at p1 p2
      simp only [List.count_append] at p1 p2 ⊢
      omega

/-- Its count over the forks. -/
theorem kus_forks (axe : Nat) : ∀ (f : List (ForkE S)),
    KUC (Map := Map) (regsL (forkEntries f)) (intoForks axe f)
      (fun q => regsL (forkEntries q.1) ++ regsL (forkEntries q.2))
  | [] => by
    rw [intoForks]
    exact ku_pure fun z => by simp [forkEntries, regsL]
  | ((oy, y), (on, n)) :: rest => by
    rw [intoForks]
    have hE : regsL (forkEntries (((oy, y), (on, n)) :: rest)) =
        sarR y ++ sarR n ++ regsL (forkEntries rest) := by
      simp only [forkEntries, regsL_append, scit_cons]
    rw [hE]
    refine ku_bind (r1 := fun p => sarR p.1 ++ sarR p.2 ++ (sarR n ++ regsL (forkEntries rest)))
      (ku_mono (kus_frame _ (kus_loopL axe y oy)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨yd, yr⟩ := p
    dsimp only
    refine ku_bind (r1 := fun p => sarR p.1 ++ sarR p.2 ++ (sarR yd ++ sarR yr ++ regsL (forkEntries rest)))
      (ku_mono (kus_frame _ (kus_loopL axe n on)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨nd, nr⟩ := p
    dsimp only
    refine ku_bind (r1 := fun p => regsL (forkEntries p.1) ++ regsL (forkEntries p.2) ++
        (sarR yd ++ sarR yr ++ sarR nd ++ sarR nr))
      (ku_mono (kus_frame _ (kus_forks axe rest)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨rd, rr⟩ := p
    dsimp only
    refine ku_pure fun z => ?_
    simp only [forkEntries, regsL_append, scit_cons, List.count_append]
    omega

/-- Its count over the bonds. -/
theorem kus_bonds (axe : Nat) : ∀ (b : List (Nat × Lazy S)),
    KUC (Map := Map) (regsL (bondEntries b)) (intoBonds axe b)
      (fun q => regsL (bondEntries q.1) ++ regsL (bondEntries q.2))
  | [] => by
    rw [intoBonds]
    exact ku_pure fun z => by simp [bondEntries, regsL]
  | (o, l) :: rest => by
    rw [intoBonds]
    have hE : regsL (bondEntries ((o, l) :: rest)) = sarR l ++ regsL (bondEntries rest) := by
      simp only [bondEntries, regsL_append, scit_cons]
    rw [hE]
    refine ku_bind (r1 := fun p => sarR p.1 ++ sarR p.2 ++ regsL (bondEntries rest))
      (kus_frame _ (kus_loopL axe l o)) fun p => ?_
    obtain ⟨ld, lr⟩ := p
    dsimp only
    refine ku_bind (r1 := fun p => regsL (bondEntries p.1) ++ regsL (bondEntries p.2) ++ (sarR ld ++ sarR lr))
      (ku_mono (kus_frame _ (kus_bonds axe rest)) (fun z => by simp only [List.count_append]; omega)
        (fun _ _ => Nat.le_refl _)) fun p => ?_
    obtain ⟨rd, rr⟩ := p
    dsimp only
    refine ku_pure fun z => ?_
    simp only [bondEntries, regsL_append, scit_cons, List.count_append]
    omega
end

/-- **`+into` with no state**: the field `into` of `KUSteps`. -/
theorem kus_into : ∀ (nex : NextL S) (axe : Nat),
    KUC (Map := Map) (sarR nex.laz) (intoL nex axe) (fun x => sarR x.1 ++ sarR x.2.1) := by
  intro nex axe
  unfold intoL
  refine ku_bind (ku_emit (sarR nex.laz) _) fun o => ?_
  refine ku_bind (r1 := fun p => sarR p.1 ++ sarR p.2) (kus_loopL axe nex.laz o) fun p => ?_
  obtain ⟨d, r⟩ := p
  exact ku_pure fun z => Nat.le_refl _

/-! ## Steps that grow `re` and `bo` -/

theorem kus_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : RB (Map := Map) (crashNeed o atom ned) := by
  cases atom with
  | inr p => simp only [crashNeed]; exact rb_addOps _ _
  | inl n => simp only [crashNeed]; exact rb_bind rb_re fun r => rb_addOps _ _

theorem kus_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), RB (Map := Map) (medeLoop o som ned)
  | _, Need.none => by simp only [medeLoop]; exact rb_pure ()
  | som, Need.this r => by simp only [medeLoop]; exact rb_addOps _ _
  | Noun.atom n, Need.pair p q => by simp only [medeLoop]; exact kus_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    simp only [medeLoop]; exact rb_bind (kus_medeLoop o a p) fun _ => kus_medeLoop o b q
  | Noun.atom n, Need.both r h t => by simp only [medeLoop]; exact kus_crashNeed _ _ _
  | Noun.cell a b, Need.both r h t => by
    simp only [medeLoop]
    exact rb_bind (rb_addOps _ _) fun _ => rb_bind (kus_medeLoop o a h) fun _ => kus_medeLoop o b t

theorem kus_sureRequireLook (sur : Sure S) : RB (Map := Map) (sureRequireLook sur : CM Map Need) := by
  intro g x g' h
  obtain ⟨k, e⟩ := (sureRequireLook_spec h).gen
  have hl := (sureRequireLook_spec h).le
  subst e
  exact ⟨hl, Nat.le_refl _⟩

/-- **A walk whose gate grows `re` and `bo`.** -/
theorem kus_walkLazy {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, RB (Map := Map) (f o s)) (o : Nat) (l : Lazy S) :
    RB (Map := Map) (walkLazy f o l) := by
  intro g x g' h
  cases x
  exact walkLazy_inv (W := fun a => g.re ≤ a.re ∧ g.bo ≤ a.bo)
    (fun e _ a b ha hb => ⟨Nat.le_trans ha.1 (hf _ _ a () b hb).1, Nat.le_trans ha.2 (hf _ _ a () b hb).2⟩)
    ⟨Nat.le_refl _, Nat.le_refl _⟩ h

/-- **`+mede` grows `re` and `bo`**: the field `mede` of `KUSteps`. -/
theorem kus_mede (th : Jmp) (k : Noun) (laz : Lazy S) : RB (Map := Map) (medeL th k laz) := by
  unfold medeL
  refine rb_bind (rb_emit _) fun o => rb_bind rb_get fun g => ?_
  refine rb_ite _ (rb_pure _) ?_
  exact rb_bind (kus_walkLazy (fun o s => rb_bind (kus_sureRequireLook s) fun ned => kus_medeLoop o k ned) o laz)
    fun _ => rb_pure _

/-- **`+forl` grows `re` and `bo`**: the field `forl` of `KUSteps`. -/
theorem kus_forl (r o : Nat) : RB (Map := Map) (forl r o) := by
  unfold forl
  exact rb_bind rb_re fun _ => rb_bind rb_re fun _ => rb_bind (rb_emit _) fun _ =>
    rb_bind (rb_emit _) fun _ => rb_bind (rb_emit _) fun _ => rb_pure _

/-- **The two `%done` blocks grow `re` and `bo`**: the field `doneBlocks` of
`KUSteps`. -/
theorem kus_doneBlocks : RB (Map := Map) (doneBlocks : CM Map (Nat × Nat)) := by
  unfold doneBlocks
  exact rb_bind rb_re fun _ => rb_bind rb_re fun _ => rb_bind (rb_emit _) fun _ =>
    rb_bind (rb_emit _) fun _ => rb_pure _

end Raw
end SkaModel
end Formalization
