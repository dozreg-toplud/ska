import lemmas.Ska.RawInvCLSARunBase

/-!
# Single assignment with calls: the count of `+split`

README Gaps 14 (b), track D.  The field `split` of `SarStepsW`
(`RawInvCLSARun.lean`): `+split` meets the definition count `SCR` from the
registers of the goal's tree to those of the two halves.  Per entry,
`+split-need` either hands the halves of a `pair` on, or defines the entry's
register `r` once by `con h t r` (the register leaves the tree) from fresh
registers or from the registers of `must` (which allocates one fresh
register for a `pair` or a `none`); `+lazy-prune` drops entries, so the
halves' registers only lose copies (`sps_prune`).

* `scsp_fr` (a count with a frame list), `scsp_must`, `scsp_need`
  (`+split-need`, all four cases), `scsp_sure` (`+split-sure`).
* `scsp_sarR_mk`, `scsp_fe_cons`, `scsp_be_cons`, `scsp_prune`.
* **`scspLoop`** (mutual with `scspForks`, `scspBonds`): the count of
  `split-loop` over the whole tree.
* **`scsp_split`**: the field `split` of `SarStepsW`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-- A count with a frame list `X` on both sides. -/
theorem scsp_fr {α : Type} {ri : List Nat} {m : CM Map α} {ro : α → List Nat} (h : SCR (Map := Map) ri m ro)
    (X : List Nat) {ri' : List Nat} {ro' : α → List Nat} (hi : ∀ y, ri.count y + X.count y ≤ ri'.count y)
    (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y + X.count y) : SCR (Map := Map) ri' m ro' := by
  intro g x g' s e
  obtain ⟨s1, l1, c1⟩ := h g x g' s e
  exact ⟨s1, l1, fun y => by have := c1 y; have := hi y; have := ho x y; omega⟩

/-- **`+must`**: the need's registers, and one fresh register for a `pair` or a `none`. -/
theorem scsp_must (ned : Need) : SCR (Map := Map) (flattenNeed ned) (must ned) (fun x => flattenNeed x.2) := by
  cases ned with
  | both r h t => exact sc_pure fun _ => Nat.le_refl _
  | this r => exact sc_pure fun _ => Nat.le_refl _
  | pair p q =>
    simp only [must]
    refine sc_bind (sc_re _) fun r => sc_pure fun y => ?_
    have e : flattenNeed (Need.both r p q) = r :: (flattenNeed (Need.pair p q)) := rfl
    rw [e]
    exact Nat.le_of_eq ((List.perm_append_singleton r _).count_eq y).symm
  | none =>
    simp only [must]
    refine sc_bind (sc_re _) fun r => sc_pure fun y => ?_
    simp [flattenNeed]

/-- **`+split-need`**: `con h t r` defines the entry's register `r` once. -/
theorem scsp_need (ned : Need) (o : Nat) :
    SCR (Map := Map) (flattenNeed ned) (splitNeed ned o) (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  cases ned with
  | pair p q => exact sc_pure fun _ => Nat.le_refl _
  | none => exact sc_pure fun _ => by simp [flattenNeed]
  | this r =>
    simp only [splitNeed]
    refine sc_bind (sc_re _) fun h => sc_bind (sc_re _) fun t => ?_
    refine sc_bind (sc_addOps (ro := [h] ++ [t]) (by simp [trOp])
      (cnt_app_le (by simp [defsOf, aliasDst, flattenNeed]))) fun _ => sc_pure fun y => ?_
    simp [flattenNeed]
  | both r h t =>
    have e : flattenNeed (Need.both r h t) = [r] ++ (flattenNeed h ++ flattenNeed t) := rfl
    simp only [splitNeed]
    rw [e]
    refine sc_bind (scsp_fr (scsp_must h) ([r] ++ flattenNeed t)
      (ro' := fun x => [r] ++ (flattenNeed x.2 ++ flattenNeed t))
      (fun y => by simp only [List.count_append]; omega) (fun x y => by simp only [List.count_append]; omega))
      fun hed => ?_
    refine sc_bind (scsp_fr (scsp_must t) ([r] ++ flattenNeed hed.2)
      (ro' := fun x => [r] ++ (flattenNeed hed.2 ++ flattenNeed x.2))
      (fun y => by simp only [List.count_append]; omega) (fun x y => by simp only [List.count_append]; omega))
      fun tel => ?_
    exact sc_bind (sc_addOps (ro := flattenNeed hed.2 ++ flattenNeed tel.2) (by simp [trOp])
      (cnt_app_le (by simp [defsOf, aliasDst]))) fun _ => sc_pure fun y => Nat.le_refl _

/-- **`+split-sure`**: the count of `+split-need`. -/
theorem scsp_sure (sur : Sure S) (o : Nat) :
    SCR (Map := Map) (flattenNeed sur.ned) (splitSure sur o) (fun x => flattenNeed x.1.ned ++ flattenNeed x.2.ned) := by
  intro g x g' s e
  unfold splitSure at e
  obtain ⟨⟨lh, lt⟩, -, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨⟨nh, nt⟩, g1⟩, e1, e2⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact scsp_need sur.ned o g _ g1 s e1

/-! ## The registers of a tree, unfolded -/

theorem scsp_sarR_mk (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    sarR (mk s f b) = flattenNeed s.ned ++ (regsL (bondEntries b) ++ regsL (forkEntries f)) := by
  simp only [sarR, sure_mk, entries, regsL_append]

theorem scsp_fe_cons (oy on : Nat) (y n : Lazy S) (rest : List (ForkE S)) :
    regsL (forkEntries (((oy, y), (on, n)) :: rest)) = sarR y ++ sarR n ++ regsL (forkEntries rest) := by
  show regsL (((oy, y) :: entries y) ++ ((on, n) :: entries n) ++ forkEntries rest) = _
  simp only [regsL_append, regsL_cons, sarR]

theorem scsp_be_cons (o : Nat) (l : Lazy S) (rest : List (Nat × Lazy S)) :
    regsL (bondEntries ((o, l) :: rest)) = sarR l ++ regsL (bondEntries rest) := by
  show regsL (((o, l) :: entries l) ++ bondEntries rest) = _
  simp only [regsL_append, regsL_cons, sarR]

/-- **A pruned tree** has at most the registers of its parts. -/
theorem scsp_prune (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) (y : Nat) :
    (sarR (lazyPrune (mk s f b))).count y ≤
      (flattenNeed s.ned ++ (regsL (bondEntries b) ++ regsL (forkEntries f))).count y := by
  have h := (sps_prune 0 s f b).2.2 y
  have e : regsL ((0, lazyPrune (mk s f b)) :: entries (lazyPrune (mk s f b))) = sarR (lazyPrune (mk s f b)) := by
    rw [regsL_cons]; rfl
  rw [e] at h
  simp only [regsL_append, regsL_cons, regsL_nil, sure_mk, List.append_nil, List.count_append] at h ⊢
  omega

/-! ## The walk -/

mutual
/-- **The count of `split-loop`.** -/
theorem scspLoop : ∀ (l : Lazy S) (o : Nat),
    SCR (Map := Map) (sarR l) (splitLoop l o) (fun x => sarR x.1 ++ sarR x.2)
  | mk s f b, o => by
    rw [splitLoop, scsp_sarR_mk]
    refine sc_bind (scsp_fr (scsp_sure s o) (regsL (bondEntries b) ++ regsL (forkEntries f))
      (ro' := fun p => flattenNeed p.1.ned ++ flattenNeed p.2.ned ++ (regsL (bondEntries b) ++ regsL (forkEntries f)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨sh, st⟩ := p
    refine sc_ite _ (sc_pure fun z => ?_) ?_
    · simp only [sarR_ofSure, List.count_append]; omega
    · refine sc_bind (scsp_fr (scspForks f) (flattenNeed sh.ned ++ flattenNeed st.ned ++ regsL (bondEntries b))
        (ro' := fun p => flattenNeed sh.ned ++ flattenNeed st.ned ++ regsL (bondEntries b) ++
          (regsL (forkEntries p.1) ++ regsL (forkEntries p.2)))
        (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
        fun p => ?_
      obtain ⟨fh, ft⟩ := p
      refine sc_bind (scsp_fr (scspBonds b)
        (flattenNeed sh.ned ++ flattenNeed st.ned ++ (regsL (forkEntries fh) ++ regsL (forkEntries ft)))
        (ro' := fun p => flattenNeed sh.ned ++ flattenNeed st.ned ++
          (regsL (bondEntries p.1) ++ regsL (bondEntries p.2)) ++ (regsL (forkEntries fh) ++ regsL (forkEntries ft)))
        (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
        fun p => ?_
      obtain ⟨bh, bt⟩ := p
      refine sc_pure fun z => ?_
      have h1 := scsp_prune sh fh bh z
      have h2 := scsp_prune st ft bt z
      simp only [List.count_append] at h1 h2 ⊢
      omega

/-- Its count over the forks. -/
theorem scspForks : ∀ (f : List (ForkE S)),
    SCR (Map := Map) (regsL (forkEntries f)) (splitForks f)
      (fun x => regsL (forkEntries x.1) ++ regsL (forkEntries x.2))
  | [] => by
    rw [splitForks]
    exact sc_pure fun z => by simp [forkEntries, regsL_nil]
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks, scsp_fe_cons]
    refine sc_bind (scsp_fr (scspLoop y oy) (sarR n ++ regsL (forkEntries rest))
      (ro' := fun p => sarR p.1 ++ sarR p.2 ++ (sarR n ++ regsL (forkEntries rest)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨yh, yt⟩ := p
    refine sc_bind (scsp_fr (scspLoop n on) (sarR yh ++ sarR yt ++ regsL (forkEntries rest))
      (ro' := fun p => sarR yh ++ sarR yt ++ (sarR p.1 ++ sarR p.2) ++ regsL (forkEntries rest))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨nh, nt⟩ := p
    refine sc_bind (scsp_fr (scspForks rest) (sarR yh ++ sarR yt ++ (sarR nh ++ sarR nt))
      (ro' := fun p => sarR yh ++ sarR yt ++ (sarR nh ++ sarR nt) ++
        (regsL (forkEntries p.1) ++ regsL (forkEntries p.2)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨rh, rt⟩ := p
    refine sc_pure fun z => ?_
    rw [scsp_fe_cons, scsp_fe_cons]
    simp only [List.count_append]
    omega

/-- Its count over the bonds. -/
theorem scspBonds : ∀ (b : List (Nat × Lazy S)),
    SCR (Map := Map) (regsL (bondEntries b)) (splitBonds b)
      (fun x => regsL (bondEntries x.1) ++ regsL (bondEntries x.2))
  | [] => by
    rw [splitBonds]
    exact sc_pure fun z => by simp [bondEntries, regsL_nil]
  | (o, l) :: rest => by
    rw [splitBonds, scsp_be_cons]
    refine sc_bind (scsp_fr (scspLoop l o) (regsL (bondEntries rest))
      (ro' := fun p => sarR p.1 ++ sarR p.2 ++ regsL (bondEntries rest))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨lh, lt⟩ := p
    refine sc_bind (scsp_fr (scspBonds rest) (sarR lh ++ sarR lt)
      (ro' := fun p => sarR lh ++ sarR lt ++ (regsL (bondEntries p.1) ++ regsL (bondEntries p.2)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨rh, rt⟩ := p
    refine sc_pure fun z => ?_
    rw [scsp_be_cons, scsp_be_cons]
    simp only [List.count_append]
    omega
end

/-- **The field `split` of `SarStepsW`.** -/
theorem scsp_split : ∀ (nex : NextL S), nex.th.args = [] →
    SCR (Map := Map) (sarR nex.laz) (splitL nex) (fun x => sarR x.1 ++ sarR x.2.1) := by
  intro nex ha
  unfold splitL
  refine sc_bind (sc_emit (ro := sarR nex.laz) (by simp) (by simp [getJmps, ha]) (fun y => by simp [blockDefs]))
    fun o => ?_
  refine sc_bind (scspLoop nex.laz o) fun p => ?_
  obtain ⟨h, t⟩ := p
  exact sc_pure fun y => Nat.le_refl _

end Raw
end SkaModel
end Formalization
