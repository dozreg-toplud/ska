import lemmas.Ska.RawInvCLSARunBase

/-!
# Single assignment with calls: counts of the walks

README Gaps 14 (b), track D.  Fields of `SarSteps` and the pieces the others
rest on.

* `sar_fromPath`, `sar_fromSure`, `sar_fromEnt`, **`sar_fromL`** (`+from`
  keeps the registers of a tree, as a list): the field `fromL`.
* **`sc_walkLazy`** (mutual with `sc_walkForks`, `sc_walkBonds`): a walk
  whose gate, at each entry, counts its definitions against the entry's sure
  need consumes the whole tree.  `+mede`, `+collapse-lazy-atom` and `+kern`
  are such walks; their gates' counts are left (`sureRequireLook` allocates
  the halves of a looked-at register, `medeLoop`, `crashNeed`,
  `collapseGate`, `kernNeed`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-! ## `+from` -/

theorem sar_fromPath (ned : Need) : ∀ axe, flattenNeed (fromPath ned axe) = flattenNeed ned := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    rw [fromPath]
    split
    · rfl
    · split
      · simp only [flattenNeed, List.append_nil]; exact ih _ (mas_lt axe (by omega))
      · simp only [flattenNeed, List.nil_append]; exact ih _ (mas_lt axe (by omega))

theorem sar_fromSure {axe : Nat} {s s' : Sure S} (h : fromSure axe s = some s') :
    flattenNeed s'.ned = flattenNeed s.ned := by
  unfold fromSure at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        rename_i hn _
        simp [hn, flattenNeed]
    · cases h
      exact sar_fromPath _ _

theorem sar_fromEnt {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) : regsL b = regsL a := by
  induction h with
  | nil => rfl
  | cons hl _ ih =>
    rw [regsL_cons, regsL_cons, ih, sar_fromSure (fromL_sure hl)]

/-- **`+from` keeps the registers of a tree.** -/
theorem sar_fromL {axe : Nat} {l l' : Lazy S} (h : fromL axe l = some l') : sarR l' = sarR l := by
  unfold sarR
  rw [sar_fromSure (fromL_sure h), sar_fromEnt (fromL_ent axe l l' h)]

theorem sar_fromL_field (ax : Nat) (l l' : Lazy S) (h : fromL ax l = some l') (y : Nat) :
    (sarR l').count y ≤ (sarR l).count y := by
  rw [sar_fromL h]; exact Nat.le_refl _

/-! ## Walks -/

theorem sarR_mk (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    sarR (mk s f b) = flattenNeed s.ned ++ (regsL (bondEntries b) ++ regsL (forkEntries f)) := by
  simp [sarR, entries, regsL_append]

theorem regsL_bond_cons (o : Nat) (l : Lazy S) (rest : List (Nat × Lazy S)) :
    regsL (bondEntries ((o, l) :: rest)) = sarR l ++ regsL (bondEntries rest) := by
  simp [bondEntries, sarR, regsL_append, regsL_cons]

theorem regsL_fork_cons (oy on : Nat) (y n : Lazy S) (rest : List (ForkE S)) :
    regsL (forkEntries (((oy, y), (on, n)) :: rest)) = sarR y ++ sarR n ++ regsL (forkEntries rest) := by
  simp [forkEntries, sarR, regsL_append, regsL_cons]

section Walk

theorem sc_frame {α : Type} {ri : List Nat} {m : CM Map α} {ro : α → List Nat} (h : SCR (Map := Map) ri m ro)
    (L : List Nat) : SCR (Map := Map) (ri ++ L) m (fun x => ro x ++ L) := by
  intro g x g' hs e
  obtain ⟨s1, l1, c1⟩ := h g x g' hs e
  exact ⟨s1, l1, fun y => by have := c1 y; simp only [List.count_append]; omega⟩

variable {f : Nat → Sure S → CM Map Unit}

mutual
/-- **A walk consumes the tree** when each gate consumes its entry's need. -/
theorem sc_walkLazy (hf : ∀ o s, SCR (Map := Map) (flattenNeed s.ned) (f o s) (fun _ => [])) :
    ∀ (o : Nat) (l : Lazy S), SCR (Map := Map) (sarR l) (walkLazy f o l) (fun _ => [])
  | o, mk s fk bd => by
    rw [walkLazy, sarR_mk]
    refine sc_bind (sc_frame (hf o s) (regsL (bondEntries bd) ++ regsL (forkEntries fk))) fun _ => ?_
    refine sc_ite _ (sc_pure fun y => by simp) ?_
    refine sc_bind (sc_mono (sc_walkForks hf fk (L := regsL (bondEntries bd)))
      (ri' := [] ++ (regsL (bondEntries bd) ++ regsL (forkEntries fk))) (ro' := fun _ => regsL (bondEntries bd))
      (fun y => by simp only [List.count_append, List.count_nil]; omega) (fun _ _ => Nat.le_refl _))
      fun _ => sc_walkBonds hf bd

theorem sc_walkForks (hf : ∀ o s, SCR (Map := Map) (flattenNeed s.ned) (f o s) (fun _ => [])) :
    ∀ (fk : List (ForkE S)) {L : List Nat},
      SCR (Map := Map) (regsL (forkEntries fk) ++ L) (walkForks f fk) (fun _ => L)
  | [], L => by
    rw [walkForks]
    exact sc_pure fun y => by simp [forkEntries, regsL_nil]
  | ((oy, y), (on, n)) :: rest, L => by
    rw [walkForks]
    refine sc_bind (sc_mono (sc_frame (sc_walkLazy hf oy y) (sarR n ++ (regsL (forkEntries rest) ++ L)))
      (ri' := regsL (forkEntries (((oy, y), (on, n)) :: rest)) ++ L)
      (ro' := fun _ => sarR n ++ (regsL (forkEntries rest) ++ L))
      (fun z => by simp only [regsL_fork_cons, List.count_append]; omega)
      (fun _ z => by simp only [List.count_append, List.count_nil]; omega)) fun _ => ?_
    exact sc_bind (sc_mono (sc_frame (sc_walkLazy hf on n) (regsL (forkEntries rest) ++ L))
      (ri' := sarR n ++ (regsL (forkEntries rest) ++ L)) (ro' := fun _ => regsL (forkEntries rest) ++ L)
      (fun z => Nat.le_refl _) (fun _ z => by simp only [List.count_append, List.count_nil]; omega))
      fun _ => sc_walkForks hf rest

theorem sc_walkBonds (hf : ∀ o s, SCR (Map := Map) (flattenNeed s.ned) (f o s) (fun _ => [])) :
    ∀ (bd : List (Nat × Lazy S)), SCR (Map := Map) (regsL (bondEntries bd)) (walkBonds f bd) (fun _ => [])
  | [] => by
    rw [walkBonds]
    exact sc_pure fun y => by simp
  | (o, l) :: rest => by
    rw [walkBonds]
    exact sc_bind (sc_mono (sc_frame (sc_walkLazy hf o l) (regsL (bondEntries rest)))
      (ri' := regsL (bondEntries ((o, l) :: rest))) (ro' := fun _ => regsL (bondEntries rest))
      (fun z => by simp only [regsL_bond_cons, List.count_append]; omega)
      (fun _ z => by simp only [List.count_append, List.count_nil]; omega)) fun _ => sc_walkBonds hf rest
end

end Walk

/-! ## `+mede` -/

theorem sc_get (ri : List Nat) : SCR (Map := Map) ri (get : CM Map (Comp.Gen Map)) (fun _ => ri) := by
  intro g x g' hs e
  rw [get_apply] at e
  cases e
  exact ⟨hs, Nat.le_refl _, fun y => by simp [fr]⟩

theorem sar_consNeed (a b : Need) : flattenNeed (consNeed a b) = flattenNeed a ++ flattenNeed b := by
  unfold consNeed
  split
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

theorem sar_split3 (ned : Need) :
    flattenNeed ned = (split3 ned).1.toList ++ (flattenNeed (split3 ned).2.1 ++ flattenNeed (split3 ned).2.2) := by
  cases ned <;> simp [split3, flattenNeed]

theorem sar_wrapN (o : Option Nat) (x : Need) (y : Nat) :
    (flattenNeed (wrapN o x)).count y ≤ (o.toList ++ flattenNeed x).count y := by
  cases o with
  | none => simp [wrapN]
  | some r =>
    cases x with
    | none => simp [wrapN, flattenNeed]
    | this a => simp [wrapN, flattenNeed, List.count_cons]
    | pair p q => simp [wrapN, flattenNeed, List.count_cons, List.count_append]
    | both a h t => simp [wrapN, flattenNeed, List.count_cons, List.count_append]

theorem sc_lookPath : ∀ (axe : Nat) (ned : Need),
    SCR (Map := Map) (flattenNeed ned) (lookPath ned axe) (fun n => flattenNeed n) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · cases ned with
      | none => exact sc_bind (sc_re _) fun r => sc_pure fun y => by simp [flattenNeed]
      | this r => exact sc_pure fun y => Nat.le_refl _
      | pair p q => exact sc_pure fun y => Nat.le_refl _
      | both r h t => exact sc_pure fun y => Nat.le_refl _
    · split
      · refine sc_bind (sc_mono (sc_frame (ih _ (mas_lt axe (by omega)) (split3 ned).2.1)
          ((split3 ned).1.toList ++ flattenNeed (split3 ned).2.2)) (ri' := flattenNeed ned)
          (ro' := fun x => flattenNeed x ++ ((split3 ned).1.toList ++ flattenNeed (split3 ned).2.2))
          (fun y => by rw [sar_split3 ned]; simp only [List.count_append]; omega) (fun _ _ => Nat.le_refl _))
          fun x => sc_pure fun y => ?_
        have := sar_wrapN (split3 ned).1 (consNeed x (split3 ned).2.2) y
        rw [sar_consNeed] at this
        simp only [List.count_append] at this ⊢
        omega
      · refine sc_bind (sc_mono (sc_frame (ih _ (mas_lt axe (by omega)) (split3 ned).2.2)
          ((split3 ned).1.toList ++ flattenNeed (split3 ned).2.1)) (ri' := flattenNeed ned)
          (ro' := fun x => flattenNeed x ++ ((split3 ned).1.toList ++ flattenNeed (split3 ned).2.1))
          (fun y => by rw [sar_split3 ned]; simp only [List.count_append]; omega) (fun _ _ => Nat.le_refl _))
          fun x => sc_pure fun y => ?_
        have := sar_wrapN (split3 ned).1 (consNeed (split3 ned).2.1 x) y
        rw [sar_consNeed] at this
        simp only [List.count_append] at this ⊢
        omega

theorem sc_lookFold : ∀ (L : List Nat) (acc : CM Map Need) (ri : List Nat),
    SCR (Map := Map) ri acc (fun n => flattenNeed n) →
    SCR (Map := Map) ri (L.foldl (fun acc axe => do
      let ned ← acc
      if axe = 1 then pure ned else
      if axe = 0 then fun _ => Option.none else
      lookPath ned axe) acc) (fun n => flattenNeed n)
  | [], _, _, h => h
  | a :: L, acc, ri, h => sc_lookFold L _ ri (sc_bind h fun ned =>
      sc_ite _ (sc_pure fun _ => Nat.le_refl _) (sc_ite _ sc_fail (sc_lookPath a ned)))

theorem sc_sureRequireLook (s : Sure S) :
    SCR (Map := Map) (flattenNeed s.ned) (sureRequireLook s) (fun n => flattenNeed n) := by
  unfold sureRequireLook
  exact sc_lookFold _ _ _ (sc_pure fun _ => Nat.le_refl _)

theorem sar_fm_imm (v : Noun) (l : List Nat) : (l.map fun x => Pole.imm v x).filterMap aliasDst = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih

theorem sc_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) :
    SCR (Map := Map) (flattenNeed ned) (crashNeed o atom ned) (fun _ => []) := by
  cases atom with
  | inr p =>
    simp only [crashNeed]
    refine sc_addOps (fun op hop => by
      simp only [List.mem_cons, List.mem_map] at hop
      rcases hop with rfl | ⟨x, -, rfl⟩ <;> rfl) fun y => ?_
    have e : defsOf (Pole.cel p :: ((flattenNeed ned).filter (· != p)).map fun x => Pole.imm (A 0) x) =
        (flattenNeed ned).filter (· != p) := sar_fm_imm _ _
    rw [e]
    simpa using (List.filter_sublist (p := (· != p)) (l := flattenNeed ned)).count_le y
  | inl n =>
    simp only [crashNeed]
    refine sc_bind (sc_re _) fun r => sc_addOps (fun op hop => by
      simp only [List.mem_cons, List.mem_map] at hop
      rcases hop with rfl | rfl | ⟨x, -, rfl⟩ <;> rfl) fun y => ?_
    have e : defsOf (Pole.imm (A n) r :: Pole.cel r :: (flattenNeed ned).map fun x => Pole.imm (A 0) x) =
        r :: flattenNeed ned := congrArg (List.cons r) (sar_fm_imm _ _)
    rw [e]
    simp only [List.count_cons, List.count_append, List.count_nil, List.count_singleton]
    omega

theorem sc_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need),
    SCR (Map := Map) (flattenNeed ned) (medeLoop o som ned) (fun _ => [])
  | _, Need.none => by rw [medeLoop]; exact sc_pure fun _ => by simp
  | som, Need.this r => by
    rw [medeLoop]; exact sc_addOps (by simp [trOp]) fun y => by simp [defsOf, aliasDst, flattenNeed]
  | Noun.atom n, Need.pair p q => by rw [medeLoop]; exact sc_crashNeed o _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]
    exact sc_bind (sc_mono (sc_frame (sc_medeLoop o a p) (flattenNeed q)) (ri' := flattenNeed (Need.pair p q))
      (ro' := fun _ => flattenNeed q) (fun _ => Nat.le_refl _) (fun _ _ => by simp)) fun _ => sc_medeLoop o b q
  | Noun.atom n, Need.both r h t => by rw [medeLoop]; exact sc_crashNeed o _ _
  | Noun.cell a b, Need.both r h t => by
    rw [medeLoop]
    refine sc_bind (sc_addOps (ro := flattenNeed h ++ flattenNeed t) (by simp [trOp])
      fun y => by simp only [defsOf, List.filterMap_cons, List.filterMap_nil, aliasDst, flattenNeed, List.count_cons,
        List.count_append, List.count_nil]; omega) fun _ => ?_
    exact sc_bind (sc_mono (sc_frame (sc_medeLoop o a h) (flattenNeed t)) (ri' := flattenNeed h ++ flattenNeed t)
      (ro' := fun _ => flattenNeed t) (fun _ => Nat.le_refl _) (fun _ _ => by simp)) fun _ => sc_medeLoop o b t

/-- **The field `mede`.** -/
theorem sar_mede (th : Jmp) (k : Noun) (laz : Lazy S) (ha : th.args = []) :
    SCR (Map := Map) (sarR laz) (medeL th k laz) (fun _ => []) := by
  unfold medeL
  refine sc_bind (sc_emit (ro := sarR laz) (by simp) (by simp [getJmps, ha]) fun y => by simp [blockDefs])
    fun o => ?_
  refine sc_bind (sc_get _) fun g => ?_
  refine sc_ite _ (sc_pure fun _ => by simp) ?_
  exact sc_bind (sc_walkLazy (fun o s => sc_bind (sc_sureRequireLook s) fun ned => sc_medeLoop o k ned) o laz)
    fun _ => sc_pure fun _ => Nat.le_refl _

end Raw
end SkaModel
end Formalization
