import lemmas.Glue.GuardStep

/-!
# `KP` of the arms of `run` (track G, step 1 of `GuardMonoX`)

The arms of `+comp` that `run` (`CompModel.lean`, the first fragment) calls,
each keeping `BlocksOK` (`Glue/GuardStep.lean`): the needs (`+must`,
`+split-need`, `+into-need`, `+copy-need-make-ops`, `+sure-require-look`,
`+crash-need`, `+mede`'s loop), and the arms that emit (`+bomb`,
`+simple-next`, `+split`, `+into`, `+copy`, `+mede`,
`+collapse-lazy-atom`, `+forl`, the blocks of `%done`).  The proofs follow
track D's `QM` proofs of `RawInvCQ.lean` with `KP` for `QM`; the ops of each
`+add-ops` have no split (the table of `GuardStep.lean`), and the jumps of
each emitted block are `jmp0 _`, `[some r0]` or jumps of the arm's input,
which pass no `~` (`JOK`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## The needs -/

theorem kp_must (ned : Need) : KB (must ned : CM Map (Nat × Need)) := by unfold must; kpb

theorem kp_splitNeed (ned : Need) (o : Nat) : KB (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · kpb
  · kpb
  · kpb
  · exact KP.bind' (kp_must _) fun _ _ => KP.bind' (kp_must _) fun _ _ => by kpb

theorem kp_splitSure (sur : Sure S) (o : Nat) : KB (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g1 hb h
  unfold splitSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨((kp_splitNeed sur.ned o).k g y g2 hb h1).1, trivial⟩

theorem kp_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    NoSplit ops → KB (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops hops
    rw [intoLoop]
    split
    · exact KP.bind' (KP.addOps' _ hops) fun _ _ => KP.pure' trivial
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _ hops
      · exact KP.bind' KP.re' fun _ _ => KP.bind' KP.re' fun _ _ => ih _ hl _ _ _ (noSplit_cons rfl hops)
      · exact ih _ hl _ _ _ hops
      · exact KP.bind' (kp_must _) fun _ _ => KP.bind' (kp_must _) fun _ _ => ih _ hl _ _ _ (noSplit_cons rfl hops)

theorem kp_intoNeed (axe : Nat) (ned : Need) (o : Nat) : KB (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KP.ite' _ KP.fail (KP.ite' _ (KP.pure' trivial) (kp_intoLoop _ _ _ _ _ noSplit_nil))

theorem kp_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : KB (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g1 hb h
  unfold intoSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨((kp_intoNeed axe sur.ned o).k g y g2 hb h1).1, trivial⟩

/-- **The ops of `+copy-need-make-ops` have no split** (moves only). -/
theorem kp_copyNeed : ∀ (a b : Need) (ops : List Pole), NoSplit ops →
    KP (fun x : Need × List Pole => NoSplit x.2) (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _, h => by rw [copyNeed]; exact KP.pure' h
  | Need.this _, Need.none, _, h => by rw [copyNeed] <;> first | exact KP.pure' h | nofun
  | Need.pair _ _, Need.none, _, h => by rw [copyNeed] <;> first | exact KP.pure' h | nofun
  | Need.both _ _ _, Need.none, _, h => by rw [copyNeed] <;> first | exact KP.pure' h | nofun
  | Need.this _, Need.this _, _, h => by rw [copyNeed]; exact KP.pure' (noSplit_cons rfl h)
  | Need.this _, Need.both _ _ _, _, h => by rw [copyNeed]; exact KP.pure' (noSplit_cons rfl h)
  | Need.this _, Need.pair _ _, _, h => by
    rw [copyNeed]; exact KP.bind' KP.re' fun _ _ => KP.pure' (noSplit_cons rfl h)
  | Need.both _ _ _, Need.this _, _, h => by rw [copyNeed]; exact KP.pure' (noSplit_cons rfl h)
  | Need.pair _ _, Need.this _, _, h => by
    rw [copyNeed]; exact KP.bind' KP.re' fun _ _ => KP.pure' (noSplit_cons rfl h)
  | Need.both _ hl tl, Need.both _ hr tr, _, h => by
    rw [copyNeed]
    exact KP.bind' (kp_copyNeed hl hr _ (noSplit_cons rfl h)) fun x hx =>
      KP.bind' (kp_copyNeed tl tr _ hx) fun y hy => KP.pure' hy
  | Need.both _ hl tl, Need.pair p q, _, h => by
    rw [copyNeed]
    exact KP.bind' KP.re' fun _ _ => KP.bind' (kp_copyNeed hl p _ (noSplit_cons rfl h)) fun x hx =>
      KP.bind' (kp_copyNeed tl q _ hx) fun y hy => KP.pure' hy
  | Need.pair pl ql, Need.pair pr qr, _, h => by
    rw [copyNeed]
    exact KP.bind' (kp_copyNeed pl pr _ h) fun x hx => KP.bind' (kp_copyNeed ql qr _ hx) fun y hy => KP.pure' hy
  | Need.pair pl ql, Need.both _ h' t, _, h => by
    rw [copyNeed]
    exact KP.bind' (kp_copyNeed pl h' _ h) fun x hx => KP.bind' (kp_copyNeed ql t _ hx) fun y hy => KP.pure' hy

theorem kp_lookPath : ∀ (axe : Nat) (ned : Need), KB (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> kpb
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact KP.bind' (ih _ hl _) fun _ _ => by kpb
      · exact KP.bind' (ih _ hl _) fun _ _ => by kpb

theorem kp_sureRequireLook (sur : Sure S) : KB (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine KP.foldl' _ (fun acc b h => KP.bind' h fun ned _ => ?_) _ _ (KP.pure' trivial)
  exact KP.ite' _ (KP.pure' trivial) (KP.ite' _ KP.fail (kp_lookPath _ _))

theorem noSplit_imms (v : Noun) (l : List Nat) : NoSplit (l.map fun x => Pole.imm v x) := by
  intro p hp; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp; rfl

theorem kp_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : KB (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed
  split
  · exact KP.addOps' _ (noSplit_cons rfl (noSplit_imms _ _))
  · exact KP.bind' KP.re' fun _ _ => KP.addOps' _ (noSplit_cons rfl (noSplit_cons rfl (noSplit_imms _ _)))

theorem kp_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), KB (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; kpb
  | _, Need.this _ => by rw [medeLoop]; kpb
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact kp_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact KP.bind' (kp_medeLoop o a p) fun _ _ => kp_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact kp_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact KP.bind' (KP.addOps' _ (noSplit_cons rfl noSplit_nil)) fun _ _ =>
      KP.bind' (kp_medeLoop o a h) fun _ _ => kp_medeLoop o b t

/-! ## The arms that emit -/

theorem kp_bomb (miss : Option Nat) : KP (fun n : Next S => JOK n.th) (bomb miss : CM Map (Next S)) := by
  unfold bomb; kpb

theorem kp_simpleNext {goal : CGoal S} (hg : GJK goal) :
    KP (fun n : Next S => JOK n.th) (simpleNext goal : CM Map (Next S)) := by
  cases goal with
  | next laz th => exact KP.pure' hg
  | done => unfold simpleNext; kpb
  | pick z o => simp only [GJK] at hg; obtain ⟨hz, ho⟩ := hg; unfold simpleNext; kpb

theorem kp_mede {th : Jmp} (hth : JOK th) (som : Noun) (laz : Sure S) : KB (mede th som laz : CM Map Nat) := by
  unfold mede
  refine KP.bind' (KP.emit' (blockOK_of (by simpa [getJmps] using hth) noSplit_nil)) fun o _ => ?_
  refine KP.bind' KP.get' fun g _ => KP.ite' _ (KP.pure' trivial) ?_
  exact KP.bind' (kp_sureRequireLook _) fun ned _ => KP.bind' (kp_medeLoop _ _ _) fun _ _ => KP.pure' trivial

theorem kp_collapseLazyAtom {nex : Next S} (hth : JOK nex.th) :
    KB (collapseLazyAtom nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtom
  refine KP.ite' _ KP.fail (KP.ite' _ (KP.pure' trivial) ?_)
  refine KP.bind' (kp_sureRequireLook _) fun ned _ => ?_
  refine KP.bind' (m := (match ned with
    | Need.this r => pure (r, nex.th.there)
    | Need.none => do let r ← re; pure (r, nex.th.there)
    | Need.pair _ _ => do
        let r ← re
        let o ← emit ⟨[], [], Termin.bom Option.none⟩
        pure (r, o)
    | Need.both r _ _ => do
        let o ← emit ⟨[], [], Termin.bom Option.none⟩
        pure (r, o) : CM Map (Nat × Nat))) (P := fun _ => True) (by split <;> kpb) fun x _ => ?_
  obtain ⟨r, there⟩ := x
  refine KP.bind' KP.get' fun g _ => KP.ite' _ (KP.pure' trivial) ?_
  refine KP.bind' (kp_sureRequireLook _) fun ned' _ => ?_
  split
  · exact KP.pure' trivial
  · exact KP.ite' _ (KP.pure' trivial) (KP.bind' (KP.addOps' _ (noSplit_cons rfl noSplit_nil)) fun _ _ =>
      KP.pure' trivial)
  · exact KP.bind' (kp_crashNeed _ _ _) fun _ _ => KP.pure' trivial

theorem kp_forl (r o : Nat) : KB (forl r o : CM Map (Nat × Nat)) := by
  unfold forl; kpb

theorem kp_doneBlocks : KB (doneBlocks : CM Map (Nat × Nat)) := by
  unfold doneBlocks; kpb

theorem kp_split {nex : Next S} (hth : JOK nex.th) : KB (Comp.split nex : CM Map (Sure S × Sure S × Nat)) := by
  unfold Comp.split
  refine KP.bind' (KP.emit' (blockOK_of (by simpa [getJmps] using hth) noSplit_nil)) fun o _ => ?_
  exact KP.bind' (kp_splitSure _ _) fun x _ => by obtain ⟨h, t⟩ := x; exact KP.pure' trivial

theorem kp_into {nex : Next S} (hth : JOK nex.th) (axe : Nat) : KB (into nex axe : CM Map (Sure S × Sure S × Nat)) := by
  unfold into
  refine KP.bind' (KP.emit' (blockOK_of (by simpa [getJmps] using hth) noSplit_nil)) fun o _ => ?_
  exact KP.bind' (kp_intoSure _ _ _) fun x _ => by obtain ⟨h, t⟩ := x; exact KP.pure' trivial

theorem kp_copyLazy (o : Nat) (first second : Sure S) : KB (copyLazy o first second : CM Map (Sure S)) := by
  unfold copyLazy
  refine KP.bind' (kp_copyNeed _ _ _ noSplit_nil) fun x hx => ?_
  obtain ⟨ned, ops⟩ := x
  exact KP.bind' (KP.addOps' _ hx) fun _ _ => KP.pure' trivial

theorem kp_copy {first : Next S} (hth : JOK first.th) (second : Sure S) :
    KP (fun n : Next S => JOK n.th) (copy first second : CM Map (Next S)) := by
  unfold copy
  refine KP.bind' (KP.emit' (blockOK_of (by simpa [getJmps] using hth) noSplit_nil)) fun o _ => ?_
  exact KP.bind' (kp_copyLazy _ _ _) fun _ _ => KP.pure' (jok_jmp0 _)

/-- `+past` returns its `next`. -/
theorem kp_past (cod : Bell → Option Bool) (nex : Next S) (nom : Nomm) :
    KP (fun x : Next S => x = nex) (past cod nex nom : CM Map (Next S)) := by
  constructor
  intro g x g' hb h
  obtain ⟨rfl, rfl⟩ := past_some h
  exact ⟨hb, rfl⟩

end Glue
end SkaModel
end Formalization
