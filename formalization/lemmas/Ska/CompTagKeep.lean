import lemmas.Ska.CompSixNextCond

/-!
# The fork-free arms keep `tags`

`KT m`: the computation `m` of `+comp` leaves `tags`, the map of the regions
of the lazy blocks, as it found it.  Only `+set-tag` and `+copy-tag` write
`tags`, and the fork-free model never calls them, so every arm of it is
`KT`: `run` on every nomm and goal (`kt_run`), `+fork-sure` and `+copy`
over full lazy needs (`kt_forkSure`, `kt_copyL`).  Generated from
`CompCond.lean` and `CompSixNextCond.lean` (`KC` with `tags` in place of
`cond`, `+set-tag` left out).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `m` keeps `tags`.  A structure, so that `intro` does not open it. -/
structure KT {α : Type} (m : CM Map α) : Prop where
  keep : ∀ g x g', m g = some (x, g') → g'.tags = g.tags

namespace KT

theorem pure' {α : Type} (a : α) : KT (pure a : CM Map α) := by
  constructor; intro g x g' h; cases h; rfl

theorem bind' {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : KT m) (hf : ∀ a, KT (f a)) :
    KT (m >>= f) := by
  constructor
  intro g x g' h
  rw [bind_apply] at h
  obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ((hf a).keep g1 x g' h2).trans (hm.keep g a g1 h1)

theorem fail {α : Type} : KT (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' h; cases h

theorem crash {α : Type} : KT (crashM : CM Map α) := fail

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KT a) (hb : KT b) :
    KT (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem re' : KT (re : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem oo' : KT (oo : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem freshId' : KT (freshId : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem get' : KT (get : CM Map (Gen Map)) := by constructor; intro g x g' h; cases h; rfl

theorem emir' (o : Nat) (b : Blob) : KT (emir o b : CM Map Unit) := by
  constructor; intro g x g' h; cases h; split <;> rfl

theorem emit' (b : Blob) : KT (emit b : CM Map Nat) := by
  constructor; intro g x g' h; rw [emit_apply] at h; cases h; rfl

theorem addOps' (o : Nat) (ops : List Pole) : KT (addOps o ops : CM Map Unit) := by
  constructor
  intro g x g' h
  unfold addOps at h
  split at h
  · cases h; rfl
  · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

theorem liftO' {α : Type} (x : Option α) : KT (liftO x : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

theorem lift' {α : Type} (x : Option α) : KT ((fun g => x.map fun a => (a, g)) : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

/-- A fold of steps that keep `cond`. -/
theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, KT acc → KT (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), KT acc → KT (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end KT

/-- One step of the tactic `kt`. -/
macro "kt_step" : tactic => `(tactic| first
  | exact KT.pure' _ | exact KT.re' | exact KT.oo' | exact KT.freshId' | exact KT.get'
  | exact KT.emit' _ | exact KT.addOps' _ _ | exact KT.emir' _ _
  | exact KT.fail | exact KT.crash | exact KT.liftO' _ | exact KT.lift' _
  | apply KT.bind' | apply KT.ite' | split | intro _)

/-- Prove `KT` of a computation built from the primitives. -/
macro "kt" : tactic => `(tactic| repeat kt_step)

/-! ## The arms -/

theorem kt_simpleNext (goal : CGoal S) : KT (simpleNext goal : CM Map (Next S)) := by
  unfold simpleNext; kt

theorem kt_bomb (miss : Option Nat) : KT (bomb miss : CM Map (Next S)) := by unfold bomb; kt

theorem kt_must (ned : Need) : KT (must ned : CM Map (Nat × Need)) := by unfold must; kt

theorem kt_splitNeed (ned : Need) (o : Nat) : KT (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · kt
  · kt
  · kt
  · exact KT.bind' (kt_must _) fun _ => KT.bind' (kt_must _) fun _ => by kt

theorem kt_splitSure (sur : Sure S) (o : Nat) : KT (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g' h
  unfold splitSure at h
  obtain ⟨⟨lh, lt⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  have k := (kt_splitNeed _ _).keep g _ g1 h1
  simp only [Prod.mk.injEq] at e
  rw [← e.2]; exact k

theorem kt_split (nex : Next S) : KT (split nex : CM Map (Sure S × Sure S × Nat)) := by
  unfold split
  exact KT.bind' (KT.emit' _) fun _ => KT.bind' (kt_splitSure _ _) fun _ => by kt

theorem kt_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    KT (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops
    rw [intoLoop]
    split
    · kt
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _
      · exact KT.bind' KT.re' fun _ => KT.bind' KT.re' fun _ => ih _ hl _ _ _
      · exact ih _ hl _ _ _
      · exact KT.bind' (kt_must _) fun _ => KT.bind' (kt_must _) fun _ => ih _ hl _ _ _

theorem kt_intoNeed (axe : Nat) (ned : Need) (o : Nat) : KT (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KT.ite' _ KT.fail (KT.ite' _ (KT.pure' _) (kt_intoLoop _ _ _ _ _))

theorem kt_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : KT (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g' h
  unfold intoSure at h
  obtain ⟨⟨ld, lr⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  have k := (kt_intoNeed _ _ _).keep g _ g1 h1
  simp only [Prod.mk.injEq] at e
  rw [← e.2]; exact k

theorem kt_into (nex : Next S) (axe : Nat) : KT (into nex axe : CM Map (Sure S × Sure S × Nat)) := by
  unfold into
  exact KT.bind' (KT.emit' _) fun _ => KT.bind' (kt_intoSure _ _ _) fun _ => by kt

theorem kt_copyNeed : ∀ (a b : Need) (ops : List Pole), KT (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _ => by rw [copyNeed]; kt
  | Need.this _, Need.none, _ => by rw [copyNeed] <;> first | exact KT.pure' _ | nofun
  | Need.pair _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KT.pure' _ | nofun
  | Need.both _ _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KT.pure' _ | nofun
  | Need.this _, Need.this _, _ => by rw [copyNeed]; kt
  | Need.this _, Need.both _ _ _, _ => by rw [copyNeed]; kt
  | Need.this _, Need.pair _ _, _ => by rw [copyNeed]; kt
  | Need.both _ _ _, Need.this _, _ => by rw [copyNeed]; kt
  | Need.pair _ _, Need.this _, _ => by rw [copyNeed]; kt
  | Need.both _ hl tl, Need.both _ hr tr, _ => by
    rw [copyNeed]
    exact KT.bind' (kt_copyNeed hl hr _) fun _ => KT.bind' (kt_copyNeed tl tr _) fun _ => by kt
  | Need.both _ hl tl, Need.pair p q, _ => by
    rw [copyNeed]
    exact KT.bind' KT.re' fun _ =>
      KT.bind' (kt_copyNeed hl p _) fun _ => KT.bind' (kt_copyNeed tl q _) fun _ => by kt
  | Need.pair pl ql, Need.pair pr qr, _ => by
    rw [copyNeed]
    exact KT.bind' (kt_copyNeed pl pr _) fun _ => KT.bind' (kt_copyNeed ql qr _) fun _ => by kt
  | Need.pair pl ql, Need.both _ h t, _ => by
    rw [copyNeed]
    exact KT.bind' (kt_copyNeed pl h _) fun _ => KT.bind' (kt_copyNeed ql t _) fun _ => by kt

theorem kt_copy (first : Next S) (second : Sure S) : KT (copy first second : CM Map (Next S)) := by
  unfold copy copyLazy
  exact KT.bind' (KT.emit' _) fun _ =>
    KT.bind' (KT.bind' (kt_copyNeed _ _ _) fun _ => by kt) fun _ => by kt

theorem kt_lookPath : ∀ (axe : Nat) (ned : Need), KT (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> kt
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact KT.bind' (ih _ hl _) fun _ => by kt
      · exact KT.bind' (ih _ hl _) fun _ => by kt

theorem kt_sureRequireLook (sur : Sure S) : KT (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine KT.foldl' _ (fun acc b h => KT.bind' h fun ned => ?_) _ _ (KT.pure' _)
  exact KT.ite' _ (KT.pure' _) (KT.ite' _ KT.fail (kt_lookPath _ _))

theorem kt_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : KT (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed; split <;> kt

theorem kt_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), KT (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; kt
  | _, Need.this _ => by rw [medeLoop]; kt
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact kt_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact KT.bind' (kt_medeLoop o a p) fun _ => kt_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact kt_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact KT.bind' (KT.addOps' _ _) fun _ => KT.bind' (kt_medeLoop o a h) fun _ => kt_medeLoop o b t

theorem kt_mede (th : Jmp) (som : Noun) (laz : Sure S) : KT (mede th som laz : CM Map Nat) := by
  unfold mede
  exact KT.bind' (KT.emit' _) fun _ => KT.bind' KT.get' fun _ => KT.ite' _ (KT.pure' _)
    (KT.bind' (kt_sureRequireLook _) fun _ => KT.bind' (kt_medeLoop _ _ _) fun _ => KT.pure' _)

theorem kt_collapseLazyAtom (nex : Next S) : KT (collapseLazyAtom nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtom
  refine KT.ite' _ KT.fail (KT.ite' _ (KT.pure' _) (KT.bind' (kt_sureRequireLook _) fun ned => ?_))
  refine KT.bind' (by split <;> kt) fun p => ?_
  refine KT.bind' KT.get' fun _ => KT.ite' _ (KT.pure' _) (KT.bind' (kt_sureRequireLook _) fun ned' => ?_)
  split
  · kt
  · kt
  all_goals exact KT.bind' (kt_crashNeed _ _ _) fun _ => KT.pure' _

theorem kt_forl (r o : Nat) : KT (forl r o : CM Map (Nat × Nat)) := by unfold forl; kt

theorem kt_doneBlocks : KT (doneBlocks : CM Map (Nat × Nat)) := by unfold doneBlocks; kt

theorem kt_past (cod : Bell → Option Bool) (nex : Next S) (nom : Nomm) : KT (past cod nex nom : CM Map (Next S)) := by
  unfold past; kt

/-- **`run` keeps `tags`**, on every nomm and goal. -/
theorem kt_run : ∀ (nm : Nomm) (goal : CGoal S), KT (run nm goal : CM Map (Next S)) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro goal
    unfold run
    refine KT.bind' (by cases goal <;> kt) fun goal => ?_
    cases goal
    · exact KT.bind' (KT.emit' _) fun _ => KT.bind' (ihq _) fun _ => KT.bind' (kt_past _ _ _) fun _ =>
        KT.bind' (ihp _) fun _ => kt_copy _ _
    · exact KT.fail
    · exact KT.bind' (kt_split _) fun _ => KT.bind' (kt_past _ _ _) fun _ => KT.bind' (ihq _) fun _ =>
        KT.bind' (kt_past _ _ _) fun _ => KT.bind' (ihp _) fun _ => kt_copy _ _
  | n0 ax =>
    intro goal
    unfold run
    refine KT.ite' _ (kt_bomb _) (KT.bind' (kt_simpleNext _) fun _ => KT.ite' _ (KT.pure' _) ?_)
    split <;> kt
  | n1 k =>
    intro goal
    unfold run
    cases goal
    · exact KT.ite' _ (KT.pure' _) (KT.ite' _ (KT.pure' _) (kt_bomb _))
    · kt
    · exact KT.bind' (kt_mede _ _ _) fun _ => KT.pure' _
  | n3 p ih =>
    intro goal
    unfold run
    cases goal
    · exact KT.bind' KT.re' fun _ => KT.bind' (KT.emit' _) fun _ => ih _
    · exact KT.bind' kt_doneBlocks fun _ => KT.bind' KT.re' fun _ => KT.bind' (KT.emit' _) fun _ => ih _
    · refine KT.ite' _ (ih _) (KT.bind' (kt_collapseLazyAtom _) fun a => ?_)
      cases a
      · exact KT.fail
      · exact KT.bind' (kt_forl _ _) fun _ => KT.bind' KT.re' fun _ => KT.bind' (KT.emit' _) fun _ => ih _
  | n4 p ih =>
    intro goal
    unfold run
    cases goal
    · exact KT.bind' KT.re' fun _ => KT.bind' KT.re' fun _ => KT.bind' (KT.emit' _) fun _ => ih _
    · exact KT.bind' KT.re' fun _ => KT.bind' KT.re' fun _ => KT.bind' (KT.emit' _) fun _ => ih _
    · refine KT.bind' (kt_collapseLazyAtom _) fun a => KT.bind' (by cases a <;> kt) fun _ => ?_
      exact KT.bind' KT.re' fun _ => KT.bind' (KT.emit' _) fun _ => ih _
  | n5 p q ihp ihq =>
    intro goal
    unfold run
    refine KT.bind' KT.re' fun _ => KT.bind' KT.re' fun _ => KT.bind' ?_ fun _ =>
      KT.bind' (ihq _) fun _ => KT.bind' (kt_past _ _ _) fun _ => KT.bind' (ihp _) fun _ => kt_copy _ _
    cases goal
    · kt
    · exact KT.bind' kt_doneBlocks fun _ => KT.emit' _
    · refine KT.bind' (kt_collapseLazyAtom _) fun a => ?_
      cases a
      · kt
      · exact KT.bind' (kt_forl _ _) fun _ => KT.emit' _
  | n7 p q ihp ihq =>
    intro goal
    unfold run
    exact KT.bind' (ihq _) fun _ => ihp _
  | n10 a v q ihv ihq =>
    intro goal
    unfold run
    exact KT.bind' (kt_simpleNext _) fun _ => KT.bind' (kt_into _ _) fun _ => KT.bind' (kt_past _ _ _) fun _ =>
      KT.bind' (ihv _) fun _ => KT.bind' (kt_past _ _ _) fun _ => KT.bind' (ihq _) fun _ => kt_copy _ _
  | _ =>
    intro goal
    unfold run
    exact KT.fail

/-! ## `+fork-sure` and `+copy` -/

theorem kt_forkNeedGo : ∀ (ned : Need), KT (forkNeedGo ned : CM Map (Need × Need))
  | Need.none => by simp only [forkNeedGo]; exact KT.pure' _
  | Need.this _ => by simp only [forkNeedGo]; kt
  | Need.pair p q => by
    simp only [forkNeedGo]
    refine KT.bind' (kt_forkNeedGo p) fun a => ?_
    rcases a with ⟨h0, h1⟩
    exact KT.bind' (kt_forkNeedGo q) fun b => by rcases b with ⟨t0, t1⟩; exact KT.pure' _
  | Need.both _ p q => by
    simp only [forkNeedGo]
    refine KT.bind' KT.re' fun _ => KT.bind' KT.re' fun _ => KT.bind' (kt_forkNeedGo p) fun a => ?_
    rcases a with ⟨h0, h1⟩
    exact KT.bind' (kt_forkNeedGo q) fun b => by rcases b with ⟨t0, t1⟩; exact KT.pure' _

theorem kt_forkNeed (ned : Need) (o o0 o1 : Nat) : KT (forkNeed ned o o0 o1 : CM Map (Need × Need)) := by
  unfold forkNeed
  refine KT.bind' (kt_forkNeedGo ned) fun a => ?_
  rcases a with ⟨n0, n1⟩
  kt

theorem kt_forkSure (sur : Sure S) (o o0 o1 : Nat) : KT (forkSure sur o o0 o1 : CM Map (Sure S × Sure S)) := by
  unfold forkSure
  refine KT.bind' (kt_forkNeed _ _ _ _) fun a => ?_
  rcases a with ⟨n0, n1⟩
  exact KT.pure' _

mutual
/-- **`+copy-lazy` keeps `tags`.** -/
theorem kt_copyLazyL (o : Nat) : ∀ (a b : Lazy S), KT (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine KT.bind' (kt_copyNeed _ _ _) fun a => ?_
    rcases a with ⟨ned, ops⟩
    refine KT.bind' (KT.addOps' _ _) fun _ => KT.bind' ?_ fun _ => KT.bind' ?_ fun _ => KT.pure' _
    · split
      · exact KT.pure' _
      · split
        · exact KT.pure' _
        · exact KT.bind' (kt_mergeForks _ f1) fun _ => KT.pure' _
    · split
      · exact KT.pure' _
      · split
        · exact KT.pure' _
        · exact KT.bind' (kt_mergeBonds _ b1) fun _ => KT.pure' _

theorem kt_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    KT (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact KT.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine KT.bind' ?_ fun _ => KT.bind' (kt_mergeForks idx rest) fun _ => KT.pure' _
    split
    · exact KT.pure' _
    · split
      · exact KT.bind' (kt_copyLazyL oy y _) fun _ => KT.bind' (kt_copyLazyL on n _) fun _ => KT.pure' _
      · exact KT.fail

theorem kt_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    KT (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact KT.pure' _
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine KT.bind' ?_ fun _ => KT.bind' (kt_mergeBonds idx rest) fun _ => KT.pure' _
    split
    · exact KT.pure' _
    · exact KT.bind' (kt_copyLazyL ob l _) fun _ => KT.pure' _
end

theorem kt_copyL (first : NextL S) (second : Lazy S) : KT (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  exact KT.bind' (KT.emit' _) fun _ => KT.bind' (kt_copyLazyL _ _ _) fun _ => KT.pure' _

end Comp
end SkaModel
end Formalization
