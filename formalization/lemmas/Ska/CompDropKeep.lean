import lemmas.Ska.CompSixNextCond

/-!
# The arms keep `drop`

`KD m`: the computation `m` of `+comp` leaves the flag `drop` as it found
it: `run` on every nomm and goal (`kd_run`), `+fork-sure` and `+copy` over
full lazy needs (`kd_forkSure`, `kd_copyL`).  Generated from `CompCond.lean`
and `CompSixNextCond.lean` (`KC` with `drop` in place of `cond`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `m` keeps `drop`.  A structure, so that `intro` does not open it. -/
structure KD {α : Type} (m : CM Map α) : Prop where
  keep : ∀ g x g', m g = some (x, g') → g'.drop = g.drop

namespace KD

theorem pure' {α : Type} (a : α) : KD (pure a : CM Map α) := by
  constructor; intro g x g' h; cases h; rfl

theorem bind' {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : KD m) (hf : ∀ a, KD (f a)) :
    KD (m >>= f) := by
  constructor
  intro g x g' h
  rw [bind_apply] at h
  obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ((hf a).keep g1 x g' h2).trans (hm.keep g a g1 h1)

theorem fail {α : Type} : KD (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' h; cases h

theorem crash {α : Type} : KD (crashM : CM Map α) := fail

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KD a) (hb : KD b) :
    KD (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem re' : KD (re : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem oo' : KD (oo : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem freshId' : KD (freshId : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem get' : KD (get : CM Map (Gen Map)) := by constructor; intro g x g' h; cases h; rfl

theorem setTag' (o : Nat) (region : List Nat) : KD (setTag o region : CM Map Unit) := by
  constructor; intro g x g' h; cases h; split <;> rfl

theorem emir' (o : Nat) (b : Blob) : KD (emir o b : CM Map Unit) := by
  constructor; intro g x g' h; cases h; split <;> rfl

theorem emit' (b : Blob) : KD (emit b : CM Map Nat) := by
  constructor; intro g x g' h; rw [emit_apply] at h; cases h; rfl

theorem addOps' (o : Nat) (ops : List Pole) : KD (addOps o ops : CM Map Unit) := by
  constructor
  intro g x g' h
  unfold addOps at h
  split at h
  · cases h; rfl
  · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

theorem liftO' {α : Type} (x : Option α) : KD (liftO x : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

theorem lift' {α : Type} (x : Option α) : KD ((fun g => x.map fun a => (a, g)) : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

/-- A fold of steps that keep `cond`. -/
theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, KD acc → KD (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), KD acc → KD (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end KD

/-- One step of the tactic `kd`. -/
macro "kd_step" : tactic => `(tactic| first
  | exact KD.pure' _ | exact KD.re' | exact KD.oo' | exact KD.freshId' | exact KD.get'
  | exact KD.emit' _ | exact KD.addOps' _ _ | exact KD.setTag' _ _ | exact KD.emir' _ _
  | exact KD.fail | exact KD.crash | exact KD.liftO' _ | exact KD.lift' _
  | apply KD.bind' | apply KD.ite' | split | intro _)

/-- Prove `KD` of a computation built from the primitives. -/
macro "kd" : tactic => `(tactic| repeat kd_step)

/-! ## The arms -/

theorem kd_simpleNext (goal : CGoal S) : KD (simpleNext goal : CM Map (Next S)) := by
  unfold simpleNext; kd

theorem kd_bomb (miss : Option Nat) : KD (bomb miss : CM Map (Next S)) := by unfold bomb; kd

theorem kd_must (ned : Need) : KD (must ned : CM Map (Nat × Need)) := by unfold must; kd

theorem kd_splitNeed (ned : Need) (o : Nat) : KD (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · kd
  · kd
  · kd
  · exact KD.bind' (kd_must _) fun _ => KD.bind' (kd_must _) fun _ => by kd

theorem kd_splitSure (sur : Sure S) (o : Nat) : KD (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g' h
  unfold splitSure at h
  obtain ⟨⟨lh, lt⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  have k := (kd_splitNeed _ _).keep g _ g1 h1
  simp only [Prod.mk.injEq] at e
  rw [← e.2]; exact k

theorem kd_split (nex : Next S) : KD (split nex : CM Map (Sure S × Sure S × Nat)) := by
  unfold split
  exact KD.bind' (KD.emit' _) fun _ => KD.bind' (kd_splitSure _ _) fun _ => by kd

theorem kd_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    KD (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops
    rw [intoLoop]
    split
    · kd
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _
      · exact KD.bind' KD.re' fun _ => KD.bind' KD.re' fun _ => ih _ hl _ _ _
      · exact ih _ hl _ _ _
      · exact KD.bind' (kd_must _) fun _ => KD.bind' (kd_must _) fun _ => ih _ hl _ _ _

theorem kd_intoNeed (axe : Nat) (ned : Need) (o : Nat) : KD (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KD.ite' _ KD.fail (KD.ite' _ (KD.pure' _) (kd_intoLoop _ _ _ _ _))

theorem kd_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : KD (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g' h
  unfold intoSure at h
  obtain ⟨⟨ld, lr⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  have k := (kd_intoNeed _ _ _).keep g _ g1 h1
  simp only [Prod.mk.injEq] at e
  rw [← e.2]; exact k

theorem kd_into (nex : Next S) (axe : Nat) : KD (into nex axe : CM Map (Sure S × Sure S × Nat)) := by
  unfold into
  exact KD.bind' (KD.emit' _) fun _ => KD.bind' (kd_intoSure _ _ _) fun _ => by kd

theorem kd_copyNeed : ∀ (a b : Need) (ops : List Pole), KD (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _ => by rw [copyNeed]; kd
  | Need.this _, Need.none, _ => by rw [copyNeed] <;> first | exact KD.pure' _ | nofun
  | Need.pair _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KD.pure' _ | nofun
  | Need.both _ _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KD.pure' _ | nofun
  | Need.this _, Need.this _, _ => by rw [copyNeed]; kd
  | Need.this _, Need.both _ _ _, _ => by rw [copyNeed]; kd
  | Need.this _, Need.pair _ _, _ => by rw [copyNeed]; kd
  | Need.both _ _ _, Need.this _, _ => by rw [copyNeed]; kd
  | Need.pair _ _, Need.this _, _ => by rw [copyNeed]; kd
  | Need.both _ hl tl, Need.both _ hr tr, _ => by
    rw [copyNeed]
    exact KD.bind' (kd_copyNeed hl hr _) fun _ => KD.bind' (kd_copyNeed tl tr _) fun _ => by kd
  | Need.both _ hl tl, Need.pair p q, _ => by
    rw [copyNeed]
    exact KD.bind' KD.re' fun _ =>
      KD.bind' (kd_copyNeed hl p _) fun _ => KD.bind' (kd_copyNeed tl q _) fun _ => by kd
  | Need.pair pl ql, Need.pair pr qr, _ => by
    rw [copyNeed]
    exact KD.bind' (kd_copyNeed pl pr _) fun _ => KD.bind' (kd_copyNeed ql qr _) fun _ => by kd
  | Need.pair pl ql, Need.both _ h t, _ => by
    rw [copyNeed]
    exact KD.bind' (kd_copyNeed pl h _) fun _ => KD.bind' (kd_copyNeed ql t _) fun _ => by kd

theorem kd_copy (first : Next S) (second : Sure S) : KD (copy first second : CM Map (Next S)) := by
  unfold copy copyLazy
  exact KD.bind' (KD.emit' _) fun _ =>
    KD.bind' (KD.bind' (kd_copyNeed _ _ _) fun _ => by kd) fun _ => by kd

theorem kd_lookPath : ∀ (axe : Nat) (ned : Need), KD (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> kd
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact KD.bind' (ih _ hl _) fun _ => by kd
      · exact KD.bind' (ih _ hl _) fun _ => by kd

theorem kd_sureRequireLook (sur : Sure S) : KD (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine KD.foldl' _ (fun acc b h => KD.bind' h fun ned => ?_) _ _ (KD.pure' _)
  exact KD.ite' _ (KD.pure' _) (KD.ite' _ KD.fail (kd_lookPath _ _))

theorem kd_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : KD (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed; split <;> kd

theorem kd_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), KD (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; kd
  | _, Need.this _ => by rw [medeLoop]; kd
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact kd_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact KD.bind' (kd_medeLoop o a p) fun _ => kd_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact kd_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact KD.bind' (KD.addOps' _ _) fun _ => KD.bind' (kd_medeLoop o a h) fun _ => kd_medeLoop o b t

theorem kd_mede (th : Jmp) (som : Noun) (laz : Sure S) : KD (mede th som laz : CM Map Nat) := by
  unfold mede
  exact KD.bind' (KD.emit' _) fun _ => KD.bind' KD.get' fun _ => KD.ite' _ (KD.pure' _)
    (KD.bind' (kd_sureRequireLook _) fun _ => KD.bind' (kd_medeLoop _ _ _) fun _ => KD.pure' _)

theorem kd_collapseLazyAtom (nex : Next S) : KD (collapseLazyAtom nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtom
  refine KD.ite' _ KD.fail (KD.ite' _ (KD.pure' _) (KD.bind' (kd_sureRequireLook _) fun ned => ?_))
  refine KD.bind' (by split <;> kd) fun p => ?_
  refine KD.bind' KD.get' fun _ => KD.ite' _ (KD.pure' _) (KD.bind' (kd_sureRequireLook _) fun ned' => ?_)
  split
  · kd
  · kd
  all_goals exact KD.bind' (kd_crashNeed _ _ _) fun _ => KD.pure' _

theorem kd_forl (r o : Nat) : KD (forl r o : CM Map (Nat × Nat)) := by unfold forl; kd

theorem kd_doneBlocks : KD (doneBlocks : CM Map (Nat × Nat)) := by unfold doneBlocks; kd

theorem kd_past (cod : Bell → Option Bool) (nex : Next S) (nom : Nomm) : KD (past cod nex nom : CM Map (Next S)) := by
  unfold past; kd

/-- **`run` keeps `drop`**, on every nomm and goal. -/
theorem kd_run : ∀ (nm : Nomm) (goal : CGoal S), KD (run nm goal : CM Map (Next S)) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro goal
    unfold run
    refine KD.bind' (by cases goal <;> kd) fun goal => ?_
    cases goal
    · exact KD.bind' (KD.emit' _) fun _ => KD.bind' (ihq _) fun _ => KD.bind' (kd_past _ _ _) fun _ =>
        KD.bind' (ihp _) fun _ => kd_copy _ _
    · exact KD.fail
    · exact KD.bind' (kd_split _) fun _ => KD.bind' (kd_past _ _ _) fun _ => KD.bind' (ihq _) fun _ =>
        KD.bind' (kd_past _ _ _) fun _ => KD.bind' (ihp _) fun _ => kd_copy _ _
  | n0 ax =>
    intro goal
    unfold run
    refine KD.ite' _ (kd_bomb _) (KD.bind' (kd_simpleNext _) fun _ => KD.ite' _ (KD.pure' _) ?_)
    split <;> kd
  | n1 k =>
    intro goal
    unfold run
    cases goal
    · exact KD.ite' _ (KD.pure' _) (KD.ite' _ (KD.pure' _) (kd_bomb _))
    · kd
    · exact KD.bind' (kd_mede _ _ _) fun _ => KD.pure' _
  | n3 p ih =>
    intro goal
    unfold run
    cases goal
    · exact KD.bind' KD.re' fun _ => KD.bind' (KD.emit' _) fun _ => ih _
    · exact KD.bind' kd_doneBlocks fun _ => KD.bind' KD.re' fun _ => KD.bind' (KD.emit' _) fun _ => ih _
    · refine KD.ite' _ (ih _) (KD.bind' (kd_collapseLazyAtom _) fun a => ?_)
      cases a
      · exact KD.fail
      · exact KD.bind' (kd_forl _ _) fun _ => KD.bind' KD.re' fun _ => KD.bind' (KD.emit' _) fun _ => ih _
  | n4 p ih =>
    intro goal
    unfold run
    cases goal
    · exact KD.bind' KD.re' fun _ => KD.bind' KD.re' fun _ => KD.bind' (KD.emit' _) fun _ => ih _
    · exact KD.bind' KD.re' fun _ => KD.bind' KD.re' fun _ => KD.bind' (KD.emit' _) fun _ => ih _
    · refine KD.bind' (kd_collapseLazyAtom _) fun a => KD.bind' (by cases a <;> kd) fun _ => ?_
      exact KD.bind' KD.re' fun _ => KD.bind' (KD.emit' _) fun _ => ih _
  | n5 p q ihp ihq =>
    intro goal
    unfold run
    refine KD.bind' KD.re' fun _ => KD.bind' KD.re' fun _ => KD.bind' ?_ fun _ =>
      KD.bind' (ihq _) fun _ => KD.bind' (kd_past _ _ _) fun _ => KD.bind' (ihp _) fun _ => kd_copy _ _
    cases goal
    · kd
    · exact KD.bind' kd_doneBlocks fun _ => KD.emit' _
    · refine KD.bind' (kd_collapseLazyAtom _) fun a => ?_
      cases a
      · kd
      · exact KD.bind' (kd_forl _ _) fun _ => KD.emit' _
  | n7 p q ihp ihq =>
    intro goal
    unfold run
    exact KD.bind' (ihq _) fun _ => ihp _
  | n10 a v q ihv ihq =>
    intro goal
    unfold run
    exact KD.bind' (kd_simpleNext _) fun _ => KD.bind' (kd_into _ _) fun _ => KD.bind' (kd_past _ _ _) fun _ =>
      KD.bind' (ihv _) fun _ => KD.bind' (kd_past _ _ _) fun _ => KD.bind' (ihq _) fun _ => kd_copy _ _
  | _ =>
    intro goal
    unfold run
    exact KD.fail

/-! ## `+fork-sure` and `+copy` -/

theorem kd_forkNeedGo : ∀ (ned : Need), KD (forkNeedGo ned : CM Map (Need × Need))
  | Need.none => by simp only [forkNeedGo]; exact KD.pure' _
  | Need.this _ => by simp only [forkNeedGo]; kd
  | Need.pair p q => by
    simp only [forkNeedGo]
    refine KD.bind' (kd_forkNeedGo p) fun a => ?_
    rcases a with ⟨h0, h1⟩
    exact KD.bind' (kd_forkNeedGo q) fun b => by rcases b with ⟨t0, t1⟩; exact KD.pure' _
  | Need.both _ p q => by
    simp only [forkNeedGo]
    refine KD.bind' KD.re' fun _ => KD.bind' KD.re' fun _ => KD.bind' (kd_forkNeedGo p) fun a => ?_
    rcases a with ⟨h0, h1⟩
    exact KD.bind' (kd_forkNeedGo q) fun b => by rcases b with ⟨t0, t1⟩; exact KD.pure' _

theorem kd_forkNeed (ned : Need) (o o0 o1 : Nat) : KD (forkNeed ned o o0 o1 : CM Map (Need × Need)) := by
  unfold forkNeed
  refine KD.bind' (kd_forkNeedGo ned) fun a => ?_
  rcases a with ⟨n0, n1⟩
  kd

theorem kd_forkSure (sur : Sure S) (o o0 o1 : Nat) : KD (forkSure sur o o0 o1 : CM Map (Sure S × Sure S)) := by
  unfold forkSure
  refine KD.bind' (kd_forkNeed _ _ _ _) fun a => ?_
  rcases a with ⟨n0, n1⟩
  exact KD.pure' _

mutual
/-- **`+copy-lazy` keeps `drop`.** -/
theorem kd_copyLazyL (o : Nat) : ∀ (a b : Lazy S), KD (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine KD.bind' (kd_copyNeed _ _ _) fun a => ?_
    rcases a with ⟨ned, ops⟩
    refine KD.bind' (KD.addOps' _ _) fun _ => KD.bind' ?_ fun _ => KD.bind' ?_ fun _ => KD.pure' _
    · split
      · exact KD.pure' _
      · split
        · exact KD.pure' _
        · exact KD.bind' (kd_mergeForks _ f1) fun _ => KD.pure' _
    · split
      · exact KD.pure' _
      · split
        · exact KD.pure' _
        · exact KD.bind' (kd_mergeBonds _ b1) fun _ => KD.pure' _

theorem kd_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    KD (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact KD.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine KD.bind' ?_ fun _ => KD.bind' (kd_mergeForks idx rest) fun _ => KD.pure' _
    split
    · exact KD.pure' _
    · split
      · exact KD.bind' (kd_copyLazyL oy y _) fun _ => KD.bind' (kd_copyLazyL on n _) fun _ => KD.pure' _
      · exact KD.fail

theorem kd_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    KD (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact KD.pure' _
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine KD.bind' ?_ fun _ => KD.bind' (kd_mergeBonds idx rest) fun _ => KD.pure' _
    split
    · exact KD.pure' _
    · exact KD.bind' (kd_copyLazyL ob l _) fun _ => KD.pure' _
end

theorem kd_copyL (first : NextL S) (second : Lazy S) : KD (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  exact KD.bind' (KD.emit' _) fun _ => KD.bind' (kd_copyLazyL _ _ _) fun _ => KD.pure' _

end Comp
end SkaModel
end Formalization
