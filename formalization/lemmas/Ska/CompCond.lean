import lemmas.Ska.CompLazyFinal

/-!
# No proxy register in the fork-free model

`KC m`: the computation `m` of `+comp` leaves `cond`, the map of proxy
registers, as it found it.  Only `+proxy` writes `cond`, and the fork-free
model never calls it, so every arm of it is `KC`: `run` on every nomm and
goal (`kc_run`), `+need-ord-alloc-regs`, and `+coerce-lazy` over full lazy
needs (`kc_coerceLazyL`).  This is what makes `toStraightF`, the whole of
`+to-straight`, take its renaming path in the scope already proved.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `m` keeps `cond`.  A structure, so that `intro` does not open it. -/
structure KC {α : Type} (m : CM Map α) : Prop where
  keep : ∀ g x g', m g = some (x, g') → g'.cond = g.cond

namespace KC

theorem pure' {α : Type} (a : α) : KC (pure a : CM Map α) := by
  constructor; intro g x g' h; cases h; rfl

theorem bind' {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : KC m) (hf : ∀ a, KC (f a)) :
    KC (m >>= f) := by
  constructor
  intro g x g' h
  rw [bind_apply] at h
  obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ((hf a).keep g1 x g' h2).trans (hm.keep g a g1 h1)

theorem fail {α : Type} : KC (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' h; cases h

theorem crash {α : Type} : KC (crashM : CM Map α) := fail

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KC a) (hb : KC b) :
    KC (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem re' : KC (re : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem oo' : KC (oo : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem freshId' : KC (freshId : CM Map Nat) := by constructor; intro g x g' h; cases h; rfl
theorem get' : KC (get : CM Map (Gen Map)) := by constructor; intro g x g' h; cases h; rfl

theorem setTag' (o : Nat) (region : List Nat) : KC (setTag o region : CM Map Unit) := by
  constructor; intro g x g' h; cases h; split <;> rfl

theorem emir' (o : Nat) (b : Blob) : KC (emir o b : CM Map Unit) := by
  constructor; intro g x g' h; cases h; split <;> rfl

theorem emit' (b : Blob) : KC (emit b : CM Map Nat) := by
  constructor; intro g x g' h; rw [emit_apply] at h; cases h; rfl

theorem addOps' (o : Nat) (ops : List Pole) : KC (addOps o ops : CM Map Unit) := by
  constructor
  intro g x g' h
  unfold addOps at h
  split at h
  · cases h; rfl
  · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

theorem liftO' {α : Type} (x : Option α) : KC (liftO x : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

theorem lift' {α : Type} (x : Option α) : KC ((fun g => x.map fun a => (a, g)) : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; rfl

/-- A fold of steps that keep `cond`. -/
theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, KC acc → KC (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), KC acc → KC (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end KC

/-- One step of the tactic `kc`. -/
macro "kc_step" : tactic => `(tactic| first
  | exact KC.pure' _ | exact KC.re' | exact KC.oo' | exact KC.freshId' | exact KC.get'
  | exact KC.emit' _ | exact KC.addOps' _ _ | exact KC.setTag' _ _ | exact KC.emir' _ _
  | exact KC.fail | exact KC.crash | exact KC.liftO' _ | exact KC.lift' _
  | apply KC.bind' | apply KC.ite' | split | intro _)

/-- Prove `KC` of a computation built from the primitives. -/
macro "kc" : tactic => `(tactic| repeat kc_step)

/-! ## The arms -/

theorem kc_simpleNext (goal : CGoal S) : KC (simpleNext goal : CM Map (Next S)) := by
  unfold simpleNext; kc

theorem kc_bomb (miss : Option Nat) : KC (bomb miss : CM Map (Next S)) := by unfold bomb; kc

theorem kc_must (ned : Need) : KC (must ned : CM Map (Nat × Need)) := by unfold must; kc

theorem kc_splitNeed (ned : Need) (o : Nat) : KC (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · kc
  · kc
  · kc
  · exact KC.bind' (kc_must _) fun _ => KC.bind' (kc_must _) fun _ => by kc

theorem kc_splitSure (sur : Sure S) (o : Nat) : KC (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g' h
  unfold splitSure at h
  obtain ⟨⟨lh, lt⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  have k := (kc_splitNeed _ _).keep g _ g1 h1
  simp only [Prod.mk.injEq] at e
  rw [← e.2]; exact k

theorem kc_split (nex : Next S) : KC (split nex : CM Map (Sure S × Sure S × Nat)) := by
  unfold split
  exact KC.bind' (KC.emit' _) fun _ => KC.bind' (kc_splitSure _ _) fun _ => by kc

theorem kc_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    KC (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops
    rw [intoLoop]
    split
    · kc
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _
      · exact KC.bind' KC.re' fun _ => KC.bind' KC.re' fun _ => ih _ hl _ _ _
      · exact ih _ hl _ _ _
      · exact KC.bind' (kc_must _) fun _ => KC.bind' (kc_must _) fun _ => ih _ hl _ _ _

theorem kc_intoNeed (axe : Nat) (ned : Need) (o : Nat) : KC (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KC.ite' _ KC.fail (KC.ite' _ (KC.pure' _) (kc_intoLoop _ _ _ _ _))

theorem kc_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : KC (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g' h
  unfold intoSure at h
  obtain ⟨⟨ld, lr⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  have k := (kc_intoNeed _ _ _).keep g _ g1 h1
  simp only [Prod.mk.injEq] at e
  rw [← e.2]; exact k

theorem kc_into (nex : Next S) (axe : Nat) : KC (into nex axe : CM Map (Sure S × Sure S × Nat)) := by
  unfold into
  exact KC.bind' (KC.emit' _) fun _ => KC.bind' (kc_intoSure _ _ _) fun _ => by kc

theorem kc_copyNeed : ∀ (a b : Need) (ops : List Pole), KC (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _ => by rw [copyNeed]; kc
  | Need.this _, Need.none, _ => by rw [copyNeed] <;> first | exact KC.pure' _ | nofun
  | Need.pair _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KC.pure' _ | nofun
  | Need.both _ _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KC.pure' _ | nofun
  | Need.this _, Need.this _, _ => by rw [copyNeed]; kc
  | Need.this _, Need.both _ _ _, _ => by rw [copyNeed]; kc
  | Need.this _, Need.pair _ _, _ => by rw [copyNeed]; kc
  | Need.both _ _ _, Need.this _, _ => by rw [copyNeed]; kc
  | Need.pair _ _, Need.this _, _ => by rw [copyNeed]; kc
  | Need.both _ hl tl, Need.both _ hr tr, _ => by
    rw [copyNeed]
    exact KC.bind' (kc_copyNeed hl hr _) fun _ => KC.bind' (kc_copyNeed tl tr _) fun _ => by kc
  | Need.both _ hl tl, Need.pair p q, _ => by
    rw [copyNeed]
    exact KC.bind' KC.re' fun _ =>
      KC.bind' (kc_copyNeed hl p _) fun _ => KC.bind' (kc_copyNeed tl q _) fun _ => by kc
  | Need.pair pl ql, Need.pair pr qr, _ => by
    rw [copyNeed]
    exact KC.bind' (kc_copyNeed pl pr _) fun _ => KC.bind' (kc_copyNeed ql qr _) fun _ => by kc
  | Need.pair pl ql, Need.both _ h t, _ => by
    rw [copyNeed]
    exact KC.bind' (kc_copyNeed pl h _) fun _ => KC.bind' (kc_copyNeed ql t _) fun _ => by kc

theorem kc_copy (first : Next S) (second : Sure S) : KC (copy first second : CM Map (Next S)) := by
  unfold copy copyLazy
  exact KC.bind' (KC.emit' _) fun _ =>
    KC.bind' (KC.bind' (kc_copyNeed _ _ _) fun _ => by kc) fun _ => by kc

theorem kc_lookPath : ∀ (axe : Nat) (ned : Need), KC (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> kc
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact KC.bind' (ih _ hl _) fun _ => by kc
      · exact KC.bind' (ih _ hl _) fun _ => by kc

theorem kc_sureRequireLook (sur : Sure S) : KC (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine KC.foldl' _ (fun acc b h => KC.bind' h fun ned => ?_) _ _ (KC.pure' _)
  exact KC.ite' _ (KC.pure' _) (KC.ite' _ KC.fail (kc_lookPath _ _))

theorem kc_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : KC (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed; split <;> kc

theorem kc_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), KC (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; kc
  | _, Need.this _ => by rw [medeLoop]; kc
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact kc_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact KC.bind' (kc_medeLoop o a p) fun _ => kc_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact kc_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact KC.bind' (KC.addOps' _ _) fun _ => KC.bind' (kc_medeLoop o a h) fun _ => kc_medeLoop o b t

theorem kc_mede (th : Jmp) (som : Noun) (laz : Sure S) : KC (mede th som laz : CM Map Nat) := by
  unfold mede
  exact KC.bind' (KC.emit' _) fun _ => KC.bind' KC.get' fun _ => KC.ite' _ (KC.pure' _)
    (KC.bind' (kc_sureRequireLook _) fun _ => KC.bind' (kc_medeLoop _ _ _) fun _ => KC.pure' _)

theorem kc_collapseLazyAtom (nex : Next S) : KC (collapseLazyAtom nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtom
  refine KC.ite' _ KC.fail (KC.ite' _ (KC.pure' _) (KC.bind' (kc_sureRequireLook _) fun ned => ?_))
  refine KC.bind' (by split <;> kc) fun p => ?_
  refine KC.bind' KC.get' fun _ => KC.ite' _ (KC.pure' _) (KC.bind' (kc_sureRequireLook _) fun ned' => ?_)
  split
  · kc
  · kc
  all_goals exact KC.bind' (kc_crashNeed _ _ _) fun _ => KC.pure' _

theorem kc_forl (r o : Nat) : KC (forl r o : CM Map (Nat × Nat)) := by unfold forl; kc

theorem kc_doneBlocks : KC (doneBlocks : CM Map (Nat × Nat)) := by unfold doneBlocks; kc

theorem kc_past (cod : Bell → Option Bool) (nex : Next S) (nom : Nomm) : KC (past cod nex nom : CM Map (Next S)) := by
  unfold past; kc

/-- **`run` keeps `cond`**, on every nomm and goal. -/
theorem kc_run : ∀ (nm : Nomm) (goal : CGoal S), KC (run nm goal : CM Map (Next S)) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro goal
    unfold run
    refine KC.bind' (by cases goal <;> kc) fun goal => ?_
    cases goal
    · exact KC.bind' (KC.emit' _) fun _ => KC.bind' (ihq _) fun _ => KC.bind' (kc_past _ _ _) fun _ =>
        KC.bind' (ihp _) fun _ => kc_copy _ _
    · exact KC.fail
    · exact KC.bind' (kc_split _) fun _ => KC.bind' (kc_past _ _ _) fun _ => KC.bind' (ihq _) fun _ =>
        KC.bind' (kc_past _ _ _) fun _ => KC.bind' (ihp _) fun _ => kc_copy _ _
  | n0 ax =>
    intro goal
    unfold run
    refine KC.ite' _ (kc_bomb _) (KC.bind' (kc_simpleNext _) fun _ => KC.ite' _ (KC.pure' _) ?_)
    split <;> kc
  | n1 k =>
    intro goal
    unfold run
    cases goal
    · exact KC.ite' _ (KC.pure' _) (KC.ite' _ (KC.pure' _) (kc_bomb _))
    · kc
    · exact KC.bind' (kc_mede _ _ _) fun _ => KC.pure' _
  | n3 p ih =>
    intro goal
    unfold run
    cases goal
    · exact KC.bind' KC.re' fun _ => KC.bind' (KC.emit' _) fun _ => ih _
    · exact KC.bind' kc_doneBlocks fun _ => KC.bind' KC.re' fun _ => KC.bind' (KC.emit' _) fun _ => ih _
    · refine KC.ite' _ (ih _) (KC.bind' (kc_collapseLazyAtom _) fun a => ?_)
      cases a
      · exact KC.fail
      · exact KC.bind' (kc_forl _ _) fun _ => KC.bind' KC.re' fun _ => KC.bind' (KC.emit' _) fun _ => ih _
  | n4 p ih =>
    intro goal
    unfold run
    cases goal
    · exact KC.bind' KC.re' fun _ => KC.bind' KC.re' fun _ => KC.bind' (KC.emit' _) fun _ => ih _
    · exact KC.bind' KC.re' fun _ => KC.bind' KC.re' fun _ => KC.bind' (KC.emit' _) fun _ => ih _
    · refine KC.bind' (kc_collapseLazyAtom _) fun a => KC.bind' (by cases a <;> kc) fun _ => ?_
      exact KC.bind' KC.re' fun _ => KC.bind' (KC.emit' _) fun _ => ih _
  | n5 p q ihp ihq =>
    intro goal
    unfold run
    refine KC.bind' KC.re' fun _ => KC.bind' KC.re' fun _ => KC.bind' ?_ fun _ =>
      KC.bind' (ihq _) fun _ => KC.bind' (kc_past _ _ _) fun _ => KC.bind' (ihp _) fun _ => kc_copy _ _
    cases goal
    · kc
    · exact KC.bind' kc_doneBlocks fun _ => KC.emit' _
    · refine KC.bind' (kc_collapseLazyAtom _) fun a => ?_
      cases a
      · kc
      · exact KC.bind' (kc_forl _ _) fun _ => KC.emit' _
  | n7 p q ihp ihq =>
    intro goal
    unfold run
    exact KC.bind' (ihq _) fun _ => ihp _
  | n10 a v q ihv ihq =>
    intro goal
    unfold run
    exact KC.bind' (kc_simpleNext _) fun _ => KC.bind' (kc_into _ _) fun _ => KC.bind' (kc_past _ _ _) fun _ =>
      KC.bind' (ihv _) fun _ => KC.bind' (kc_past _ _ _) fun _ => KC.bind' (ihq _) fun _ => kc_copy _ _
  | _ =>
    intro goal
    unfold run
    exact KC.fail

/-! ## The end of `+comp` -/

theorem kc_needOrdAllocRegs : ∀ (ord : NeedOrd), KC (needOrdAllocRegs ord : CM Map Need)
  | NeedOrd.none => by unfold needOrdAllocRegs; kc
  | NeedOrd.this => by unfold needOrdAllocRegs; kc
  | NeedOrd.pair p q => by
    unfold needOrdAllocRegs
    exact KC.bind' (kc_needOrdAllocRegs p) fun _ => KC.bind' (kc_needOrdAllocRegs q) fun _ => by kc
  | NeedOrd.both p q => by
    unfold needOrdAllocRegs
    exact KC.bind' KC.re' fun _ =>
      KC.bind' (kc_needOrdAllocRegs p) fun _ => KC.bind' (kc_needOrdAllocRegs q) fun _ => by kc

theorem kc_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, KC (kh x a)) (ht : ∀ x a, KC (kt x a)) (ops : List Pole) :
    KC (kernBoth r d kh kt ops) := by
  unfold kernBoth
  exact KC.bind' KC.re' fun _ => KC.bind' (ht _ _) fun _ => KC.bind' KC.re' fun _ =>
    KC.bind' (hh _ _) fun _ => by kc

theorem kc_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), KC (kernLoop r ned ops : CM Map (List Pole))
  | _, Need.none, _ => by unfold kernLoop; kc
  | _, Need.this _, _ => by unfold kernLoop; kc
  | _, Need.pair p q, _ => by
    unfold kernLoop
    exact KC.bind' KC.re' fun _ => kc_kernBoth _ _ (fun x a => kc_kernLoop x p a) (fun x a => kc_kernLoop x q a) _
  | _, Need.both _ h t, _ => by
    unfold kernLoop
    exact kc_kernBoth _ _ (fun x a => kc_kernLoop x h a) (fun x a => kc_kernLoop x t a) _

theorem kc_sureLoop (o : Nat) : ∀ (ned tgt : Need), KC (sureLoop o ned tgt : CM Map Unit)
  | Need.none, _ => by unfold sureLoop; kc
  | Need.this _, _ => by
    unfold sureLoop; exact KC.bind' (kc_kernLoop _ _ _) fun _ => KC.addOps' _ _
  | Need.pair p q, tgt => by
    unfold sureLoop
    cases tgt
    · exact KC.bind' (kc_sureLoop o p _) fun _ => kc_sureLoop o q _
    · exact KC.crash
    · exact KC.crash
    · exact KC.pure' _
  | Need.both _ h t, tgt => by
    unfold sureLoop
    cases tgt
    · exact KC.bind' (kc_sureLoop o h _) fun _ => kc_sureLoop o t _
    · exact KC.ite' _ KC.crash (KC.bind' (KC.addOps' _ _) fun _ =>
        KC.bind' (kc_sureLoop o h _) fun _ => kc_sureLoop o t _)
    · exact KC.ite' _ KC.crash (KC.addOps' _ _)
    · exact KC.pure' _

theorem kc_coerceLazy (ned : Need) (o : Nat) (laz : Sure S) (less : Cape) :
    KC (coerceLazy ned o laz less : CM Map Unit) := by
  unfold coerceLazy
  exact KC.bind' (KC.lift' _) fun _ => KC.bind' (kc_sureRequireLook _) fun _ => kc_sureLoop _ _ _

mutual
theorem kc_coerceLazyL (ned : Need) (less : Cape) : ∀ (o : Nat) (l : Lazy S),
    KC (coerceLazyL ned less o l : CM Map Unit)
  | o, mk s f b => by
    unfold coerceLazyL
    exact KC.bind' (kc_coerceLazy _ _ _ _) fun _ => KC.ite' _ (KC.pure' _)
      (KC.bind' (kc_coerceBonds ned less b) fun _ => kc_coerceForks ned less f)

theorem kc_coerceBonds (ned : Need) (less : Cape) : ∀ (l : List (Nat × Lazy S)),
    KC (coerceBonds ned less l : CM Map Unit)
  | [] => by unfold coerceBonds; kc
  | (o, l) :: rest => by
    unfold coerceBonds
    exact KC.bind' (kc_coerceLazyL ned less o l) fun _ => kc_coerceBonds ned less rest

theorem kc_coerceForks (ned : Need) (less : Cape) : ∀ (l : List (ForkE S)),
    KC (coerceForks ned less l : CM Map Unit)
  | [] => by unfold coerceForks; kc
  | ((oy, y), (on, n)) :: rest => by
    unfold coerceForks
    exact KC.bind' (kc_coerceLazyL ned less oy y) fun _ =>
      KC.bind' (kc_coerceLazyL ned less on n) fun _ => kc_coerceForks ned less rest
end

end Comp
end SkaModel
end Formalization
