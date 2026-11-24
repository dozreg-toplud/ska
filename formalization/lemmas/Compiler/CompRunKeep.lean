import lemmas.Compiler.CompRunCopyRegs

/-!
# The counters only grow and the mode stays

`KM m`: the computation `m` of `+comp` does not lower the register counter
`re` nor the label counter `bo`, and leaves `drop` as it found it.  The
primitives (`re`, `oo`, `emit`, `addOps`, `setTag`, `+proxy`, ...) meet it,
binds and branches keep it (the tactic `km`, as `kd` of
`Ska/CompDropKeep.lean`), and so do the helpers of `+run` on lazy needs:
`+walk-lazy` (with a gate that meets it), `+kern`, `+kerf`, `+mede`,
`+collapse-lazy-atom`, `+split`, `+into`, `+copy`, `+past`,
`+simple-next`, `+bomb`, `+forl`.  `GRes` asks the counters to grow; this
file gives it for every step between the runs of the parts.  Every block
with a tag keeps it (`TagsUp`): only `+set-tag` writes `tags`, and it puts.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- Every block with a tag in `g` has one in `g'`. -/
def TagsUp (g g' : Gen Map) : Prop := ∀ o, (HoonMap.get g.tags o).isSome = true → (HoonMap.get g'.tags o).isSome = true

theorem TagsUp.refl (g : Gen Map) : TagsUp g g := fun _ h => h

theorem TagsUp.trans {g0 g1 g2 : Gen Map} (a : TagsUp g0 g1) (b : TagsUp g1 g2) : TagsUp g0 g2 :=
  fun o h => b o (a o h)

/-- `m` does not lower the counters, keeps `drop`, and keeps every tag. -/
structure KM {α : Type} (m : CM Map α) : Prop where
  keep : ∀ g x g', m g = some (x, g') → g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = g.drop
  tags : ∀ g x g', m g = some (x, g') → TagsUp g g'

namespace KM

theorem pure' {α : Type} (a : α) : KM (pure a : CM Map α) := by
  constructor
  · intro g x g' h; cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  · intro g x g' h; cases h; exact TagsUp.refl _

theorem bind' {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : KM m) (hf : ∀ a, KM (f a)) :
    KM (m >>= f) := by
  constructor
  · intro g x g' h
    rw [bind_apply] at h
    obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a1, b1, c1⟩ := hm.keep g a g1 h1
    obtain ⟨a2, b2, c2⟩ := (hf a).keep g1 x g' h2
    exact ⟨Nat.le_trans a1 a2, Nat.le_trans b1 b2, c2.trans c1⟩
  · intro g x g' h
    rw [bind_apply] at h
    obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (hm.tags g a g1 h1).trans ((hf a).tags g1 x g' h2)

theorem fail {α : Type} : KM (fun _ => Option.none : CM Map α) := by
  constructor <;> (intro g x g' h; cases h)

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KM a) (hb : KM b) :
    KM (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A step that keeps the tags and the mode and moves the counters up. -/
theorem of_gen {α : Type} {m : CM Map α}
    (h : ∀ g x g', m g = some (x, g') → g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = g.drop ∧ g'.tags = g.tags) :
    KM m :=
  ⟨fun g x g' e => let k := h g x g' e; ⟨k.1, k.2.1, k.2.2.1⟩,
   fun g x g' e o ho => by rw [(h g x g' e).2.2.2]; exact ho⟩

theorem re' : KM (re : CM Map Nat) := of_gen fun g x g' h => by cases h; exact ⟨Nat.le_succ _, Nat.le_refl _, rfl, rfl⟩
theorem oo' : KM (oo : CM Map Nat) := of_gen fun g x g' h => by cases h; exact ⟨Nat.le_refl _, Nat.le_succ _, rfl, rfl⟩
theorem freshId' : KM (freshId : CM Map Nat) :=
  of_gen fun g x g' h => by cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
theorem idM' : KM (idM : CM Map Nat) := of_gen fun g x g' h => by cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
theorem get' : KM (get : CM Map (Gen Map)) :=
  of_gen fun g x g' h => by cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

theorem setTag' (o : Nat) (region : List Nat) : KM (setTag o region : CM Map Unit) := by
  constructor
  · intro g x g' h; cases h; split <;> exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  · intro g x g' h; cases h
    split
    · exact TagsUp.refl _
    · intro o' h'
      simp only [HoonMap.get_put]
      split
      · rfl
      · exact h'

theorem emir' (o : Nat) (b : Blob) : KM (emir o b : CM Map Unit) :=
  of_gen fun g x g' h => by cases h; split <;> exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

theorem emit' (b : Blob) : KM (emit b : CM Map Nat) :=
  of_gen fun g x g' h => by rw [emit_apply] at h; cases h; exact ⟨Nat.le_refl _, Nat.le_succ _, rfl, rfl⟩

theorem addOps' (o : Nat) (ops : List Pole) : KM (addOps o ops : CM Map Unit) :=
  of_gen fun g x g' h => by
    unfold addOps at h
    split at h
    · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
    · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

theorem liftO' {α : Type} (x : Option α) : KM (liftO x : CM Map α) :=
  of_gen fun g a g' h => by
    obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

theorem proxy' (r o : Nat) : KM (proxy r o : CM Map Nat) :=
  of_gen fun g x g' h => by
    unfold proxy at h
    simp only at h
    split at h
    · cases h; exact ⟨Nat.le_succ _, Nat.le_refl _, rfl, rfl⟩
    · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; exact ⟨Nat.le_succ _, Nat.le_refl _, rfl, rfl⟩

theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, KM acc → KM (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), KM acc → KM (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end KM

/-- One step of the tactic `km`. -/
macro "km_step" : tactic => `(tactic| first
  | exact KM.pure' _ | exact KM.re' | exact KM.oo' | exact KM.freshId' | exact KM.idM' | exact KM.get'
  | exact KM.emit' _ | exact KM.addOps' _ _ | exact KM.setTag' _ _ | exact KM.emir' _ _
  | exact KM.fail | exact KM.liftO' _ | exact KM.proxy' _ _
  | apply KM.bind' | apply KM.ite' | split | intro _)

/-- Prove `KM` of a computation built from the primitives. -/
macro "km" : tactic => `(tactic| repeat km_step)

/-! ## The arms on sure needs -/

theorem km_must (ned : Need) : KM (must ned : CM Map (Nat × Need)) := by unfold must; km

theorem km_splitNeed (ned : Need) (o : Nat) : KM (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · km
  · km
  · km
  · exact KM.bind' (km_must _) fun _ => KM.bind' (km_must _) fun _ => by km

theorem km_splitSure (sur : Sure S) (o : Nat) : KM (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  all_goals
    intro g x g' h
    unfold splitSure at h
    obtain ⟨⟨lh, lt⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
  · exact (km_splitNeed _ _).keep g _ g1 h1
  · exact (km_splitNeed _ _).tags g _ g1 h1

theorem km_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    KM (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops
    rw [intoLoop]
    split
    · km
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _
      · exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => ih _ hl _ _ _
      · exact ih _ hl _ _ _
      · exact KM.bind' (km_must _) fun _ => KM.bind' (km_must _) fun _ => ih _ hl _ _ _

theorem km_intoNeed (axe : Nat) (ned : Need) (o : Nat) : KM (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KM.ite' _ KM.fail (KM.ite' _ (KM.pure' _) (km_intoLoop _ _ _ _ _))

theorem km_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : KM (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  all_goals
    intro g x g' h
    unfold intoSure at h
    obtain ⟨⟨ld, lr⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨_, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
  · exact (km_intoNeed _ _ _).keep g _ g1 h1
  · exact (km_intoNeed _ _ _).tags g _ g1 h1

theorem km_copyNeed : ∀ (a b : Need) (ops : List Pole), KM (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _ => by rw [copyNeed]; km
  | Need.this _, Need.none, _ => by rw [copyNeed] <;> first | exact KM.pure' _ | nofun
  | Need.pair _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KM.pure' _ | nofun
  | Need.both _ _ _, Need.none, _ => by rw [copyNeed] <;> first | exact KM.pure' _ | nofun
  | Need.this _, Need.this _, _ => by rw [copyNeed]; km
  | Need.this _, Need.both _ _ _, _ => by rw [copyNeed]; km
  | Need.this _, Need.pair _ _, _ => by rw [copyNeed]; km
  | Need.both _ _ _, Need.this _, _ => by rw [copyNeed]; km
  | Need.pair _ _, Need.this _, _ => by rw [copyNeed]; km
  | Need.both _ hl tl, Need.both _ hr tr, _ => by
    rw [copyNeed]
    exact KM.bind' (km_copyNeed hl hr _) fun _ => KM.bind' (km_copyNeed tl tr _) fun _ => by km
  | Need.both _ hl tl, Need.pair p q, _ => by
    rw [copyNeed]
    exact KM.bind' KM.re' fun _ =>
      KM.bind' (km_copyNeed hl p _) fun _ => KM.bind' (km_copyNeed tl q _) fun _ => by km
  | Need.pair pl ql, Need.pair pr qr, _ => by
    rw [copyNeed]
    exact KM.bind' (km_copyNeed pl pr _) fun _ => KM.bind' (km_copyNeed ql qr _) fun _ => by km
  | Need.pair pl ql, Need.both _ h t, _ => by
    rw [copyNeed]
    exact KM.bind' (km_copyNeed pl h _) fun _ => KM.bind' (km_copyNeed ql t _) fun _ => by km

theorem km_lookPath : ∀ (axe : Nat) (ned : Need), KM (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> km
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact KM.bind' (ih _ hl _) fun _ => by km
      · exact KM.bind' (ih _ hl _) fun _ => by km

theorem km_sureRequireLook (sur : Sure S) : KM (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine KM.foldl' _ (fun acc b h => KM.bind' h fun ned => ?_) _ _ (KM.pure' _)
  exact KM.ite' _ (KM.pure' _) (KM.ite' _ KM.fail (km_lookPath _ _))

theorem km_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : KM (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed; split <;> km

theorem km_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), KM (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; km
  | _, Need.this _ => by rw [medeLoop]; km
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact km_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact KM.bind' (km_medeLoop o a p) fun _ => km_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact km_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact KM.bind' (KM.addOps' _ _) fun _ => KM.bind' (km_medeLoop o a h) fun _ => km_medeLoop o b t

theorem km_forl (r o : Nat) : KM (forl r o : CM Map (Nat × Nat)) := by unfold forl; km

theorem km_doneBlocks : KM (doneBlocks : CM Map (Nat × Nat)) := by unfold doneBlocks; km

theorem km_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, KM (kh x a)) (ht : ∀ x a, KM (kt x a)) (ops : List Pole) :
    KM (kernBoth r d kh kt ops : CM Map (List Pole)) := by
  unfold kernBoth
  exact KM.bind' KM.re' fun _ => KM.bind' (ht _ _) fun _ => KM.bind' KM.re' fun _ => KM.bind' (hh _ _) fun _ =>
    KM.ite' _ KM.fail (KM.pure' _)

theorem km_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), KM (kernLoop r ned ops : CM Map (List Pole))
  | _, Need.none, _ => by rw [kernLoop]; km
  | _, Need.this _, _ => by rw [kernLoop]; exact KM.ite' _ KM.fail (KM.pure' _)
  | r, Need.pair p q, ops => by
    rw [kernLoop]
    exact KM.bind' KM.re' fun _ => km_kernBoth _ _ (fun x a => km_kernLoop x p a) (fun x a => km_kernLoop x q a) _
  | r, Need.both d h t, ops => by
    rw [kernLoop]
    exact km_kernBoth _ _ (fun x a => km_kernLoop x h a) (fun x a => km_kernLoop x t a) _

/-! ## The arms on lazy needs -/

mutual
theorem km_walkLazy {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, KM (f o s)) :
    ∀ (o : Nat) (laz : Lazy S), KM (walkLazy f o laz : CM Map Unit)
  | o, mk s fk bd => by
    rw [walkLazy]
    exact KM.bind' (hf o s) fun _ => KM.ite' _ (KM.pure' _)
      (KM.bind' (km_walkForks hf fk) fun _ => km_walkBonds hf bd)

theorem km_walkForks {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, KM (f o s)) :
    ∀ (fk : List (ForkE S)), KM (walkForks f fk : CM Map Unit)
  | [] => by rw [walkForks]; exact KM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [walkForks]
    exact KM.bind' (km_walkLazy hf oy y) fun _ => KM.bind' (km_walkLazy hf on n) fun _ => km_walkForks hf rest

theorem km_walkBonds {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, KM (f o s)) :
    ∀ (bd : List (Nat × Lazy S)), KM (walkBonds f bd : CM Map Unit)
  | [] => by rw [walkBonds]; exact KM.pure' _
  | (o, l) :: rest => by
    rw [walkBonds]
    exact KM.bind' (km_walkLazy hf o l) fun _ => km_walkBonds hf rest
end

theorem km_kern (o : Nat) (laz : Lazy S) : KM (kern o laz : CM Map Nat) := by
  unfold kern
  refine KM.bind' KM.re' fun r => KM.bind' KM.get' fun g => KM.ite' _ (KM.pure' _)
    (KM.bind' (km_walkLazy (fun oLaz sur => ?_) o laz) fun _ => KM.pure' _)
  refine KM.bind' (km_sureRequireLook _) fun ned => KM.ite' _ (KM.pure' _) ?_
  refine KM.bind' (KM.ite' _ (KM.pure' _) (KM.proxy' _ _)) fun src => KM.ite' _ KM.fail ?_
  exact KM.bind' (km_kernLoop _ _ _) fun _ => KM.addOps' _ _

theorem km_kerf (nex : NextL S) : KM (kerf nex : CM Map (Nat × Nat)) := by
  unfold kerf
  exact KM.bind' (KM.emit' _) fun _ => KM.bind' (km_kern _ _) fun _ => KM.pure' _

theorem km_medeL (th : Jmp) (som : Noun) (laz : Lazy S) : KM (medeL th som laz : CM Map Nat) := by
  unfold medeL
  refine KM.bind' (KM.emit' _) fun o => KM.bind' KM.get' fun g => KM.ite' _ (KM.pure' _) ?_
  exact KM.bind' (km_walkLazy (fun o sur => KM.bind' (km_sureRequireLook _) fun _ => km_medeLoop _ _ _) _ _)
    fun _ => KM.pure' _

theorem km_collapseGate (r o oLaz : Nat) (sur : Sure S) : KM (collapseGate r o oLaz sur : CM Map Unit) := by
  unfold collapseGate
  refine KM.bind' (km_sureRequireLook _) fun ned => ?_
  split
  · exact KM.pure' _
  · exact KM.ite' _ (KM.pure' _) (KM.bind' (KM.ite' _ (KM.pure' _) (KM.proxy' _ _)) fun _ => KM.addOps' _ _)
  · exact KM.bind' (KM.ite' _ (KM.pure' _) (KM.proxy' _ _)) fun _ => km_crashNeed _ _ _

theorem km_collapseLazyAtomL (nex : NextL S) : KM (collapseLazyAtomL nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtomL
  refine KM.ite' _ KM.fail (KM.ite' _ (KM.pure' _) (KM.bind' (km_sureRequireLook _) fun ned => ?_))
  refine KM.bind' (by split <;> km) fun p => ?_
  refine KM.bind' KM.get' fun _ => KM.ite' _ (KM.pure' _) ?_
  exact KM.bind' (km_walkLazy (fun o s => km_collapseGate _ _ o s) _ _) fun _ => KM.pure' _

mutual
theorem km_splitLoop : ∀ (laz : Lazy S) (o : Nat), KM (splitLoop laz o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [splitLoop]
    refine KM.bind' (km_splitSure _ _) fun x => ?_
    obtain ⟨sh, st⟩ := x
    exact KM.ite' _ (KM.pure' _) (KM.bind' (km_splitForks f) fun y => KM.bind' (km_splitBonds b) fun z => KM.pure' _)

theorem km_splitForks : ∀ (f : List (ForkE S)), KM (splitForks f : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [splitForks]; exact KM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks]
    exact KM.bind' (km_splitLoop y oy) fun _ => KM.bind' (km_splitLoop n on) fun _ =>
      KM.bind' (km_splitForks rest) fun _ => KM.pure' _

theorem km_splitBonds : ∀ (b : List (Nat × Lazy S)), KM (splitBonds b : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [splitBonds]; exact KM.pure' _
  | (o, l) :: rest => by
    rw [splitBonds]
    exact KM.bind' (km_splitLoop l o) fun _ => KM.bind' (km_splitBonds rest) fun _ => KM.pure' _
end

theorem km_splitL (nex : NextL S) : KM (splitL nex : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold splitL
  exact KM.bind' (KM.emit' _) fun _ => KM.bind' (km_splitLoop _ _) fun _ => KM.pure' _

mutual
theorem km_intoLoopL (axe : Nat) : ∀ (laz : Lazy S) (o : Nat), KM (intoLoopL axe laz o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [intoLoopL]
    refine KM.bind' (km_intoSure _ _ _) fun x => ?_
    obtain ⟨sh, st⟩ := x
    exact KM.ite' _ (KM.pure' _) (KM.bind' (km_intoForks axe f) fun y => KM.bind' (km_intoBonds axe b) fun z => KM.pure' _)

theorem km_intoForks (axe : Nat) : ∀ (f : List (ForkE S)), KM (intoForks axe f : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [intoForks]; exact KM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [intoForks]
    exact KM.bind' (km_intoLoopL axe y oy) fun _ => KM.bind' (km_intoLoopL axe n on) fun _ =>
      KM.bind' (km_intoForks axe rest) fun _ => KM.pure' _

theorem km_intoBonds (axe : Nat) : ∀ (b : List (Nat × Lazy S)),
    KM (intoBonds axe b : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [intoBonds]; exact KM.pure' _
  | (o, l) :: rest => by
    rw [intoBonds]
    exact KM.bind' (km_intoLoopL axe l o) fun _ => KM.bind' (km_intoBonds axe rest) fun _ => KM.pure' _
end

theorem km_intoL (nex : NextL S) (axe : Nat) : KM (intoL nex axe : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold intoL
  exact KM.bind' (KM.emit' _) fun _ => KM.bind' (km_intoLoopL _ _ _) fun _ => KM.pure' _

mutual
theorem km_copyLazyL (o : Nat) : ∀ (a b : Lazy S), KM (copyLazyL (Map := Map) o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine KM.bind' (km_copyNeed _ _ _) fun a => ?_
    rcases a with ⟨ned, ops⟩
    refine KM.bind' (KM.addOps' _ _) fun _ => KM.bind' ?_ fun _ => KM.bind' ?_ fun _ => KM.pure' _
    · split
      · exact KM.pure' _
      · split
        · exact KM.pure' _
        · exact KM.bind' (km_mergeForks _ f1) fun _ => KM.pure' _
    · split
      · exact KM.pure' _
      · split
        · exact KM.pure' _
        · exact KM.bind' (km_mergeBonds _ b1) fun _ => KM.pure' _

theorem km_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    KM (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact KM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine KM.bind' ?_ fun _ => KM.bind' (km_mergeForks idx rest) fun _ => KM.pure' _
    split
    · exact KM.pure' _
    · split
      · exact KM.bind' (km_copyLazyL oy y _) fun _ => KM.bind' (km_copyLazyL on n _) fun _ => KM.pure' _
      · exact KM.fail

theorem km_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    KM (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact KM.pure' _
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine KM.bind' ?_ fun _ => KM.bind' (km_mergeBonds idx rest) fun _ => KM.pure' _
    split
    · exact KM.pure' _
    · exact KM.bind' (km_copyLazyL ob l _) fun _ => KM.pure' _
end

theorem km_copyL (first : NextL S) (second : Lazy S) : KM (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  exact KM.bind' (KM.emit' _) fun _ => KM.bind' (km_copyLazyL _ _ _) fun _ => KM.pure' _

theorem km_pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    KM (pastL cod nex nom region : CM Map (NextL S)) := by
  unfold pastL; km

theorem km_simpleNextL (goal : CGoalL S) : KM (simpleNextL goal : CM Map (NextL S)) := by
  unfold simpleNextL; km

theorem km_bombL (miss : Option Nat) : KM (bombL miss : CM Map (NextL S)) := by unfold bombL; km

end Compiler
end Formalization
