import lemmas.Ska.RawInvAT
import lemmas.Ska.CompSimBody

/-!
# Steps that make no label: `QM`

README Gaps 14 (b), track D.  `QM m`: every run of `m` is `Quiet` (track C,
`CompDown.lean`: it grows the state and makes no label, so the blocks keep
their parameters and ends and no block is added).  Kept by `pure`, `bind`,
`if`, `re`, `+add-ops`, `+set-tag`, `+copy-tag`, `+proxy`, `get`,
`getCond`, `liftO`.  The arms are the text of `CompSimBody.lean` (`SimM`)
with `QM` for `SimM`: the needs (`+must` .. `+kern-need`), the walks over
lazy needs (`splitLoop`, `intoLoopL`, `copyLazyL` with the merge of forks
and bonds, `walkLazy`), the gate of `+collapse-lazy-atom`, `+kern` and
`+lazy-shut`.  None of them emits a block: the arms that do (`+split`,
`+copy`, `+kerf`, ...) are in `RawInvCAT.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Every run of `m` makes no label.**  A structure, so that `intro` does
not open it. -/
structure QM {α : Type} (m : CM Map α) : Prop where
  q : ∀ g x g', m g = some (x, g') → Quiet g g'

/-- A step that changes neither the blocks nor `bo` nor `drop`. -/
theorem quiet_same {g g' : Gen Map} (hb : g'.blocks = g.blocks) (hbo : g'.bo = g.bo) (hd : g'.drop = g.drop) :
    Quiet g g' :=
  ⟨⟨Nat.le_of_eq hbo.symm, hd, fun _ b _ h => ⟨b, by rw [hb]; exact h, rfl, rfl⟩,
    fun _ b h => Or.inl ⟨b, by rw [← hb]; exact h, rfl, rfl⟩⟩, hbo⟩

namespace QM

theorem pure' {α : Type} (a : α) : QM (pure a : CM Map α) := by
  constructor; intro g x g' h; cases h; exact Quiet.refl g

theorem bind' {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : QM m) (hf : ∀ a, QM (f a)) :
    QM (m >>= f) := by
  constructor
  intro g x g' h
  rw [bind_apply] at h
  obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact (hm.q g a g1 h1).trans ((hf a).q g1 x g' h2)

theorem fail {α : Type} : QM (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' h; cases h

theorem crash {α : Type} : QM (crashM : CM Map α) := fail

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CM Map α} (ha : QM a) (hb : QM b) :
    QM (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem re' : QM (re : CM Map Nat) := by
  constructor; intro g x g' h; rw [re_apply] at h; cases h; exact quiet_re g

theorem freshId' : QM (freshId : CM Map Nat) := by
  constructor; intro g x g' h; cases h; exact quiet_same rfl rfl rfl

theorem idM' : QM (idM : CM Map Nat) := by
  constructor; intro g x g' h; cases h; exact quiet_same rfl rfl rfl

theorem get' : QM (get : CM Map (Gen Map)) := by
  constructor; intro g x g' h; rw [get_apply] at h; cases h; exact Quiet.refl g

theorem getCond' : QM (getCond : CM Map (Map (Nat × List Nat))) := by
  constructor; intro g x g' h; cases h; exact Quiet.refl g

theorem addOps' (o : Nat) (ops : List Pole) : QM (addOps o ops : CM Map Unit) := by
  constructor; intro g x g' h; exact quiet_addOps h

theorem setTag' (o : Nat) (region : List Nat) : QM (setTag o region : CM Map Unit) := by
  constructor; intro g x g' h; cases h
  split
  · exact Quiet.refl g
  · exact quiet_same rfl rfl rfl

theorem copyTag' (frm : Nat) (tos : List Nat) : QM (copyTag frm tos : CM Map Unit) := by
  constructor
  intro g x g' h
  unfold copyTag at h
  split at h
  · cases h; exact Quiet.refl g
  · obtain ⟨rg, _, e⟩ := Option.map_eq_some_iff.mp h
    cases e; exact quiet_same rfl rfl rfl

theorem proxy' (r o : Nat) : QM (proxy r o : CM Map Nat) := by
  constructor
  intro g x g' h
  unfold proxy at h
  simp only at h
  split at h
  · cases h; exact quiet_same rfl rfl rfl
  · obtain ⟨tag, _, e⟩ := Option.map_eq_some_iff.mp h
    cases e; exact quiet_same rfl rfl rfl

theorem liftO' {α : Type} (x : Option α) : QM (liftO x : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
  cases e; exact Quiet.refl g

theorem lift' {α : Type} (x : Option α) : QM ((fun g => x.map fun a => (a, g)) : CM Map α) := by
  constructor
  intro g a g' h
  obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
  cases e; exact Quiet.refl g

theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, QM acc → QM (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), QM acc → QM (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end QM

/-- One step of the tactic `qmb`. -/
macro "qmb_step" : tactic => `(tactic| first
  | exact QM.pure' _ | exact QM.re' | exact QM.freshId' | exact QM.idM' | exact QM.get'
  | exact QM.getCond' | exact QM.addOps' _ _ | exact QM.setTag' _ _
  | exact QM.copyTag' _ _ | exact QM.proxy' _ _
  | exact QM.fail | exact QM.crash | exact QM.liftO' _ | exact QM.lift' _
  | apply QM.bind' | apply QM.ite' | split | intro _)

/-- Prove `QM` of a computation built from the primitives. -/
macro "qmb" : tactic => `(tactic| repeat qmb_step)

/-! ## The arms -/

theorem qm_must (ned : Need) : QM (must ned : CM Map (Nat × Need)) := by unfold must; qmb

theorem qm_splitNeed (ned : Need) (o : Nat) : QM (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · qmb
  · qmb
  · qmb
  · exact QM.bind' (qm_must _) fun _ => QM.bind' (qm_must _) fun _ => by qmb

theorem qm_splitSure (sur : Sure S) (o : Nat) : QM (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g1 h
  unfold splitSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact (qm_splitNeed sur.ned o).q g y g2 h1

theorem qm_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    QM (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops
    rw [intoLoop]
    split
    · qmb
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _
      · exact QM.bind' QM.re' fun _ => QM.bind' QM.re' fun _ => ih _ hl _ _ _
      · exact ih _ hl _ _ _
      · exact QM.bind' (qm_must _) fun _ => QM.bind' (qm_must _) fun _ => ih _ hl _ _ _

theorem qm_intoNeed (axe : Nat) (ned : Need) (o : Nat) : QM (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact QM.ite' _ QM.fail (QM.ite' _ (QM.pure' _) (qm_intoLoop _ _ _ _ _))

theorem qm_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : QM (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g1 h
  unfold intoSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact (qm_intoNeed axe sur.ned o).q g y g2 h1

theorem qm_copyNeed : ∀ (a b : Need) (ops : List Pole), QM (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _ => by rw [copyNeed]; qmb
  | Need.this _, Need.none, _ => by rw [copyNeed] <;> first | exact QM.pure' _ | nofun
  | Need.pair _ _, Need.none, _ => by rw [copyNeed] <;> first | exact QM.pure' _ | nofun
  | Need.both _ _ _, Need.none, _ => by rw [copyNeed] <;> first | exact QM.pure' _ | nofun
  | Need.this _, Need.this _, _ => by rw [copyNeed]; qmb
  | Need.this _, Need.both _ _ _, _ => by rw [copyNeed]; qmb
  | Need.this _, Need.pair _ _, _ => by rw [copyNeed]; qmb
  | Need.both _ _ _, Need.this _, _ => by rw [copyNeed]; qmb
  | Need.pair _ _, Need.this _, _ => by rw [copyNeed]; qmb
  | Need.both _ hl tl, Need.both _ hr tr, _ => by
    rw [copyNeed]
    exact QM.bind' (qm_copyNeed hl hr _) fun _ => QM.bind' (qm_copyNeed tl tr _) fun _ => by qmb
  | Need.both _ hl tl, Need.pair p q, _ => by
    rw [copyNeed]
    exact QM.bind' QM.re' fun _ =>
      QM.bind' (qm_copyNeed hl p _) fun _ => QM.bind' (qm_copyNeed tl q _) fun _ => by qmb
  | Need.pair pl ql, Need.pair pr qr, _ => by
    rw [copyNeed]
    exact QM.bind' (qm_copyNeed pl pr _) fun _ => QM.bind' (qm_copyNeed ql qr _) fun _ => by qmb
  | Need.pair pl ql, Need.both _ h t, _ => by
    rw [copyNeed]
    exact QM.bind' (qm_copyNeed pl h _) fun _ => QM.bind' (qm_copyNeed ql t _) fun _ => by qmb

theorem qm_lookPath : ∀ (axe : Nat) (ned : Need), QM (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> qmb
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact QM.bind' (ih _ hl _) fun _ => by qmb
      · exact QM.bind' (ih _ hl _) fun _ => by qmb

theorem qm_sureRequireLook (sur : Sure S) : QM (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine QM.foldl' _ (fun acc b h => QM.bind' h fun ned => ?_) _ _ (QM.pure' _)
  exact QM.ite' _ (QM.pure' _) (QM.ite' _ QM.fail (qm_lookPath _ _))

theorem qm_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : QM (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed; split <;> qmb

theorem qm_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), QM (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; qmb
  | _, Need.this _ => by rw [medeLoop]; qmb
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact qm_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact QM.bind' (qm_medeLoop o a p) fun _ => qm_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact qm_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact QM.bind' (QM.addOps' _ _) fun _ => QM.bind' (qm_medeLoop o a h) fun _ => qm_medeLoop o b t

theorem qm_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, QM (kh x a)) (ht : ∀ x a, QM (kt x a)) (ops : List Pole) :
    QM (kernBoth r d kh kt ops) := by
  unfold kernBoth
  exact QM.bind' QM.re' fun _ => QM.bind' (ht _ _) fun _ => QM.bind' QM.re' fun _ =>
    QM.bind' (hh _ _) fun _ => by qmb

theorem qm_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), QM (kernLoop r ned ops : CM Map (List Pole))
  | _, Need.none, _ => by unfold kernLoop; qmb
  | _, Need.this _, _ => by unfold kernLoop; qmb
  | _, Need.pair p q, _ => by
    unfold kernLoop
    exact QM.bind' QM.re' fun _ =>
      qm_kernBoth _ _ (fun x a => qm_kernLoop x p a) (fun x a => qm_kernLoop x q a) _
  | _, Need.both _ h t, _ => by
    unfold kernLoop
    exact qm_kernBoth _ _ (fun x a => qm_kernLoop x h a) (fun x a => qm_kernLoop x t a) _

mutual
theorem qm_splitLoop : ∀ (l : Lazy S) (o : Nat), QM (splitLoop l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [splitLoop]
    refine QM.bind' (qm_splitSure s o) fun a => ?_
    rcases a with ⟨sh, st⟩
    refine QM.ite' _ (QM.pure' _) (QM.bind' (qm_splitForks f) fun x => ?_)
    rcases x with ⟨fh, ft⟩
    refine QM.bind' (qm_splitBonds b) fun y => ?_
    rcases y with ⟨bh, bt⟩
    exact QM.pure' _

theorem qm_splitForks : ∀ (l : List (ForkE S)), QM (splitForks l : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [splitForks]; exact QM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks]
    refine QM.bind' (qm_splitLoop y oy) fun a => ?_
    rcases a with ⟨yh, yt⟩
    refine QM.bind' (qm_splitLoop n on) fun b => ?_
    rcases b with ⟨nh, nt⟩
    refine QM.bind' (qm_splitForks rest) fun c => ?_
    rcases c with ⟨rh, rt⟩
    exact QM.pure' _

theorem qm_splitBonds : ∀ (l : List (Nat × Lazy S)),
    QM (splitBonds l : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [splitBonds]; exact QM.pure' _
  | (o, l) :: rest => by
    rw [splitBonds]
    refine QM.bind' (qm_splitLoop l o) fun a => ?_
    rcases a with ⟨lh, lt⟩
    refine QM.bind' (qm_splitBonds rest) fun c => ?_
    rcases c with ⟨rh, rt⟩
    exact QM.pure' _
end

mutual
theorem qm_intoLoopL (axe : Nat) : ∀ (l : Lazy S) (o : Nat), QM (intoLoopL axe l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [intoLoopL]
    refine QM.bind' (qm_intoSure axe s o) fun a => ?_
    rcases a with ⟨sd, sr⟩
    refine QM.ite' _ (QM.pure' _) (QM.bind' (qm_intoForks axe f) fun x => ?_)
    rcases x with ⟨fd, fr⟩
    refine QM.bind' (qm_intoBonds axe b) fun y => ?_
    rcases y with ⟨bd', br⟩
    exact QM.pure' _

theorem qm_intoForks (axe : Nat) : ∀ (l : List (ForkE S)),
    QM (intoForks axe l : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [intoForks]; exact QM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [intoForks]
    refine QM.bind' (qm_intoLoopL axe y oy) fun a => ?_
    rcases a with ⟨yd, yr⟩
    refine QM.bind' (qm_intoLoopL axe n on) fun b => ?_
    rcases b with ⟨nd, nr⟩
    refine QM.bind' (qm_intoForks axe rest) fun c => ?_
    rcases c with ⟨rd, rr⟩
    exact QM.pure' _

theorem qm_intoBonds (axe : Nat) : ∀ (l : List (Nat × Lazy S)),
    QM (intoBonds axe l : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [intoBonds]; exact QM.pure' _
  | (o, l) :: rest => by
    rw [intoBonds]
    refine QM.bind' (qm_intoLoopL axe l o) fun a => ?_
    rcases a with ⟨ld, lr⟩
    refine QM.bind' (qm_intoBonds axe rest) fun c => ?_
    rcases c with ⟨rd, rr⟩
    exact QM.pure' _
end

mutual
theorem qm_copyLazyL (o : Nat) : ∀ (a b : Lazy S), QM (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine QM.bind' (qm_copyNeed _ _ _) fun a => ?_
    rcases a with ⟨ned, ops⟩
    refine QM.bind' (QM.addOps' _ _) fun _ => QM.bind' ?_ fun _ => QM.bind' ?_ fun _ => QM.pure' _
    · split
      · exact QM.pure' _
      · split
        · exact QM.pure' _
        · exact QM.bind' (qm_mergeForks _ f1) fun _ => QM.pure' _
    · split
      · exact QM.pure' _
      · split
        · exact QM.pure' _
        · exact QM.bind' (qm_mergeBonds _ b1) fun _ => QM.pure' _

theorem qm_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    QM (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact QM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine QM.bind' ?_ fun _ => QM.bind' (qm_mergeForks idx rest) fun _ => QM.pure' _
    split
    · exact QM.pure' _
    · split
      · exact QM.bind' (qm_copyLazyL oy y _) fun _ => QM.bind' (qm_copyLazyL on n _) fun _ => QM.pure' _
      · exact QM.fail

theorem qm_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    QM (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact QM.pure' _
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine QM.bind' ?_ fun _ => QM.bind' (qm_mergeBonds idx rest) fun _ => QM.pure' _
    split
    · exact QM.pure' _
    · exact QM.bind' (qm_copyLazyL ob l _) fun _ => QM.pure' _
end

mutual
theorem qm_walkLazy {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, QM (f o s)) :
    ∀ (o : Nat) (l : Lazy S), QM (walkLazy f o l : CM Map Unit)
  | o, mk s fk bd => by
    rw [walkLazy]
    exact QM.bind' (hf o s) fun _ => QM.ite' _ (QM.pure' _)
      (QM.bind' (qm_walkForks hf fk) fun _ => qm_walkBonds hf bd)

theorem qm_walkForks {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, QM (f o s)) :
    ∀ (l : List ((Nat × Lazy S) × (Nat × Lazy S))), QM (walkForks f l : CM Map Unit)
  | [] => by rw [walkForks]; exact QM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [walkForks]
    exact QM.bind' (qm_walkLazy hf oy y) fun _ => QM.bind' (qm_walkLazy hf on n) fun _ =>
      qm_walkForks hf rest

theorem qm_walkBonds {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, QM (f o s)) :
    ∀ (l : List (Nat × Lazy S)), QM (walkBonds f l : CM Map Unit)
  | [] => by rw [walkBonds]; exact QM.pure' _
  | (o, l) :: rest => by
    rw [walkBonds]
    exact QM.bind' (qm_walkLazy hf o l) fun _ => qm_walkBonds hf rest
end

theorem qm_collapseGate (r o oLaz : Nat) (sur : Sure S) : QM (collapseGate r o oLaz sur : CM Map Unit) := by
  unfold collapseGate
  refine QM.bind' (qm_sureRequireLook _) fun ned => ?_
  split
  · exact QM.pure' _
  · exact QM.ite' _ (QM.pure' _) (QM.bind' (QM.ite' _ (QM.pure' _) (QM.proxy' _ _)) fun _ =>
      QM.addOps' _ _)
  · exact QM.bind' (QM.ite' _ (QM.pure' _) (QM.proxy' _ _)) fun _ => qm_crashNeed _ _ _

theorem qm_kern (o : Nat) (laz : Lazy S) : QM (kern o laz : CM Map Nat) := by
  unfold kern
  refine QM.bind' QM.re' fun r => QM.bind' QM.get' fun g => ?_
  refine QM.ite' _ (QM.pure' _) (QM.bind' (qm_walkLazy (fun oLaz sur => ?_) o laz) fun _ => QM.pure' _)
  refine QM.bind' (qm_sureRequireLook _) fun ned => QM.ite' _ (QM.pure' _) ?_
  refine QM.bind' (QM.ite' _ (QM.pure' _) (QM.proxy' _ _)) fun src => QM.ite' _ QM.fail ?_
  exact QM.bind' (qm_kernLoop _ _ _) fun _ => QM.addOps' _ _

theorem qm_lazyShut (o : Nat) (laz : Lazy S) : QM (lazyShut o laz : CM Map (Lazy S)) := by
  unfold lazyShut
  exact QM.ite' _ (QM.pure' _) (QM.bind' (qm_kern _ _) fun _ => QM.pure' _)


end Comp
end SkaModel
end Formalization
