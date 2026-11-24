import lemmas.Ska.CompRunOKLB

/-!
# Runs do not read the bodies of the blocks they are given: `SimM`

README Gaps 12.23.  Every relation proved so far for a run under a lazy goal
(`LOKC`) assumes the goal entries' blocks empty (`⟨[], [], hop th⟩`).  Under
`RunOKLB` a goal entry's block may hold a body (the `con` of `+split`, the
moves of `+copy`, the ops of a part that ran before).  This file shows that
a run does not look at those bodies: it only puts ops in FRONT of them
(`+add-ops`), so the run from a state whose blocks carry extra bodies at the
end is the run from the stripped state with the same bodies kept.

* `addBody`, `SimB bd g g'`: `g` is `g'` with `bd o` appended to the body of
  the block at `o`, for labels `o` below `g.bo` only; every other field
  equal.
* `SimM m`: from `SimB`-related states, `m` gives the same result and
  `SimB`-related states (the stripped run exists when the real one does).
  Kept by `pure`, `bind`, `if`, `re`, `oo`, `+emit`, `+add-ops`, `+set-tag`,
  `+proxy`, `liftO`, and `get` followed by a test of `drop` only
  (`SimM.getDrop`, the pattern of `+mede`, `+collapse-lazy-atom`, `+kern`).
* The arms: `+split`, `+into`, `+copy` (with the merge of forks and bonds),
  `+walk-lazy`, `+mede`, `+collapse-lazy-atom`, `+kern`, `+kerf`, `+past`,
  `+bomb`, `+simple-next`, `+forl`, `doneBlocks`, the indirect call.
* `PlainN`: no `%6`, no direct call, no hint.  `simM_runLC`: `runLC` on a
  nomm of `PlainN` is `SimM` for every goal.

**The hypothesis that makes "runs never read block bodies" true** is
`PlainN`: the only arms that read a block's body are `+insert-hop` (in
`+fork`, which moves a fork's or bond's body behind a new branch block) and
`jabBlock` of `+sect`, and both are reached only through `%6` under `%next`
(`sixNextLC`).  Direct calls and hints are out of the model's scope.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation of states -/

/-- A block with `B` appended to its body. -/
def addBody (B : List Pole) (b : Blob) : Blob := ⟨b.par, b.body ++ B, b.fin⟩

@[simp] theorem addBody_nil (b : Blob) : addBody [] b = b := by cases b; simp [addBody]

/-- **`g` is `g'` with the bodies `bd o` appended** at the labels below
`g.bo`, every other field equal. -/
structure SimB (bd : Nat → List Pole) (g g' : Gen Map) : Prop where
  re : g.re = g'.re
  bo : g.bo = g'.bo
  id : g.id = g'.id
  drop : g.drop = g'.drop
  tags : g.tags = g'.tags
  cond : g.cond = g'.cond
  blocks : ∀ o, HoonMap.get g.blocks o = (HoonMap.get g'.blocks o).map (addBody (bd o))
  above : ∀ o, g.bo ≤ o → bd o = []

/-- **A computation that does not read the extra bodies.** -/
structure SimM {α : Type} (m : CM Map α) : Prop where
  sim : ∀ (bd : Nat → List Pole) (g g' : Gen Map) (a : α) (g1 : Gen Map), SimB bd g g' → m g = some (a, g1) →
    ∃ g1', m g' = some (a, g1') ∧ SimB bd g1 g1'

namespace SimM

theorem pure' {α : Type} (a : α) : SimM (pure a : CM Map α) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  exact ⟨g', rfl, hs⟩

theorem bind' {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : SimM m) (hf : ∀ a, SimM (f a)) :
    SimM (m >>= f) := by
  constructor
  intro bd g g' x g2 hs h
  rw [bind_apply] at h
  obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g1', e1, s1⟩ := hm.sim bd g g' a g1 hs h1
  obtain ⟨g2', e2, s2⟩ := (hf a).sim bd g1 g1' x g2 s1 h2
  refine ⟨g2', ?_, s2⟩
  rw [bind_apply, e1]
  exact e2

theorem fail {α : Type} : SimM (fun _ => Option.none : CM Map α) := by
  constructor; intro bd g g' x g1 _ h; cases h

theorem crash {α : Type} : SimM (crashM : CM Map α) := fail

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CM Map α} (ha : SimM a) (hb : SimM b) :
    SimM (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem re' : SimM (re : CM Map Nat) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  refine ⟨{ g' with re := g'.re + 1 }, by rw [re_apply, hs.re], ?_⟩
  exact ⟨by simp [hs.re], hs.bo, hs.id, hs.drop, hs.tags, hs.cond, hs.blocks, hs.above⟩

theorem oo' : SimM (oo : CM Map Nat) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  refine ⟨{ g' with bo := g'.bo + 1 }, by simp only [oo, hs.bo], ?_⟩
  exact ⟨hs.re, by simp [hs.bo], hs.id, hs.drop, hs.tags, hs.cond, hs.blocks,
    fun o ho => hs.above o (by simp at ho; omega)⟩

theorem freshId' : SimM (freshId : CM Map Nat) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  refine ⟨{ g' with id := g'.id + 1 }, by simp only [freshId, hs.id], ?_⟩
  exact ⟨hs.re, hs.bo, by simp [hs.id], hs.drop, hs.tags, hs.cond, hs.blocks, hs.above⟩

theorem idM' : SimM (idM : CM Map Nat) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  refine ⟨{ g' with id := g'.id + 1 }, by simp only [idM, hs.id], ?_⟩
  exact ⟨hs.re, hs.bo, by simp [hs.id], hs.drop, hs.tags, hs.cond, hs.blocks, hs.above⟩

theorem getCond' : SimM (getCond : CM Map (Map (Nat × List Nat))) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  exact ⟨g', by simp only [getCond, hs.cond], hs⟩

theorem emit' (b : Blob) : SimM (emit b : CM Map Nat) := by
  constructor
  intro bd g g' x g1 hs h
  rw [emit_apply] at h
  cases h
  refine ⟨g'.emitted b, by rw [emit_apply, hs.bo], ?_⟩
  have a0 : bd g.bo = [] := hs.above g.bo (Nat.le_refl _)
  have eb : g'.bo = g.bo := hs.bo.symm
  have ed : g'.drop = g.drop := hs.drop.symm
  refine ⟨hs.re, by simp [Gen.emitted, hs.bo], hs.id, by simp [Gen.emitted, hs.drop], hs.tags, hs.cond,
    fun o => ?_, fun o ho => hs.above o (by simp [Gen.emitted] at ho; omega)⟩
  simp only [Gen.emitted, eb, ed]
  cases hd : g.drop
  · simp only [Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
    by_cases e : o = g.bo
    · subst e; simp [a0]
    · simp only [e, ↓reduceIte]; exact hs.blocks o
  · simp only [↓reduceIte]; exact hs.blocks o

theorem addOps' (o : Nat) (ops : List Pole) : SimM (addOps o ops : CM Map Unit) := by
  constructor
  intro bd g g' x g1 hs h
  unfold addOps at h
  by_cases d : g.drop = true
  · rw [if_pos d] at h
    cases h
    exact ⟨g', by unfold addOps; rw [if_pos (hs.drop ▸ d)], hs⟩
  · rw [if_neg d] at h
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    rw [hs.blocks o] at hb
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    refine ⟨{ g' with blocks := HoonMap.put g'.blocks o { b' with body := ops ++ b'.body } }, ?_, ?_⟩
    · unfold addOps; rw [if_neg (hs.drop ▸ d), hb']; rfl
    · refine ⟨hs.re, hs.bo, hs.id, hs.drop, hs.tags, hs.cond, fun k => ?_, hs.above⟩
      simp only [HoonMap.get_put]
      by_cases e : k = o
      · subst e; simp [addBody]
      · simp only [e, ↓reduceIte]; exact hs.blocks k

theorem setTag' (o : Nat) (region : List Nat) : SimM (setTag o region : CM Map Unit) := by
  constructor
  intro bd g g' x g1 hs h
  cases h
  refine ⟨if g'.drop then g' else { g' with tags := HoonMap.put g'.tags o region }, by simp [setTag], ?_⟩
  by_cases d : g.drop = true
  · have d' : g'.drop = true := hs.drop ▸ d
    rw [if_pos d, if_pos d']; exact hs
  · have d' : ¬ g'.drop = true := hs.drop ▸ d
    rw [if_neg d, if_neg d']
    exact ⟨hs.re, hs.bo, hs.id, hs.drop, by simp [hs.tags], hs.cond, hs.blocks, hs.above⟩

theorem copyTag' (frm : Nat) (tos : List Nat) : SimM (copyTag frm tos : CM Map Unit) := by
  constructor
  intro bd g g' x g1 hs h
  unfold copyTag at h
  by_cases d : g.drop = true
  · rw [if_pos d] at h
    cases h
    exact ⟨g', by unfold copyTag; rw [if_pos (hs.drop ▸ d)], hs⟩
  · rw [if_neg d] at h
    obtain ⟨rg, hr, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    refine ⟨{ g' with tags := tos.foldl (fun m o => HoonMap.put m o rg) g'.tags }, ?_, ?_⟩
    · unfold copyTag; rw [if_neg (hs.drop ▸ d), ← hs.tags, hr]; rfl
    · exact ⟨hs.re, hs.bo, hs.id, hs.drop, by simp [hs.tags], hs.cond, hs.blocks, hs.above⟩

theorem proxy' (r o : Nat) : SimM (proxy r o : CM Map Nat) := by
  constructor
  intro bd g g' x g1 hs h
  unfold proxy at h
  simp only at h
  by_cases d : g.drop = true
  · rw [if_pos d] at h
    cases h
    refine ⟨{ g' with re := g'.re + 1 }, by unfold proxy; simp only; rw [if_pos (hs.drop ▸ d), hs.re], ?_⟩
    exact ⟨by simp [hs.re], hs.bo, hs.id, hs.drop, hs.tags, hs.cond, hs.blocks, hs.above⟩
  · rw [if_neg d] at h
    obtain ⟨tag, ht, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    refine ⟨{ g' with re := g'.re + 1, cond := HoonMap.put g'.cond g'.re (r, tag) }, ?_, ?_⟩
    · unfold proxy; simp only; rw [if_neg (hs.drop ▸ d), ← hs.tags, ht, hs.re]; rfl
    · exact ⟨by simp [hs.re], hs.bo, hs.id, hs.drop, hs.tags, by simp [hs.cond, hs.re], hs.blocks, hs.above⟩

theorem liftO' {α : Type} (x : Option α) : SimM (liftO x : CM Map α) := by
  constructor
  intro bd g g' a g1 hs h
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
  cases e
  exact ⟨g', by simp [liftO, hb], hs⟩

theorem lift' {α : Type} (x : Option α) : SimM ((fun g => x.map fun a => (a, g)) : CM Map α) := by
  constructor
  intro bd g g' a g1 hs h
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
  cases e
  exact ⟨g', by simp [hb], hs⟩

/-- **`get` followed by a computation that reads only `drop`.** -/
theorem getDrop {α : Type} {f : Gen Map → CM Map α} (hf : ∀ g g' : Gen Map, g.drop = g'.drop → f g = f g')
    (hs : ∀ g, SimM (f g)) : SimM (get >>= f) := by
  constructor
  intro bd g g' x g1 sb h
  rw [bind_apply, get_apply] at h
  simp only [Option.bind_some] at h
  obtain ⟨g1', e, s⟩ := (hs g).sim bd g g' x g1 sb h
  refine ⟨g1', ?_, s⟩
  rw [bind_apply, get_apply]
  simp only [Option.bind_some]
  rw [← hf g g' sb.drop]
  exact e

/-- A fold of steps that do not read the extra bodies. -/
theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, SimM acc → SimM (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), SimM acc → SimM (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end SimM

/-- One step of the tactic `simb`. -/
macro "simb_step" : tactic => `(tactic| first
  | exact SimM.pure' _ | exact SimM.re' | exact SimM.oo' | exact SimM.freshId' | exact SimM.idM'
  | exact SimM.getCond' | exact SimM.emit' _ | exact SimM.addOps' _ _ | exact SimM.setTag' _ _
  | exact SimM.copyTag' _ _ | exact SimM.proxy' _ _
  | exact SimM.fail | exact SimM.crash | exact SimM.liftO' _ | exact SimM.lift' _
  | apply SimM.bind' | apply SimM.ite' | split | intro _)

/-- Prove `SimM` of a computation built from the primitives. -/
macro "simb" : tactic => `(tactic| repeat simb_step)

/-! ## The arms of the needs -/

theorem simM_must (ned : Need) : SimM (must ned : CM Map (Nat × Need)) := by unfold must; simb

theorem simM_splitNeed (ned : Need) (o : Nat) : SimM (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · simb
  · simb
  · simb
  · exact SimM.bind' (simM_must _) fun _ => SimM.bind' (simM_must _) fun _ => by simb

theorem simM_splitSure (sur : Sure S) (o : Nat) : SimM (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro bd g g' x g1 hs h
  unfold splitSure at h ⊢
  obtain ⟨⟨lh, lt⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨g2', e2, s2⟩ := (simM_splitNeed sur.ned o).sim bd g g' y g2 hs h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨g2', by simp [hl, e2], s2⟩

theorem simM_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    SimM (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops
    rw [intoLoop]
    split
    · simb
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _
      · exact SimM.bind' SimM.re' fun _ => SimM.bind' SimM.re' fun _ => ih _ hl _ _ _
      · exact ih _ hl _ _ _
      · exact SimM.bind' (simM_must _) fun _ => SimM.bind' (simM_must _) fun _ => ih _ hl _ _ _

theorem simM_intoNeed (axe : Nat) (ned : Need) (o : Nat) : SimM (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact SimM.ite' _ SimM.fail (SimM.ite' _ (SimM.pure' _) (simM_intoLoop _ _ _ _ _))

theorem simM_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : SimM (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro bd g g' x g1 hs h
  unfold intoSure at h ⊢
  obtain ⟨⟨ld, lr⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨g2', e2, s2⟩ := (simM_intoNeed axe sur.ned o).sim bd g g' y g2 hs h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨g2', by simp [hl, e2], s2⟩

theorem simM_copyNeed : ∀ (a b : Need) (ops : List Pole), SimM (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _ => by rw [copyNeed]; simb
  | Need.this _, Need.none, _ => by rw [copyNeed] <;> first | exact SimM.pure' _ | nofun
  | Need.pair _ _, Need.none, _ => by rw [copyNeed] <;> first | exact SimM.pure' _ | nofun
  | Need.both _ _ _, Need.none, _ => by rw [copyNeed] <;> first | exact SimM.pure' _ | nofun
  | Need.this _, Need.this _, _ => by rw [copyNeed]; simb
  | Need.this _, Need.both _ _ _, _ => by rw [copyNeed]; simb
  | Need.this _, Need.pair _ _, _ => by rw [copyNeed]; simb
  | Need.both _ _ _, Need.this _, _ => by rw [copyNeed]; simb
  | Need.pair _ _, Need.this _, _ => by rw [copyNeed]; simb
  | Need.both _ hl tl, Need.both _ hr tr, _ => by
    rw [copyNeed]
    exact SimM.bind' (simM_copyNeed hl hr _) fun _ => SimM.bind' (simM_copyNeed tl tr _) fun _ => by simb
  | Need.both _ hl tl, Need.pair p q, _ => by
    rw [copyNeed]
    exact SimM.bind' SimM.re' fun _ =>
      SimM.bind' (simM_copyNeed hl p _) fun _ => SimM.bind' (simM_copyNeed tl q _) fun _ => by simb
  | Need.pair pl ql, Need.pair pr qr, _ => by
    rw [copyNeed]
    exact SimM.bind' (simM_copyNeed pl pr _) fun _ => SimM.bind' (simM_copyNeed ql qr _) fun _ => by simb
  | Need.pair pl ql, Need.both _ h t, _ => by
    rw [copyNeed]
    exact SimM.bind' (simM_copyNeed pl h _) fun _ => SimM.bind' (simM_copyNeed ql t _) fun _ => by simb

theorem simM_lookPath : ∀ (axe : Nat) (ned : Need), SimM (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> simb
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact SimM.bind' (ih _ hl _) fun _ => by simb
      · exact SimM.bind' (ih _ hl _) fun _ => by simb

theorem simM_sureRequireLook (sur : Sure S) : SimM (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine SimM.foldl' _ (fun acc b h => SimM.bind' h fun ned => ?_) _ _ (SimM.pure' _)
  exact SimM.ite' _ (SimM.pure' _) (SimM.ite' _ SimM.fail (simM_lookPath _ _))

theorem simM_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : SimM (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed; split <;> simb

theorem simM_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), SimM (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; simb
  | _, Need.this _ => by rw [medeLoop]; simb
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact simM_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact SimM.bind' (simM_medeLoop o a p) fun _ => simM_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact simM_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact SimM.bind' (SimM.addOps' _ _) fun _ => SimM.bind' (simM_medeLoop o a h) fun _ => simM_medeLoop o b t

theorem simM_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, SimM (kh x a)) (ht : ∀ x a, SimM (kt x a)) (ops : List Pole) :
    SimM (kernBoth r d kh kt ops) := by
  unfold kernBoth
  exact SimM.bind' SimM.re' fun _ => SimM.bind' (ht _ _) fun _ => SimM.bind' SimM.re' fun _ =>
    SimM.bind' (hh _ _) fun _ => by simb

theorem simM_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), SimM (kernLoop r ned ops : CM Map (List Pole))
  | _, Need.none, _ => by unfold kernLoop; simb
  | _, Need.this _, _ => by unfold kernLoop; simb
  | _, Need.pair p q, _ => by
    unfold kernLoop
    exact SimM.bind' SimM.re' fun _ =>
      simM_kernBoth _ _ (fun x a => simM_kernLoop x p a) (fun x a => simM_kernLoop x q a) _
  | _, Need.both _ h t, _ => by
    unfold kernLoop
    exact simM_kernBoth _ _ (fun x a => simM_kernLoop x h a) (fun x a => simM_kernLoop x t a) _

theorem simM_forl (r o : Nat) : SimM (forl r o : CM Map (Nat × Nat)) := by unfold forl; simb

theorem simM_doneBlocks : SimM (doneBlocks : CM Map (Nat × Nat)) := by unfold doneBlocks; simb

/-! ## The arms of the lazy needs -/

mutual
theorem simM_splitLoop : ∀ (l : Lazy S) (o : Nat), SimM (splitLoop l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [splitLoop]
    refine SimM.bind' (simM_splitSure s o) fun a => ?_
    rcases a with ⟨sh, st⟩
    refine SimM.ite' _ (SimM.pure' _) (SimM.bind' (simM_splitForks f) fun x => ?_)
    rcases x with ⟨fh, ft⟩
    refine SimM.bind' (simM_splitBonds b) fun y => ?_
    rcases y with ⟨bh, bt⟩
    exact SimM.pure' _

theorem simM_splitForks : ∀ (l : List (ForkE S)), SimM (splitForks l : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [splitForks]; exact SimM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks]
    refine SimM.bind' (simM_splitLoop y oy) fun a => ?_
    rcases a with ⟨yh, yt⟩
    refine SimM.bind' (simM_splitLoop n on) fun b => ?_
    rcases b with ⟨nh, nt⟩
    refine SimM.bind' (simM_splitForks rest) fun c => ?_
    rcases c with ⟨rh, rt⟩
    exact SimM.pure' _

theorem simM_splitBonds : ∀ (l : List (Nat × Lazy S)),
    SimM (splitBonds l : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [splitBonds]; exact SimM.pure' _
  | (o, l) :: rest => by
    rw [splitBonds]
    refine SimM.bind' (simM_splitLoop l o) fun a => ?_
    rcases a with ⟨lh, lt⟩
    refine SimM.bind' (simM_splitBonds rest) fun c => ?_
    rcases c with ⟨rh, rt⟩
    exact SimM.pure' _
end

mutual
theorem simM_intoLoopL (axe : Nat) : ∀ (l : Lazy S) (o : Nat), SimM (intoLoopL axe l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [intoLoopL]
    refine SimM.bind' (simM_intoSure axe s o) fun a => ?_
    rcases a with ⟨sd, sr⟩
    refine SimM.ite' _ (SimM.pure' _) (SimM.bind' (simM_intoForks axe f) fun x => ?_)
    rcases x with ⟨fd, fr⟩
    refine SimM.bind' (simM_intoBonds axe b) fun y => ?_
    rcases y with ⟨bd', br⟩
    exact SimM.pure' _

theorem simM_intoForks (axe : Nat) : ∀ (l : List (ForkE S)),
    SimM (intoForks axe l : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [intoForks]; exact SimM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [intoForks]
    refine SimM.bind' (simM_intoLoopL axe y oy) fun a => ?_
    rcases a with ⟨yd, yr⟩
    refine SimM.bind' (simM_intoLoopL axe n on) fun b => ?_
    rcases b with ⟨nd, nr⟩
    refine SimM.bind' (simM_intoForks axe rest) fun c => ?_
    rcases c with ⟨rd, rr⟩
    exact SimM.pure' _

theorem simM_intoBonds (axe : Nat) : ∀ (l : List (Nat × Lazy S)),
    SimM (intoBonds axe l : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [intoBonds]; exact SimM.pure' _
  | (o, l) :: rest => by
    rw [intoBonds]
    refine SimM.bind' (simM_intoLoopL axe l o) fun a => ?_
    rcases a with ⟨ld, lr⟩
    refine SimM.bind' (simM_intoBonds axe rest) fun c => ?_
    rcases c with ⟨rd, rr⟩
    exact SimM.pure' _
end

mutual
theorem simM_copyLazyL (o : Nat) : ∀ (a b : Lazy S), SimM (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine SimM.bind' (simM_copyNeed _ _ _) fun a => ?_
    rcases a with ⟨ned, ops⟩
    refine SimM.bind' (SimM.addOps' _ _) fun _ => SimM.bind' ?_ fun _ => SimM.bind' ?_ fun _ => SimM.pure' _
    · split
      · exact SimM.pure' _
      · split
        · exact SimM.pure' _
        · exact SimM.bind' (simM_mergeForks _ f1) fun _ => SimM.pure' _
    · split
      · exact SimM.pure' _
      · split
        · exact SimM.pure' _
        · exact SimM.bind' (simM_mergeBonds _ b1) fun _ => SimM.pure' _

theorem simM_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    SimM (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact SimM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine SimM.bind' ?_ fun _ => SimM.bind' (simM_mergeForks idx rest) fun _ => SimM.pure' _
    split
    · exact SimM.pure' _
    · split
      · exact SimM.bind' (simM_copyLazyL oy y _) fun _ => SimM.bind' (simM_copyLazyL on n _) fun _ => SimM.pure' _
      · exact SimM.fail

theorem simM_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    SimM (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact SimM.pure' _
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine SimM.bind' ?_ fun _ => SimM.bind' (simM_mergeBonds idx rest) fun _ => SimM.pure' _
    split
    · exact SimM.pure' _
    · exact SimM.bind' (simM_copyLazyL ob l _) fun _ => SimM.pure' _
end

mutual
theorem simM_walkLazy {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, SimM (f o s)) :
    ∀ (o : Nat) (l : Lazy S), SimM (walkLazy f o l : CM Map Unit)
  | o, mk s fk bd => by
    rw [walkLazy]
    exact SimM.bind' (hf o s) fun _ => SimM.ite' _ (SimM.pure' _)
      (SimM.bind' (simM_walkForks hf fk) fun _ => simM_walkBonds hf bd)

theorem simM_walkForks {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, SimM (f o s)) :
    ∀ (l : List ((Nat × Lazy S) × (Nat × Lazy S))), SimM (walkForks f l : CM Map Unit)
  | [] => by rw [walkForks]; exact SimM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [walkForks]
    exact SimM.bind' (simM_walkLazy hf oy y) fun _ => SimM.bind' (simM_walkLazy hf on n) fun _ =>
      simM_walkForks hf rest

theorem simM_walkBonds {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, SimM (f o s)) :
    ∀ (l : List (Nat × Lazy S)), SimM (walkBonds f l : CM Map Unit)
  | [] => by rw [walkBonds]; exact SimM.pure' _
  | (o, l) :: rest => by
    rw [walkBonds]
    exact SimM.bind' (simM_walkLazy hf o l) fun _ => simM_walkBonds hf rest
end

theorem simM_medeL (th : Jmp) (som : Noun) (laz : Lazy S) : SimM (medeL th som laz : CM Map Nat) := by
  unfold medeL
  refine SimM.bind' (SimM.emit' _) fun o => SimM.getDrop (fun g g' e => by simp only [e]) fun g => ?_
  refine SimM.ite' _ (SimM.pure' _) (SimM.bind' (simM_walkLazy (fun o' sur => ?_) o laz) fun _ => SimM.pure' _)
  exact SimM.bind' (simM_sureRequireLook _) fun _ => simM_medeLoop _ _ _

theorem simM_collapseGate (r o oLaz : Nat) (sur : Sure S) : SimM (collapseGate r o oLaz sur : CM Map Unit) := by
  unfold collapseGate
  refine SimM.bind' (simM_sureRequireLook _) fun ned => ?_
  split
  · exact SimM.pure' _
  · exact SimM.ite' _ (SimM.pure' _) (SimM.bind' (SimM.ite' _ (SimM.pure' _) (SimM.proxy' _ _)) fun _ =>
      SimM.addOps' _ _)
  · exact SimM.bind' (SimM.ite' _ (SimM.pure' _) (SimM.proxy' _ _)) fun _ => simM_crashNeed _ _ _

theorem simM_collapseLazyAtomL (nex : NextL S) : SimM (collapseLazyAtomL nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtomL
  refine SimM.ite' _ SimM.fail (SimM.ite' _ (SimM.pure' _) (SimM.bind' (simM_sureRequireLook _) fun ned => ?_))
  refine SimM.bind' (by split <;> simb) fun p => ?_
  rcases p with ⟨r, there⟩
  refine SimM.getDrop (fun g g' e => by simp only [e]) fun g => ?_
  exact SimM.ite' _ (SimM.pure' _)
    (SimM.bind' (simM_walkLazy (fun o s => simM_collapseGate r there o s) _ _) fun _ => SimM.pure' _)

theorem simM_kern (o : Nat) (laz : Lazy S) : SimM (kern o laz : CM Map Nat) := by
  unfold kern
  refine SimM.bind' SimM.re' fun r => SimM.getDrop (fun g g' e => by simp only [e]) fun g => ?_
  refine SimM.ite' _ (SimM.pure' _) (SimM.bind' (simM_walkLazy (fun oLaz sur => ?_) o laz) fun _ => SimM.pure' _)
  refine SimM.bind' (simM_sureRequireLook _) fun ned => SimM.ite' _ (SimM.pure' _) ?_
  refine SimM.bind' (SimM.ite' _ (SimM.pure' _) (SimM.proxy' _ _)) fun src => SimM.ite' _ SimM.fail ?_
  exact SimM.bind' (simM_kernLoop _ _ _) fun _ => SimM.addOps' _ _

theorem simM_kerf (nex : NextL S) : SimM (kerf nex : CM Map (Nat × Nat)) := by
  unfold kerf
  exact SimM.bind' (SimM.emit' _) fun _ => SimM.bind' (simM_kern _ _) fun _ => SimM.pure' _

theorem simM_lazyShut (o : Nat) (laz : Lazy S) : SimM (lazyShut o laz : CM Map (Lazy S)) := by
  unfold lazyShut
  exact SimM.ite' _ (SimM.pure' _) (SimM.bind' (simM_kern _ _) fun _ => SimM.pure' _)

theorem simM_pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    SimM (pastL cod nex nom region : CM Map (NextL S)) := by
  unfold pastL; simb

theorem simM_simpleNextL (goal : CGoalL S) : SimM (simpleNextL goal : CM Map (NextL S)) := by
  unfold simpleNextL; simb

theorem simM_bombL (miss : Option Nat) : SimM (bombL miss : CM Map (NextL S)) := by unfold bombL; simb

theorem simM_splitL (nex : NextL S) : SimM (splitL nex : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold splitL
  refine SimM.bind' (SimM.emit' _) fun o => SimM.bind' (simM_splitLoop _ _) fun a => ?_
  rcases a with ⟨h, t⟩
  exact SimM.pure' _

theorem simM_intoL (nex : NextL S) (axe : Nat) : SimM (intoL nex axe : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold intoL
  refine SimM.bind' (SimM.emit' _) fun o => SimM.bind' (simM_intoLoopL _ _ _) fun a => ?_
  rcases a with ⟨d, r⟩
  exact SimM.pure' _

theorem simM_copyL (first : NextL S) (second : Lazy S) : SimM (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  exact SimM.bind' (SimM.emit' _) fun _ => SimM.bind' (simM_copyLazyL _ _ _) fun _ => SimM.pure' _

/-! ## `runLC` -/

/-- **The nomms whose runs do not read block bodies**: no `%6`, no direct
call, no hint. -/
def PlainN : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => PlainN p
  | Nomm.n4 p => PlainN p
  | Nomm.n5 p q => PlainN p ∧ PlainN q
  | Nomm.cons p q => PlainN p ∧ PlainN q
  | Nomm.n7 p q => PlainN p ∧ PlainN q
  | Nomm.n10 _ v q => PlainN v ∧ PlainN q
  | Nomm.n2 p q Option.none => PlainN p ∧ PlainN q
  | _ => False

theorem simM_callL (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (p q : Nomm)
    (sup : Option Nomm) (hp : ∀ g r, SimM (rp g r)) (hq : ∀ g r, SimM (rq g r)) (goal : CGoalL S)
    (region : List Nat) : SimM (callL env rp rq p q Option.none sup goal region : CM Map (NextL S)) := by
  unfold callL
  refine SimM.bind' (simM_simpleNextL _) fun nex => SimM.bind' (simM_kerf _) fun a => ?_
  rcases a with ⟨out, pro⟩
  exact SimM.bind' SimM.re' fun _ => SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ =>
    SimM.bind' (hq _ _) fun _ => SimM.bind' (simM_pastL _ _ _ _) fun _ => SimM.bind' (hp _ _) fun _ =>
      simM_copyL _ _

/-- **`runLC` on `PlainN` does not read the extra bodies**, for every goal. -/
theorem simM_runLC (env : CallEnv) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm) (goal : CGoalL S)
    (region : List Nat), SimM (runLC (Map := Map) env sup nm goal region)
  | Nomm.cons p q, h, sup, goal, region => by
    unfold runLC
    refine SimM.bind' (by cases goal <;> dsimp only <;> simb) fun goal' => ?_
    cases goal' <;> dsimp only
    · exact SimM.bind' (SimM.emit' _) fun _ => SimM.bind' (simM_runLC env q h.2 _ _ _) fun _ =>
        SimM.bind' (simM_pastL _ _ _ _) fun _ => SimM.bind' (simM_runLC env p h.1 _ _ _) fun _ => simM_copyL _ _
    · exact SimM.fail
    · refine SimM.bind' (simM_splitL _) fun a => ?_
      rcases a with ⟨hed, tel, o⟩
      exact SimM.bind' (simM_pastL _ _ _ _) fun _ => SimM.bind' (simM_runLC env q h.2 _ _ _) fun _ =>
        SimM.bind' (simM_pastL _ _ _ _) fun _ => SimM.bind' (simM_runLC env p h.1 _ _ _) fun _ => simM_copyL _ _
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLC
    refine SimM.ite' _ (simM_bombL _) (SimM.bind' (simM_simpleNextL _) fun nex => SimM.ite' _ (SimM.pure' _) ?_)
    cases fromL ax nex.laz
    · exact SimM.fail
    · exact SimM.pure' _
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLC
    cases goal <;> dsimp only
    · exact SimM.ite' _ (SimM.pure' _) (SimM.ite' _ (SimM.pure' _) (simM_bombL _))
    · exact SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ => SimM.pure' _
    · exact SimM.bind' (simM_medeL _ _ _) fun _ => SimM.pure' _
  | Nomm.n3 p, h, sup, goal, region => by
    unfold runLC
    have ih := simM_runLC env p h
    cases goal <;> dsimp only
    · exact SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ => ih _ _ _
    · exact SimM.bind' simM_doneBlocks fun _ => SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ =>
        ih _ _ _
    · refine SimM.ite' _ (ih _ _ _) (SimM.bind' (simM_collapseLazyAtomL _) fun a => ?_)
      cases a
      · exact SimM.fail
      · exact SimM.bind' (simM_forl _ _) fun _ => SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ =>
          ih _ _ _
  | Nomm.n4 p, h, sup, goal, region => by
    unfold runLC
    have ih := simM_runLC env p h
    cases goal <;> dsimp only
    · exact SimM.bind' SimM.re' fun _ => SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ => ih _ _ _
    · exact SimM.bind' SimM.re' fun _ => SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ => ih _ _ _
    · refine SimM.bind' (simM_collapseLazyAtomL _) fun a => SimM.bind' ?_ fun _ => ?_
      · cases a <;> dsimp only
        · exact SimM.bind' SimM.re' fun _ => SimM.ite' _ (SimM.pure' _) SimM.fail
        · exact SimM.pure' _
      · exact SimM.bind' SimM.re' fun _ => SimM.bind' (SimM.emit' _) fun _ => ih _ _ _
  | Nomm.n5 p q, h, sup, goal, region => by
    unfold runLC
    refine SimM.bind' SimM.re' fun _ => SimM.bind' SimM.re' fun _ => SimM.bind' ?_ fun _ =>
      SimM.bind' (simM_runLC env q h.2 _ _ _) fun _ => SimM.bind' (simM_pastL _ _ _ _) fun _ =>
        SimM.bind' (simM_runLC env p h.1 _ _ _) fun _ => simM_copyL _ _
    cases goal <;> dsimp only
    · exact SimM.emit' _
    · exact SimM.bind' simM_doneBlocks fun _ => SimM.emit' _
    · refine SimM.bind' (simM_collapseLazyAtomL _) fun a => ?_
      cases a <;> dsimp only
      · exact SimM.ite' _ (SimM.emit' _) SimM.fail
      · exact SimM.bind' (simM_forl _ _) fun _ => SimM.emit' _
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLC
    exact SimM.bind' (simM_runLC env q h.2 _ _ _) fun _ => simM_runLC env p h.1 _ _ _
  | Nomm.n10 a v q, h, sup, goal, region => by
    unfold runLC
    refine SimM.bind' (simM_simpleNextL _) fun _ => SimM.bind' (simM_intoL _ _) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    exact SimM.bind' (simM_pastL _ _ _ _) fun _ => SimM.bind' (simM_runLC env v h.1 _ _ _) fun _ =>
      SimM.bind' (simM_pastL _ _ _ _) fun _ => SimM.bind' (simM_runLC env q h.2 _ _ _) fun _ => simM_copyL _ _
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLC
    exact simM_callL env p q sup (fun g r => simM_runLC env p h.1 _ _ _) (fun g r => simM_runLC env q h.2 _ _ _)
      goal region

end Comp
end SkaModel
end Formalization
