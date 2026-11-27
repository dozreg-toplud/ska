import lemmas.Glue.GuardRun

/-!
# `BlocksOK` kept step by step: `KP` (track G, step 1 of `GuardMonoX`)

`KP P m`: every run of `m` from a state whose blocks meet `BlocksOK` (no
block passes `~`, every body is guarded, `Glue/Entry.lean`) ends in such a
state, with a result that meets `P`.  Kept by `pure`, `bind`, `if`, the
steps that leave the blocks alone (`re`, `get`, `+set-tag`, `+proxy`, ...),
`+add-ops` of a list with no split (`NoSplit`, `guardedBody_of_noSplit`) or
of a guarded list, `+emit` / `+emir` of a block that meets `BlockOK`, and
`+insert-hop`.  The tactic `kpb` puts a computation built from them
together (as track D's `qmb` does for `QM`).

## Where the ops of a raw run come from

Every list that a raw run of `FragX` and its final passes put in front of a
block, by reading the model (`CompModel.lean`, `CompLazyRun.lean`,
`CompTop.lean`, `CompLazyArms.lean`, `CompFinishF.lean`):

| site                                   | ops                                   | kind      |
|----------------------------------------|---------------------------------------|-----------|
| `splitNeed` (`+split-need`)            | `[con h t r]`                         | no split  |
| `intoLoop` (`+into-need`)              | `con l r' r` each                     | no split  |
| `copyNeed`, `copyLazy`, `copyLazyL`    | `mov` each                            | no split  |
| `crashNeed` (`+crash-need`)            | `cel p, imm..` / `imm, cel r, imm..`  | no split  |
| `medeLoop` (`+mede`)                   | `[imm som r]`                         | no split  |
| `collapseLazyAtom`, `collapseGate`     | `[mov r r']`, `crashNeed`             | no split  |
| `sureLoop` (`+sure-loop`)              | `[mov r d]`, `kernNeed`               | both      |
| `kern` (`+kern`, `+kerf`, `+lazy-shut`)| `kernNeed src ned`                    | guarded   |
| `finishLF` (the baked constants)       | `imm v r` each                        | no split  |

The only `%hed` / `%tal` of the model are those of `kernLoop` / `kernBoth`
(`+kern-need`), proved guarded in `GuardKern.lean` (`kernNeed_guarded`).
The emitted blocks: their bodies are `[]` or one of `[imm k r]`,
`[inc arg pro]`, `[equ rp rq]`, `[imm (A 0) r0]`, `[imm (A 1) r1]`; their
jumps are `jmp0 _`, the goal's jumps, a sub-run's result jump, `+forl`'s
`[some r0]`, `+fork-need`'s `(flattenNeed n).map some`, and `+insert-hop`'s
`[]`.  Only `+sect`'s threading (`sectStep`, `lensHop`) passes `~`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Lists with no split -/

/-- A list of ops with no `%hed` / `%tal`. -/
def NoSplit (A : List Pole) : Prop := ∀ p ∈ A, splitReg p = Option.none

/-- **A list with no split is guarded.** -/
theorem guardedBody_of_noSplit {A : List Pole} (h : NoSplit A) : GuardedBody A := by
  intro i p s hp hs
  rw [h p (List.mem_of_getElem? hp)] at hs; cases hs

theorem noSplit_nil : NoSplit [] := fun p hp => absurd hp List.not_mem_nil

theorem noSplit_cons {p : Pole} {A : List Pole} (h0 : splitReg p = Option.none) (h : NoSplit A) :
    NoSplit (p :: A) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h0
  · exact h q hq

theorem noSplit_append {A B : List Pole} (hA : NoSplit A) (hB : NoSplit B) : NoSplit (A ++ B) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hA q hq
  · exact hB q hq

/-! ## Jumps with no `~` -/

/-- No `~` among a jump's arguments. -/
def JOK (j : Jmp) : Prop := Option.none ∉ j.args

theorem jok_jmp0 (o : Nat) : JOK (jmp0 o) := by simp [JOK, jmp0]

/-- The jumps of a goal pass no `~`. -/
def GJK : CGoal S → Prop
  | CGoal.next _ th => JOK th
  | CGoal.pick z o => JOK z ∧ JOK o
  | CGoal.done => True

theorem blockOK_of {b : Blob} (hj : ∀ j ∈ getJmps b.fin, JOK j) (hb : NoSplit b.body) : BlockOK b :=
  ⟨hj, guardedBody_of_noSplit hb⟩

/-! ## `KP` -/

/-- The state invariant: `BlocksOK`, and the run is not dropping (no step
of `+comp` sets `drop`). -/
def Inv (g : Comp.Gen Map) : Prop := BlocksOK g.blocks ∧ g.drop = false

/-- **Every run of `m` keeps `Inv` and returns a result in `P`.**  A
structure, so that `intro` does not open it. -/
structure KP {α : Type} (P : α → Prop) (m : CM Map α) : Prop where
  k : ∀ g x g', Inv g → m g = some (x, g') → Inv g' ∧ P x

/-- A step that keeps `BlocksOK`, whatever it returns. -/
abbrev KB {α : Type} (m : CM Map α) : Prop := KP (fun _ : α => True) m

namespace KP

theorem pure' {α : Type} {P : α → Prop} {a : α} (h : P a) : KP P (pure a : CM Map α) := by
  constructor; intro g x g' hb e; cases e; exact ⟨hb, h⟩

theorem bind' {α β : Type} {P : α → Prop} {Q : β → Prop} {m : CM Map α} {f : α → CM Map β}
    (hm : KP P m) (hf : ∀ a, P a → KP Q (f a)) : KP Q (m >>= f) := by
  constructor
  intro g x g' hb e
  obtain ⟨a, g1, h1, h2⟩ := bind_some e
  obtain ⟨b1, pa⟩ := hm.k g a g1 hb h1
  exact (hf a pa).k g1 x g' b1 h2

theorem mono {α : Type} {P Q : α → Prop} {m : CM Map α} (h : KP P m) (hpq : ∀ a, P a → Q a) : KP Q m := by
  constructor
  intro g x g' hb e
  obtain ⟨b1, p⟩ := h.k g x g' hb e
  exact ⟨b1, hpq x p⟩

theorem fail {α : Type} {P : α → Prop} : KP P (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' _ h; cases h

theorem crash {α : Type} {P : α → Prop} : KP P (crashM : CM Map α) := fail

theorem ite' {α : Type} {P : α → Prop} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KP P a) (hb : KP P b) :
    KP P (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A step that leaves the blocks and `drop` alone. -/
theorem same {α : Type} {m : CM Map α}
    (h : ∀ g x g', m g = some (x, g') → g'.blocks = g.blocks ∧ g'.drop = g.drop) : KB m := by
  constructor
  intro g x g' hb e
  obtain ⟨e1, e2⟩ := h g x g' e
  exact ⟨⟨by rw [e1]; exact hb.1, by rw [e2]; exact hb.2⟩, trivial⟩

theorem re' : KB (re : CM Map Nat) := same fun g x g' h => by rw [re_apply] at h; cases h; exact ⟨rfl, rfl⟩

theorem oo' : KB (oo : CM Map Nat) := same fun g x g' h => by cases h; exact ⟨rfl, rfl⟩

theorem freshId' : KB (freshId : CM Map Nat) := same fun g x g' h => by cases h; exact ⟨rfl, rfl⟩

theorem idM' : KB (idM : CM Map Nat) := same fun g x g' h => by cases h; exact ⟨rfl, rfl⟩

theorem get' : KB (get : CM Map (Comp.Gen Map)) := same fun g x g' h => by rw [get_apply] at h; cases h; exact ⟨rfl, rfl⟩

theorem getCond' : KB (getCond : CM Map (Map (Nat × List Nat))) := same fun g x g' h => by cases h; exact ⟨rfl, rfl⟩

theorem setTag' (o : Nat) (region : List Nat) : KB (setTag o region : CM Map Unit) :=
  same fun g x g' h => by
    cases h
    split <;> exact ⟨rfl, rfl⟩

theorem copyTag' (frm : Nat) (tos : List Nat) : KB (copyTag frm tos : CM Map Unit) :=
  same fun g x g' h => by
    unfold copyTag at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · obtain ⟨rg, _, e⟩ := Option.map_eq_some_iff.mp h
      cases e; exact ⟨rfl, rfl⟩

theorem proxy' (r o : Nat) : KB (proxy r o : CM Map Nat) :=
  same fun g x g' h => by
    unfold proxy at h
    simp only at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · obtain ⟨tag, _, e⟩ := Option.map_eq_some_iff.mp h
      cases e; exact ⟨rfl, rfl⟩

theorem liftO' {α : Type} (x : Option α) : KB (liftO x : CM Map α) :=
  same fun g a g' h => by
    obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
    cases e; exact ⟨rfl, rfl⟩

theorem lift' {α : Type} (x : Option α) : KB ((fun g => x.map fun a => (a, g)) : CM Map α) :=
  same fun g a g' h => by
    obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
    cases e; exact ⟨rfl, rfl⟩

/-- **`+add-ops` of a guarded list.** -/
theorem addOpsG (o : Nat) {ops : List Pole} (h : GuardedBody ops) : KB (addOps o ops : CM Map Unit) := by
  constructor
  intro g x g' hb e
  refine ⟨⟨(addOps_ok hb.1 h e).1, ?_⟩, trivial⟩
  unfold addOps at e
  split at e
  · cases e; exact hb.2
  · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp e
    cases e; exact hb.2

/-- **`+add-ops` of a list with no split.** -/
theorem addOps' (o : Nat) {ops : List Pole} (h : NoSplit ops) : KB (addOps o ops : CM Map Unit) :=
  addOpsG o (guardedBody_of_noSplit h)

/-- **`+emir` of a block that meets `BlockOK`.** -/
theorem emir' (o : Nat) {b : Blob} (h : BlockOK b) : KB (emir o b : CM Map Unit) := by
  constructor
  intro g x g' hb e
  cases e
  refine ⟨?_, trivial⟩
  split
  · exact hb
  · exact ⟨blocksOK_put hb.1 h, hb.2⟩

/-- **`+emit` of a block that meets `BlockOK`.** -/
theorem emit' {b : Blob} (h : BlockOK b) : KB (emit b : CM Map Nat) := by
  constructor
  intro g x g' hb e
  rw [emit_apply] at e
  cases e
  exact ⟨⟨blocksOK_emitted hb.1 h, hb.2⟩, trivial⟩

/-- `+emit`, with the label it returns. -/
theorem emitL {b : Blob} (h : BlockOK b) : KB (emit b : CM Map Nat) := emit' h

theorem insertHop' (a o1 o2 : Nat) : KB (insertHop a o1 o2 : CM Map Unit) := by
  constructor
  intro g x g' hb e
  refine ⟨⟨blocksOK_insertHop hb.1 e, ?_⟩, trivial⟩
  unfold insertHop at e
  split at e
  · cases e; exact hb.2
  · cases hb' : HoonMap.get g.blocks a with
    | none => rw [hb'] at e; cases e
    | some b =>
      rw [hb'] at e
      simp only [Option.bind_some] at e
      split at e
      · split at e
        · cases e
        · cases e; exact hb.2
      · cases e

theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, KB acc → KB (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), KB acc → KB (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

end KP

/-- The side goal of an `+emit`: the block passes no `~` and has no split. -/
macro "kpblk" : tactic => `(tactic| (apply blockOK_of <;>
  simp_all [getJmps, JOK, jmp0, NoSplit, splitReg]))

/-- One step of the tactic `kpb`. -/
macro "kpb_step" : tactic => `(tactic| first
  | exact KP.re' | exact KP.oo' | exact KP.freshId' | exact KP.idM' | exact KP.get'
  | exact KP.getCond' | exact KP.setTag' _ _ | exact KP.copyTag' _ _ | exact KP.proxy' _ _
  | exact KP.fail | exact KP.crash | exact KP.liftO' _ | exact KP.lift' _ | exact KP.insertHop' _ _ _
  | exact KP.addOps' _ (by simp [NoSplit, splitReg])
  | exact KP.emit' (by kpblk)
  | exact KP.emir' _ (by kpblk)
  | exact KP.pure' trivial
  | exact KP.pure' (jok_jmp0 _)
  | (apply KP.pure'; simp_all [JOK, jmp0])
  | apply KP.bind' | apply KP.ite' | split | intro _)

/-- Prove `KP` of a computation built from the primitives. -/
macro "kpb" : tactic => `(tactic| repeat kpb_step)

end Glue
end SkaModel
end Formalization
