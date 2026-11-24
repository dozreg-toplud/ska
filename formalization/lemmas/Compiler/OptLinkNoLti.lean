import lemmas.Compiler.OptLinkBase
import lemmas.Ska.OptDriverTopo

/-!
# The passes before `+switch-chains` make no `%lti`

The links of `+bb-topo`, `+rev-cfg`, `+remove-dead-code` and the readers of
`+remove-empty-middle` take blocks with no `%lti` (`NoLti`), because
`+get-jmps` and `+get-regs` give `~` on `%lti` where the models do not.  The
structural passes and `+remove-dead-code` keep `NoLti` (on any map instance):
`+remove-useless-branching` and `+remove-empty-middle` give each block a
terminator of the same kind or a `%hop` (`noLti_rub`, `noLti_mid`),
`+remove-hops` ends a merged block with the terminator of a block
(`noLti_hops`), and `+remove-dead-code` keeps the terminators
(`noLti_dead`).  So in `+optimize-once` every pass meets blocks with no
`%lti` when the input has none.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel SkaModel.Opt

variable {Map : Type → Type} [HoonMap Map]

theorem rubFin_plain (bl : Map Blob) (fin : Termin) (e : List Pole × Termin) (h : rubFin bl fin = some e)
    (hf : finPlain fin = true) : finPlain e.2 = true := by
  have two : ∀ (z o : Jmp) (epi : List Pole), rubTwo bl fin z o epi = some e → finPlain e.2 = true := by
    intro z o epi h2
    unfold rubTwo at h2
    split at h2
    · obtain ⟨nz, -, h3⟩ := Option.bind_eq_some_iff.mp h2
      obtain ⟨no, -, rfl⟩ := Option.map_eq_some_iff.mp h3
      split
      · rfl
      · exact hf
    · cases h2
  cases fin with
  | clq s z o => exact two z o [] h
  | eqq l r z o => exact two z o _ h
  | brn s z o => exact two z o _ h
  | brz s z o => exact two z o [] h
  | lti => simp [finPlain] at hf
  | _ => simp only [rubFin, Option.some.injEq] at h; subst h; exact hf

theorem noLti_rub [MapKeys Map] {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hl : NoLti bl) : NoLti bl' := by
  intro k b' hb'
  obtain ⟨b, e, hb, he, rfl⟩ := (rub_blocks h).back hb'
  exact rubFin_plain bl b.fin e he (hl k b hb)

theorem middleFin_plain (bl : Map Blob) (rd : Nat → List Nat) (fuel : Nat) (fin f' : Termin)
    (h : middleFin bl rd fuel fin = some f') (hf : finPlain fin = true) : finPlain f' = true := by
  cases fin with
  | clq s z o =>
    obtain ⟨z', -, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o', -, rfl⟩ := Option.map_eq_some_iff.mp h2; rfl
  | eqq l r z o =>
    obtain ⟨z', -, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o', -, rfl⟩ := Option.map_eq_some_iff.mp h2; rfl
  | brn s z o =>
    obtain ⟨z', -, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o', -, rfl⟩ := Option.map_eq_some_iff.mp h2; rfl
  | brz s z o =>
    obtain ⟨z', -, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o', -, rfl⟩ := Option.map_eq_some_iff.mp h2; rfl
  | hop t =>
    obtain ⟨t', -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  | lti => simp [finPlain] at hf
  | _ => simp only [middleFin, Option.some.injEq] at h; subst h; exact hf

theorem noLti_mid [MapKeys Map] {fuel : Nat} {bl bl' : Map Blob} {ch : Bool}
    (h : removeEmptyMiddle fuel bl = some (ch, bl')) (hl : NoLti bl) : NoLti bl' := by
  intro k b' hb'
  obtain ⟨b, f', hb, hf', rfl⟩ := (mid_blocks h).back hb'
  exact middleFin_plain bl _ fuel b.fin f' hf' (hl k b hb)

theorem noLti_dead {bl bl' : Map Blob} {revTopo : List Nat} (h : removeDeadCode bl revTopo = some bl')
    (hl : NoLti bl) : NoLti bl' := by
  intro k b' hb'
  obtain ⟨b, hb, -, hf⟩ := (dead_shape h).1 k b' hb'
  rw [hf]; exact hl k b hb

theorem hopChain_plain (bl : Map Blob) (rev : Map (List Nat)) (hl : NoLti bl) :
    ∀ (n o : Nat) (bnew : Blob) (segs : List (List Pole)) (saw : List Nat) (r : Blob × List Nat),
    hopChain bl rev n o bnew segs saw = some r → finPlain bnew.fin = true → finPlain r.1.fin = true := by
  intro n
  induction n with
  | zero => intro o bnew segs saw r h; simp [hopChain] at h
  | succ n ih =>
    intro o bnew segs saw r h hf
    simp only [hopChain] at h
    split at h
    · rename_i t ht
      split at h
      · cases h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; simpa [hopDone] using hf
        · obtain ⟨b1, hb1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨seg, -, h3⟩ := Option.bind_eq_some_iff.mp h2
          exact ih _ _ _ _ _ h3 (hl _ b1 hb1)
    · simp only [Option.some.injEq] at h; subst h; simpa [hopDone] using hf

theorem noLti_hops {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (h : removeHops fuel bl rev topo = some (ch, bl')) (hl : NoLti bl) : NoLti bl' := by
  unfold removeHops at h
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  have key : ∀ (l : List Nat) (acc r : Map Blob × List Nat), NoLti acc.1 →
      l.foldlM (hopsStep fuel bl rev) acc = some r → NoLti r.1 := by
    intro l
    induction l with
    | nil => intro acc r ha h; simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; subst h; exact ha
    | cons o l ih =>
      intro acc r ha h
      simp only [List.foldlM_cons] at h
      cases e1 : hopsStep fuel bl rev acc o with
      | none => rw [e1] at h; cases h
      | some a1 =>
        rw [e1] at h
        refine ih a1 r ?_ h
        unfold hopsStep at e1
        split at e1
        · simp only [Option.some.injEq] at e1; subst e1; exact ha
        · obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.mp e1
          obtain ⟨rc, hrc, rfl⟩ := Option.map_eq_some_iff.mp h2
          intro k b' hb'
          simp only [HoonMap.get_put] at hb'
          split at hb'
          · simp only [Option.some.injEq] at hb'; subst hb'
            exact hopChain_plain bl rev hl fuel o b [] acc.2 rc hrc (hl o b hb)
          · exact ha k b' hb'
  exact key topo (HoonMap.empty, []) r (fun k b hb => by simp [HoonMap.get_empty] at hb) hr

end Compiler
end Formalization
