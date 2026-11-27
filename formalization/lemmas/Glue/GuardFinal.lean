import lemmas.Glue.GuardRun
import lemmas.Ska.RawInvWholeX

/-!
# `BlocksOK` through the final passes (track G, step 6: `GuardFinalU`, `GuardFinalF`)

The pieces of the two final passes, each keeping `BlocksOK` (no block passes
`~`, every body is guarded):

* `kernStepG`, `kernListG`: one gate of `+kern` and the walk over a list of
  entries, under track D's `KI` (`RawInvKernX.lean`).  A gate puts in front of
  the entry's block the output of one `+kern-need` (`kernNeed_guarded`), from
  the facts `KI` gives (the sure need `Distinct`, below `sub`, and the source
  register not in it);
* `coerceStepG`, `coerceListG`: one step of `+coerce-lazy` and the iteration,
  under track D's `CoI` (`RawInvFinishX.lean`), through `sureLoop_guard`;
* `chase_keeps`: whatever holds of a jump and of the hop of every block holds
  of what `+chase` returns (fixpoint induction, no rank needed);
* `blocksOK_rename`: the renaming path (`renameBlocks`, each kept block
  renamed by `f` with its end chased) keeps `BlocksOK` when `f` does not send
  a register a body writes onto another register (`RenOK`).  The map path
  on a run of inputs is the renaming path by `renReg ∘ unproxy`
  (`toStraightF_run`): `unproxy` fixes every defined register and sends every
  other one to itself or to `sub`, which is not defined, so `RenOK` holds.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+chase` -/

open Lean.Order in
/-- **What holds of a jump and of the hop of every block holds of its chase.** -/
theorem chase_keeps (bs : Map Blob) (br : Bool) (P : Jmp → Prop)
    (h : ∀ k b t, HoonMap.get bs k = some b → b.fin = Termin.hop t → P t) :
    ∀ j j', chase bs br j = some j' → P j → P j' := by
  refine chase.fixpoint_induct bs br (fun f => ∀ j j', f j = some j' → P j → P j') ?_ ?_
  · exact admissible_pi_apply _ (fun j => admissible_pi _ (fun j' => Option.admissible_eq_some _ j'))
  · intro f ih j j' hf hj
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
    obtain ⟨b, hb, hf⟩ := hf
    split at hf
    · rename_i t ht
      split at hf
      · split at hf
        · exact ih t j' hf (h _ _ _ hb ht)
        · cases hf
      · cases hf; exact hj
    · cases hf; exact hj

/-- The jumps of a chased end are chased jumps of the end, renamed. -/
theorem chaseFin_jmps {bs : Map Blob} {f : Nat → Nat} {fin fin' : Termin} (hc : chaseFin bs f fin = some fin') :
    ∀ j'' ∈ getJmps fin', ∃ j ∈ getJmps fin, ∃ br j', chase bs br j = some j' ∧ j'' = renJmp f j' := by
  intro j'' hm
  cases fin with
  | clq s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], _, z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], _, o'', ho, rfl⟩
  | eqq l q z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], _, z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], _, o'', ho, rfl⟩
  | brn s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], _, z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], _, o'', ho, rfl⟩
  | brz s z o' =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o'', ho, rfl⟩ := hc
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨z, by simp [getJmps], _, z', hz, rfl⟩
    · exact ⟨o', by simp [getJmps], _, o'', ho, rfl⟩
  | hop t =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨t', ht, rfl⟩ := hc
    simp only [getJmps, List.mem_singleton] at hm
    subst hm
    exact ⟨t, by simp [getJmps], _, t', ht, rfl⟩
  | lti _ _ _ _ => simp [chaseFin] at hc
  | bom x =>
    cases x with
    | none => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [getJmps] at hm
    | some x =>
      simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨_, _, rfl⟩ := hc; simp [getJmps] at hm
  | jmp a v => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [getJmps] at hm
  | jmf a v n => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [getJmps] at hm
  | jsp a s => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [getJmps] at hm
  | jsf a s n => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [getJmps] at hm
  | don s => simp only [chaseFin, Option.some.injEq] at hc; subst hc; simp [getJmps] at hm

theorem none_not_mem_renJmp {f : Nat → Nat} {j : Jmp} (h : Option.none ∉ j.args) :
    Option.none ∉ (renJmp f j).args := by
  simp only [renJmp, List.mem_map, not_exists, not_and]
  intro a ha e
  cases a with
  | none => exact h ha
  | some x => cases e

/-! ## Renaming a guarded body -/

theorem splitReg_ren (f : Nat → Nat) (p : Pole) : splitReg (renPole f p) = (splitReg p).map f := by
  cases p <;> rfl

theorem aliasDst_ren (f : Nat → Nat) (p : Pole) : aliasDst (renPole f p) = (aliasDst p).map f := by
  cases p <;> rfl

/-- **A renaming that does not send a written register onto another one
keeps a body guarded.** -/
theorem guardedBody_ren {f : Nat → Nat} {body : List Pole}
    (hf : ∀ q ∈ body, ∀ x, aliasDst q = some x → ∀ s, f x = f s → x = s) (h : GuardedBody body) :
    GuardedBody (body.map (renPole f)) := by
  intro i p' s' hp hs
  rw [List.getElem?_map] at hp
  obtain ⟨p, hp0, rfl⟩ := Option.map_eq_some_iff.mp hp
  rw [splitReg_ren] at hs
  obtain ⟨s, hs0, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨j, hj, hjc, hw⟩ := h i p s hp0 hs0
  refine ⟨j, hj, by rw [List.getElem?_map, hjc]; rfl, fun l h1 h2 q' hq => ?_⟩
  rw [List.getElem?_map] at hq
  obtain ⟨q, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  rw [aliasDst_ren]
  intro e
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.mp e
  have qm : q ∈ body := List.mem_of_getElem? hq0
  exact hw l h1 h2 q hq0 (by rw [hx, hf q qm x hx s ex])

/-- A renaming that sends no register a body of `bs` writes onto another one. -/
def RenOK (bs : Map Blob) (f : Nat → Nat) : Prop :=
  ∀ k b, HoonMap.get bs k = some b → ∀ q ∈ b.body, ∀ x, aliasDst q = some x → ∀ s, f x = f s → x = s

/-- **The renaming path keeps `BlocksOK`.** -/
theorem blocksOK_rename {bs new : Map Blob} {f : Nat → Nat} (hB : BlocksOK bs) (hf : RenOK bs f)
    (h : renameBlocks bs f = some new) : BlocksOK new := by
  intro k b' hk
  obtain ⟨b, hb, hkb⟩ := renameBlocks_get h hk
  unfold keepBlock at hkb
  split at hkb
  · cases hkb
  obtain ⟨fin, hfin, e⟩ := Option.map_eq_some_iff.mp hkb
  cases e
  refine ⟨fun j'' hj => ?_, guardedBody_ren (hf k b hb) (hB k b hb).2⟩
  obtain ⟨j, hj0, br, j', hc, rfl⟩ := chaseFin_jmps hfin j'' hj
  refine none_not_mem_renJmp (chase_keeps bs br (fun j => Option.none ∉ j.args) (fun k1 b1 t hb1 ht => ?_)
    j j' hc ((hB k b hb).1 j hj0))
  exact (hB k1 b1 hb1).1 t (by rw [ht]; simp [getJmps])

/-- The start block moved to `0`. -/
theorem blocksOK_start {bl : Map Blob} {o : Nat} {start : Blob} (hB : BlocksOK bl)
    (hst : HoonMap.get bl o = some start) : BlocksOK (HoonMap.put (HoonMap.del bl o) 0 start) := by
  intro k b hb
  rw [HoonMap.get_put] at hb
  split at hb
  · cases hb; exact hB o start hst
  · rw [HoonMap.get_del] at hb
    split at hb
    · cases hb
    · exact hB k b hb

/-! ## `+kern` -/

variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}

/-- **One gate of `+kern` keeps `BlocksOK`**, under `KI`. -/
theorem kernStepG {sub o oL : Nat} {l : Comp.Lazy S} {rest : List (Nat × Comp.Lazy S)} {g g' : Comp.Gen Map}
    (hI : KI X ρ lo sub ((oL, l) :: rest) g) (hB : BlocksOK g.blocks)
    (h : kernGate sub o oL l.sure g = some ((), g')) : BlocksOK g'.blocks := by
  obtain ⟨S0, hsub, hc, hdc, hns, hap, he⟩ := hI
  obtain ⟨⟨b, hb⟩, dl, hl⟩ := he (oL, l) List.mem_cons_self
  unfold kernGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  have lk : g.re ≤ kk := L.le
  have mN : ∀ y, NMem ned y → NMem l.sure.ned y ∨ (g.re ≤ y ∧ y < kk) := fun y hy => by
    rcases L.mem y hy with e | ⟨a, c⟩
    · exact Or.inl e
    · exact Or.inr ⟨a, c⟩
  by_cases en : ned = Need.none
  · rw [if_pos en] at h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    exact hB
  rw [if_neg en] at h2
  obtain ⟨src, g2, hs, h3⟩ := bind_some h2
  have SRC : g2.blocks = g.blocks ∧ ((src = sub ∧ g2.re = kk) ∨ (src = kk ∧ g2.re = kk + 1)) := by
    by_cases e : oL = o
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · rw [if_neg e] at hs
      unfold proxy at hs
      simp only [S0.drop, Bool.false_eq_true, if_false] at hs
      obtain ⟨tag, -, he'⟩ := Option.map_eq_some_iff.mp hs
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨hb2, hsrc⟩ := SRC
  have srcl : src < g2.re := by
    rcases hsrc with ⟨e, e'⟩ | ⟨e, e'⟩
    · omega
    · omega
  have nsrc : ¬ NMem ned src := fun hm => by
    rcases mN src hm with e | ⟨a, c⟩
    · have := (hl src e).1
      rcases hsrc with ⟨e', -⟩ | ⟨e', -⟩
      · omega
      · omega
    · rcases hsrc with ⟨e', -⟩ | ⟨e', -⟩
      · omega
      · omega
  rw [show noSoft oL = false from rfl] at h3
  simp only [Bool.false_eq_true, ↓reduceIte] at h3
  obtain ⟨ops, g3, h4, h5⟩ := bind_some h3
  have nb2 : NB g2.re ned := fun y hy => by
    rcases mN y hy with e | ⟨a, c⟩
    · have := (hl y e).1; omega
    · omega
  have dn : Distinct ned := L.dist dl (fun y hy => by have := (hl y hy).1; omega)
  obtain ⟨A, eA, K, G⟩ := kernLoop_guarded ned src [] g2 g3 ops h4 srcl nsrc nb2 dn
  simp only [List.append_nil] at eA
  subst eA
  have hb3 : g3.blocks = g.blocks := by rw [K.gen]; exact hb2
  exact (addOps_ok (by rw [hb3]; exact hB) G h5).1

/-- **The walk of `+kern` over a list of entries keeps `BlocksOK`.** -/
theorem kernListG (sub o : Nat) : ∀ (es : List (Nat × Comp.Lazy S)) (g g' : Comp.Gen Map),
    KI X ρ lo sub es g → BlocksOK g.blocks → walkList (kernGate sub o) es g = some ((), g') →
    BlocksOK g'.blocks
  | [], g, g', hI, hB, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact hB
  | (o', l) :: rest, g, g', hI, hB, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    exact kernListG sub o rest g1 g' (kernStep hI h1).1 (kernStepG hI hB h1) h2

/-! ## `+coerce-lazy` -/

/-- **One step of `+coerce-lazy` keeps `BlocksOK`**, under `CoI`. -/
theorem coerceStepG {ned : Need} {R : Nat} {less : Cape} {o : Nat} {l : Comp.Lazy S}
    {rest : List (Nat × Comp.Lazy S)} {g g' : Comp.Gen Map} {u : Unit}
    (hI : CoI X ρ lo ned R ((o, l) :: rest) g) (hB : BlocksOK g.blocks)
    (h : Comp.coerceLazy ned o l.sure less g = some (u, g')) : BlocksOK g'.blocks := by
  obtain ⟨S0, hR, hn, hap, he⟩ := hI
  obtain ⟨⟨b, hb⟩, dl, hl⟩ := he (o, l) List.mem_cons_self
  unfold Comp.coerceLazy at h
  obtain ⟨lok, g1, h1, h2⟩ := bind_some h
  obtain ⟨lk, -, e1⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨tgt, g2, h3, h4⟩ := bind_some h2
  have L := sureRequireLook_spec h3
  obtain ⟨kk, e2⟩ := L.gen
  subst e2
  have lk : g.re ≤ kk := L.le
  have mN : ∀ y, NMem tgt y → NMem l.sure.ned y ∨ (g.re ≤ y ∧ y < kk) := fun y hy => by
    rcases L.mem y hy with e | ⟨a, c⟩
    · exact Or.inl e
    · exact Or.inr ⟨a, c⟩
  refine (sureLoop_guard ned tgt ({ g with re := kk } : Comp.Gen Map) g' u hB (L.dist dl (fun y hy => by have := (hl y hy).1; omega))
    (fun y hy => ?_) (fun y hy => ?_) (fun y hy ht => ?_) h4).1
  · show y < kk
    rcases mN y hy with e | ⟨a, c⟩
    · have := (hl y e).1; omega
    · omega
  · show y < kk
    have := (hn y hy).1; omega
  · rcases mN y ht with e | ⟨a, c⟩
    · exact (hl y e).2.1 hy
    · have := (hn y hy).1; omega

/-- **The iteration of `+coerce-lazy` keeps `BlocksOK`**, under `CoI`. -/
theorem coerceListG {ned : Need} {R : Nat} {less : Cape} : ∀ (es : List (Nat × Comp.Lazy S)) (g g' : Comp.Gen Map),
    CoI X ρ lo ned R es g → BlocksOK g.blocks → Comp.coerceList ned less es g = some ((), g') →
    BlocksOK g'.blocks
  | [], g, g', hI, hB, h => by
    simp only [Comp.coerceList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact hB
  | (o, l) :: rest, g, g', hI, hB, h => by
    simp only [Comp.coerceList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    exact coerceListG rest g1 g' (coI_step hI h1).1 (coerceStepG hI hB h1) h2

/-- **`+coerce-lazy` over the lazy tree keeps `BlocksOK`**, under `CoI`. -/
theorem coerceLazyLG {ned : Need} {R : Nat} {less : Cape} {o : Nat} {laz : Comp.Lazy S} {g g' : Comp.Gen Map}
    (hI : CoI X ρ lo ned R ((o, laz) :: Comp.entries laz) g) (hB : BlocksOK g.blocks)
    (h : Comp.coerceLazyL ned less o laz g = some ((), g')) : BlocksOK g'.blocks := by
  rw [Comp.coerceLazyL_flat] at h
  have h' : (Comp.coerceList ned less ((o, laz) :: Comp.entries laz) : Comp.CM Map Unit) g = some ((), g') := by
    simp only [Comp.coerceList]; exact h
  exact coerceListG _ g g' hI hB h'

end Glue
end SkaModel
end Formalization
