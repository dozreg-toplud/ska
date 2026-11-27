import lemmas.Ska.OptAliasResult

/-!
# Invariants of the walk of `+alias` for the pill link

Three facts of every state of `aliasWalk`, on any input (no `TopoInvR`, no
`DInvS`: the link `AliasLink` assumes only that the blocks have no `%lti`).

* **`BrzInv`**: a `%brz` end of `new` at `p` has a test register `s` whose
  facts in `info p` exist and have no `hasImm`.  The refinement after a
  single predecessor's `%brz` (`aliasStart`, `is-loob:(~(got by info) s)` in
  the Hoon) reads `isLoob` of those facts, which the link's `InfoRel` fixes
  only up to `loobImm`; with no `hasImm` it fixes it exactly
  (`brzInv_loob`, and `InfoEq.isLoob` of `OptAliasPerm.lean`).  `aliasFin`
  keeps or makes a `%brz` only on a test register with no `hasImm`
  (`afin_brz`), and stores the facts it read as `info o` with the block
  (`brzInv_block`, `brzInv_walk`, `brzInv_empty`).
* **`RevNodup`**: the lists of `rev` have no duplicates (`dedupN`, then
  `erase`: `revNodup_init`, `revNodup_block`, `revNodup_walk`), so the
  Hoon's `pre` (a set) and the model's `g.rev o` with the same members are
  permutations (`perm_of_nodup`).
* **`aliasM_noLti`**: the result of `aliasM` has no `%lti` end when its input
  has none (`noLti_block`, `noLti_walk`), with no other hypothesis.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- **The `%brz` invariant.** -/
def BrzInv (g : AGen Map) : Prop :=
  ∀ p b s z o', HoonMap.get g.new p = some b → b.fin = Termin.brz s z o' →
    ∃ ip si, g.info p = some ip ∧ ip s = some si ∧ si.hasImm = none

/-- **`aliasFin` keeps or makes a `%brz` only on a test register with no
`hasImm`.** -/
theorem afin_brz {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r)
    {s : Nat} {z o' : Jmp} (hr : r.1 = Termin.brz s z o') : ∃ si, loc s = some si ∧ si.hasImm = none := by
  cases fin with
  | clq s0 z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; simp [aliasFold] at hr
      · split at e
        · subst e; simp [aliasFold] at hr
        · subst e; cases hr
  | eqq l r' z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; cases hr
      · cases h; simp [aliasFold] at hr
  | brn s0 z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · rename_i hi
        split at e
        · subst e
          simp only [Termin.brz.injEq] at hr
          obtain ⟨rfl, -, -⟩ := hr
          exact ⟨ic, hic, hi⟩
        · subst e; cases hr
      · subst e; simp [aliasFold] at hr
      · subst e; simp [aliasFold] at hr
      · subst e; cases hr
  | brz s0 z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · rename_i hz
        subst e
        simp only [Termin.brz.injEq] at hr
        obtain ⟨rfl, -, -⟩ := hr
        refine ⟨ic, hic, ?_⟩
        revert hz
        cases ic.hasImm <;> simp
      · subst e; simp [aliasFold] at hr
      · subst e; simp [aliasFold] at hr
  | hop t => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr
  | lti => simp only [aliasFin, Option.some.injEq] at h; subst h; cases hr

/-- What a walked block of `aliasBlock` is: the steps, each as it returned. -/
theorem aliasBlock_walked {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (hw : ¬(g.rev o = [] ∧ o ≠ 0)) :
    ∃ (b : Blob) (rb : List Pole × ABody) (rf : Termin × (Nat → List Nat) × Bool), HoonMap.get bl o = some b ∧
      aliasFin rb.2.old rb.2.loc g.rev g.folded o b.fin = some rf ∧
      g' = { new := HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }
             old := rb.2.old
             info := updA g.info o (some rb.2.loc)
             imms := updA g.imms o (some rb.2.imml)
             rev := rf.2.1
             folded := rf.2.2 } := by
  unfold aliasBlock at h
  rw [if_neg hw] at h
  obtain ⟨info, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨imms, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨edges, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨loc0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rb, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rf, hrf, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b, rb, rf, hb, hrf, rfl⟩

/-- A dropped block of `aliasBlock` changes only `folded` and `rev`. -/
theorem aliasBlock_dropped {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (h : aliasBlock pick nargs bl g o = some g') (hw : g.rev o = [] ∧ o ≠ 0) :
    ∃ b, HoonMap.get bl o = some b ∧
      g' = { g with folded := true, rev := (getJmps b.fin).foldl (fun acc j => delJu acc j.there o) g.rev } := by
  unfold aliasBlock at h
  rw [if_pos hw] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b, hb, rfl⟩

/-- **`aliasBlock` keeps `BrzInv`.** -/
theorem brzInv_block {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (hg : BrzInv g) (h : aliasBlock pick nargs bl g o = some g') : BrzInv g' := by
  by_cases hw : g.rev o = [] ∧ o ≠ 0
  · obtain ⟨b, -, rfl⟩ := aliasBlock_dropped h hw
    exact hg
  · obtain ⟨b, rb, rf, -, hrf, rfl⟩ := aliasBlock_walked h hw
    intro p b' s z o' hb' hf
    simp only [HoonMap.get_put] at hb'
    by_cases e : p = o
    · subst e
      rw [if_pos rfl, Option.some.injEq] at hb'
      subst hb'
      obtain ⟨si, hsi, hn⟩ := afin_brz hrf hf
      exact ⟨rb.2.loc, si, by simp [updA], hsi, hn⟩
    · rw [if_neg e] at hb'
      obtain ⟨ip, si, h1, h2, h3⟩ := hg p b' s z o' hb' hf
      exact ⟨ip, si, by simp [updA, e, h1], h2, h3⟩

/-- **The walk keeps `BrzInv`.** -/
theorem brzInv_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} :
    ∀ (topo : List Nat) {g g' : AGen Map}, BrzInv g → aliasWalk pick nargs bl topo g = some g' → BrzInv g'
  | [], _, _, hg, h => by cases h; exact hg
  | o :: topo, _, _, hg, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    exact brzInv_walk topo (brzInv_block hg h1) h

/-- `BrzInv` of a state with no blocks yet (the start of `aliasM`). -/
theorem brzInv_empty {g : AGen Map} (h : ∀ p, HoonMap.get g.new p = none) : BrzInv g := by
  intro p b s z o' hb
  rw [h p] at hb; cases hb

/-- **What the refinement after a `%brz` needs**: the facts of its test
register exist, and `isLoob` is all that `InfoRel` fixes of them. -/
theorem brzInv_loob {g : AGen Map} (hg : BrzInv g) {p : Nat} {b : Blob} {s : Nat} {z o' : Jmp} {ip : AInfo}
    (hb : HoonMap.get g.new p = some b) (hf : b.fin = Termin.brz s z o') (hi : g.info p = some ip) :
    ∃ si, ip s = some si ∧ si.loobImm = false := by
  obtain ⟨ip', si, h1, h2, h3⟩ := hg p b s z o' hb hf
  rw [hi, Option.some.injEq] at h1
  subst h1
  refine ⟨si, h2, ?_⟩
  unfold InfoReg.loobImm; rw [h3]

/-! ## `rev` without duplicates -/

/-- The lists of `rev` have no duplicates. -/
def RevNodup (rev : Nat → List Nat) : Prop := ∀ k, (rev k).Nodup

theorem revNodup_delJu {rev : Nat → List Nat} (h : RevNodup rev) (k o : Nat) : RevNodup (delJu rev k o) := by
  intro k'
  unfold delJu updA
  by_cases e : k' = k
  · rw [if_pos e]; exact (h k).erase o
  · rw [if_neg e]; exact h k'

/-- `aliasFin` changes `rev` only by `delJu`. -/
theorem afin_revNodup {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r) (hr : RevNodup rev) :
    RevNodup r.2.1 := by
  have hfold : ∀ go cut, RevNodup (aliasFold rev o go cut).2.1 := by
    intro go cut
    unfold aliasFold
    dsimp only
    split
    · exact hr
    · exact revNodup_delJu hr cut o
  cases fin with
  | clq s0 z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact hfold _ _
      · split at e
        · subst e; exact hfold _ _
        · subst e; exact hr
  | eqq l r' z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; exact hr
      · cases h; exact hfold _ _
  | brn s0 z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · subst e; exact hr
        · subst e; exact hr
      · subst e; exact hfold _ _
      · subst e; exact hfold _ _
      · subst e; exact revNodup_delJu (revNodup_delJu hr _ _) _ _
  | brz s0 z0 o0 =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact hr
      · subst e; exact hfold _ _
      · subst e; exact hfold _ _
  | hop t => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr
  | lti => simp only [aliasFin, Option.some.injEq] at h; subst h; exact hr

theorem revNodup_foldl_delJu (o : Nat) :
    ∀ (js : List Jmp) {rev : Nat → List Nat}, RevNodup rev → RevNodup (js.foldl (fun acc j => delJu acc j.there o) rev)
  | [], _, h => h
  | j :: js, _, h => revNodup_foldl_delJu o js (revNodup_delJu h j.there o)

/-- **`aliasBlock` keeps `RevNodup` of `rev`.** -/
theorem revNodup_block {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (hg : RevNodup g.rev) (h : aliasBlock pick nargs bl g o = some g') : RevNodup g'.rev := by
  by_cases hw : g.rev o = [] ∧ o ≠ 0
  · obtain ⟨b, -, rfl⟩ := aliasBlock_dropped h hw
    exact revNodup_foldl_delJu o _ hg
  · obtain ⟨b, rb, rf, -, hrf, rfl⟩ := aliasBlock_walked h hw
    exact afin_revNodup hrf hg

theorem revNodup_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} :
    ∀ (topo : List Nat) {g g' : AGen Map}, RevNodup g.rev → aliasWalk pick nargs bl topo g = some g' →
      RevNodup g'.rev
  | [], _, _, hg, h => by cases h; exact hg
  | o :: topo, _, _, hg, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    exact revNodup_walk topo (revNodup_block hg h1) h

/-- `rev` at the start of `aliasM`. -/
theorem revNodup_init (rev : Map (List Nat)) : RevNodup fun o => dedupN ((HoonMap.get rev o).getD []) :=
  fun _ => awr_dedup_nodup _

/-! ## No `%lti` in the result -/

/-- **`aliasBlock` keeps `NoLti` of `new`** when the blocks have no `%lti`. -/
theorem noLti_block {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {g g' : AGen Map} {o : Nat}
    (hbl : NoLti bl) (hg : NoLti g.new) (h : aliasBlock pick nargs bl g o = some g') : NoLti g'.new := by
  by_cases hw : g.rev o = [] ∧ o ≠ 0
  · obtain ⟨b, -, rfl⟩ := aliasBlock_dropped h hw
    exact hg
  · obtain ⟨b, rb, rf, hb, hrf, rfl⟩ := aliasBlock_walked h hw
    intro p b' hb'
    simp only [HoonMap.get_put] at hb'
    by_cases e : p = o
    · subst e
      rw [if_pos rfl, Option.some.injEq] at hb'
      subst hb'
      exact afin_nolti hrf (hbl p b hb)
    · rw [if_neg e] at hb'
      exact hg p b' hb'

theorem noLti_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} (hbl : NoLti bl) :
    ∀ (topo : List Nat) {g g' : AGen Map}, NoLti g.new → aliasWalk pick nargs bl topo g = some g' → NoLti g'.new
  | [], _, _, hg, h => by cases h; exact hg
  | o :: topo, _, _, hg, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    exact noLti_walk hbl topo (noLti_block hbl hg h1) h

/-- **The result of `aliasM` has no `%lti` end when its input has none**, on
any `nargs`, `rev`, `topo` and any `pick` (the first conjunct of `AliasLink`). -/
theorem aliasM_noLti {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {rev : Map (List Nat)}
    {topo : List Nat} {ra : Bool × Map Blob} (hbl : NoLti bl) (h : aliasM pick nargs bl rev topo = some ra) :
    NoLti ra.2 := by
  unfold aliasM at h
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
  refine noLti_walk hbl topo ?_ hg
  intro p b hb
  simp [HoonMap.get_empty] at hb

/-- **`BrzInv` and `RevNodup` hold at every state of the walk of `aliasM`**
reached after a prefix of `topo`. -/
theorem aliasM_inv {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {rev : Map (List Nat)}
    {topo : List Nat} {g : AGen Map}
    (h : aliasWalk pick nargs bl topo
      { new := HoonMap.empty, old := id, info := fun _ => none, imms := fun _ => none,
        rev := fun o => dedupN ((HoonMap.get rev o).getD []), folded := false } = some g) :
    BrzInv g ∧ RevNodup g.rev :=
  ⟨brzInv_walk topo (brzInv_empty fun p => HoonMap.get_empty p) h, revNodup_walk topo (revNodup_init rev) h⟩

end Opt
end SkaModel
end Formalization
