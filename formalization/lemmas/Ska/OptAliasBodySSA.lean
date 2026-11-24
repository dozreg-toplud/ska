import lemmas.Ska.OptAliasBody
import lemmas.Ska.OptAliasSSA
import lemmas.Ska.OptAliasSSADead

/-!
# `BodyOK` from single assignment along a path

The hypothesis `BodyOK` of the body fold `as_body` holds on a block `o` at the
end of a path `o :: p` of blocks from `0` (`BPath`), for the body up to any
place `m` before which no op is a dead fill, on blocks with `AliasSSAB` and
`Acyclic` (**`bodyOK_ssa`**), with

* `Def` = `PathDef bl p b`: the registers no definition writes, the
  parameters of `b`, and the definitions of the earlier blocks of the path;
* `Cl` = `ClR bl`: the registers with no dead fill, or read somewhere
  reachable;
* `Done` any set that holds every register of `PathDef` in `Cl` whose dead
  fills are all in `o` (at the walk, those whose dead fills are in blocks not
  walked yet).

A source of an op is read there, so `DefFirst` defines it before (in `PathDef`
or by an earlier op), it is in `Cl`, and every dead fill of it is in `o`
(`DeadFill` puts every reachable read of a filled register in the fill's
block).  A destination is a definition that counts (`LiveDef`: a reachable
block, before the first dead fill), so `DefOnceB` makes it differ from every
parameter of `o`, every earlier op of `o`, and every definition of an earlier
block of the path (a definition there is not a dead fill, since those blocks
jump, and is in another block, since `Acyclic` makes the path repeat no
block).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- The registers defined before block `b` at the end of the path `o :: p`
(with every register no definition writes). -/
def PathDef (bl : Map Blob) (p : List Nat) (b : Blob) (x : Nat) : Prop :=
  x ∉ allDefs bl ∨ x ∈ b.par ∨ ∃ o' ∈ p, ∃ b', HoonMap.get bl o' = some b' ∧ x ∈ blockDefs b'

/-- The registers whose `old` no dead fill disturbs before they are read: no
dead fill, or a reachable read. -/
def ClR (bl : Map Blob) (x : Nat) : Prop :=
  (∀ o i, ¬ DeadFill bl x o i) ∨ ∃ o' b' j, Reach bl o' ∧ HoonMap.get bl o' = some b' ∧ ReadAt b' j x

theorem bdef_rank {bl : Map Blob} {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o) :
    ∀ {L : List Nat}, BPath bl L → ∀ {o p}, L = o :: p → ∀ o' ∈ p, ρ o < ρ o'
  | _, BPath.start, _, _, e, o', h => by cases e; cases h
  | _, BPath.step (o := o1) (p := p1) hp hb hj, o, p, e, o', h => by
    cases e
    have ih := bdef_rank hρ hp rfl
    have hlt := hρ _ _ _ hb hj
    rcases List.mem_cons.mp h with rfl | h
    · exact hlt
    · exact Nat.lt_trans hlt (ih o' h)

/-- An acyclic path repeats no block. -/
theorem bdef_nodup {bl : Map Blob} (hA : Acyclic bl) {o : Nat} {p : List Nat} (h : BPath bl (o :: p)) : o ∉ p := by
  obtain ⟨ρ, hρ⟩ := hA
  intro hm
  exact Nat.lt_irrefl _ (bdef_rank hρ h rfl o hm)

/-- Every earlier block of a path jumps. -/
theorem bdef_jumps {bl : Map Blob} : ∀ {L : List Nat}, BPath bl L → ∀ {o p}, L = o :: p → ∀ o' ∈ p,
    ∃ b' j, HoonMap.get bl o' = some b' ∧ j ∈ getJmps b'.fin
  | _, BPath.start, _, _, e, o', h => by cases e; cases h
  | _, BPath.step (o := o1) (p := p1) hp hb hj, o, p, e, o', h => by
    cases e
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, _, hb, hj⟩
    · exact bdef_jumps hp rfl o' h

theorem bdef_allDefs {bl : Map Blob} {o x : Nat} {b : Blob} (hb : HoonMap.get bl o = some b)
    (hx : x ∈ blockDefs b) : x ∈ allDefs bl := by
  unfold allDefs
  refine List.mem_flatMap.mpr ⟨o, (MapKeys.mem_keys bl o).mpr (by rw [hb]; rfl), ?_⟩
  rw [hb]; exact hx

theorem bdef_idx {l : List Pole} {x : Nat} (h : x ∈ l.filterMap aliasDst) :
    ∃ (j : Nat) (op : Pole), l[j]? = some op ∧ aliasDst op = some x := by
  obtain ⟨op, hop, he⟩ := List.mem_filterMap.mp h
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hop
  exact ⟨j, op, by rw [List.getElem?_eq_getElem hj, e], he⟩

theorem bdef_src_reads {op : Pole} {x : Nat} (h : x ∈ asSrc op) : x ∈ aliasReads op := by
  cases op <;> simp only [asSrc, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    simp only [aliasReads, aliasDst, poleRegs]
  case mov s d =>
    subst h; by_cases e : x = d
    · subst e; simp
    · simp [e]
  case inc s d =>
    subst h; by_cases e : x = d
    · subst e; simp
    · simp [e]
  case con h0 t0 d =>
    by_cases e1 : h0 = d <;> by_cases e2 : t0 = d <;> rcases h with rfl | rfl <;> simp [e1, e2]
  case hed s d =>
    subst h; by_cases e : x = d
    · subst e; simp
    · simp [e]
  case tal s d =>
    subst h; by_cases e : x = d
    · subst e; simp
    · simp [e]
  all_goals (subst h; simp)

/-- `BodyOK` from places: each op's sources done or written before in the body
by a register of `Cl`, each destination neither defined nor written before. -/
theorem bodyOK_of {Cl : Nat → Prop} : ∀ (ops : List Pole) (Def Done : Nat → Prop),
    (∀ k op, ops[k]? = some op →
      (∀ x ∈ asSrc op, Done x ∨ (x ∈ (ops.take k).filterMap aliasDst ∧ Cl x)) ∧
      (∀ e, aliasDst op = some e → ¬ Def e ∧ e ∉ (ops.take k).filterMap aliasDst)) →
    BodyOK Cl ops Def Done
  | [], _, _, _ => trivial
  | op :: l, Def, Done, h => by
    obtain ⟨h1, h2⟩ := h 0 op rfl
    refine ⟨fun x hx => ?_, fun e he => (h2 e he).1, bodyOK_of l _ _ fun k op' hk => ?_⟩
    · rcases h1 x hx with h | h
      · exact h
      · simp at h
    · obtain ⟨s1, s2⟩ := h (k + 1) op' (by simpa using hk)
      refine ⟨fun x hx => ?_, fun e he => ?_⟩
      · rcases s1 x hx with s | ⟨s, c⟩
        · exact Or.inl (Or.inl s)
        · simp only [List.take_succ_cons, List.filterMap_cons] at s
          cases hd : aliasDst op with
          | none => rw [hd] at s; exact Or.inr ⟨s, c⟩
          | some d =>
            rw [hd] at s
            rcases List.mem_cons.mp s with s | s
            · subst s; exact Or.inl (Or.inr ⟨rfl, c⟩)
            · exact Or.inr ⟨s, c⟩
      · obtain ⟨n1, n2⟩ := s2 e he
        simp only [List.take_succ_cons, List.filterMap_cons] at n2
        refine ⟨fun hd => ?_, fun hm => ?_⟩
        · rcases hd with hd | hd
          · exact n1 hd
          · rw [hd] at n2; exact n2 (List.mem_cons_self ..)
        · cases hd : aliasDst op with
          | none => rw [hd] at n2; exact n2 hm
          | some d => rw [hd] at n2; exact n2 (List.mem_cons_of_mem _ hm)

/-- **`BodyOK` from single assignment along a path**: on blocks with
`AliasSSAB` and `Acyclic`, at the end `o` of a path from `0`, for the body up
to a place `m` before which no op is a dead fill. -/
theorem bodyOK_ssa {bl : Map Blob} (hS : AliasSSAB bl) (hA : Acyclic bl) {o : Nat} {p : List Nat} {b : Blob}
    (hπ : BPath bl (o :: p)) (hb : HoonMap.get bl o = some b) {m : Nat} (hm : ∀ k r, k < m → ¬ DeadFill bl r o k)
    {Done : Nat → Prop}
    (hD : ∀ x, PathDef bl p b x → ClR bl x → (∀ o' i, DeadFill bl x o' i → o' = o) → Done x) :
    BodyOK (ClR bl) (b.body.take m) (PathDef bl p b) Done := by
  have hR : Reach bl o := ssk_bpath_reach hπ o (List.mem_cons_self ..)
  refine bodyOK_of _ _ _ fun k op hk => ?_
  rw [List.getElem?_take] at hk
  split at hk
  case isFalse => cases hk
  rename_i hkm
  have htk : (b.body.take m).take k = b.body.take k := by
    rw [List.take_take]; congr 1; omega
  rw [htk]
  constructor
  · intro x hx
    have hread : ReadAt b k x := Or.inl (by rw [List.head?_drop, hk]; exact bdef_src_reads hx)
    have hcl : ClR bl x := Or.inr ⟨o, b, k, hR, hb, hread⟩
    have hdf : ∀ o' i, DeadFill bl x o' i → o' = o := fun o' i ⟨_, _, _, _, _, hreads⟩ =>
      (hreads o b k hR hb hread).1.symm
    by_cases hx' : x ∈ allDefs bl
    · rcases hS.2 o p b hπ hb k x hread hx' with h | h | h
      · exact Or.inl (hD x (Or.inr (Or.inl h)) hcl hdf)
      · exact Or.inr ⟨h, hcl⟩
      · exact Or.inl (hD x (Or.inr (Or.inr h)) hcl hdf)
    · exact Or.inl (hD x (Or.inl hx') hcl hdf)
  · intro e he
    have hlive : LiveDef bl e (o, some k) :=
      ⟨hR, ⟨b, op, hb, hk, he⟩, fun i hi => by cases hi; exact hm k e hkm⟩
    refine ⟨fun hd => ?_, fun hm' => ?_⟩
    · rcases hd with hd | hd | ⟨o', ho', b', hb', hd⟩
      · exact hd (bdef_allDefs hb (List.mem_append_right _
          (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hk, he⟩)))
      · have := hS.1 e _ (o, none) hlive ⟨hR, ⟨b, hb, hd⟩, fun i hi => by cases hi⟩
        cases this
      · have hR' : Reach bl o' := ssk_bpath_reach hπ o' (List.mem_cons_of_mem _ ho')
        obtain ⟨b'', j, hb'', hj⟩ := bdef_jumps hπ rfl o' ho'
        rw [hb'] at hb''; cases hb''
        have hne := bdef_nodup hA hπ
        rcases List.mem_append.mp hd with hd | hd
        · have := hS.1 e _ (o', none) hlive ⟨hR', ⟨b', hb', hd⟩, fun i hi => by cases hi⟩
          cases this
        · obtain ⟨i, op', hi, hd'⟩ := bdef_idx hd
          have := hS.1 e _ (o', some i) hlive ⟨hR', ⟨b', op', hb', hi, hd'⟩, fun i' _ hdf => by
            obtain ⟨b3, hb3, ⟨u, hu⟩, _⟩ := hdf
            rw [hb'] at hb3; cases hb3; rw [hu] at hj; simp [getJmps] at hj⟩
          simp only [Prod.mk.injEq] at this
          exact hne (this.1 ▸ ho')
    · obtain ⟨i, op', hi, hd'⟩ := bdef_idx hm'
      rw [List.getElem?_take] at hi
      split at hi
      · rename_i hik
        have := hS.1 e _ (o, some i) hlive ⟨hR, ⟨b, op', hb, hi, hd'⟩, fun i' hi' => by
          cases hi'; exact hm i e (by omega)⟩
        simp only [Prod.mk.injEq, Option.some.injEq] at this
        omega
      · cases hi

end Opt
end SkaModel
end Formalization
