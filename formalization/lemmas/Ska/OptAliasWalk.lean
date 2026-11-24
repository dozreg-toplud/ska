import lemmas.Ska.OptAliasBodySSA
import lemmas.Ska.OptAliasRev
import lemmas.Ska.OptTrimWalk

/-!
# The walk of `+alias`: the blocks it walks are reachable

`+alias` keeps `old` global to the walk, so a block that no jump reaches must
not be walked: its ops would rename registers that a reachable block defines
(`OptAliasRev.lean`).  The walk drops a block of `topo` whose `rev` list is
empty (and is not `0`) and deletes its edges from `rev`; a walked block
deletes edges only.  So, with `RevSound` at the start, the walk keeps
**`ARev`**: every block `rev.gen` lists for `o` is a member of `topo` that
jumps to `o` in the blocks before, the lists have no duplicates, and a listed
block that was walked already is reachable (it was walked, not dropped, since
a dropped block's edges are gone).  At the next block `o`, a listed
predecessor `p` comes before `o` in `topo` (`awr_pre`), so it was walked and
is reachable, and so is `o` (**`arev_step`**).  **`aliasWalk_reach`**: every
block the walk puts in `new` is reachable in the blocks before.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-! ## `dedupN`, `delJu` -/

theorem awr_dedup_mem : ∀ {l : List Nat} {x : Nat}, x ∈ dedupN l ↔ x ∈ l
  | [], _ => by simp [dedupN]
  | y :: l, x => by
    simp only [dedupN]
    split
    · rename_i h
      rw [awr_dedup_mem]
      constructor
      · exact fun hx => List.mem_cons_of_mem _ hx
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact awr_dedup_mem.mp h
        · exact hx
    · simp only [List.mem_cons, awr_dedup_mem]

theorem awr_dedup_nodup : ∀ l : List Nat, (dedupN l).Nodup
  | [] => List.nodup_nil
  | y :: l => by
    simp only [dedupN]
    split
    · exact awr_dedup_nodup l
    · rename_i h
      exact List.nodup_cons.mpr ⟨h, awr_dedup_nodup l⟩

theorem awr_del_sub {rev : Nat → List Nat} {k o o' p : Nat} (h : p ∈ delJu rev k o o') : p ∈ rev o' := by
  unfold delJu updA at h
  split at h
  · rename_i e; subst e; exact List.mem_of_mem_erase h
  · exact h

theorem awr_del_nodup {rev : Nat → List Nat} {k o : Nat} (h : ∀ o', (rev o').Nodup) (o' : Nat) :
    (delJu rev k o o').Nodup := by
  unfold delJu updA
  split
  · exact (h k).erase o
  · exact h o'

theorem awr_del_gone {rev : Nat → List Nat} {k o : Nat} (h : ∀ o', (rev o').Nodup) : o ∉ delJu rev k o k := by
  unfold delJu updA
  simp only [if_true]
  exact (h k).not_mem_erase

theorem awr_del_keep {rev : Nat → List Nat} {k o o' : Nat} (_h : ∀ o', (rev o').Nodup)
    (hm : o ∉ rev o') : o ∉ delJu rev k o o' := fun h' => hm (awr_del_sub h')

/-- The edges of a dropped block: deleted, and only they. -/
theorem awr_drop (o : Nat) : ∀ (js : List Jmp) (rev : Nat → List Nat), (∀ o', (rev o').Nodup) →
    let r := js.foldl (fun acc j => delJu acc j.there o) rev
    (∀ o', (r o').Nodup) ∧ (∀ o' p, p ∈ r o' → p ∈ rev o') ∧ ∀ j ∈ js, o ∉ r j.there
  | [], rev, h => ⟨h, fun _ _ hp => hp, fun _ hj => absurd hj List.not_mem_nil⟩
  | j :: js, rev, h => by
    dsimp only
    simp only [List.foldl_cons]
    have ih := awr_drop o js (delJu rev j.there o) (awr_del_nodup h)
    dsimp only at ih
    obtain ⟨i1, i2, i3⟩ := ih
    refine ⟨i1, fun o' p hp => awr_del_sub (i2 o' p hp), fun j' hj' => ?_⟩
    rcases List.mem_cons.mp hj' with rfl | hj'
    · exact fun hm => awr_del_gone h (i2 _ _ hm)
    · exact i3 j' hj'

/-- `aliasFin` only deletes edges. -/
theorem awr_fin {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r) (hn : ∀ o', (rev o').Nodup) :
    (∀ o', (r.2.1 o').Nodup) ∧ ∀ o' p, p ∈ r.2.1 o' → p ∈ rev o' := by
  have fold : ∀ go cut, (aliasFold rev o go cut).2.1 = rev ∨ (aliasFold rev o go cut).2.1 = delJu rev cut o := by
    intro go cut; unfold aliasFold; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have same : r.2.1 = rev → (∀ o', (r.2.1 o').Nodup) ∧ ∀ o' p, p ∈ r.2.1 o' → p ∈ rev o' :=
    fun e => by rw [e]; exact ⟨hn, fun _ _ hp => hp⟩
  have del1 : ∀ k, r.2.1 = delJu rev k o → (∀ o', (r.2.1 o').Nodup) ∧ ∀ o' p, p ∈ r.2.1 o' → p ∈ rev o' :=
    fun k e => by rw [e]; exact ⟨awr_del_nodup hn, fun _ _ hp => awr_del_sub hp⟩
  have byFold : ∀ go cut, r = aliasFold rev o go cut →
      (∀ o', (r.2.1 o').Nodup) ∧ ∀ o' p, p ∈ r.2.1 o' → p ∈ rev o' := fun go cut e => by
    subst e; rcases fold go cut with e | e
    · exact same e
    · exact del1 _ e
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · exact byFold _ _ e.symm
      · split at e
        · exact byFold _ _ e.symm
        · exact same (by rw [← e])
  | eqq l r' z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; exact same rfl
      · cases h; exact byFold _ _ rfl
  | brn s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · exact same (by rw [← e])
        · exact same (by rw [← e])
      · exact byFold _ _ e.symm
      · exact byFold _ _ e.symm
      · rw [← e]
        exact ⟨awr_del_nodup (awr_del_nodup hn), fun o2 p hp => awr_del_sub (awr_del_sub hp)⟩
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · exact same (by rw [← e])
      · exact byFold _ _ e.symm
      · exact byFold _ _ e.symm
  | hop t => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl
  | lti => simp only [aliasFin, Option.some.injEq] at h; subst h; exact same rfl

/-! ## The invariant of `rev.gen` -/

/-- **What `rev.gen` lists** after the prefix `pre` of `topo` was walked. -/
structure ARev (bl : Map Blob) (topo pre : List Nat) (g : AGen Map) : Prop where
  sound : ∀ o p, p ∈ g.rev o → p ∈ topo ∧ ∃ b j, HoonMap.get bl p = some b ∧ j ∈ getJmps b.fin ∧ j.there = o
  nodup : ∀ o, (g.rev o).Nodup
  reach : ∀ o p, p ∈ g.rev o → p ∈ pre → Reach bl p

/-- A member of `topo` that jumps to the next block was walked. -/
theorem awr_pre {bl : Map Blob} {pre l : List Nat} {o p : Nat} {b : Blob} {j : Jmp}
    (ht : TopoOK bl (pre ++ o :: l)) (hp : p ∈ pre ++ o :: l) (hb : HoonMap.get bl p = some b)
    (hj : j ∈ getJmps b.fin) (he : j.there = o) : p ∈ pre := by
  obtain ⟨hnd, -, -, -, hf⟩ := ht
  have hl : (pre ++ o :: l).idxOf p < (pre ++ o :: l).length := List.idxOf_lt_length_of_mem hp
  have hx : (pre ++ o :: l)[(pre ++ o :: l).idxOf p]? = some p := by
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]
  obtain ⟨k, hk, hk'⟩ := hf _ p b j hx hb hj
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk'
  have hko : (pre ++ o :: l).idxOf j.there = k := by rw [← hkv, hnd.idxOf_getElem k hkl]
  rw [he] at hko
  have hop : o ∉ pre := fun h => by
    have := (List.nodup_append.mp hnd).2.2 o h o List.mem_cons_self
    exact this rfl
  rw [idxOf_pre hop] at hko
  exact mem_pre_of_idx (l := o :: l) (by omega)

/-- The state the walk starts from. -/
def aliasInit (rev : Map (List Nat)) : AGen Map :=
  { new := HoonMap.empty, old := id, info := fun _ => none, imms := fun _ => none,
    rev := fun o => dedupN ((HoonMap.get rev o).getD []), folded := false }

theorem arev_init {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (h : RevSound bl topo rev) :
    ARev bl topo [] (aliasInit (Map := Map) rev) where
  sound := fun o p hp => h o p (awr_dedup_mem.mp hp)
  nodup := fun _ => awr_dedup_nodup _
  reach := fun _ _ _ hp => absurd hp List.not_mem_nil

/-- **One block of the walk keeps `ARev`**, and a block it walks (puts in
`new`) is reachable. -/
theorem arev_step {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {pre l : List Nat} {o : Nat}
    {g g' : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hi : ARev bl (pre ++ o :: l) pre g)
    (h : aliasBlock pick nargs bl g o = some g') :
    ARev bl (pre ++ o :: l) (pre ++ [o]) g' ∧
      ((g.rev o = [] ∧ o ≠ 0 ∧ g'.new = g.new) ∨ (Reach bl o ∧ ∃ b', g'.new = HoonMap.put g.new o b')) := by
  have hreach : (g.rev o = [] → o = 0) → Reach bl o := by
    intro h0
    by_cases e : g.rev o = []
    · rw [h0 e]; exact Reach.zero
    · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ e
      obtain ⟨hpt, b, j, hb, hj, he⟩ := hi.sound o p hp
      have hpre := awr_pre ht hpt hb hj he
      have := Reach.jump (hi.reach o p hp hpre) hb hj
      rwa [he] at this
  unfold aliasBlock at h
  dsimp only at h
  split at h
  · rename_i hd
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨n1, n2, n3⟩ := awr_drop o (getJmps b.fin) g.rev hi.nodup
    refine ⟨⟨fun o' p hp => hi.sound o' p (n2 o' p hp), n1, fun o' p hp hpre => ?_⟩, Or.inl ⟨hd.1, hd.2, rfl⟩⟩
    rcases List.mem_append.mp hpre with hpre | hpre
    · exact hi.reach o' p (n2 o' p hp) hpre
    · simp only [List.mem_singleton] at hpre
      subst hpre
      obtain ⟨-, b', j, hb', hj, he⟩ := hi.sound o' p (n2 o' p hp)
      rw [hb] at hb'; cases hb'
      exact absurd (he ▸ hp) (n3 j hj)
  · rename_i hd
    have hR : Reach bl o := hreach fun e => Classical.byContradiction fun ne => hd ⟨e, ne⟩
    obtain ⟨info, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨imms, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨edges, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨loc0, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rb, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rf, hf, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨n1, n2⟩ := awr_fin hf hi.nodup
    refine ⟨⟨fun o' p hp => hi.sound o' p (n2 o' p hp), n1, fun o' p hp hpre => ?_⟩, Or.inr ⟨hR, _, rfl⟩⟩
    rcases List.mem_append.mp hpre with hpre | hpre
    · exact hi.reach o' p (n2 o' p hp) hpre
    · simp only [List.mem_singleton] at hpre
      subst hpre; exact hR

/-- The walk from a prefix with `ARev`: every block put in `new` is
reachable or was in `new` before. -/
theorem arev_walk {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} :
    ∀ (l pre : List Nat) (g g' : AGen Map), TopoOK bl (pre ++ l) → ARev bl (pre ++ l) pre g →
      aliasWalk pick nargs bl l g = some g' →
      ∀ k, (HoonMap.get g'.new k).isSome → (HoonMap.get g.new k).isSome ∨ Reach bl k
  | [], pre, g, g', _, _, h => by
    simp only [aliasWalk, Option.some.injEq] at h; subst h
    exact fun k hk => Or.inl hk
  | o :: l, pre, g, g', ht, hi, h => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hi1, hn⟩ := arev_step ht hi h1
    have ht' : TopoOK bl ((pre ++ [o]) ++ l) := by rw [List.append_assoc]; exact ht
    have hi1' : ARev bl ((pre ++ [o]) ++ l) (pre ++ [o]) g1 := by rw [List.append_assoc]; exact hi1
    intro k hk
    rcases arev_walk l (pre ++ [o]) g1 g' ht' hi1' h k hk with hk | hk
    · rcases hn with ⟨-, -, e⟩ | ⟨hR, b', e⟩
      · rw [e] at hk; exact Or.inl hk
      · rw [e, HoonMap.get_put] at hk
        by_cases ek : k = o
        · subst ek; exact Or.inr hR
        · simp only [ek, if_false] at hk; exact Or.inl hk
    · exact Or.inr hk

/-- **Every block `+alias` keeps is reachable** in the blocks before, on
`topo` with `TopoOK` and `rev` with `RevSound`. -/
theorem aliasWalk_reach {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
    {rev : Map (List Nat)} {g' : AGen Map} (ht : TopoOK bl topo) (hr : RevSound bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g') :
    ∀ k, (HoonMap.get g'.new k).isSome → Reach bl k := by
  intro k hk
  rcases arev_walk topo [] (aliasInit rev) g' ht (arev_init hr) h k hk with hk | hk
  · simp [aliasInit, HoonMap.get_empty] at hk
  · exact hk

end Opt
end SkaModel
end Formalization
