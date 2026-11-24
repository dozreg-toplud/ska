import lemmas.Ska.OptAliasKeepsB
import lemmas.Ska.OptAliasSSAOnce

/-!
# The blocks `+alias` returns: their shape, `NoLti`, `ParNodup`, `Acyclic`, `TopoInvR`

Toward the other conjuncts of `AliasFieldSSAB` (README Gaps 12.8).  The
blocks after are `g.new` for the walk `g` of `aliasWalk` over `topo`.

* **`aw_new`**: a block of `g.new` at `o` is the block the walk made of the
  block before at `o`, which was walked (`topo = pre ++ o :: l`) and not
  dropped: its parameters, the ops `aliasBody` kept, the end `aliasFin` made.
* **`afin_nolti`**, **`afin_jmps`**: `aliasFin` makes no `%lti` of an end that
  is none, and every jump of the end after goes to a target of the end before,
  with the edge kept in `rev` when it was listed.
* **`alias_nolti`**, **`alias_parNodup`**, **`alias_targetsSub`**,
  **`alias_acyclic`**: `NoLti`, `ParNodup`, `TargetsSub` and `Acyclic` of the
  result.
* **`alias_closed`**: every jump of a block after goes to a block after (the
  edge stays listed in `rev` until the target is walked, so the target is not
  dropped).
* **`topoOK_filter`**: `TopoOK` of `topo` filtered by the blocks of a map whose
  jumps go to its own blocks and to targets of the blocks before;
  **`alias_topoInvR`**: `TopoInvR` of the result on the filtered `topo` and
  `revCfg`, as the driver asks.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-! ## The blocks of the walk -/

/-- **A block after**: the block the walk made of a walked block that was not
dropped. -/
theorem aw_new {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    (ht : TopoOK bl topo) (hr : RevSound bl topo rev) {g : AGen Map}
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) {o : Nat} {b' : Blob}
    (hb' : HoonMap.get g.new o = some b') :
    ∃ pre l g1 g2 b st0 rb rf, topo = pre ++ o :: l ∧ aliasWalk pick nargs bl pre (aliasInit rev) = some g1 ∧
      aliasBlock pick nargs bl g1 o = some g2 ∧ aliasWalk pick nargs bl l g2 = some g ∧
      ¬ (g1.rev o = [] ∧ o ≠ 0) ∧ HoonMap.get bl o = some b ∧ aStart nargs g1 o b = some st0 ∧
      aliasBody pick b.body st0 = some rb ∧ aliasFin rb.2.old rb.2.loc g1.rev g1.folded o b.fin = some rf ∧
      g2.rev = rf.2.1 ∧ b' = { par := b.par, body := rb.1, fin := rf.1 } := by
  have hR : Reach bl o := aliasWalk_reach ht hr h o (by rw [hb']; rfl)
  have ho : o ∈ topo := ht.2.2.2.1 o hR
  obtain ⟨pre, l, g1, g2, hto, h1, h2, h3⟩ := alias_start_parts (c := ⟨NeedOrd.none, 0, bl⟩) h ho
  have hnd := ht.1
  rw [hto] at hnd
  have hol : o ∉ l := fun h' => ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1 h'
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp hnd).2.2 _ h' _ List.mem_cons_self rfl
  have hfr : HoonMap.get g.new o = HoonMap.get g2.new o := ((awk_walk l g2 g h3).2 o hol).2.2
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ht.2.2.1 o ho)
  by_cases hd : g1.rev o = [] ∧ o ≠ 0
  · exfalso
    have e0 : HoonMap.get g1.new o = HoonMap.get (aliasInit (Map := Map) rev).new o :=
      ((awk_walk pre _ g1 h1).2 o hopre).2.2
    unfold aliasBlock at h2
    dsimp only at h2
    rw [if_pos hd] at h2
    obtain ⟨b2, -, rfl⟩ := Option.map_eq_some_iff.mp h2
    rw [hfr] at hb'
    simp only at hb'
    rw [e0] at hb'
    simp [aliasInit, HoonMap.get_empty] at hb'
  · obtain ⟨st0, rb, rf, hA, -, hrb, hrf, hg2⟩ := aStart_some (c := ⟨NeedOrd.none, 0, bl⟩) h2 hd hb
    refine ⟨pre, l, g1, g2, b, st0, rb, rf, hto, h1, h2, h3, hd, hb, hA, hrb, hrf, by rw [hg2], ?_⟩
    rw [hfr, hg2] at hb'
    simp only [HoonMap.get_put, if_true, Option.some.injEq] at hb'
    exact hb'.symm

/-! ## The end after -/

theorem afold_nolti {rev : Nat → List Nat} {o go cut : Nat} :
    ∀ n s z o', (aliasFold rev o go cut).1 ≠ Termin.lti n s z o' := by
  intro n s z o' e; simp [aliasFold] at e

/-- **`aliasFin` makes no `%lti`** of an end that is none. -/
theorem afin_nolti {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r)
    (hnl : ∀ n s z o', fin ≠ Termin.lti n s z o') : ∀ n s z o', r.1 ≠ Termin.lti n s z o' := by
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact afold_nolti
      · split at e
        · subst e; exact afold_nolti
        · subst e; intro n s z o' e; cases e
  | eqq l r' z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; intro n s z o' e; cases e
      · cases h; exact afold_nolti
  | brn s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · subst e; intro n s z o' e; cases e
        · subst e; intro n s z o' e; cases e
      · subst e; exact afold_nolti
      · subst e; exact afold_nolti
      · subst e; intro n s z o' e; cases e
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; intro n s z o' e; cases e
      · subst e; exact afold_nolti
      · subst e; exact afold_nolti
  | hop t => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; intro n s z o' e; cases e
  | lti n s z o' => exact absurd rfl (hnl n s z o')

theorem afold_jmps {rev : Nat → List Nat} {o go cut : Nat} {j' : Jmp} (hj' : j' ∈ getJmps (aliasFold rev o go cut).1) :
    j'.there = go ∧ (o ∈ rev j'.there → o ∈ (aliasFold rev o go cut).2.1 j'.there) := by
  simp only [aliasFold, getJmps, List.mem_singleton] at hj'
  subst hj'
  exact ⟨rfl, afn_fold_rev⟩

/-- **The jumps of the end after** go to targets of the end before, and an
edge listed in `rev` stays listed. -/
theorem afin_jmps {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} (h : aliasFin old loc rev f o fin = some r) {j' : Jmp}
    (hj' : j' ∈ getJmps r.1) : (∃ j ∈ getJmps fin, j.there = j'.there) ∧ (o ∈ rev j'.there → o ∈ r.2.1 j'.there) := by
  cases fin with
  | clq s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨z, by simp [getJmps], h1.symm⟩, h2⟩
      · split at e
        · subst e; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨o', by simp [getJmps], h1.symm⟩, h2⟩
        · subst e; exact ⟨⟨j', hj', rfl⟩, id⟩
  | eqq l r' z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · split at h
      · cases h; exact ⟨⟨j', hj', rfl⟩, id⟩
      · cases h; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨z, by simp [getJmps], h1.symm⟩, h2⟩
  | brn s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · split at e
        · subst e; exact ⟨⟨j', hj', rfl⟩, id⟩
        · subst e; exact ⟨⟨j', hj', rfl⟩, id⟩
      · subst e; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨z, by simp [getJmps], h1.symm⟩, h2⟩
      · subst e; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨o', by simp [getJmps], h1.symm⟩, h2⟩
      · subst e; simp [getJmps] at hj'
  | brz s z o' =>
    simp only [aliasFin] at h
    split at h
    · cases h
    · obtain ⟨ic, -, e⟩ := Option.map_eq_some_iff.mp h
      try dsimp only at e
      split at e
      · subst e; exact ⟨⟨j', hj', rfl⟩, id⟩
      · subst e; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨z, by simp [getJmps], h1.symm⟩, h2⟩
      · subst e; obtain ⟨h1, h2⟩ := afold_jmps hj'; exact ⟨⟨o', by simp [getJmps], h1.symm⟩, h2⟩
  | hop t =>
    simp only [aliasFin, Option.some.injEq] at h; subst h
    simp only [getJmps, List.mem_singleton] at hj'
    subst hj'
    exact ⟨⟨t, by simp [getJmps], rfl⟩, id⟩
  | lti n s z o' => simp only [aliasFin, Option.some.injEq] at h; subst h; exact ⟨⟨j', hj', rfl⟩, id⟩
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [getJmps] at hj'
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [getJmps] at hj'
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [getJmps] at hj'
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [getJmps] at hj'
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [getJmps] at hj'
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [getJmps] at hj'

/-! ## Static properties of the result -/

section
variable {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
  {g : AGen Map}

/-- **`NoLti` of the result.** -/
theorem alias_nolti (hT : TopoInvR bl topo rev) (hnl : NoLti bl)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) : NoLti g.new := by
  intro o b' hb'
  obtain ⟨_pre, _l, _g1, _g2, b, _st0, rb, rf, _e1, _e2, _e3, _e4, _e5, hb, _e7, _e8, hrf, _e10, rfl⟩ :=
    aw_new hT.1.1 hT.2 h hb'
  exact afin_nolti hrf (hnl o b hb)

/-- **`ParNodup` of the result.** -/
theorem alias_parNodup (hT : TopoInvR bl topo rev) (hpn : ParNodup bl)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) : ParNodup g.new := by
  intro o b' hb'
  obtain ⟨_pre, _l, _g1, _g2, b, _st0, rb, rf, _e1, _e2, _e3, _e4, _e5, hb, _e7, _e8, _e9, _e10, rfl⟩ :=
    aw_new hT.1.1 hT.2 h hb'
  exact hpn o b hb

/-- **The jumps of the result go to targets of the blocks before.** -/
theorem alias_targetsSub (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) :
    TargetsSub bl g.new := by
  intro o b' hb'
  obtain ⟨_pre, _l, _g1, _g2, b, _st0, rb, rf, _e1, _e2, _e3, _e4, _e5, hb, _e7, _e8, hrf, _e10, rfl⟩ :=
    aw_new hT.1.1 hT.2 h hb'
  exact ⟨b, hb, fun j' hj' => (afin_jmps hrf hj').1⟩

/-- **`Acyclic` of the result.** -/
theorem alias_acyclic (hT : TopoInvR bl topo rev) (ha : Acyclic bl)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) : Acyclic g.new :=
  acyclic_sub ha (alias_targetsSub hT h)

/-- A walk deletes from `rev` only the blocks it walks. -/
theorem rev_keep_walk : ∀ (l : List Nat) (g g' : AGen Map), aliasWalk pick nargs bl l g = some g' →
    ∀ p x, p ∈ g.rev x → p ∉ l → p ∈ g'.rev x
  | [], g, g', h, p, x, hp, _ => by simp only [aliasWalk, Option.some.injEq] at h; subst h; exact hp
  | o :: l, g, g', h, p, x, hp, hpl => by
    simp only [aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    exact rev_keep_walk l g1 g' h p x (awa_rev_keep h1 hp (fun e => hpl (e ▸ List.mem_cons_self)))
      (fun h' => hpl (List.mem_cons_of_mem _ h'))

/-- **Every jump of a block after goes to a block after**: the edge stays
listed in `rev` until its target is walked, so the target is not dropped. -/
theorem alias_closed (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g)
    {o : Nat} {b' : Blob} {j' : Jmp} (hb' : HoonMap.get g.new o = some b') (hj' : j' ∈ getJmps b'.fin) :
    (HoonMap.get g.new j'.there).isSome := by
  have ht := hT.1.1
  obtain ⟨pre, l, g1, g2, b, st0, rb, rf, hto, h1, h2, h3, _e5, hb, _e7, _e8, hrf, hrev, rfl⟩ := aw_new ht hT.2 h hb'
  obtain ⟨⟨j, hj, hjt⟩, hkeep⟩ := afin_jmps hrf hj'
  have hoT : o ∈ topo := by rw [hto]; simp
  have hnd := ht.1
  rw [hto] at hnd
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp hnd).2.2 _ h' _ List.mem_cons_self rfl
  have h0 : o ∈ (aliasInit (Map := Map) rev).rev j.there := awr_dedup_mem.mpr (hT.1.2 o b j hoT hb hj)
  have h1r : o ∈ g1.rev j'.there := by rw [← hjt]; exact rev_keep_walk pre _ g1 h1 o _ h0 hopre
  have h2r : o ∈ g2.rev j'.there := by rw [hrev]; exact hkeep h1r
  -- the target is walked after `o`
  have hjT : j.there ∈ topo := (awi_fwd ht hoT hb hj).1
  obtain ⟨pret, lt, g1t, g2t, htopo, h1t, h2t, h3t⟩ := alias_start_parts (c := ⟨NeedOrd.none, 0, bl⟩) h hjT
  have hopret : o ∈ pret := awr_pre (htopo ▸ ht) (htopo ▸ hoT) hb hj rfl
  obtain ⟨A, mid, rfl⟩ := List.append_of_mem hopret
  have hnd0 : topo.Nodup := ht.1
  have hoA : o ∉ A := by
    intro hm
    rw [htopo] at hnd0
    exact (List.nodup_append.mp (List.nodup_append.mp hnd0).1).2.2 o hm o List.mem_cons_self rfl
  have e1 : A ++ o :: (mid ++ j.there :: lt) = pre ++ o :: l := by rw [← hto, htopo]; simp
  obtain ⟨rfl, hl⟩ := split_unique A pre _ _ hoA hopre e1
  have hw2 : aliasWalk pick nargs bl (A ++ [o]) (aliasInit rev) = some g2 := by
    rw [awa_walk_append, h1]; simp only [Option.bind_some, aliasWalk, h2]
  have hmid : aliasWalk pick nargs bl mid g2 = some g1t := by
    have e := h1t
    rw [show A ++ o :: mid = (A ++ [o]) ++ mid by simp, awa_walk_append, hw2, Option.bind_some] at e
    exact e
  have homid : o ∉ mid := by
    intro hm
    rw [← hl] at hnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (List.mem_append_left _ hm)
  have h3r : o ∈ g1t.rev j.there := by rw [hjt]; exact rev_keep_walk mid g2 g1t hmid o _ h2r homid
  have hne : ¬ (g1t.rev j.there = [] ∧ j.there ≠ 0) := fun e => by rw [e.1] at h3r; cases h3r
  obtain ⟨bt, hbt⟩ := Option.isSome_iff_exists.mp (ht.2.2.1 _ hjT)
  obtain ⟨_st, _rb, _rf, _f1, _f2, _f3, _f4, hg4⟩ := aStart_some (c := ⟨NeedOrd.none, 0, bl⟩) h2t hne hbt
  have htlt : j.there ∉ lt := by
    intro hm
    rw [htopo] at hnd0
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd0).2.1).1 hm
  rw [← hjt, ((awk_walk lt g2t g h3t).2 _ htlt).2.2, hg4]
  simp only [HoonMap.get_put, if_true]; rfl

end

/-! ## `TopoOK` of the filtered `topo` -/

theorem idxOf_filter_lt (p : Nat → Bool) : ∀ (L : List Nat) {a b : Nat}, a ∈ L → p a = true →
    L.idxOf a < L.idxOf b → (L.filter p).idxOf a < (L.filter p).idxOf b
  | [], a, b, ha, _, _ => absurd ha List.not_mem_nil
  | x :: L, a, b, ha, hpa, hlt => by
    by_cases hxa : x = a
    · subst hxa
      have hxb : x ≠ b := fun e => by subst e; simp at hlt
      rw [List.filter_cons_of_pos hpa, List.idxOf_cons_self, List.idxOf_cons, beq_false_of_ne hxb]
      simp
    · have hxb : x ≠ b := fun e => by subst e; simp at hlt
      have ha' : a ∈ L := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
      rw [List.idxOf_cons, List.idxOf_cons, beq_false_of_ne hxa, beq_false_of_ne hxb] at hlt
      simp only [cond_false] at hlt
      have ih := idxOf_filter_lt p L (b := b) ha' hpa (by omega)
      by_cases hpx : p x = true
      · rw [List.filter_cons_of_pos hpx, List.idxOf_cons, List.idxOf_cons, beq_false_of_ne hxa, beq_false_of_ne hxb]
        simp only [cond_false]; omega
      · rw [List.filter_cons_of_neg hpx]; exact ih

/-- **`TopoOK` of `topo` filtered** by the blocks of a map whose blocks jump
to targets of the blocks before and to its own blocks, and that has block
`0`. -/
theorem topoOK_filter {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo) (hs : TargetsSub bl bl')
    (h0 : (HoonMap.get bl' 0).isSome)
    (hcl : ∀ o b' j', HoonMap.get bl' o = some b' → j' ∈ getJmps b'.fin → (HoonMap.get bl' j'.there).isSome) :
    TopoOK bl' (topo.filter fun o => (HoonMap.get bl' o).isSome) := by
  have hreach : ∀ o, Reach bl' o → (HoonMap.get bl' o).isSome := by
    intro o h
    induction h with
    | zero => exact h0
    | jump _ hb hj _ => exact hcl _ _ _ hb hj
  have hnd' : (topo.filter fun o => (HoonMap.get bl' o).isSome).Nodup := ht.1.filter _
  refine ⟨hnd', ?_, fun o ho => (List.mem_filter.mp ho).2,
    fun o h => List.mem_filter.mpr ⟨ht.2.2.2.1 o (reach_sub hs h), hreach o h⟩, ?_⟩
  · obtain ⟨-, hh, -⟩ := ht
    cases topo with
    | nil => cases hh
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [List.filter_cons_of_pos (p := fun o => (HoonMap.get bl' o).isSome) h0]; rfl
  · intro i o b' j' hi hb' hj'
    obtain ⟨b, hb, hjs⟩ := hs o b' hb'
    obtain ⟨j, hj, hjt⟩ := hjs j' hj'
    have hoF := List.mem_of_getElem? hi
    have hoT := (List.mem_filter.mp hoF).1
    obtain ⟨-, hlt⟩ := awi_fwd ht hoT hb hj
    rw [hjt] at hlt
    have hlt' := idxOf_filter_lt (fun o => (HoonMap.get bl' o).isSome) topo hoT (List.mem_filter.mp hoF).2 hlt
    obtain ⟨hil, hiv⟩ := List.getElem?_eq_some_iff.mp hi
    have hio : (topo.filter fun o => (HoonMap.get bl' o).isSome).idxOf o = i := by
      rw [← hiv]; exact hnd'.idxOf_getElem i hil
    have htF : j'.there ∈ topo.filter fun o => (HoonMap.get bl' o).isSome :=
      List.mem_filter.mpr ⟨by rw [← hjt]; exact (awi_fwd ht hoT hb hj).1, hcl o b' j' hb' hj'⟩
    have hlen := List.idxOf_lt_length_of_mem htF
    refine ⟨_, by rw [← hio]; exact hlt', ?_⟩
    rw [List.getElem?_eq_getElem hlen, List.getElem_idxOf hlen]

/-- **`TopoInvR` of the result** on the filtered `topo` and `revCfg`, as the
driver asks. -/
theorem alias_topoInvR {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
    {rev : Map (List Nat)} (hT : TopoInvR bl topo rev) {g : AGen Map}
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) :
    TopoInvR g.new (topo.filter fun o => (HoonMap.get g.new o).isSome)
      (revCfg g.new (topo.filter fun o => (HoonMap.get g.new o).isSome)) := by
  obtain ⟨_l, _g2, _b0, _st0, _rb, _rf, _e1, _e2, _e3, _e4, _e5, _e6, _e7, hg0⟩ := alias_zero hT.1.1 h
  exact ⟨topoInv_revCfg (topoOK_filter hT.1.1 (alias_targetsSub hT h) (by rw [hg0]; rfl)
    (fun o b' j' hb' hj' => alias_closed hT h hb' hj')), revCfg_sound _ _⟩

/-! ## What is left of the field -/

/-- **What is left of `AliasFieldSSAB`** for the model: the static
properties of the result that need the walk invariant in a form free of
executions (the check of `+eval-pass` on the renamed arguments, `DownPar`,
bracketed hints with the keys renamed, single assignment). -/
def AliasRestSSAB (Map : Type → Type) [HoonMap Map] [MapKeys Map] (pick : List Nat → Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev (g : AGen Map), DInvS bl → TopoInvR bl topo rev →
    aliasWalk pick n bl topo (aliasInit rev) = some g →
    PassOK g.new ∧ DownPar g.new ∧ (∃ K, TrimBr g.new K) ∧ AliasSSAB g.new

/-- **`AliasFieldSSAB` from what is left**: `KeepsB`, `ParNodup`, `Acyclic`,
`NoLti` and `TopoInv` of the filtered `topo` are proved. -/
theorem aliasFieldSSAB_of {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    (H : AliasRestSSAB Map pick) : AliasFieldSSAB Map pick := by
  intro n bl topo rev f bl' hdt hs hnl hti hrs h
  have hD : DInvS bl := ⟨hdt, hs, hnl⟩
  have hT : TopoInvR bl topo rev := ⟨hti, hrs⟩
  have hk := alias_keepsB hpick hD hT h
  unfold aliasM at h
  obtain ⟨g, hg, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain ⟨hpo, hdp, hK, hss⟩ := H n bl topo rev g hD hT hg
  exact ⟨hk, ⟨⟨⟨alias_parNodup hT hdt.1.1.1 hg, hpo⟩, alias_acyclic hT hdt.1.2.1 hg, hdp⟩, hK⟩, hss,
    alias_nolti hT hnl hg, (alias_topoInvR hT hg).1⟩

/-- **`+optimize` with the model of `+alias` keeps the code** on blocks with
`DInvS`, given `hpick` and what is left of the field (`AliasRestSSAB`). -/
theorem optimize_keeps_alias {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (H : AliasRestSSAB Map pick)
    (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints) (hs : P.switch = switchChains sfuel)
    {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps_ssaD (driverRestSSA_of_aliasM (aliasFieldSSAB_of hpick H) ha ht hs) hb h

end Opt
end SkaModel
end Formalization
