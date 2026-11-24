import lemmas.Ska.OptAliasPass

/-!
# `TrimBr` of the blocks `+alias` returns

`+alias` keeps every hint op and renames the registers of the keys of trace
hints (`%hdp`, `%hde` of `%spot`, `%mean`; `%hmp`, `%hme`) by `old` at the
op.  The bracketing after is the bracketing before with every key renamed by
the final `old` (`renKey`): `K' o = (K o).map (Option.map (renKey g.old))`.
Equality of keys is kept by any renaming, so a pop that found its key on top
before finds it after (the rename may merge keys, which `TrimBr` allows: see
the header of `OptAliasField.lean`).

What makes one renaming fit every block: a register of a key is read at the
op that pushes or pops it, and `old` changes at a register only at its
definitions, which come before every read of it except the dead fills of the
reading block, after the read (**`trb_defs`**).  So the `old` at a hint op of
a block with no dead fill, the `old` at the end of its body and the final
`old` agree on the key's registers; in a block with a dead fill (which ends in
`%bom` and has no successor) they agree up to the first dead fill, after which
only `%imm` ops follow.  A key on the stack at the start of a block was pushed
in a block before it in `topo` (**`trb_origin`**).

* **`brOp_rename`**, **`abr_body`**: the stack after a renamed body is the
  stack before renamed, when the keys' registers are not written later in the
  body.
* **`alias_trimBr`**: `TrimBr` of the result.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- A key with its registers renamed. -/
def renKey (f : Nat → Nat) : TKey → TKey
  | TKey.clue n p => TKey.clue n (f p)
  | TKey.defer a v fm => TKey.defer a (v.map f) fm
  | TKey.konst n fm => TKey.konst n fm

/-- The registers of a key. -/
def keyRegs : TKey → List Nat
  | TKey.clue _ p => [p]
  | TKey.defer _ v _ => v
  | TKey.konst _ _ => []

/-- The registers of the key of an op. -/
def opKeyRegs (op : Pole) : List Nat :=
  match traceKey op with
  | some (_, k) => keyRegs k
  | none => []

theorem renKey_congr {f f' : Nat → Nat} {k : TKey} (h : ∀ x ∈ keyRegs k, f x = f' x) : renKey f k = renKey f' k := by
  cases k with
  | clue n p => simp only [renKey, keyRegs, List.mem_singleton] at h ⊢; rw [h p rfl]
  | defer a v fm => simp only [renKey, keyRegs] at h ⊢; rw [List.map_congr_left h]
  | konst => rfl

/-- **One op renamed acts on the renamed stack as the op before.** -/
theorem brOp_rename {g g1 : List (Option TKey)} {op : Pole} (h : brOp g op = some g1) {σ f : Nat → Nat}
    (hk : ∀ x ∈ opKeyRegs op, σ x = f x) :
    brOp (g.map (Option.map (renKey f))) (renameP σ op) = some (g1.map (Option.map (renKey f))) := by
  cases op
  case hdp n p fm =>
    simp only [renameP]
    by_cases hn : n = Tag.spot ∨ n = Tag.mean
    · have hp : σ p = f p := hk p (by simp [opKeyRegs, traceKey, hn, keyRegs])
      simp only [brOp, traceKey, hn, if_true, Option.some.injEq] at h ⊢
      subst h
      simp [renKey, hp]
    · simp only [brOp, traceKey, hn, if_false] at h ⊢
      split at h
      · rename_i hs; cases h; simp [hs]
      · rename_i hs; cases h; simp [hs]
  case hde n p fm =>
    simp only [renameP]
    by_cases hn : n = Tag.spot ∨ n = Tag.mean
    · have hp : σ p = f p := hk p (by simp [opKeyRegs, traceKey, hn, keyRegs])
      simp only [brOp, traceKey, hn, if_true] at h ⊢
      split at h
      · rename_i k' g0
        split at h
        · rename_i e
          cases h
          subst e
          simp [renKey, hp]
        · cases h
      · cases h
    · simp only [brOp, traceKey, hn, if_false] at h ⊢
      split at h
      · rename_i hs
        split at h
        · rename_i g0 _; cases h; simp [hs]
        · cases h
      · rename_i hs; cases h; simp [hs]
  case hmp a v fm =>
    have hv : v.map σ = v.map f := List.map_congr_left fun x hx => hk x (by simp [opKeyRegs, traceKey, keyRegs, hx])
    simp only [renameP, brOp, traceKey, Option.some.injEq] at h ⊢
    subst h
    simp [renKey, hv]
  case hme a v fm =>
    have hv : v.map σ = v.map f := List.map_congr_left fun x hx => hk x (by simp [opKeyRegs, traceKey, keyRegs, hx])
    simp only [renameP, brOp, traceKey] at h ⊢
    split at h
    · rename_i k' g0
      split at h
      · rename_i e
        cases h
        subst e
        simp [renKey, hv]
      · cases h
    · cases h
  case hcp n fm =>
    simp only [renameP, brOp, traceKey, Option.some.injEq] at h ⊢
    subst h
    simp [renKey]
  case hce n fm =>
    simp only [renameP, brOp, traceKey] at h ⊢
    split at h
    · rename_i k' g0
      split at h
      · rename_i e
        cases h
        subst e
        simp [renKey]
      · cases h
    · cases h
  all_goals (simp only [renameP, brOp, traceKey, Option.some.injEq] at h ⊢; subst h; rfl)

/-- An op the walk drops has no frame. -/
theorem aop_drop_noFrame {pick : List Nat → Nat} {st st2 : ABody} {op : Pole}
    (h : aliasOp pick st op = some (none, st2)) : NoFrame op := by
  cases op
  case hsp => simp [aliasOp] at h
  case hse => simp [aliasOp] at h
  case hdp => simp [aliasOp] at h
  case hde => simp [aliasOp] at h
  case hmp => simp [aliasOp] at h
  case hme => simp [aliasOp] at h
  case hcp => simp [aliasOp] at h
  case hce => simp [aliasOp] at h
  all_goals (intro g; simp [brOp, traceKey])

/-- **The renamed body acts on the renamed stack as the body before**, with
the renaming the state at the end of the body, when no register of a key is
written at or after its op. -/
theorem abr_body {pick : List Nat → Nat} : ∀ (ops : List Pole) (st : ABody) (out : List Pole) (st' : ABody)
    (gk gk' : List (Option TKey)), aliasBody pick ops st = some (out, st') → brBody gk ops = some gk' →
    (∀ k op x, ops[k]? = some op → x ∈ opKeyRegs op → x ∉ (ops.drop k).filterMap aliasDst) →
    brBody (gk.map (Option.map (renKey st'.old))) out = some (gk'.map (Option.map (renKey st'.old)))
  | [], st, out, st', gk, gk', h, hb, _ => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [brBody, Option.some.injEq] at hb
    subst hb; rfl
  | op :: l, st, out, st', gk, gk', h, hb, hk => by
    have hall := h
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [brBody] at hb
    obtain ⟨g1, hg1, hb⟩ := Option.bind_eq_some_iff.mp hb
    have ih := abr_body l st1 out2 st2 g1 gk' h2 hb (fun k op' x hk' hx => by
      have := hk (k + 1) op' x (by simpa using hk') hx
      simpa using this)
    cases res with
    | none =>
      have e : g1 = gk := by have := aop_drop_noFrame h1 gk; rw [this] at hg1; exact (Option.some.inj hg1).symm
      subst e
      simpa using ih
    | some op' =>
      have e := aop_rename h1
      subst e
      have hσ : ∀ x ∈ opKeyRegs op, st.old x = st2.old x := by
        intro x hx
        exact (awk_body_old (op :: l) st _ st2 hall x (by simpa using hk 0 op x rfl hx)).symm
      simp only [Option.toList_some, List.cons_append, List.nil_append, brBody]
      rw [brOp_rename hg1 hσ, Option.bind_some]
      exact ih

/-- The ops the walk keeps of a body are ops of the body renamed. -/
theorem abody_kept {pick : List Nat → Nat} : ∀ (ops : List Pole) (st : ABody) (out : List Pole) (st' : ABody),
    aliasBody pick ops st = some (out, st') → ∀ op' ∈ out, ∃ op ∈ ops, ∃ σ, op' = renameP σ op
  | [], st, out, st', h => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun _ h => absurd h List.not_mem_nil
  | op :: l, st, out, st', h => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    intro op' hm
    rcases List.mem_append.mp hm with hm | hm
    · cases res with
      | none => cases hm
      | some o1 =>
        simp only [Option.toList_some, List.mem_singleton] at hm
        subst hm
        exact ⟨op, List.mem_cons_self, st.old, aop_rename h1⟩
    · obtain ⟨op0, hop0, σ, e⟩ := abody_kept l st1 out2 st2 h2 op' hm
      exact ⟨op0, List.mem_cons_of_mem _ hop0, σ, e⟩

/-! ## Where the registers of keys are written -/

theorem opKeyRegs_reads {op : Pole} {x : Nat} (h : x ∈ opKeyRegs op) : x ∈ aliasReads op := by
  cases op
  case hdp n p fm =>
    by_cases hn : n = Tag.spot ∨ n = Tag.mean
    · simp only [opKeyRegs, traceKey, hn, if_true, keyRegs, List.mem_singleton] at h
      subst h; simp [aliasReads, aliasDst, poleRegs]
    · simp [opKeyRegs, traceKey, hn] at h
  case hde n p fm =>
    by_cases hn : n = Tag.spot ∨ n = Tag.mean
    · simp only [opKeyRegs, traceKey, hn, if_true, keyRegs, List.mem_singleton] at h
      subst h; simp [aliasReads, aliasDst, poleRegs]
    · simp [opKeyRegs, traceKey, hn] at h
  case hmp a v fm => simpa [opKeyRegs, traceKey, keyRegs, aliasReads, aliasDst, poleRegs] using h
  case hme a v fm => simpa [opKeyRegs, traceKey, keyRegs, aliasReads, aliasDst, poleRegs] using h
  all_goals simp [opKeyRegs, traceKey, keyRegs] at h

theorem trb_readAt {b : Blob} {k : Nat} {op : Pole} (hk : b.body[k]? = some op) {x : Nat}
    (hx : x ∈ opKeyRegs op) : ReadAt b k x :=
  Or.inl (by rw [List.head?_drop, hk]; exact opKeyRegs_reads hx)

/-- The stack after a body: what it started with, or a key one of its ops
pushes. -/
theorem brOp_origin {g g1 : List (Option TKey)} {op : Pole} (h : brOp g op = some g1) {key : TKey}
    (hk : some key ∈ g1) : some key ∈ g ∨ traceKey op = some (true, key) := by
  unfold brOp at h
  split at h
  · rename_i k e
    cases h
    rcases List.mem_cons.mp hk with e2 | e2
    · cases e2; exact Or.inr e
    · exact Or.inl e2
  · split at h
    · split at h
      · cases h; exact Or.inl (List.mem_cons_of_mem _ hk)
      · cases h
    · cases h
  · split at h
    · split at h
      · cases h
        rcases List.mem_cons.mp hk with e2 | e2
        · cases e2
        · exact Or.inl e2
      · cases h; exact Or.inl hk
    · split at h
      · split at h
        · cases h; exact Or.inl (List.mem_cons_of_mem _ hk)
        · cases h
      · cases h; exact Or.inl hk
    · cases h; exact Or.inl hk

theorem brb_origin : ∀ (g : List (Option TKey)) (l : List Pole) (g' : List (Option TKey)), brBody g l = some g' →
    ∀ key, some key ∈ g' → some key ∈ g ∨ ∃ (i : Nat) (op : Pole), l[i]? = some op ∧ traceKey op = some (true, key)
  | g, [], g', h, key, hk => by
    simp only [brBody, Option.some.injEq] at h; subst h; exact Or.inl hk
  | g, op :: l, g', h, key, hk => by
    simp only [brBody] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    rcases brb_origin g1 l g' h key hk with hk | ⟨i, op', hi, he⟩
    · rcases brOp_origin h1 hk with hk | he
      · exact Or.inl hk
      · exact Or.inr ⟨0, op, rfl, he⟩
    · exact Or.inr ⟨i + 1, op', by simpa using hi, he⟩

/-- A least witness. -/
theorem trb_min {P : Nat → Prop} (h : ∃ k, P k) : ∃ k, P k ∧ ∀ j, j < k → ¬ P j := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hm : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hpj⟩ := hm; exact ih j hj hpj
    · exact ⟨k, hk, fun j hj hpj => hm ⟨j, hj, hpj⟩⟩

theorem trb_idx_l {pre l : List Nat} {o o' : Nat} (hnd : (pre ++ o :: l).Nodup) (ho' : o' ∈ l) :
    (pre ++ o :: l).idxOf o < (pre ++ o :: l).idxOf o' := by
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp hnd).2.2 o h' o List.mem_cons_self rfl
  have ho'pre : o' ∉ pre := fun h' => (List.nodup_append.mp hnd).2.2 o' h' o' (List.mem_cons_of_mem _ ho') rfl
  have hoo' : o ≠ o' := fun e => ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1 (e ▸ ho')
  rw [idxOf_pre hopre, List.idxOf_append, if_neg ho'pre, List.idxOf_cons, beq_false_of_ne hoo']
  simp only [cond_false]
  omega

section
variable [MapKeys Map]

/-- **Where a register read at a place is written**: every definition of it in
a reachable block is an earlier op of the reading block, a definition in a
block before it in `topo`, or a dead fill of the reading block (after the
read). -/
theorem trb_defs {bl : Map Blob} (hS : AliasSSAB bl) {T : List Nat} (ht : TopoOK bl T)
    {y i x : Nat} {by_ : Blob} (hRy : Reach bl y) (hby : HoonMap.get bl y = some by_) (hread : ReadAt by_ i x)
    {o' k' : Nat} {b' : Blob} {op' : Pole} (hR' : Reach bl o') (hb' : HoonMap.get bl o' = some b')
    (hk' : b'.body[k']? = some op') (hd' : aliasDst op' = some x) :
    (o' = y ∧ (k' < i ∨ DeadFill bl x y k')) ∨ T.idxOf o' < T.idxOf y := by
  by_cases hdf : DeadFill bl x o' k'
  · obtain ⟨_, _, _, _, _, hrd⟩ := id hdf
    obtain ⟨e, -⟩ := hrd y by_ i hRy hby hread
    subst e
    exact Or.inl ⟨rfl, Or.inr hdf⟩
  · have hlive : LiveDef bl x (o', some k') := ⟨hR', ⟨b', op', hb', hk', hd'⟩, fun i hi => by cases hi; exact hdf⟩
    have hall : x ∈ allDefs bl :=
      bdef_allDefs hb' (List.mem_append_right _ (List.mem_filterMap.mpr ⟨op', List.mem_of_getElem? hk', hd'⟩))
    obtain ⟨p, hπ⟩ := awi_reach_bpath hRy
    rcases hS.2 y p by_ hπ hby i x hread hall with hd | hd | ⟨o'', ho'', b'', hb'', hd⟩
    · have e := hS.1 x _ _ hlive (awi_par_live hRy hby hd); simp at e
    · obtain ⟨k'', op'', hk'', hd''⟩ := bdef_idx hd
      rw [List.getElem?_take] at hk''
      split at hk''
      · rename_i hki
        have hl2 : LiveDef bl x (y, some k'') := ⟨hRy, ⟨by_, op'', hby, hk'', hd''⟩, fun i2 hi2 hdf2 => by
          cases hi2
          obtain ⟨_, _, _, _, _, hrd⟩ := hdf2
          have := (hrd y by_ i hRy hby hread).2
          omega⟩
        have e := hS.1 x _ _ hlive hl2
        simp only [Prod.mk.injEq, Option.some.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact Or.inl ⟨rfl, Or.inl hki⟩
      · cases hk''
    · have hR'' := ssk_bpath_reach hπ o'' (List.mem_cons_of_mem _ ho'')
      obtain ⟨b3, j3, hb3, hj3⟩ := bdef_jumps hπ rfl o'' ho''
      rw [hb''] at hb3; cases hb3
      rcases List.mem_append.mp hd with hd | hd
      · have e := hS.1 x _ _ hlive (awi_par_live hR'' hb'' hd); simp at e
      · obtain ⟨i3, op3, hi3, he3⟩ := bdef_idx hd
        have e := hS.1 x _ _ hlive (awi_jump_live hR'' hb'' hj3 hi3 he3)
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Or.inr ((awi_bpath_idx ht hπ rfl).2 o' ho'')

/-- **A key on the stack at the start of a reachable block** was pushed by an
op of a reachable block before it in `topo`. -/
theorem trb_origin {bl : Map Blob} {K : Nat → List (Option TKey)} (hK : TrimBr bl K) {T : List Nat}
    (ht : TopoOK bl T) : ∀ x, Reach bl x → ∀ key, some key ∈ K x → ∃ (y : Nat) (b : Blob) (i : Nat) (op : Pole), Reach bl y ∧
      T.idxOf y < T.idxOf x ∧ HoonMap.get bl y = some b ∧ b.body[i]? = some op ∧ traceKey op = some (true, key) := by
  intro x hx
  induction hx with
  | zero => intro key hk; rw [hK.1] at hk; cases hk
  | @jump q b j hRq hb hj ih =>
    intro key hk
    obtain ⟨g, hg, hjs⟩ := hK.2 q b hRq hb
    rw [hjs j hj] at hk
    have hqT := ht.2.2.2.1 q hRq
    have hlt := (awi_fwd ht hqT hb hj).2
    rcases brb_origin _ _ _ hg key hk with hk | ⟨i, op, hi, he⟩
    · obtain ⟨y, b', i', op', hRy, hly, hb', hi', he'⟩ := ih key hk
      exact ⟨y, b', i', op', hRy, by omega, hb', hi', he'⟩
    · exact ⟨q, b, i, op, hRq, hlt, hb, hi, he⟩

end

/-! ## `TrimBr` of the result -/

section
variable [MapKeys Map] {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
  {rev : Map (List Nat)} {g : AGen Map}

theorem trb_map_congr {f f' : Nat → Nat} {L : List (Option TKey)}
    (h : ∀ key, some key ∈ L → ∀ x ∈ keyRegs key, f x = f' x) :
    L.map (Option.map (renKey f)) = L.map (Option.map (renKey f')) := by
  apply List.map_congr_left
  intro a ha
  cases a with
  | none => rfl
  | some key => simp only [Option.map_some]; rw [renKey_congr (h key ha)]

theorem trb_opKeyRegs {op : Pole} {key : TKey} {b : Bool} (he : traceKey op = some (b, key)) {x : Nat}
    (hx : x ∈ keyRegs key) : x ∈ opKeyRegs op := by
  simp only [opKeyRegs, he]; exact hx

/-- **`TrimBr` of the result**, with the keys renamed by the final `old`. -/
theorem alias_trimBr (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) : ∃ K, TrimBr g.new K := by
  obtain ⟨K, hK⟩ := hD.1.2
  have hS : AliasSSAB bl := hD.2.1
  have ht := hT.1.1
  refine ⟨fun o => (K o).map (Option.map (renKey g.old)), trimBr_of' (bl := bl) (by simp only [hK.1, List.map_nil]) ?_⟩
  intro o b' hR hb'
  obtain ⟨pre, l, g1, g2, b, st0, rb, rf, hto, h1, h2, h3, hne, hb, hA0, hrb, hrf, -, hbe⟩ := aw_new ht hT.2 h hb'
  obtain ⟨st0', rb', rf', hA0', -, hrb', hrf', hg2⟩ := aStart_some (c := ⟨NeedOrd.none, 0, bl⟩) h2 hne hb
  rw [hA0] at hA0'; cases hA0'
  rw [hrb] at hrb'; cases hrb'
  rw [hrf] at hrf'; cases hrf'
  subst hbe
  obtain ⟨g0, hg0, hjs⟩ := hK.2 o b hR hb
  have hI := sst_at hpick hD hT hto h1 h2
  have hnd : (pre ++ o :: l).Nodup := hto ▸ ht.1
  -- a register read at a block up to `o` is not written after `o`'s body
  have hlate : ∀ x y by_ i, Reach bl y → HoonMap.get bl y = some by_ → ReadAt by_ i x →
      (y = o ∨ topo.idxOf y < topo.idxOf o) → g.old x = rb.2.old x := by
    intro x y by_ i hRy hby hread hy
    have ht' : TopoOK bl ((pre ++ [o]) ++ l) := by
      rw [List.append_assoc, List.singleton_append, ← hto]; exact ht
    have hI' : ARev bl ((pre ++ [o]) ++ l) (pre ++ [o]) g2 := by
      rw [List.append_assoc, List.singleton_append, ← hto]; exact hI.rev
    rw [awi_frame_walk l (pre ++ [o]) g2 g ht' hI' h3 x ?_, hg2]
    intro o' ho' hR' b2 hb2 hm
    obtain ⟨k', op', hk', hd'⟩ := bdef_idx hm
    have hlo := trb_idx_l hnd ho'
    rw [← hto] at hlo
    rcases trb_defs hS ht hRy hby hread hR' hb2 hk' hd' with ⟨e, -⟩ | hlt
    · subst e
      rcases hy with e | hy
      · subst e; omega
      · omega
    · rcases hy with e | hy
      · subst e; omega
      · omega
  -- the keys at the start of `o`
  have hKo : ∀ key, some key ∈ K o → ∀ x ∈ keyRegs key, g.old x = rb.2.old x := by
    intro key hk x hx
    obtain ⟨y, by_, i, op, hRy, hly, hby, hi, he⟩ := trb_origin hK ht o hR key hk
    exact hlate x y by_ i hRy hby (trb_readAt hi (trb_opKeyRegs he hx)) (Or.inr hly)
  -- no register of `K o` is written in `o`
  have hKnd : ∀ key, some key ∈ K o → ∀ x ∈ keyRegs key, x ∉ b.body.filterMap aliasDst := by
    intro key hk x hx hm
    obtain ⟨y, by_, i, op, hRy, hly, hby, hi, he⟩ := trb_origin hK ht o hR key hk
    obtain ⟨k', op', hk', hd'⟩ := bdef_idx hm
    rcases trb_defs hS ht hRy hby (trb_readAt hi (trb_opKeyRegs he hx)) hR hb hk' hd' with ⟨e, -⟩ | hlt
    · subst e; omega
    · omega
  -- a key register of an op of `o` before every dead fill is not written later in the prefix
  have hpre : ∀ m, (∀ k r, k < m → ¬ DeadFill bl r o k) → ∀ k op x, (b.body.take m)[k]? = some op →
      x ∈ opKeyRegs op → x ∉ ((b.body.take m).drop k).filterMap aliasDst := by
    intro m hm k op x hk hx hmem
    rw [List.getElem?_take] at hk
    split at hk
    · rename_i hkm
      obtain ⟨i', op', hi', hd'⟩ := bdef_idx hmem
      rw [List.getElem?_drop, List.getElem?_take] at hi'
      split at hi'
      · rename_i hlt'
        rcases trb_defs hS ht hR hb (trb_readAt hk hx) hR hb hi' hd' with ⟨-, hc | hc⟩ | hc
        · omega
        · exact hm _ _ hlt' hc
        · omega
      · cases hi'
    · cases hk
  by_cases hfill : ∃ k r, DeadFill bl r o k
  · -- a block with a dead fill: it ends in `%bom`
    obtain ⟨m, ⟨r0, hm0⟩, hmin⟩ := trb_min (P := fun k => ∃ r, DeadFill bl r o k) (by
      obtain ⟨k, r, hk⟩ := hfill; exact ⟨k, r, hk⟩)
    obtain ⟨b5, hb5, ⟨u, hu⟩, -, himm, -⟩ := hm0
    rw [hb] at hb5; cases hb5
    have hnf : ∀ k r, k < m → ¬ DeadFill bl r o k := fun k r hk hd => hmin k hk ⟨r, hd⟩
    have hrf1 : rf.1 = Termin.bom u := by
      rw [hu] at hrf; simp only [aliasFin, Option.some.injEq] at hrf; rw [← hrf]
    have hrb2 := hrb
    rw [← List.take_append_drop m b.body, aliasBody_append] at hrb2
    obtain ⟨⟨outa, sta⟩, ha, hrb2⟩ := Option.bind_eq_some_iff.mp hrb2
    obtain ⟨⟨outb, st'⟩, hbb, e⟩ := Option.map_eq_some_iff.mp hrb2
    rw [← List.take_append_drop m b.body, brBody_append] at hg0
    obtain ⟨gm, hgm, -⟩ := Option.bind_eq_some_iff.mp hg0
    have hA := abr_body _ st0 outa sta (K o) gm ha hgm (hpre m hnf)
    have hst : ∀ key, some key ∈ K o → ∀ x ∈ keyRegs key, g.old x = sta.old x := by
      intro key hk x hx
      rw [hKo key hk x hx, ← e]
      exact awk_body_old _ sta outb st' hbb x (fun hm => hKnd key hk x hx
        (((List.drop_sublist m b.body).filterMap aliasDst).subset hm))
    have hout : ∀ op' ∈ outb, NoFrame op' := by
      intro op' hop'
      obtain ⟨op0, hop0, σ, rfl⟩ := abody_kept _ sta outb st' hbb op' hop'
      obtain ⟨n, d, rfl⟩ := himm op0 hop0
      intro gg; rfl
    refine ⟨gm.map (Option.map (renKey sta.old)), ?_, fun j hj => ?_⟩
    · rw [← e]
      dsimp only
      rw [brBody_append, trb_map_congr hst, hA, Option.bind_some]
      exact brBody_noFrame _ _ hout
    · rw [← e, hrf1] at hj
      simp [getJmps] at hj
  · -- a block with no dead fill: the whole body
    have hnf : ∀ k r, k < b.body.length → ¬ DeadFill bl r o k := fun k r _ hd => hfill ⟨k, r, hd⟩
    have hpre' := hpre b.body.length hnf
    rw [List.take_length] at hpre'
    have hA := abr_body _ st0 rb.1 rb.2 (K o) g0 hrb hg0 hpre'
    have hg0k : ∀ key, some key ∈ g0 → ∀ x ∈ keyRegs key, g.old x = rb.2.old x := by
      intro key hk x hx
      rcases brb_origin _ _ _ hg0 key hk with hk | ⟨i, op, hi, he⟩
      · exact hKo key hk x hx
      · exact hlate x o b i hR hb (trb_readAt hi (trb_opKeyRegs he hx)) (Or.inl rfl)
    refine ⟨g0.map (Option.map (renKey rb.2.old)), ?_, fun j' hj' => ?_⟩
    · rw [trb_map_congr hKo]
      exact hA
    · obtain ⟨⟨j, hj, hjt⟩, -⟩ := afin_jmps hrf hj'
      refine ⟨?_, by rw [← hjt]; exact Reach.jump hR hb hj⟩
      rw [← hjt, hjs j hj, trb_map_congr hg0k]

end

end Opt
end SkaModel
end Formalization
