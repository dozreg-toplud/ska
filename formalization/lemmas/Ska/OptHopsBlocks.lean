import lemmas.Ska.OptHopsPass

/-!
# The blocks after `+remove-hops`

`MTail bl rev o b T F`: the block `b` at `o` becomes, in the code after,
`b` with the ops `T` appended and the end `F` (`merge b T F`).  Either the
chain stops at `b` (`stop`: its end is no hop to a block whose only
predecessor in `rev` is `o`), or `b` ends in a hop `t` to the block `b1` whose
only predecessor is `o`, and `T` is the moves of the hop, the body of `b1`
and the tail of `b1` (`link`).

`hopChain_spec` and `hopsFold_spec`: every block of the result is the merge of
the block at its label (`hops_blocks`); every label of `topo` holds such a
merge or was merged, and a merged label `x` has one predecessor `p` in `rev`,
whose block ends in a hop to `x` (`Wit`); block `0` is the merge of block `0`.
`revCfg_mem`: the list of a block in `+rev-cfg` holds every member of `topo`
that jumps to it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-- The tail of a merged chain. -/
inductive MTail (bl : Map Blob) (rev : Map (List Nat)) : Nat → Blob → List Pole → Termin → Prop
  | stop {o : Nat} {b : Blob} : (∀ t, b.fin = Termin.hop t → getJa rev t.there ≠ [o]) → MTail bl rev o b [] b.fin
  | link {o : Nat} {b : Blob} {t : Jmp} {b1 : Blob} {ops T : List Pole} {F : Termin} :
      b.fin = Termin.hop t → getJa rev t.there = [o] → HoonMap.get bl t.there = some b1 →
      hopSeg t.args b1.par [] = some ops → MTail bl rev t.there b1 T F → MTail bl rev o b (ops ++ b1.body ++ T) F

/-- The merged block. -/
def merge (b : Blob) (T : List Pole) (F : Termin) : Blob := { b with body := b.body ++ T, fin := F }

/-- A label merged into the chain of its one predecessor. -/
def Wit (bl : Map Blob) (rev : Map (List Nat)) (x : Nat) : Prop :=
  ∃ p bp t, getJa rev x = [p] ∧ HoonMap.get bl p = some bp ∧ bp.fin = Termin.hop t ∧ t.there = x

/-- A block of the result: the merge of the block at its label. -/
def Mrg (bl : Map Blob) (rev : Map (List Nat)) (o : Nat) (m : Blob) : Prop :=
  ∃ b T F, HoonMap.get bl o = some b ∧ MTail bl rev o b T F ∧ m = merge b T F

/-- The end of a merged chain is the end of a block. -/
theorem MTail.fin_of {bl : Map Blob} {rev : Map (List Nat)} {o : Nat} {b : Blob} {T : List Pole} {F : Termin}
    (h : MTail bl rev o b T F) : F = b.fin ∨ ∃ e be, HoonMap.get bl e = some be ∧ F = be.fin := by
  induction h with
  | stop => exact Or.inl rfl
  | link _ _ hb1 _ _ ih =>
    rcases ih with e | ⟨e, be, hbe, e'⟩
    · exact Or.inr ⟨_, _, hb1, e⟩
    · exact Or.inr ⟨e, be, hbe, e'⟩

theorem hopChain_spec (bl : Map Blob) (rev : Map (List Nat)) : ∀ (n o : Nat) (bnew : Blob)
    (segs : List (List Pole)) (saw : List Nat) (bout : Blob) (saw' : List Nat),
    hopChain bl rev n o bnew segs saw = some (bout, saw') → ∀ bo, HoonMap.get bl o = some bo → bnew.fin = bo.fin →
    ∃ T F, MTail bl rev o bo T F ∧ bout = { bnew with body := bnew.body ++ segs.reverse.flatten ++ T, fin := F } ∧
      (∀ x ∈ saw', x ∈ saw ∨ Wit bl rev x) ∧ (∀ x ∈ saw, x ∈ saw')
  | 0, _, _, _, _, _, _, h, _, _, _ => by simp [hopChain] at h
  | n + 1, o, bnew, segs, saw, bout, saw', h, bo, hbo, hf => by
    simp only [hopChain] at h
    split at h
    · rename_i t ht
      split at h
      · cases h
      · split at h
        · rename_i hne
          simp only [hopDone, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨[], bnew.fin, ?_, by simp, fun x hx => Or.inl hx, fun x hx => hx⟩
          rw [hf]
          exact MTail.stop (fun t' h' => by rw [← hf, ht] at h'; cases h'; exact hne)
        · rename_i hpre
          have hpre' : getJa rev t.there = [o] := Decidable.of_not_not hpre
          obtain ⟨b1, hb1, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨seg, hseg, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨T1, F1, hm, hout, hs1, hs2⟩ := hopChain_spec bl rev n t.there _ _ _ _ _ h b1 hb1 rfl
          rw [hopSeg_eq] at hseg
          split at hseg
          · rename_i hlen
            simp only [Option.some.injEq] at hseg
            subst hseg
            have hops : hopSeg t.args b1.par [] = some ((t.args.zip b1.par).reverse.map argOp) := by
              rw [hopSeg_eq, if_pos hlen, List.append_nil]
            refine ⟨_, F1, MTail.link (hf ▸ ht) hpre' hb1 hops hm, ?_, ?_, ?_⟩
            · rw [hout]; simp
            · intro x hx
              rcases hs1 x hx with hx | hx
              · rcases List.mem_cons.mp hx with rfl | hx
                · exact Or.inr ⟨o, bo, t, hpre', hbo, hf ▸ ht, rfl⟩
                · exact Or.inl hx
              · exact Or.inr hx
            · intro x hx; exact hs2 x (List.mem_cons_of_mem _ hx)
          · cases hseg
    · rename_i hnh
      simp only [hopDone, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[], bnew.fin, ?_, by simp, fun x hx => Or.inl hx, fun x hx => hx⟩
      rw [hf]
      exact MTail.stop (fun t' h' => absurd (hf ▸ h') (hnh t'))

theorem hopsFold_spec (fuel : Nat) (bl : Map Blob) (rev : Map (List Nat)) :
    ∀ (l : List Nat) (acc r : Map Blob × List Nat), l.Nodup → l.foldlM (hopsStep fuel bl rev) acc = some r →
    (∀ k, k ∉ l → HoonMap.get r.1 k = HoonMap.get acc.1 k) ∧
    ((∀ o m, HoonMap.get acc.1 o = some m → Mrg bl rev o m) → ∀ o m, HoonMap.get r.1 o = some m → Mrg bl rev o m) ∧
    (∀ x ∈ r.2, x ∈ acc.2 ∨ Wit bl rev x) ∧ (∀ x ∈ acc.2, x ∈ r.2) ∧
    (∀ o ∈ l, (∃ m, HoonMap.get r.1 o = some m ∧ Mrg bl rev o m) ∨ o ∈ r.2)
  | [], acc, r, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨fun _ _ => rfl, fun h => h, fun x hx => Or.inl hx, fun x hx => hx, fun _ h => absurd h List.not_mem_nil⟩
  | o :: l, acc, r, hn, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hn' := List.nodup_cons.mp hn
    obtain ⟨i1, i2, i3, i4, i5⟩ := hopsFold_spec fuel bl rev l acc1 r hn'.2 h
    unfold hopsStep at h1
    split at h1
    · rename_i hsaw
      cases h1
      refine ⟨fun k hk => i1 k (fun h => hk (List.mem_cons_of_mem _ h)), i2, i3, i4, ?_⟩
      intro o' ho'
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact Or.inr (i4 _ hsaw)
      · exact i5 o' ho'
    · obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨⟨bout, saw'⟩, hc, h1⟩ := Option.map_eq_some_iff.mp h1
      cases h1
      obtain ⟨T, F, hm, hout, hs1, hs2⟩ := hopChain_spec bl rev fuel o b [] acc.2 bout saw' hc b hb rfl
      have hmrg : Mrg bl rev o bout := ⟨b, T, F, hb, hm, by rw [hout]; simp [merge]⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro k hk
        rw [i1 k (fun h => hk (List.mem_cons_of_mem _ h))]
        simp [HoonMap.get_put, show k ≠ o from fun e => hk (e ▸ List.mem_cons_self)]
      · intro hacc o' m hm'
        apply i2 _ o' m hm'
        intro o'' m' hm''
        simp only [HoonMap.get_put] at hm''
        split at hm''
        · rename_i e; subst e; cases hm''; exact hmrg
        · exact hacc o'' m' hm''
      · intro x hx
        rcases i3 x hx with hx | hx
        · exact hs1 x hx
        · exact Or.inr hx
      · intro x hx; exact i4 x (hs2 x hx)
      · intro o' ho'
        rcases List.mem_cons.mp ho' with rfl | ho'
        · left; refine ⟨bout, ?_, hmrg⟩
          rw [i1 o' hn'.1]; simp [HoonMap.get_put]
        · exact i5 o' ho'

/-- **The blocks after `+remove-hops`.** -/
structure HopsBlocks (bl : Map Blob) (rev : Map (List Nat)) (topo : List Nat) (bl' : Map Blob) : Prop where
  back : ∀ o m, HoonMap.get bl' o = some m → Mrg bl rev o m
  cover : ∀ o ∈ topo, (∃ m, HoonMap.get bl' o = some m ∧ Mrg bl rev o m) ∨ Wit bl rev o
  zero : ∃ m, HoonMap.get bl' 0 = some m ∧ Mrg bl rev 0 m

theorem hops_blocks {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel bl rev topo = some (ch, bl')) : HopsBlocks bl rev topo bl' := by
  unfold removeHops at h
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  obtain ⟨i1, i2, i3, -, i5⟩ := hopsFold_spec fuel bl rev topo _ r hn hr
  have hback := i2 (fun o m hm => by rw [HoonMap.get_empty] at hm; cases hm)
  refine ⟨hback, fun o ho => ?_, ?_⟩
  · rcases i5 o ho with h | h
    · exact Or.inl h
    · rcases i3 o h with h | h
      · exact absurd h List.not_mem_nil
      · exact Or.inr h
  · cases topo with
    | nil => cases h0
    | cons o rest =>
      simp only [List.head?_cons, Option.some.injEq] at h0
      subst h0
      rw [List.foldlM_cons] at hr
      obtain ⟨acc1, h1, h2⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨j1, -, -, -, -⟩ := hopsFold_spec fuel bl rev rest acc1 r (List.nodup_cons.mp hn).2 h2
      unfold hopsStep at h1
      simp only [List.not_mem_nil, if_false] at h1
      obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨⟨bout, saw'⟩, hc, h1⟩ := Option.map_eq_some_iff.mp h1
      cases h1
      obtain ⟨T, F, hm, hout, -, -⟩ := hopChain_spec bl rev fuel 0 b [] [] bout saw' hc b hb rfl
      refine ⟨bout, ?_, b, T, F, hb, hm, by rw [hout]; simp [merge]⟩
      rw [j1 0 (List.nodup_cons.mp hn).1]; simp [HoonMap.get_put]

/-! ## `+rev-cfg` -/

theorem addJa_mono {acc : Map (List Nat)} {k k' o x : Nat} (h : x ∈ getJa acc k) :
    x ∈ getJa (addJa acc k' o) k := by
  unfold addJa getJa at *
  simp only [HoonMap.get_put]
  split
  · rename_i e; subst e; simp [h]
  · exact h

theorem inner_mono (o x k : Nat) : ∀ (js : List Jmp) (acc : Map (List Nat)), x ∈ getJa acc k →
    x ∈ getJa (js.foldl (fun acc j => addJa acc j.there o) acc) k
  | [], _, h => h
  | _ :: js, _, h => inner_mono o x k js _ (addJa_mono h)

theorem inner_adds (o : Nat) : ∀ (js : List Jmp) (acc : Map (List Nat)) (j : Jmp), j ∈ js →
    o ∈ getJa (js.foldl (fun acc j => addJa acc j.there o) acc) j.there
  | [], _, _, h => absurd h List.not_mem_nil
  | j' :: js, acc, j, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact inner_mono o o _ js _ (by simp [addJa, getJa, HoonMap.get_put])
    · exact inner_adds o js _ j h

theorem revStep_mono {bl : Map Blob} {topo : List Nat} {acc : Map (List Nat)} {o x k : Nat}
    (h : x ∈ getJa acc k) : x ∈ getJa (revStep bl topo acc o) k := by
  unfold revStep
  split
  · split
    · exact inner_mono _ _ _ _ _ h
    · exact h
  · exact h

theorem revFold_mono {bl : Map Blob} {topo : List Nat} {x k : Nat} : ∀ (ks : List Nat) (acc : Map (List Nat)),
    x ∈ getJa acc k → x ∈ getJa (ks.foldl (revStep bl topo) acc) k
  | [], _, h => h
  | _ :: ks, _, h => revFold_mono ks _ (revStep_mono h)

theorem revFold_adds {bl : Map Blob} {topo : List Nat} {o : Nat} {b : Blob} {j : Jmp}
    (hmem : o ∈ topo) (hb : HoonMap.get bl o = some b) (hj : j ∈ getJmps b.fin) :
    ∀ (ks : List Nat) (acc : Map (List Nat)), o ∈ ks → o ∈ getJa (ks.foldl (revStep bl topo) acc) j.there
  | [], _, h => absurd h List.not_mem_nil
  | k :: ks, acc, h => by
    simp only [List.foldl_cons]
    by_cases e : k = o
    · subst e
      apply revFold_mono
      unfold revStep
      rw [hb]; simp only [if_pos hmem]
      exact inner_adds _ _ _ _ hj
    · exact revFold_adds hmem hb hj ks _ (by rcases List.mem_cons.mp h with h | h; exact absurd h.symm e; exact h)

/-- **The list of a block in `+rev-cfg` holds every member of `topo` that
jumps to it.** -/
theorem revCfg_mem [MapKeys Map] {bl : Map Blob} {topo : List Nat} {o : Nat} {b : Blob} {j : Jmp}
    (hmem : o ∈ topo) (hb : HoonMap.get bl o = some b) (hj : j ∈ getJmps b.fin) :
    o ∈ getJa (revCfg bl topo) j.there :=
  revFold_adds hmem hb hj _ _ ((MapKeys.mem_keys bl o).mpr (by simp [hb]))

end Opt
end SkaModel
end Formalization
