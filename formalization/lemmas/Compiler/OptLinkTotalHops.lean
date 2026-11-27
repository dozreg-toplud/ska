import lemmas.Compiler.OptLinkTotalInv

/-!
# `+remove-hops` keeps the invariant of the structural loop

`hops_inv_step`: on blocks with `StInv ρ L` and `topo`, `rev` with
`TopoInv`, `+remove-hops` keeps `StInv ρ L`, does not raise the measure `mu`,
and lowers it when it reports a merge.  The facts beyond `HopsBlocks` of
`OptHopsBlocks.lean`:

* `hops_keys`: every block of the result is at a label of `topo`;
* `mtail_end`: a merged chain from a label of `topo` ends at a block of
  `topo` whose end is no hop to a target whose only predecessor it is;
* `hops_drop`: a merged label holds no block after the pass (`hopChain_saw`:
  the labels a chain merges come after its start in `topo`; `hopsFold_drop`:
  the fold puts a block only at the label it visits, and skips a label it has
  merged), so a merge lowers the number of blocks.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map]

theorem hops_keys {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (hn : topo.Nodup) (h : Opt.removeHops fuel bl rev topo = some (ch, bl')) :
    ∀ k, (HoonMap.get bl' k).isSome → k ∈ topo := by
  unfold Opt.removeHops at h
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  obtain ⟨i1, -⟩ := Opt.hopsFold_spec fuel bl rev topo _ r hn hr
  intro k hk
  refine Classical.byContradiction fun hk' => ?_
  rw [i1 k hk', HoonMap.get_empty] at hk; cases hk

/-- A jump of a member of a suffix of `topo` goes to a later member. -/
theorem suffix_fwd {bl : Map Blob} {topo pre l : List Nat} {o : Nat} (e : topo = pre ++ o :: l)
    (hf : ∀ (i x : Nat) (b : Blob) (j : Jmp), topo[i]? = some x → HoonMap.get bl x = some b →
      j ∈ Opt.getJmps b.fin → ∃ k : Nat, i < k ∧ topo[k]? = some j.there)
    {c : Nat} (hc : c ∈ o :: l) {bc : Blob} {j : Jmp} (hb : HoonMap.get bl c = some bc)
    (hj : j ∈ Opt.getJmps bc.fin) : j.there ∈ l := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
  have hti : topo[pre.length + i]? = some c := by
    rw [e, List.getElem?_append_right (Nat.le_add_right _ _)]; simpa using hi
  obtain ⟨k, hk, hkt⟩ := hf _ c bc j hti hb hj
  rw [e, List.getElem?_append_right (by omega)] at hkt
  obtain ⟨m, hm⟩ : ∃ m, k - pre.length = m + 1 := ⟨k - pre.length - 1, by omega⟩
  rw [hm, List.getElem?_cons_succ] at hkt
  exact List.mem_iff_getElem?.2 ⟨m, hkt⟩

/-- The labels a chain merges are targets of the blocks of `P`, in `Q`. -/
theorem hopChain_saw (bl : Map Blob) (rev : Map (List Nat)) (P Q : Nat → Prop)
    (hPQ : ∀ c, P c → ∀ bc j, HoonMap.get bl c = some bc → j ∈ Opt.getJmps bc.fin → Q j.there)
    (hQP : ∀ x, Q x → P x) : ∀ (n c : Nat) (bnew : Blob) (segs : List (List Pole)) (saw : List Nat)
    (bout : Blob) (saw' : List Nat), Opt.hopChain bl rev n c bnew segs saw = some (bout, saw') → P c →
    (∃ bc, HoonMap.get bl c = some bc ∧ bnew.fin = bc.fin) → ∀ x ∈ saw', x ∈ saw ∨ Q x
  | 0, _, _, _, _, _, _, h, _, _ => by simp [Opt.hopChain] at h
  | n + 1, c, bnew, segs, saw, bout, saw', h, hp, ⟨bc, hbc, hfc⟩ => by
    simp only [Opt.hopChain] at h
    cases e : bnew.fin with
    | hop t =>
      simp only [e] at h
      have hq : Q t.there := hPQ c hp bc t hbc (by rw [← hfc, e]; simp [Opt.getJmps])
      by_cases h1 : Opt.getJa rev t.there = []
      · simp [h1] at h
      · by_cases h2 : Opt.getJa rev t.there = [c]
        · simp only [h1, h2, if_false, ne_eq, not_true_eq_false] at h
          obtain ⟨b1, hb1, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨seg, -, h⟩ := Option.bind_eq_some_iff.1 h
          intro x hx
          rcases hopChain_saw bl rev P Q hPQ hQP n t.there _ _ _ bout saw' h (hQP _ hq) ⟨b1, hb1, rfl⟩ x hx with
            hx | hx
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr hq
            · exact Or.inl hx
          · exact Or.inr hx
        · simp only [h1, h2, if_false, ne_eq, not_false_eq_true, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact fun x hx => Or.inl hx
    | _ =>
      simp only [e, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact fun x hx => Or.inl hx

/-- The fold of `+remove-hops` leaves no block at a label it merged. -/
theorem hopsFold_drop (fuel : Nat) (bl : Map Blob) (rev : Map (List Nat)) {topo : List Nat} (hn : topo.Nodup)
    (hf : ∀ (i x : Nat) (b : Blob) (j : Jmp), topo[i]? = some x → HoonMap.get bl x = some b →
      j ∈ Opt.getJmps b.fin → ∃ k : Nat, i < k ∧ topo[k]? = some j.there) :
    ∀ (l pre : List Nat) (acc r : Map Blob × List Nat), topo = pre ++ l →
      l.foldlM (Opt.hopsStep fuel bl rev) acc = some r →
      (∀ x ∈ acc.2, HoonMap.get acc.1 x = none) → (∀ k, (HoonMap.get acc.1 k).isSome → k ∈ pre) →
      ∀ x ∈ r.2, HoonMap.get r.1 x = none
  | [], pre, acc, r, e, h, h1, h2 => by
    simp only [List.foldlM_nil] at h; cases h; exact h1
  | o :: l, pre, acc, r, e, h, h1, h2 => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, ha, h⟩ := Option.bind_eq_some_iff.1 h
    have hnd : (pre ++ o :: l).Nodup := e ▸ hn
    have hol : o ∉ l := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
    have hpl : ∀ x ∈ pre, x ∉ o :: l := fun x hx hx' => (List.nodup_append.1 hnd).2.2 x hx x hx' rfl
    refine hopsFold_drop fuel bl rev hn hf l (pre ++ [o]) acc1 r (by rw [e]; simp) h ?_ ?_
    · unfold Opt.hopsStep at ha
      by_cases ho : o ∈ acc.2
      · simp only [ho, if_true, Option.some.injEq] at ha; subst ha; exact h1
      · simp only [ho, if_false] at ha
        obtain ⟨b, hb, ha⟩ := Option.bind_eq_some_iff.1 ha
        obtain ⟨⟨bout, saw'⟩, hc, ha⟩ := Option.map_eq_some_iff.1 ha
        subst ha
        have hsaw := hopChain_saw bl rev (· ∈ o :: l) (· ∈ l)
          (fun c hc bc j hbc hj => suffix_fwd e hf hc hbc hj) (fun x hx => List.mem_cons_of_mem _ hx)
          fuel o b [] acc.2 bout saw' hc (by simp) ⟨b, hb, rfl⟩
        intro x hx
        simp only [HoonMap.get_put]
        rcases hsaw x hx with hx | hx
        · have hxo : x ≠ o := fun h => ho (h ▸ hx)
          simp only [hxo, if_false]; exact h1 x hx
        · have hxo : x ≠ o := fun h => hol (h ▸ hx)
          simp only [hxo, if_false]
          cases e2 : HoonMap.get acc.1 x with
          | none => rfl
          | some _ => exact absurd (List.mem_cons_of_mem _ hx) (hpl x (h2 x (by simp [e2])))
    · unfold Opt.hopsStep at ha
      intro k hk
      by_cases ho : o ∈ acc.2
      · simp only [ho, if_true, Option.some.injEq] at ha; subst ha
        exact List.mem_append_left _ (h2 k hk)
      · simp only [ho, if_false] at ha
        obtain ⟨b, hb, ha⟩ := Option.bind_eq_some_iff.1 ha
        obtain ⟨⟨bout, saw'⟩, hc, ha⟩ := Option.map_eq_some_iff.1 ha
        subst ha
        simp only [HoonMap.get_put] at hk
        split at hk
        · rename_i hko; subst hko; simp
        · exact List.mem_append_left _ (h2 k hk)

/-- **A merge drops a block.** -/
theorem hops_drop {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {bl' : Map Blob}
    (hi : Opt.TopoInv bl topo rev) (hc : Closed bl) (h : Opt.removeHops fuel bl rev topo = some (true, bl')) :
    ∃ x, (HoonMap.get bl x).isSome ∧ HoonMap.get bl' x = none := by
  unfold Opt.removeHops at h
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq, decide_eq_true_eq] at e
  obtain ⟨e1, rfl⟩ := e
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ e1
  obtain ⟨-, -, i3, -, -⟩ := Opt.hopsFold_spec fuel bl rev topo _ r hi.1.1 hr
  rcases i3 x hx with hx' | ⟨p, bp, t, -, hbp, hft, hxt⟩
  · cases hx'
  · refine ⟨x, ?_, hopsFold_drop fuel bl rev hi.1.1 hi.1.2.2.2.2 topo [] _ r rfl hr
      (fun _ h => absurd h List.not_mem_nil) (fun k hk => by simp [HoonMap.get_empty] at hk) x hx⟩
    rw [← hxt]; exact hc p bp t hbp (by rw [hft]; simp [Opt.getJmps])

/-- A merged chain from a label of `topo` ends at a block of `topo` whose end
is no hop to a target whose only predecessor it is. -/
theorem mtail_end {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} (ht : Opt.TopoOK bl topo)
    {o : Nat} {b : Blob} {T : List Pole} {F : Termin} (h : Opt.MTail bl rev o b T F) :
    HoonMap.get bl o = some b → o ∈ topo →
    ∃ e be, HoonMap.get bl e = some be ∧ F = be.fin ∧ e ∈ topo ∧
      ∀ t, be.fin = Termin.hop t → Opt.getJa rev t.there ≠ [e] := by
  induction h with
  | @stop o b hs => intro hb ho; exact ⟨o, b, hb, rfl, ho, hs⟩
  | @link o b t b1 ops T F hf hpre hb1 _ _ ih =>
    intro hb ho
    refine ih hb1 ?_
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ho
    obtain ⟨k, -, hk⟩ := ht.2.2.2.2 i o b t hi hb (by rw [hf]; simp [Opt.getJmps])
    exact List.mem_iff_getElem?.2 ⟨k, hk⟩

/-- **`+remove-hops` keeps `StInv` and lowers the measure when it merges.** -/
theorem hops_inv_step {ρ : Nat → Nat} {L : List Nat} {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)}
    {topo : List Nat} {ch : Bool} {bl' : Map Blob} (hI : StInv ρ L bl) (hi : Opt.TopoInv bl topo rev)
    (h : Opt.removeHops fuel bl rev topo = some (ch, bl')) :
    StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl) ∧ (ch = true → LexLt (mu ρ L bl') (mu ρ L bl)) := by
  have hB := Opt.hops_blocks hi.1.1 hi.1.2.1 h
  have hK := hops_keys hi.1.1 h
  -- the end of every block of the result
  have hend : ∀ o m, HoonMap.get bl' o = some m → ∃ b, HoonMap.get bl o = some b ∧ m.par = b.par ∧
      ∃ e be, HoonMap.get bl e = some be ∧ m.fin = be.fin ∧ e ∈ topo ∧
        ∀ t, be.fin = Termin.hop t → Opt.getJa rev t.there ≠ [e] := by
    intro o m hm
    obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o m hm
    exact ⟨b, hb, rfl, mtail_end hi.1 hmt hb (hK o (by simp [hm]))⟩
  have hold : ∀ o, (HoonMap.get bl' o).isSome → (HoonMap.get bl o).isSome := by
    intro o ho
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 ho
    obtain ⟨b, hb, -⟩ := hend o m hm
    simp [hb]
  have hpres : ∀ o ∈ L, presN (HoonMap.get bl' o) ≤ presN (HoonMap.get bl o) := by
    intro o _
    cases e1 : HoonMap.get bl' o with
    | none => simp [presN]
    | some m =>
      have := hold o (by simp [e1])
      cases e2 : HoonMap.get bl o with
      | none => rw [e2] at this; cases this
      | some _ => exact Nat.le_refl _
  refine ⟨⟨fun o m j hm hj => ?_, fun o m j hm hj => ?_, fun o m j m2 hm hj hm2 => ?_, ?_,
    fun o m j hm ht hj => ?_, fun o ho => hI.keys o (hold o ho)⟩, ?_, fun hc => ?_⟩
  · obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o m hm
    obtain ⟨e, be, hbe, hF, hle⟩ := Opt.mtail_rank hI.rank hmt hb
    simp only [Opt.merge] at hj
    rw [hF] at hj
    have := hI.rank e be j hbe hj
    omega
  · obtain ⟨b, hb, -, e, be, hbe, hfe, het, hstop⟩ := hend o m hm
    rw [hfe] at hj
    obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.1 het
    obtain ⟨k, -, hk⟩ := hi.1.2.2.2.2 i e be j hi' hbe hj
    rcases hB.cover j.there (List.mem_iff_getElem?.2 ⟨k, hk⟩) with ⟨m2, hm2, -⟩ | ⟨p, bp, t, hpre, hbp, hft, hxt⟩
    · simp [hm2]
    · have hep : e ∈ Opt.getJa rev j.there := hi.2 e be j het hbe hj
      rw [hpre, List.mem_singleton] at hep
      subst hep
      rw [hbe] at hbp; cases hbp
      exact absurd (by rw [hxt]; exact hpre) (hstop t hft)
  · obtain ⟨b, hb, -, e, be, hbe, hfe, het, -⟩ := hend o m hm
    obtain ⟨b2, hb2, hpar2, -⟩ := hend j.there m2 hm2
    rw [hfe] at hj
    rw [hpar2]
    exact hI.arity e be j b2 hbe hj hb2
  · obtain ⟨m, hm, -⟩ := hB.zero; simp [hm]
  · obtain ⟨b, hb, -, e, be, hbe, hfe, -, -⟩ := hend o m hm
    rw [hfe] at ht hj
    exact hI.two e be j hbe ht hj
  · cases ch with
    | true =>
      obtain ⟨x, hx, hx'⟩ := hops_drop hi hI.closed h
      refine Or.inl (mu_lt1 hpres (hI.keys x hx) ?_)
      rw [hx']; obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hx; rw [hb]; simp [presN]
    | false =>
      obtain ⟨hs, hout⟩ := Opt.hops_same hi.1.1 h
      by_cases hall : ∀ k ∈ L, HoonMap.get bl' k = HoonMap.get bl k
      · exact Or.inr (mu_eq fun o ho => by rw [hall o ho]; exact ⟨rfl, rfl, rfl⟩)
      · obtain ⟨k, hk, hne⟩ : ∃ k ∈ L, HoonMap.get bl' k ≠ HoonMap.get bl k :=
          Classical.byContradiction fun hn => hall fun k hk => Classical.byContradiction fun h' => hn ⟨k, hk, h'⟩
        have hkt : k ∉ topo := fun hkt => hne (hs k hkt)
        refine Or.inl (mu_lt1 hpres hk ?_)
        rw [hout k hkt] at hne ⊢
        cases e2 : HoonMap.get bl k with
        | none => rw [e2] at hne; exact absurd rfl hne
        | some _ => simp [presN]
  · obtain ⟨x, hx, hx'⟩ := hops_drop hi hI.closed (hc ▸ h)
    refine mu_lt1 hpres (hI.keys x hx) ?_
    rw [hx']; obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hx; rw [hb]; simp [presN]

end

end Compiler
end Formalization
