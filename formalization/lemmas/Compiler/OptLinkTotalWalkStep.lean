import lemmas.Compiler.OptLinkTotalWalk

/-!
# `+alias` returns: the induction on the walk

**`winv_drop`**: a dropped block (`rev = []`, not `0`) keeps `WInv`.
**`winv_kept`**: at a kept block, `WInv` and `WIn` give the hypotheses of
`aliasBlock_some`, so the block returns, and the state after it has `WInv`
with the block walked.  **`winv_walk`**: the walk returns from any prefix
with `WInv`; **`winv_init`**: the start has it.  **`aliasRetN_of`**:
`AliasRetN pick ρ L` for every `pick` that picks a member.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

theorem get_put_eq' {ν : Type} (m : Map ν) (k : Nat) (v : ν) : HoonMap.get (HoonMap.put m k v) k = some v := by
  rw [HoonMap.get_put, if_pos rfl]

theorem get_put_ne' {ν : Type} (m : Map ν) {k k' : Nat} (v : ν) (h : k' ≠ k) :
    HoonMap.get (HoonMap.put m k v) k' = HoonMap.get m k' := by
  rw [HoonMap.get_put, if_neg h]

/-- **A dropped block keeps `WInv`.** -/
theorem winv_drop {pick : List Nat → Nat} {n : Nat} {bl : Map Blob} {pre l : List Nat} {o : Nat}
    {rev0 : Map (List Nat)} {g g' : Opt.AGen Map}
    (I : WIn n bl (pre ++ o :: l) rev0) (W : WInv n bl (pre ++ o :: l) pre g) (hop : o ∉ pre)
    (hd : g.rev o = [] ∧ o ≠ 0) (h : Opt.aliasBlock pick n bl g o = some g') :
    WInv n bl (pre ++ o :: l) (pre ++ [o]) g' := by
  have A := (Opt.arev_step I.tok W.rev h).1
  unfold Opt.aliasBlock at h
  dsimp only at h
  rw [if_pos hd] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨n1, n2, n3⟩ := Opt.awr_drop o (Opt.getJmps b.fin) g.rev W.rev.nodup
  refine ⟨A, fun t ht => W.none t (fun h' => ht (List.mem_append_left _ h')), ?_, ?_, ?_⟩
  · intro t q ht hq hqp
    have ht' : t ∉ pre := fun h' => ht (List.mem_append_left _ h')
    rcases List.mem_append.1 hqp with hqp | hqp
    · exact W.drop t q ht' (n2 t q hq) hqp
    · have e := List.mem_singleton.1 hqp
      subst e
      obtain ⟨-, b', j, hb', hj, hjt⟩ := W.rev.sound t q (n2 t q hq)
      rw [hb] at hb'; cases hb'
      exact absurd (by rw [hjt]; exact hq) (n3 j hj)
  · intro r hr
    obtain ⟨q, b', hq, hi, hb', hr'⟩ := W.old r hr
    exact ⟨q, b', List.mem_append_left _ hq, hi, hb', hr'⟩
  · intro q i hi
    have K := W.kept q i hi
    obtain ⟨bq, pb, hbq, hpb, tf, ar, rv, w3⟩ := K.blk
    exact ⟨K.reach, K.imms, bq, pb, hbq, hpb, tf, ar,
      fun t ht hq => rv t (fun h' => ht (List.mem_append_left _ h')) (n2 t q hq), w3⟩

/-- **A kept block returns and keeps `WInv`.** -/
theorem winv_kept {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {n : Nat}
    {bl : Map Blob} {pre l : List Nat} {o : Nat} {rev0 : Map (List Nat)} {g : Opt.AGen Map}
    (I : WIn n bl (pre ++ o :: l) rev0) (W : WInv n bl (pre ++ o :: l) pre g) (hop : o ∉ pre)
    (hd : ¬ (g.rev o = [] ∧ o ≠ 0)) :
    ∃ g', Opt.aliasBlock pick n bl g o = some g' ∧ WInv n bl (pre ++ o :: l) (pre ++ [o]) g' := by
  have hk : g.rev o ≠ [] ∨ o = 0 := by
    by_cases e : g.rev o = []
    · exact Or.inr (Classical.byContradiction fun ne => hd ⟨e, ne⟩)
    · exact Or.inl e
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (I.tok.2.2.1 o (List.mem_append_right _ List.mem_cons_self))
  have hpre : ∀ q ∈ g.rev o, q ∈ pre ∧ ∃ i, g.info q = some i := by
    intro q hq
    obtain ⟨hqt, b', j, hb', hj, hjo⟩ := W.rev.sound o q hq
    have hqp := Opt.awr_pre I.tok hqt hb' hj hjo
    exact ⟨hqp, Option.isSome_iff_exists.1 (W.drop o q hop hq hqp)⟩
  have hR : Opt.Reach bl o := by
    rcases hk with e | e
    · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ e
      obtain ⟨-, b', j, hb', hj, hjo⟩ := W.rev.sound o q hq
      obtain ⟨hqp, i, hi⟩ := hpre q hq
      have := Opt.Reach.jump (W.kept q i hi).reach hb' hj
      rwa [hjo] at this
    · rw [e]; exact Opt.Reach.zero
  have hF := I.first
  -- `W3` at `o`
  have hS : ∀ r, SqR n bl o b r → r ∈ b.par ∨ (g.rev o = [] ∧ g.old r < n) ∨
      (g.rev o ≠ [] ∧ ∀ q ∈ g.rev o, ∀ i, g.info q = some i → (i (g.old r)).isSome) := by
    intro r hr
    rcases hr with hr | ⟨nd, lt⟩ | ⟨d, hall⟩
    · exact Or.inl hr
    · have e : g.old r = r := Classical.byContradiction fun ne => by
        obtain ⟨q, b', -, -, hb', hr'⟩ := W.old r ne
        exact nd (dst_allDefs hb' hr')
      by_cases hp : g.rev o = []
      · exact Or.inr (Or.inl ⟨hp, by rw [e]; exact lt⟩)
      · refine Or.inr (Or.inr ⟨hp, fun q hq i hi => ?_⟩)
        obtain ⟨bq, pb, hbq, -, -, -, -, w3⟩ := (W.kept q i hi).blk
        exact w3 r (Or.inl (Or.inr (Or.inl ⟨nd, lt⟩)))
    · by_cases hp : g.rev o = []
      · exfalso
        have e0 : o = 0 := hk.resolve_left (fun h => h hp)
        rw [e0] at hall
        obtain ⟨o', ho', -⟩ := hall [] Opt.BPath.start
        cases ho'
      · refine Or.inr (Or.inr ⟨hp, fun q hq i hi => ?_⟩)
        obtain ⟨bq, pb, hbq, -, -, -, -, w3⟩ := (W.kept q i hi).blk
        obtain ⟨-, b', j, hb', hj, hjo⟩ := W.rev.sound o q hq
        rw [hbq] at hb'; cases hb'
        refine w3 r ?_
        by_cases hdef : r ∈ Opt.blockDefs bq
        · rcases List.mem_append.1 hdef with h1 | h1
          · exact Or.inl (Or.inl h1)
          · exact Or.inr h1
        · refine Or.inl (Or.inr (Or.inr ⟨d, fun p hp' => ?_⟩))
          have hpo : Opt.BPath bl (o :: q :: p) := by
            have := Opt.BPath.step hp' hbq hj; rwa [hjo] at this
          obtain ⟨o', ho', b'', hb'', hr''⟩ := hall (q :: p) hpo
          rcases List.mem_cons.1 ho' with e | ho'
          · rw [e, hbq] at hb''; cases hb''; exact absurd hr'' hdef
          · exact ⟨o', ho', b'', hb'', hr''⟩
  have hpar : ∀ x ∈ b.par, g.old x = x := fun x hx => Classical.byContradiction fun ne => by
    obtain ⟨q, b', hq, hi, hb', hr'⟩ := W.old x ne
    obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.1 hi
    obtain ⟨k, hs⟩ := site_dst hb' hr'
    have := I.once x (o, none) (q, some k) hR ⟨b, hb, hx⟩ (W.kept q i hi').reach hs
    simp at this
  have hold : ∀ d ∈ dsts b, g.old d = d := fun d hdd => Classical.byContradiction fun ne => by
    obtain ⟨q, b', hq, hi, hb', hr'⟩ := W.old d ne
    obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.1 hi
    obtain ⟨k, hs⟩ := site_dst hb' hr'
    obtain ⟨k', hs'⟩ := site_dst hb hdd
    have := I.once d (o, some k') (q, some k) hR hs' (W.kept q i hi').reach hs
    simp only [Prod.mk.injEq] at this
    exact hop (by rw [this.1]; exact hq)
  have hreads : ∀ i op, b.body[i]? = some op → ∀ r ∈ Opt.aliasReads op,
      SqR n bl o b r ∨ r ∈ (b.body.take i).filterMap Opt.aliasDst := fun i op hi r hr =>
    readS I.reads hF hR hb (show Opt.ReadAt b i r from
      Or.inl (by simp only [List.head?_drop, hi, Option.map_some, Option.getD_some]; exact hr))
  have hfin : ∀ s, s ∈ (Opt.finRegs b.fin).head? → twoWay b.fin = true →
      (∀ l r z o', b.fin ≠ Termin.eqq l r z o') → SqR n bl o b s ∨ s ∈ b.body.filterMap Opt.aliasDst :=
    fun s hs _ _ => by
      have := readS I.reads hF hR hb (show Opt.ReadAt b b.body.length s from Or.inr ⟨rfl, List.mem_of_mem_head? hs⟩)
      rwa [List.take_length] at this
  obtain ⟨g', hg', loc, im, hloc, him, cl, ic, hav, hoff⟩ := aliasBlock_some pick hpick n bl g o b hb hk
    (fun q hq => by
      obtain ⟨-, i, hi⟩ := hpre q hq
      obtain ⟨m, hm, c1, c2⟩ := (W.kept q i hi).imms
      exact ⟨i, m, hi, hm, c1, c2⟩)
    (fun q hq => by
      obtain ⟨-, i, hi⟩ := hpre q hq
      obtain ⟨bq, pb, hbq, hpb, tf, ar, rv, -⟩ := (W.kept q i hi).blk
      refine ⟨pb, hpb, rv o hop hq, fun j hj hjo => ?_, fun i' hi' => ?_⟩
      · obtain ⟨l1, l2⟩ := ar j hj b (by rw [hjo]; exact hb)
        exact ⟨l1, fun k u hk hu => by simp only [hi, Option.bind_some]; exact l2 k u hk hu⟩
      · rw [hi] at hi'; cases hi'; exact tf)
    (SqR n bl o b) hS hpar hold (dsts_nodup I.once hR hb) hreads hfin (fun ht j hj => I.two o b j hb ht hj)
  have A := Opt.arev_step I.tok W.rev hg'
  refine ⟨g', hg', ?_⟩
  have hg2 := hg'
  unfold Opt.aliasBlock at hg2
  dsimp only at hg2
  rw [if_neg hd] at hg2
  obtain ⟨info, -, hg2⟩ := Option.bind_eq_some_iff.mp hg2
  obtain ⟨imms, -, hg2⟩ := Option.bind_eq_some_iff.mp hg2
  obtain ⟨b', hb', hg2⟩ := Option.bind_eq_some_iff.mp hg2
  rw [hb] at hb'; cases hb'
  obtain ⟨edges, -, hg2⟩ := Option.bind_eq_some_iff.mp hg2
  obtain ⟨loc0, -, hg2⟩ := Option.bind_eq_some_iff.mp hg2
  obtain ⟨rb, -, hg2⟩ := Option.bind_eq_some_iff.mp hg2
  obtain ⟨rf, hf, rfl⟩ := Option.map_eq_some_iff.mp hg2
  change Opt.updA g.info o (some rb.2.loc) o = some loc at hloc
  change Opt.updA g.imms o (some rb.2.imml) o = some im at him
  rw [updA_self, Option.some.injEq] at hloc him
  subst hloc; subst him
  obtain ⟨n1, n2⟩ := Opt.awr_fin hf W.rev.nodup
  obtain ⟨t1, t2, t3⟩ := afin_walk hf W.rev.nodup (I.nolti o b hb)
  refine ⟨A.1, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht1 : t ∉ pre := fun h' => ht (List.mem_append_left _ h')
    have ht2 : t ≠ o := fun e => ht (List.mem_append_right _ (List.mem_singleton.2 e))
    show Opt.updA g.info o _ t = none
    rw [updA_ne _ _ ht2]; exact W.none t ht1
  · intro t q ht hq hqp
    have ht1 : t ∉ pre := fun h' => ht (List.mem_append_left _ h')
    show (Opt.updA g.info o _ q).isSome
    by_cases e : q = o
    · rw [e, updA_self]; rfl
    · rw [updA_ne _ _ e]
      have hqp' : q ∈ pre := (List.mem_append.1 hqp).resolve_right (fun h' => e (List.mem_singleton.1 h'))
      exact W.drop t q ht1 (n2 t q hq) hqp'
  · intro r hr
    by_cases hd' : r ∈ dsts b
    · refine ⟨o, b, List.mem_append_right _ (List.mem_singleton_self _), ?_, hb, hd'⟩
      show (Opt.updA g.info o _ o).isSome
      rw [updA_self]; rfl
    · have e : rb.2.old r = g.old r := hoff r hd'
      obtain ⟨q, b', hq, hi, hb', hr'⟩ := W.old r (by rw [← e]; exact hr)
      have hqo : q ≠ o := fun e' => hop (by rw [← e']; exact hq)
      refine ⟨q, b', List.mem_append_left _ hq, ?_, hb', hr'⟩
      show (Opt.updA g.info o _ q).isSome
      rw [updA_ne _ _ hqo]; exact hi
  · intro q i hi
    by_cases e : q = o
    · rw [e] at hi ⊢
      change Opt.updA g.info o (some rb.2.loc) o = some i at hi
      rw [updA_self, Option.some.injEq] at hi
      subst hi
      refine ⟨hR, ⟨rb.2.imml, by show Opt.updA g.imms o _ o = _; rw [updA_self], cl, ic⟩, b,
        { par := b.par, body := rb.1, fin := rf.1 }, hb, get_put_eq' _ _ _, t1, ?_, ?_, hav⟩
      · intro j hj bt hbt
        obtain ⟨j0, hj0, e1, e2⟩ := (afin_facts (fun _ => 0) hf).1 j hj
        have har := I.arity o b j0 bt hb hj0 (by rw [e1]; exact hbt)
        refine ⟨by omega, fun k u hk hu => ?_⟩
        obtain ⟨a, ha, hu'⟩ := t2 j hj u (List.mem_of_getElem? hu)
        have hs := readS I.reads hF hR hb (show Opt.ReadAt b b.body.length a from Or.inr ⟨rfl, ha⟩)
        rw [List.take_length] at hs
        rw [hu']; exact hav a hs
      · intro t ht hm
        obtain ⟨-, b', j, hb', hj, hjt⟩ := W.rev.sound t o (n2 t o hm)
        rw [hb] at hb'; cases hb'
        exact t3 t hm ⟨j, hj, hjt⟩
    · have hi' : g.info q = some i := by
        have : Opt.updA g.info o (some rb.2.loc) q = some i := hi
        rwa [updA_ne _ _ e] at this
      have K := W.kept q i hi'
      have hqp : q ∈ pre := Classical.byContradiction fun h' => by rw [W.none q h'] at hi'; cases hi'
      obtain ⟨bq, pb, hbq, hpb, tf, ar, rv, w3⟩ := K.blk
      obtain ⟨m, hm, c1, c2⟩ := K.imms
      refine ⟨K.reach, ⟨m, by show Opt.updA g.imms o _ q = _; rw [updA_ne _ _ e]; exact hm, c1, c2⟩, bq, pb, hbq,
        by show HoonMap.get (HoonMap.put g.new o _) q = _; rw [get_put_ne' _ _ e]; exact hpb, tf, ar, ?_, ?_⟩
      · intro t ht hq
        exact rv t (fun h' => ht (List.mem_append_left _ h')) (n2 t q hq)
      · intro r hr
        by_cases hd' : r ∈ dsts b
        · exact (later_dst I.tok I.once hop hR hb hd' hqp K.reach hbq hr).elim
        · have e2 : rb.2.old r = g.old r := hoff r hd'
          show (i (rb.2.old r)).isSome
          rw [e2]; exact w3 r hr

/-- **The walk returns** from a prefix with `WInv`. -/
theorem winv_walk {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {n : Nat}
    {bl : Map Blob} {rev0 : Map (List Nat)} : ∀ (l pre : List Nat) (g : Opt.AGen Map),
    WIn n bl (pre ++ l) rev0 → WInv n bl (pre ++ l) pre g → (Opt.aliasWalk pick n bl l g).isSome
  | [], pre, g, _, _ => rfl
  | o :: l, pre, g, I, W => by
    have hop : o ∉ pre := fun h => by
      have := (List.nodup_append.mp I.tok.1).2.2 o h o List.mem_cons_self
      exact this rfl
    obtain ⟨g', hg', W'⟩ : ∃ g', Opt.aliasBlock pick n bl g o = some g' ∧
        WInv n bl (pre ++ o :: l) (pre ++ [o]) g' := by
      by_cases hd : g.rev o = [] ∧ o ≠ 0
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1
          (I.tok.2.2.1 o (List.mem_append_right _ List.mem_cons_self))
        have hs : (Opt.aliasBlock pick n bl g o).isSome := by
          unfold Opt.aliasBlock; dsimp only; rw [if_pos hd, hb]; rfl
        obtain ⟨g', h⟩ := Option.isSome_iff_exists.1 hs
        exact ⟨g', h, winv_drop I W hop hd h⟩
      · exact winv_kept hpick I W hop hd
    simp only [Opt.aliasWalk, hg', Option.bind_some]
    have e : pre ++ o :: l = (pre ++ [o]) ++ l := by simp
    rw [e] at I W'
    exact winv_walk hpick l (pre ++ [o]) g' I W'

/-- **The start of the walk has `WInv`.** -/
theorem winv_init {n : Nat} {bl : Map Blob} {topo : List Nat} {rev0 : Map (List Nat)} (I : WIn n bl topo rev0) :
    WInv n bl topo [] (Opt.aliasInit (Map := Map) rev0) where
  rev := Opt.arev_init I.rs
  none := fun _ _ => rfl
  drop := fun _ _ _ _ h => absurd h List.not_mem_nil
  old := fun r h => absurd rfl h
  kept := fun q i h => by simp [Opt.aliasInit] at h

/-- **`AliasRetN`**: the model of `+alias` returns on every block map with
`StInv`, `DInvR`, `ReadsIn n` and `TopoInvR`, for a `pick` that picks a
member. -/
theorem aliasRetN_of (pick : List Nat → Nat) (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (ρ : Nat → Nat)
    (L : List Nat) : AliasRetN (Map := Map) pick ρ L := by
  intro n bl topo rev hS hD hR hT
  have I : WIn n bl topo rev := ⟨hT.1.1, hT.2, hD.2.1, hD.2.2.2, hD.2.2.1, hS.arity, hS.two, hR⟩
  have := winv_walk hpick topo [] (Opt.aliasInit rev) I (winv_init I)
  unfold Opt.aliasM
  rw [Option.isSome_map]
  exact this

end Compiler
end Formalization
