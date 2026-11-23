import lemmas.Ska.ConvPass

/-!
# Convergence: `+analyze`, the induction, and the final graph

`+analyze` keeps the convergence invariant (`analyzeStep_ok2`): a memo hit
of an earlier poke is a new frozen entry (`MemoHitE`), a new function is
pushed (with no run yet, so with nothing to justify), run, and then popped
alone (`pop_frozen`, with no callee on the stack since `back` is clear), or
culled and iterated (`cullPass_ok2`).  By induction on the fuel every arm
keeps it (`allP2`), and at the end of `+ska-callgraph` the stack is empty, so
every entry of the final graph is frozen (`skaCallgraph_frozen`).
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

theorem memOK_bound {st : SkaState M R} {F : Entry → Prop} {m : Ident} {L L' : Nat} (h : MemOK st F m L)
    (hL : L ≤ L') : MemOK st F m L' := fun d hd hr => by
  obtain ⟨P, L0, h0, hrun, hP⟩ := h d hd hr
  exact ⟨P, L0, Nat.le_trans h0 hL, hrun, hP⟩

/-- The state after `+analyze` pushes a new function. -/
def pushSt (st : SkaState M R) (id : Ident) : SkaState M R :=
  { st with next := st.next + 1, order := Treap.put st.order id st.next, stk := id :: st.stk, g := Treap.put st.g id FDatum.bunt }

/-- **A push keeps the convergence invariant.** -/
theorem push_cinv {memoF : Memo M} {st : SkaState M R} {F : Entry → Prop} (hc : CInv memoF st F) {id : Ident}
    (hw : WellFormed id.1) (hg : Treap.get st.g id = none) :
    CInv memoF (pushSt st id) F ∧
    GStepsR (gCore st.g) (gCore (Treap.put st.g id FDatum.bunt)) ∧
    Keep st.stk (· ∈ st.stk) st (pushSt st id) ∧
    Frame (· ∈ st.stk) st (pushSt st id) ∧
    (∀ m L, m ∈ st.stk → MemOK st F m L → MemOK (pushSt st id) F m L) := by
  have hn : id ∉ st.stk := hc.s.not_mem hg
  have hno : Treap.get st.order id = none := by
    cases e : Treap.get st.order id with
    | none => rfl
    | some o => exact absurd ((hc.s.ord_stk id).mp ⟨o, e⟩) hn
  have htn : Treap.get st.ticks id = none := by
    cases e : Treap.get st.ticks id with
    | none => rfl
    | some v => exact absurd hno (hc.tkeys id (by rw [e]; simp))
  obtain ⟨i1, s1, k1⟩ := push_ok hc.s hw hg st.next
  have hmem : ∀ m L, m ∈ st.stk → MemOK st F m L → MemOK (pushSt st id) F m L :=
    fun m L hm h => memOK_frame hc.s hm k1 (fun _ _ => rfl) (fun _ h => h) h
  have hneid : ∀ i, Treap.get st.g i ≠ none → i ≠ id := fun i hi e => hi (e ▸ hg)
  unfold pushSt at hmem ⊢
  refine ⟨⟨i1, fun m => hc.tick m, ⟨fun i o hio => ?_, ?_⟩, ⟨hc.frz.ok, fun i d h1 h2 => ?_, fun e he => ?_,
    hc.frz.wf, fun f ms s ent h1 h2 => ?_⟩, fun m o hmo => ?_, fun j hj => ?_⟩, s1, k1,
    ⟨fun i d h1 h2 => ?_, fun _ _ => rfl, Nat.le_succ _, Nat.le_refl _, fun x o hxo hx => ?_⟩, hmem⟩
  · simp only [Treap.get_put] at hio
    split at hio
    · cases hio; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hc.ord.1 i o hio)
  · show (id :: st.stk).Pairwise _
    refine List.pairwise_cons.mpr ⟨fun b hb oa ob h1 h2 => ?_, hc.ord.2.imp_of_mem (fun {a b} ha hb hab oa ob h1 h2 => ?_)⟩
    · simp only [Treap.get_put, if_pos rfl] at h1
      cases h1
      have hbi : b ≠ id := fun e => hn (e ▸ hb)
      simp only [Treap.get_put, if_neg hbi] at h2
      exact hc.ord.1 b ob h2
    · have hai : a ≠ id := fun e => hn (e ▸ ha)
      have hbi : b ≠ id := fun e => hn (e ▸ hb)
      simp only [Treap.get_put, if_neg hai] at h1
      simp only [Treap.get_put, if_neg hbi] at h2
      exact hab oa ob h1 h2
  · have hi : i ≠ id := by intro e; subst e; simp [Treap.get_put] at h2
    simp only [Treap.get_put, if_neg hi] at h1 h2
    exact hc.frz.cover i d h1 h2
  · obtain ⟨⟨d, hd⟩, ho⟩ := hc.frz.sub e he
    have hi := hneid _ (by rw [hd]; simp)
    exact ⟨⟨d, by simp only [Treap.get_put, if_neg hi]; exact hd⟩, by simp only [Treap.get_put, if_neg hi]; exact ho⟩
  · obtain ⟨hF, hk, hge⟩ := hc.frz.done f ms s ent h1 h2
    have hi := hneid _ (by rw [hge]; simp)
    exact ⟨hF, hk, by simp only [Treap.get_put, if_neg hi]; exact hge⟩
  · by_cases hm : m = id
    · subst hm
      intro d _ hr
      simp only [ranOf, Treap.gut, htn, Option.getD_none] at hr
      omega
    · simp only [Treap.get_put, if_neg hm] at hmo
      exact memOK_bound (hmem m _ ((hc.s.ord_stk m).mp ⟨o, hmo⟩) (hc.mem m o hmo)) (Nat.le_succ _)
  · by_cases hj' : j = id
    · subst hj'; simp [Treap.get_put]
    · simp only [Treap.get_put, if_neg hj']; exact hc.tkeys j hj
  · have hi : i ≠ id := hneid i (by rw [h1]; simp)
    exact ⟨by simp only [Treap.get_put, if_neg hi]; exact h1, by simp only [Treap.get_put, if_neg hi]; exact h2⟩
  · simp only [Treap.get_put] at hxo
    split at hxo
    · cases hxo; exact Nat.le_refl _
    · exact absurd hxo hx

/-- **The cull before the first pass and the pass loop keep the convergence
invariant.** -/
theorem cullPass_ok2 {memoF : Memo M} {n : Nat} {pass : PassGo M R} (hpass : PassP2 memoF pass) {id : Ident}
    {index : Nat} {st st' : SkaState M R} {low : Nat} {F : Entry → Prop} {l rest : List Ident}
    (hc : CInv memoF st F) (hs : st.stk = l ++ id :: rest) (hidx : Treap.get st.order id = some index)
    (hrest : ∀ m ∈ rest, MemOK st F m index)
    (hcl : ∀ x o, Treap.get st.order x = some o → x ∉ rest → 1 ≤ ranOf st x ∧ LowB st x index)
    (h : cullPass n pass id index st = some (low, st')) :
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F') ∧
    GStepsR (gCore st.g) (gCore st'.g) ∧ Keep rest (· ∈ rest) st st' ∧ Frame (· ∈ rest) st st' ∧
    (∀ x o, Treap.get st'.order x = some o → x ∉ rest → 1 ≤ ranOf st' x ∧ LowB st' x low) ∧
    (∃ d, Treap.get st'.g id = some d) ∧ (∀ o, Treap.get st'.order id = some o → low ≤ o) ∧
    (∀ x o, Treap.get st'.order x = some o → x ∉ rest → low < index) := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st3, hcu, e⟩ := h
  obtain ⟨c3, s3, k3, fr3, hsurv3, hreach3⟩ := cull_ok2 hc hs hidx hrest hcu
  have hrest3 : ∀ m ∈ rest, MemOK st3 F m index := fun m hm =>
    memOK_keepRest hc.ord hc.s hs hidx k3 fr3.ticks (fun _ h => h) hm (hrest m hm)
  obtain ⟨l3, el3⟩ := k3.1
  have hidx3 : Treap.get st3.order id = some index := by rw [k3.2.1 id List.mem_cons_self]; exact hidx
  have hcl3 : ∀ x o, Treap.get st3.order x = some o → x ∉ rest → 1 ≤ ranOf st3 x ∧ LowB st3 x index := by
    intro x o hxo hx
    obtain ⟨a, b, d⟩ := hsurv3 x (by rw [hxo]; simp)
    obtain ⟨h1, h2⟩ := hcl x o (by rw [← d]; exact hxo) hx
    refine ⟨by simp only [ranOf, Treap.gut, b]; exact h1, fun c hce oc hco => ?_⟩
    have hce' : InCallees (calleesOf st x) c := by simpa only [calleesOf, gitG, Treap.gut, a] using hce
    obtain ⟨_, _, dc⟩ := hsurv3 c (by rw [hco]; simp)
    exact h2 c hce' oc (by rw [← dc]; exact hco)
  obtain ⟨⟨F4, hF4, c4⟩, s4, k4, fr4, hcl4, hid4, hlo4, hlt4⟩ := hpass id index 1 st3 low st' F l3 rest c3 el3 hidx3
    hrest3 hcl3 hreach3 e
  exact ⟨⟨F4, hF4, c4⟩, gStepsR_trans s3 s4, (k3.weaken ⟨[id], rfl⟩ (fun j hj => List.mem_cons_of_mem _ hj)).trans k4,
    (fr3.weaken (fun j hj => List.mem_cons_of_mem _ hj)).trans2 fr4 (fun j hj => hj), hcl4, hid4, hlo4, hlt4⟩

/-- The state after `+analyze` takes a memo hit. -/
def hitSt (st : SkaState M R) (id : Ident) (d : FDatum M) : SkaState M R :=
  { st with g := Treap.put st.g id d, done := putMi st.done id d }

/-- **A memo hit of an earlier poke is a new frozen entry.** -/
theorem hit_cinv {memoF : Memo M} (hmF : MemoWF memoF) {st : SkaState M R} {F : Entry → Prop}
    (hc : CInv memoF st F) {id : Ident} (hw : WellFormed id.1) (hg : Treap.get st.g id = none)
    {hit : Ident × FDatum M} (h : gitMi memoF id.2 id.1 = some (some hit)) :
    CInv memoF (hitSt st id hit.2) (fun e => F e ∨ e = entOf id hit.2) ∧
    GStepsR (gCore st.g) (gCore (hitSt st id hit.2).g) ∧ Keep st.stk (· ∈ st.stk) st (hitSt st id hit.2) ∧
    Frame (· ∈ st.stk) st (hitSt st id hit.2) := by
  have hn : id ∉ st.stk := hc.s.not_mem hg
  have hno : Treap.get st.order id = none := by
    cases e : Treap.get st.order id with
    | none => rfl
    | some o => exact absurd ((hc.s.ord_stk id).mp ⟨o, e⟩) hn
  obtain ⟨i1, s1, k1⟩ := hit_ok hmF hc.s hw hg h
  have hneid : ∀ i, Treap.get st.g i ≠ none → i ≠ id := fun i hi e => hi (e ▸ hg)
  have hF : ∀ e, F e → F e ∨ e = entOf id hit.2 := fun e h => Or.inl h
  unfold hitSt
  refine ⟨⟨i1, fun m => hc.tick m, hc.ord, ⟨fun e he => ?_, fun i d h1 h2 => ?_, fun e he => ?_, fun e he => ?_,
    fun f ms s ent h1 h2 => ?_⟩, fun m o hmo => ?_, hc.tkeys⟩, s1, k1,
    ⟨fun i d h1 h2 => ?_, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _, fun x o hxo hx => absurd hxo hx⟩⟩
  · rcases he with he | rfl
    · exact hc.frz.ok.mono hF he
    · exact Or.inr ⟨hit.1, hit.2, h, rfl⟩
  · simp only [Treap.get_put] at h1
    split at h1
    · rename_i e; cases h1; exact Or.inr (by rw [e])
    · exact Or.inl (hc.frz.cover i d h1 h2)
  · rcases he with he | rfl
    · obtain ⟨⟨d, hd⟩, ho⟩ := hc.frz.sub e he
      have hi := hneid _ (by rw [hd]; simp)
      exact ⟨⟨d, by simp only [Treap.get_put, if_neg hi]; exact hd⟩, ho⟩
    · exact ⟨⟨hit.2, by simp [entOf, Treap.get_put]⟩, hno⟩
  · rcases he with he | rfl
    · exact hc.frz.wf e he
    · exact gitMi_wf hmF hw h
  · rcases putMi_get h1 h2 with ⟨ms', e1, e2⟩ | ⟨rfl, rfl⟩
    · obtain ⟨hF', hk, hge⟩ := hc.frz.done f ms' s ent e1 e2
      have hi := hneid _ (by rw [hge]; simp)
      exact ⟨Or.inl hF', hk, by simp only [Treap.get_put, if_neg hi]; exact hge⟩
    · exact ⟨Or.inr rfl, rfl, by simp [Treap.get_put]⟩
  · exact memOK_frame hc.s ((hc.s.ord_stk m).mp ⟨o, hmo⟩) k1 (fun _ _ => rfl) hF (hc.mem m o hmo)
  · have hi := hneid i (by rw [h1]; simp)
    exact ⟨by simp only [Treap.get_put, if_neg hi]; exact h1, h2⟩

end Ana
end SkaModel
end Formalization
