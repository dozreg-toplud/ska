import lemmas.Ska.ConvPass
import lemmas.Ska.MemoPoke

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
  have hcalF : ∀ e, F e → calleesOf (pushSt st id) (e.more, e.fol) = calleesOf st (e.more, e.fol) :=
    fun e he => by
      obtain ⟨⟨d, hd, _⟩, _⟩ := hc.frz.sub e he
      have hi := hneid _ (by rw [hd]; simp)
      simp only [pushSt, calleesOf, gitG, Treap.gut, Treap.get_put, if_neg hi]
  unfold pushSt at hmem hcalF ⊢
  refine ⟨⟨i1, fun m => hc.tick m, ⟨fun i o hio => ?_, ?_⟩, ⟨fun e he => hc.frz.ok.mono (fun _ h => h) hcalF he,
    fun i d h1 h2 => ?_, fun e he => ?_,
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
  · obtain ⟨⟨d, hd, hl⟩, ho⟩ := hc.frz.sub e he
    have hi := hneid _ (by rw [hd]; simp)
    exact ⟨⟨d, by simp only [Treap.get_put, if_neg hi]; exact hd, hl⟩,
      by simp only [Treap.get_put, if_neg hi]; exact ho⟩
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
    · refine hc.frz.ok.mono hF (fun e he => ?_) he
      obtain ⟨⟨d, hd, _⟩, _⟩ := hc.frz.sub e he
      have hi := hneid _ (by rw [hd]; simp)
      simp only [calleesOf, gitG, Treap.gut, Treap.get_put, if_neg hi]
    · exact Or.inr ⟨hit.1, hit.2, h, rfl⟩
  · simp only [Treap.get_put] at h1
    split at h1
    · rename_i e; cases h1; exact Or.inr (by rw [e])
    · exact Or.inl (hc.frz.cover i d h1 h2)
  · rcases he with he | rfl
    · obtain ⟨⟨d, hd, hl⟩, ho⟩ := hc.frz.sub e he
      have hi := hneid _ (by rw [hd]; simp)
      exact ⟨⟨d, by simp only [Treap.get_put, if_neg hi]; exact hd, hl⟩, ho⟩
    · exact ⟨⟨hit.2, by simp [entOf, Treap.get_put], rfl⟩, hno⟩
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

/-- **`+analyze` keeps the convergence invariant.** -/
theorem analyzeStep_ok2 {memoF : Memo M} (hmF : MemoWF memoF) {n : Nat} {run : RunGo M R} {pass : PassGo M R}
    (hrun : RunP2 memoF run) (hpass : PassP2 memoF pass) : AnaP2 memoF (analyzeStep n memoF run pass) := by
  intro id st low st' F hc hw hg e
  have hn : id ∉ st.stk := hc.s.not_mem hg
  unfold analyzeStep at e
  split at e
  · cases e
  · rename_i hit hh
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨c1, s1, k1, fr1⟩ := hit_cinv hmF hc hw hg hh
    have hno : Treap.get st.order id = none := by
      cases e : Treap.get st.order id with
      | none => rfl
      | some o => exact absurd ((hc.s.ord_stk id).mp ⟨o, e⟩) hn
    exact ⟨⟨_, fun e h => Or.inl h, c1⟩, s1, k1, fr1,
      fun x o hxo hx => absurd ((hc.s.ord_stk x).mp ⟨o, hxo⟩) hx, ⟨hit.2, by simp [Treap.get_put]⟩,
      fun o ho => absurd (ho.symm.trans hno) (by simp),
      fun x o hxo hx => absurd ((hc.s.ord_stk x).mp ⟨o, hxo⟩) hx⟩
  · obtain ⟨c1, s1, k1, fr1, hm1⟩ := push_cinv hc hw hg
    simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    have hid1 : id ∈ (pushSt st id).stk := List.mem_cons_self
    have hidx1 : Treap.get (pushSt st id).order id = some st.next := by simp [pushSt, Treap.get_put]
    obtain ⟨⟨F2, hF2, c2, hmo2⟩, s2, k2, fr2, hran2, htick2, _, _, hlow2, hlb2, hpush2, hback2⟩ :=
      hrun id st.next (pushSt st id) r1 st2 F c1 hid1 hidx1 hr
    obtain ⟨l, el⟩ := k2.1
    have hst2 : st2.stk = l ++ id :: st.stk := el
    have hidx2 : Treap.get st2.order id = some st.next := by rw [k2.2.1 id hid1]; exact hidx1
    have hrest2 : ∀ m ∈ st.stk, MemOK st2 F2 m st.next := fun m hm => by
      obtain ⟨o, ho⟩ := (hc.s.ord_stk m).mpr hm
      exact hmo2 m st.next (List.mem_cons_of_mem _ hm) (fun e => hn (e ▸ hm)) (hm1 m _ hm (hc.mem m o ho))
    have hcl2 : ∀ x o, Treap.get st2.order x = some o → x ∉ st.stk → 1 ≤ ranOf st2 x ∧ LowB st2 x r1.1 := by
      intro x o hxo hx
      by_cases hxi : x = id
      · subst hxi
        exact ⟨by rw [hran2]; omega, hlb2⟩
      · exact hpush2 x o hxo (by simp [pushSt, hxi, hx])
    have keep2 : Keep st.stk (· ∈ st.stk) st st2 :=
      k1.trans (k2.weaken ⟨[id], rfl⟩ (fun j hj => ⟨List.mem_cons_of_mem _ hj, fun e => hn (e ▸ hj)⟩))
    have frame2 : Frame (· ∈ st.stk) st st2 :=
      fr1.trans2 (fr2.weaken (fun j hj => ⟨List.mem_cons_of_mem _ hj, fun e => hn (e ▸ hj)⟩)) (fun j hj => hj)
    have steps2 : GStepsR (gCore st.g) (gCore st2.g) := gStepsR_trans s1 s2
    have hcp : ∀ low st', cullPass n pass id st.next st2 = some (low, st') → r1.1 = st.next →
        (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F') ∧
        GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ st.stk) st st' ∧ Frame (· ∈ st.stk) st st' ∧
        Pushed st st' low ∧ (∃ d, Treap.get st'.g id = some d) ∧
        (∀ o, Treap.get st'.order id = some o → low ≤ o) ∧
        (∀ x o, Treap.get st'.order x = some o → x ∉ st.stk → low < st.next) := by
      intro low st' hcpe hr1
      obtain ⟨⟨F4, hF4, c4⟩, s4, k4, fr4, hcl4, hid4, hlo4, hlt4⟩ := cullPass_ok2 hpass c2 hst2 hidx2 hrest2
        (fun x o hxo hx => by rw [← hr1]; exact hcl2 x o hxo hx) hcpe
      exact ⟨⟨F4, fun e he => hF4 e (hF2 e he), c4⟩, gStepsR_trans steps2 s4, keep2.trans k4,
        frame2.trans2 fr4 (fun j hj => hj), hcl4, hid4, hlo4, hlt4⟩
    simp only at e
    split at e
    · rename_i hne0
      have hne : r1.1 ≠ st.next := by simpa using hne0
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨⟨F2, hF2, c2⟩, steps2, keep2, frame2, hcl2, ?_, fun o ho => ?_, fun _ _ _ _ => by omega⟩
      · obtain ⟨d, hd⟩ := c2.s.ord_g id _ hidx2; exact ⟨d, hd⟩
      · rw [hidx2] at ho; cases ho; exact hlow2
    · rename_i heq0
      have hr1 : r1.1 = st.next := by simpa using heq0
      split at e
      · exact hcp low st' e hr1
      · rename_i hb0
        have hb : r1.2.1 = false := by simpa using hb0
        simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, hab, e⟩ := e
        split at e
        · exact hcp low st' e hr1
        · rename_i hlen0
          have hlen : ab.length = 1 := by simpa using hlen0
          simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hpop, e⟩ := e
          cases e
          obtain ⟨ab0, rest', rfl, hs', _⟩ := above_eq hab
          have hab0 : ab0 = [] := by
            cases ab0 with
            | nil => rfl
            | cons a t => simp at hlen
          subst hab0
          have hl : l = [] := by
            have h1 : st2.stk.Nodup := c2.s.nodup
            rw [hst2] at h1
            have := nodup_split_unique h1 (hst2.symm.trans hs')
            exact this.1
          subst hl
          have hs2 : st2.stk = [] ++ id :: st.stk := hst2
          have hready : ∀ x ∈ ([] : List Ident) ++ [id], 1 ≤ ranOf st2 x ∧ ∀ c, InCallees (calleesOf st2 x) c →
              ∀ o, Treap.get st2.order c = some o → chgOf st2 c < ranOf st2 x ∧ st.next ≤ o := by
            intro x hx
            simp only [List.nil_append, List.mem_singleton] at hx
            subst hx
            refine ⟨by rw [hran2]; omega, fun c hce o hco => ?_⟩
            exfalso
            have hcs : c ∈ st2.stk := (c2.s.ord_stk c).mp ⟨o, hco⟩
            rw [hst2] at hcs
            exact hback2 hb c hce o hco hcs
          obtain ⟨F3, hF3, c3⟩ := pop_frozen c2 hs2 hidx2 hrest2 hready hpop
          obtain ⟨a1, _, _, a4, _, a6, _⟩ := popGo_eff [] st2 _ st.stk hs2 (by rw [← hs2]; exact c2.s.nodup)
            (fun j hj => c2.s.mem_g (by rw [hs2]; exact mem_split_of hj)) (by unfold pop at hpop; exact hpop)
          obtain ⟨_, s3, k3⟩ := pop_ok c2.s hpop hs2
          refine ⟨⟨F3, fun e he => hF3 e (hF2 e he), c3⟩, gStepsR_trans steps2 s3, keep2.trans k3,
            frame2.trans2 (pop_frame c2.s hs2 hpop) (fun j hj => hj), fun x o hxo hx => ?_, ?_,
            fun o ho => ?_, fun x o hxo hx => ?_⟩
          · exfalso
            have hxs := (c3.s.ord_stk x).mp ⟨o, hxo⟩
            rw [a1] at hxs; exact hx hxs
          · obtain ⟨d, hd⟩ := c2.s.mem_g (by rw [hs2]; exact List.mem_cons_self)
            rw [a6, if_pos (List.mem_append_right [] (List.mem_singleton.mpr rfl)), hd]; exact ⟨_, rfl⟩
          · rw [a4, if_pos (List.mem_append_right [] (List.mem_singleton.mpr rfl))] at ho; cases ho
          · exfalso
            have hxs := (c3.s.ord_stk x).mp ⟨o, hxo⟩
            rw [a1] at hxs; exact hx hxs

/-! ## The induction on the fuel -/

/-- The arms at the fuel `n` keep the convergence invariant. -/
def AllP2 (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  ResP2 memoF (resolve env memoF n) ∧ AnaP2 memoF (analyze env memoF n) ∧ RunP2 memoF (run env memoF n) ∧
    PassP2 memoF (passLoop env memoF n) ∧ MemP2 memoF (memberLoop env memoF n)

theorem allP2_zero (env : Env R) (memoF : Memo M) : AllP2 env memoF 0 := by
  refine ⟨fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm of the analysis keeps the convergence invariant**, at every
fuel, for a persistent memo with well-formed products. -/
theorem allP2 (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) : ∀ n, ∀ k, k ≤ n → AllP2 env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allP2_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allP2 env memoF hmF n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allP2 env memoF hmF n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [resolve_succ]; exact resolveStep_ok2 env memoF r a
      · rw [analyze_succ]; exact analyzeStep_ok2 hmF u p
      · rw [run_succ]
        exact runStep_ok2 env memoF (fun k hk => (allP2 env memoF hmF n k (Nat.le_of_lt hk)).1)
      · rw [passLoop_succ]; exact passStep_ok2 m p
      · rw [memberLoop_succ]; exact memberStep_ok2 u m

/-! ## The final graph -/

theorem CInv.init (memoF : Memo M) (reg : R) : CInv memoF (SkaState.init reg : SkaState M R) (fun _ => False) where
  s := SInv.init reg
  tick := fun m => by simp [ranOf, chgOf, Treap.gut, SkaState.init, Treap.get_empty]
  ord := ⟨fun i o h => by simp [SkaState.init, Treap.get_empty] at h, List.Pairwise.nil⟩
  frz := ⟨fun _ h => h.elim, fun i d h _ => by simp [SkaState.init, Treap.get_empty] at h, fun _ h => h.elim,
    fun _ h => h.elim, fun f ms s ent h _ => by simp [SkaState.init, Treap.get_empty] at h⟩
  mem := fun m o h => by simp [SkaState.init, Treap.get_empty] at h
  tkeys := fun j h => by simp [SkaState.init, Treap.get_empty] at h

/-- **The final graph of `+ska-callgraph` is frozen**: every entry is a memo
hit of an earlier poke, or was written by its last run with answers that are
answers of the frozen entries (the entries of the final graph and the
versions of them before `+pop`); for a root with a well-formed subject sock
and a persistent memo with well-formed products.  No assumption on the
scheduling: this is convergence, for the Hoon with the cull before the first
pass. -/
theorem skaCallgraph_frozen (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) {n : Nat} {root : Ident}
    {reg reg' : R} {g : Callgraph M} (hw : WellFormed root.1)
    (h : skaCallgraph env n root memoF reg = some (g, reg')) :
    ∃ F : Entry → Prop, FrozenOK memoF F (fun i => (gitG g i).callees) ∧
      (∀ i d, Treap.get g i = some d → F (entOf i d)) ∧
      (∀ e, F e → ∃ d, Treap.get g (e.more, e.fol) = some d ∧ e.d.less = d.less) ∧ (∀ e, F e → WellFormed e.d.prod) ∧
      GStepsR (fun _ => none) (gCore g) := by
  unfold skaCallgraph at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨low, st⟩, ha, rfl, _⟩ := h
  obtain ⟨⟨F, _, c⟩, s, _, _, _, _, _, hlt⟩ := (allP2 env memoF hmF n n (Nat.le_refl n)).2.1 root
    (SkaState.init reg) low st (fun _ => False) (CInv.init memoF reg) hw
    (by simp [SkaState.init, Treap.get_empty]) ha
  have hempty : ∀ x, Treap.get st.order x = none := by
    intro x
    cases e : Treap.get st.order x with
    | none => rfl
    | some o =>
      have := hlt x o e (by simp [SkaState.init])
      simp [SkaState.init] at this
  rw [show gCore (SkaState.init reg : SkaState M R).g = fun _ => none from gCore_empty] at s
  exact ⟨F, c.frz.ok, fun i d hd => c.frz.cover i d hd (hempty i), fun e he => (c.frz.sub e he).1,
    c.frz.wf, s⟩

/-! ## To `ConvergedGraphM` -/

/-- The entries of a memo, as `Entry`. -/
def MemEnt (memo : Memo M) : Entry → Prop := fun m =>
  ∃ f ms s ent, Treap.get memo f = some ms ∧ Treap.get ms s = some ent ∧ m = entOf ent.1 ent.2

/-- The entries of a memo under the formula `f` have the formula `f` (as
`+put:mi` stores them). -/
def MemoKeys (memo : Memo M) : Prop :=
  ∀ f ms s ent, Treap.get memo f = some ms → Treap.get ms s = some ent → ent.1.2 = f

/-- **A memo hit is a `HitEntry`**, for a memo whose entries are sound and
stored under their formula, on a subject sock that is not `%void`. -/
theorem memoHit_hitEntry {lib : Lib} {code : Bell → Option Nomm} {memo : Memo M} (hkey : MemoKeys memo)
    (hok : ∀ m, MemEnt memo m → MemoEntryOK lib code m) {e : Entry} (hnv : e.more ≠ Sock.void)
    (h : MemoHitE memo e) : HitEntry lib code (MemEnt memo) e := by
  obtain ⟨i, d, hg, hd⟩ := h
  obtain ⟨k, d0, hk, ht, hcore, _⟩ := gitMi_hit hg
  have hget : Treap.get memo e.fol = some (gutMi memo e.fol) := by
    unfold gutMi Treap.gut
    cases e2 : Treap.get memo e.fol with
    | none => simp only [gutMi, Treap.gut, e2, Option.getD_none, Treap.get_empty] at hk; cases hk
    | some ms => rfl
  have hm : MemEnt memo (entOf i d0) := ⟨e.fol, _, k, (i, d0), hget, hk, rfl⟩
  have hf : i.2 = e.fol := hkey _ _ _ _ hget hk
  exact ⟨entOf i d0, hm, hok _ hm, hnv, ht, hf.symm, by rw [hd, hcore]; rfl⟩

/-- **Convergence as `ConvergedGraphM`**: the frozen entries of the final
graph, with the memo hits as `HitEntry`s of the persistent memo. -/
theorem skaCallgraph_convergedM {lib : Lib} {code : Bell → Option Nomm} (env : Env R) (memoF : Memo M)
    (hmF : MemoWF memoF) (hkey : MemoKeys memoF) (hok : ∀ m, MemEnt memoF m → MemoEntryOK lib code m)
    {n : Nat} {root : Ident} {reg reg' : R} {g : Callgraph M} (hw : WellFormed root.1)
    (hnv : ∀ i d, Treap.get g i = some d → i.1 ≠ Sock.void)
    (h : skaCallgraph env n root memoF reg = some (g, reg')) :
    ∃ G : Entry → Prop, ConvergedGraphM lib code (MemEnt memoF) G ∧
      (∀ i d, Treap.get g i = some d → G (entOf i d)) ∧
      (∀ e, G e → ∃ d, Treap.get g (e.more, e.fol) = some d) ∧ GStepsR (fun _ => none) (gCore g) := by
  obtain ⟨F, hok', hcov, hsub, _, hs⟩ := skaCallgraph_frozen env memoF hmF hw h
  refine ⟨F, fun e he => ?_, hcov, fun e he => (hsub e he).imp fun _ h => h.1, hs⟩
  rcases hok' e he with ⟨P, hP, hr⟩ | hm
  · exact Or.inl ⟨P, fun s f a hp => answers_mono (fun _ h => h.1) (hP s f a hp), hr⟩
  · obtain ⟨d, hd, _⟩ := hsub e he
    exact Or.inr (memoHit_hitEntry hkey hok (hnv _ d hd) hm)

end Ana
end SkaModel
end Formalization
