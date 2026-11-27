import lemmas.Ska.PassFreeze
import lemmas.Ska.ConvAna

/-!
# Runs that push give a member a new callee (track F, Gaps 16)

This file proved C (`PassMoves`, a pass that goes on moves some member of
its start) for the freezing argument of the pass loop as it was before
dab8478.  Since dab8478 the loop does not cull between passes and C is no
longer needed: `passOn_moves`, `PassHyp`, `passHyp_step`, `passMoves_chain`
and `finPushes_of_freezeC` are deleted.  What stays are facts of one pass:
`+sweep` lists each member once (`sweep_nodup`), entries of the graph stay
entries (`inG_keep`), a `resolve` that moves `next` answers with an identity
that was not in the graph (`resolve_new`), and a run or a member loop that
pushes gives a member a callee it did not have (`run_new`, `memberLoop_new`).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. `+sweep` lists each member once -/

theorem sweepLoop_nodup {st : SkaState M R} {was : M Ident Unit} : ∀ (n : Nat)
    (seen : M Ident Unit) (stack : List (Ident × List Ident)) (out res : List Ident),
    sweepLoop st was n seen stack out = some res → (stack.map (·.1) ++ out).Nodup →
    (∀ x ∈ stack.map (·.1) ++ out, Treap.has seen x = true) → res.Nodup
  | 0, _, _, _, _, h, _, _ => by simp [sweepLoop] at h
  | n + 1, seen, [], out, res, h, hn, _ => by
    simp only [sweepLoop, Option.some.injEq] at h
    subst h; exact (List.reverse_perm out).nodup_iff.mpr (by simpa using hn)
  | n + 1, seen, (i, []) :: rest, out, res, h, hn, hs => by
    simp only [sweepLoop] at h
    refine sweepLoop_nodup n seen rest (i :: out) res h ?_ ?_
    · have hp : (rest.map (·.1) ++ i :: out).Perm (i :: (rest.map (·.1) ++ out)) := List.perm_middle
      exact hp.nodup_iff.mpr (by simpa using hn)
    · intro x hx
      apply hs
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_append_left _ List.mem_cons_self
        · exact List.mem_append_right _ h
  | n + 1, seen, (i, k :: ks) :: rest, out, res, h, hn, hs => by
    simp only [sweepLoop] at h
    split at h
    · exact sweepLoop_nodup n seen ((i, ks) :: rest) out res h (by simpa using hn)
        (fun x hx => hs x (by simpa using hx))
    · rename_i hc
      have hk : Treap.has seen k = false := by
        cases e : Treap.has seen k with
        | false => rfl
        | true => exact absurd (Or.inl e) hc
      refine sweepLoop_nodup n _ _ out res h ?_ ?_
      · simp only [List.map_cons, List.cons_append]
        refine List.nodup_cons.mpr ⟨fun hm => ?_, by simpa using hn⟩
        have := hs k (by simpa using hm)
        rw [hk] at this; cases this
      · intro x hx
        rw [Treap.has_ins]
        simp only [List.map_cons, List.cons_append, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (hs x (by simpa using hx))

theorem sweep_nodup {n : Nat} {id : Ident} {was : M Ident Unit} {st : SkaState M R} {res : List Ident}
    (h : sweep n id was st = some res) : res.Nodup :=
  sweepLoop_nodup n _ _ [] res h (by simp) (by
    intro x hx
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_singleton] at hx
    subst hx; rw [Treap.has_ins]; exact Or.inl rfl)

/-! ## 2. Entries of the graph stay entries -/

/-- An arm that keeps the old stack at the bottom and finalized entries keeps
every entry of the graph an entry. -/
theorem inG_keep {st st' : SkaState M R} {bt : Ident → Prop} (hi : SInv st) (hi' : SInv st')
    (hs : ∃ l, st'.stk = l ++ st.stk) (hf : Frame bt st st') {c : Ident}
    (h : Treap.get st.g c ≠ none) : Treap.get st'.g c ≠ none := by
  cases ho : Treap.get st.order c with
  | some o =>
    have hcs : c ∈ st.stk := (hi.ord_stk c).mp ⟨o, ho⟩
    obtain ⟨l, el⟩ := hs
    obtain ⟨d, hd⟩ := hi'.mem_g (by rw [el]; exact List.mem_append_right _ hcs)
    rw [hd]; simp
  | none =>
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp h
    rw [(hf.fin c d hd ho).1]; simp

theorem inCallees_ins_self (cs : M CalleeEntry Unit) (seat : Option Noun) (i : Ident) :
    InCallees (Treap.ins cs ⟨seat, i⟩) i :=
  ⟨seat, (Treap.has_ins _ _ _).mpr (Or.inl rfl)⟩

theorem inCallees_ins_of {cs : M CalleeEntry Unit} {c : Ident} (x : CalleeEntry) (h : InCallees cs c) :
    InCallees (Treap.ins cs x) c := by
  obtain ⟨seat, hs⟩ := h
  exact ⟨seat, (Treap.has_ins _ _ _).mpr (Or.inr hs)⟩

theorem inCallees_of_kids {st : SkaState M R} {m c : Ident} (h : c ∈ kids st m) :
    InCallees (calleesOf st m) c := by
  obtain ⟨⟨ce, v⟩, hm, e⟩ := List.mem_map.mp h
  have hg := (Treap.mem_tap _ _ _).mp hm
  refine ⟨ce.seat, ?_⟩
  have : (⟨ce.seat, c⟩ : CalleeEntry) = ce := by cases ce; simp only at e; rw [e]
  rw [this]; exact (Treap.has_iff _ _).mpr ⟨v, hg⟩

/-! ## 3. A `resolve` that pushes answers with a new identity -/

/-- **A `resolve` loop that moves `next` answers with an identity that was
not in the graph**: the only branch that changes the state is `+analyze`,
taken when the identity has no entry; the `%he` branch loops. -/
theorem resolve_new (env : Env R) (memoF : Memo M) : ∀ n orig idT (gs : GenS M R) r gs',
    resolve env memoF n orig idT gs = some (r, gs') → gs.st.next < gs'.st.next →
    Treap.get gs.st.g r.1 = none
  | 0 => by intro orig idT gs r gs' h; rw [resolve_zero] at h; cases h
  | n + 1 => by
    intro orig idT gs r gs' h hn
    rw [resolve_succ] at h
    unfold resolveStep at h
    split at h
    · split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at hn)
    · rename_i hg
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at hn
      · split at h
        · cases h
        · exact resolve_new env memoF n orig _ gs r gs' h hn
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨o, _, rfl, rfl⟩ := h; simp at hn
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨r', _, rfl, rfl⟩ := h; exact hg

/-! ## 4. A run that pushes gives its member a new callee -/

/-- Since the start `st0` of a run: if `next` moved, some callee of the run
was not in the graph at `st0`. -/
def NewInv (st0 : SkaState M R) (gs : GenS M R) : Prop :=
  st0.next < gs.st.next → ∃ c, InCallees gs.callees c ∧ Treap.get st0.g c = none

/-- **A run that moves `next` gives its member a callee that was not in the
graph when the run began.** -/
theorem runStep_new (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResP2 memoF (resolveR env memoF k)) {id : Ident} {index : Nat}
    {st : SkaState M R} {r : Nat × Bool × Bool} {st' : SkaState M R} {F : Entry → Prop}
    (hc : CInv memoF st F) (hid : id ∈ st.stk) (hidx : Treap.get st.order id = some index)
    (e : runStep (folLoop env memoF n) id index st = some (r, st')) (hn : st.next < st'.next) :
    ∃ c, InCallees (calleesOf st' id) c ∧ Treap.get st.g c = none := by
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  have e' : runEnd id (gitG st.g id) out gs = (r, st') := e
  have est : st' = (runEnd id (gitG st.g id) out gs).2 := (congrArg Prod.snd e').symm
  subst est
  generalize hdat : gitG st.g id = data at hn ⊢
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have c0 : CInv memoF st0 F := hc.congr rfl rfl rfl rfl rfl rfl rfl
  have hidx0 : index < st0.next := hc.ord.1 id index hidx
  let Inv : GenS M R → Prop := fun gs => RunInv memoF st0 F index gs ∧ NewInv st0 gs
  have r0 : Inv (genInit index st0) := by
    refine ⟨⟨F, fun _ h => h, c0, GStepsR.refl _, Keep.refl' _ rfl rfl rfl,
      Frame.refl' rfl rfl rfl rfl rfl rfl c0.s, Nat.le_refl _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x o hxo hx; exact absurd ((c0.s.ord_stk x).mp ⟨o, hxo⟩) hx
    · intro c hc'; exact absurd hc' (not_inCallees_empty c)
    · intro _ c hc'; exact absurd hc' (not_inCallees_empty c)
    · intro c hc'; exact absurd hc' (not_inCallees_empty c)
    · intro h; exact absurd h (Nat.lt_irrefl _)
  have hL : LocalStableC Inv := by
    intro gs gs' h hlf hcal
    refine ⟨runInv_stable memoF st0 F index gs gs' h.1 hlf hcal, fun hn' => ?_⟩
    rw [hlf.2.2.2.2.2.2.1] at hn'
    obtain ⟨c, h1, h2⟩ := h.2 hn'
    exact ⟨c, hcal ▸ h1, h2⟩
  have hR : ∀ k, k < n → ResOKD PfR Inv (resolveR env memoF k) := by
    intro k hk idT gs r gs' hi hw hnv e
    obtain ⟨a, b, c⟩ := resOKD_of_resP2 (hres k hk) st0 F index hidx0 idT gs r gs' hi.1 hw hnv e
    refine ⟨a, b, fun gs'' seat hlf hcs => ?_⟩
    obtain ⟨i1, p1⟩ := c gs'' seat hlf hcs
    refine ⟨⟨i1, fun hn' => ?_⟩, p1⟩
    obtain ⟨F1, _, hc1, _, k1, fr1, _⟩ := hi.1
    obtain ⟨⟨F', _, hc'⟩, _, k2, fr2, _, hcal2, _⟩ := hres k hk idT gs r gs' F1 hc1 hw.1 hw.2 hnv e
    rw [hlf.2.2.2.2.2.2.1] at hn'
    by_cases hg : gs.st.next < gs'.st.next
    · have hnew := resolve_new env memoF k idT idT gs r gs' e hg
      exact ⟨r.1, by rw [hcs]; exact inCallees_ins_self _ _ _,
        Classical.byContradiction fun hin => inG_keep c0.s hc1.s k1.1 fr1 hin hnew⟩
    · have hle := fr2.next
      obtain ⟨c', h1, h2⟩ := hi.2 (by omega)
      exact ⟨c', by rw [hcs, hcal2]; exact inCallees_ins_of _ h1, h2⟩
  have hnid : NormSock id.1 := by
    obtain ⟨d0, hd0⟩ := hc.s.mem_g hid; exact (hc.norm id d0 hd0).1
  obtain ⟨i1, _, _⟩ := run_folTopRD env memoF pfR_wf hL pfR_stable hR r0 ⟨hc.s.wf_stk hid, hnid⟩ hf
  obtain ⟨_, eg, _, _, _, en, _, _⟩ := runEnd_eff id data out gs
  have hcal : calleesOf (runEnd id data out gs).2 id = gs.callees := by
    unfold calleesOf gitG Treap.gut; rw [eg, Treap.get_put, if_pos rfl]; rfl
  rw [en] at hn
  obtain ⟨c, h1, h2⟩ := i1.2 hn
  exact ⟨c, by rw [hcal]; exact h1, h2⟩

theorem run_new (env : Env R) (memoF : Memo M) (hall : ∀ k, AllP2 env memoF k) {n : Nat} {id : Ident}
    {index : Nat} {st : SkaState M R} {r : Nat × Bool × Bool} {st' : SkaState M R} {F : Entry → Prop}
    (hc : CInv memoF st F) (hid : id ∈ st.stk) (hidx : Treap.get st.order id = some index)
    (e : run env memoF n id index st = some (r, st')) (hn : st.next < st'.next) :
    ∃ c, InCallees (calleesOf st' id) c ∧ Treap.get st.g c = none := by
  cases n with
  | zero => rw [run_zero] at e; cases e
  | succ k =>
    rw [run_succ] at e
    exact runStep_new env memoF (fun j _ => resP2_of_loop (resl := resolve env memoF j) (hall j).1)
      hc hid hidx e hn

/-! ## 5. The member loop -/

/-- What the member loop over `ms` gives: the invariant, the old stack at the
bottom, `next` grows, entries stay entries, the entries of the other identities
of the stack are kept, and if `ms` lists each member once and `next` moved,
some member of `ms` has a callee that was not in the graph at the start. -/
abbrev MemNewG (memoF : Memo M) (ms : List Ident) (st st' : SkaState M R) : Prop :=
  (∃ F', CInv memoF st' F') ∧ (∃ l, st'.stk = l ++ st.stk) ∧ st.next ≤ st'.next ∧
    (∀ c, Treap.get st.g c ≠ none → Treap.get st'.g c ≠ none) ∧
    (∀ j ∈ st.stk, j ∉ ms → Treap.get st'.g j = Treap.get st.g j) ∧
    (ms.Nodup → st.next < st'.next →
      ∃ m ∈ ms, ∃ c, InCallees (calleesOf st' m) c ∧ Treap.get st.g c = none)

/-- **A member loop that pushes gives one of its members a new callee.** -/
theorem memberLoop_new (env : Env R) (memoF : Memo M) (hall : ∀ k, AllP2 env memoF k) :
    ∀ n index pass (ms : List Ident) (st : SkaState M R) r st' (F : Entry → Prop),
      CInv memoF st F → memberLoop env memoF n index pass ms st = some (r, st') → MemNewG memoF ms st st'
  | 0 => by intro index pass ms st r st' F _ h; rw [memberLoop_zero] at h; cases h
  | n + 1 => by
    intro index pass ms st r st' F hc h
    rw [memberLoop_succ] at h
    cases ms with
    | nil =>
      simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨F, hc⟩, ⟨[], rfl⟩, Nat.le_refl _, fun _ h => h, fun _ _ _ => rfl,
        fun _ h => absurd h (Nat.lt_irrefl _)⟩
    | cons m ms =>
      have key : ∀ st1 : SkaState M R,
          ((Treap.get st.order m).bind fun o => (run env memoF n m o st1).bind fun r =>
            if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
            (memberLoop env memoF n index pass ms r.2).map fun t =>
              ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
          CInv memoF st1 F → st1.g = st.g → st1.order = st.order → st1.stk = st.stk → st1.next = st.next →
          MemNewG memoF (m :: ms) st st' := by
        intro st1 e c1 h1 h3 h4 h5
        simp only [Option.bind_eq_some_iff] at e
        obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
        have ho1 : Treap.get st1.order m = some o := by rw [h3]; exact ho
        have hm1 : m ∈ st1.stk := (c1.s.ord_stk m).mp ⟨o, ho1⟩
        obtain ⟨⟨F2, _, c2, _⟩, _, k2, fr2, _⟩ := (hall n).2.2.1 m o st1 r1 st2 F c1 hm1 ho1 hr
        have ing2 : ∀ c, Treap.get st.g c ≠ none → Treap.get st2.g c ≠ none := fun c hcg =>
          inG_keep c1.s c2.s k2.1 fr2 (by rw [h1]; exact hcg)
        have kp2 : ∀ j ∈ st.stk, j ≠ m → Treap.get st2.g j = Treap.get st.g j := fun j hj hjm => by
          rw [k2.2.2 j ⟨by rw [h4]; exact hj, hjm⟩, h1]
        have nx2 : st.next ≤ st2.next := by rw [← h5]; exact fr2.next
        have new2 : st.next < st2.next → ∃ c, InCallees (calleesOf st2 m) c ∧ Treap.get st.g c = none :=
          fun hn => by
            obtain ⟨c, a, b⟩ := run_new env memoF hall c1 hm1 ho1 hr (by rw [h5]; exact hn)
            exact ⟨c, a, by rw [← h1]; exact b⟩
        obtain ⟨l2, el2⟩ := k2.1
        rw [h4] at el2
        have hms : m ∈ st2.stk := by rw [el2]; exact List.mem_append_right _ (by rw [← h4]; exact hm1)
        split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨-, rfl⟩ := e
          refine ⟨⟨F2, c2⟩, ⟨l2, el2⟩, nx2, ing2,
            fun j hj hjn => kp2 j hj (fun e => hjn (e ▸ List.mem_cons_self)), fun _ hn => ?_⟩
          obtain ⟨c, a, b⟩ := new2 hn
          exact ⟨m, List.mem_cons_self, c, a, b⟩
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨⟨r3, st3⟩, h3', e⟩ := e
          simp only [Prod.mk.injEq] at e
          obtain ⟨-, rfl⟩ := e
          obtain ⟨⟨F3, c3⟩, ⟨l3, el3⟩, nx3, ing3, kp3, new3⟩ :=
            memberLoop_new env memoF hall n index pass ms st2 r3 st3 F2 c2 h3'
          refine ⟨⟨F3, c3⟩, ⟨l3 ++ l2, by rw [el3, el2, List.append_assoc]⟩, Nat.le_trans nx2 nx3,
            fun c hcg => ing3 c (ing2 c hcg), fun j hj hjn => ?_, fun hnd hn => ?_⟩
          · have hjm : j ≠ m := fun e => hjn (e ▸ List.mem_cons_self)
            have hjs : j ∈ st2.stk := by rw [el2]; exact List.mem_append_right _ hj
            rw [kp3 j hjs (fun h => hjn (List.mem_cons_of_mem _ h)), kp2 j hj hjm]
          · obtain ⟨hmn, hnd'⟩ := List.nodup_cons.mp hnd
            by_cases hn3 : st2.next < st3.next
            · obtain ⟨m', hm', c, a, b⟩ := new3 hnd' hn3
              exact ⟨m', List.mem_cons_of_mem _ hm', c, a,
                Classical.byContradiction fun hin => ing2 c hin b⟩
            · obtain ⟨c, a, b⟩ := new2 (by omega)
              have : calleesOf st3 m = calleesOf st2 m := by
                unfold calleesOf gitG Treap.gut; rw [kp3 m hms hmn]
              exact ⟨m, List.mem_cons_self, c, by rw [this]; exact a, b⟩
      simp only [memberStep] at h
      split at h
      · obtain ⟨cF, s, nx, ing, kp, new⟩ := memberLoop_new env memoF hall n index pass ms st r st' F hc h
        refine ⟨cF, s, nx, ing, fun j hj hjn => kp j hj (fun h => hjn (List.mem_cons_of_mem _ h)),
          fun hnd hn => ?_⟩
        obtain ⟨m', hm', rest⟩ := new (List.nodup_cons.mp hnd).2 hn
        exact ⟨m', List.mem_cons_of_mem _ hm', rest⟩
      · by_cases hp : pass > 1
        · simp only [hp, if_true] at h
          exact key _ h (hc.congr rfl rfl rfl rfl rfl rfl rfl) rfl rfl rfl rfl
        · simp only [hp, if_false] at h
          exact key _ h hc rfl rfl rfl rfl

end Ana
end SkaModel
end Formalization
