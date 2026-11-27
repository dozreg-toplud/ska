import lemmas.Compiler.OptLinkTotalBody

/-!
# `+alias` returns: the start of a block

The facts and immediates at the start of a block `o` with predecessors
`pre ≠ []` (`aliasStart`, `aliasStartImms`) and its edges (`aliasEdges`).

* **`aliasStart_inv`** (places `S1` .. `S5`): the join returns once every
  predecessor has closed facts, and for one predecessor its new block ends in
  a jump to `o` with a fact for the test register of a `%brn`, `%brz`,
  `%clq` (`TestFact`).  The facts it gives are closed and hold every register
  that has a fact in every predecessor.
* **`aliasStartImms_inv`** (place `B3`): the join of the immediates returns
  once every predecessor has immediates, and a register in it is in the
  immediates of every predecessor.
* **`aliasEdges_inv`** (place `E1`): the edges return once every predecessor
  has a new block, and each edge is a jump of the new block of a predecessor
  to `o`, with its arguments.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map]

theorem iref_joinReg {a b : Opt.InfoReg} {x : Nat} (h : IRef (Opt.joinReg a b) x) : IRef a x ∧ IRef b x := by
  simp only [IRef, Opt.joinReg, List.mem_filter, decide_eq_true_eq] at h
  rcases h with h | h | h | h | h
  · exact ⟨Or.inl h.1, Or.inl h.2⟩
  · exact ⟨Or.inr (Or.inl h.1), Or.inr (Or.inl h.2)⟩
  · split at h
    · rename_i e; exact ⟨Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inl (e.symm.trans h)))⟩
    · cases h
  · split at h
    · rename_i e; exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inl (e.symm.trans h))))⟩
    · cases h
  · split at h
    · rename_i e; exact ⟨Or.inr (Or.inr (Or.inr (Or.inr h))), Or.inr (Or.inr (Or.inr (Or.inr (e.symm.trans h))))⟩
    · cases h

theorem iref_joinRegE {a b : Opt.InfoReg} {x : Nat} (h : IRef (Opt.joinRegE a b) x) : IRef a x ∧ IRef b x := by
  unfold Opt.joinRegE at h
  split at h
  · rename_i e; subst e; exact ⟨h, h⟩
  · exact iref_joinReg h

theorem join_isSome {a b : Opt.AInfo} {k : Nat} (ha : (a k).isSome) (hb : (b k).isSome) :
    (Opt.joinInfoA a b k).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ha
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hb
  simp [Opt.joinInfoA, hx, hy]

/-- **The pointwise join keeps the facts closed.** -/
theorem aclo_join {a b : Opt.AInfo} (ha : AClo a) (hb : AClo b) : AClo (Opt.joinInfoA a b) := by
  intro k v x hk hx
  simp only [Opt.joinInfoA] at hk
  split at hk
  · rename_i x' y' ex ey
    cases hk
    obtain ⟨h1, h2⟩ := iref_joinRegE hx
    exact join_isSome (ha k x' x ex h1) (hb k y' x ey h2)
  · cases hk

theorem startFold (g : Opt.AGen Map) : ∀ (t : List Nat) (acc : Opt.AInfo), AClo acc →
    (∀ q ∈ t, ∃ i, g.info q = some i ∧ AClo i) →
    ∃ info, t.foldlM (fun acc o1 => (g.info o1).map fun i1 => Opt.joinInfoA acc i1) acc = some info ∧ AClo info ∧
      ∀ k, (acc k).isSome → (∀ q ∈ t, ∀ i, g.info q = some i → (i k).isSome) → (info k).isSome
  | [], acc, hc, _ => ⟨acc, rfl, hc, fun _ h _ => h⟩
  | q :: t, acc, hc, ht => by
    obtain ⟨i, hi, ci⟩ := ht q List.mem_cons_self
    obtain ⟨info, e, c, hk⟩ := startFold g t (Opt.joinInfoA acc i) (aclo_join hc ci)
      (fun q' hq' => ht q' (List.mem_cons_of_mem _ hq'))
    refine ⟨info, by simp only [List.foldlM_cons, hi, Option.map_some, Option.bind_some]; exact e, c, ?_⟩
    intro k ha hq
    exact hk k (join_isSome ha (hq q List.mem_cons_self i hi)) (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))

/-- The test register of a one-predecessor two-way end has a fact. -/
def TestFact (fin : Termin) (i : Opt.AInfo) : Prop :=
  match fin with
  | Termin.brn s _ _ => (i s).isSome
  | Termin.brz s _ _ => (i s).isSome
  | Termin.clq s _ _ => (i s).isSome
  | _ => True

theorem jab_post {m : Opt.AInfo} {k : Nat} {g : Opt.InfoReg → Opt.InfoReg} (hc : AClo m) (hs : (m k).isSome)
    (hg : ∀ v x, IRef (g v) x → IRef v x) : ∃ m', Opt.jabA m k g = some m' ∧ AClo m' ∧ KGrow m m' := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨_, jabA_of g hv, aclo_jab hc hv fun x hx => Or.inl (hg v x hx), kgrow_upd _ _ _⟩

/-- **`S1` .. `S5`**: the join at the start of a block returns, with closed
facts that hold every register with a fact in every predecessor. -/
theorem aliasStart_inv (g : Opt.AGen Map) (o p : Nat) (t : List Nat)
    (hi : ∀ q ∈ p :: t, ∃ i, g.info q = some i ∧ AClo i)
    (h1 : t = [] → ∃ pb, HoonMap.get g.new p = some pb ∧ (∃ j ∈ Opt.getJmps pb.fin, j.there = o) ∧
      ∀ i, g.info p = some i → TestFact pb.fin i) :
    ∃ info, Opt.aliasStart g o (p :: t) = some info ∧ AClo info ∧
      ∀ k, (∀ q ∈ p :: t, ∀ i, g.info q = some i → (i k).isSome) → (info k).isSome := by
  obtain ⟨i0, e0, c0⟩ := hi p List.mem_cons_self
  obtain ⟨info, ef, cf, kf⟩ := startFold g t i0 c0 (fun q hq => hi q (List.mem_cons_of_mem _ hq))
  have K : ∀ k, (∀ q ∈ p :: t, ∀ i, g.info q = some i → (i k).isSome) → (info k).isSome := fun k hk =>
    kf k (hk p List.mem_cons_self i0 e0) (fun q hq => hk q (List.mem_cons_of_mem _ hq))
  simp only [Opt.aliasStart, e0, Option.bind_some, ef]
  by_cases ht : t = []
  · subst ht
    rw [if_neg (fun h => h rfl)]
    obtain ⟨pb, hpb, ⟨j, hj, hjo⟩, htf⟩ := h1 rfl
    have hT := htf i0 e0
    have ei : info = i0 := by simpa using ef.symm
    subst ei
    rw [hpb, Option.bind_some]
    have J := fun (gg : Opt.InfoReg → Opt.InfoReg) (hg : ∀ v x, IRef (gg v) x → IRef v x) s (hs : (info s).isSome) =>
      (show ∃ m', Opt.jabA info s gg = some m' ∧ AClo m' ∧ ∀ k, (∀ q ∈ [p], ∀ i, g.info q = some i → (i k).isSome) →
          (m' k).isSome from
        let ⟨m', e, c, gk⟩ := jab_post cf hs hg; ⟨m', e, c, fun k hk => gk k (K k hk)⟩)
    cases hf : pb.fin with
    | brn s z o' =>
      rw [hf] at hT hj; simp only [TestFact] at hT
      dsimp only
      simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
      by_cases c1 : z.there = o ∧ o'.there ≠ o
      · rw [if_pos c1]; refine J _ ?_ s hT; exact fun _ _ h => h
      · rw [if_neg c1]
        by_cases c2 : o'.there = o ∧ z.there ≠ o
        · rw [if_pos c2]; refine J _ ?_ s hT; exact fun _ _ h => h
        · rw [if_neg c2]
          by_cases c3 : z.there = o'.there ∧ z.there = o
          · rw [if_pos c3]; refine J _ ?_ s hT; exact fun _ _ h => h
          · exfalso
            rcases hj with rfl | rfl
            · by_cases e : o'.there = j.there
              · exact c3 ⟨e.symm, hjo⟩
              · exact c1 ⟨hjo, fun h => e (h.trans hjo.symm)⟩
            · by_cases e : z.there = j.there
              · exact c3 ⟨e, e.trans hjo⟩
              · exact c2 ⟨hjo, fun h => e (h.trans hjo.symm)⟩
    | brz s z o' =>
      rw [hf] at hT; simp only [TestFact] at hT
      dsimp only
      obtain ⟨si, esi⟩ := Option.isSome_iff_exists.1 hT
      by_cases c1 : z.there = o ∧ o'.there ≠ o
      · rw [if_pos c1]; refine J _ ?_ s hT; exact fun _ _ h => h
      · rw [if_neg c1]
        by_cases c2 : o'.there = o ∧ z.there ≠ o
        · rw [if_pos c2, esi, Option.bind_some]
          by_cases c3 : si.isLoob = true
          · rw [if_pos c3]; refine J _ ?_ s hT; exact fun _ _ h => h
          · rw [if_neg c3]; exact ⟨_, rfl, cf, K⟩
        · rw [if_neg c2]; exact ⟨_, rfl, cf, K⟩
    | clq s z o' =>
      rw [hf] at hT hj; simp only [TestFact] at hT
      dsimp only
      simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
      by_cases c1 : z.there = o ∧ o'.there ≠ o
      · rw [if_pos c1]; refine J _ ?_ s hT; exact fun _ _ h => h
      · rw [if_neg c1]
        by_cases c2 : o'.there = o
        · rw [if_pos c2]; exact ⟨_, rfl, cf, K⟩
        · exfalso
          rcases hj with rfl | rfl
          · exact c1 ⟨hjo, fun h => c2 h⟩
          · exact c2 hjo
    | _ => exact ⟨_, rfl, cf, K⟩
  · rw [if_pos ht]
    exact ⟨info, rfl, cf, K⟩

/-- **`B3`**: the join of the immediates returns, and a register in it is in
the immediates of every predecessor. -/
theorem aliasStartImms_inv (g : Opt.AGen Map) (pre : List Nat)
    (hm : ∀ q ∈ pre, (g.imms q).isSome) :
    ∃ im, Opt.aliasStartImms g pre = some im ∧
      ∀ n x, x ∈ im n → ∀ q ∈ pre, ∃ m, g.imms q = some m ∧ x ∈ m n := by
  cases pre with
  | nil => exact ⟨_, rfl, fun _ _ h => by cases h⟩
  | cons p t =>
    obtain ⟨m0, e0⟩ := Option.isSome_iff_exists.1 (hm p List.mem_cons_self)
    suffices F : ∀ (t : List Nat) (acc : Opt.AImms), (∀ q ∈ t, (g.imms q).isSome) →
        ∃ im, t.foldlM (fun acc o1 => (g.imms o1).map fun m1 => Opt.joinImmsA acc m1) acc = some im ∧
          ∀ n x, x ∈ im n → x ∈ acc n ∧ ∀ q ∈ t, ∃ m, g.imms q = some m ∧ x ∈ m n by
      obtain ⟨im, e, h⟩ := F t m0 (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      refine ⟨im, by simp only [Opt.aliasStartImms, e0, Option.bind_some]; exact e, fun n x hx q hq => ?_⟩
      obtain ⟨h1, h2⟩ := h n x hx
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨m0, e0, h1⟩
      · exact h2 q hq
    intro t
    induction t with
    | nil => exact fun acc _ => ⟨acc, rfl, fun _ _ h => ⟨h, fun _ h => by cases h⟩⟩
    | cons q t ih =>
      intro acc ht
      obtain ⟨m, em⟩ := Option.isSome_iff_exists.1 (ht q List.mem_cons_self)
      obtain ⟨im, e, h⟩ := ih (Opt.joinImmsA acc m) (fun q' hq' => ht q' (List.mem_cons_of_mem _ hq'))
      refine ⟨im, by simp only [List.foldlM_cons, em, Option.map_some, Option.bind_some]; exact e, fun n x hx => ?_⟩
      obtain ⟨h1, h2⟩ := h n x hx
      simp only [Opt.joinImmsA, List.mem_filter, decide_eq_true_eq] at h1
      refine ⟨h1.1, fun q' hq' => ?_⟩
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨m, em, h1.2⟩
      · exact h2 q' hq'

/-- **`E1`**: the edges into `o` return once every predecessor has a new
block; each is a jump of the new block of a predecessor to `o`. -/
theorem aliasEdges_inv (g : Opt.AGen Map) (o : Nat) (pre : List Nat)
    (hn : ∀ q ∈ pre, (HoonMap.get g.new q).isSome) :
    ∃ es, Opt.aliasEdges g o pre = some es ∧
      ∀ e ∈ es, e.1 ∈ pre ∧ ∃ pb, HoonMap.get g.new e.1 = some pb ∧ ∃ j ∈ Opt.getJmps pb.fin, j.there = o ∧ e.2 = j.args := by
  have M : ∀ (l : List Nat), (∀ q ∈ l, (HoonMap.get g.new q).isSome) →
      ∃ ls, (l.mapM fun p => (HoonMap.get g.new p).map fun pb =>
        (Opt.getJmps pb.fin).filterMap fun j => if j.there = o then some (p, j.args) else none) = some ls ∧
        ∀ e ∈ ls.flatten, e.1 ∈ l ∧ ∃ pb, HoonMap.get g.new e.1 = some pb ∧
          ∃ j ∈ Opt.getJmps pb.fin, j.there = o ∧ e.2 = j.args := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], rfl, fun _ h => by simp at h⟩
    | cons q l ih =>
      intro hl
      obtain ⟨pb, epb⟩ := Option.isSome_iff_exists.1 (hl q List.mem_cons_self)
      obtain ⟨ls, e, h⟩ := ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq'))
      refine ⟨_ :: ls, by simp only [List.mapM_cons, epb, Option.map_some, Option.bind_some, e]; rfl, ?_⟩
      intro x hx
      rcases List.mem_append.1 (List.flatten_cons ▸ hx) with hx | hx
      · obtain ⟨j, hj, hjx⟩ := List.mem_filterMap.1 hx
        split at hjx
        · rename_i c; cases hjx; exact ⟨List.mem_cons_self, pb, epb, j, hj, c, rfl⟩
        · cases hjx
      · obtain ⟨h1, h2⟩ := h x hx; exact ⟨List.mem_cons_of_mem _ h1, h2⟩
  obtain ⟨ls, e, h⟩ := M pre hn
  exact ⟨ls.flatten, by simp only [Opt.aliasEdges, e, Option.map_some], h⟩

/-! ## The parameter loop (`I1` .. `I3`) -/

theorem iref_foldJoin {x : Nat} : ∀ (t : List Opt.InfoReg) (h : Opt.InfoReg),
    IRef (t.foldl (fun b a => Opt.joinReg a b) h) x → IRef h x ∧ ∀ a ∈ t, IRef a x
  | [], h, hx => ⟨hx, fun _ h => by cases h⟩
  | a :: t, h, hx => by
    obtain ⟨h1, h2⟩ := iref_foldJoin t (Opt.joinReg a h) hx
    obtain ⟨ha, hh⟩ := iref_joinReg h1
    exact ⟨hh, fun a' ha' => by
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact ha
      · exact h2 a' ha'⟩

theorem filterMap_id_len : ∀ (l : List (Option Opt.InfoReg)), none ∈ l → (l.filterMap id).length < l.length
  | [], h => by cases h
  | a :: l, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · simp only [List.filterMap_cons, id, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filterMap_le _ _)
    · have := filterMap_id_len l h'
      cases a <;> simp only [List.filterMap_cons, id, List.length_cons] <;> omega

/-- A register `param-info` refers to is referred to by the fact of every
edge. -/
theorem iref_paramInfo {ins : List (Option Opt.InfoReg)} {x : Nat} (h : IRef (Opt.paramInfo ins) x) :
    ins ≠ [] ∧ ∀ a ∈ ins, ∃ v, a = some v ∧ IRef v x := by
  unfold Opt.paramInfo at h
  split at h
  · exact absurd h (iref_empty x)
  · rename_i hd tl e
    split at h
    · rename_i hlen
      have hall : ∀ a ∈ ins, ∃ v, a = some v := fun a ha => by
        cases a with
        | some v => exact ⟨v, rfl⟩
        | none => have := filterMap_id_len ins ha; omega
      obtain ⟨h1, h2⟩ := iref_foldJoin tl hd h
      refine ⟨fun hn => by subst hn; simp at e, fun a ha => ?_⟩
      obtain ⟨v, rfl⟩ := hall a ha
      have hv : v ∈ ins.filterMap id := List.mem_filterMap.2 ⟨some v, ha, rfl⟩
      rw [e] at hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨_, rfl, h1⟩
      · exact ⟨v, rfl, h2 v hv⟩
    · simp [IRef] at h

theorem mapM_aliasIn (g : Opt.AGen Map) : ∀ (es : List (Nat × List (Option Nat))),
    (∀ e ∈ es, (Opt.aliasIn g e).isSome) →
    ∃ ins, es.mapM (Opt.aliasIn g) = some ins ∧ (es ≠ [] → ins ≠ []) ∧ ∀ e ∈ es, ∃ a ∈ ins, Opt.aliasIn g e = some a
  | [], _ => ⟨[], rfl, fun h => absurd rfl h, fun _ h => by cases h⟩
  | e :: es, h => by
    obtain ⟨a, ea⟩ := Option.isSome_iff_exists.1 (h e List.mem_cons_self)
    obtain ⟨ins, ei, -, hi⟩ := mapM_aliasIn g es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    refine ⟨a :: ins, by simp only [List.mapM_cons, ea, Option.bind_some, ei]; rfl, (fun _ h => by cases h),
      fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨a, List.mem_cons_self, ea⟩
    · obtain ⟨a', ha', h'⟩ := hi e' he'; exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem aliasIn_some {g : Opt.AGen Map} {e : Nat × List (Option Nat)} {v : Opt.InfoReg}
    (h : Opt.aliasIn g e = some (some v)) : ∃ i u, g.info e.1 = some i ∧ i u = some v := by
  obtain ⟨p, args⟩ := e
  cases args with
  | nil => cases h
  | cons a args =>
    cases a with
    | none => cases h
    | some u =>
      simp only [Opt.aliasIn, Option.map_eq_some_iff, Option.some.injEq, exists_eq_right] at h
      obtain ⟨i, hi, hu⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨i, u, hi, hu⟩

/-- **`I1` .. `I3`**: the parameter loop returns once every edge passes at
least as many arguments as there are parameters (`I1`) and every register an
edge passes to a parameter has a fact in its predecessor (`I2`, `I3`).  With
closed facts in the predecessors, and a fact in `loc` for every register with
a fact in the predecessor of every edge, the facts after are closed, keep
those of `loc`, and hold every parameter. -/
theorem aliasPars_inv (g : Opt.AGen Map) : ∀ (ps : List Nat) (es : List (Nat × List (Option Nat))) (loc : Opt.AInfo),
    AClo loc → (∀ e ∈ es, ∃ i, g.info e.1 = some i ∧ AClo i) →
    (∀ x, es ≠ [] → (∀ e ∈ es, ∃ i, g.info e.1 = some i ∧ (i x).isSome) → (loc x).isSome) →
    (∀ e ∈ es, ps.length ≤ e.2.length) →
    (∀ e ∈ es, ∀ k u, k < ps.length → e.2[k]? = some (some u) → ((g.info e.1).bind fun i => i u).isSome) →
    ∃ loc', Opt.aliasPars g ps es loc = some loc' ∧ AClo loc' ∧ KGrow loc loc' ∧ ∀ x ∈ ps, (loc' x).isSome
  | [], es, loc, hc, _, _, _, _ => ⟨loc, rfl, hc, kgrow_refl _, fun _ h => by cases h⟩
  | x :: ps, es, loc, hc, hci, hR, hl, hu => by
    have hin : ∀ e ∈ es, (Opt.aliasIn g e).isSome := by
      intro e he
      obtain ⟨p, args⟩ := e
      cases args with
      | nil => have := hl _ he; simp at this
      | cons a args =>
        cases a with
        | none => rfl
        | some u =>
          simp only [Opt.aliasIn, Option.isSome_map]
          exact hu _ he 0 u (by simp) rfl
    obtain ⟨ins, ei, hne, hins⟩ := mapM_aliasIn g es hin
    have cw : AClo (Opt.updA loc x (some (Opt.paramInfo ins))) := aclo_upd hc fun y hy => by
      obtain ⟨hne', hall⟩ := iref_paramInfo hy
      refine kgrow_upd _ _ _ _ (hR y ?_ ?_)
      · intro he; subst he; cases ei; exact hne' rfl
      · intro e he
        obtain ⟨a, ha, ea⟩ := hins e he
        obtain ⟨v, rfl, hv⟩ := hall a ha
        obtain ⟨i, u, hi, hiu⟩ := aliasIn_some ea
        obtain ⟨i', hi', ci⟩ := hci e he
        rw [hi] at hi'; cases hi'
        exact ⟨i, hi, ci u v y hiu hv⟩
    obtain ⟨loc', e2, c2, g2, p2⟩ := aliasPars_inv g ps (es.map fun e => (e.1, e.2.tail)) _ cw
      (fun e he => by
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he; exact hci e0 he0)
      (fun y hne' hall => by
        refine kgrow_upd _ _ _ _ (hR y (fun h => hne' (by simp [h])) fun e he => ?_)
        exact hall (e.1, e.2.tail) (List.mem_map.2 ⟨e, he, rfl⟩))
      (fun e he => by
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
        have := hl e0 he0; simp only [List.length_cons] at this; simp only [List.length_tail]; omega)
      (fun e he k u hk hku => by
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
        refine hu e0 he0 (k + 1) u (by simp only [List.length_cons]; omega) ?_
        simpa [List.getElem?_tail] using hku)
    refine ⟨loc', ?_, c2, kgrow_trans (kgrow_upd _ _ _) g2, fun y hy => ?_⟩
    · simp only [Opt.aliasPars, ei, Option.bind_some]; exact e2
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact g2 _ (by simp [Opt.updA])
      · exact p2 y hy

end Compiler
end Formalization
