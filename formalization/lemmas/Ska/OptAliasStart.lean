import lemmas.Ska.OptAliasWalk

/-!
# The facts at the start of a block of `+alias`

At the start of a walked block `o`, the facts are the join of the facts at
the end of every predecessor that `rev.gen` still lists, refined after a
one-predecessor `%brn`, `%brz` or `%clq` by the side that goes to `o`
(`aliasStart`), and the immediates the intersection (`aliasStartImms`).

**`ast_start`**: if the facts at the end of one listed predecessor `q` hold of
the register file `R` there (`FactsOK`), then so do the facts of
`aliasStart`, given that when `q` is the only predecessor its end (in the
code after) goes to `o` on `R` (`GoesTo`: the side the execution took).
`ast_joinL`, `ast_joinR` (the pointwise join with an equal value kept is
weaker than each side), `ast_fold` (the fold over the other predecessors), and
the refinement: a `%brn` that goes to `o` on one side only knows its test is
`0` or `1`, both sides `o` that it is a loobean; a `%brz` taken to its `z`
side knows `0`, to its other side `1` when the test was known loobean; a
`%clq` to its `z` side knows a cell.  **`ast_imms`**: the immediates of one
predecessor that hold on `R` give those of the start.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- The facts of a map hold on the register file `R`. -/
def FactsOK (R : Nat → Option Noun) (m : AInfo) : Prop :=
  ∀ r i v, m r = some i → R r = some v → InfoHolds R i v

/-- The immediates hold on `R`. -/
def ImmsOK (R : Nat → Option Noun) (m : AImms) : Prop := ∀ n r, r ∈ m n → R r = some n

/-- An end of the code after goes to `o` on the register file `R`. -/
def GoesTo (R : Nat → Option Noun) (o : Nat) : Termin → Prop
  | Termin.brn s z o' => (R s = some (Noun.atom 0) ∧ z.there = o) ∨ (R s = some (Noun.atom 1) ∧ o'.there = o)
  | Termin.brz s z o' =>
      (R s = some (Noun.atom 0) ∧ z.there = o) ∨ (∃ v, R s = some v ∧ v ≠ Noun.atom 0 ∧ o'.there = o)
  | Termin.clq s z o' =>
      (∃ a b, R s = some (Noun.cell a b) ∧ z.there = o) ∨ (∃ a, R s = some (Noun.atom a) ∧ o'.there = o)
  | _ => True

section
variable {R : Nat → Option Noun}

theorem ast_with_imm {i : InfoReg} {v n : Noun} (h : InfoHolds R i v) (hv : v = n) :
    InfoHolds R { i with hasImm := some n } v := by
  obtain ⟨c, l, _, hh, ht, ho, to, dc⟩ := h
  exact ⟨c, l, fun n' e => by simp only [Option.some.injEq] at e; subst e; exact hv, hh, ht, ho, to, dc⟩

theorem ast_joinE_L {a b : InfoReg} {v : Noun} (h : InfoHolds R a v) : InfoHolds R (joinRegE a b) v := by
  unfold joinRegE; split
  · exact h
  · exact info_joinL h

theorem ast_joinE_R {a b : InfoReg} {v : Noun} (h : InfoHolds R b v) : InfoHolds R (joinRegE a b) v := by
  unfold joinRegE; split
  · rename_i e; subst e; exact h
  · exact info_joinR h

theorem ast_joinL {a b : AInfo} (h : FactsOK R a) : FactsOK R (joinInfoA a b) := by
  intro r i v hr hv
  cases ha : a r <;> cases hb : b r <;> simp only [joinInfoA, ha, hb, reduceCtorEq, Option.some.injEq] at hr
  subst hr; exact ast_joinE_L (h r _ v ha hv)

theorem ast_joinR {a b : AInfo} (h : FactsOK R b) : FactsOK R (joinInfoA a b) := by
  intro r i v hr hv
  cases ha : a r <;> cases hb : b r <;> simp only [joinInfoA, ha, hb, reduceCtorEq, Option.some.injEq] at hr
  subst hr; exact ast_joinE_R (h r _ v hb hv)

/-- The join over the other predecessors keeps the facts of one of them. -/
theorem ast_fold (g : AGen Map) (R : Nat → Option Noun) : ∀ (t : List Nat) (acc info : AInfo),
    t.foldlM (fun acc o1 => (g.info o1).map fun i1 => joinInfoA acc i1) acc = some info →
    (FactsOK R acc ∨ ∃ q ∈ t, ∃ iq, g.info q = some iq ∧ FactsOK R iq) → FactsOK R info
  | [], acc, info, h, hh => by
    simp only [List.foldlM_nil] at h
    cases h
    rcases hh with hh | ⟨q, hq, _⟩
    · exact hh
    · cases hq
  | o1 :: t, acc, info, h, hh => by
    simp only [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i1, hi1, rfl⟩ := Option.map_eq_some_iff.mp h1
    apply ast_fold g R t _ info h
    rcases hh with hh | ⟨q, hq, iq, hiq, hR⟩
    · exact Or.inl (ast_joinL hh)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hiq] at hi1; cases hi1; exact Or.inl (ast_joinR hR)
      · exact Or.inr ⟨q, hq, iq, hiq, hR⟩

/-- A refinement of the facts of `s` that holds of its value keeps
`FactsOK`. -/
theorem ast_jab {m m' : AInfo} {s : Nat} {f : InfoReg → InfoReg} (hm : FactsOK R m) (hj : jabA m s f = some m')
    (hf : ∀ i v, m s = some i → R s = some v → InfoHolds R (f i) v) : FactsOK R m' := by
  obtain ⟨i, hi, rfl⟩ := as_jab hj
  exact as_info_upd hm (fun v hv => hf i v hi hv)

/-- **The facts at the start of a block** hold on the register file at the
end of the predecessor the execution came from. -/
theorem ast_start {g : AGen Map} {o q : Nat} {pre : List Nat} {info iq : AInfo}
    (h : aliasStart g o pre = some info) (hq : q ∈ pre) (hiq : g.info q = some iq) (hR : FactsOK R iq)
    (hgo : pre = [q] → ∀ pb, HoonMap.get g.new q = some pb → GoesTo R o pb.fin) : FactsOK R info := by
  cases pre with
  | nil => cases hq
  | cons p t =>
    simp only [aliasStart] at h
    obtain ⟨i0, hi0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨info0, hf, h⟩ := Option.bind_eq_some_iff.mp h
    have hj : FactsOK R info0 := ast_fold g R t i0 info0 hf (by
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hiq] at hi0; cases hi0; exact Or.inl hR
      · exact Or.inr ⟨q, hq, iq, hiq, hR⟩)
    by_cases ht : t = []
    · subst ht
      have hqp : q = p := by simpa using hq
      subst hqp
      simp only [ne_eq, not_true_eq_false, if_false] at h
      obtain ⟨pb, hpb, h⟩ := Option.bind_eq_some_iff.mp h
      have hg := hgo rfl pb hpb
      generalize pb.fin = fin at h hg
      cases fin with
      | brn s z o' =>
        simp only [GoesTo] at hg
        simp only at h
        split at h
        · rename_i hc
          refine ast_jab hj h fun i v _ hv => ast_with_imm (hj s i v ‹_› hv) ?_
          rcases hg with ⟨e, -⟩ | ⟨-, e⟩
          · rw [hv] at e; cases e; rfl
          · exact absurd e hc.2
        · split at h
          · rename_i _ hc
            refine ast_jab hj h fun i v _ hv => ast_with_imm (hj s i v ‹_› hv) ?_
            rcases hg with ⟨-, e⟩ | ⟨e, -⟩
            · exact absurd e hc.2
            · rw [hv] at e; cases e; rfl
          · split at h
            · refine ast_jab hj h fun i v hi hv => as_with_loob (hj s i v hi hv) ?_
              rcases hg with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [hv] at e <;> cases e
              · exact Or.inl rfl
              · exact Or.inr rfl
            · cases h
      | brz s z o' =>
        simp only [GoesTo] at hg
        simp only at h
        split at h
        · rename_i hc
          refine ast_jab hj h fun i v _ hv => ast_with_imm (hj s i v ‹_› hv) ?_
          rcases hg with ⟨e, -⟩ | ⟨-, -, -, e⟩
          · rw [hv] at e; cases e; rfl
          · exact absurd e hc.2
        · split at h
          · rename_i _ hc
            obtain ⟨si, hsi, h⟩ := Option.bind_eq_some_iff.mp h
            split at h
            · rename_i hl
              refine ast_jab hj h fun i v hi hv => ast_with_imm (hj s i v hi hv) ?_
              rw [hsi] at hi; cases hi
              rcases hg with ⟨-, e⟩ | ⟨w, ew, hw, -⟩
              · exact absurd e hc.2
              · rw [hv] at ew; cases ew
                rcases (hj s si v hsi hv).2.1 hl with e | e
                · exact absurd e hw
                · exact e
            · cases h; exact hj
          · cases h; exact hj
      | clq s z o' =>
        simp only [GoesTo] at hg
        simp only at h
        split at h
        · rename_i hc
          refine ast_jab hj h fun i v hi hv => as_with_cell (hj s i v hi hv) ?_
          rcases hg with ⟨a, b, e, -⟩ | ⟨-, -, e⟩
          · rw [hv] at e; cases e; exact ⟨a, b, rfl⟩
          · exact absurd e hc.2
        · split at h
          · cases h; exact hj
          · cases h
      | hop => cases h; exact hj
      | lti => cases h; exact hj
      | eqq => cases h; exact hj
      | jmp => cases h; exact hj
      | jmf => cases h; exact hj
      | jsp => cases h; exact hj
      | jsf => cases h; exact hj
      | don => cases h; exact hj
      | bom => cases h; exact hj
    · simp only [ne_eq, ht, not_false_eq_true, if_true, Option.some.injEq] at h
      subst h; exact hj

theorem ast_immsL {a b : AImms} (h : ImmsOK R a) : ImmsOK R (joinImmsA a b) :=
  fun n r hr => h n r (List.mem_filter.mp hr).1

theorem ast_immsR {a b : AImms} (h : ImmsOK R b) : ImmsOK R (joinImmsA a b) :=
  fun n r hr => h n r (by simpa using (List.mem_filter.mp hr).2)

theorem ast_imms_fold (g : AGen Map) (R : Nat → Option Noun) : ∀ (t : List Nat) (acc m : AImms),
    t.foldlM (fun acc o1 => (g.imms o1).map fun m1 => joinImmsA acc m1) acc = some m →
    (ImmsOK R acc ∨ ∃ q ∈ t, ∃ mq, g.imms q = some mq ∧ ImmsOK R mq) → ImmsOK R m
  | [], acc, m, h, hh => by
    simp only [List.foldlM_nil] at h
    cases h
    rcases hh with hh | ⟨q, hq, _⟩
    · exact hh
    · cases hq
  | o1 :: t, acc, m, h, hh => by
    simp only [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m1, hm1, rfl⟩ := Option.map_eq_some_iff.mp h1
    apply ast_imms_fold g R t _ m h
    rcases hh with hh | ⟨q, hq, mq, hmq, hR⟩
    · exact Or.inl (ast_immsL hh)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hmq] at hm1; cases hm1; exact Or.inl (ast_immsR hR)
      · exact Or.inr ⟨q, hq, mq, hmq, hR⟩

/-- **The immediates at the start of a block** hold on the register file at
the end of a listed predecessor whose immediates hold there. -/
theorem ast_imms {g : AGen Map} {pre : List Nat} {m mq : AImms} {q : Nat}
    (h : aliasStartImms g pre = some m) (hq : q ∈ pre) (hmq : g.imms q = some mq) (hR : ImmsOK R mq) :
    ImmsOK R m := by
  cases pre with
  | nil => cases hq
  | cons p t =>
    simp only [aliasStartImms] at h
    obtain ⟨m0, hm0, h⟩ := Option.bind_eq_some_iff.mp h
    exact ast_imms_fold g R t m0 m h (by
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hmq] at hm0; cases hm0; exact Or.inl hR
      · exact Or.inr ⟨q, hq, mq, hmq, hR⟩)

/-- At the entry block there are no immediates. -/
theorem ast_imms_nil {g : AGen Map} {m : AImms} (h : aliasStartImms g [] = some m) : ImmsOK R m := by
  simp only [aliasStartImms, Option.some.injEq] at h
  subst h; intro n r hr; cases hr

/-- At the entry block the facts are empty. -/
theorem ast_entry (nargs : Nat) : FactsOK R (entryInfo nargs) := by
  intro r i v hr _
  unfold entryInfo at hr
  split at hr
  · cases hr; exact info_empty
  · cases hr

/-! ## The parameters (`aliasPars`) -/

theorem ast_join_names {a b : InfoReg} {x : Nat} (h : ANames (joinReg a b) x) : ANames a x ∧ ANames b x := by
  rcases h with h | h | h | h | h
  · simp only [joinReg] at h; split at h
    · rename_i e; exact ⟨Or.inl h, Or.inl (e ▸ h)⟩
    · cases h
  · simp only [joinReg] at h; split at h
    · rename_i e; exact ⟨Or.inr (Or.inl h), Or.inr (Or.inl (e ▸ h))⟩
    · cases h
  · simp only [joinReg, List.mem_filter, decide_eq_true_eq] at h
    exact ⟨Or.inr (Or.inr (Or.inl h.1)), Or.inr (Or.inr (Or.inl h.2))⟩
  · simp only [joinReg, List.mem_filter, decide_eq_true_eq] at h
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h.1))), Or.inr (Or.inr (Or.inr (Or.inl h.2)))⟩
  · simp only [joinReg] at h; split at h
    · rename_i e; exact ⟨Or.inr (Or.inr (Or.inr (Or.inr h))), Or.inr (Or.inr (Or.inr (Or.inr (e ▸ h))))⟩
    · cases h

theorem ast_fold_names {x : Nat} : ∀ (t : List InfoReg) (acc : InfoReg),
    ANames (t.foldl (fun b a => joinReg a b) acc) x → ANames acc x ∧ ∀ c ∈ t, ANames c x
  | [], acc, h => ⟨h, fun _ hc => absurd hc List.not_mem_nil⟩
  | c :: t, acc, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ast_fold_names t _ h
    obtain ⟨hc, hacc⟩ := ast_join_names h1
    exact ⟨hacc, fun c' hc' => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hc
      · exact h2 c' hc'⟩

/-- **The names of `param-info`** are names of every edge's facts. -/
theorem ast_param_names {ins : List (Option InfoReg)} {a : InfoReg} {x : Nat} (ha : some a ∈ ins)
    (h : ANames (paramInfo ins) x) : ANames a x := by
  have hm : a ∈ ins.filterMap id := List.mem_filterMap.mpr ⟨some a, ha, rfl⟩
  unfold paramInfo at h
  split at h
  · exact absurd h ab_nm_empty
  · rename_i hd tl heq
    rw [heq] at hm
    dsimp only at h
    have hj : ANames (tl.foldl (fun b a => joinReg a b) hd) x := by
      split at h
      · exact h
      · rcases h with h | h | h | h | h <;> simp at h
    obtain ⟨h1, h2⟩ := ast_fold_names tl hd hj
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h1
    · exact h2 a hm

theorem ast_mapM_mem {α β : Type} {f : α → Option β} : ∀ {l : List α} {ins : List β} {e : α},
    l.mapM f = some ins → e ∈ l → ∃ y, y ∈ ins ∧ f e = some y
  | [], _, _, _, he => absurd he List.not_mem_nil
  | a :: l, ins, e, h, he => by
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hfy⟩ := ast_mapM_mem hbs he
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- Facts whose names keep their values hold in the new file. -/
theorem ast_frame_set {R R' : Nat → Option Noun} {i : InfoReg} {v : Noun} (h : InfoHolds R i v)
    (hn : ∀ x, ANames i x → R' x = R x) : InfoHolds R' i v := by
  obtain ⟨c, l, im, hh, ht, ho, to, dc⟩ := h
  refine ⟨c, l, im, fun d hd => ?_, fun d hd => ?_, fun x hx => ?_, fun x hx => ?_, fun d hd => ?_⟩
  · rw [hn d (Or.inl hd)]; exact hh d hd
  · rw [hn d (Or.inr (Or.inl hd))]; exact ht d hd
  · rw [hn x (Or.inr (Or.inr (Or.inl hx)))]; exact ho x hx
  · rw [hn x (Or.inr (Or.inr (Or.inr (Or.inl hx))))]; exact to x hx
  · rw [hn d (Or.inr (Or.inr (Or.inr (Or.inr hd))))]; exact dc d hd

/-- **The parameter loop keeps the facts**: along the edge `(q, args)` that
the execution took, with `R` the file at the end of `q` and `R'` the file
after the moves of the jump (each parameter gets the value of its argument,
poison for `~`, every register outside `Ps` keeps its value), the facts
`aliasPars` gives hold on `R'`, when no fact at the end of `q` names a
parameter. -/
theorem ast_pars {g : AGen Map} {R R' : Nat → Option Noun} {q : Nat} {iq : AInfo} {Ps : List Nat}
    (hiq : g.info q = some iq) (hR : FactsOK R iq) (hnq : ∀ r i x, iq r = some i → ANames i x → x ∉ Ps)
    (hoff : ∀ x, x ∉ Ps → R' x = R x) :
    ∀ (ps : List Nat) (edges : List (Nat × List (Option Nat))) (loc loc0 : AInfo) (args : List (Option Nat)),
      aliasPars g ps edges loc = some loc0 → (q, args) ∈ edges → (∀ x ∈ ps, x ∈ Ps) →
      (∀ (k : Nat) (x : Nat), ps[k]? = some x → R' x = match args[k]? with | some (some u) => R u | _ => none) →
      (∀ r i v, loc r = some i → r ∉ ps → R' r = some v → InfoHolds R' i v) → FactsOK R' loc0
  | [], edges, loc, loc0, args, h, _, _, _, hl => by
    simp only [aliasPars, Option.some.injEq] at h
    subst h
    exact fun r i v hr hv => hl r i v hr List.not_mem_nil hv
  | x :: ps, edges, loc, loc0, args, h, he, hps, hk, hl => by
    simp only [aliasPars] at h
    obtain ⟨ins, hins, h⟩ := Option.bind_eq_some_iff.mp h
    refine ast_pars hiq hR hnq hoff ps _ _ loc0 args.tail h
      (List.mem_map.mpr ⟨(q, args), he, rfl⟩) (fun y hy => hps y (List.mem_cons_of_mem _ hy))
      (fun k y hy => by
        have := hk (k + 1) y (by simpa using hy)
        rw [this]; cases args <;> simp) (fun r i v hr hrn hv => ?_)
    by_cases erx : r = x
    · subst erx
      rw [as_upd_self] at hr; cases hr
      obtain ⟨y, hy, hyq⟩ := ast_mapM_mem hins he
      have hx := hk 0 r rfl
      cases args with
      | nil => simp [aliasIn] at hyq
      | cons a0 rest =>
        cases a0 with
        | none => simp at hx; rw [hx] at hv; cases hv
        | some u =>
          simp only [List.getElem?_cons_zero] at hx
          simp only [aliasIn, hiq, Option.bind_some] at hyq
          obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hyq
          rw [hx] at hv
          refine ast_frame_set (info_param hy (hR u a v ha hv)) fun z hz => hoff z fun hzP => ?_
          exact hnq u a z ha (ast_param_names hy hz) hzP
    · rw [as_upd_other _ _ erx] at hr
      exact hl r i v hr (fun hm => by
        rcases List.mem_cons.mp hm with e | hm
        · exact erx e
        · exact hrn hm) hv

end

end Opt
end SkaModel
end Formalization
