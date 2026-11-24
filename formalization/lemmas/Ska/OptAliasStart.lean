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

end

end Opt
end SkaModel
end Formalization
