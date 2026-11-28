import lemmas.Ska.SccLoopMsg

/-! # `+msg-need-ord-kept`: the join of the sweep loop only climbs (README Gaps 30)

Since 2a5b618 `member` (`+compile-scc-in`, line 3601) joins a member's new shape with its entry
by `+msg-need-ord-kept`, not `+msg-need-ord`:

```hoon
++  msg-need-ord-kept
  |=  [new=need-ordered old=need-ordered less=cape]
  ^-  need-ordered
  =*  kept  .
  ?:  =(new old)  new
  ?:  ?=(%this -.old)  old
  ?:  ?|  ?=(%none -.old)
          ?=(%none -.new)
          ?=(%this -.new)
      ==
    (msg-need-ord new old less)
  ~+
  ?:  ?=(%both -.new)
    ?:  ?=(%both -.old)
      [%both (kept h.new h.old (hed:ca less)) (kept t.new t.old (tel:ca less))]
    [%both (kept h.new p.old (hed:ca less)) (kept t.new q.old (tel:ca less))]
  ?:  ?=(%both -.old)
    [%both (kept p.new h.old (hed:ca less)) (kept q.new t.old (tel:ca less))]
  %-  cons-need
  [(kept p.new p.old (hed:ca less)) (kept q.new q.old (tel:ca less))]
```

`msgOrdKept` is the arm line for line (the `~+` is a memo hint, no model).  What is proved:

* `OrdLe`: the climb order, nothing below parts (`pair`) below the noun and its parts (`both`)
  below the noun (`this`), pointwise through cells.  `msgOrd` does not climb in it:
  `msgOrd_falls` (the entry `this` regrows to a `both`, the step T -> B of `msgOrd_cycle`).
* `kept_climbs`: on a canonical entry (`Canon`: no `[[%none ~] [%none ~]]` inside, which
  `+cons-need` never builds) the kept join is above the entry, for every new shape and cape;
  `kept_eq_or_lt`: it is the entry or strictly above it.  On a non-canonical entry the claim is
  false in any order with `none` at the bottom: `kept_noncanon` (the entry
  `[[%none ~] [%none ~]]` falls to `[%none ~]`).
* `kept_canon`: the kept join of a canonical entry is canonical.
* `pot`: a potential of shapes under a cape (`topC` for `none`, so that everything the cape
  bounds lies below it), and `kept_pot`: the kept join is the entry or has a strictly smaller
  potential.  So the entries of a member, from its first entry on, form a finite chain: the
  measure that `SccLoopKept.lean` uses for the loop.
* The old cycle climbs now: `kept_cycle_stops` (`kept(B, T) = T` for the T, B, G of
  `msgOrd_cycle`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

/-- **`+msg-need-ord-kept`** (2a5b618), line for line. -/
def msgOrdKept (new old : NeedOrd) (less : Cape) : NeedOrd :=
  if new = old then new else
  match new, old with
  | _, NeedOrd.this => NeedOrd.this
  | n, NeedOrd.none => msgOrd n NeedOrd.none less
  | NeedOrd.none, o => msgOrd NeedOrd.none o less
  | NeedOrd.this, o => msgOrd NeedOrd.this o less
  | NeedOrd.both h t, NeedOrd.both h' t' =>
    NeedOrd.both (msgOrdKept h h' (capeHed less)) (msgOrdKept t t' (capeTel less))
  | NeedOrd.both h t, NeedOrd.pair p q =>
    NeedOrd.both (msgOrdKept h p (capeHed less)) (msgOrdKept t q (capeTel less))
  | NeedOrd.pair p q, NeedOrd.both h t =>
    NeedOrd.both (msgOrdKept p h (capeHed less)) (msgOrdKept q t (capeTel less))
  | NeedOrd.pair p q, NeedOrd.pair p' q' =>
    consOrd (msgOrdKept p p' (capeHed less)) (msgOrdKept q q' (capeTel less))

/-! ## The order -/

/-- **The climb order**: `none` below everything, everything below `this`, and through cells
pointwise, a `pair` below a `both` of the same halves or above. -/
def OrdLe : NeedOrd → NeedOrd → Prop
  | NeedOrd.none, _ => True
  | _, NeedOrd.this => True
  | NeedOrd.pair p q, NeedOrd.pair p' q' => OrdLe p p' ∧ OrdLe q q'
  | NeedOrd.pair p q, NeedOrd.both h t => OrdLe p h ∧ OrdLe q t
  | NeedOrd.both h t, NeedOrd.both h' t' => OrdLe h h' ∧ OrdLe t t'
  | _, _ => False

/-- The strict climb. -/
def OrdLt (a b : NeedOrd) : Prop := OrdLe a b ∧ a ≠ b

/-- No `[[%none ~] [%none ~]]` inside: what `+cons-need` builds. -/
def Canon : NeedOrd → Prop
  | NeedOrd.pair p q => ¬ (p = NeedOrd.none ∧ q = NeedOrd.none) ∧ Canon p ∧ Canon q
  | NeedOrd.both h t => Canon h ∧ Canon t
  | _ => True

theorem ordLe_refl : ∀ a, OrdLe a a
  | NeedOrd.none => trivial
  | NeedOrd.this => trivial
  | NeedOrd.pair p q => ⟨ordLe_refl p, ordLe_refl q⟩
  | NeedOrd.both h t => ⟨ordLe_refl h, ordLe_refl t⟩

theorem ordLe_this (a : NeedOrd) : OrdLe a NeedOrd.this := by
  cases a <;> trivial

theorem ordLe_none {a : NeedOrd} (h : OrdLe a NeedOrd.none) : a = NeedOrd.none := by
  cases a <;> first | rfl | exact h.elim

theorem consOrd_pair {a b : NeedOrd} (h : ¬ (a = NeedOrd.none ∧ b = NeedOrd.none)) :
    consOrd a b = NeedOrd.pair a b := by
  simp only [consOrd, if_neg h]

theorem msgCap_or (r : NeedOrd) : msgCap r = NeedOrd.this ∨ msgCap r = r := by
  unfold msgCap; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **`msgOrd` does not climb**: the entry `this` with the new shape `[%both this this]` gives
`[%both this this]`, below `this`. -/
theorem msgOrd_falls :
    msgOrd (NeedOrd.both NeedOrd.this NeedOrd.this) NeedOrd.this cape22 =
      NeedOrd.both NeedOrd.this NeedOrd.this ∧
    ¬ OrdLe NeedOrd.this (NeedOrd.both NeedOrd.this NeedOrd.this) := by
  refine ⟨by decide, fun h => h⟩

/-! ## `msgNone` and `msgOne` climb -/

theorem msgNone_le : ∀ (x : NeedOrd) (c : Cape), Canon x → OrdLe x (msgNone x c)
  | NeedOrd.none, _, _ => trivial
  | NeedOrd.this, _, _ => trivial
  | NeedOrd.pair p q, Cape.cell a b, hx => by
    simp only [msgNone]
    rcases msgCap_or (consOrd (msgNone p a) (msgNone q b)) with h | h <;> rw [h]
    · exact ordLe_this _
    · have hp := msgNone_le p a hx.2.1
      have hq := msgNone_le q b hx.2.2
      have hn : ¬ (msgNone p a = NeedOrd.none ∧ msgNone q b = NeedOrd.none) := by
        rintro ⟨e1, e2⟩
        rw [e1] at hp; rw [e2] at hq
        exact hx.1 ⟨ordLe_none hp, ordLe_none hq⟩
      rw [consOrd_pair hn]; exact ⟨hp, hq⟩
  | NeedOrd.pair _ _, Cape.yes, _ => trivial
  | NeedOrd.pair _ _, Cape.no, _ => trivial
  | NeedOrd.both h t, Cape.cell a b, hx => by
    simp only [msgNone]
    rcases msgCap_or (NeedOrd.both (msgNone h a) (msgNone t b)) with e | e <;> rw [e]
    · exact ordLe_this _
    · exact ⟨msgNone_le h a hx.1, msgNone_le t b hx.2⟩
  | NeedOrd.both _ _, Cape.yes, _ => trivial
  | NeedOrd.both _ _, Cape.no, _ => trivial

theorem msgNone_eq_none : ∀ (x : NeedOrd) (c : Cape), Canon x →
    msgNone x c = NeedOrd.none → x = NeedOrd.none := by
  intro x c hx h
  have := msgNone_le x c hx
  rw [h] at this
  exact ordLe_none this

theorem msgOne_both (s h t : NeedOrd) (a b : Cape) :
    msgOne s (NeedOrd.both h t) (Cape.cell a b) = msgCap (NeedOrd.both (msgNone h a) (msgNone t b)) := by
  simp [msgOne, ordHed, ordTel]

theorem msgOne_pair_this (p q : NeedOrd) (a b : Cape) :
    msgOne NeedOrd.this (NeedOrd.pair p q) (Cape.cell a b) =
      msgCap (NeedOrd.both (msgNone p a) (msgNone q b)) := by
  simp [msgOne, ordHed, ordTel]

theorem msgOne_pair_none (p q : NeedOrd) (a b : Cape) :
    msgOne NeedOrd.none (NeedOrd.pair p q) (Cape.cell a b) =
      msgCap (consOrd (msgNone p a) (msgNone q b)) := by
  simp [msgOne, ordHed, ordTel]

theorem msgOne_le (s d : NeedOrd) (c : Cape) (hs : s = NeedOrd.this ∨ s = NeedOrd.none)
    (hd : Canon d) (hc : d ≠ NeedOrd.none ∧ d ≠ NeedOrd.this) : OrdLe d (msgOne s d c) := by
  cases c with
  | yes => exact ordLe_this _
  | no => exact ordLe_this _
  | cell a b =>
    cases d with
    | none => exact absurd rfl hc.1
    | this => exact absurd rfl hc.2
    | pair p q =>
      have hp := msgNone_le p a hd.2.1
      have hq := msgNone_le q b hd.2.2
      rcases hs with rfl | rfl
      · rw [msgOne_pair_this]
        rcases msgCap_or (NeedOrd.both (msgNone p a) (msgNone q b)) with e | e <;> rw [e]
        · exact ordLe_this _
        · exact ⟨hp, hq⟩
      · rw [msgOne_pair_none]
        rcases msgCap_or (consOrd (msgNone p a) (msgNone q b)) with e | e <;> rw [e]
        · exact ordLe_this _
        · have hn : ¬ (msgNone p a = NeedOrd.none ∧ msgNone q b = NeedOrd.none) := by
            rintro ⟨e1, e2⟩
            exact hd.1 ⟨msgNone_eq_none p a hd.2.1 e1, msgNone_eq_none q b hd.2.2 e2⟩
          rw [consOrd_pair hn]; exact ⟨hp, hq⟩
    | both h t =>
      rw [msgOne_both]
      rcases msgCap_or (NeedOrd.both (msgNone h a) (msgNone t b)) with e | e <;> rw [e]
      · exact ordLe_this _
      · exact ⟨msgNone_le h a hd.1, msgNone_le t b hd.2⟩

theorem msgOrd_none_r (d : NeedOrd) (less : Cape) (h1 : d ≠ NeedOrd.none) (h2 : d ≠ NeedOrd.this) :
    msgOrd d NeedOrd.none less = msgOne NeedOrd.none d less := by
  cases d with
  | none => exact absurd rfl h1
  | this => exact absurd rfl h2
  | pair p q => simp [msgOrd]
  | both h t => simp [msgOrd]

theorem msgOrd_none_l (d : NeedOrd) (less : Cape) (h1 : d ≠ NeedOrd.none) (h2 : d ≠ NeedOrd.this) :
    msgOrd NeedOrd.none d less = msgOne NeedOrd.none d less := by
  cases d with
  | none => exact absurd rfl h1
  | this => exact absurd rfl h2
  | pair p q => simp [msgOrd]
  | both h t => simp [msgOrd]

theorem msgOrd_this_l (d : NeedOrd) (less : Cape) (h1 : d ≠ NeedOrd.none) (h2 : d ≠ NeedOrd.this) :
    msgOrd NeedOrd.this d less = msgOne NeedOrd.this d less := by
  cases d with
  | none => exact absurd rfl h1
  | this => exact absurd rfl h2
  | pair p q => simp [msgOrd]
  | both h t => simp [msgOrd]

/-! ## The kept join climbs -/

/-- **The kept join is above a canonical entry**, for every new shape and cape. -/
theorem kept_climbs : ∀ (new old : NeedOrd) (less : Cape), Canon old →
    OrdLe old (msgOrdKept new old less) := by
  intro new
  induction new with
  | none =>
    intro old less ho
    unfold msgOrdKept
    split
    · rename_i e; subst e; exact ordLe_refl _
    · rename_i hne
      cases old with
      | none => exact absurd rfl hne
      | this => exact trivial
      | pair p q => dsimp only; rw [msgOrd_none_l _ _ (by simp) (by simp)]; exact msgOne_le _ _ _ (Or.inr rfl) ho ⟨by simp, by simp⟩
      | both h t => dsimp only; rw [msgOrd_none_l _ _ (by simp) (by simp)]; exact msgOne_le _ _ _ (Or.inr rfl) ho ⟨by simp, by simp⟩
  | this =>
    intro old less ho
    unfold msgOrdKept
    split
    · rename_i e; subst e; exact ordLe_refl _
    · rename_i hne
      cases old with
      | none => trivial
      | this => exact trivial
      | pair p q => dsimp only; rw [msgOrd_this_l _ _ (by simp) (by simp)]; exact msgOne_le _ _ _ (Or.inl rfl) ho ⟨by simp, by simp⟩
      | both h t => dsimp only; rw [msgOrd_this_l _ _ (by simp) (by simp)]; exact msgOne_le _ _ _ (Or.inl rfl) ho ⟨by simp, by simp⟩
  | pair p q ihp ihq =>
    intro old less ho
    unfold msgOrdKept
    split
    · rename_i e; subst e; exact ordLe_refl _
    · rename_i hne
      cases old with
      | none => trivial
      | this => exact trivial
      | pair p' q' =>
        simp only
        have h1 := ihp p' (capeHed less) ho.2.1
        have h2 := ihq q' (capeTel less) ho.2.2
        have hn : ¬ (msgOrdKept p p' (capeHed less) = NeedOrd.none ∧
            msgOrdKept q q' (capeTel less) = NeedOrd.none) := by
          rintro ⟨e1, e2⟩
          rw [e1] at h1; rw [e2] at h2
          exact ho.1 ⟨ordLe_none h1, ordLe_none h2⟩
        rw [consOrd_pair hn]; exact ⟨h1, h2⟩
      | both h t => exact ⟨ihp h _ ho.1, ihq t _ ho.2⟩
  | both h t ihh iht =>
    intro old less ho
    unfold msgOrdKept
    split
    · rename_i e; subst e; exact ordLe_refl _
    · rename_i hne
      cases old with
      | none => trivial
      | this => exact trivial
      | pair p q => exact ⟨ihh p _ ho.2.1, iht q _ ho.2.2⟩
      | both h' t' => exact ⟨ihh h' _ ho.1, iht t' _ ho.2⟩

/-- **The kept join is the entry or strictly above it.** -/
theorem kept_eq_or_lt (new old : NeedOrd) (less : Cape) (ho : Canon old) :
    msgOrdKept new old less = old ∨ OrdLt old (msgOrdKept new old less) := by
  by_cases e : msgOrdKept new old less = old
  · exact Or.inl e
  · exact Or.inr ⟨kept_climbs new old less ho, fun h => e h.symm⟩

theorem kept_eq_none {new old : NeedOrd} {less : Cape} (ho : Canon old)
    (h : msgOrdKept new old less = NeedOrd.none) : old = NeedOrd.none := by
  have := kept_climbs new old less ho
  rw [h] at this; exact ordLe_none this

/-- **Not for every shape**: the non-canonical entry `[[%none ~] [%none ~]]` falls to
`[%none ~]`, below it in any order with `none` at the bottom. -/
theorem kept_noncanon :
    msgOrdKept NeedOrd.none (NeedOrd.pair NeedOrd.none NeedOrd.none) cape22 = NeedOrd.none := by
  decide

/-- The steps of the old cycle `T -> B -> G -> T` (`msgOrd_cycle`): the kept join of the
entry `T = this` is `this`, whatever comes. -/
theorem kept_this (new : NeedOrd) (less : Cape) :
    msgOrdKept new NeedOrd.this less = NeedOrd.this := by
  unfold msgOrdKept; split
  · rename_i e; exact e
  · cases new <;> rfl

/-! ## Canonical shapes stay canonical -/

theorem canon_consOrd {a b : NeedOrd} (ha : Canon a) (hb : Canon b) : Canon (consOrd a b) := by
  unfold consOrd; split
  · trivial
  · rename_i h; exact ⟨h, ha, hb⟩

theorem canon_msgCap {r : NeedOrd} (h : Canon r) : Canon (msgCap r) := by
  rcases msgCap_or r with e | e <;> rw [e]
  · trivial
  · exact h

theorem msgNone_canon : ∀ (x : NeedOrd) (c : Cape), Canon (msgNone x c)
  | NeedOrd.none, _ => trivial
  | NeedOrd.this, _ => trivial
  | NeedOrd.pair p q, Cape.cell a b =>
    canon_msgCap (canon_consOrd (msgNone_canon p a) (msgNone_canon q b))
  | NeedOrd.pair _ _, Cape.yes => trivial
  | NeedOrd.pair _ _, Cape.no => trivial
  | NeedOrd.both h t, Cape.cell a b =>
    canon_msgCap (show Canon (NeedOrd.both _ _) from ⟨msgNone_canon h a, msgNone_canon t b⟩)
  | NeedOrd.both _ _, Cape.yes => trivial
  | NeedOrd.both _ _, Cape.no => trivial

theorem msgOne_canon (s d : NeedOrd) (c : Cape) : Canon (msgOne s d c) := by
  cases c with
  | yes => trivial
  | no => trivial
  | cell a b =>
    simp only [msgOne]
    apply canon_msgCap
    repeat' split
    all_goals first
      | exact ⟨msgNone_canon _ _, msgNone_canon _ _⟩
      | exact canon_consOrd (msgNone_canon _ _) (msgNone_canon _ _)

/-- **The kept join of a canonical entry is canonical.** -/
theorem kept_canon : ∀ (new old : NeedOrd) (less : Cape), Canon old →
    Canon (msgOrdKept new old less) := by
  intro new
  induction new with
  | none =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; subst e; exact ho
    · cases old with
      | none => trivial
      | this => trivial
      | pair p q => dsimp only; rw [msgOrd_none_l _ _ (by simp) (by simp)]; exact msgOne_canon _ _ _
      | both h t => dsimp only; rw [msgOrd_none_l _ _ (by simp) (by simp)]; exact msgOne_canon _ _ _
  | this =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; subst e; exact ho
    · cases old with
      | none => dsimp only; simp [msgOrd, Canon]
      | this => trivial
      | pair p q => dsimp only; rw [msgOrd_this_l _ _ (by simp) (by simp)]; exact msgOne_canon _ _ _
      | both h t => dsimp only; rw [msgOrd_this_l _ _ (by simp) (by simp)]; exact msgOne_canon _ _ _
  | pair p q ihp ihq =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; subst e; exact ho
    · cases old with
      | none => dsimp only; rw [msgOrd_none_r _ _ (by simp) (by simp)]; exact msgOne_canon _ _ _
      | this => trivial
      | pair p' q' => exact canon_consOrd (ihp p' _ ho.2.1) (ihq q' _ ho.2.2)
      | both h t => exact ⟨ihp h _ ho.1, ihq t _ ho.2⟩
  | both h t ihh iht =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; subst e; exact ho
    · cases old with
      | none => dsimp only; rw [msgOrd_none_r _ _ (by simp) (by simp)]; exact msgOne_canon _ _ _
      | this => trivial
      | pair p q => exact ⟨ihh p _ ho.2.1, iht q _ ho.2.2⟩
      | both h' t' => exact ⟨ihh h' _ ho.1, iht t' _ ho.2⟩

/-! ## The potential -/

/-- The potential of `[%none ~]` under a cape: above every shape the cape bounds. -/
def topC : Cape → Nat
  | Cape.cell a b => 3 + topC a + topC b
  | _ => 1

/-- **The potential of a shape under a cape**: `0` for the noun, `topC` for nothing, and
through cells `2` for a split, `1` for the noun and its parts. -/
def pot (c : Cape) : NeedOrd → Nat
  | NeedOrd.this => 0
  | NeedOrd.none => topC c
  | NeedOrd.pair p q => 2 + pot (capeHed c) p + pot (capeTel c) q
  | NeedOrd.both h t => 1 + pot (capeHed c) h + pot (capeTel c) t

theorem topC_pos (c : Cape) : 1 ≤ topC c := by
  cases c <;> simp [topC] <;> omega

theorem pot_le_top {c : Cape} {y : NeedOrd} (h : y = NeedOrd.none ∨ pot c y < topC c) :
    pot c y ≤ topC c := by
  rcases h with e | e
  · subst e; simp [pot]
  · omega

theorem msgNone_top : ∀ (x : NeedOrd) (c : Cape),
    msgNone x c = NeedOrd.none ∨ pot c (msgNone x c) < topC c
  | NeedOrd.none, _ => Or.inl rfl
  | NeedOrd.this, c => Or.inr (by simp [msgNone, pot]; exact topC_pos c)
  | NeedOrd.pair p q, Cape.cell a b => by
    simp only [msgNone]
    have h1 := pot_le_top (msgNone_top p a)
    have h2 := pot_le_top (msgNone_top q b)
    rcases msgCap_or (consOrd (msgNone p a) (msgNone q b)) with e | e <;> rw [e]
    · right; simp only [pot, topC]; omega
    · unfold consOrd; split
      · left; rfl
      · right; simp only [pot, capeHed, capeTel, topC]; omega
  | NeedOrd.pair _ _, Cape.yes => Or.inr (by simp [msgNone, pot, topC])
  | NeedOrd.pair _ _, Cape.no => Or.inr (by simp [msgNone, pot, topC])
  | NeedOrd.both h t, Cape.cell a b => by
    simp only [msgNone]
    have h1 := pot_le_top (msgNone_top h a)
    have h2 := pot_le_top (msgNone_top t b)
    rcases msgCap_or (NeedOrd.both (msgNone h a) (msgNone t b)) with e | e <;> rw [e]
    · right; simp only [pot, topC]; omega
    · right; simp only [pot, capeHed, capeTel, topC]; omega
  | NeedOrd.both _ _, Cape.yes => Or.inr (by simp [msgNone, pot, topC])
  | NeedOrd.both _ _, Cape.no => Or.inr (by simp [msgNone, pot, topC])

theorem msgOne_top (s d : NeedOrd) (c : Cape) :
    msgOne s d c = NeedOrd.none ∨ pot c (msgOne s d c) < topC c := by
  cases c with
  | yes => right; simp [msgOne, pot, topC]
  | no => right; simp [msgOne, pot, topC]
  | cell a b =>
    have h1 := pot_le_top (msgNone_top (ordHed d) a)
    have h2 := pot_le_top (msgNone_top (ordTel d) b)
    have k1 : ∀ x, msgCap x = NeedOrd.this → pot (Cape.cell a b) (msgCap x) < topC (Cape.cell a b) := by
      intro x e; rw [e]; simp only [pot, topC]; omega
    simp only [msgOne]
    generalize msgNone (ordHed d) a = l at h1 ⊢
    generalize msgNone (ordTel d) b = r at h2 ⊢
    repeat' split
    all_goals first
      | (rcases msgCap_or (NeedOrd.both l r) with e | e
         · exact Or.inr (k1 _ e)
         · rw [e]; right; simp only [pot, capeHed, capeTel, topC]; omega)
      | (rcases msgCap_or (consOrd l r) with e | e
         · exact Or.inr (k1 _ e)
         · rw [e]; unfold consOrd; split
           · left; rfl
           · right; simp only [pot, capeHed, capeTel, topC]; omega)

theorem pot_cell_pos (c : Cape) (x : NeedOrd) (h1 : x ≠ NeedOrd.none) (h2 : x ≠ NeedOrd.this) :
    1 ≤ pot c x := by
  cases x with
  | none => exact absurd rfl h1
  | this => exact absurd rfl h2
  | pair p q => simp only [pot]; omega
  | both h t => simp only [pot]; omega

theorem msgNone_pot : ∀ (x : NeedOrd) (c : Cape), Canon x →
    msgNone x c = x ∨ pot c (msgNone x c) < pot c x
  | NeedOrd.none, _, _ => Or.inl rfl
  | NeedOrd.this, _, _ => Or.inl rfl
  | NeedOrd.pair p q, Cape.cell a b, hx => by
    simp only [msgNone]
    have i1 := msgNone_pot p a hx.2.1
    have i2 := msgNone_pot q b hx.2.2
    rcases msgCap_or (consOrd (msgNone p a) (msgNone q b)) with e | e <;> rw [e]
    · right; simp only [pot]; omega
    · have hn : ¬ (msgNone p a = NeedOrd.none ∧ msgNone q b = NeedOrd.none) := by
        rintro ⟨e1, e2⟩
        exact hx.1 ⟨msgNone_eq_none p a hx.2.1 e1, msgNone_eq_none q b hx.2.2 e2⟩
      rw [consOrd_pair hn]
      rcases i1 with e1 | l1 <;> rcases i2 with e2 | l2
      · left; rw [e1, e2]
      all_goals (right; simp only [pot, capeHed, capeTel]; first | (rw [e1]; omega) | (rw [e2]; omega) | omega)
  | NeedOrd.pair _ _, Cape.yes, _ => Or.inr (by simp [msgNone, pot]; omega)
  | NeedOrd.pair _ _, Cape.no, _ => Or.inr (by simp [msgNone, pot]; omega)
  | NeedOrd.both h t, Cape.cell a b, hx => by
    simp only [msgNone]
    have i1 := msgNone_pot h a hx.1
    have i2 := msgNone_pot t b hx.2
    rcases msgCap_or (NeedOrd.both (msgNone h a) (msgNone t b)) with e | e <;> rw [e]
    · right; simp only [pot]; omega
    · rcases i1 with e1 | l1 <;> rcases i2 with e2 | l2
      · left; rw [e1, e2]
      all_goals (right; simp only [pot, capeHed, capeTel]; first | (rw [e1]; omega) | (rw [e2]; omega) | omega)
  | NeedOrd.both _ _, Cape.yes, _ => Or.inr (by simp [msgNone, pot]; omega)
  | NeedOrd.both _ _, Cape.no, _ => Or.inr (by simp [msgNone, pot]; omega)

theorem pot_le_of {c : Cape} {x y : NeedOrd} (h : y = x ∨ pot c y < pot c x) : pot c y ≤ pot c x := by
  rcases h with e | e
  · rw [e]; exact Nat.le_refl _
  · omega

theorem msgOne_pot (s d : NeedOrd) (c : Cape) (hs : s = NeedOrd.this ∨ s = NeedOrd.none)
    (hd : Canon d) (hc : d ≠ NeedOrd.none ∧ d ≠ NeedOrd.this) :
    msgOne s d c = d ∨ pot c (msgOne s d c) < pot c d := by
  have hp := pot_cell_pos c d hc.1 hc.2
  cases c with
  | yes => right; simp only [msgOne, pot]; omega
  | no => right; simp only [msgOne, pot]; omega
  | cell a b =>
    cases d with
    | none => exact absurd rfl hc.1
    | this => exact absurd rfl hc.2
    | pair p q =>
      have i1 := msgNone_pot p a hd.2.1
      have i2 := msgNone_pot q b hd.2.2
      have l1 := pot_le_of i1
      have l2 := pot_le_of i2
      rcases hs with rfl | rfl
      · rw [msgOne_pair_this]
        rcases msgCap_or (NeedOrd.both (msgNone p a) (msgNone q b)) with e | e <;> rw [e]
        · right; simp only [pot]; omega
        · right; simp only [pot, capeHed, capeTel]; omega
      · rw [msgOne_pair_none]
        rcases msgCap_or (consOrd (msgNone p a) (msgNone q b)) with e | e <;> rw [e]
        · right; simp only [pot]; omega
        · have hn : ¬ (msgNone p a = NeedOrd.none ∧ msgNone q b = NeedOrd.none) := by
            rintro ⟨e1, e2⟩
            exact hd.1 ⟨msgNone_eq_none p a hd.2.1 e1, msgNone_eq_none q b hd.2.2 e2⟩
          rw [consOrd_pair hn]
          rcases i1 with e1 | k1 <;> rcases i2 with e2 | k2
          · left; rw [e1, e2]
          all_goals (right; simp only [pot, capeHed, capeTel]; omega)
    | both h t =>
      have i1 := msgNone_pot h a hd.1
      have i2 := msgNone_pot t b hd.2
      have l1 := pot_le_of i1
      have l2 := pot_le_of i2
      rw [msgOne_both]
      rcases msgCap_or (NeedOrd.both (msgNone h a) (msgNone t b)) with e | e <;> rw [e]
      · right; simp only [pot]; omega
      · rcases i1 with e1 | k1 <;> rcases i2 with e2 | k2
        · left; rw [e1, e2]
        all_goals (right; simp only [pot, capeHed, capeTel]; omega)

/-- **The potential falls at every change of the kept join** of a canonical entry. -/
theorem kept_pot : ∀ (new old : NeedOrd) (less : Cape), Canon old →
    msgOrdKept new old less = old ∨ pot less (msgOrdKept new old less) < pot less old := by
  intro new
  induction new with
  | none =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; exact Or.inl e
    · cases old with
      | none => exact Or.inl rfl
      | this => exact Or.inl rfl
      | pair p q => dsimp only; rw [msgOrd_none_l _ _ (by simp) (by simp)]; exact msgOne_pot _ _ _ (Or.inr rfl) ho ⟨by simp, by simp⟩
      | both h t => dsimp only; rw [msgOrd_none_l _ _ (by simp) (by simp)]; exact msgOne_pot _ _ _ (Or.inr rfl) ho ⟨by simp, by simp⟩
  | this =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; exact Or.inl e
    · cases old with
      | none => right; dsimp only; simp [msgOrd, pot]; exact topC_pos less
      | this => exact Or.inl rfl
      | pair p q => dsimp only; rw [msgOrd_this_l _ _ (by simp) (by simp)]; exact msgOne_pot _ _ _ (Or.inl rfl) ho ⟨by simp, by simp⟩
      | both h t => dsimp only; rw [msgOrd_this_l _ _ (by simp) (by simp)]; exact msgOne_pot _ _ _ (Or.inl rfl) ho ⟨by simp, by simp⟩
  | pair p q ihp ihq =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; exact Or.inl e
    · cases old with
      | none =>
        dsimp only; rw [msgOrd_none_r _ _ (by simp) (by simp)]
        rcases msgOne_top NeedOrd.none (NeedOrd.pair p q) less with e | e
        · exact Or.inl e
        · right; simpa [pot] using e
      | this => exact Or.inl rfl
      | pair p' q' =>
        simp only
        have i1 := ihp p' (capeHed less) ho.2.1
        have i2 := ihq q' (capeTel less) ho.2.2
        have l1 := pot_le_of i1
        have l2 := pot_le_of i2
        have hn : ¬ (msgOrdKept p p' (capeHed less) = NeedOrd.none ∧
            msgOrdKept q q' (capeTel less) = NeedOrd.none) := by
          rintro ⟨e1, e2⟩
          exact ho.1 ⟨kept_eq_none ho.2.1 e1, kept_eq_none ho.2.2 e2⟩
        rw [consOrd_pair hn]
        rcases i1 with e1 | k1 <;> rcases i2 with e2 | k2
        · left; rw [e1, e2]
        all_goals (right; simp only [pot]; omega)
      | both h t =>
        dsimp only
        have i1 := ihp h (capeHed less) ho.1
        have i2 := ihq t (capeTel less) ho.2
        have l1 := pot_le_of i1
        have l2 := pot_le_of i2
        rcases i1 with e1 | k1 <;> rcases i2 with e2 | k2
        · left; rw [e1, e2]
        all_goals (right; simp only [pot]; omega)
  | both h t ihh iht =>
    intro old less ho
    unfold msgOrdKept; split
    · rename_i e; exact Or.inl e
    · cases old with
      | none =>
        dsimp only; rw [msgOrd_none_r _ _ (by simp) (by simp)]
        rcases msgOne_top NeedOrd.none (NeedOrd.both h t) less with e | e
        · exact Or.inl e
        · right; simpa [pot] using e
      | this => exact Or.inl rfl
      | pair p q =>
        dsimp only
        have l1 := pot_le_of (ihh p (capeHed less) ho.2.1)
        have l2 := pot_le_of (iht q (capeTel less) ho.2.2)
        right; simp only [pot]; omega
      | both h' t' =>
        dsimp only
        have i1 := ihh h' (capeHed less) ho.1
        have i2 := iht t' (capeTel less) ho.2
        have l1 := pot_le_of i1
        have l2 := pot_le_of i2
        rcases i1 with e1 | k1 <;> rcases i2 with e2 | k2
        · left; rw [e1, e2]
        all_goals (right; simp only [pot]; omega)

/-- **The old cycle climbs** (`msgOrd_cycle` gave `bTT`, `bBig`, `this`): from `this` the
need `bTT` keeps `this`; from `bTT` the need `bBig` keeps `bTT`; from `bBig` the need `this`
gives `this`, above it. -/
theorem kept_cycle_stops :
    msgOrdKept bTT NeedOrd.this cape22 = NeedOrd.this ∧
    msgOrdKept bBig bTT cape22 = bTT ∧
    msgOrdKept NeedOrd.this bBig cape22 = NeedOrd.this := by decide

end Comp
end SkaModel
end Formalization
