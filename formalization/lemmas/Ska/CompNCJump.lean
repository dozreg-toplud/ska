import lemmas.Ska.CompNCLeaf

/-!
# The jump facts of the cons and of `[7 p q]` on every `Annot`

README Gaps 12.22, the jump facts `JNew` and `EntNew` (the component `t`
of `NCOK`, `CompNC.lean`) of the cons and of `[7 p q]`.  They are facts of
the run, but the relations they come from (`consLC_runN`, `sevenC_parts`,
`sevenL_parts`) take the parts' `UOKC`, `LOKC` on some annotation, which the
induction gives through the parts' `Annot` inside the whole's.

* `entNew_consAny`: every cons whose parts meet the hypotheses of
  `uokc_consEA` meets `EntNew` (its code begins at the block of `+copy`),
  hinted or not.
* `isLeaf`, `annot_atomLeaf`, `annot_slot1Leaf`, `jNew_consLeaf`: in the
  forms of `[8 b c]` with an atom `b` the `p` part is a cons of two leaves,
  whose `EntNew` comes from `consLC_runN` on no subject at all.
* `jump_sevenNA`: `[7 p q]` with `q`'s result without entries (`NoEnt`),
  every form of `Annot`.
* `jump_sevenEA`: `[7 p q]` with `p` meeting `LOKC`, the forms `n7`,
  `inline`, `n9`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The cons -/

/-- **Every cons with the hypotheses of `uokc_consEA` meets `EntNew`** on
every `Annot` (`entNew_consLC`, whether it is hinted or not). -/
theorem entNew_consAny {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p d : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (ihb : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → hinted env.cod d = some true →
      BondOKC (S := S) (Map := Map) lib env P f p)
    (ihd : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f d →
      UOKC (S := S) (Map := Map) lib env P f d ∧ (hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d))
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.cons p d → EntNew (S := S) (Map := Map) env nm := by
  induction hA with
  | cons hA1 hA2 _ _ =>
    intro e
    cases e
    exact entNew_consLC lib env (ihp hA1) (ihb hA1) ⟨_, _, rfl⟩ (ihd hA2).1 (ihd hA2).2
  | memo hm _ ih' => intro e; exact ih' e
  | six0 hb' _ ih' => intro e; exact ih' e
  | six1 hb' _ ih' => intro e; exact ih' e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e
  | bareLit => intro e; cases e

/-! ## A cons of two leaves -/

/-- `[0 axe]` or `[1 k]`. -/
def isLeaf : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | _ => false

theorem annot_atomLeaf {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {k : Nat} {nm : Nomm}
    (h : Annot lib code P (A k) nm) : isLeaf nm = true := by
  generalize e : A k = f at h
  cases h <;> (try subst e) <;> simp_all [isBare, isLeaf]

theorem annot_slot1Leaf {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {nm : Nomm}
    (h : Annot lib code P (slot 1) nm) : isLeaf nm = true := by
  generalize e : slot 1 = f at h
  cases h <;> (try subst e) <;> simp_all [isBare, isLeaf]

theorem leaf_cases {nm : Nomm} (h : isLeaf nm = true) : (∃ a, nm = Nomm.n0 a) ∨ ∃ k, nm = Nomm.n1 k := by
  cases nm <;> simp_all [isLeaf]

/-- A leaf meets `UOKC` on no subject, for any formula. -/
theorem uokc_leafNone (lib : Lib) (env : CallEnv) {nm : Nomm} (h : isLeaf nm = true) (f : Noun) :
    UOKC (S := S) (Map := Map) lib env (fun _ => False) f nm := by
  have hx : FragX (S := S) nm := by
    rcases leaf_cases h with ⟨a, rfl⟩ | ⟨k, rfl⟩ <;> exact FragX.frag fun _ => trivial
  exact uokc_of_uok lib env (runU_uok lib (FragU.x hx)) (fun s hs => hs.elim)

theorem hinted_leaf (cod : Bell → Option Bool) {nm : Nomm} (h : isLeaf nm = true) : hinted cod nm = some false := by
  rcases leaf_cases h with ⟨a, rfl⟩ | ⟨k, rfl⟩ <;> rfl

theorem sixCount_leaf {nm : Nomm} (h : isLeaf nm = true) : sixCount nm = 0 := by
  rcases leaf_cases h with ⟨a, rfl⟩ | ⟨k, rfl⟩ <;> rfl

/-- **A cons of two leaves meets `EntNew`**: `consLC_runN` on no subject. -/
theorem entNew_consLeaf (lib : Lib) (env : CallEnv) {a b : Nomm} (ha : isLeaf a = true) (hb : isLeaf b = true) :
    EntNew (S := S) (Map := Map) env (Nomm.cons a b) := by
  intro sup sur th region g0 g1 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  exact (consLC_runN lib (uokc_leafNone (Map := Map) lib env ha (slot 1))
    (fun e => by rw [hinted_leaf env.cod hb] at e; cases e) ⟨_, _, rfl⟩ (uokc_leafNone lib env hb (slot 1))
    (fun e => by rw [hinted_leaf env.cod hb] at e; cases e) (by rw [sixCount_leaf ha, sixCount_leaf hb]; omega)
    hj hth hok hcl b0 d0 hu hcl0 hcb hkg h).2

/-! ## `[7 p q]` -/

/-- `+hinted` of `[7 p q]` from its parts'. -/
theorem hinted_noDirect_seven {cod : Bell → Option Bool} {p q : Nomm} (hp : hinted cod p = some (!p.pure))
    (hq : hinted cod q = some (!q.pure)) : hinted cod (Nomm.n7 p q) = some (!(Nomm.n7 p q).pure) := by
  simp only [hinted, Nomm.pure, hp, hq]
  cases p.pure <;> cases q.pure <;> rfl

/-- **The jump facts of `[7 p q]` when `q`'s result has no entries**, on
every `Annot`: `JNew` from both parts' (`jNew_sevenC`), `EntNew` from
`p`'s, or from `p`'s `JNew` and `q`'s `EntNew` (`entNew_sevenC`).  In the
forms of `[8 b c]` with an atom `b` the `p` part is a cons of two leaves
(`entNew_consLeaf`). -/
theorem jump_sevenNA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p q : Nomm}
    (hp : hinted env.cod p = some (!p.pure)) (hq : hinted env.cod q = some (!q.pure))
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p →
      JNew (S := S) (Map := Map) env p ∧ (hinted env.cod p = some true → EntNew (S := S) (Map := Map) env p))
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → UOKC (S := S) (Map := Map) lib env P f q ∧
      (p.pure = true → JNew (S := S) (Map := Map) env q ∧
        (hinted env.cod q = some true → EntNew (S := S) (Map := Map) env q)))
    (Nq : NoEnt (S := S) (Map := Map) env q)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n7 p q → JNew (S := S) (Map := Map) env nm ∧
      (hinted env.cod nm = some true → EntNew (S := S) (Map := Map) env nm) := by
  -- the facts from `p`'s jump facts and `q`'s relation
  have core : ∀ {Pq : Noun → Prop} {fc : Noun}, Annot lib code Pq fc q →
      (JNew (S := S) (Map := Map) env p ∧ (hinted env.cod p = some true → EntNew (S := S) (Map := Map) env p)) →
      JNew (S := S) (Map := Map) env (Nomm.n7 p q) ∧
        (hinted env.cod (Nomm.n7 p q) = some true → EntNew (S := S) (Map := Map) env (Nomm.n7 p q)) := by
    intro Pq fc hc ⟨Jp, Ep⟩
    obtain ⟨Uq, Xq⟩ := ihq hc
    have E : hinted env.cod (Nomm.n7 p q) = some true → EntNew (S := S) (Map := Map) env (Nomm.n7 p q) := by
      intro hh
      cases e : p.pure with
      | false => exact @entNew_sevenC S _ Map _ _ lib env p q _ _ Uq Nq (Or.inl (Ep (by rw [hp, e]; rfl)))
      | true =>
        have this : hinted env.cod q = some true := by
          simp only [hinted, hp, e, Bool.not_true] at hh
          exact hh
        exact @entNew_sevenC S _ Map _ _ lib env p q _ _ Uq Nq (Or.inr ⟨Jp, (Xq e).2 this⟩)
    refine ⟨?_, E⟩
    cases e7 : (Nomm.n7 p q).pure with
    | false => exact jNew_of_entNew (E (by rw [hinted_noDirect_seven hp hq, e7]; rfl))
    | true =>
      have ep : p.pure = true := by simp only [Nomm.pure, Bool.and_eq_true] at e7; exact e7.1
      exact @jNew_sevenC S _ Map _ _ lib env p q _ _ Uq Nq Jp (Xq ep).1
  induction hA with
  | n7 hb hc _ _ => intro e; cases e; exact core hc (ihp hb)
  | inline hb hc hg _ _ => intro e; cases e; exact core hg (ihp hb)
  | n9 hc hr _ _ => intro e; cases e; exact core hr (ihp hc)
  | @n8 P' b c p0 q0 hb hc _ _ =>
    intro e; cases e
    cases b with
    | atom k =>
      have E : EntNew (S := S) (Map := Map) env (Nomm.cons p0 (Nomm.n0 1)) :=
        @entNew_consLeaf S _ Map _ _ lib env p0 (Nomm.n0 1) (annot_atomLeaf hb) rfl
      exact core hc ⟨jNew_of_entNew E, fun _ => E⟩
    | cell a1 a2 => exact core hc (ihp (Annot.cons hb Annot.n0))
  | @n8g P' b c p0 r0 q0 hb hr hc _ _ _ =>
    intro e; cases e
    cases b with
    | atom k =>
      have E : EntNew (S := S) (Map := Map) env (Nomm.cons p0 r0) :=
        @entNew_consLeaf S _ Map _ _ lib env p0 r0 (annot_atomLeaf hb) (annot_slot1Leaf hr)
      exact core hc ⟨jNew_of_entNew E, fun _ => E⟩
    | cell a1 a2 => exact core hc (ihp (Annot.cons hb hr))
  | @n8l P' b c y d q0 hb hc _ => intro e; cases e; exact core hc (ihp (P := P') (Annot.n1 (k := C y d)))
  | memo hm _ ih' => intro e; exact ih' e
  | six0 hb' _ ih' => intro e; exact ih' e
  | six1 hb' _ ih' => intro e; exact ih' e
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | bareLit => intro e; cases e

/-- **The jump facts of `[7 p q]` with `p` meeting `LOKC`**, on the forms
`n7`, `inline`, `n9` (`hpc` excludes the others): `JNew` from `q`'s
(`jNew_sevenL`); `EntNew` from `q`'s when `q` is hinted (`entNew_sevenL`),
and from `p`'s when `q` is call-free without `%6` (`q`'s result without
entries, `entNew_sevenC`). -/
theorem jump_sevenEA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p q : Nomm}
    (hp : hinted env.cod p = some (!p.pure)) (hq : hinted env.cod q = some (!q.pure))
    (h6 : q.pure = true → noSix q = true)
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → LOKC (S := S) (Map := Map) lib env P f p ∧
      (hinted env.cod p = some true → EntNew (S := S) (Map := Map) env p))
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → UOKC (S := S) (Map := Map) lib env P f q ∧
      JNew (S := S) (Map := Map) env q ∧ (hinted env.cod q = some true → EntNew (S := S) (Map := Map) env q))
    (hpc : (∀ a b, p ≠ Nomm.cons a b) ∧ ∀ k, p ≠ Nomm.n1 k)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n7 p q → JNew (S := S) (Map := Map) env nm ∧
      (hinted env.cod nm = some true → EntNew (S := S) (Map := Map) env nm) := by
  have core : ∀ {Pp : Noun → Prop} {fb : Noun} {Pq : Noun → Prop} {fc : Noun}, Annot lib code Pp fb p →
      Annot lib code Pq fc q → JNew (S := S) (Map := Map) env (Nomm.n7 p q) ∧
        (hinted env.cod (Nomm.n7 p q) = some true → EntNew (S := S) (Map := Map) env (Nomm.n7 p q)) := by
    intro Pp fb Pq fc hb hc
    obtain ⟨Lp, Ep⟩ := ihp hb
    obtain ⟨Uq, Jq, Eqq⟩ := ihq hc
    refine ⟨jNew_sevenL Lp Uq Jq, fun hh => ?_⟩
    cases e : q.pure with
    | false => exact entNew_sevenL Lp Uq (Eqq (by rw [hq, e]; rfl))
    | true =>
      have hpp : hinted env.cod p = some true := by
        cases ep : p.pure with
        | false => rw [hp, ep]; rfl
        | true =>
          simp only [hinted, hp, hq, ep, e, Bool.not_true] at hh
          cases hh
      exact @entNew_sevenC S _ Map _ _ lib env p q _ _ Uq (noEnt_pure env e (h6 e)) (Or.inl (Ep hpp))
  induction hA with
  | n7 hb hc _ _ => intro e; cases e; exact core hb hc
  | inline hb hc hg _ _ => intro e; cases e; exact core hb hg
  | n9 hc hr _ _ => intro e; cases e; exact core hc hr
  | n8 => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8g => intro e; cases e; exact absurd rfl (hpc.1 _ _)
  | n8l => intro e; cases e; exact absurd rfl (hpc.2 _)
  | memo hm _ ih' => intro e; exact ih' e
  | six0 hb' _ ih' => intro e; exact ih' e
  | six1 hb' _ ih' => intro e; exact ih' e
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | bareLit => intro e; cases e

end Comp
end SkaModel
end Formalization
