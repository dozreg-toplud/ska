import lemmas.Glue.PokeOnR
import lemmas.Glue.RefSideH
import lemmas.Ska.CompRingContract

/-!
# The reference compiler on track K's ring model (track G, sixteenth pass; misfit 9 gone)

* **`refDHR S D sn`**: the whole-subject form is `finishLUCMR` (K's ring model, `env.ring` read
  from `call.cole`) of the table's nomm when it has no hint, `finishLUCH` of it under the
  table's `+sound` with the rings dropped when it has one (no hinted ring model exists: the real
  compiler's hinted code with ring callees is then the reference's up to rings, which
  `CompStateOnR` allows); the n-ary form is `finishLFCR` of `D.inl`.
* `(noRingD D)`: `D` with `env.noRing` at every bell.  `ref0 := refDH S (noRingD D) sn` is the
  no-ring reference of `gap15`, on which the class leaves already speak.
* **`refDHR_rel`**: at the `Tr` tables, `refDHR` and `ref0` are related by K's `RingRel`, from
  the two leaves `RingEraseU` / `RingEraseF` (owner K) at the table's nomms.
* `refN_refDHR`: their needs are the same (with the optimizer leaf `OptRing`, owner H).
* **`contractR_of`**: the contract of `refDHR`'s code from that of `ref0`'s (K's
  `execEntry_ringEq` through `bellContract_ringSameN`): every class leaf of `gap15` carries over
  unchanged at `(noRingD D)`.
* `compHypOnR_of`: `CompHypOnR` at `refDHR` from the state leaves up to rings, the contract
  leaves and class facts at `ref0`, the ring leaves.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon

variable {S : Type} [Comp.HoonSet S]

/-- **`D` with no ring in any environment.** -/
def noRingD (D : CompData FinMap (TreapMap mugF) Noun Noun) : CompData FinMap (TreapMap mugF) Noun Noun :=
  { D with env := fun long jets hot b m => (D.env long jets hot b m).noRing }

/-- **The reference compiler on the ring model** (with hints: the hinted nomms through
`finishLUCH` with the rings dropped). -/
noncomputable def refDHR (S : Type) [Comp.HoonSet S] (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (sn : LongB FinMap → SndT) : Ref FinMap (TreapMap mugF) Noun Noun := fun long jets hot b m =>
  if m then (realOf long.code b).bind fun nm =>
    if nm.noHint then Comp.finishLUCMR (S := S) (D.env long jets hot b true) nm
    else Comp.finishLUCH (S := S) (D.env long jets hot b true).noRing (sn long) nm
  else match b.less with
    | Sock.mk cape _ => (realOf long.code b).bind fun _ => (D.inl long jets hot b).bind fun nm =>
        Comp.finishLFCR (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape (D.bake long jets hot b)
    | _ => none

/-- **The ring leaves (owner K)**: the ring compiles erase to the no-ring ones, at the
reached tables' nomms. -/
structure RingLeaves (S : Type) [Comp.HoonSet S] (lib : Lib) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (Tr : LongB FinMap → Noun → Noun → Prop) : Prop where
  /-- K: `RingEraseU` at the table's hint-free nomms. -/
  eraseU : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → realOf long.code b = some nm →
    nm.noHint = true → Comp.RingEraseU (S := S) (Map := TreapMap mugF) (D.env long jets hot b true) nm
  /-- K: `RingEraseF` at `D.inl` of the table's bells. -/
  eraseF : ∀ long jets hot b nb nm cape data, InvB lib long → Tr long jets hot → realOf long.code b = some nb →
    D.inl long jets hot b = some nm → b.less = Sock.mk cape data →
    Comp.RingEraseF (S := S) (Map := TreapMap mugF) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
      (D.bake long jets hot b)

variable {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun} {sn : LongB FinMap → SndT}
  {Tr : LongB FinMap → Noun → Noun → Prop}

/-- **`refDHR` and the no-ring reference are related by `RingRel`** at the reached tables. -/
theorem refDHR_rel (hL : RingLeaves S lib D Tr) {long : LongB FinMap} {jets hot : Noun} (hI : InvB lib long)
    (hT : Tr long jets hot) (b : Bell) (m : Bool) :
    Comp.RingRel (refDHR S D sn long jets hot b m) (refDH S (noRingD D) sn long jets hot b m) := by
  cases m with
  | true =>
    simp only [refDHR, refDH, if_true]
    cases hnm : realOf long.code b with
    | none => first | trivial | simp [Comp.RingRel]
    | some nm =>
      simp only [Option.bind_some, noRingD]
      by_cases hh : nm.noHint = true
      · rw [if_pos hh, Comp.finishLUCH_eq _ _ hh]
        exact hL.eraseU long jets hot b nm hI hT hnm hh
      · rw [if_neg hh]
        exact Comp.ringRel_refl _
  | false =>
    simp only [refDHR, refDH, refD, Bool.false_eq_true, if_false]
    obtain ⟨less, fol⟩ := b
    cases less with
    | mk cape data =>
      simp only
      cases hnb : realOf long.code ⟨Sock.mk cape data, fol⟩ with
      | none => first | trivial | simp [Comp.RingRel]
      | some nb =>
        simp only [Option.bind_some, noRingD]
        cases hinl : D.inl long jets hot ⟨Sock.mk cape data, fol⟩ with
        | none => first | trivial | simp [Comp.RingRel]
        | some nm =>
          simp only [Option.bind_some]
          exact hL.eraseF long jets hot _ nb nm cape data hI hT hnb hinl rfl
    | _ => first | trivial | simp [Comp.RingRel]

/-- From `RingRel`, one side's straight gives the other's, `RingSameN`. -/
theorem ringRel_some {a b : Option (Straight (TreapMap mugF))} {s : Straight (TreapMap mugF)} (h : Comp.RingRel a b)
    (ha : a = some s) : ∃ s0, b = some s0 ∧ RingSameN s s0 := by
  subst ha
  cases b with
  | none => exact h.elim
  | some s0 => exact ⟨s0, rfl, h.2.2, h.1, h.2.1⟩

theorem ringRel_none {a b : Option (Straight (TreapMap mugF))} (h : Comp.RingRel a b) (ha : a = none) : b = none := by
  subst ha
  cases b with
  | none => rfl
  | some _ => exact h.elim

/-- **The needs of `refDHR` are those of the no-ring reference** (the optimizer keeps the need
up to rings). -/
theorem refN_refDHR {Ar : ArmsP} (hO : OptRing Ar) (hL : RingLeaves S lib D Tr) {long : LongB FinMap} {jets hot : Noun}
    (hI : InvB lib long) (hT : Tr long jets hot) :
    refN Ar (refDHR S D sn) long jets hot = refN Ar (refDH S (noRingD D) sn) long jets hot := by
  funext b m
  have h := refDHR_rel (sn := sn) hL hI hT b m
  unfold refN
  cases e : refDHR S D sn long jets hot b m with
  | none => rw [ringRel_none h e]
  | some s =>
    obtain ⟨s0, e0, hs⟩ := ringRel_some h e
    rw [e0]
    simp only [Option.map_some, Option.some.injEq]
    exact (hO s s0 hs).2.1

/-- **The contract of `refDHR`'s code from that of the no-ring reference's** (K's
`execEntry_ringEq`). -/
theorem contractR_of {Ar : ArmsP} (hO : OptRing Ar) (hL : RingLeaves S lib D Tr)
    (h0 : ∀ long jets hot b m s, InvB lib long → Tr long jets hot → refDH S (noRingD D) sn long jets hot b m = some s →
      BellContract lib (refN Ar (refDH S (noRingD D) sn) long jets hot) b m (Ar.optimize s) ∧
        (m = true → (Ar.optimize s).nargs = 1 ∧ (Ar.optimize s).need = NeedOrd.this)) :
    ∀ long jets hot b m s, InvB lib long → Tr long jets hot → refDHR S D sn long jets hot b m = some s →
      BellContract lib (refN Ar (refDHR S D sn) long jets hot) b m (Ar.optimize s) ∧
        (m = true → (Ar.optimize s).nargs = 1 ∧ (Ar.optimize s).need = NeedOrd.this) := by
  intro long jets hot b m s hI hT hr
  obtain ⟨s0, e0, hs⟩ := ringRel_some (refDHR_rel (sn := sn) hL hI hT b m) hr
  have ho := hO s s0 hs
  obtain ⟨hc, hn⟩ := h0 long jets hot b m s0 hI hT e0
  rw [refN_refDHR hO hL hI hT]
  refine ⟨bellContract_ringSameN ho hc, fun hm => ?_⟩
  obtain ⟨n1, n2⟩ := hn hm
  exact ⟨ho.2.2.trans n1, ho.2.1.trans n2⟩

/-- **`CompHypOnR` at `refDHR`** from the state leaves up to rings, the contract-side leaves
and class facts of the no-ring reference (`gap15`'s, at `(noRingD D)`), the ring leaves and the
optimizer leaf. -/
theorem compHypOnR_of {Ar : ArmsP} {FM : MonoClassH} {FN : NaryClass} {I : PSt → Prop} {Rd : PSt → Bell → Prop}
    (U : CompStateOnR Ar lib (refDHR S D sn) I Rd)
    (P : ContractLeavesOnH S Ar lib (refDH S (noRingD D) sn) (noRingD D) sn FM FN Tr) (K : ClassLeavesH S lib FM FN)
    (hO : OptRing Ar) (hL : RingLeaves S lib D Tr) (hRT : ∀ st b, Rd st b → Tr st.long st.jets st.hot) :
    CompHypOnR Ar lib (refDHR S D sn) I Rd :=
  { toCompStateOnR := U
    contract := fun st b m s hrd hI hr =>
      contractR_of hO hL (contractOnH_of P K) st.long st.jets st.hot b m s hI (hRT st b hrd) hr }

end Glue
end SkaModel
end Formalization
