import lemmas.Compiler.CompShapeCol
import lemmas.Ska.ShapeCol

/-!
# `+uni-need-ord` in full

`uno_gate`: the gate body of `+uni-need-ord` (arm `2794` of `K`, `unoBody`)
on `[[a b] K]` is `uniOrd a b` (`Ska/ShapeCol.lean`), for every `a` and `b`,
given `+cons-need` at axis `350` of `K` (`compK_cn`).  By induction on `a`:
the test `=(a b)` (`nord_eqCode`, `NeedOrd.toNoun` is injective), the
`%none` and `%this` cases, and the cell and `%both` cases, whose two
recursive calls `$(a .., b ..)` under `~+` are the induction hypothesis.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of a shape is injective. -/
theorem nord_inj : ∀ a b : NeedOrd, a.toNoun = b.toNoun → a = b
  | NeedOrd.pair p q, NeedOrd.pair p' q', h => by
    simp only [NeedOrd.toNoun, Noun.cell.injEq] at h
    rw [nord_inj p p' h.1, nord_inj q q' h.2]
  | NeedOrd.both p q, NeedOrd.both p' q', h => by
    simp only [NeedOrd.toNoun, Noun.cell.injEq, true_and] at h
    rw [nord_inj p p' h.1, nord_inj q q' h.2]
  | NeedOrd.this, NeedOrd.this, _ => rfl
  | NeedOrd.none, NeedOrd.none, _ => rfl
  | NeedOrd.pair p _, NeedOrd.both _ _, h => by
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [NeedOrd.toNoun, e] at h
  | NeedOrd.pair p _, NeedOrd.this, h => by
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [NeedOrd.toNoun, e] at h
  | NeedOrd.pair p _, NeedOrd.none, h => by
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [NeedOrd.toNoun, e] at h
  | NeedOrd.both _ _, NeedOrd.pair p _, h => by
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [NeedOrd.toNoun, e] at h
  | NeedOrd.this, NeedOrd.pair p _, h => by
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [NeedOrd.toNoun, e] at h
  | NeedOrd.none, NeedOrd.pair p _, h => by
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [NeedOrd.toNoun, e] at h
  | NeedOrd.both _ _, NeedOrd.this, h => by simp [NeedOrd.toNoun, Tag.both, Tag.this] at h
  | NeedOrd.both _ _, NeedOrd.none, h => by simp [NeedOrd.toNoun, Tag.both, Tag.none] at h
  | NeedOrd.this, NeedOrd.both _ _, h => by simp [NeedOrd.toNoun, Tag.both, Tag.this] at h
  | NeedOrd.none, NeedOrd.both _ _, h => by simp [NeedOrd.toNoun, Tag.both, Tag.none] at h
  | NeedOrd.this, NeedOrd.none, h => by simp [NeedOrd.toNoun, Tag.this, Tag.none] at h
  | NeedOrd.none, NeedOrd.this, h => by simp [NeedOrd.toNoun, Tag.this, Tag.none] at h

theorem nord_toNoun_eq (a b : NeedOrd) : a.toNoun = b.toNoun ↔ a = b :=
  ⟨nord_inj a b, fun h => h ▸ rfl⟩

theorem atom_eq_nord (n : Nat) (o : NeedOrd) : A n = o.toNoun ↔ False := by
  obtain ⟨u, v, e⟩ := nord_cell o
  rw [e]; simp

theorem nord_eq_atom (n : Nat) (o : NeedOrd) : o.toNoun = A n ↔ False := by
  obtain ⟨u, v, e⟩ := nord_cell o
  rw [e]; simp

/-- **`+uni-need-ord`** is `uniOrd`. -/
theorem uno_gate (KC : Noun) (hcn : slot? 350 KC = some cnArm) :
    ∀ a b : NeedOrd, nock (C unoBody (C (C a.toNoun b.toNoun) KC)) unoBody = some (uniOrd a b).toNoun := by
  have hc := fun x y => cn_gate_ord KC x y
  intro a
  induction a with
  | none => intro b; rw [uno_none, uniOrd_none_left]
  | this =>
    intro b
    by_cases e : NeedOrd.this = b
    · subst e; conv => { lhs; arg 2; unfold unoBody }
      simp [nock_exec, NeedOrd.toNoun, eqCode_self, uniOrd]
    rw [uniOrd.eq_def, if_neg e]
    conv => { lhs; arg 2; unfold unoBody unoRest }
    cases b <;> simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
      wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn]
  | both h t ih1 ih2 =>
    intro b
    by_cases e : NeedOrd.both h t = b
    · subst e; conv => { lhs; arg 2; unfold unoBody }
      simp [nock_exec, NeedOrd.toNoun, eqCode_self, uniOrd]
    rw [uniOrd.eq_def, if_neg e]
    conv => { lhs; arg 2; unfold unoBody unoRest }
    cases b with
    | pair p' q' =>
      by_cases e2 : h = p' <;>
      rcases consOrd_cases (uniOrd h p') (uniOrd t q') with ⟨e1, -, -⟩ | e1 <;>
      simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
    | both p' q' =>
      by_cases e2 : h = p' <;>
      rcases consOrd_cases (uniOrd h p') (uniOrd t q') with ⟨e1, -, -⟩ | e1 <;>
      simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
    | this => simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
    | none => simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
  | pair p q ih1 ih2 =>
    intro b
    by_cases e : NeedOrd.pair p q = b
    · subst e; conv => { lhs; arg 2; unfold unoBody }
      simp [nock_exec, NeedOrd.toNoun, eqCode_self, uniOrd]
    rw [uniOrd.eq_def, if_neg e]
    conv => { lhs; arg 2; unfold unoBody unoRest }
    cases b with
    | pair p' q' =>
      by_cases e2 : p = p' <;>
      rcases consOrd_cases (uniOrd p p') (uniOrd q q') with ⟨e1, -, -⟩ | e1 <;>
      simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
    | both p' q' =>
      by_cases e2 : p = p' <;>
      rcases consOrd_cases (uniOrd p p') (uniOrd q q') with ⟨e1, -, -⟩ | e1 <;>
      simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
    | this => simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]
    | none => simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
        wut_ord, atom_eq_nord, nord_eq_atom, nord_toNoun_eq, hcn, uniBoth, cnArm]

end Compiler
end Formalization
