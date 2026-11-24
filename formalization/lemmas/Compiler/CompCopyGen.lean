import lemmas.Compiler.CompPruneLink

/-!
# `+copy-lazy` and `+copy` on lazy needs with forks and bonds

`+copy-lazy` (door axis `1022`, battery `clBat` of `CompCopyLink.lean`) runs
`+copy-need-make-ops` on the two sure needs and `+add-ops` of its moves into
block `o`, then builds the forks and the bonds of the result, each by the
same three branches:

    ?:  =(~ fork.second)  [fork.first gen]
    ?:  =(~ fork.first)  [fork.second gen]
    (merge: malt, spin with a recursive copy-lazy, silt, skip, weld)

and the same over the bonds, then `[[ned (~(uni in lok.first) lok.second)]
fork bond]`.  The model `copyLazyL` of `Ska/CompLazyArms.lean` takes the
same three branches in the same order, for the forks first and the bonds
second: no departure.

**What is linked here** (`comp_copy_lazy_nm`): the arm on every pair of lazy
needs, forks and bonds to any depth, on which neither list needs the merge:
the forks of one of the two needs are `~`, and the bonds of one of the two
are `~` (`NoMerge`).  Then the result's lists are those of the need that
has some, unchanged.  The merge branch (a fork or bond list on both sides)
is not linked here.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- Neither the forks nor the bonds of the two needs need the merge of
`+copy-lazy`: one of the two fork lists is `~`, and one of the two bond lists
is `~`. -/
def NoMerge (f s : Lazy CSet) : Prop := (f.fork = [] ∨ s.fork = []) ∧ (f.bond = [] ∨ s.bond = [])

variable {x} in
/-- **`+copy-lazy` on two lazy needs that need no merge** (`NoMerge`, forks
and bonds to any depth), under the side conditions of `comp_copy_need` on
the sure needs. -/
theorem comp_copy_lazy_nm (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF))
    (o : Nat) (f s : Lazy CSet) (hnm : NoMerge f s) (hlt : cnLt g.re f.sure.ned)
    (hrt : cnLt g.re s.sure.ned) (hm : cnMeet f.sure.ned s.sure.ned) :
    nock (C clBat (C (C (A o) (C f.toNoun s.toNoun)) (compCore g x ctx))) clBat
      = (Lazy.copyLazyL o f s g).map fun p => C p.1.toNoun (genNoun p.2 x) := by
  obtain ⟨sf, ff, bf⟩ := f
  obtain ⟨ss, fs, bs⟩ := s
  obtain ⟨hnf, hnb⟩ := hnm
  simp only [Lazy.sure_mk, Lazy.fork_mk, Lazy.bond_mk] at hlt hrt hm hnf hnb
  obtain ⟨n, ops, g1, e, _, _⟩ := cnm_seg (x := x) (B := cnmBat) (S := C (A 0) (A 0)) hl sf.ned ss.ned
    [] [] [] g hlt hrt hm
  have hcn := comp_copy_need (x := x) hl g sf.ned ss.ned hlt hrt hm
  rw [e] at hcn
  have hao := comp_add_ops x hc g1 o ops
  have huni := cs_uni_is sf.lok ss.lok
  have hD1 := comp_cnm_at
  have hD2 := comp_add_ops_at
  simp only [compCore] at hcn hao ⊢
  rw [lazy_toNoun_mk, lazy_toNoun_mk]
  unfold clBat
  generalize comp.door = Dr at hD1 hD2 hcn hao ⊢
  cases ea : addOps (Map := TreapMap mugF) o ops g1 with
  | none =>
    rw [ea] at hao
    simp [nock_exec, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao,
      Lazy.copyLazyL, e, ea, bind, StateT.bind]
  | some p =>
    obtain ⟨u, g2⟩ := p
    rw [ea] at hao
    have key : ∀ {α : Type} (E : α → Noun) (a b : List α), (a = [] ∨ b = []) →
        (b = [] ∧ listN (b.map E) = A 0 ∧ True ∧ True) ∨ (b ≠ [] ∧ a = [] ∧ eqCode (A 0) (listN (b.map E)) = A 1 ∧
          listN (a.map E) = A 0) := by
      intro α E a b h
      by_cases hb : b = []
      · left; subst hb; exact ⟨rfl, rfl, trivial, trivial⟩
      · right
        have ha : a = [] := h.resolve_right hb
        subst ha
        exact ⟨hb, rfl, wl_eq_nil _ (by simpa using hb), rfl⟩
    rcases key forkE ff fs hnf with ⟨hf0, hf1, hf2, hf3⟩ | ⟨hf0, hf1, hf2, hf3⟩ <;>
    rcases key bondE bf bs hnb with ⟨hb0, hb1, hb2, hb3⟩ | ⟨hb0, hb1, hb2, hb3⟩ <;>
    · simp [nock_exec, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao,
        Lazy.copyLazyL, e, ea, bind, StateT.bind, hc, in_arm, in.arm_at, in.uni.arm_at, cl_uni_arm, huni,
        pure, StateT.pure, lazy_toNoun_mk, hf0, hf1, hf2, hf3, hb0, hb1, hb2, hb3, List.isEmpty_iff]
      first
      | done
      | simp_all [eqCode, listN]

variable {x} in
/-- **`+copy` on lazy needs that need no merge**: `+emit` of `[~ ~ %hop
then.first]`, then `+copy-lazy` into the new block (`comp_copy_lazy_nm`). -/
theorem comp_copy_nm (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF))
    (first : NextL CSet) (second : Lazy CSet) (hnm : NoMerge first.laz second)
    (hlt : cnLt g.re first.laz.sure.ned) (hrt : cnLt g.re second.sure.ned)
    (hm : cnMeet first.laz.sure.ned second.sure.ned) :
    nock (C cpBat (C (C first.goal.toNoun second.toNoun) (compCore g x ctx))) cpBat
      = (copyL first second g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨laz, th⟩ := first
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Jmp.toNoun] at he
  have hre := cf_emitG_re ⟨[], [], Termin.hop th⟩ g
  have hcl := comp_copy_lazy_nm (x := x) hc hl (cfEmitG ⟨[], [], Termin.hop th⟩ g) g.bo laz second hnm
    (by rw [hre]; exact hlt) (by rw [hre]; exact hrt) hm
  have hD1 := comp_cp_at
  have hD2 := comp_emit_at
  have hD3 := comp_cl_at
  simp only [compCore] at hcl ⊢
  unfold cpBat
  generalize comp.door = Dr at hD1 hD2 hD3 he hcl ⊢
  cases ec : Lazy.copyLazyL (Map := TreapMap mugF) g.bo laz second (cfEmitG ⟨[], [], Termin.hop th⟩ g) with
  | none =>
    rw [ec] at hcl
    simp [nock_exec, NextL.goal, CGoalL.toNoun, hD2, hD3, comp_emit_arm, he, comp_cl_arm, hcl, copyL,
      cf_emit_g, ec, bind, StateT.bind, Jmp.toNoun]
  | some p =>
    obtain ⟨l2, g2⟩ := p
    rw [ec] at hcl
    simp [nock_exec, NextL.goal, CGoalL.toNoun, hD2, hD3, comp_emit_arm, he, comp_cl_arm, hcl, copyL,
      cf_emit_g, ec, bind, StateT.bind, pure, StateT.pure, Jmp.toNoun, jmp0, listNoun]

end Compiler
end Formalization
