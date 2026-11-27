import lemmas.Compiler.CompRunShapeFrom
import lemmas.Compiler.CompRunShapeNoneCut
import lemmas.Compiler.CompClaGen

/-!
# The link of `+laze-none-equivalent` (track A, 2026-11-27)

`+laze-none-equivalent` (door arm `0x15575`, cut in `CompRunShapeNoneCut.lean`) against
`noneEq` of `Ska/RunShape.lean`, on every `laze` (forks and bonds to any depth) and every noun
`G` of `gen` (it reads none): **`lne_all`**, the proof of `ne_all` (`CompClaGen.lean`, the same
Hoon on a `need-lazy`) on the nouns of `Laze`, with `+levy` of layer 2 found through
`CompIn ctx`.  No departure.  **`lne_door`**: the arm on the door gives the gate.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem noneEqF_all : ∀ f : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    noneEqF f = f.all fun e => noneEq e.1.2 && noneEq e.2.2
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by simp [noneEqF, noneEqF_all rest]

theorem noneEqB_all : ∀ b : List (Nat × Laze CSet), noneEqB b = b.all fun e => noneEq e.2
  | [] => rfl
  | (o, l) :: rest => by simp [noneEqB, noneEqB_all rest]

section
variable (hc : CompIn ctx) (G : Noun)
include hc

mutual
/-- **`+none-equivalent` on every lazy need** (forks and bonds to any
depth). -/
theorem lne_all : ∀ laz : Laze CSet,
    nock (C lneGate (C laz.toNoun (C comp.door (C G ctx)))) lneGate = some (loob (noneEq laz))
  | Laze.mk ⟨ned, lok⟩ fk bd => by
    have hL := hc
    have hLF := levy_gate_map lzfE layer2 lneGF (C (C (A 0) lneBunt) (C (A 0) lneBunt))
      (C lneGate (C (C (SureO.toNoun ⟨ned, lok⟩) (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C G ctx))))
      (fun e => noneEq e.1.2 && noneEq e.2.2) fk
      (fun e he => lne_forks fk e he _)
    have hLB := levy_gate_map lzbE layer2 lneGB (C (A 0) lneBunt)
      (C lneGate (C (C (SureO.toNoun ⟨ned, lok⟩) (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C G ctx))))
      (fun e => noneEq e.2) bd
      (fun e he => lne_bonds bd e he _)
    rw [lz_toNoun_mk]
    simp only [noneEq, ← noneEqF_all, ← noneEqB_all] at hLF hLB ⊢
    have other : ∀ (ned : NeedOrd), ned ≠ NeedOrd.none → ∀ (L : Noun),
        nock (C lneGate (C (C (C ned.toNoun L) (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))
          (C comp.door (C G ctx)))) lneGate = some (A 1) := by
      intro ned hn L
      conv => { lhs; arg 2; unfold lneGate }
      cases ned with
      | none => exact absurd rfl hn
      | pair p q =>
        obtain ⟨a, b, hp⟩ := no_cell p
        simp [nock_exec, NeedOrd.toNoun, hp, eqCode]
      | this => simp [nock_exec, NeedOrd.toNoun, eqCode_atom, Tag.this]
      | both h t => simp [nock_exec, NeedOrd.toNoun, eqCode_atom, Tag.both]
    by_cases hn : ned = NeedOrd.none
    · subst hn
      conv => { lhs; arg 2; unfold lneGate }
      simp only [SureO.toNoun, NeedOrd.toNoun, Tag.none] at hLF hLB
      simp only [SureO.toNoun]
      rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
      · rw [hl] at hLF hLB ⊢
        cases hb1 : noneEqF fk <;> cases hb2 : noneEqB bd <;>
          simp [nock_exec, NeedOrd.toNoun, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, Tag.none, loob, hb1, hb2]
      · rw [hl] at hLF hLB ⊢
        cases hb1 : noneEqF fk <;> cases hb2 : noneEqB bd <;>
          simp [nock_exec, NeedOrd.toNoun, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, Tag.none, loob, hb1, hb2]
      · rw [hl]
        rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, NeedOrd.toNoun, hsm, loob, eqCode_atom, Tag.none, Ne.symm hr0]
                · simp [nock_exec, NeedOrd.toNoun, hsm, loob, eqCode_atom, eqCode, Tag.none]
              · simp [nock_exec, NeedOrd.toNoun, hsm, loob, eqCode_atom, Tag.none, Ne.symm hl0]
            · simp [nock_exec, NeedOrd.toNoun, hsm, loob, eqCode_atom, eqCode, Tag.none]
          · simp [nock_exec, NeedOrd.toNoun, hsm, loob, eqCode_atom, Tag.none, Ne.symm hk]
        · simp [nock_exec, NeedOrd.toNoun, hsm, loob, eqCode_atom, eqCode, Tag.none]
    · simp only [SureO.toNoun]
      rw [other ned hn]
      simp [hn, loob]

theorem lne_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), ∀ e ∈ fk, ∀ L : Noun,
    nock (C lneGF (C (lzfE e) (C lneGate (C L (C comp.door (C G ctx)))))) lneGF
      = some (loob (noneEq e.1.2 && noneEq e.2.2))
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hy := lne_all y
      have hn := lne_all n
      unfold lneGF
      cases ey : noneEq y <;> cases en : noneEq n <;>
        simp [nock_exec, lzfE, hy, hn, ey, en, loob]
    · exact lne_forks rest e he'

theorem lne_bonds : ∀ (bd : List (Nat × Laze CSet)), ∀ e ∈ bd, ∀ L : Noun,
    nock (C lneGB (C (lzbE e) (C lneGate (C L (C comp.door (C G ctx)))))) lneGB = some (loob (noneEq e.2))
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hl := lne_all l
      unfold lneGB
      simp [nock_exec, lzbE, hl]
    · exact lne_bonds rest e he'
end

end

/-- **The arm `+laze-none-equivalent` on the door gives the gate `lneGate`**. -/
theorem lne_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0x15575) (C (A 0) (A 1))))
    = some (C lneGate (C lneBunt (C comp.door y))) := by
  simp [nock_exec, lne_at', lneArm]

end Compiler
end Formalization
