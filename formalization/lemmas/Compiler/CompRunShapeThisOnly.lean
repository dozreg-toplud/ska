import lemmas.Compiler.CompRunShapeThisOnlyCut
import lemmas.Compiler.CompRunShapeFrom
import lemmas.Compiler.CompClaGen
import lemmas.Compiler.CompClaLink

/-!
# `+laze-this-only` (track A, 2026-11-28)

The second test of the kerf of `%6` under `[%next laz]` (`rs6Kerf`, door arm `0x2bfa` called on
the core at axis `127`, `CompRunShapeThisOnlyCut.lean`).  Its gate `ltoGate` is the battery
`thoBat` of `+this-only` (`CompSixKerf.lean`, `tho_all`) with `levy` read from `layer2` at
axis `262143` of the door's context (`CompIn ctx`), and the proof is that of `tho_all` on a
`laze`: the head of the shape is `%this` or `%none`, the `lok` is `~` or `[1 ~ ~]`
(`cs_small_cases`), and `+levy` over the forks (`ltoGF`) and the bonds (`ltoGB`), each calling
the gate's own core.

* **`lto_all`**: on every `laze` (forks and bonds to any depth), at the door `[comp.door [G
  ctx]]` for every `gen` `G`, the gate is `thisOnlyS`.  No other hypothesis.
* `lto_arm`: the arm builds its gate; `lto_at'` (cut file): the arm at core axis `0x2bfa`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem lto_arm (d : Noun) : nock d ltoArm = some (C ltoGate (C ltoBunt d)) := by
  unfold ltoArm; simp only [nock_exec]

theorem lto_ord_cell : ∀ o : NeedOrd, ∃ a b, o.toNoun = C a b
  | NeedOrd.pair _ _ => ⟨_, _, rfl⟩
  | NeedOrd.both _ _ => ⟨_, _, rfl⟩
  | NeedOrd.this => ⟨_, _, rfl⟩
  | NeedOrd.none => ⟨_, _, rfl⟩

theorem thisOnlyF_all : ∀ f : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    thisOnlyF f = f.all fun e => thisOnlyS e.1.2 && thisOnlyS e.2.2
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by simp [thisOnlyF, thisOnlyF_all rest]

theorem thisOnlyB_all : ∀ b : List (Nat × Laze CSet),
    thisOnlyB b = b.all fun e => thisOnlyS e.2
  | [] => rfl
  | (o, l) :: rest => by simp [thisOnlyB, thisOnlyB_all rest]

section
variable (hc : CompIn ctx) (G : Noun)
include hc

mutual
/-- **`+laze-this-only` on every `laze`** (forks and bonds to any depth): `thisOnlyS`. -/
theorem lto_all : ∀ laz : Laze CSet,
    nock (C ltoGate (C laz.toNoun (C comp.door (C G ctx)))) ltoGate = some (loob (thisOnlyS laz))
  | Laze.mk ⟨ned, lok⟩ fk bd => by
    have hL : slot? 262143 ctx = some layer2 := hc
    have hLF := levy_gate_map lzfE layer2 ltoGF (C (C (A 0) ltoBunt) (C (A 0) ltoBunt))
      (C ltoGate (C (C (SureO.toNoun ⟨ned, lok⟩) (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))
        (C comp.door (C G ctx))))
      (fun e => thisOnlyS e.1.2 && thisOnlyS e.2.2) fk
      (fun e he => lto_forks fk e he _)
    have hLB := levy_gate_map lzbE layer2 ltoGB (C (A 0) ltoBunt)
      (C ltoGate (C (C (SureO.toNoun ⟨ned, lok⟩) (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))
        (C comp.door (C G ctx))))
      (fun e => thisOnlyS e.2) bd
      (fun e he => lto_bonds bd e he _)
    rw [lz_toNoun_mk]
    simp only [thisOnlyS, ← thisOnlyF_all, ← thisOnlyB_all] at hLF hLB ⊢
    cases ned with
    | pair p q =>
      obtain ⟨a, b, hp⟩ := lto_ord_cell p
      conv => { lhs; arg 2; unfold ltoGate }
      simp [nock_exec, NeedOrd.toNoun, SureO.toNoun, hp, eqCode, loob]
    | both h t =>
      conv => { lhs; arg 2; unfold ltoGate }
      simp [nock_exec, NeedOrd.toNoun, SureO.toNoun, eqCode_atom, Tag.both, loob]
    | none =>
      simp only [SureO.toNoun, NeedOrd.toNoun, Tag.none] at hLF hLB ⊢
      conv => { lhs; arg 2; unfold ltoGate }
      rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyF fk <;> cases hb2 : thisOnlyB bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyF fk <;> cases hb2 : thisOnlyB bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl]
        rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hr0]
                · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
              · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hl0]
            · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
          · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hk]
        · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
    | this =>
      simp only [SureO.toNoun, NeedOrd.toNoun, Tag.this] at hLF hLB ⊢
      conv => { lhs; arg 2; unfold ltoGate }
      rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyF fk <;> cases hb2 : thisOnlyB bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl] at hLF hLB ⊢
        cases hb1 : thisOnlyF fk <;> cases hb2 : thisOnlyB bd <;>
          simp [nock_exec, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, loob, hb1, hb2]
      · rw [hl]
        rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hr0]
                · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
              · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hl0]
            · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]
          · simp [nock_exec, hsm, loob, eqCode_atom, Ne.symm hk]
        · simp [nock_exec, hsm, loob, eqCode_atom, eqCode]

theorem lto_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), ∀ e ∈ fk, ∀ L : Noun,
    nock (C ltoGF (C (lzfE e) (C ltoGate (C L (C comp.door (C G ctx)))))) ltoGF
      = some (loob (thisOnlyS e.1.2 && thisOnlyS e.2.2))
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hy := lto_all y
      have hn := lto_all n
      unfold ltoGF
      cases ey : thisOnlyS y <;> cases en : thisOnlyS n <;>
        simp [nock_exec, lzfE, hy, hn, ey, en, loob]
    · exact lto_forks rest e he'

theorem lto_bonds : ∀ (bd : List (Nat × Laze CSet)), ∀ e ∈ bd, ∀ L : Noun,
    nock (C ltoGB (C (lzbE e) (C ltoGate (C L (C comp.door (C G ctx)))))) ltoGB
      = some (loob (thisOnlyS e.2))
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hl := lto_all l
      unfold ltoGB
      simp [nock_exec, lzbE, hl]
    · exact lto_bonds rest e he'
end

/-- **The call from the door core**: the arm at core axis `0x2bfa` of `[comp.door [G ctx]]`,
slammed on `laz`, is `thisOnlyS laz` (the shape of the call in `rs6Kerf`). -/
theorem lto_call (laz : Laze CSet) :
    nock (C comp.door (C G ctx))
      (C (A 8) (C (C (A 9) (C (A 0x2bfa) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10)
        (C (C (A 6) (C (A 1) laz.toNoun)) (C (A 0) (A 2))))))))
      = some (loob (thisOnlyS laz)) := by
  have h := lto_all hc G laz
  simp [nock_exec, lto_at', lto_arm, h]

end

end Compiler
end Formalization
