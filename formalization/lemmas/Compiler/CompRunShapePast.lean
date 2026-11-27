import lemmas.Compiler.CompRunShapeInd
import lemmas.Compiler.CompRunShapePastCut
import lemmas.Compiler.CompRunRPast

/-!
# The link of `+laze-past` (track A, 2026-11-27)

`+laze-past` (door arm `0x154`, cut in `CompRunShapePastCut.lean`) against `lazePast` of
`Ska/RunShape.lean`, at the door of `+run-shape` (`rsDoor`), exact (crashes included) on every
`laze` and every nomm whose direct calls are in the code table (`CallCode`, the hypothesis of
`hd_gateR` for `+hinted`), for the `ShapeEnv` whose `pure` is that table's (`shapeCE`).

* `lzp_test`: the inline test is `lzpTestB`, the model's test.
* `callCode_hinted`: under `CallCode` the model's `hinted` returns.
* `lzp_id_at'`: the `+id` the gate pulls (`[9 0xabef 0 7]`) is `comp.id.arm`, by the kernel.
* **`lzp_gate`**: the gate is `lazePast`; **`lzp_door`**: the arm on the door gives that gate.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The test of `+laze-past`, as the model writes it. -/
noncomputable def lzpTestB (laz : Laze CSet) : Bool :=
  decide (laz.sure.ned = NeedOrd.none) && HoonSet.small laz.sure.lok && laz.fork.isEmpty

/-- **The test of `+laze-past`** on the noun of a `laze` at axis `12`. -/
theorem lzp_test (bat rest D : Noun) (laz : Laze CSet) :
    nock (C bat (C (C laz.toNoun rest) D)) lzpTest = some (loob (lzpTestB laz)) := by
  obtain ⟨⟨ned, lok⟩, f, b⟩ := laz
  unfold lzpTest
  cases ned with
  | pair p q =>
    obtain ⟨a, b', hp⟩ := no_cell p
    simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, hp, lzpTestB, Laze.sure, eqCode, loob]
  | both h t =>
    simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom, loob,
      Tag.both, Tag.none]
  | this =>
    simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom, loob,
      Tag.this, Tag.none]
  | none =>
    rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
    · cases f <;> simp [nock_exec, Laze.toNoun, Laze.forksNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB,
        Laze.sure, Laze.fork, eqCode_atom, eqCode, loob, Tag.none, hl, hsm]
    · cases f <;> simp [nock_exec, Laze.toNoun, Laze.forksNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB,
        Laze.sure, Laze.fork, eqCode_atom, eqCode, loob, Tag.none, hl, hsm]
    · rcases n with k | ⟨n1, n2⟩
      · by_cases hk : k = 1
        · subst hk
          rcases l with l | ⟨l1, l2⟩
          · by_cases hl0 : l = 0
            · subst hl0
              rcases r with r | ⟨r1, r2⟩
              · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom,
                  loob, Tag.none, hl, hsm, Ne.symm hr0]
              · simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom,
                  eqCode, loob, Tag.none, hl, hsm]
            · simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom,
                loob, Tag.none, hl, hsm, Ne.symm hl0]
          · simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom,
              eqCode, loob, Tag.none, hl, hsm]
        · simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom,
            loob, Tag.none, hl, hsm, Ne.symm hk]
      · simp [nock_exec, Laze.toNoun, SureO.toNoun, NeedOrd.toNoun, lzpTestB, Laze.sure, eqCode_atom,
          eqCode, loob, Tag.none, hl, hsm]

/-- The `CallEnv` whose code-table reads are those of a `ShapeEnv` (the other fields are not
read by `+hinted`). -/
noncomputable def shapeCE (env : ShapeEnv) : CallEnv where
  need := env.need
  sure := env.sure
  pure := fun b => (env.pure b).getD false
  ring := fun _ => Option.none
  cod := env.pure
  sof := fun _ _ _ _ _ => false

theorem orB_ne_none {x y : Option Bool} (hx : x ≠ Option.none) (hy : y ≠ Option.none) :
    orB x y ≠ Option.none := by
  rcases x with _ | _ | _ <;> simp_all [orB]

/-- Under `CallCode` the model's `hinted` returns. -/
theorem callCode_hinted (cod : Noun) (env : CallEnv) :
    ∀ n, CallCode cod env n → hinted env.cod n ≠ Option.none
  | Nomm.cons p q, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (callCode_hinted cod env p h.1) (callCode_hinted cod env q h.2)
  | Nomm.n0 _, _ => by simp [hinted]
  | Nomm.n1 _, _ => by simp [hinted]
  | Nomm.n3 p, h => by
    simp only [CallCode] at h; simp only [hinted]; exact callCode_hinted cod env p h
  | Nomm.n4 p, h => by
    simp only [CallCode] at h; simp only [hinted]; exact callCode_hinted cod env p h
  | Nomm.n5 p q, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (callCode_hinted cod env p h.1) (callCode_hinted cod env q h.2)
  | Nomm.n6 p q r, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (callCode_hinted cod env p h.1)
      (orB_ne_none (callCode_hinted cod env q h.2.1) (callCode_hinted cod env r h.2.2))
  | Nomm.n7 p q, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (callCode_hinted cod env p h.1) (callCode_hinted cod env q h.2)
  | Nomm.n10 _ v q, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (callCode_hinted cod env v h.1) (callCode_hinted cod env q h.2)
  | Nomm.n2 p q info, h => by
    simp only [CallCode] at h
    obtain ⟨hi, hp, hq⟩ := h
    rcases info with _ | ⟨b, k⟩
    · simp [hinted]
    · simp only [hinted]
      refine orB_ne_none ?_ (orB_ne_none (callCode_hinted cod env p hp) (callCode_hinted cod env q hq))
      rw [hi.2]; simp
  | Nomm.n11s _ q _, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (by simp) (callCode_hinted cod env q h)
  | Nomm.n11d _ hh q _, h => by
    simp only [CallCode] at h; simp only [hinted]
    exact orB_ne_none (by simp) (orB_ne_none (callCode_hinted cod env hh h.1) (callCode_hinted cod env q h.2))
  | Nomm.n12 _ _, _ => by simp [hinted]
  | Nomm.mean _ _ _ _ _, _ => by simp [hinted]

/-- The `+id` that the gate pulls (`[9 0xabef 0 7]` on the door). -/
theorem lzp_id_at' (y : Noun) : slot? 0xabef (C comp.door y) = some comp.id.arm := by kernel_rfl

/-- `+id` on the door of `+run-shape`: `idS`. -/
theorem rs_id (st : RSt CSet) (y : RsRest) :
    nock (C comp.door (C (rsGenNoun st y) ctx)) comp.id.arm
      = some (C (A st.idg) (rsGenNoun { st with idg := st.idg + 1 } y)) := by
  nock_open comp.id.arm
  simp [nock_exec, rsGenNoun]

/-- **`+laze-past` is `lazePast`** at the door of `+run-shape`, exact, on every `laze` and every
nomm whose direct calls are in the code table at axis `52` of `ctx` (`CallCode`), with `K` at
axis `7` of `ctx`. -/
theorem lzp_gate (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : ShapeEnv) (nom : Nomm) (hcc : CallCode cod (shapeCE env) nom) (st : RSt CSet) (y : RsRest)
    (laz : Laze CSet) :
    nock (C lzpGate (C (C laz.toNoun nom.toNoun) (rsDoor st y ctx))) lzpGate
      = (lazePast env laz nom st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  have ht := lzp_test lzpGate nom.toNoun (rsDoor st y ctx) laz
  conv => { lhs; arg 2; unfold lzpGate }
  rw [nock_op6, ht]
  by_cases hb : lzpTestB laz = true
  · have hp : (decide (laz.sure.ned = NeedOrd.none) && HoonSet.small laz.sure.lok && laz.fork.isEmpty) = true := hb
    simp [hb, loob, nock_exec, lazePast, hp, pure, StateT.pure, rsDoor]
  · simp only [Bool.not_eq_true] at hb
    have hp : (decide (laz.sure.ned = NeedOrd.none) && HoonSet.small laz.sure.lok && laz.fork.isEmpty) = false := hb
    rcases e : hinted env.pure nom with _ | b
    · exact absurd e (callCode_hinted cod (shapeCE env) nom hcc)
    have hh := hd_gateR cod (shapeCE env) nom b hcc e
    obtain ⟨s, f, bd⟩ := laz
    simp only [Laze.sure, Laze.fork] at hp
    have hp' : ¬ ((s.ned = NeedOrd.none ∧ HoonSet.small s.lok = true) ∧ f = []) := by
      intro ⟨⟨h1, h2⟩, h3⟩; subst h3; simp [h1, h2] at hp
    cases b
    · simp [hb, loob, nock_exec, lazePast, hp, hp', e, shLiftS, pure, StateT.pure, rsDoor, lzpHi, h7, hcode,
        compK_hd, hd_arm, hh, bind, StateT.bind, Laze.sure, Laze.fork, Laze.bond]
    · simp [hb, loob, nock_exec, lazePast, hp, hp', e, shLiftS, pure, StateT.pure, rsDoor, lzpHi, lzpId, h7, hcode,
        compK_hd, hd_arm, hh, bind, StateT.bind, lzp_id_at', comp_id_at, idS, rs_id, Laze.toNoun,
        Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun, Tag.none,
        HoonSet.toNoun_empty, Laze.sure, Laze.fork, Laze.bond]

/-- **The arm `+laze-past` on the door gives the gate `lzpGate`** (the call `[9 0x154 0 63]` of the
cases of `+run-shape`). -/
theorem lzp_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0x154) (C (A 0) (A 1))))
    = some (C lzpGate (C lzpBunt (C comp.door y))) := by
  simp [nock_exec, lzp_at', lzpArm]

end Compiler
end Formalization
