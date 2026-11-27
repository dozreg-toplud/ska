import lemmas.Compiler.CompMedeLink
import lemmas.Compiler.GitG

/-!
# The context of the door of `+comp` in the pill

The door's context `ctx` is the core of the gate `+comp`: `[battery [sample
K]]`, with `K` the core in which `+comp` is defined, at axis `63` of `cor`
(battery at `126`).  `K` is `[nh5592f9d7750f compTypes]`, and its payload
`compTypes` (axis `15` of `ctx`) is the core of the types of the library
(battery `nh15c74912d225`) on `[0 ana]`.

Every context whose axis `7` is `compK` meets `CompIn`, `CompLib` and
`CompMolds` (`comp_ctx_pill`).  The two mold runs of `CompMolds` (the bunts of
`need-lazy`, arm `191`, and of `sure`, arm `4`, of `compTypes`) are evaluated
by the kernel; the bunts are `[[[%none ~] ~] ~ ~]` and `[[%none ~] ~]`
(`ct_nl_bunt_eq`, `ct_su_bunt_eq`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The payload of `K`: the core of the library's types on `[0 ana]`. -/
def compTypes : Noun := C nh15c74912d225 (C (A 0) ana)

/-- The core `K` in which the gate `+comp` is defined. -/
def compK : Noun := C nh5592f9d7750f compTypes

/-- `K` is at axis `63` of `cor`. -/
theorem compK_at : slot? 63 cor = some compK := by kernel_rfl

theorem compK_layer2 : slot? 65535 compK = some layer2 := by
  have h : slot? 15 compK = slot? 1 ana := rfl
  have := slot_spine (by omega) (by omega) h 12
  simp only [show 2 ^ 12 * (15 + 1) - 1 = 65535 from rfl,
    show 2 ^ 12 * (1 + 1) - 1 = 8191 from rfl] at this
  rw [this]
  exact ana_layer2

theorem compK_gep : slot? 5597 compK = some gepArm := by kernel_rfl

theorem compK_cn : slot? 350 compK = some cnArm := by kernel_rfl

/-! ## The molds -/

noncomputable def ctNlArm : Noun := (slot? 191 compTypes).getD (A 0)
theorem ct_nl_at : slot? 191 compTypes = some ctNlArm := by kernel_rfl
noncomputable def ctNlGate : Noun := (evalFuel 2000 compTypes ctNlArm).getD (A 0)
theorem ct_nl_gate : nock compTypes ctNlArm = some ctNlGate :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)
noncomputable def ctNlBat : Noun := (slot? 2 ctNlGate).getD (A 0)
theorem ct_nl_bat : slot? 2 ctNlGate = some ctNlBat := by kernel_rfl
noncomputable def ctNlBunt : Noun := (evalFuel 2000 ctNlGate ctNlBat).getD (A 0)
theorem ct_nl_bunt : nock ctNlGate ctNlBat = some ctNlBunt :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- The bunt of `need-lazy` is `[[[%none ~] ~] ~ ~]`. -/
theorem ct_nl_bunt_eq : ctNlBunt = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)) := by
  kernel_rfl

noncomputable def ctSuArm : Noun := (slot? 4 compTypes).getD (A 0)
theorem ct_su_at : slot? 4 compTypes = some ctSuArm := by kernel_rfl
noncomputable def ctSuGate : Noun := (evalFuel 2000 compTypes ctSuArm).getD (A 0)
theorem ct_su_gate : nock compTypes ctSuArm = some ctSuGate :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)
noncomputable def ctSuBat : Noun := (slot? 2 ctSuGate).getD (A 0)
theorem ct_su_bat : slot? 2 ctSuGate = some ctSuBat := by kernel_rfl
noncomputable def ctSuBunt : Noun := (evalFuel 2000 ctSuGate ctSuBat).getD (A 0)
theorem ct_su_bunt : nock ctSuGate ctSuBat = some ctSuBunt :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- The bunt of `sure` is `[[%none ~] ~]`. -/
theorem ct_su_bunt_eq : ctSuBunt = C (C (A 0x656e6f6e) (A 0)) (A 0) := by
  kernel_rfl

/-! ## The context -/

/-- **The pill's context of the door meets `CompIn`, `CompLib` and
`CompMolds`**: every `ctx` with `K` (axis `63` of `cor`) at axis `7`, that is
every core of the gate `+comp` whatever its sample. -/
theorem comp_ctx_pill (ctx : Noun) (h7 : slot? 7 ctx = some compK) :
    CompIn ctx ∧ CompLib ctx ∧ CompMolds ctx := by
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have h15 : slot? 15 ctx = some compTypes := by
    have := slot_spine (by omega) (by omega) h1 1
    simp only [show 2 ^ 1 * (7 + 1) - 1 = 15 from rfl,
      show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
    rw [this]; rfl
  refine ⟨?_, ⟨compK, h7, compK_gep, compK_cn⟩, ?_, ?_⟩
  · have := slot_spine (by omega) (by omega) h1 15
    simp only [show 2 ^ 15 * (7 + 1) - 1 = 262143 from rfl,
      show 2 ^ 15 * (1 + 1) - 1 = 65535 from rfl] at this
    show slot? 262143 ctx = some layer2
    rw [this]; exact compK_layer2
  · exact ⟨compTypes, ctNlArm, ctNlGate, ctNlBat, ctNlBunt, h15, ct_nl_at, ct_nl_gate,
      ct_nl_bat, ct_nl_bunt⟩
  · exact ⟨compTypes, ctSuArm, ctSuGate, ctSuBat, ctSuBunt, h15, ct_su_at, ct_su_gate,
      ct_su_bat, ct_su_bunt⟩

/-- The same, stated through `cor`. -/
theorem comp_ctx_cor (ctx : Noun) (h7 : slot? 7 ctx = slot? 63 cor) :
    CompIn ctx ∧ CompLib ctx ∧ CompMolds ctx :=
  comp_ctx_pill ctx (h7.trans compK_at)

end Compiler
end Formalization
