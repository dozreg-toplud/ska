import lemmas.Compiler.PokeLinkEvalCut
import lemmas.Compiler.PokeLinkLoopRun

/-!
# `+eval-finalized` against `efGo`: the subject and the cases (track P, README Gaps 23)

The trap `nomm-loop` (`efLoop`, cut in `PokeLinkEvalCut.lean`) runs on the
core `efK b M n sub`: `[[efHave efLoop] [nomm [sub [efBat [[b code] ana]]]]]`
(the gate `+eval-finalized` slammed on `[b code]`, `code` the noun of an
accumulator `M`, then `sub` and `nomm` pushed and the `|^` core built).  A
recursive call edits `nomm` (axis `6`) and, in `%7`, `sub` (axis `14`), and
pulls `$` (axis `5`).

* `EfLoopAt b M n`: wherever `efGo` on the flags of `M` returns on `n` from
  a sock `sub`, the trap returns its noun `[s pure total]` (`efRes`).
* `ef_disp_*`: the `?-` of `efLoop` picks the body of the nomm's case.
* the case lemmas `ef_*`: each takes `EfLoopAt` of the sub-nomms the case
  reads and gives `EfLoopAt` of the nomm.  Here: `%1`, `%4`, `%12`, `%3`,
  the cell, `%7`, `%mean`, `%11`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

set_option linter.unusedSimpArgs false

/-- The core of the trap `nomm-loop`: `[[have $] [nomm [sub [efBat [[b code] ana]]]]]`. -/
noncomputable def efK (b : Bell) (M : FinMap Bell Noun) (n : Nomm) (sub : Sock) : Noun :=
  C (C efHave efLoop) (C n.toNoun (C sub.toNoun (C efBat (C (C (TKey.enc b) (M.toNoun id)) ana))))

/-- The noun `[s pure total]` of a result of `efGo`. -/
def efRes (r : Sock × Bool × Bool) : Noun := C r.1.toNoun (flagNoun r.2)

/-- **The trap on a nomm**: where `efGo` returns, the trap returns its noun. -/
def EfLoopAt (b : Bell) (M : FinMap Bell Noun) (n : Nomm) : Prop :=
  ∀ (sub : Sock) (r : Sock × Bool × Bool), efGo (accFt M) sub n = some r →
    nock (efK b M n sub) efLoop = some (efRes r)

/-! ## The layers of `ana` the cases read -/

theorem ana_l2e : slot? 8191 ana = some layer2 := ana_layer2

theorem ana_l1 : slot? 0x3fff ana = some layer1 := by
  have h : slot? 8191 ana = slot? 1 layer2 := by rw [ana_layer2]; rfl
  have := slot_spine (by omega) (by omega) h 1
  simp only [show 2 ^ 1 * (8191 + 1) - 1 = 0x3fff from rfl,
    show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
  rw [this, layer2_layer1]

/-- A nomm's noun is a cell. -/
theorem nomm_toNoun_cell (n : Nomm) : ∃ h t, n.toNoun = C h t := by
  cases n <;> exact ⟨_, _, rfl⟩

/-! ## The `?-` of `efLoop` -/

section Disp

variable (b : Bell) (M : FinMap Bell Noun) (sub : Sock)

theorem ef_disp_cons (p q : Nomm) :
    nock (efK b M (Nomm.cons p q) sub) efLoop = nock (efK b M (Nomm.cons p q) sub) efCcons := by
  obtain ⟨h, t, e⟩ := nomm_toNoun_cell p
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun, e]

theorem ef_disp_0 (p : Nat) :
    nock (efK b M (Nomm.n0 p) sub) efLoop = nock (efK b M (Nomm.n0 p) sub) efC0 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_1 (p : Noun) :
    nock (efK b M (Nomm.n1 p) sub) efLoop = nock (efK b M (Nomm.n1 p) sub) efC1 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_2 (p q : Nomm) (i : Option (Bell × Option Noun)) :
    nock (efK b M (Nomm.n2 p q i) sub) efLoop = nock (efK b M (Nomm.n2 p q i) sub) efC2 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_3 (p : Nomm) :
    nock (efK b M (Nomm.n3 p) sub) efLoop = nock (efK b M (Nomm.n3 p) sub) efC3 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_4 (p : Nomm) :
    nock (efK b M (Nomm.n4 p) sub) efLoop = nock (efK b M (Nomm.n4 p) sub) efC4 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_5 (p q : Nomm) :
    nock (efK b M (Nomm.n5 p q) sub) efLoop = nock (efK b M (Nomm.n5 p q) sub) efC5 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_6 (p q r : Nomm) :
    nock (efK b M (Nomm.n6 p q r) sub) efLoop = nock (efK b M (Nomm.n6 p q r) sub) efC6 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_7 (p q : Nomm) :
    nock (efK b M (Nomm.n7 p q) sub) efLoop = nock (efK b M (Nomm.n7 p q) sub) efC7 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_10 (a : Nat) (v q : Nomm) :
    nock (efK b M (Nomm.n10 a v q) sub) efLoop = nock (efK b M (Nomm.n10 a v q) sub) efC10 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_11s (t : Nat) (q : Nomm) (bd : Noun) :
    nock (efK b M (Nomm.n11s t q bd) sub) efLoop = nock (efK b M (Nomm.n11s t q bd) sub) efC11 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_11d (t : Nat) (h q : Nomm) (bd : Noun) :
    nock (efK b M (Nomm.n11d t h q bd) sub) efLoop = nock (efK b M (Nomm.n11d t h q bd) sub) efC11 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_12 (p q : Nomm) :
    nock (efK b M (Nomm.n12 p q) sub) efLoop = nock (efK b M (Nomm.n12 p q) sub) efC12 := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun]

theorem ef_disp_mean (p : Nomm) (c : Bell) (q : Nomm) (bd : Noun) (k : Option Noun) :
    nock (efK b M (Nomm.mean p c q bd k) sub) efLoop = nock (efK b M (Nomm.mean p c q bd k) sub) efCmean := by
  rw [efLoop_eq]; simp [efK, nock_exec, Nomm.toNoun, Tag.mean]

end Disp

/-! ## The cases that read no arm -/

section Cases

variable (b : Bell) (M : FinMap Bell Noun)

theorem ef_1 (p : Noun) : EfLoopAt b M (Nomm.n1 p) := by
  intro sub r h
  simp only [efGo, Option.some.injEq] at h; subst h
  rw [ef_disp_1, efC1_eq]
  simp [efK, nock_exec, efRes, flagNoun, Sock.toNoun, Cape.toNoun]

theorem ef_4 (p : Nomm) : EfLoopAt b M (Nomm.n4 p) := by
  intro sub r h
  simp only [efGo, Option.some.injEq] at h; subst h
  rw [ef_disp_4, efC4_eq]
  simp [efK, nock_exec, efRes, flagNoun, Sock.toNoun, Cape.toNoun, Sock.dunno]

theorem ef_12 (p q : Nomm) : EfLoopAt b M (Nomm.n12 p q) := by
  intro sub r h
  simp only [efGo, Option.some.injEq] at h; subst h
  rw [ef_disp_12, efC12_eq]
  simp [efK, nock_exec, efRes, flagNoun, Sock.toNoun, Cape.toNoun, Sock.dunno, Nomm.toNoun]

end Cases

end Compiler
end Formalization
