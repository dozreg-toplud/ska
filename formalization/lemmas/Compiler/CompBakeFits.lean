import lemmas.Compiler.CompBakeNeed
import lemmas.Ska.BakeNeed

/-!
# `+need-fits` against the model

`+need-fits` (arm `4` of `K`, `nf_at`, its gate body `nfBody`, 169 cells
with the gate): on a need noun and any noun, the gate returns the loobean
of `needFits` (`nf_gate`, by induction on the need, both recursive calls
through the gate itself).  README Gaps 9, the MAP of 2026-11-27.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def nfBody : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))))))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 3) (C (A 0) (A 25))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 0) (A 25)) (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 0) (A 5)) (C (A 0) (A 2))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4)) (C (A 0) (A 122)))) (C (A 0) (A 7)))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 5)) (C (A 0) (A 123)))) (C (A 0) (A 7)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 0) (A 0))))))))) (C (A 0) (A 0)))))))) (C (A 1) (A 0))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 24)) (C (A 0) (A 26)))) (C (A 0) (A 1)))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 25)) (C (A 0) (A 27)))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 0) (A 0)))))))))))

theorem nf_at : slot? 4 compK = some (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) nfBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- **`+need-fits`** on a need: the loobean of `needFits`. -/
theorem nf_gate : ∀ (ned : Need) (som : Noun),
    nock (C nfBody (C (C ned.toNoun som) compK)) nfBody = some (loob (needFits ned som))
  | Need.none, som => by
    conv => { lhs; arg 2; unfold nfBody }
    generalize nfBody = B
    cases som <;> simp [nock_exec, Need.toNoun, Tag.none, Tag.both, Tag.this, needFits, loob]
  | Need.this r, som => by
    conv => { lhs; arg 2; unfold nfBody }
    generalize nfBody = B
    cases som <;> simp [nock_exec, Need.toNoun, Tag.none, Tag.both, Tag.this, needFits, loob]
  | Need.pair p q, som => by
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    cases som with
    | atom n =>
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B
      simp [nock_exec, Need.toNoun, hp, Tag.none, Tag.both, Tag.this, needFits, loob]
    | cell x y =>
      have ihp := nf_gate p x
      have ihq := nf_gate q y
      rw [hp] at ihp
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B at ihp ihq ⊢
      cases e1 : needFits p x <;> cases e2 : needFits q y <;>
        simp [nock_exec, Need.toNoun, hp, Tag.none, Tag.both, Tag.this, needFits, loob, ihp, ihq, e1, e2]
  | Need.both r h t, som => by
    cases som with
    | atom n =>
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B
      simp [nock_exec, Need.toNoun, Tag.none, Tag.both, Tag.this, needFits, loob]
    | cell x y =>
      have ihh := nf_gate h x
      have iht := nf_gate t y
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B at ihh iht ⊢
      cases e1 : needFits h x <;> cases e2 : needFits t y <;>
        simp [nock_exec, Need.toNoun, Tag.none, Tag.both, Tag.this, needFits, loob, ihh, iht, e1, e2]

end Compiler
end Formalization
