import lemmas.Compiler.CompSofFar
import lemmas.Compiler.CompShapeColMsg
import lemmas.Compiler.CompBakeNeed

/-!
# `+need-soft` and `+cell-sure` (README Gaps 19, item (f))

`+need-soft` is K arm `5466`, gate battery `nsBat` (134 cells,
`CompSofNouns.lean`): `%none`/`%this` give `|`; else `+cell-sure` (K arm
`48047`, `csBat`) of `[sur k]`, `&` when it is no; else the halves of the
need, and `|` of the two recursive calls on the sample `[h (hed-need-ord
sur) (hed:so k)]` and `[t (tel-need-ord sur) (tel:so k)]`.  The arms
`+hed-need-ord` (K arm `374`) and `+tel-need-ord` (K arm `92`) are track A's
`hon_gate`, `ton_gate` (`CompShapeColMsg.lean`); `hed:so`, `tel:so` come
from the library core at K axis `63` (`compK_lib`, `so_hed_gate`).

* `csu_arm`, **`csu_gate`**: `+cell-sure` is `cellSure` (`none`: `-.k` of
  `%void`).
* **`ns_gate`**: where `needSoft` returns, the gate returns its loobean.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem csu_arm (d : Noun) :
    nock d csArm = some (C csBat (C (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0))) d)) := by
  unfold csArm; simp only [nock_exec]

/-- **`+cell-sure` is `cellSure`**, for every need and sock. -/
theorem csu_gate (KC : Noun) (sur : NeedOrd) (k : Sock) :
    nock (C csBat (C (C sur.toNoun k.toNoun) KC)) csBat = (cellSure sur k).map loob := by
  conv => { lhs; arg 2; unfold csBat }
  cases sur with
  | pair p q =>
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [nock_exec, NeedOrd.toNoun, cellSure, e, Tag.both, loob]
  | both p q => simp [nock_exec, NeedOrd.toNoun, cellSure, Tag.both, loob]
  | _ =>
    rcases k with _ | ⟨c, d⟩
    · simp [nock_exec, NeedOrd.toNoun, Sock.toNoun, cellSure, Tag.both, Tag.none, Tag.this, Tag.void, loob]
    · rcases c with _ | _ | ⟨c1, c2⟩ <;> rcases d with _ | ⟨d1, d2⟩ <;>
        simp [nock_exec, NeedOrd.toNoun, Sock.toNoun, Cape.toNoun, cellSure, Tag.both, Tag.none, Tag.this, loob]

theorem orB_cases {x y : Option Bool} {s : Bool} (h : orB x y = some s) :
    (x = some true ∧ s = true) ∨ (x = some false ∧ y = some s) := by
  rcases x with _ | _ | _ <;> simp_all [orB]

/-- One case of `+need-soft`. -/
macro "ns_simp" : tactic => `(tactic|
  (simp [nock_exec, nock_ite, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, eqCode_atom, loob,
     ite_some, so.lib.arm_at, so_lib_arm, so.hed.arm_at, so_hed_arm, so.tel.arm_at, so_tel_arm, *]))

/-- **`+need-soft` is `needSoft`** where the model returns: for every need,
sure need and sock, the gate on `[ned sur k]` in `compK` returns the
model's loobean. -/
theorem ns_gate : ∀ (ned sur : NeedOrd) (k : Sock) (s : Bool), needSoft ned sur k = some s →
    nock (C nsBat (C (C ned.toNoun (C sur.toNoun k.toNoun)) compK)) nsBat = some (loob s) := by
  intro ned
  induction ned with
  | none =>
    intro sur k s h
    simp [needSoft] at h; subst h
    conv => { lhs; arg 2; unfold nsBat }
    simp [nock_exec, NeedOrd.toNoun, Tag.none, loob]
  | this =>
    intro sur k s h
    simp [needSoft] at h; subst h
    conv => { lhs; arg 2; unfold nsBat }
    simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, loob]
  | pair h t ihh iht =>
    intro sur k s hs
    simp only [needSoft] at hs
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 hs
    have hcs := (csu_gate compK sur k).trans (congrArg (Option.map _) hc)
    simp only [Option.map_some] at hcs
    have hK := compK_cs
    have hca := csu_arm
    have hl := compK_lib
    have hhed := so_hed_gate (C so.battery lib) k
    have htel := so_tel_gate (C so.battery lib) k
    have hho := hon_gate compK sur
    have hto := ton_gate compK sur
    have hha := hon_at
    have hta := ton_at
    have hhr := hon_arm
    have htr := ton_arm
    cases c
    · simp at hs; subst hs
      clear ihh iht
      conv => { lhs; arg 2; unfold nsBat }
      ns_simp
    · simp only [if_true] at hs
      rcases orB_cases hs with ⟨h1, rfl⟩ | ⟨h1, h2⟩
      · have e1 := ihh _ _ _ h1
        clear ihh iht hs h1
        conv => { lhs; arg 2; unfold nsBat }
        ns_simp
      · have e1 := ihh _ _ _ h1
        have e2 := iht _ _ _ h2
        clear ihh iht hs h1 h2
        conv => { lhs; arg 2; unfold nsBat }
        cases s <;> ns_simp
  | both h t ihh iht =>
    intro sur k s hs
    simp only [needSoft] at hs
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 hs
    have hcs := (csu_gate compK sur k).trans (congrArg (Option.map _) hc)
    simp only [Option.map_some] at hcs
    have hK := compK_cs
    have hca := csu_arm
    have hl := compK_lib
    have hhed := so_hed_gate (C so.battery lib) k
    have htel := so_tel_gate (C so.battery lib) k
    have hho := hon_gate compK sur
    have hto := ton_gate compK sur
    have hha := hon_at
    have hta := ton_at
    have hhr := hon_arm
    have htr := ton_arm
    cases c
    · simp at hs; subst hs
      clear ihh iht
      conv => { lhs; arg 2; unfold nsBat }
      ns_simp
    · simp only [if_true] at hs
      rcases orB_cases hs with ⟨h1, rfl⟩ | ⟨h1, h2⟩
      · have e1 := ihh _ _ _ h1
        clear ihh iht hs h1
        conv => { lhs; arg 2; unfold nsBat }
        ns_simp
      · have e1 := ihh _ _ _ h1
        have e2 := iht _ _ _ h2
        clear ihh iht hs h1 h2
        conv => { lhs; arg 2; unfold nsBat }
        cases s <;> ns_simp

end Compiler
end Formalization
