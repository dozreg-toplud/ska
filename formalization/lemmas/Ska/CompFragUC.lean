import lemmas.Ska.CompConsGH
import lemmas.Ska.CompCallParent

/-!
# The fragment with calls `FragUC` and its contract

README Gaps 12.17 (twentieth session).  The joint induction `UOKC` over a
fragment with indirect calls: `FragC` (the nomms that call, so are hinted)
is the indirect call `[2 p q]` with parts in `FragU` and the cons whose head
is in `FragC` and whose tail is in `FragU`; `FragUC` is `FragU` or `FragC`.

* `fragC_hinted`: a nomm of `FragC` is hinted for every code table.
* `uokc_of_fragC`, `uokc_of_fragUC`: every `Annot` of a nomm of the fragment
  meets `UOKC` (the wrappers `Annot.memo`, `Annot.six0`, `Annot.six1` by
  `UOKC.wrap`).
* `finishLUC_contractUC`: the whole-subject code of a nomm of `FragUC` with
  at most 255 `%6` meets `BellContract … true`.
* `uokc_example2`: `[[[2 [0 3] [0 2]] [0 1]] [0 1]]`, a call two conses deep;
  `finishLUC` equals its raw blocks (`tools/hoon/cc2dump.hoon`, subject
  `[[4 0 1] 5]`, product `[[6 [4 0 1] 5] [4 0 1] 5]`): the outer tail's need
  is parked behind the inner cons (`0w3 mov v0 v3`), the inner tail's behind
  the call (`0w5 mov v0 v5`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The nomms that call**: the indirect call with call-free parts (its
formula not the literal of a `%bare` formula), and the cons whose head
calls and whose tail is call-free. -/
inductive FragC : Nomm → Prop
  | ind {p q : Nomm} : FragU (S := S) p → FragU (S := S) q → bareLitQ q = false →
      FragC (Nomm.n2 p q Option.none)
  | consH {p d : Nomm} : FragC p → FragU (S := S) d → FragC (Nomm.cons p d)

/-- **The fragment with calls.** -/
def FragUC (S : Type) [HoonSet S] (nm : Nomm) : Prop := FragU (S := S) nm ∨ FragC (S := S) nm

theorem fragC_hinted (cod : Bell → Option Bool) {nm : Nomm} (h : FragC (S := S) nm) : hinted cod nm = some true := by
  induction h with
  | ind _ _ _ => rfl
  | consH _ _ ih => simp only [hinted, ih]; rfl

/-- **The cons on every `Annot`**: `Annot.cons` gives `uokc_consH`, the
wrappers `UOKC.wrap`. -/
theorem uokc_consA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p d : Nomm}
    (ih : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (hh : hinted env.cod p = some true) (hd : FragU (S := S) d) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hA : Annot lib code P f nm) : nm = Nomm.cons p d → UOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | cons hA1 hA2 _ _ =>
    intro e
    cases e
    exact uokc_consH lib env (ih hA1) hh (runU_uok lib hd)
      (fun s hs gul tm r => mink_pure hok (fragU_pure hd) hA2 hs gul tm r) ⟨_, _, rfl⟩
  | memo hm _ ih' => intro e; exact UOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e
  | bareLit => intro e; cases e

/-- **The joint induction over `FragC`**: every `Annot` of a nomm that calls
meets `UOKC` (`uokc_indirect` with `minkN2_of_annot`, `uokc_consA`). -/
theorem uokc_of_fragC {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {nm : Nomm}
    (hf : FragC (S := S) nm) :
    ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f nm → UOKC (S := S) (Map := Map) lib env P f nm := by
  induction hf with
  | ind hp hq hbl =>
    intro P f hA
    exact uokc_indirect lib env (runU_uok lib hp) (runU_uok lib hq)
      (minkN2_of_annot hok hA rfl (fragU_pure hp) (fragU_pure hq) hbl)
  | consH hp hd ih =>
    intro P f hA
    exact uokc_consA hok env ih (fragC_hinted env.cod hp) hd hA rfl

/-- **Every `Annot` of a nomm of `FragUC` meets `UOKC`** (`uokc_of_uok`
with `mink_pure` on `FragU`, `uokc_of_fragC`). -/
theorem uokc_of_fragUC {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {nm : Nomm}
    (hf : FragUC S nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    UOKC (S := S) (Map := Map) lib env P f nm := by
  rcases hf with h | h
  · exact uokc_of_uok lib env (runU_uok lib h) (fun s hs gul tm r => mink_pure hok (fragU_pure h) hA hs gul tm r)
  · exact uokc_of_fragC hok env h hA

/-- **The contract on `FragUC`**: the whole-subject code of a nomm of
`FragUC` with at most 255 `%6`, standing for the bell's formula on the
subjects that fit it, has the need `this` and meets `BellContract … true`
(`finishLUC_contractG`). -/
theorem finishLUC_contractUC {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm) (hf : FragUC S nm)
    (hcount : sixCount nm ≤ 255) {env : CallEnv} {cd : Straight Map} (h : finishLUC (S := S) env nm = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractG lib (uokc_of_fragUC (Map := Map) hok env hf hA) hcount h N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

#guard monoOutC envR (Nomm.cons (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n0 1)) 9 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 9, Pole.cel 9, Pole.hed 9 11, Pole.mov 11 8, Pole.tal 9 10,
      Pole.mov 10 7] (hp 7)),
    (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)), (3, bk [Pole.mov 0 3] (hp 2)),
    (4, bk [Pole.con 4 5 2] (hp 3)), (5, bk [Pole.mov 0 5] (hp 4)), (6, bk [Pole.mov 6 4] (hp 5)),
    (7, bk [Pole.nok 7 8 6] (hp 6)), (8, none)])

/-- **`[[[2 [0 3] [0 2]] [0 1]] [0 1]]` end to end**: a call in the head of
a cons in the head of a cons, which no class before `FragUC` has. -/
theorem uokc_example2 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = C (C (n3 (A 2) (slot 3) (slot 2)) (slot 1)) (slot 1)) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))
      (Nomm.n0 1)) = some cd) (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.cons (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n0 1)) := by
    rw [hfol]
    exact Annot.cons (Annot.cons (Annot.indirect Annot.n0 Annot.n0) Annot.n0) Annot.n0
  have hf : FragUC S (Nomm.cons (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n0 1)) :=
    Or.inr (FragC.consH (FragC.consH (FragC.ind (FragU.x (FragX.frag fun _ => trivial))
      (FragU.x (FragX.frag fun _ => trivial)) rfl) (FragU.x (FragX.frag fun _ => trivial)))
      (FragU.x (FragX.frag fun _ => trivial)))
  exact finishLUC_contractUC hok hA hf (by decide) h N

end Comp
end SkaModel
end Formalization
