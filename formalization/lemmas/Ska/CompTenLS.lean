import lemmas.Ska.CompSixLSClass
import lemmas.Ska.CompTenLSCheck

/-!
# `[10 [a v] q]` under goals without entries, and `[7 p q]` under `%done`

README Gaps 12.35.  The checks first (`CompTenLSCheck.lean`): `%10` with
call-free and calling parts agrees with `+mink`, and every conclusion of
`LOKS.run` that is not semantic holds under the 30 flat lazy goals.

`LOKS` asks a run under EVERY flat lazy goal, entries included; for `%10`
that needs `+into` over the goal's bonds (`intoBonds`, the twin of
`splitBonds`: an `IntoAt` in place of `SplitAt`, and `pairLS_ok` with the
edit in place of the cell), which is not done.  The goal the `%10` of `R`
meets has no entry (it is the result of the tail call under `%done`), so
this file states the relation at goals without entries:

* `LOKSE x`: `LOKS x` with the premise `entries L = []` (so the premises
  about the goal's entries are gone) and without the clause on the jump;
  `LOKS.toE`: every member of `LOKS` meets it.
* `lokSE_of_uok`: every call-free nomm with `UOK` (every member of `FragX`)
  and no `%6` meets `LOKSE false`: `RunOKNV` of `UOK.next`, `RunOKNV.toGC`,
  `RunOKGC.toLC`, `RunOKLC.toB`, the fronts vacuous.  So does `%10` over
  `FragX` parts (`lokSE_ten`), and the instance `R` needs,
  `[10 [3 [0 7]] [0 1]]` (`lokSE_tenR`).
* `DoneE`: `DoneOK` under `%done` with a result without entries;
  `doneE_of_uok` (call-free, no `%6`: `[0 axe]`, the `%10` above);
  `doneE_seven`: `[7 p q]` with `q` of `DoneE` (on `p`'s products) and `p` of
  `LOKSE false` and `NoEnt` (the `seven` case of `callTreeA_done`, with the
  goal's entries known empty); `sixD_of_doneE`: a branch of `DoneE` meets
  `SixD` with the bound `0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`LOKS` at goals without entries**: the premises of `LOKS.run` that
are left when `entries L = []`, and its conclusions but the jump's. -/
structure LOKSE (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) → Clean L.sure.ned →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      Flat nex.laz ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)

/-- **Every member of `LOKS` meets `LOKSE`.** -/
theorem LOKS.toE {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS (S := S) (Map := Map) x lib N env P f nm) : LOKSE (S := S) (Map := Map) x lib N env P f nm := by
  refine ⟨fun _ hc hr => H.clean hc hr, fun {sup L th region g0 g1 nex} hE hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl
    hcs hr => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, L = ofSure s := ⟨_, eq_ofSure_of_entries hE⟩
  obtain ⟨R, hne, -, hfl, hec⟩ := H.run hcount b0 d0 hu hcl hcb h1 h2 hta (by rw [hE]; simp) hsd hsl
    (fun e he => by rw [hE] at he; cases he) (by rw [hE]; simp) (fun e he => by rw [hE] at he; cases he)
    (flat_ofSure _) hcs (fun e he => by rw [hE] at he; cases he) hr
  exact ⟨R, hne, hfl, hec⟩

/-- **A call-free nomm with `UOK` and no `%6` meets `LOKSE false`**: under
`ofSure s` the run is `runL` under a fork-free `%next`, whose `RunOKNV`
(`UOK.next`) gives `RunOKGC` (`MinkEq`), then `RunOKLC` with `noWit`, then
`RunOKLB`; the goal has no entry, so the fronts are vacuous; the result has
no entry (`RunOKNV.size`). -/
theorem lokSE_of_uok (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (u : UOK (S := S) (Map := Map) lib nm) (M : MinkEq lib P f nm) (h6 : sixCount nm = 0) :
    LOKSE (S := S) (Map := Map) false lib N env P f nm := by
  refine ⟨fun {sup L th region g0 g1 nex} hE hc hr => ?_, fun {sup L th region g0 g1 nex} hE hcount b0 d0 hu hcl hcb
    h1 h2 hta hsd hsl hcs hr => ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s, L = ofSure s := ⟨_, eq_ofSure_of_entries hE⟩
    rw [runLC_eq env nm (Nomm.noCall_of_pure nm u.pure)] at hr
    exact u.clean (goal := CGoal.next s th) hc hr
  · obtain ⟨s, rfl⟩ : ∃ s, L = ofSure s := ⟨_, eq_ofSure_of_entries hE⟩
    rw [runLC_eq env nm (Nomm.noCall_of_pure nm u.pure)] at hr
    have R := u.next (sur := s) (th := th) (region := region) ⟨h1, h2⟩ hta ⟨hsd, fun r hr => (hsl r hr).1⟩ hcs hcount
      b0 d0 hu hcl hcb (fun r hr => (hsl r hr).2) hr
    have e1 : entries nex.laz = [] := by
      have := R.size; rw [h6] at this; exact List.eq_nil_of_length_eq_zero (by omega)
    have e0 : entries (ofSure s : Lazy S) = [] := entries_ofSure s
    refine ⟨⟨noWit, { toRunOKLB := ((RunOKNV.toGC M R).toLC).toB (N := N), fs := fun e he => ?_ }⟩,
      by rw [e1]; simp, by rw [eq_ofSure_of_entries e1]; exact flat_ofSure _, fun e he => by rw [e1] at he; cases he⟩
    rw [e0] at he; cases he

/-- **`[10 [a v] q]` over parts of `FragX`, with `+mink` its pure value,
meets `LOKSE false`.** -/
theorem lokSE_ten (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {a : Nat} {v q : Nomm}
    (hv : FragX (S := S) v) (hq : FragX (S := S) q) (h6 : sixCount v + sixCount q = 0)
    (M : MinkEq lib P f (Nomm.n10 a v q)) : LOKSE (S := S) (Map := Map) false lib N env P f (Nomm.n10 a v q) :=
  lokSE_of_uok lib env (uok_x lib (FragX.ten hv hq)) M (by simpa [Comp.sixCount] using h6)

/-- `[0 axe]` with `axe ≥ 1` is in `FragX`. -/
theorem fragX_n0 {axe : Nat} (ha : 1 ≤ axe) : FragX (S := S) (Nomm.n0 axe) :=
  FragX.frag fun _ => trivial

/-- The `%10` of `R`. -/
def tenR : Nomm := Nomm.n10 3 (Nomm.n0 7) (Nomm.n0 1)

/-- Its formula, as `nommRF` reads it. -/
def tenRF : Noun := n3 (A 10) (C (A 3) (slot 7)) (slot 1)

theorem tenR_annot (lib : Lib) (code : Bell → Option Nomm) (P : Noun → Prop) : Annot lib code P tenRF tenR :=
  Annot.n10 (by decide) Annot.n0 Annot.n0

theorem minkEq_tenR (lib : Lib) (P : Noun → Prop) : MinkEq lib P tenRF tenR :=
  fun s hs gul tm r => mink_pure (codeOK_none lib) rfl (tenR_annot lib _ P) hs gul tm r

/-- **The `%10` of `R`, `[10 [3 [0 7]] [0 1]]`, meets `LOKSE false`** on
every set of subjects. -/
theorem lokSE_tenR (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    LOKSE (S := S) (Map := Map) false lib N env P tenRF tenR :=
  lokSE_ten lib env (fragX_n0 (by decide)) (fragX_n0 (by decide)) rfl (minkEq_tenR lib P)

/-! ## Under `%done` -/

/-- **`DoneOK` under `%done` with a result without entries**, from every
state a compile has. -/
abbrev DoneE (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) →
    DoneOK lib N P f g0 g1 nex ∧ entries nex.laz = []

/-- **A call-free nomm with `UOK` and no `%6` meets `DoneE`**: `UOKC.run`
at `%done` (as `n1_doneB`), the result without entries by `RunOKV.size`. -/
theorem doneE_of_uok (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (u : UOK (S := S) (Map := Map) lib nm) (M : MinkEq lib P f nm) (h6 : sixCount nm = 0) :
    DoneE (S := S) (Map := Map) lib N env P f nm := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  have U := uokc_of_uok (S := S) (Map := Map) lib env u M
  have hc := U.clean (goal := CGoal.done) trivial trivial hr
  rw [runLC_eq env nm (Nomm.noCall_of_pure nm u.pure)] at hr
  have R := u.done (region := region) trivial trivial (by rw [h6]; omega) b0 d0 hu hcl hcb hr
  have e1 : entries nex.laz = [] := by
    have := R.size; rw [h6] at this; exact List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨⟨(RunOKV.toGC (goal := CGoal.done) M trivial R).toB, by rw [e1]; simp,
    by rw [eq_ofSure_of_entries e1]; exact flat_ofSure _, hc, fun e he => by rw [e1] at he; cases he⟩, e1⟩

/-- **`[7 p q]` under `%done`**: `q` meets `DoneE` on `p`'s products, `p`
meets `LOKSE false` and `NoEnt`; `p` runs under `q`'s result, a goal
without entries (the `seven` case of `callTreeA_done`). -/
theorem doneE_seven (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun} {p q : Nomm}
    (Lp : LOKSE (S := S) (Map := Map) false lib N env P fb p) (Np : NoEnt (S := S) (Map := Map) env p)
    (hcount : sixCount p ≤ 255) (Hq : DoneE (S := S) (Map := Map) lib N env (Img lib P fb) fc q) :
    DoneE (S := S) (Map := Map) lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [runLC_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  obtain ⟨D, eq⟩ := Hq b0 d0 hu hcl hcb h1
  have Rq := D.run
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  obtain ⟨⟨Q, RS⟩, hne, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region) eq
    hcount (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj Rq.dist
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · exact e.elim
      · exact e.2, Rq.ncond x hx⟩) D.clean h2
  have h2' : runLC env sup p (CGoal.toL (CGoal.next nx.laz.sure nx.th : CGoal S)) region ga = some (nex, g1) := by
    simp only [CGoal.toL]; rw [← eq_ofSure_of_entries eq]; exact h2
  exact ⟨⟨runOKGB_sevenL (minkC7_seven lib P fb fc) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
    Lp.clean (L := nx.laz) eq D.clean h2, hec⟩, Np (goal := CGoal.next nx.laz.sure nx.th) trivial h2'⟩

/-- **A branch of `DoneE` meets `SixD` with the bound `0`.** -/
theorem sixD_of_doneE {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : DoneE (S := S) (Map := Map) lib N env P f nm) : SixD (S := S) (Map := Map) lib N env P f nm 0 :=
  fun b0 d0 hu hcl hcb hr => ⟨(H b0 d0 hu hcl hcb hr).1.run, by rw [(H b0 d0 hu hcl hcb hr).2]; exact Nat.le_refl _⟩

end Comp
end SkaModel
end Formalization
