import lemmas.Ska.CompGenConsG
import lemmas.Ska.CompGenConsJ

/-!
# The cons of two leaves in `RunOKGen`, and the example's contract

README Gaps 12.39, item 11.  The frame (`frameG_cons00`), the fronts
(`frontsG_cons00`), the sure part and `nec` (`semCore_cons00`), with the
copy's semantics per label (`CopyOKL.runAt`), its preconditions
(`consCopyPre`) and `LabDisj` of the merged tree (`labDisj_copyLazyL`), make
`runOKGen_cons00`.  Then `nextGG_cons0` puts `[[0 a] [0 b]]` in the class
`NextGG`, and `exCons_contract` is the contract of the example
`[7 [[0 2] [0 3]] [6 [2 [0 3] [0 2]] [0 2] [0 2]]]`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The cons of two leaves in `RunOKGen`**, at any `GoalG` goal (forks,
bonds, repeated labels) whose registers are no keys of `cond`, with
`LabUniq` and `Clean` needs and a jump without arguments. -/
theorem runOKGen_cons00 (lib : Lib) {N : Needs} {P : Noun → Prop} {f : Noun} (env : CallEnv) (sup : Option Nomm)
    {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b) (M : MinkEq lib P f (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)))
    {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (G : GoalG (Map := Map) L th g0) (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none) (lu : Raw.LabUniq L)
    (cl : Clean L.sure.ned) (ecl : ∀ e ∈ entries L, Clean e.2.sure.ned) (hta : th.args = [])
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (CGoalL.next L th) region g0 = some (nex, g1))
    (W : Noun → Noun) :
    RunOKGen lib N P f L th (pureWit (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (fun _ => Need.none) W) false g0 g1 nex ∧
      GrowU g0 g1 ∧ ∀ k ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 k := by
  obtain ⟨hed, tel, hed', tel', gS, CA⟩ := consAt_of_run env sup ha hb G lu d0 hu h
  have CP := consCopyPre CA G cl ecl
  have CR := CopyOKL.runAt CA.cp
  have CR0 := CR
  obtain ⟨PC, PPC, OC, AC⟩ := CR0
  have LD : LabDisj nex.laz := labDisj_copyLazyL CA.hc CA.dS CA.luh CA.lut
    (fun k F hF => ((CP k).1 F hF).2.2) (fun k => (AC k (CP k).1 (CP k).2).2.2.1)
  have F := frameG_cons00 CA G hnc hec hcb CR CP LD W
  have FS := frontsG_cons00 CA G hec hcb CR CP W
  obtain ⟨S1, S2, S3⟩ := semCore_cons00 (N := N) lib M CA G hnc hcb hta CR CP W
  exact ⟨{ toFrameG := F, nec := S3, front := FS, sem := S1, semB := S2 }, CA.grow, CA.norep⟩

/-- **`+mink` of the cons of two leaves is the pure evaluation.** -/
theorem minkEq_cons00 (lib : Lib) (P : Noun → Prop) (a b : Nat) :
    MinkEq lib P (C (slot a) (slot b)) (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) := fun s hs gul tm r =>
  mink_pure (codeOK_none lib) rfl ((CallTreeA.cons (CallTreeA.n0 a) (CallTreeA.n0 b)).annot P) hs gul tm r

/-- **The cons of two leaves is in the class `NextGG`** (axes at least `2`). -/
theorem nextGG_cons0 (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) {a b : Nat} (ha : 2 ≤ a)
    (hb : 2 ≤ b) :
    NextGG (S := S) (Map := Map) lib N env P (C (slot a) (slot b)) (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) := by
  intro sup region g0 g1 L th nex G hnc hec lu cl ecl hta b0 d0 hu hcl hcb h
  obtain ⟨R, hg, hn⟩ := runOKGen_cons00 (N := N) lib env sup ha hb (minkEq_cons00 lib P a b) G hnc hec lu cl ecl hta
    d0 hu hcb h (fun _ => Nock.Noun.atom 0)
  exact ⟨_, R, hg, hn⟩

/-- **The contract of the example `[7 [[0 2] [0 3]] [6 [2 [0 3] [0 2]] [0 2]
[0 2]]]`**, unconditional: the cons's result has repeated labels (`[7 7 8
8]`, the wrapper of `+past-fork` split by the cons), which the flat tower
cannot take. -/
theorem exCons_contract (lib : Lib) (env : CallEnv) (N : Needs) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env (Nomm.n7 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3))
      (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 2))) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 7) (C (slot 2) (slot 3)) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2)))
        [s] c ∧
      ContractBwd lib N s (n3 (A 7) (C (slot 2) (slot 3)) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (slot 2) (slot 2)))
        [s] c :=
  exCons_contract_of lib env N (nextGG_cons0 lib N env (fun _ => True) (by decide) (by decide)) hc

end Comp
end SkaModel
end Formalization
