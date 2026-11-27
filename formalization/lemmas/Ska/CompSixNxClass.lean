import lemmas.Ska.CompSixNxTag

/-!
# The class `Six1`: `%6` at the top and under `%next`, with one contract

README Gaps 12.38, step 6.  `Six1` is what has a contract so far with a
`[6 c a b]` in it: a nomm of `Six0` (the `%6` at the top under `%done`,
nested in its branches down to `CallTreeA` leaves, `CompSixLSClass.lean`),
or a `%6` as the operand of `[4 p]` or `[3 p]` (run under `%next
(lazy-from-reg r)`, phase S) whose test is in `SixTest` and whose branches
are in `CallTreeA` with `NoEntF`.

* `CallTreeA.noSix`, `PickE` (the test's result under `%pick` has no
  entry), `pickE_pure`, `pickE_pickTree`, `runLC_n3_pickT`, `pickE_three`,
  `sixTest_pickF`, `sixTest_sixCount`: every test of `SixTest` meets
  `PickF`.
* `six1N_runTE`: such a `%6` meets `RunTE`.
* `Six1`, `finishLUC_contractSix1`: the contract at the top.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem CallTreeA.noSix {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) : noSix nm = true := by
  induction h with
  | n0 axe => rfl
  | cons _ _ ihp ihq => simp only [Comp.noSix, ihp, ihq, Bool.and_self]
  | ind _ _ => rfl
  | seven _ _ ihp ihq => simp only [Comp.noSix, ihp, ihq, Bool.and_self]
  | four _ ihp => simp only [Comp.noSix, ihp]
  | three _ ihp => simp only [Comp.noSix, ihp]
  | five _ _ ihp ihq => simp only [Comp.noSix, ihp, ihq, Bool.and_self]
  | n1 k => rfl

/-! ## The tests' results under `%pick` -/

/-- **The test's result under `%pick` has no entry.** -/
abbrev PickE (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {z o : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    runLC env sup nm (CGoalL.pick z o : CGoalL S) region g0 = some (nex, g1) → entries nex.laz = []

/-- A call-free test without `%6` (the text of `pickF_pure`). -/
theorem pickE_pure (env : CallEnv) {nm : Nomm} (hp : nm.pure = true) (h6 : noSix nm = true) :
    PickE (S := S) (Map := Map) env nm := by
  intro sup z o region g0 g1 nex h
  rw [show (CGoalL.pick z o : CGoalL S) = CGoal.toL (CGoal.pick z o) from rfl,
    runLC_eq env nm (Nomm.noCall_of_pure nm hp), runL_toL nm hp h6 _ region, map_apply] at h
  obtain ⟨⟨n, g'⟩, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact entries_ofSure _

/-- **The tests of `PickTree` with `NoEntF`**: the indirect call and `[0
axe]` begin with `[brn re z o]` and run under a goal with no entry
(`runLC_pick_next`), `[7 p q]` runs `p` under `q`'s result, which has no
entry. -/
theorem pickE_pickTree (env : CallEnv) {f : Noun} {nm : Nomm} (h : PickTree f nm) (hn : NoEntF nm) :
    PickE (S := S) (Map := Map) env nm := by
  induction h with
  | ind hp hq =>
    intro sup z o region g0 g1 nex hr
    rw [runLC_pick_next env sup (Or.inl ⟨_, _, rfl⟩) z o region g0] at hr
    exact noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial hr
  | n0 ha =>
    intro sup z o region g0 g1 nex hr
    rw [runLC_pick_next env sup (Or.inr ⟨_, ha, rfl⟩) z o region g0] at hr
    exact noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) trivial hr
  | @seven b c p q hp hq ih =>
    cases hn with
    | pure hpu h6 => exact pickE_pure env hpu h6
    | seven np nq =>
      intro sup z o region g0 g1 nex hr
      rw [runLC_n7] at hr
      obtain ⟨nx, g, h1, h2⟩ := bind_some hr
      have e1 := ih nq h1
      simp only [NextL.goal] at h2
      obtain ⟨s, hs⟩ : ∃ s, nx.laz = ofSure s := ⟨_, eq_ofSure_of_entries e1⟩
      rw [hs] at h2
      exact noEnt_of_noEntF (S := S) (Map := Map) env np (goal := CGoal.next s nx.th) trivial h2

/-- **The `%3` case of `run` under `%pick z o`.** -/
theorem runLC_n3_pickT (env : CallEnv) (sup : Option Nomm) (p : Nomm) (z o : Jmp) (region : List Nat) :
    (runLC env sup (Nomm.n3 p) (CGoalL.pick z o) region : CM Map (NextL S)) = (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := rfl

/-- **`[3 p]` with `NoEntF p` as a test**: `p` runs under a goal with no
entry. -/
theorem pickE_three (env : CallEnv) {p : Nomm} (hn : NoEntF p) : PickE (S := S) (Map := Map) env (Nomm.n3 p) := by
  intro sup z o region g0 g1 nex hr
  rw [runLC_n3_pickT] at hr
  obtain ⟨r, ga, h1, hr⟩ := bind_some hr
  obtain ⟨oc, gb, h2, hr⟩ := bind_some hr
  exact noEnt_of_noEntF (S := S) (Map := Map) env hn (goal := CGoal.next (lazyReg r) (jmp0 oc)) trivial hr

/-- **Every test of `SixTest` meets `PickF`.** -/
theorem sixTest_pickF (env : CallEnv) {f : Noun} {c : Nomm} (h : SixTest (S := S) f c) :
    PickF (S := S) (Map := Map) env c := by
  cases h with
  | pure _ ht hp => exact pickF_pure env hp ht.noSix
  | call ht hn => exact fun hr => entries_nil_flat (pickE_pickTree env ht hn hr)
  | three _ hn => exact fun hr => entries_nil_flat (pickE_three env hn hr)

theorem sixTest_sixCount {f : Noun} {c : Nomm} (h : SixTest (S := S) f c) : sixCount c = 0 := by
  cases h with
  | pure _ ht _ => exact ht.sixCount
  | call ht _ => exact ht.sixCount
  | three ht _ => simp only [sixCount, ht.sixCount]

/-! ## The `%6` under `%next` -/

/-- **A `%6` with a test of `SixTest` and branches of `CallTreeA` with
`NoEntF` meets `RunTE`** (phase S, `six_nextT`). -/
theorem six1N_runTE (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) {fc fa fb : Noun} {c a b : Nomm}
    {ba bb : Bool} (hc : SixTest (S := S) fc c) (ha : CallTreeA ba fa a) (na : NoEntF a) (hb : CallTreeA bb fb b)
    (nb : NoEntF b) : RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) :=
  six_nextT lib env (sixTest_pickD lib env P hc) (sixTest_pickF env hc) (sixN_callTreeA lib env P ha na)
    (sixN_callTreeA lib env P hb nb) (by decide)

/-! ## The class and its contract -/

/-- **The nomms with a `%6` that have a contract**: `Six0` (the `%6` at the
top under `%done`), or a `%6` as the operand of `[4 p]` or `[3 p]` with a
test of `SixTest` and branches of `CallTreeA` with `NoEntF`. -/
inductive Six1 : Noun → Nomm → Prop
  | top {f : Noun} {nm : Nomm} {k : Nat} : Six0 (S := S) f nm k → Six1 f nm
  | four {fc fa fb : Noun} {c a b : Nomm} {ba bb : Bool} : SixTest (S := S) fc c → CallTreeA ba fa a → NoEntF a →
      CallTreeA bb fb b → NoEntF b → Six1 (n2 (A 4) (n4 (A 6) fc fa fb)) (Nomm.n4 (Nomm.n6 c a b))
  | three {fc fa fb : Noun} {c a b : Nomm} {ba bb : Bool} : SixTest (S := S) fc c → CallTreeA ba fa a → NoEntF a →
      CallTreeA bb fb b → NoEntF b → Six1 (n2 (A 3) (n4 (A 6) fc fa fb)) (Nomm.n3 (Nomm.n6 c a b))

/-- **The contract of `Six1` at the top**: the whole-subject code of every
nomm of the class meets both halves of the contract for its formula, on
every subject, with no hypothesis about the run. -/
theorem finishLUC_contractSix1 (lib : Lib) (env : CallEnv) (P : Noun → Prop) {f : Noun} {nm : Nomm}
    (h : Six1 (S := S) f nm) {c : Straight Map} (hc : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  cases h with
  | top h0 => exact finishLUC_contractSix0 lib env P h0 hc N
  | @four fc fa fb c0 a b ba bb ht ha na hb nb =>
    have hcount : sixCount (Nomm.n6 c0 a b) ≤ 255 := by
      simp only [sixCount, sixTest_sixCount ht, ha.sixCount, hb.sixCount]; omega
    exact finishLUC_contractGBW (S := S) (Map := Map) lib (P := P) N
      (fun hr => four_doneT lib (six1N_runTE lib env P ht ha na hb nb) (minkC4_four lib _ _) hcount
        (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  | @three fc fa fb c0 a b ba bb ht ha na hb nb =>
    have hcount : sixCount (Nomm.n6 c0 a b) ≤ 255 := by
      simp only [sixCount, sixTest_sixCount ht, ha.sixCount, hb.sixCount]; omega
    exact finishLUC_contractGBW (S := S) (Map := Map) lib (P := P) N
      (fun hr => three_doneT lib (six1N_runTE lib env P ht ha na hb nb) (minkC3_three lib _ _) hcount
        (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc

/-! ## An instance: a calling test and a calling branch under `%3` -/

/-- **`[3 [6 [2 [0 3] [0 2]] [2 [0 6] [0 7]] [0 3]]]`**: both the test and
the yes branch call. -/
theorem threeSixCalls_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env (Nomm.n3 (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
      (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3))) = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 3) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3)))
        [s] c ∧
      ContractBwd lib N s (n2 (A 3) (n4 (A 6) (n3 (A 2) (slot 3) (slot 2)) (n3 (A 2) (slot 6) (slot 7)) (slot 3)))
        [s] c :=
  have H := finishLUC_contractSix1 (S := S) (Map := Map) lib env (fun _ => True)
    (Six1.three sixTest_ind (CallTreeA.ind (CallTreeA.n0 6) (CallTreeA.n0 7))
      (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)) (CallTreeA.n0 3) (NoEntF.pure rfl rfl)) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

-- Its whole-subject code exists and agrees with `+mink` on the 24
-- subjects of `CompSixLSCheck.lean`.
#guard SixCheck.sem [Nomm.n3 (Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)
  (Nomm.n2 (Nomm.n0 6) (Nomm.n0 7) Option.none) (Nomm.n0 3))] == (1, 1, 24, 24)

end Comp
end SkaModel
end Formalization
