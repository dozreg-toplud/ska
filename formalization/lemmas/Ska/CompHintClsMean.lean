import lemmas.Ska.CompHintTenEx
import lemmas.Ska.CompHintRegKeep
import lemmas.Ska.CompHintSixRegClass
import lemmas.Ska.CompHintSixRegS2

/-!
# Pieces of the class of hinted nomms: `%mean`, `[7 [0 1] q]`, the `%6` (README Gaps 24)

* `runLCH_mean_eq`: `%mean` with no constant (`+mean-konst` `~`) runs as the
  kept dynamic hint `%mean` with the trap as its clue; so `regGBT_mean`,
  `surGBT_mean`, `shapeH_mean` (membership moves from `[11 [%mean p] q]`).
* `runLCH_n0one`, **`runLCH_seven01`** (`[7 [0 1] q]` runs as `q` with
  `sup = [0 1]`), `minkAs_seven01`, **`regGBT_seven01`**, `surGBT_seven01`,
  `DoneG7` (every run under `%done` gives `RunOKGBT`), `doneG7_seven01`.
* `sixNH_n1` (a constant branch, no entry), `pickD_n0`, `pickD_wut` (`?@` on
  any axis), `pickD_three0`: tests and branches of a `%6`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `%mean` with no constant -/

/-- **`%mean` with no constant is the kept dynamic case for `%mean`**, the
trap `p` as the clue. -/
theorem runLCH_mean_eq {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {sup : Option Nomm} {p q : Nomm} {b : Bell}
    {body : Noun} {k : Option Noun} (hk : meanKonst env b k = Option.none) (goal : CGoalL S) (region : List Nat) :
    (runLCH (S := S) (Map := Map) env snd true sup (Nomm.mean p b q body k) goal region) =
      runLCH env snd true sup (Nomm.n11d Tag.mean p q body) goal region := by
  have hs : hintDynamic Tag.mean = true := by decide
  simp only [runLCH, hk, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

section
variable {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun}
  {p q : Nomm} {b : Bell} {body : Noun} {k : Option Noun}

theorem regGBT_mean (hk : meanKonst env b k = Option.none)
    (H : RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n11d Tag.mean p q body)) :
    RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.mean p b q body k) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_mean_eq hk] at hr
  exact H b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr

theorem surGBT_mean {Ap : Sure S → Prop} (hk : meanKonst env b k = Option.none)
    (H : SurGBT (S := S) (Map := Map) snd lib N env P Ap f (Nomm.n11d Tag.mean p q body)) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap f (Nomm.mean p b q body k) := by
  intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr
  rw [runLCH_mean_eq hk] at hr
  exact H hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr

theorem shapeH_mean {Ap : Sure S → Prop} {k' : Nat} (hk : meanKonst env b k = Option.none)
    (H : ShapeH (S := S) (Map := Map) snd env Ap (Nomm.n11d Tag.mean p q body) k') :
    ShapeH (S := S) (Map := Map) snd env Ap (Nomm.mean p b q body k) k' := by
  intro sup sur th region g0 g1 nex hA d0 hta hr
  rw [runLCH_mean_eq hk] at hr
  exact H hA d0 hta hr

end

/-! ## `[7 [0 1] q]` -/

section
variable {snd : Nomm → NeedOrd → Bool} {env : CallEnv}

/-- `[0 1]` under a `%next` goal returns the goal. -/
theorem runLCH_n0one (sup : Option Nomm) (nx : NextL S) (region : List Nat) :
    (runLCH (S := S) (Map := Map) env snd true sup (Nomm.n0 1) nx.goal region : CM Map (NextL S)) = pure nx := by
  funext g
  simp [runLCH, NextL.goal, simpleNextL, bind_apply, pure_apply]

/-- **`[7 [0 1] q]` runs as `q`**, with `[0 1]` as `q`'s `sup`. -/
theorem runLCH_seven01 (sup : Option Nomm) (q : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runLCH (S := S) (Map := Map) env snd true sup (Nomm.n7 (Nomm.n0 1) q) goal region : CM Map (NextL S)) =
      runLCH env snd true (some (Nomm.n0 1)) q goal region := by
  rw [runLCH_n7]
  funext g
  rw [bind_apply]
  cases h : runLCH (S := S) (Map := Map) env snd true (some (Nomm.n0 1)) q goal region g with
  | none => rfl
  | some r => simp only [Option.bind_some, runLCH_n0one, pure_apply]

end

/-- `+mink` runs `[7 [0 1] c]` as `c`. -/
theorem minkAs_seven01 (lib : Lib) (c : Noun) : MinkAs lib (n3 (A 7) (slot 1) c) c where
  fwd := fun {gul n tm s r} h => by
    obtain ⟨n', hn, rb, hb, h1 | ⟨u, rfl, hc⟩⟩ := minkF_sevenC h
    · cases n' with
      | zero => simp [minkF] at hb
      | succ m =>
        rw [minkF_slot1] at hb
        cases hb
        exact absurd rfl (h1.1 s)
    · cases n' with
      | zero => simp [minkF] at hb
      | succ m =>
        rw [minkF_slot1] at hb
        cases hb
        exact ⟨m + 1, Nat.le_of_lt hn, hc⟩
  bwd := fun {gul tm s r} hc => (mink_sevenC_bwd ⟨1, minkF_slot1 lib gul 0 tm s⟩).2 s r rfl hc

/-- Every run under `%done`, from a state as the top gives, meets `RunOKGBT`. -/
def DoneG7 (lib : Lib) (N : Needs) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLCH env snd true sup nm CGoalL.done region g0 = some (nex, g1) →
    RunOKGBT lib N P f (CGoal.done : CGoal S) g0 g1 nex

section
variable {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}
  {c : Noun} {q : Nomm}

/-- **`[7 [0 1] q]` in `RegGBT`** from `q`. -/
theorem regGBT_seven01 (H : ∀ P, RegGBT (S := S) (Map := Map) snd lib N env P c q) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 7) (slot 1) c) (Nomm.n7 (Nomm.n0 1) q) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_seven01] at hr
  exact (H P b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr).minkAs (minkAs_seven01 lib c)

/-- **`[7 [0 1] q]` in `SurGBT Ap`** from `q`. -/
theorem surGBT_seven01 {Ap : Sure S → Prop} (H : ∀ P, SurGBT (S := S) (Map := Map) snd lib N env P Ap c q) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap (n3 (A 7) (slot 1) c) (Nomm.n7 (Nomm.n0 1) q) := by
  intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr
  rw [runLCH_seven01] at hr
  exact (H P hA b0 d0 hu hcl hcb h1 h2 hta hd hc hx hr).minkAs (minkAs_seven01 lib c)

/-- **`[7 [0 1] q]` under `%done`** from `q`. -/
theorem doneG7_seven01 (H : ∀ P, DoneG7 (S := S) (Map := Map) lib N env snd P c q) :
    DoneG7 (S := S) (Map := Map) lib N env snd P (n3 (A 7) (slot 1) c) (Nomm.n7 (Nomm.n0 1) q) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  rw [runLCH_seven01] at hr
  exact (H P b0 d0 hu hcl hcb hr).minkAs (minkAs_seven01 lib c)

end

/-! ## Tests and branches of a `%6` -/

section
variable {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}

/-- **A constant branch** `[1 k]`: `SixNH` with no entry (`sixN_of_uok`). -/
theorem sixNH_n1 (k : Noun) {Ap : Sure S → Prop} :
    SixNH (S := S) (Map := Map) snd lib N env P Ap (quote k) (Nomm.n1 k) 0 :=
  sixNH_of_sixN rfl rfl (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 k) fun _ => trivial))
    (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 k).annot P) hs gul tm r) rfl)

/-- **The test `[0 a]`** (`SixTest.pure`). -/
theorem pickD_n0 {a : Nat} (ha : 2 ≤ a) : ∃ kc, PickD (S := S) (Map := Map) lib N env P (slot a) (Nomm.n0 a) kc :=
  ⟨0, sixTest_pickD lib env P (SixTest.pure (fragX_n0 (by omega)) (CallTreeA.n0 a) rfl)⟩

/-- **The test `?@` on the axis `a`**, `[6 [3 [0 a]] [1 1] [1 0]]` (the
text of `pickD_spotTest`). -/
theorem pickD_wut {a : Nat} (ha : 2 ≤ a) :
    ∃ kc, PickD (S := S) (Map := Map) lib N env P (n4 (A 6) (n2 (A 3) (slot a)) (quote (A 1)) (quote (A 0)))
      (Nomm.n6 (Nomm.n3 (Nomm.n0 a)) (Nomm.n1 (A 1)) (Nomm.n1 (A 0))) kc :=
  ⟨_, pickD_of_uok lib env (uok_x lib (FragX.six (FragX.three (fragX_n0 (by omega)))
      (FragX.frag (nm := Nomm.n1 (A 1)) fun _ => trivial) (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial)))
    (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl (Annot.n6 (Annot.n3 Annot.n0) Annot.n1 Annot.n1) hs gul tm r)
    (by simp [sixCount])⟩

/-- **The test `[3 [0 a]]`** (`pickD_three`). -/
theorem pickD_three0 {a : Nat} (ha : 2 ≤ a) :
    ∃ kc, PickD (S := S) (Map := Map) lib N env P (n2 (A 3) (slot a)) (Nomm.n3 (Nomm.n0 a)) kc :=
  ⟨0, pickD_three lib env (CallTreeA.n0 a) (NoEntF.pure rfl rfl)⟩

end

end Comp
end SkaModel
end Formalization
