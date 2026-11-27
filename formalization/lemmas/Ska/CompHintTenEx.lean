import lemmas.Ska.CompHintSixRegS2
import lemmas.Ska.CompHintRegEx

/-!
# `%10` with a kept value: `spotArm`'s positions 4 and 5, `spotArm` whole, `d20` (README Gaps 24.21)

From `surGBT_tenKept'` (`CompHintTenSur.lean`):
* `into_regLike_fit`: under a `RegLike` need, `+into` at an axis of at
  least `2` gives a donor need every noun fits (a `this`, the lock empty).
* `surGBT_spotS4`: `S4 = [spot [0 13]]` in `SurGBT` at the class its
  `+past-if` asks (`SoundK`, `FitP`); `surGBT_spotS3Ten`: the `%10` of `S3`,
  `[10 6 S4 [0 1]]`, in `SurGBT RegLike` (the premise `Hten` of
  `regGBT_spotArm5`, now proved from `+sound` of `%this` of `[0 13]`).
* **`regGBT_spotArm45F`**: positions 5 and 4 with no hinted premise.
* **`contract_spotArm`**: `spotArm` at the top (`contract_spotS1S2` with
  `S2` from `regGBT_spotArm45F`): every position, from the callee's table
  entry and `+sound` of `%this` at five nomms.
* `runLCH_n10_done_next`, `ten_doneS`: `%10` under `%done` (the block `[don
  re]`, then the run under `%next (lazy-from-reg re)`); **`contract_d20`**.
* `outReasonTen`, the table of the 39 at the top (`#guard`: 20 in, with
  `d18` (`contract_d18`, `CompHintSixRegClass.lean`) and `d20`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Under a `RegLike` need, `+into` at an axis of at least `2` gives a
donor every noun fits** (its need a `this`, its lock empty). -/
theorem into_regLike_fit {sur : Sure S} {th : Jmp} {a : Nat} (ha : 2 ≤ a) {g g' : Gen Map} {d r : Sure S}
    {o : Nat} (hR : RegLike sur) (h : into (⟨sur, th⟩ : Next S) a g = some ((d, r, o), g')) (p : Noun) :
    FitsS d p := by
  obtain ⟨k, hk, hl⟩ := hR
  simp only [into] at h
  obtain ⟨o', g0, h0, h⟩ := bind_some h
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, hl', h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [intoLok, hl, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hl'
  obtain ⟨rfl, rfl⟩ := hl'
  rw [hk] at h3
  simp only [intoNeed, show a ≠ 0 by omega, show a ≠ 1 by omega, ↓reduceIte] at h3
  obtain ⟨k', rfl⟩ := intoLoop_this o' a k [] [] g0 g2 nd nr h3
  exact ⟨trivial, looks_empty _⟩

/-- `lazy-from-reg r` is `RegLike`. -/
theorem regLike_lazyReg (r : Nat) : RegLike (lazyReg r : Sure S) :=
  ⟨r, rfl, List.eq_nil_iff_forall_not_mem.mpr fun x hx => HoonSet.mem_empty x hx⟩

section
variable {snd : Nomm → NeedOrd → Bool}

/-- **A kept spot over a clue-free value `q` is a donor of `%10` under a
`RegLike` need**: `surGBT_tenKept'` with `v = [spot [1 k] q]`, `q` of
`LOKSFH` with `+sound` of `%this`, the value's class from
`surGBT_n11dKept` (the donor of `into_regLike_fit` fits every product). -/
theorem surGBT_tenSpot (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {fq : Noun} {q : Nomm}
    (Hq : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fq q) (hcq : sixCount q ≤ 255)
    (hsq : snd q NeedOrd.this = true) (k body : Noun) {a : Nat} (ha : 2 ≤ a) :
    SurGBT (S := S) (Map := Map) snd lib N env P RegLike
      (n3 (A 10) (C (A a) (n3 (A 11) (C (A tagSpot) (quote k)) fq)) (slot 1))
      (Nomm.n10 a (Nomm.n11d tagSpot (Nomm.n1 k) q body) (Nomm.n0 1)) :=
  surGBT_tenKept' ha rfl
    (surGBT_n11dKept (SurGBT.of_loksf (fun _ => True) Hq hcq) (clueLOKS_n1 lib env P k) (by simp [sixCount])
      (noBondH_n1 k) spot_dynamic spot_stop body)
    (fun hR hi => ⟨trivial, ⟨(into_regLike_sound ha hR hi).1, by rw [(into_regLike_sound ha hR hi).2]; exact hsq⟩,
      fun _ _ _ _ p _ => into_regLike_fit ha hR hi p⟩)

/-- **The `%10` of `S3`, `[10 6 S4 [0 1]]`, in `SurGBT RegLike`** (the
premise `Hten` of `regGBT_spotArm5`). -/
theorem surGBT_spotS3Ten (lib : Lib) {N : Needs} (env : CallEnv) (k4 : Noun)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true) :
    SurGBT (S := S) (Map := Map) snd lib N env (fun _ => True) RegLike (spotS3TenF k4) (spotS3Ten k4) :=
  surGBT_tenSpot lib (clueLOKS_n0 lib env _ 13) (by simp [sixCount]) h13 k4 (C (A 0) (A 13)) (by decide)

/-- **Positions 5 and 4 of `spotArm` with no hinted premise**: `S3` and
`S2 = [spot [4 S3]]` in `RegGBT` (`regGBT_spotArm45` with
`surGBT_spotS3Ten`), from the callee's table entry and `+sound` of `%this`
of the `%7`, of the `%4` and of `[0 13]`. -/
theorem regGBT_spotArm45F (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs)
    (k2 k3 k4 F B2 B3 : Noun)
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false) (hF : F = b.fol)
    (hAp : ∀ x gul y, Img lib (fun _ => True) (spotS3TenF k4) x → Mink lib gul [] x (slot 1) (Tone.zero y) →
      SkaModel.Fits b.less y)
    (hsnd : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) NeedOrd.this = true)
    (h4 : snd (Nomm.n4 (spotS3 k3 k4 F b B3)) NeedOrd.this = true)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true) :
    RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS3F k3 k4 F) (spotS3 k3 k4 F b B3) ∧
      RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS2F k2 k3 k4 F) (spotS2 k2 k3 k4 F b B2 B3) :=
  regGBT_spotArm45 (S := S) (Map := Map) lib env snd N k2 k3 k4 F B2 B3 hring hned hNf hNt hpure hF hAp
    (surGBT_spotS3Ten lib env k4 h13) hsnd h4

/-- **`spotArm` at the top, every position**: `S1` over the `%6` whose
test is `?@` and whose `no` branch is `S2` (`contract_spotS1S2`, `S2` from
`regGBT_spotArm45F`), both halves of the contract, traces included.  What
it assumes: the callee's table entry (`hring`, `hned`, `hNf`, `hNt`,
`hpure`, `hF`, the products of the `%10` fitting `b.less`), `+sound` of
`%this` of the `%7`, the `%4`, `[0 13]` and the `%6`, and the count of
`%6`s. -/
theorem contract_spotArm (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs)
    (k1 k2 k3 k4 F B1 B2 B3 : Noun)
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false) (hF : F = b.fol)
    (hAp : ∀ x gul y, Img lib (fun _ => True) (spotS3TenF k4) x → Mink lib gul [] x (slot 1) (Tone.zero y) →
      SkaModel.Fits b.less y)
    (hsnd7 : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) NeedOrd.this = true)
    (h4 : snd (Nomm.n4 (spotS3 k3 k4 F b B3)) NeedOrd.this = true)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true)
    (h6 : sixCount (spotSix (spotS2 k2 k3 k4 F b B2 B3)) ≤ 255)
    (hsnd : snd (spotSix (spotS2 k2 k3 k4 F b B2 B3)) NeedOrd.this = true) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd
      (Nomm.n11d tagSpot (Nomm.n1 k1) (spotSix (spotS2 k2 k3 k4 F b B2 B3)) B1) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 F))) [s] c ∧
      ContractBwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF (spotS2F k2 k3 k4 F))) [s] c :=
  contract_spotS1S2 lib env snd N k1 k2 k3 k4 F B1 B2 B3 hring hned hpure hsnd7 h4 h13
    (regGBT_spotArm45F (S := S) (Map := Map) lib env snd N k2 k3 k4 F B2 B3 hring hned hNf hNt hpure hF hAp hsnd7
      h4 h13).2 h6 hsnd hc

/-! ## `%10` under `%done`, `d20` -/

/-- `+run` of `[10 [a v] q]` under `%done` is the block `[don re]`, then
the run under `%next (lazy-from-reg re)` into it. -/
theorem runLCH_n10_done_next {a : Nat} {v q : Nomm} (env : CallEnv) (sup : Option Nomm) (region : List Nat)
    (g0 : Gen Map) :
    (runLCH env snd true sup (Nomm.n10 a v q) CGoalL.done region g0 : Option (NextL S × Gen Map)) =
      runLCH env snd true sup (Nomm.n10 a v q) (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) := by
  simp only [runLCH, bind_apply, simpleNextL_done, Option.bind_some]
  simp only [simpleNextL, pure_apply, Option.bind_some]

/-- **A `%10` in `SurGBT RegLike`, under `%done`** (`runLCH_n10_done_next`,
`runOKGBT_done`). -/
theorem ten_doneS {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {a : Nat} {v q : Nomm}
    (H : SurGBT (S := S) (Map := Map) snd lib N env P RegLike f (Nomm.n10 a v q))
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH env snd true sup (Nomm.n10 a v q) CGoalL.done region g0 = some (nex, g1)) :
    RunOKGBT lib N P f (CGoal.done : CGoal S) g0 g1 nex := by
  rw [runLCH_n10_done_next] at hr
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have GA := (growU_re g0 _).trans G1
  have R := H (regLike_lazyReg g0.re) (by simp [Gen.emitted]) (by simpa [Gen.emitted] using d0) (GA.up hu)
    (hcl.growU GA) (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl
    (by simp [lazyReg, Distinct]) (by simp [lazyReg, Clean])
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      exact ⟨by simp [Gen.emitted], by simp only [Gen.emitted]; exact condBelow_none hcb (Nat.le_refl _)⟩) hr
  exact runOKGBT_done hu hcb (by rw [R.ext.2.2.2 _ (by simp [Gen.emitted])]; exact hk_emitted_self d0 _) R

end

/-- `d20`: `[10 2 [11 [%spot [1 0]] [4 [0 3]]] [0 1]]`. -/
def exD20 : Nomm := Nomm.n10 2 exD19K (Nomm.n0 1)
def exD20F : Noun := n3 (A 10) (C (A 2) exD19KF) (slot 1)

namespace HintTenEx
open HintNest HintKeep HintSpot HintSeven
#guard dumped "d20" == some (exD20.toNoun, exD20F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD20).isSome
#guard sndH exD10Q NeedOrd.this
#guard sndH (Nomm.n0 13) NeedOrd.this
-- the nomm of `contract_spotArm` is `spotArm`'s text (`Compiler/CompRunHintCallEx.lean`, the clues
-- `spotK l c l' c'` = `spK l c l' c'`), the recursion `d22`'s call; `+sound` of `%this` holds of its parts
open HintTen in
#guard (Nomm.n11d tagSpot (Nomm.n1 (spK 108 29 108 48)) (spotSix (spotS2 (spK 108 36 108 47) (spK 108 38 108 46)
    (spK 108 42 108 45) (A 77) bellR (A 2) (A 3))) (A 1)).toNoun ==
  (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 29 108 48))
    (Nomm.n6 (Nomm.n6 (Nomm.n3 (Nomm.n0 6)) (Nomm.n1 (A 1)) (Nomm.n1 (A 0))) (Nomm.n1 (A 0))
      (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 36 108 47))
        (Nomm.n4 (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 38 108 46))
          (Nomm.n7 (Nomm.n10 6 (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 42 108 45)) (Nomm.n0 13) (C (A 0) (A 13)))
              (Nomm.n0 1))
            (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (A 77)) (some (bellR, Option.none))))
          (A 3)))
        (A 2)))
    (A 1)).toNoun
open HintTen in
#guard sndH (spotSix (spotS2 (spK 108 36 108 47) (spK 108 38 108 46) (spK 108 42 108 45) (A 77) bellR (A 2) (A 3)))
  NeedOrd.this
open HintTen in
#guard sndH (Nomm.n4 (spotS3 (spK 108 38 108 46) (spK 108 42 108 45) (A 77) bellR (A 3))) NeedOrd.this
end HintTenEx

section
variable {snd : Nomm → NeedOrd → Bool}

/-- **The contract at the top of the dumped `d20`**, `[10 2 [11 [%spot [1
0]] [4 [0 3]]] [0 1]]`: a `%10` whose value is a kept spot
(`surGBT_tenSpot`, `ten_doneS`), for any `snd` with `+sound` of `%this` of
`[4 [0 3]]`. -/
theorem contract_d20 (lib : Lib) (env : CallEnv) (N : Needs) {c : Straight Map}
    (hsq : snd exD10Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD20 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD20F [s] c ∧ ContractBwd lib N s exD20F [s] c := by
  have hq : CallTreeHU lib env N (fun _ => True) false exD10QF exD10Q :=
    CallTreeHU.four (b1 := true) (CallTreeHU.base (CallTreeD.n0 3) rfl)
  have T : SurGBT (S := S) (Map := Map) snd lib N env (fun _ => True) RegLike exD20F exD20 :=
    surGBT_tenSpot lib (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env hq).1.1 (by decide) hsq (A 0)
      exD10QF (by decide)
  have H := finishLUCH_contractGBT (S := S) (snd := snd) lib N (fun hr => ten_doneS T
    (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

/-! ## The table of the 39 at the top -/

/-- `outReasonSur` with `d18` (`contract_d18`) and `d20` (`contract_d20`) in. -/
def outReasonTen (nm : Nomm) : Option String :=
  if nm.toNoun == exD18.toNoun || nm.toNoun == exD20.toNoun then Option.none else outReasonSur nm

def reasonsTen : List (String × Option String) :=
  HintData.all.map fun (n, j) => (n, ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).bind outReasonTen)

#guard (reasonsTen.filter fun r => r.2.isNone).map Prod.fst ==
  ["s01", "s02", "s03", "s05", "s06", "d01", "d02", "d03", "d06", "d08", "d09", "d10", "d13", "d14", "d18", "d19",
    "d20", "d21", "d23", "m01"]

end Comp
end SkaModel
end Formalization
