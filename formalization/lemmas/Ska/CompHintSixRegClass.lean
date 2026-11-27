import lemmas.Ska.CompHintSixReg
import lemmas.Ska.CompHintTreeUEx
import lemmas.Ska.CompHintSurEx

/-!
# The `%6` constructor of `SurGBT` and `RegGBT`, and the dumped `d18` (README Gaps 24.21)

* `sixNH_of_sixN`: a hint-free branch without a direct call in `SixN` (the
  unhinted class) meets `SixNH` (`runLCH_eq`, `runLCM_eq`, `RunOKGB.toT`).
* **`surGBT_six`**: `[6 c a b]` is in `SurGBT Ap` when the test is hint-free,
  without a direct call, with `hinted` `some false`, in `PickD` (its result
  may have forks),
  and the branches meet `SixNH` at the sure needs `+fork-sure` makes of a
  member of `Ap` (`six_nextGBT`).
* **`regGBT_six`**: the same in `RegGBT`, the branches in `SixNH IsReg`
  (`forkSure_lazyReg`, `RegGBT.ofSur`).
* `pickD_spotTest` (position 2 of `spotArm`, the test `?@`, a `%6`, in
  `PickD`), **`regGBT_spotSix`** (`spotArm`'s `%6`, positions 2 and 3, in
  `RegGBT` from its branch `S2` in `RegGBT` with `EntH` and `TagH`),
  **`contract_spotS1`** (`spotArm` at the top, `S1` over the `%6`, from the
  same premises).
* `exD18`, **`contract_d18`**: the dumped `d18`, `[11 [%spot [0 2]] [6 [0 3]
  [1 1] [1 2]]]` (a spot over a `%6`, the fork inside the bond), both halves
  of the contract at the top (`finishLUCH_contractN11dKeptR` over
  `regGBT_six`), for any `snd` with `+sound` of `%this` of the `%6`.

Left for `spotArm` (`contract_spotS1`'s premises on `S2`): `RegGBT` of `S2`
(`regGBT_spotArm45`, from `Hten`), the bound `EntH IsReg S2 4` (four
entries on the model) and the tag clause `TagH IsReg S2` (`cond` untouched
on the model, `CompHintSixRegCheck.lean`): neither is proved for any hinted
run yet.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A hint-free branch without a direct call in `SixN` meets `SixNH`.** -/
theorem sixNH_of_sixN {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {Ap : Sure S → Prop} {f : Noun} {nm : Nomm} {k : Nat} (hh : nm.noHint = true) (hd : nm.noDirect = true)
    (H : SixN (S := S) (Map := Map) lib N env P f nm k) : SixNH (S := S) (Map := Map) snd lib N env P Ap f nm k := by
  intro sup sur th region g0 g1 nex hc b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs _ hr
  rw [runLCH_eq env snd true nm hh, runLCM_eq env true nm (by simp [hd])] at hr
  obtain ⟨R, k1, -, T⟩ := H hc b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hr
  exact ⟨R.toT, k1, T⟩

/-- **`[6 c a b]` in `SurGBT Ap`** (`six_nextGBT`). -/
theorem surGBT_six (lib : Lib) {N : Needs} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {P : Noun → Prop}
    {fc fa fb : Noun} {c a b : Nomm} {kc ka kb : Nat}
    (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (hch : c.noHint = true) (hcd : c.noDirect = true) (hcfk : hinted env.cod c = some false)
    {Ap Aa Ab : Sure S → Prop} (Ha : SixNH (S := S) (Map := Map) snd lib N env P Aa fa a ka)
    (Hb : SixNH (S := S) (Map := Map) snd lib N env P Ab fb b kb) (hk : 5 + ka + kb ≤ lazyMax)
    (h6 : sixCount (Nomm.n6 c a b) ≤ 255)
    (hA : ∀ {sur : Sure S} {o : Nat} {g g' : Gen Map} {s0 s1 : Sure S}, Ap sur → g.drop = false →
      forkSure sur o g.bo (g.bo + 1) { g with bo := g.bo + 2 } = some ((s0, s1), g') → Aa s0 ∧ Ab s1) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap (n4 (A 6) fc fa fb) (Nomm.n6 c a b) := by
  intro sup sur th region g0 g1 nex hAp b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr
  exact six_nextGBT lib env Hc hch hcd hcfk Ha Hb hk h6 b0 d0 hu hcl hcb th1 th2 hta hsd hsl hcs
    (fun hF => hA hAp d0 hF) hr

/-- **`[6 c a b]` in `RegGBT`**, the branches in `SixNH IsReg` (they run
under `%next (lazy-from-reg r)` of the registers of `+fork-sure`). -/
theorem regGBT_six (lib : Lib) {N : Needs} {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {P : Noun → Prop}
    {fc fa fb : Noun} {c a b : Nomm} {kc ka kb : Nat}
    (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (hch : c.noHint = true) (hcd : c.noDirect = true) (hcfk : hinted env.cod c = some false)
    (Ha : SixNH (S := S) (Map := Map) snd lib N env P IsReg fa a ka)
    (Hb : SixNH (S := S) (Map := Map) snd lib N env P IsReg fb b kb) (hk : 5 + ka + kb ≤ lazyMax)
    (h6 : sixCount (Nomm.n6 c a b) ≤ 255) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) :=
  RegGBT.ofSur (surGBT_six lib Hc hch hcd hcfk Ha Hb hk h6 (fun {sur o g g' s0 s1} hA hd hF => by
    obtain ⟨r, rfl⟩ := hA
    obtain ⟨r0, r1, rfl, rfl⟩ := forkSure_lazyReg hF hd
    exact ⟨⟨r0, rfl⟩, ⟨r1, rfl⟩⟩))

/-! ## The dumped `d18` -/

/-- The `%6` of `d18`: `[6 [0 3] [1 1] [1 2]]`. -/
def exD18Q : Nomm := Nomm.n6 (Nomm.n0 3) (Nomm.n1 (A 1)) (Nomm.n1 (A 2))
def exD18QF : Noun := n4 (A 6) (slot 3) (quote (A 1)) (quote (A 2))
/-- `d18`: `[11 [%spot [0 2]] [6 [0 3] [1 1] [1 2]]]`. -/
def exD18 : Nomm := Nomm.n11d tagSpot (Nomm.n0 2) exD18Q exD18QF
def exD18F : Noun := n3 (A 11) (C (A tagSpot) (slot 2)) exD18QF

namespace HintSix
open HintNest HintKeep HintSpot HintSeven
#guard dumped "d18" == some (exD18.toNoun, exD18F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD18).isSome
#guard sndH exD18Q NeedOrd.this
end HintSix

/-- `[6 [0 3] [1 1] [1 2]]` in `RegGBT`: the test `[0 3]` (`SixTest.pure`), the branches `sixN_of_uok` through `sixNH_of_sixN`. -/
theorem regGBT_d18Q (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop) :
    RegGBT (S := S) (Map := Map) snd lib N env P exD18QF exD18Q :=
  regGBT_six lib (sixTest_pickD lib env P (SixTest.pure (fragX_n0 (by decide)) (CallTreeA.n0 3) rfl))
    rfl rfl rfl
    (sixNH_of_sixN rfl rfl (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 1)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 1)).annot P) hs gul tm r) rfl))
    (sixNH_of_sixN rfl rfl (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 2)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 2)).annot P) hs gul tm r) rfl))
    (by decide) (by decide)

/-- **The contract at the top of the dumped `d18`**, `[11 [%spot [0 2]] [6
[0 3] [1 1] [1 2]]]`: a spot over a `%6` (`finishLUCH_contractN11dKeptR`
over `regGBT_d18Q`), for any `snd` with `+sound` of `%this` of the `%6`. -/
theorem contract_d18 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd exD18Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD18 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD18F [s] c ∧ ContractBwd lib N s exD18F [s] c := by
  have H := finishLUCH_contractN11dKeptR (S := S) (Map := Map) (snd := snd) lib (N := N) (P := fun _ => True)
    (regGBT_d18Q lib env snd N _) hsnd (clueLOKS_n0 lib env _ 2) (by decide) (noBondH_n0 2) spot_dynamic
    spot_stop _ hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-! ## `spotArm`'s `%6`: the test, and the `%6` from `S2` -/

/-- `spotArm`'s test `?@`: `[6 [3 [0 6]] [1 1] [1 0]]` (a `%6` itself). -/
def spotTest : Nomm := Nomm.n6 (Nomm.n3 (Nomm.n0 6)) (Nomm.n1 (A 1)) (Nomm.n1 (A 0))
def spotTestF : Noun := n4 (A 6) (n2 (A 3) (slot 6)) (quote (A 1)) (quote (A 0))
/-- `spotArm`'s `%6` with the branch `s2` (there `S2`): `[6 ?@ [1 0] s2]`. -/
def spotSix (s2 : Nomm) : Nomm := Nomm.n6 spotTest (Nomm.n1 (A 0)) s2
def spotSixF (fs2 : Noun) : Noun := n4 (A 6) spotTestF (quote (A 0)) fs2

namespace HintSix
open HintNest HintKeep HintSpot HintSeven HintTen
#guard spotTest.toNoun == testT.toNoun
#guard (spotSix s2c).toNoun == six2.toNoun
end HintSix

/-- **Position 2 of `spotArm`, the test `?@`, is in `PickD`** (a call-free
`%6`: `FragX.six`, `pickD_of_uok`, its formula its pure value). -/
theorem pickD_spotTest (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    PickD (S := S) (Map := Map) lib N env P spotTestF spotTest 2 :=
  pickD_of_uok lib env (uok_x lib (FragX.six (FragX.three (fragX_n0 (by decide)))
      (FragX.frag (nm := Nomm.n1 (A 1)) fun _ => trivial) (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial)))
    (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl (Annot.n6 (Annot.n3 Annot.n0) Annot.n1 Annot.n1) hs gul tm r)
    (by decide)

/-- **`spotArm`'s `%6` (positions 2 and 3) is in `RegGBT`** from its branch
`s2` (there `S2`) in `RegGBT` with at most four entries and the tag clause
(`regGBT_six`, `pickD_spotTest`; the yes branch `[1 0]` by `sixN_of_uok`). -/
theorem regGBT_spotSix (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (P : Noun → Prop)
    {fs2 : Noun} {s2 : Nomm} (H2 : RegGBT (S := S) (Map := Map) snd lib N env P fs2 s2)
    (K2 : EntH (S := S) (Map := Map) snd env IsReg s2 4) (T2 : TagH (S := S) (Map := Map) snd env IsReg s2)
    (h6 : sixCount (spotSix s2) ≤ 255) :
    RegGBT (S := S) (Map := Map) snd lib N env P (spotSixF fs2) (spotSix s2) :=
  regGBT_six lib (pickD_spotTest lib env P) rfl rfl rfl
    (sixNH_of_sixN rfl rfl (sixN_of_uok lib env (uok_x lib (FragX.frag (nm := Nomm.n1 (A 0)) fun _ => trivial))
      (fun s hs gul tm r => mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 (A 0)).annot P) hs gul tm r) rfl))
    (sixNH_of (RegGBT.toSur H2) K2 T2) (by decide) h6

/-- **`spotArm` at the top (position 1, `S1` over the `%6`)**, both halves of
the contract, from its branch `s2` (there `S2`) in `RegGBT` with `EntH` and
`TagH` (`regGBT_spotSix`, `finishLUCH_contractN11dKeptR`), for any `snd`
with `+sound` of `%this` of the `%6`. -/
theorem contract_spotS1 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (k1 B1 : Noun)
    {fs2 : Noun} {s2 : Nomm} (H2 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) fs2 s2)
    (K2 : EntH (S := S) (Map := Map) snd env IsReg s2 4) (T2 : TagH (S := S) (Map := Map) snd env IsReg s2)
    (h6 : sixCount (spotSix s2) ≤ 255) (hsnd : snd (spotSix s2) NeedOrd.this = true) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd (Nomm.n11d tagSpot (Nomm.n1 k1) (spotSix s2) B1) = some c) :
    c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF fs2)) [s] c ∧
      ContractBwd lib N s (n3 (A 11) (C (A tagSpot) (quote k1)) (spotSixF fs2)) [s] c := by
  have H := finishLUCH_contractN11dKeptR (S := S) (Map := Map) (snd := snd) lib (N := N) (P := fun _ => True)
    (regGBT_spotSix lib env snd N _ H2 K2 T2 h6) hsnd (clueLOKS_n1 lib env _ k1) (by simp [sixCount])
    (noBondH_n1 k1) spot_dynamic spot_stop B1 hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
