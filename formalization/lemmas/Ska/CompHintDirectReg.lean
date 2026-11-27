import lemmas.Ska.CompHintLSDirect
import lemmas.Ska.CompHintSurEx
import lemmas.Ska.CompHintRegKeepEx
import lemmas.Ska.CompHintTenCheck

/-!
# The direct call in `RegFT`, and `spotArm`'s positions 5 and 4 from its `%10` (README Gaps 24.20)

* **`regFT_direct`**: the direct call `[2 p q b]` (`p` in `LOKSFH`, the
  callee not pure, `q` skipped and returning the callee's formula, the
  products of `p` fitting the bell) is in `RegFT` (`lokSH_directF`,
  `LOKSH.toF`, `RegFT.of_loksf`).
* `RegLike`: a sure need that asks one register and has an empty lock (the
  need the direct call hands the `p` of its `%7`: `lazy-from-reg` of the
  subject register, its lock `uni ~ ~` after the copy); `runLCH_n0_one`;
  **`directZ_shape`**: the direct call with `p = [0 1]` under `%next
  (lazy-from-reg r)` has a result without entries whose sure need is
  `RegLike` (the premise `hq` of `regGBT_sevenS`).  Checked first on the
  model on `d22`'s call (`#guard`).
* **`regGBT_spotArm5`**: position 5 of `spotArm`, `S3 = [spot [7 [10 6 S4
  [0 1]] [2 [0 1] [1 F] b]]]`, is in `RegGBT` from the `%10` in `SurGBT
  RegLike` (the one premise left on the hinted side: the `%10` itself) and
  the callee's table entry (`env.ring b = ~`, `env.need b`, the needs `N b`,
  `env.pure b = |`, `F = b.fol`, the products of the `%10` fitting
  `b.less`); **`regGBT_spotArm4`'** (`regGBT_spotArm45`): position 4, `S2 =
  [spot [4 S3]]`, from the same.  The sub-formula is `#guard`ed equal to the
  text of `spotArm` (`Compiler/CompRunHintCallEx.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

-- the statement first, on the model: `d22`'s call under `%next (lazy-from-reg 0)`
-- has a result without entries, its sure need `this` of a register, its lock empty
namespace HintTen
open HintNest HintKeep HintSpot HintSeven
#guard call22 matches Nomm.n2 (Nomm.n0 1) (Nomm.n1 _) (some (_, Option.none))
#guard (runLCH (S := LS) (Map := FM) envH sndH true Option.none call22 gReg [] gS).map
  (fun (nex, _) => (nex.laz.sure.ned matches Need.this _) && (entries nex.laz).isEmpty &&
    (HoonSet.toList nex.laz.sure.lok).isEmpty) == some true
#guard [gReg, CGoalL.next (ofSure (lazyReg 4)) (jmp0 2)].all fun G =>
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none call22 G [] gS).map
    (fun (nex, _) => (nex.laz.sure.ned matches Need.this _) && (entries nex.laz).isEmpty &&
      (HoonSet.toList nex.laz.sure.lok).isEmpty) == some true
end HintTen

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section
variable {snd : Nomm → NeedOrd → Bool}

/-- **The direct call is in `RegFT`.** -/
theorem regFT_direct (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false)
    (Sp : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fb p) (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol))
    (hc : sixCount (Nomm.n2 p q (some (b, Option.none))) ≤ 255) :
    RegFT (S := S) (Map := Map) snd lib N env P (n3 (A 2) fb fq) (Nomm.n2 p q (some (b, Option.none))) :=
  RegFT.of_loksf (lokSH_directF lib env hring hned hNf hNt hpure Sp hq hAp hq1 hq2).toF hc

/-- A sure need asking one register, with an empty lock. -/
def RegLike (sur : Sure S) : Prop := ∃ k, sur.ned = Need.this k ∧ HoonSet.toList sur.lok = []

/-- `[0 1]` under `%next L th` is the goal itself, the state unchanged. -/
theorem runLCH_n0_one {env : CallEnv} {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S}
    (h : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n0 1) (CGoalL.next L th) region g0 = some (nex, g1)) :
    nex = ⟨L, th⟩ ∧ g1 = g0 := by
  simp only [runLCH, simpleNextL, Nat.one_ne_zero, ↓reduceIte, bind_apply, pure_apply, Option.bind_some,
    Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **The direct call with `p = [0 1]` under `%next (lazy-from-reg r)`**:
its result has no entries and a `RegLike` sure need (`runLCH_cal`, `p` the
goal itself, `+copy` with the need that asks nothing). -/
theorem directZ_shape {env : CallEnv} {q : Nomm} {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none)
    (hned : env.need b = some bNed) (hq : safeFolFol q = true) (hpure : env.pure b = false)
    {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S}
    (h : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n2 (Nomm.n0 1) q (some (b, Option.none)))
      (CGoalL.next (ofSure (lazyReg rg)) th) region g0 = some (nx, g1)) :
    entries nx.laz = [] ∧ RegLike nx.laz.sure := by
  have hp' : (env.pure b && noneEquivalentL (ofSure (lazyReg rg) : Lazy S)) = false := by rw [hpure]; rfl
  obtain ⟨sub, gA, out, pro, g2, o', gT, nexS, g5, -, -, -, hp, hc⟩ := runLCH_cal hring hned hq hp' h
  obtain ⟨rfl, rfl⟩ := runLCH_n0_one hp
  unfold copyL at hc
  obtain ⟨oc, ge, -, hc⟩ := bind_some hc
  obtain ⟨laz, gl, hl, hc⟩ := bind_some hc
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [copyLazyL_ofSure] at hl
  obtain ⟨s, gs, hs, hl⟩ := bind_some hl
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  refine ⟨entries_ofSure _, ?_⟩
  unfold copyLazy at hs
  obtain ⟨⟨ned, ops⟩, g', hn, hs⟩ := bind_some hs
  simp only [lazyReg, Sure.bunt, copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at hn
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hn
  obtain ⟨u, gu, -, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  refine ⟨g2.re + 1, rfl, ?_⟩
  simp only [ofSure, sure_mk]
  exact List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    rcases (HoonSet.mem_uni _ _ x).1 hx with e | e <;> exact HoonSet.mem_empty x e

/-! ## `spotArm`'s positions 5 and 4 -/

/-- The `%10` of `S3`: `[10 6 S4 [0 1]]`. -/
def spotS3Ten (k4 : Noun) : Nomm := Nomm.n10 6 (spotS4 k4) (Nomm.n0 1)
def spotS3TenF (k4 : Noun) : Noun := n3 (A 10) (C (A 6) (spotS4F k4)) (slot 1)
/-- The recursion of `S3`: `[2 [0 1] [1 F] b]`. -/
def spotS3Call (F : Noun) (b : Bell) : Nomm := Nomm.n2 (Nomm.n0 1) (Nomm.n1 F) (some (b, Option.none))
def spotS3CallF (F : Noun) : Noun := n3 (A 2) (slot 1) (quote F)
/-- `S3 = [spot [7 [10 6 S4 [0 1]] [2 [0 1] [1 F] b]]]`, its clue `k3`. -/
def spotS3 (k3 k4 F : Noun) (b : Bell) (B3 : Noun) : Nomm :=
  Nomm.n11d tagSpot (Nomm.n1 k3) (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) B3
def spotS3F (k3 k4 F : Noun) : Noun := n3 (A 11) (C (A tagSpot) (quote k3)) (n3 (A 7) (spotS3TenF k4) (spotS3CallF F))
/-- `S2 = [spot [4 S3]]`, its clue `k2`. -/
def spotS2 (k2 k3 k4 F : Noun) (b : Bell) (B2 B3 : Noun) : Nomm :=
  Nomm.n11d tagSpot (Nomm.n1 k2) (Nomm.n4 (spotS3 k3 k4 F b B3)) B2
def spotS2F (k2 k3 k4 F : Noun) : Noun := n3 (A 11) (C (A tagSpot) (quote k2)) (n2 (A 4) (spotS3F k3 k4 F))

/-- **Position 5 of `spotArm`, `S3`, is in `RegGBT`**, from the `%10` in
`SurGBT RegLike` and the callee's table entry: `regFT_direct` (`p = [0
1]`, `q = [1 F]` with `F = b.fol`), `directZ_shape`, `regGBT_sevenS`,
`regGBT_n11dKept`.  What it assumes of the callee: it is not in the ring
and not pure, its need `bNed` is the analysis's (`N b false`), its formula
is `F`, and the products of the `%10` fit its `less` (`hAp`). -/
theorem regGBT_spotArm5 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (k3 k4 F B3 : Noun)
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false) (hF : F = b.fol)
    (hAp : ∀ x gul y, Img lib (fun _ => True) (spotS3TenF k4) x → Mink lib gul [] x (slot 1) (Tone.zero y) →
      SkaModel.Fits b.less y)
    (Hten : SurGBT (S := S) (Map := Map) snd lib N env (fun _ => True) RegLike (spotS3TenF k4) (spotS3Ten k4))
    (hsnd : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) NeedOrd.this = true) :
    RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS3F k3 k4 F) (spotS3 k3 k4 F b B3) := by
  have Hq : RegFT (S := S) (Map := Map) snd lib N env (Img lib (fun _ => True) (spotS3TenF k4)) (spotS3CallF F)
      (spotS3Call F b) :=
    regFT_direct lib env hring hned hNf hNt hpure (clueLOKS_n0 lib env _ 1) rfl hAp
      (fun _ h => by rw [← hF]; exact quote_hq1 h) (fun _ => by rw [← hF]; exact quote_hq2)
      (by simp [sixCount])
  have H7 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (n3 (A 7) (spotS3TenF k4) (spotS3CallF F))
      (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) :=
    regGBT_sevenS lib Hten Hq (fun h => directZ_shape hring hned rfl hpure h)
  have R : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS3F k3 k4 F) (spotS3 k3 k4 F b B3) :=
    regGBT_n11dKept H7 hsnd (clueLOKS_n1 lib env _ k3) (by simp [sixCount]) (noBondH_n1 k3) spot_dynamic spot_stop B3
  exact @R

/-- **Positions 5 and 4 of `spotArm`**: `S3` and `S2 = [spot [4 S3]]` in
`RegGBT` from the same premises (`regGBT_four`, `regGBT_n11dKept`). -/
theorem regGBT_spotArm45 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs)
    (k2 k3 k4 F B2 B3 : Noun)
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false) (hF : F = b.fol)
    (hAp : ∀ x gul y, Img lib (fun _ => True) (spotS3TenF k4) x → Mink lib gul [] x (slot 1) (Tone.zero y) →
      SkaModel.Fits b.less y)
    (Hten : SurGBT (S := S) (Map := Map) snd lib N env (fun _ => True) RegLike (spotS3TenF k4) (spotS3Ten k4))
    (hsnd : snd (Nomm.n7 (spotS3Ten k4) (spotS3Call F b)) NeedOrd.this = true)
    (h4 : snd (Nomm.n4 (spotS3 k3 k4 F b B3)) NeedOrd.this = true) :
    RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS3F k3 k4 F) (spotS3 k3 k4 F b B3) ∧
      RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS2F k2 k3 k4 F) (spotS2 k2 k3 k4 F b B2 B3) := by
  have R5 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS3F k3 k4 F) (spotS3 k3 k4 F b B3) :=
    regGBT_spotArm5 (S := S) (Map := Map) lib env snd N k3 k4 F B3 hring hned hNf hNt hpure hF hAp Hten hsnd
  exact ⟨R5, regGBT_n11dKept (regGBT_four R5 (minkC4_four lib _ (spotS3F k3 k4 F))) h4 (clueLOKS_n1 lib env _ k2)
    (by simp [sixCount]) (noBondH_n1 k2) spot_dynamic spot_stop B2⟩

end

-- the sub-formulas are `spotArm`'s (its text, `Compiler/CompRunHintCallEx.lean`, with `spotK l c l' c'`
-- = `[0 [l c] [l' c']]`), and `+sound` of `%this` holds of the `%7` and of the `%4` (`sndH`)
namespace HintTen
open HintNest HintKeep HintSpot HintSeven
def spK (l c l' c' : Nat) : Noun := C (A 0) (C (C (A l) (A c)) (C (A l') (A c')))
#guard (spotS3 (spK 108 38 108 46) (spK 108 42 108 45) (A 77) bellR (A 3)).toNoun ==
  (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 38 108 46))
    (Nomm.n7 (Nomm.n10 6 (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 42 108 45)) (Nomm.n0 13) (C (A 0) (A 13)))
        (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 1) (Nomm.n1 (A 77)) (some (bellR, Option.none))))
    (A 3)).toNoun
#guard (spotS2 (spK 108 36 108 47) (spK 108 38 108 46) (spK 108 42 108 45) (A 77) bellR (A 2) (A 3)).toNoun ==
  (Nomm.n11d 0x746f7073 (Nomm.n1 (spK 108 36 108 47)) (Nomm.n4 (spotS3 (spK 108 38 108 46) (spK 108 42 108 45)
    (A 77) bellR (A 3))) (A 2)).toNoun
#guard sndH (Nomm.n7 (spotS3Ten (spK 108 42 108 45)) call22) NeedOrd.this
end HintTen

end Comp
end SkaModel
end Formalization
