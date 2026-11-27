import lemmas.Ska.CompNaryTopSixR

/-!
# `R` closed: the decrement loop on its own table

README Gaps 18.16, step 6.  `R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0
3]]`, `nommR = [6 [3 [0 3]] [7 [10 [3 [0 7]] [0 1]] [2 [0 1] [1 R] R-bell]]
[0 3]]` (the analysis reads `[9 2 c]` as `[7 c [2 [0 1] [0 2]]]`, `Annot.n9`,
and `[0 2]` of `c`'s product as `[1 R]`).  The contracts are for the bell's
own formula `R` (with its `%9`), so the yes branch is composed by
`minkC7_nine` (`doneE_sevenC`, `doneEM_sevenC`) and its call's formula part is
`[0 2]` on the products of the `%10`, which hold `R` at `2` (`img_tenR`).

* `img_tenR`, `hAp_R`, `hq1_R`, `hq2_R`: what the `%10` gives the call.
* `doneE_yesR9`, `doneEM_yesR9`: the yes branch under `%done`, both runs.
* `bellContract_RN`, `bellContract_RW`: `R`'s two real entries meet their
  bell contracts, given only the environment's facts of `R-bell` and the
  table's needs (`SplitsLess` holds for `R-bell`'s real need `[~ this]`:
  `splitsLess_walk`).
* `tableOK_R`: the table of `R`'s two entries (`table2 bellR rN rW`, with
  `envD`), only `NeedsRead` of `R`.
* `mink_R`: `+mink` on `[R x]` returns the atom that ends `x`.
* `closed_R`: each entry answers that atom at some number of levels, and
  every answer it gives is that one.
* `closed_dt`: `%dt` (`dt_closed_of_table`) with `TableOK` discharged.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem bellR_less : bellR.less = walkSock nounR := rfl

/-- **The products of the `%10` on `R`'s subjects hold `R` at `2`.** -/
theorem img_tenR {lib : Lib} {x : Noun} (h : Img lib (SkaModel.Fits bellR.less) tenRF x) : ∃ w, x = C nounR w := by
  obtain ⟨s, gul, hs, hm⟩ := h
  rw [bellR_less] at hs
  obtain ⟨z, rfl⟩ := fits_walk hs
  have e := (minkEq_tenR lib (fun _ => True) _ trivial gul [] _).mp hm
  cases z with
  | atom a => simp [pureEval, tenR, toneOf, edit?, axisPath, axisPathFuel, slot, slot?, slotAtPath] at e
  | cell a b =>
    simp [pureEval, tenR, toneOf, edit?, axisPath, axisPathFuel, slot, slot?, slotAtPath, editAtPath] at e
    exact ⟨_, e⟩

theorem hAp_R {lib : Lib} : ∀ x gul y, Img lib (SkaModel.Fits bellR.less) tenRF x →
    Mink lib gul [] x (slot 1) (Tone.zero y) → SkaModel.Fits bellR.less y := by
  intro x gul y hx hm
  have e1 := Mink.det hm ⟨1, minkStep_axis1 _ _ _ _ _⟩
  cases e1
  obtain ⟨w, rfl⟩ := img_tenR hx
  rw [bellR_less]; exact walk_fits nounR w

theorem hq1_R {lib : Lib} : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone},
    Img lib (SkaModel.Fits bellR.less) tenRF s → minkF lib gul n tm s (slot 2) = some rc → rc = Tone.zero bellR.fol := by
  intro s gul n tm rc hs hm
  obtain ⟨w, rfl⟩ := img_tenR hs
  cases n with
  | zero => simp [minkF] at hm
  | succ k => rw [minkF_succ_eq, minkStep_axis2] at hm; exact (Option.some.inj hm).symm

theorem hq2_R {lib : Lib} : ∀ {s gul : Noun} {tm : Trace},
    Img lib (SkaModel.Fits bellR.less) tenRF s → Mink lib gul tm s (slot 2) (Tone.zero bellR.fol) := by
  intro s gul tm hs
  obtain ⟨w, rfl⟩ := img_tenR hs
  exact ⟨1, by rw [minkF_succ_eq, minkStep_axis2]; rfl⟩

theorem lokS_slot1 (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    LOKS (S := S) (Map := Map) false lib N env P (slot 1) (Nomm.n0 1) :=
  lokS_n0 lib env (Nat.le_refl 1) (fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 1).annot _) hs gul tm r)

/-- The formula of `R`'s yes branch: `[9 2 [10 [3 [0 7]] [0 1]]]`. -/
def yesRF : Noun := n3 (A 9) (A 2) tenRF

theorem nounR_eq : nounR = n4 (A 6) (n2 (A 3) (slot 3)) yesRF (slot 3) := rfl

/-- **`R`'s yes branch, n-ary**: `DoneE` for the formula with `%9`. -/
theorem doneE_yesR9 (lib : Lib) {N : Needs} {env : CallEnv} {bNed : NeedOrd}
    (hring : env.ring bellR = Option.none) (hned : env.need bellR = some bNed)
    (hsof : ∀ m, env.sof m (Nomm.n0 1) (Nomm.n1 nounR) bellR bNed = false) (hNf : N bellR false = some bNed)
    (hspl : SplitsLess bellR bNed) :
    DoneE (S := S) (Map := Map) lib N env (SkaModel.Fits bellR.less) yesRF (Nomm.n7 tenR callR) :=
  doneE_sevenC lib (lokSE_tenR lib env _) (noEnt_pure env rfl rfl) (by decide)
    (doneE_tailN lib hring hned hsof hNf hspl (lokS_slot1 lib env _) (noEnt_pure env rfl rfl) (by decide) rfl
      hAp_R hq1_R hq2_R)
    (minkC7_nine lib _ 2 tenRF)

/-- **`R`'s yes branch, whole-subject**: `DoneEM`. -/
theorem doneEM_yesR9 (lib : Lib) {N : Needs} {env : CallEnv} {bNed ndT : NeedOrd}
    (hring : env.ring bellR = Option.none) (hned : env.need bellR = some bNed)
    (hNf : N bellR false = some bNed) (hNt : N bellR true = some ndT) :
    DoneEM (S := S) (Map := Map) lib N env (SkaModel.Fits bellR.less) yesRF (Nomm.n7 tenR callR) :=
  doneEM_sevenC lib (lokSE_tenR lib env _) (noEnt_pure env rfl rfl) rfl (by decide)
    (doneEM_tailP lib hring hned hNf hNt (lokS_slot1 lib env _) rfl (noEnt_pure env rfl rfl) (by decide) rfl
      hAp_R hq1_R hq2_R)
    (minkC7_nine lib _ 2 tenRF)

/-- **The n-ary bell contract of `R`** (its real code, need `[~ this]`, cape
`[& |]`). -/
theorem bellContract_RN (lib : Lib) {N : Needs} {env : CallEnv} (hring : env.ring bellR = Option.none)
    (hned : env.need bellR = some walkNeed)
    (hsof : ∀ m, env.sof m (Nomm.n0 1) (Nomm.n1 nounR) bellR walkNeed = false) (hNf : N bellR false = some walkNeed)
    {c : Straight Map} (h : finishLFC (S := S) env nommR walkNeed capeW (fun ned => (ned, [])) = some c) :
    BellContract lib N bellR false c := by
  have H : SixDN (S := S) (Map := Map) lib N env (SkaModel.Fits bellR.less) bellR.fol nommR (0 + 0 + 0 + 2) :=
    six_doneGBN (S := S) (Map := Map) lib env (P := SkaModel.Fits bellR.less) (c := Nomm.n3 (Nomm.n0 3))
      rfl (pickD_three3 lib env _) (sixD_of_doneE (doneE_yesR9 lib hring hned hsof hNf (splitsLess_walk bellR_less)))
      (sixD_slot3 lib env _) (by decide)
  exact finishLFC_bellContractGBN N (fun hr =>
    ⟨(H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1,
      (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).2.2⟩) rfl capeNorm_W (fun _ => rfl) h

/-- **The whole-subject bell contract of `R`.** -/
theorem bellContract_RW (lib : Lib) {N : Needs} {env : CallEnv} {ndT : NeedOrd} (hring : env.ring bellR = Option.none)
    (hned : env.need bellR = some walkNeed) (hNf : N bellR false = some walkNeed) (hNt : N bellR true = some ndT)
    {c : Straight Map} (h : finishLUCM (S := S) env nommR = some c) : BellContract lib N bellR true c := by
  have H : SixDWM (S := S) (Map := Map) lib N env (SkaModel.Fits bellR.less) bellR.fol nommR (0 + 0 + 0 + 4) :=
    six_doneGBWM (S := S) (Map := Map) lib env (P := SkaModel.Fits bellR.less) (c := Nomm.n3 (Nomm.n0 3))
      (pickDM_of_pickD rfl (pickD_three3 lib env _)) (sixDWM_of_doneEM (doneEM_yesR9 lib hring hned hNf hNt))
      (sixDWM_of_sixD rfl (sixD_slot3 lib env _)) (by decide)
  exact finishLUCM_bellContractGBW N (fun hr => (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) h

/-- **The table of `R`'s two real entries meets its contracts** (`envD`,
the environment of the dumps), given only that the n-ary entry's need is the
need read (`NeedsRead`). -/
theorem tableOK_R (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envD nommR walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envD nommR = some cW) (hR : NeedsRead envD (table2 bellR cN cW) bellR) :
    TableOK lib (table2 bellR cN cW) := by
  obtain ⟨cN', cW', h1, -, h3⟩ := hR
  simp only [table2, if_true, Bool.false_eq_true, if_false, Option.some.injEq] at h1
  subst h1
  have hned : envD.need bellR = some walkNeed := by simp [envD, walkNeed]
  have hn : cN.need = walkNeed := by rw [hned] at h3; exact (Option.some.inj h3).symm
  have hNf : Table.needs (table2 bellR cN cW) bellR false = some walkNeed := by
    rw [(table2_needs bellR cN cW).1, hn]
  intro b m c hc
  simp only [table2] at hc
  split at hc
  · rename_i e; subst e
    cases m with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc; subst hc
      exact bellContract_RN lib rfl hned (fun _ => rfl) hNf hN
    | true =>
      simp only [if_true, Option.some.injEq] at hc; subst hc
      exact bellContract_RW lib rfl hned hNf (table2_needs bellR cN cW).2 hW
  · cases hc

/-- **`+mink` on `R` returns the atom that ends `x`**, on every `[R x]`. -/
theorem mink_R (lib : Lib) (gul : Noun) : ∀ x, Mink lib gul [] (C nounR x) nounR (Tone.zero (lastAtom x))
  | Noun.atom a => ⟨3, by simp [nounR, minkF_succ_eq, minkStep, lastAtom, slot, slot?, axisPath, axisPathFuel,
      slotAtPath, tbind, wut]⟩
  | Noun.cell h t => by
    have IH := mink_R lib gul t
    have ht : Mink lib gul [] (C nounR (C h t)) (n2 (A 3) (slot 3)) (Tone.zero (A 0)) :=
      ⟨2, by simp [minkF_succ_eq, minkStep, slot, slot?, axisPath, axisPathFuel, slotAtPath, tbind, wut, n2]⟩
    have h10 : Mink lib gul [] (C nounR (C h t)) tenRF (Tone.zero (C nounR t)) :=
      (minkEq_tenR lib (fun _ => True) _ trivial gul [] _).mpr
        (by simp [pureEval, tenR, toneOf, edit?, axisPath, axisPathFuel, slot, slot?, slotAtPath, editAtPath])
    have h1 : Mink lib gul [] (C nounR t) (slot 1) (Tone.zero (C nounR t)) := ⟨1, minkStep_axis1 _ _ _ _ _⟩
    have h2 : Mink lib gul [] (C nounR t) (slot 2) (Tone.zero nounR) := ⟨1, by rw [minkF_succ_eq, minkStep_axis2]⟩
    have hy : Mink lib gul [] (C nounR (C h t)) yesRF (Tone.zero (lastAtom t)) :=
      ((minkC7_nine lib (fun _ => True) 2 tenRF).bwd trivial h10).2 _ _ rfl (mink_n2_of h1 h2 IH)
    rw [nounR_eq]
    exact (mink_sixC_bwd (fc := yesRF) (fd := slot 3) ht).2.1 _ rfl hy

/-- **`R`, closed, with a product**: on every subject `[R x]`, each of `R`'s
two real entries (`envD`), run on the table of its entries, answers at some
number of levels, and every answer it gives at any number of levels stands
for the atom that ends `x`.  The only hypothesis is `NeedsRead` of `R`. -/
theorem closed_R (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envD nommR walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envD nommR = some cW) (hR : NeedsRead envD (table2 bellR cN cW) bellR)
    (m : Bool) (x gul : Noun) {args : List Noun}
    (ha : (if m then some [C nounR x] else SkaModel.split cN.need (C nounR x)) = some args) :
    (∃ k ton, execEntry lib (tableOracle lib (table2 bellR cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) ∧ ToneRel lib (Table.needs (table2 bellR cN cW)) ton (Tone.zero (lastAtom x))) ∧
    (∀ k ton, execEntry lib (tableOracle lib (table2 bellR cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) → ToneRel lib (Table.needs (table2 bellR cN cW)) ton (Tone.zero (lastAtom x))) := by
  have hc : table2 bellR cN cW bellR m = some (if m then cW else cN) := by cases m <;> simp [table2]
  have ha' : (if m then some [C nounR x] else SkaModel.split (if m then cW else cN).need (C nounR x)) =
      some args := by cases m <;> simpa using ha
  have H := closed_entry lib (tableOK_R lib hN hW hR) hc (by rw [bellR_less]; exact walk_fits nounR x) ha' gul
  obtain ⟨n, hn⟩ := mink_R lib gul x
  refine ⟨?_, fun k ton he => ?_⟩
  · obtain ⟨ton, he, hrel⟩ := H.1 n _ hn
    exact ⟨n, ton, he, hrel⟩
  · obtain ⟨r, hr, hrel⟩ := H.2 k ton he
    rw [Mink.det hr ⟨n, hn⟩] at hrel
    exact hrel

/-- **`%dt` closed on `R`'s table**, `TableOK` discharged by `tableOK_R`:
the only hypothesis left is `NeedsRead` of `R`. -/
theorem closed_dt (lib : Lib) {cN cW c : Straight FM}
    (hN : finishLFC (S := LS) envD nommR walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := LS) envD nommR = some cW) (hR : NeedsRead envD (table2 bellR cN cW) bellR)
    (hc : finishLUCM (S := LS) envD dtNomm = some c) (s gul p : Noun) :
    Mink lib gul [] s dtFolD (Tone.zero p) ↔
      ∃ k, execEntry lib (tableOracle lib (table2 bellR cN cW) k) () c [s] [] gul = some (Tone.zero p, ()) := by
  have hn : cN.need = NeedOrd.pair NeedOrd.none NeedOrd.this := by
    obtain ⟨cN', cW', h1, -, h3⟩ := hR
    simp only [table2, if_true, Bool.false_eq_true, if_false, Option.some.injEq] at h1
    subst h1
    simp [envD] at h3; exact h3.symm
  exact dt_closed_of_table lib hn (tableOK_R lib hN hW hR) hc s gul p

-- `R`'s real entries are `rN`, `rW`: the codes the closed theorems take exist
#guard (finishLFC (S := LS) (Map := FM) envD nommR walkNeed capeW (fun ned => (ned, []))).isSome
#guard rW.isSome
theorem rN_eq : rN = finishLFC (S := LS) (Map := FM) envD nommR walkNeed capeW (fun ned => (ned, [])) := rfl

/-- **`R` closed on its real entries** `rN`, `rW` (`closed_R` at `S := LS`,
`Map := FM`), with only `NeedsRead` of `R`. -/
theorem closed_R_real (lib : Lib) {cN cW : Straight FM} (hN : rN = some cN) (hW : rW = some cW)
    (hR : NeedsRead envD (table2 bellR cN cW) bellR) (m : Bool) (x gul : Noun) {args : List Noun}
    (ha : (if m then some [C nounR x] else SkaModel.split cN.need (C nounR x)) = some args) :
    (∃ k ton, execEntry lib (tableOracle lib (table2 bellR cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) ∧ ToneRel lib (Table.needs (table2 bellR cN cW)) ton (Tone.zero (lastAtom x))) ∧
    (∀ k ton, execEntry lib (tableOracle lib (table2 bellR cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) → ToneRel lib (Table.needs (table2 bellR cN cW)) ton (Tone.zero (lastAtom x))) :=
  closed_R (S := LS) lib (rN_eq ▸ hN) hW hR m x gul ha

end Comp
end SkaModel
end Formalization
