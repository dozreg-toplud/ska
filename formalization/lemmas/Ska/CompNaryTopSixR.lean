import lemmas.Ska.CompNaryTopSixE
import lemmas.Ska.CompNaryTopSixM
import lemmas.Ska.CompNaryTopSixN
import lemmas.Ska.CompSixLSRCall
import lemmas.Ska.CompNaryTopSixEx

/-!
# Recursion with a product: the walker `L`, closed

README Gaps 18.16, steps 4 and 5.  A `%6` at the top whose branch is a
direct call, for both entries:

* n-ary (`finishLFC`, `runLC env`): track C's `six_doneGBN` /
  `finishLFC_contractGBN` with the branch's `DoneE` from `doneE_tailN`;
* whole-subject (`finishLUCM`, `runLCM env true`): the copies
  `six_doneGBWM` / `finishLUCM_contractGBW` (CompNaryTopSixM.lean) with
  the branch's `DoneEM` from `doneEM_tailP` (here: `tailP_done` and the
  result without entries, from `runLCM_tailP`), `sixDWM_of_doneEM`, and the
  call-free parts read through `runLCM_true` (`pickDM_of_pickD`,
  `sixDWM_of_sixD`).
* `finishLFC_bellContractGBN`, `finishLUCM_bellContractGBW`: the bell
  contracts from those tops.
* The walker `L = [6 [3 [0 3]] [2 [[0 2] [0 7]] [0 2]] [0 3]]` on `[L x]`:
  `tableOK_walkL` (its two entries on the table of themselves, only
  `NeedsRead` of `L`), `mink_walkL` (`+mink` returns the atom that ends
  `x`, by induction on `x`), `closed_walkL` (each entry answers that atom at
  some number of levels, and every answer it gives is that one).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Parts for `runLCM env true` -/

/-- **The direct tail call with `mono` `&` meets `DoneEM`** (`tailP_done`
and a result without entries: the run of `p` under `%next (lazy-from-reg
sub-pes)` has none, `NoEnt`, and `+copy` with the empty need adds none). -/
theorem doneEM_tailP (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true)
    (Np : NoEnt (S := S) (Map := Map) env p) (hcount : sixCount p ≤ 255) (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol)) :
    DoneEM (S := S) (Map := Map) lib N env P (n3 (A 2) fb fq) (Nomm.n2 p q (some (b, Option.none))) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  refine ⟨tailP_done lib hring hned hNf hNt Sp hpd hcount hq hAp hq1 hq2 b0 d0 hu hcl hcb hr, ?_⟩
  obtain ⟨sub, gA, o', gT, nexS, g5, ha, ht, hp, hc⟩ := runLCM_tailP hring hned hq hr
  rw [runLCM_true env hpd] at hp
  have eS : entries nexS.laz = [] := Np (goal := CGoal.next (lazyReg gA.re) (jmp0 o')) trivial hp
  have eL := eq_ofSure_of_entries eS
  unfold copyL at hc
  obtain ⟨o, g6, -, hc⟩ := bind_some hc
  obtain ⟨laz, g7, h7, hc⟩ := bind_some hc
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [eL, copyLazyL_ofSure] at h7
  obtain ⟨s, g8, -, h7⟩ := bind_some h7
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h7
  obtain ⟨rfl, rfl⟩ := h7
  exact entries_ofSure _

/-- **A branch of `DoneEM` meets `SixDWM` with the bound `0`.** -/
theorem sixDWM_of_doneEM {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : DoneEM (S := S) (Map := Map) lib N env P f nm) : SixDWM (S := S) (Map := Map) lib N env P f nm 0 :=
  fun b0 d0 hu hcl hcb hr =>
    ⟨⟨_, rfl, walkEq_refl _, (H b0 d0 hu hcl hcb hr).1.run⟩, by rw [(H b0 d0 hu hcl hcb hr).2]; exact Nat.le_refl _⟩

/-- **A branch without direct call**: `SixD` gives `SixDWM`. -/
theorem sixDWM_of_sixD {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} {k : Nat}
    (hd : nm.noDirect = true) (H : SixD (S := S) (Map := Map) lib N env P f nm k) :
    SixDWM (S := S) (Map := Map) lib N env P f nm k :=
  fun b0 d0 hu hcl hcb hr => by
    rw [runLCM_true env hd] at hr
    exact SixD.toW H b0 d0 hu hcl hcb hr

/-- **A test without direct call**: `PickD` gives `PickDM`. -/
theorem pickDM_of_pickD {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} {k : Nat}
    (hd : nm.noDirect = true) (H : PickD (S := S) (Map := Map) lib N env P f nm k) :
    PickDM (S := S) (Map := Map) lib N env P f nm k :=
  fun z o hz ho hj b0 d0 hu hcl hcb hr => by
    rw [runLCM_true env hd] at hr
    exact H z o hz ho hj b0 d0 hu hcl hcb hr

/-! ## Bell contracts from the tops -/

/-- **The n-ary bell contract from `RunOKGB` and the jump at no entry**
(`finishLFC_contractGBN` at the bell's subjects). -/
theorem finishLFC_bellContractGBN {lib : Lib} {env : CallEnv} {bl : Bell} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → RunOKGB lib N (SkaModel.Fits bl.less) bl.fol (CGoal.done : CGoal S) gen0 gE nex ∧
        nex.th.there ∉ (entries nex.laz).map Prod.fst)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) env nm ord cape bake = some c) : BellContract lib N bl false c := by
  intro s hs args hargs
  simp only [Bool.false_eq_true, if_false] at hargs
  rw [hbl] at hs
  have hca : CapeAxes cape s := fun axe h1 ha => capeAxes_of_fits axe h1 cape data s hn hs ha
  rw [← hbl] at hs
  exact finishLFC_contractGBN lib N hR hbake h s hs hca args hargs

/-- **The whole-subject bell contract from `SixDWM`'s premise**
(`finishLUCM_contractGBW` at the bell's subjects). -/
theorem finishLUCM_bellContractGBW {lib : Lib} {env : CallEnv} {bl : Bell} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLCM env true Option.none nm (CGoalL.done : CGoalL S) []
      (gen0 : Gen Map) = some (nex, gE) → ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEq (Map := Map) nex.laz nexU.laz ∧
        RunOKGB lib N (SkaModel.Fits bl.less) bl.fol (CGoal.done : CGoal S) gen0 gE nexU)
    {c : Straight Map} (h : finishLUCM (S := S) env nm = some c) : BellContract lib N bl true c := by
  have H := finishLUCM_contractGBW lib N hR h
  intro s hs args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-! ## The walker `L` -/

/-- The yes branch of `L`: the self call on `[L x.tail]`. -/
def yesLW : Nomm := Nomm.n2 (Nomm.cons (Nomm.n0 2) (Nomm.n0 7)) (Nomm.n0 2) (some (bellLW, Option.none))

theorem nommLW_eq : nommLW = Nomm.n6 (Nomm.n3 (Nomm.n0 3)) yesLW (Nomm.n0 3) := rfl
theorem nounLW_eq : nounLW = n4 (A 6) (n2 (A 3) (slot 3)) (n3 (A 2) (C (slot 2) (slot 7)) (slot 2)) (slot 3) := rfl

theorem slot_LW (lib : Lib) :
    ∀ x gul go t, minkStep lib gul go t (C nounLW x) (slot 2) = some (Tone.zero bellLW.fol) :=
  fun x gul go t => minkStep_axis2 lib gul go t nounLW x

theorem lokS_walkP (lib : Lib) {N : Needs} (env : CallEnv) (P : Noun → Prop) :
    LOKS (S := S) (Map := Map) false lib N env P (C (slot 2) (slot 7)) (Nomm.cons (Nomm.n0 2) (Nomm.n0 7)) :=
  ((lokS_callTreeA lib env (CallTreeA.cons (CallTreeA.n0 2) (CallTreeA.n0 7)) P).2 rfl).1

/-- **The yes branch of `L`, n-ary**: `DoneE` (`doneE_tailN`). -/
theorem doneE_yesLW (lib : Lib) {N : Needs} (hNf : N bellLW false = some walkNeed) :
    DoneE (S := S) (Map := Map) lib N envLW (SkaModel.Fits bellLW.less) (n3 (A 2) (C (slot 2) (slot 7)) (slot 2))
      yesLW :=
  doneE_tailN lib (by simp [envLW]) (by simp [envLW]) (fun _ => rfl) hNf (splitsLess_walk rfl)
    (lokS_walkP lib envLW _) (noEnt_pure envLW rfl rfl) (by decide) rfl (walk_hAp rfl)
    (qDirect_walk (slot_LW lib)).ret (qDirect_walk (slot_LW lib)).mink

/-- **The yes branch of `L`, whole-subject**: `DoneEM` (`doneEM_tailP`). -/
theorem doneEM_yesLW (lib : Lib) {N : Needs} {ndT : NeedOrd} (hNf : N bellLW false = some walkNeed)
    (hNt : N bellLW true = some ndT) :
    DoneEM (S := S) (Map := Map) lib N envLW (SkaModel.Fits bellLW.less) (n3 (A 2) (C (slot 2) (slot 7)) (slot 2))
      yesLW :=
  doneEM_tailP lib (by simp [envLW]) (by simp [envLW]) hNf hNt (lokS_walkP lib envLW _) rfl
    (noEnt_pure envLW rfl rfl) (by decide) rfl (walk_hAp rfl)
    (qDirect_walk (slot_LW lib)).ret (qDirect_walk (slot_LW lib)).mink

/-- **The n-ary bell contract of `L`.** -/
theorem bellContract_walkLN (lib : Lib) {N : Needs} (hNf : N bellLW false = some walkNeed) {c : Straight Map}
    (h : finishLFC (S := S) envLW nommLW walkNeed capeW (fun ned => (ned, [])) = some c) :
    BellContract lib N bellLW false c := by
  have H : SixDN (S := S) (Map := Map) lib N envLW (SkaModel.Fits bellLW.less) bellLW.fol nommLW (0 + 0 + 0 + 2) :=
    six_doneGBN (S := S) (Map := Map) lib envLW (P := SkaModel.Fits bellLW.less) (c := Nomm.n3 (Nomm.n0 3))
    rfl (pickD_three3 lib envLW _) (sixD_of_doneE (doneE_yesLW lib hNf)) (sixD_slot3 lib envLW _) (by decide)
  exact finishLFC_bellContractGBN N (fun hr =>
    ⟨(H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1,
      (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).2.2⟩) rfl capeNorm_W (fun _ => rfl) h

/-- **The whole-subject bell contract of `L`.** -/
theorem bellContract_walkLW (lib : Lib) {N : Needs} {ndT : NeedOrd} (hNf : N bellLW false = some walkNeed)
    (hNt : N bellLW true = some ndT) {c : Straight Map} (h : finishLUCM (S := S) envLW nommLW = some c) :
    BellContract lib N bellLW true c := by
  have H : SixDWM (S := S) (Map := Map) lib N envLW (SkaModel.Fits bellLW.less) bellLW.fol nommLW (0 + 0 + 0 + 4) :=
    six_doneGBWM (S := S) (Map := Map) lib envLW (P := SkaModel.Fits bellLW.less) (c := Nomm.n3 (Nomm.n0 3))
    (pickDM_of_pickD rfl (pickD_three3 lib envLW _)) (sixDWM_of_doneEM (doneEM_yesLW lib hNf hNt))
    (sixDWM_of_sixD rfl (sixD_slot3 lib envLW _)) (by decide)
  exact finishLUCM_bellContractGBW N (fun hr => (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) h

/-- **The table of `L`'s two entries meets its contracts**, given only that
the n-ary entry's need is the need read (`NeedsRead`). -/
theorem tableOK_walkL (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envLW nommLW walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envLW nommLW = some cW) (hR : NeedsRead envLW (table2 bellLW cN cW) bellLW) :
    TableOK lib (table2 bellLW cN cW) := by
  obtain ⟨cN', cW', h1, -, h3⟩ := hR
  simp only [table2, if_true, Bool.false_eq_true, if_false, Option.some.injEq] at h1
  subst h1
  have hn : cN.need = walkNeed := by simp [envLW] at h3; exact h3.symm
  have hNf : Table.needs (table2 bellLW cN cW) bellLW false = some walkNeed := by
    rw [(table2_needs bellLW cN cW).1, hn]
  intro b m c hc
  simp only [table2] at hc
  split at hc
  · rename_i e; subst e
    cases m with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc; subst hc
      exact bellContract_walkLN lib hNf hN
    | true =>
      simp only [if_true, Option.some.injEq] at hc; subst hc
      exact bellContract_walkLW lib hNf (table2_needs bellLW cN cW).2 hW
  · cases hc

/-- **`+mink` on `L` returns the atom that ends `x`**, on every `[L x]`: by
induction on `x`, `[3 [0 3]]` picks the no branch `[0 3]` on an atom and the
self call on `[L x.tail]` on a cell. -/
theorem mink_walkL (lib : Lib) (gul : Noun) :
    ∀ x, Mink lib gul [] (C nounLW x) nounLW (Tone.zero (lastAtom x))
  | Noun.atom a => ⟨3, by simp [nounLW, minkF_succ_eq, minkStep, lastAtom, slot, slot?, axisPath, axisPathFuel,
      slotAtPath, tbind, wut, n2, n3, n4]⟩
  | Noun.cell h t => by
    have IH := mink_walkL lib gul t
    have ht : Mink lib gul [] (C nounLW (C h t)) (n2 (A 3) (slot 3)) (Tone.zero (A 0)) :=
      ⟨2, by simp [minkF_succ_eq, minkStep, slot, slot?, axisPath, axisPathFuel, slotAtPath, tbind, wut, n2]⟩
    have h1 : Mink lib gul [] (C nounLW (C h t)) (C (slot 2) (slot 7)) (Tone.zero (C nounLW t)) :=
      ⟨2, by simp [minkF_succ_eq, minkStep, slot, slot?, axisPath, axisPathFuel, slotAtPath, tbind]⟩
    have h2 : Mink lib gul [] (C nounLW (C h t)) (slot 2) (Tone.zero nounLW) :=
      ⟨1, by rw [minkF_succ_eq, minkStep_axis2]⟩
    have hy := mink_n2_of h1 h2 IH
    rw [nounLW_eq] at hy ⊢
    exact (mink_sixC_bwd (fc := n3 (A 2) (C (slot 2) (slot 7)) (slot 2)) (fd := slot 3) ht).2.1 _ rfl hy

/-- **The walker `L`, closed, with a product**: on every subject `[L x]`,
each of `L`'s two entries, run on the table of its entries, answers at some
number of levels, every answer it gives at any number of levels stands for
the atom that ends `x`, and so does the one it gives.  The only hypothesis is
`NeedsRead` of `L`. -/
theorem closed_walkL (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envLW nommLW walkNeed capeW (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envLW nommLW = some cW) (hR : NeedsRead envLW (table2 bellLW cN cW) bellLW)
    (m : Bool) (x gul : Noun) {args : List Noun}
    (ha : (if m then some [C nounLW x] else SkaModel.split cN.need (C nounLW x)) = some args) :
    (∃ k ton, execEntry lib (tableOracle lib (table2 bellLW cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) ∧ ToneRel lib (Table.needs (table2 bellLW cN cW)) ton (Tone.zero (lastAtom x))) ∧
    (∀ k ton, execEntry lib (tableOracle lib (table2 bellLW cN cW) k) () (if m then cW else cN) args [] gul =
        some (ton, ()) → ToneRel lib (Table.needs (table2 bellLW cN cW)) ton (Tone.zero (lastAtom x))) := by
  have hc : table2 bellLW cN cW bellLW m = some (if m then cW else cN) := by cases m <;> simp [table2]
  have ha' : (if m then some [C nounLW x] else SkaModel.split (if m then cW else cN).need (C nounLW x)) =
      some args := by cases m <;> simpa using ha
  have H := closed_entry lib (tableOK_walkL lib hN hW hR) hc (walk_fits nounLW x) ha' gul
  obtain ⟨n, hn⟩ := mink_walkL lib gul x
  refine ⟨?_, fun k ton he => ?_⟩
  · obtain ⟨ton, he, hrel⟩ := H.1 n _ hn
    exact ⟨n, ton, he, hrel⟩
  · obtain ⟨r, hr, hrel⟩ := H.2 k ton he
    rw [Mink.det hr ⟨n, hn⟩] at hrel
    exact hrel

end Comp
end SkaModel
end Formalization
