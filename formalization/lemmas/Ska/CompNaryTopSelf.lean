import lemmas.Ska.CompNaryTopDirect

/-!
# A self-calling bell, closed

README Gaps 18.15, step 4.  `L = [2 [0 1] [0 2]]` on a subject whose head is
`L` itself calls itself on its own subject: `+mink` never returns
(`minkF_L`).  The analysis turns it into the nomm `[2 [0 1] [0 2] [L-bell
~]]` (`nommL`), a direct call of its own bell with no `%6` and no `%10`.
Both entries of `L-bell` meet their contracts with no hypothesis on any
callee: the n-ary entry by `finishLFC_contractTailN` (the direct call
compiled by `callL`, `SplitsLess` holding since every noun that fits `[&
|]` is a cell), the whole-subject entry by `finishLUCM_contractTailP`.  So
the table of the two entries meets `TableOK`, and `closed_selfCall` says that
on that table neither entry gives any answer at any number of levels, on
every subject of the bell: a closed statement about a recursive bell, its
recursion run by the table's oracle.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `L = [2 [0 1] [0 2]]`. -/
def nounL : Noun := n3 (A 2) (slot 1) (slot 2)

/-- The bell of `L` on subjects `[L *]`. -/
def bellL : Bell := ⟨Sock.mk (Cape.cell Cape.yes Cape.no) (C nounL (A 0)), nounL⟩

/-- `L-bell` needs `[~ this]`, is impure, no jet, hinted, not soft. -/
def envL : CallEnv :=
  ⟨fun b => if b = bellL then some (NeedOrd.pair NeedOrd.none NeedOrd.this) else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false,
   fun _ _ _ _ _ => false⟩

/-- The nomm of `L`: `[2 [0 1] [0 2] [L-bell ~]]`. -/
def nommL : Nomm := Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) (some (bellL, Option.none))

theorem minkStep_axis2 (lib : Lib) (gul : Noun) (go : Trace → Noun → Noun → Option Tone) (t : Trace) (h tl : Noun) :
    minkStep lib gul go t (C h tl) (C (A 0) (A 2)) = some (Tone.zero h) := by
  simp [minkStep, slot?, axisPath, axisPathFuel, slotAtPath]

/-- **`+mink` on `L` never returns** on a subject whose head is `L`. -/
theorem minkF_L (lib : Lib) (gul : Noun) : ∀ (n : Nat) (tm : Trace) (x : Noun),
    minkF lib gul n tm (C nounL x) nounL = Option.none
  | 0, _, _ => by simp [minkF]
  | 1, tm, x => by
    rw [minkF_succ_eq]
    simp [nounL, n3, slot, minkStep_two, minkF]
  | m + 2, tm, x => by
    rw [minkF_succ_eq]
    simp only [nounL, n3, slot, minkStep_two, minkF_succ_eq, minkStep_axis1, minkStep_axis2, tbind_zero]
    exact minkF_L lib gul (m + 1) tm x

theorem fits_bellL {s : Noun} (h : SkaModel.Fits bellL.less s) : ∃ x, s = C nounL x := by
  simp only [bellL, SkaModel.Fits, FitsCape] at h
  rcases h with h | ⟨dh, dt, nh, nt, e1, rfl, h1, -⟩
  · simp [Cape.isNo] at h
  · simp only [Noun.cell.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    exact ⟨nt, by rw [h1]⟩

theorem splitsLess_bellL : SplitsLess bellL (NeedOrd.pair NeedOrd.none NeedOrd.this) := fun s hs => by
  obtain ⟨x, rfl⟩ := fits_bellL hs
  exact ⟨[x], rfl⟩

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The table of `L-bell` meets its contracts**, given only that the need
the n-ary entry has is the need `+callee-need` read (`[~ this]`). -/
theorem tableOK_selfCall (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envL nommL (NeedOrd.pair NeedOrd.none NeedOrd.this) (Cape.cell Cape.yes Cape.no)
      (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envL nommL = some cW)
    (hneed : cN.need = NeedOrd.pair NeedOrd.none NeedOrd.this) :
    TableOK lib (table2 bellL cN cW) := by
  have hT := table2_needs bellL cN cW
  have hned : envL.need bellL = some cN.need := by rw [hneed]; simp [envL]
  have Sp := ((lokS_callTreeA (S := S) (Map := Map) lib (N := Table.needs (table2 bellL cN cW)) envL
    (CallTreeA.n0 1) (SkaModel.Fits bellL.less)).2 rfl).1
  have hAp : ∀ x gul y, SkaModel.Fits bellL.less x → Mink lib gul [] x (slot 1) (Tone.zero y) →
      SkaModel.Fits bellL.less y := fun x gul y hx hm => by rw [mink_slot1 hm]; exact hx
  have hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, SkaModel.Fits bellL.less s →
      minkF lib gul n tm s (slot 2) = some rc → rc = Tone.zero bellL.fol := by
    intro s gul n tm rc hs hm
    obtain ⟨x, rfl⟩ := fits_bellL hs
    cases n with
    | zero => simp [minkF] at hm
    | succ n =>
      rw [minkF_succ_eq] at hm
      simp only [slot, minkStep_axis2, Option.some.injEq] at hm
      exact hm.symm
  have hq2 : ∀ {s gul : Noun} {tm : Trace}, SkaModel.Fits bellL.less s → Mink lib gul tm s (slot 2) (Tone.zero bellL.fol) :=
    fun {s gul tm} hs => by
      obtain ⟨x, rfl⟩ := fits_bellL hs
      exact ⟨1, by rw [minkF_succ_eq]; simp only [slot, minkStep_axis2]; rfl⟩
  intro b m c hc
  simp only [table2] at hc
  split at hc
  · rename_i e
    subst e
    cases m with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hc
      subst hc
      intro s hs args hargs
      simp only [Bool.false_eq_true, if_false] at hargs
      have hca : CapeAxes (Cape.cell Cape.yes Cape.no) s := fun axe h1 ha =>
        capeAxes_of_fits axe h1 _ _ s (by simp [CapeNorm, Cape.isNo]) hs ha
      exact finishLFC_contractTailN lib rfl hned (fun _ => rfl) hT.1 (by rw [hneed]; exact splitsLess_bellL) Sp
        (by simp [sixCount]) rfl hAp hq1 hq2 hN s hs hca args hargs
    | true =>
      simp only [if_true, Option.some.injEq] at hc
      subst hc
      intro s hs args hargs
      simp only [if_true, Option.some.injEq] at hargs
      subst hargs
      exact (finishLUCM_contractTailP lib rfl hned hT.1 hT.2 Sp rfl (by simp [sixCount]) rfl hAp hq1 hq2 hW).2 s hs
  · simp at hc

/-- **A closed theorem for a self-calling bell**: on the table of `L-bell`'s
two entries, neither the whole-subject entry nor the n-ary entry gives any
answer, at any number of levels of the table's oracle, on every subject of
the bell, as `+mink` gives none.  The only hypothesis left is that the need of
the n-ary entry is the need read. -/
theorem closed_selfCall (lib : Lib) {cN cW : Straight Map}
    (hN : finishLFC (S := S) envL nommL (NeedOrd.pair NeedOrd.none NeedOrd.this) (Cape.cell Cape.yes Cape.no)
      (fun ned => (ned, [])) = some cN)
    (hW : finishLUCM (S := S) envL nommL = some cW)
    (hneed : cN.need = NeedOrd.pair NeedOrd.none NeedOrd.this)
    {s : Noun} (hs : SkaModel.Fits bellL.less s) (k : Nat) (gul : Noun) (ton : Tone) :
    execEntry lib (tableOracle lib (table2 bellL cN cW) k) () cW [s] [] gul ≠ some (ton, ()) ∧
      ∀ args, SkaModel.split cN.need s = some args →
        execEntry lib (tableOracle lib (table2 bellL cN cW) k) () cN args [] gul ≠ some (ton, ()) := by
  have hT := tableOK_selfCall (S := S) lib hN hW hneed
  obtain ⟨x, rfl⟩ := fits_bellL hs
  have nm : ∀ r, ¬ Mink lib gul [] (C nounL x) nounL r := fun r ⟨n, hn⟩ => by rw [minkF_L] at hn; cases hn
  have cW' := hT bellL true cW (by simp [table2])
  have cN' := hT bellL false cN (by simp [table2])
  refine ⟨fun h => ?_, fun args hargs h => ?_⟩
  · obtain ⟨F, B⟩ := cW' _ hs [C nounL x] (by simp)
    obtain ⟨r, hr, -⟩ := (table_closed lib hT (Needs.le_refl _) F B gul).2 k ton h
    exact nm r hr
  · obtain ⟨F, B⟩ := cN' _ hs args (by simpa using hargs)
    obtain ⟨r, hr, -⟩ := (table_closed lib hT (Needs.le_refl _) F B gul).2 k ton h
    exact nm r hr

end

/-! ## The real codes -/

/-- The n-ary entry of `L-bell`. -/
def lN : Option (Straight FM) :=
  finishLFC (S := LS) envL nommL (NeedOrd.pair NeedOrd.none NeedOrd.this) (Cape.cell Cape.yes Cape.no)
    (fun ned => (ned, []))

/-- The whole-subject entry of `L-bell`. -/
def lW : Option (Straight FM) := finishLUCM (S := LS) envL nommL

/-- Both entries on the table with `k` levels give no answer. -/
def lRun (k : Nat) (s : Noun) : Bool :=
  match lN, lW with
  | some cN, some cW =>
    (execEntry libT (tableOracle libT (table2 bellL cN cW) k) () cW [s] [] (A 0)).isNone &&
      match SkaModel.split cN.need s with
      | some args => (execEntry libT (tableOracle libT (table2 bellL cN cW) k) () cN args [] (A 0)).isNone
      | Option.none => false
  | _, _ => false

-- the codes exist, the need is the one read (`hneed`), and neither entry answers, as `+mink` does not
#guard lN.map (·.need) == some (NeedOrd.pair NeedOrd.none NeedOrd.this)
#guard lW.isSome
#guard lRun 3 (C nounL (A 7))
#guard lRun 12 (C nounL (C (A 1) (A 2)))
#guard (minkF libT (A 0) 300 [] (C nounL (A 7)) nounL).isNone

end Comp
end SkaModel
end Formalization
