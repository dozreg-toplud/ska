import lemmas.Ska.CompGenConsE
import lemmas.Ska.RawInvCLLabCopy
import lemmas.Ska.RawInvCLCopyIL

/-!
# The cons of two leaves: the shared statements of the assembly

README Gaps 12.39, item 11.  The run of `[[0 a] [0 b]]` under `%next L th`
with every state and fact named (`ConsAt`, `consAt_of_run`: `ConsSt` with
the halves, the labels of every entry list and the copy's run kept), and the
per-label semantics of `+copy` that the assembly reads (`CopyRunAt`, proved
from `CopyOKL` in `CompGenConsG.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+copy` at one label, in the needs of the entries** (what `CopyOKL`
gives at each label, `CopyOKL.runAt`): where the needs of both inputs at
the label are clean, distinct, below the start and pairwise apart, the
merged needs fit iff both sides do, are distinct, take their registers from
the inputs' or fresh ones, are apart on old registers, and the ops build both
sides' needs from the merged ones. -/
def CopyRunAt (g g' : Gen Map) (fs ss rs : List (Nat × Lazy S)) : Prop :=
  ∃ P : Nat → List Pole, Pref g g' P ∧ (∀ k, k ∉ (fs ++ ss).map Prod.fst → P k = []) ∧ ∀ k,
    (∀ F ∈ atL fs k ++ atL ss k, Clean F.ned ∧ Distinct F.ned ∧ ∀ y, NMem F.ned y → y < g.re) →
    (atL fs k ++ atL ss k).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) →
    (∀ z, (∀ M ∈ atL rs k, FitsS M z) ↔ (∀ F ∈ atL fs k, FitsS F z) ∧ (∀ T ∈ atL ss k, FitsS T z)) ∧
    (∀ M ∈ atL rs k, Distinct M.ned ∧ ∀ y, NMem M.ned y →
      (∃ F ∈ atL fs k ++ atL ss k, NMem F.ned y) ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (atL rs k).Pairwise (fun M M' => ∀ r, r < g.re → NMem M.ned r → ¬ NMem M'.ned r) ∧
    RegsIn (fun x => (∃ F ∈ atL fs k ++ atL ss k, NMem F.ned x) ∨ (g.re ≤ x ∧ x < g'.re)) (P k) ∧
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (z : Noun), (∀ M ∈ atL rs k, HoldsN M.ned R z) →
      ∃ R', Runs lib O c gul st' t (P k) R R' ∧ (∀ F ∈ atL fs k ++ atL ss k, HoldsN F.ned R' z) ∧
        ∀ y, (∀ F ∈ atL fs k ++ atL ss k, ¬ NMem F.ned y) → SkaModel.read y R' = SkaModel.read y R

/-- **The run of the cons of two leaves, every state named**: `gE` (the
split's block emitted), `gS` (after the split), `gC` (the copy's block
emitted), `g1`; the halves `hed`, `tel` and their moves `hed'`, `tel'`. -/
structure ConsAt (L : Lazy S) (th : Jmp) (a b : Nat) (g0 g1 : Gen Map) (nex : NextL S)
    (hed tel hed' tel' : Lazy S) (gS : Gen Map) : Prop where
  f1 : fromL b tel = some tel'
  f2 : fromL a hed = some hed'
  eo : HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks g0.bo = some ⟨[], [], Termin.hop th⟩
  sp : SplitOKD (g0.emitted ⟨[], [], Termin.hop th⟩) gS ((g0.bo, L) :: entries L) ((g0.bo, hed) :: entries hed)
    ((g0.bo, tel) :: entries tel)
  luh : Raw.LabUniq hed'
  lut : Raw.LabUniq tel'
  eth : nex.th = jmp0 gS.bo
  boS : gS.bo = g0.bo + 1
  eC : HoonMap.get (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).blocks gS.bo =
    some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩
  dS : gS.drop = false
  cp : CopyOKL (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 ((gS.bo, hed') :: entries hed')
    ((gS.bo, tel') :: entries tel') ((gS.bo, nex.laz) :: entries nex.laz)
  hc : copyLazyL gS.bo hed' tel' (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) = some (nex.laz, g1)
  labH : ∀ e ∈ entries hed, e.1 ∈ (entries L).map Prod.fst
  labT : ∀ e ∈ entries tel, e.1 ∈ (entries L).map Prod.fst
  labH' : ∀ e ∈ entries hed', e.1 ∈ (entries L).map Prod.fst
  labT' : ∀ e ∈ entries tel', e.1 ∈ (entries L).map Prod.fst
  labN : ∀ e ∈ entries nex.laz, e.1 ∈ (entries L).map Prod.fst
  grow : GrowU g0 g1
  norep : ∀ k ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 k
  bo : g1.bo = g0.bo + 2
  reS : g0.re ≤ gS.re
  reC : gS.re ≤ g1.re
  drop : g1.drop = g0.drop
  condS : gS.cond = g0.cond
  cond : g1.cond = g0.cond

theorem consAt_of_run (env : CallEnv) (sup : Option Nomm) {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (G : GoalG (Map := Map) L th g0) (lu : Raw.LabUniq L) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runLC env sup (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ∃ (hed tel hed' tel' : Lazy S) (gS : Gen Map), ConsAt L th a b g0 g1 nex hed tel hed' tel' gS := by
  have CS := consSt_of_run env sup ha hb G lu d0 hu h
  obtain ⟨hed, tel, hed', tel', o, gS, hs, hf1, hf2, hcp⟩ := runLC_cons00_apart env sup ha hb h
  obtain ⟨rfl, eo, WS⟩ := splitL_okD hs d0 (fun e he => by
    obtain ⟨_, hlt, B, th', hb'⟩ := G.lab e he
    exact ⟨hlt, B, _, hb'⟩)
  obtain ⟨eth, hc⟩ := copyL_apart hcp
  obtain ⟨luh, lut, qh, qt⟩ := Raw.lab_splitL (Q := fun o => o ∈ (entries L).map Prod.fst) hs lu
    (fun e he => List.mem_map_of_mem he)
  obtain ⟨luh', qh'⟩ := Raw.lab_fromL hf2 luh qh
  obtain ⟨lut', qt'⟩ := Raw.lab_fromL hf1 lut qt
  obtain ⟨-, qn⟩ := Raw.lab_copyL (Q := fun o => o ∈ (entries L).map Prod.fst) hcp luh' lut' qh' qt'
  have dE : (g0.emitted ⟨[], [], Termin.hop th⟩).drop = false := d0
  have WS0 := WS
  obtain ⟨PS, PPS, -, -⟩ := WS0
  have dS : gS.drop = false := PPS.drop.trans dE
  have WC := copyLazyL_okL gS.bo hed' tel' _ g1 nex.laz hc dS luh' lut'
  have WC0 := WC
  obtain ⟨PC, PPC, -, -⟩ := WC0
  have eC := emitted_get gS ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ dS
  refine ⟨hed, tel, hed', tel', gS, hf1, hf2, eo, WS, luh', lut', eth, PPS.bo, eC, dS, WC, hc, qh, qt, qh', qt',
    qn, CS.grow, CS.norep, CS.bo, ?_, ?_, CS.drop, ?_, CS.cond⟩
  · have := PPS.re; simp only [emitted_re] at *; omega
  · have := PPC.re; simp only [emitted_re] at *; omega
  · rw [PPS.cond]; rfl

end Comp
end SkaModel
end Formalization
