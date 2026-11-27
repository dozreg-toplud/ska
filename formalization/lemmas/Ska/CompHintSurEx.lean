import lemmas.Ska.CompHintSur
import lemmas.Ska.CompHintRegKeepEx

/-!
# `[7 p q]` with a kept `p`: the dumped `d13` (README Gaps 24.19)

* `d13` `[7 [11 [%spot [1 0]] [[0 2] [0 3]]] [4 [0 2]]]`: the spot is the
  `p` of the `%7`, under the need of `[4 [0 2]]` (a cell whose head goes to
  a register), which `+sound` of the cons meets; `contract_d13`
  (`finishLUCH_contractSurSeven`, `surGBT_n11dKept` over the cons).
* `runLCH_n4n0_done`: the result of `[4 [0 a]]` under `%done` is the flat
  `+from` of `a` over a register.
* `regGBT_sevenS`: `[7 p q]` under `%next (lazy-from-reg r)` with `p` in
  `SurGBT`, `q` in `RegFT`, so `[spot [7 [spot k] q]]` nests.
* `outReasonSur`, the table of the 39 at the top (`#guard`: 18 in).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

def exD13K : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 0)) (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (C (slot 2) (slot 3))
def exD13KF : Noun := n3 (A 11) (C (A tagSpot) (quote (A 0))) (C (slot 2) (slot 3))
def exD13 : Nomm := Nomm.n7 exD13K (Nomm.n4 (Nomm.n0 2))
def exD13F : Noun := n3 (A 7) exD13KF (n2 (A 4) (slot 2))

#guard dumped "d13" == some (exD13.toNoun, exD13F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD13).isSome
#guard sndH (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (NeedOrd.pair NeedOrd.this NeedOrd.none)

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem setRun_emptyS (f : Nat → Nat) : setRun f (HoonSet.empty : S) = HoonSet.empty := by
  simp [setRun, toList_emptyR]

/-- **The run of `[4 [0 a]]` under `%done`**: its need is `+from` of `a`
over the register of the operand, flat, the lock empty. -/
theorem runLCH_n4n0_done {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {sup : Option Nomm} {region : List Nat}
    {g0 g1 : Gen Map} {nx : NextL S} {a : Nat} (ha : 2 ≤ a)
    (hr : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n4 (Nomm.n0 a)) CGoalL.done region g0 = some (nx, g1)) :
    ∃ r, nx.laz = ofSure ⟨fromPath (Need.this r) a, HoonSet.empty⟩ := by
  have a0 : a ≠ 0 := by omega
  have a1 : a ≠ 1 := by omega
  simp only [runLCH, a0, a1, if_false, bind_apply, Option.bind_some, re_apply, emit_apply, simpleNextL, pure_apply, fromL, ofSure,
    lazyReg, List.isEmpty_nil, Bool.and_self, if_true, fromSure] at hr
  simp only [reduceCtorEq, if_false, Option.map_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  exact ⟨g0.re + 1, by simp only [setRun_emptyS]⟩

theorem fromPath_two (r : Nat) : fromPath (Need.this r) 2 = Need.pair (Need.this r) Need.none := by
  rw [fromPath]; simp only [show ¬ (2 ≤ 1) by omega, dite_false, show cap 2 = 2 by simp [cap], if_true,
    show mas 2 = 1 by simp [mas]]
  rw [fromPath]; simp

/-- The products of `[[0 2] [0 3]]` are cells. -/
theorem fitP_cons23 (lib : Lib) (env : CallEnv) (P : Noun → Prop) {sur : Sure S}
    (hf : ∀ a b, FitsS sur (C a b)) : FitP lib P (C (slot 2) (slot 3)) sur := by
  intro s hs gul tm p hm
  have M : MinkEq lib P (C (slot 2) (slot 3)) (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) :=
    ((CallTree.cons (CallTree.n0 2) (CallTree.n0 3)).kind lib env.cod P).elim (fun h => h.2)
      (fun h => by simp [hinted, orB] at h)
  have e := (M s hs gul tm _).1 hm
  simp only [pureEval] at e
  cases h2 : slot? 2 s with
  | none => rw [h2] at e; cases e
  | some x =>
    cases h3 : slot? 3 s with
    | none => rw [h2, h3] at e; cases e
    | some y =>
      rw [h2, h3] at e
      simp only [Option.bind_some, toneOf, Tone.zero.injEq] at e
      subst e; exact hf x y

/-- **The contract at the top of the dumped `d13`**,
`[7 [11 [%spot [1 0]] [[0 2] [0 3]]] [4 [0 2]]]`: the kept spot as the `p`
of a `%7`, under the need of `[4 [0 2]]`, for any `snd` with `+sound` of the
cons at that need (`sndH` has it, `#guard`). -/
theorem contract_d13 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (NeedOrd.pair NeedOrd.this NeedOrd.none) = true)
    (hc : finishLUCH (S := S) env snd exD13 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD13F [s] c ∧ ContractBwd lib N s exD13F [s] c := by
  have Hc : CallTreeHU lib env N (fun _ => True) _ (C (slot 2) (slot 3)) (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) :=
    CallTreeHU.cons (CallTreeHU.base (CallTreeD.n0 2) rfl) (CallTreeHU.base (CallTreeD.n0 3) rfl)
  have RC : SurGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (fun _ => True) (C (slot 2) (slot 3))
      (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) :=
    SurGBT.of_loksf (fun _ => True) (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env Hc).1.1 (by decide)
  have RK : SurGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (fun sur => (fun _ => True) sur ∧
      SoundK snd (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) sur ∧ FitP lib (fun _ => True) (C (slot 2) (slot 3)) sur)
      exD13KF exD13K := surGBT_n11dKept RC (clueLOKS_n1 lib env _ (A 0)) (by simp [sixCount]) (noBondH_n1 (A 0)) spot_dynamic
    spot_stop (C (slot 2) (slot 3))
  have Hq : DoneAllT (S := S) (Map := Map) lib N env snd (Img lib (fun _ => True) exD13KF) (n2 (A 4) (slot 2))
      (Nomm.n4 (Nomm.n0 2)) :=
    doneAllT_callTreeHU lib env (CallTreeHU.four (b1 := true) (CallTreeHU.base (CallTreeD.n0 2) rfl))
  have H := finishLUCH_contractSurSeven (S := S) (snd := snd) (N := N) lib RK Hq (fun hr => by
    obtain ⟨r, e⟩ := runLCH_n4n0_done (by decide) hr
    rw [e]
    refine ⟨entries_ofSure _, trivial, ⟨?_, ?_⟩, fitP_cons23 lib env _ fun a b => ⟨?_, looks_empty _⟩⟩
    · simp [ofSure]; exact (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x)
    · simp only [ofSure, fromPath_two]; exact hsnd
    · simp only [ofSure, fromPath_two, Fits]; exact ⟨trivial, trivial⟩) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **`[7 p q]` under `%next (lazy-from-reg r) th` with `p` in `SurGBT Ap`**
(a kept hint, nested in any way `surGBT_n11dKept` allows): `q` in `RegFT`,
its result without entries and with `Ap` of its sure need (`hq`).  So a
kept spot whose formula is such a `%7` is in `RegGBT` (`regGBT_n11dKept`):
the shape `[spot [7 [spot k] q]]` of a `!:` arm's step. -/
theorem regGBT_sevenS (lib : Lib) {snd : Nomm → NeedOrd → Bool} {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {b c : Noun} {p q : Nomm} {Ap : Sure S → Prop} (Hp : SurGBT (S := S) (Map := Map) snd lib N env P Ap b p)
    (Hq : RegFT (S := S) (Map := Map) snd lib N env (Img lib P b) c q)
    (hq : ∀ {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLCH (S := S) (Map := Map) env snd true sup q (CGoalL.next (ofSure (lazyReg rg)) th) region g0 =
        some (nx, g1) → entries nx.laz = [] ∧ Ap nx.laz.sure) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 7) b c) (Nomm.n7 p q) := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 h1
  have Rq := D.run
  obtain ⟨hne, hA⟩ := hq h1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · simp only [GoalJ] at e; rw [e]; exact hta
  have h2' : runLCH (S := S) (Map := Map) env snd true sup p (CGoalL.next (ofSure nx.laz.sure) nx.th) region ga =
      some (nex, g1) := by
    rw [← eq_ofSure_of_entries hne]; exact h2
  have Rp := Hp hA (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow)
    (Rq.cfr.below hcb) Rq.lo Rq.hi hj Rq.dist D.clean
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · have := Rq.ext.1; simp only [GMem, lazyReg, NMem] at e; omega
      · exact e.2, Rq.ncond x hx⟩) h2'
  exact runOKGBT_sevenG (minkC7_seven lib P b c) Rq hne Rp
    (fun r hr => by simp only [GMem, lazyReg, NMem] at hr; omega)

/-! ## The table of the 39 at the top -/

/-- `outReasonOps` with `d13` in (`contract_d13`; the only dumped `%7`
whose `p` is kept and whose `+sound` holds, `d12`'s fails). -/
def outReasonSur (nm : Nomm) : Option String :=
  if nm.toNoun == exD13.toNoun then Option.none else outReasonOps nm

def reasonsSur : List (String × Option String) :=
  HintData.all.map fun (n, j) => (n, ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).bind outReasonSur)

#guard (reasonsSur.filter fun r => r.2.isNone).map Prod.fst ==
  ["s01", "s02", "s03", "s05", "s06", "d01", "d02", "d03", "d06", "d08", "d09", "d10", "d13", "d14", "d19", "d21",
    "d23", "m01"]

end

end Comp
end SkaModel
end Formalization
