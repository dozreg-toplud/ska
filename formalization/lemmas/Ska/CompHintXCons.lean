import lemmas.Ska.CompHintWSound

/-!
# The cons with a hinted part: the run apart (README Gaps 24.24)

What a cons `[p q]` does under the goal of `RegGBT`, `%next (lazy-from-reg
rg) th`, when one part is hinted (the goal-kind facts of a cons rule for
`hcX`, checked by proof here):

* `doneNext_cons`: under `%done` a cons is the block `[don re]`, then the
  run under `%next (lazy-from-reg re)` (so `DoneG` of a cons follows from its
  `RegGBT`, `doneG_of_next`);
* `splitL_lazyReg`: `+split` of `lazy-from-reg rg` is the block `[con h t rg]
  hop th` at `g.bo` and the two fresh registers `h = re`, `t = re + 1`, each
  `lazy-from-reg`: so each part runs under a goal of `RegGBT`'s form;
* `runLCH_consA_next` (head hinted, tail not: `m24`, `m31`): the tail runs
  under `%next (lazy-from-reg t) (jmp0 o)`, `+past` parks its result in a
  bond, the head runs under `%next (lazy-from-reg h) th2` (a goal of
  `RegGBT`), then `+copy`;
* `runLCH_consB_next` (tail hinted, head not: `m25`): `+past` parks the
  head's need `lazy-from-reg h` behind a block, the tail runs under
  `%next (lazy-from-reg t) (jmp0 o1)` (a goal of `RegGBT`), the head under the
  bond, then `+copy`.

What is missing for the rule itself is `RunOKGBT` of the result: for `A`, a
`+copy` of a first result WITH bonds (the head's, from `RegGBT`) into one
bond (the tail's, behind `+past`), where `copyL_bond1` asks the first to have
none; for `B`, the head (a leaf) run under a goal with a bond, which
`LOKSFH` covers only for flat lazies.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {snd : Nomm → NeedOrd → Bool}

/-- **A cons under `%done` is the block `[don re]`, then the run under
`%next (lazy-from-reg re)`.** -/
theorem doneNext_cons (env : CallEnv) (p q : Nomm) : DoneNext (S := S) (Map := Map) env snd (Nomm.cons p q) :=
  fun sup region g0 => runLCH_done_next env sup (Or.inl ⟨p, q, rfl⟩) region g0

/-- **`DoneG` of a cons from its `RegGBT`.** -/
theorem doneG_consOfReg {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {p q : Nomm}
    (H : RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.cons p q)) :
    DoneG (S := S) (Map := Map) lib N env snd P f (Nomm.cons p q) :=
  doneG_of_next H (doneNext_cons env p q)

theorem splitLok_emptyX : splitLok (HoonSet.empty : S) = some (HoonSet.empty, HoonSet.empty) := by
  simp [splitLok, toList_emptyR]

/-- **`+split` of `lazy-from-reg rg`**: the block `[con h t rg] hop th` at
`g.bo`, the fresh registers `h = g.re`, `t = g.re + 1`, each part
`lazy-from-reg`. -/
theorem splitL_lazyReg {rg : Nat} {th : Jmp} {g g' : Gen Map} {hed tel : Lazy S} {o : Nat} (hd : g.drop = false)
    (h : splitL (⟨ofSure (lazyReg rg), th⟩ : NextL S) g = some ((hed, tel, o), g')) :
    o = g.bo ∧ hed = ofSure (lazyReg g.re) ∧ tel = ofSure (lazyReg (g.re + 1)) ∧ g'.re = g.re + 2 ∧
      g'.bo = g.bo + 1 ∧ g'.drop = false ∧ g'.cond = g.cond ∧ g'.tags = g.tags ∧
      HoonMap.get g'.blocks g.bo = some ⟨[], [Pole.con g.re (g.re + 1) rg], Termin.hop th⟩ ∧
      ∀ k, k ≠ g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k := by
  unfold splitL at h
  obtain ⟨o', g1, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨h', t'⟩, g2, hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  rw [splitLoop_ofSure] at hl
  obtain ⟨⟨sh, st⟩, g3, h3, h4⟩ := bind_some hl
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  unfold splitSure at h3
  simp only [lazyReg, splitLok_emptyX, Option.bind_some, splitNeed] at h3
  obtain ⟨⟨⟨nh, nt⟩, g4⟩, h5, h6⟩ := Option.map_eq_some_iff.mp h3
  simp only [Prod.mk.injEq] at h6
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h6
  obtain ⟨r1, g5, e1, h5⟩ := bind_some h5
  rw [re_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨r2, g6, e2, h5⟩ := bind_some h5
  rw [re_apply] at e2
  simp only [Option.some.injEq, Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  obtain ⟨u, g7, e3, h5⟩ := bind_some h5
  simp only [pure_apply, Option.some.injEq] at h5
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h5
  have d1 : ({ ({ (g.emitted ⟨[], [], Termin.hop th⟩) with re := (g.emitted ⟨[], [], Termin.hop th⟩).re + 1 } : Gen Map)
      with re := (g.emitted ⟨[], [], Termin.hop th⟩).re + 1 + 1 } : Gen Map).drop = false := by
    simp only [emitted_drop]; exact hd
  obtain ⟨b, hb, rfl⟩ := addOps_spec e3 d1
  have hb' : b = ⟨[], [], Termin.hop th⟩ := by
    have := hk_emitted_self hd ⟨[], [], Termin.hop th⟩
    simp only at hb
    rw [this] at hb; exact (Option.some.inj hb).symm
  subst hb'
  refine ⟨rfl, rfl, rfl, by simp [Gen.emitted], by simp [Gen.emitted], by simp [emitted_drop, hd],
    by simp [Gen.emitted, hd], by simp [Gen.emitted, hd], by simp [Gen.emitted, HoonMap.get_put], fun k hk => ?_⟩
  simp only [HoonMap.get_put, Gen.emitted, hd, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hk, if_neg hk]

/-- **The cons with a hinted head and a tail that is not hinted, under the
goal of `RegGBT`, apart**: the split block, the tail under `%next
(lazy-from-reg (re + 1)) (jmp0 bo)`, `+past` (the tail's result behind a
block), the head under `%next (lazy-from-reg re) th2`, `+copy`. -/
theorem runLCH_consA_next {env : CallEnv} {p q : Nomm} (hq : hinted env.cod q ≠ some true)
    {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (d0 : g0.drop = false)
    (hr : runLCH env snd true sup (Nomm.cons p q) (CGoalL.next (ofSure (lazyReg rg)) th) region g0 = some (nex, g1)) :
    ∃ gA nq gq nq' gq' np gp,
      gA.re = g0.re + 2 ∧ gA.bo = g0.bo + 1 ∧ gA.drop = false ∧ gA.cond = g0.cond ∧ gA.tags = g0.tags ∧
      HoonMap.get gA.blocks g0.bo = some ⟨[], [Pole.con g0.re (g0.re + 1) rg], Termin.hop th⟩ ∧
      (∀ k, k ≠ g0.bo → HoonMap.get gA.blocks k = HoonMap.get g0.blocks k) ∧
      runLCH env snd true sup q (CGoalL.next (ofSure (lazyReg (g0.re + 1))) (jmp0 g0.bo)) region gA = some (nq, gq) ∧
      pastL env.cod nq p region gq = some (nq', gq') ∧
      runLCH env snd true sup p (CGoalL.next (ofSure (lazyReg g0.re)) nq'.th) region gq' = some (np, gp) ∧
      copyL np nq'.laz gp = some (nex, g1) := by
  have e : (runLCH env snd true sup (Nomm.cons p q) (CGoalL.next (ofSure (lazyReg rg)) th) region : CM Map (NextL S)) =
      (do
        let (hed, tel, o) ← splitL ⟨ofSure (lazyReg rg), th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLCH env snd true sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLCH env snd true sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, gA, hs, hr⟩ := bind_some hr
  simp only at hr
  obtain ⟨nexh, gb, hph, hr⟩ := bind_some hr
  obtain ⟨nq, gq, h3, hr⟩ := bind_some hr
  obtain ⟨nq', gq', hp2, hr⟩ := bind_some hr
  obtain ⟨np, gp, h4, hcp⟩ := bind_some hr
  obtain ⟨rfl, rfl, rfl, a1, a2, a3, a4, a5, a6, a7⟩ := splitL_lazyReg d0 hs
  have hnx := pastL_notHinted hq hph
  have hg : gb = gA := by
    unfold pastL at hph
    split at hph
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hph; exact hph.2.symm
    · cases eh : hinted env.cod q with
      | none => simp [eh] at hph
      | some b =>
        cases b with
        | true => exact absurd eh hq
        | false => simp only [eh, pure_apply, Option.some.injEq, Prod.mk.injEq] at hph; exact hph.2.symm
  subst hnx
  have hg' := hg.symm
  subst hg'
  exact ⟨gA, nq, gq, nq', gq', np, gp, a1, a2, a3, a4, a5, a6, a7, h3, hp2, h4, hcp⟩

/-- **The cons with a hinted tail and a head that is not hinted, under the
goal of `RegGBT`, apart**: the split block, `+past` of the head's need
(behind a block `o1` when it asks something), the tail under `%next
(lazy-from-reg (re + 1)) nexh.th` (a goal of `RegGBT`), the head under the
parked need, `+copy`. -/
theorem runLCH_consB_next {env : CallEnv} {p q : Nomm} (hp : hinted env.cod p ≠ some true)
    {sup : Option Nomm} {rg : Nat} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (d0 : g0.drop = false)
    (hr : runLCH env snd true sup (Nomm.cons p q) (CGoalL.next (ofSure (lazyReg rg)) th) region g0 = some (nex, g1)) :
    ∃ gA nexh gb nq gq np gp,
      gA.re = g0.re + 2 ∧ gA.bo = g0.bo + 1 ∧ gA.drop = false ∧ gA.cond = g0.cond ∧ gA.tags = g0.tags ∧
      HoonMap.get gA.blocks g0.bo = some ⟨[], [Pole.con g0.re (g0.re + 1) rg], Termin.hop th⟩ ∧
      (∀ k, k ≠ g0.bo → HoonMap.get gA.blocks k = HoonMap.get g0.blocks k) ∧
      pastL env.cod ⟨ofSure (lazyReg g0.re), jmp0 g0.bo⟩ q region gA = some (nexh, gb) ∧
      runLCH env snd true sup q (CGoalL.next (ofSure (lazyReg (g0.re + 1))) nexh.th) region gb = some (nq, gq) ∧
      runLCH env snd true sup p (CGoalL.next nexh.laz nq.th) region gq = some (np, gp) ∧
      copyL np nq.laz gp = some (nex, g1) := by
  have e : (runLCH env snd true sup (Nomm.cons p q) (CGoalL.next (ofSure (lazyReg rg)) th) region : CM Map (NextL S)) =
      (do
        let (hed, tel, o) ← splitL ⟨ofSure (lazyReg rg), th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLCH env snd true sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLCH env snd true sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at hr
  obtain ⟨⟨hed, tel, o⟩, gA, hs, hr⟩ := bind_some hr
  simp only at hr
  obtain ⟨nexh, gb, hph, hr⟩ := bind_some hr
  obtain ⟨nq, gq, h3, hr⟩ := bind_some hr
  obtain ⟨nq', gq', hp2, hr⟩ := bind_some hr
  obtain ⟨np, gp, h4, hcp⟩ := bind_some hr
  obtain ⟨rfl, rfl, rfl, a1, a2, a3, a4, a5, a6, a7⟩ := splitL_lazyReg d0 hs
  have hnx := pastL_notHinted hp hp2
  have hg : gq' = gq := by
    unfold pastL at hp2
    split at hp2
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp2; exact hp2.2.symm
    · cases eh : hinted env.cod p with
      | none => simp [eh] at hp2
      | some b =>
        cases b with
        | true => exact absurd eh hp
        | false => simp only [eh, pure_apply, Option.some.injEq, Prod.mk.injEq] at hp2; exact hp2.2.symm
  have hnx' := hnx.symm
  have hg' := hg.symm
  subst hnx' hg'
  exact ⟨gA, nexh, gb, nq, gq, np, gp, a1, a2, a3, a4, a5, a6, a7, hph, h3, h4, hcp⟩

end Comp
end SkaModel
end Formalization
