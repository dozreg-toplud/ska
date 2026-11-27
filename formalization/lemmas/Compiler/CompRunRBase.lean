import lemmas.Compiler.CompRunDirectMonoP
import lemmas.Compiler.CompRunTenL

/-!
# The run link against `runLCM env true` with a rest predicate (README Gaps 19)

The case lemmas of `+run` of track A (`CompRunLeafL.lean`, `CompRunConsL.lean`,
`CompRunFiveL.lean`, `CompRunTenL.lean`, `comp_run_n7C`) are stated against
`runLC env msup` for every `mono`, Hoon `sup` and rest `x` with an empty
`soft`.  A part with a direct call is linked only at `mono` `A 0`, the Hoon
`sup` the noun of `msup`, and a rest that meets `E` (`CompRunAtMM`).  The
copies `CompRunR*.lean` (by `tools/gen/runr.py`) state the cases against
`runLCM env true msup` with the link `CompRunAtX`: `CompRunAtR` with one more
hypothesis `X x mono sup` on the rest, `mono` and `sup`.

* `CompRunAtX` and `XM E msup` (`E x`, `mono = A 0`, `sup` the noun of
  `msup`): `CompRunAtX … (XM E msup)` is `CompRunAtMM` (`crx_iff_mm`).
* `PastAt ctx cod n`: the pill's `+past` over `n` is `pastL cod`
  (`comp_past` is `PastAt ctx noCode`); `pastAt_nd`: with no direct call it
  is `PastAt ctx cod` for every `cod`.
* `PartR`: what the copied cases take of a part (the link `CompRunAtX`, the
  result `ResForR`, and `PastAt ctx env.cod`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The run link against `R` with a rest predicate `X`.** -/
def CompRunAtX (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (ctx : Noun)
    (X : GenRest → Noun → Noun → Prop) (n : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) : Prop :=
  ∀ (x : GenRest) (mono sup : Noun), x.NoSoft → X x mono sup →
    nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
      = (R n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

/-- The rest predicate of the link at `mono` `&`. -/
def XM (E : GenRest → Prop) (msup : Option Nomm) : GenRest → Noun → Noun → Prop :=
  fun x mono sup => E x ∧ mono = A 0 ∧ sup = unitNoun Nomm.toNoun msup

theorem crx_iff_mm {E : GenRest → Prop} {env : CallEnv} {msup : Option Nomm} {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)} :
    CompRunAtX (runLCM env true msup) ctx (XM E msup) n goal region g ↔ CompRunAtMM env msup ctx E n goal region g := by
  constructor
  · intro h x hx hE
    exact h x _ _ hx ⟨hE, rfl, rfl⟩
  · rintro h x mono sup hx ⟨hE, rfl, rfl⟩
    exact h x hx hE

/-- Every link against `R` is one with a rest predicate. -/
theorem crx_of_r {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {n : Nomm} {goal : CGoalL CSet} {region : List Nat}
    {g : Gen (TreapMap mugF)} (h : CompRunAtR R ctx n goal region g) : CompRunAtX R ctx X n goal region g :=
  fun x mono sup hx _ => h x mono sup hx

/-- With no direct call the link against `runLC` is one against `runLCM env true`. -/
theorem crx_of_runLC {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {n : Nomm}
    (hn : n.noDirect = true) {goal : CGoalL CSet} {region : List Nat} {g : Gen (TreapMap mugF)}
    (h : CompRunAtR (runLC env msup) ctx n goal region g) :
    CompRunAtX (runLCM env true msup) ctx X n goal region g := by
  intro x mono sup hx _
  rw [runLCM_true env hn msup]
  exact h x mono sup hx

/-- **`+past` over `n` is `pastL cod`.** -/
def PastAt (ctx : Noun) (cod : Bell → Option Bool) (n : Nomm) : Prop :=
  ∀ (x : GenRest) (g : Gen (TreapMap mugF)) (nex : NextL CSet) (region : List Nat),
    nock (C paBat (C (C nex.goal.toNoun (C n.toNoun (listNoun A region))) (compCore g x ctx))) paBat
      = (pastL cod nex n region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

/-- With no direct call, `+past` is `pastL cod` for every `cod`. -/
theorem pastAt_nd (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (cod' : Bell → Option Bool) {n : Nomm} (hn : NoDirect n) : PastAt ctx cod' n := by
  intro x g nex region
  rw [pastL_cod (hinted_nd cod' hn).1]
  exact comp_past h7 hcode x g nex n region (hinted_nd cod' hn).2

/-- What the copied cases take of a part. -/
structure PartR (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (X : GenRest → Noun → Noun → Prop) (n : Nomm)
    (region : List Nat) : Prop where
  link : ∀ (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal →
    CompRunAtX (runLCM env true msup) ctx X n goal region g
  res : ResForR (runLCM env true msup) n region
  past : PastAt ctx env.cod n

/-- **`PartL` gives `PartR`** for every `X`. -/
theorem partR_of_partL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {X : GenRest → Noun → Noun → Prop} {env : CallEnv} {msup : Option Nomm} {n : Nomm} {region : List Nat}
    (P : PartL env msup ctx n region) : PartR env msup ctx X n region := by
  have hm := runLCM_true (S := CSet) (Map := TreapMap mugF) env (noDirect_of_nd n P.nd) msup
  refine ⟨fun goal g hi => crx_of_runLC (noDirect_of_nd n P.nd) (P.link goal g hi), fun goal g g' nex hi h => ?_,
    pastAt_nd h7 hcode env.cod P.nd⟩
  rw [hm] at h
  exact P.res goal g g' nex hi h

/-- `PartR` at `XM E msup` gives `PartLM`. -/
theorem partLM_of_partR {E : GenRest → Prop} {env : CallEnv} {msup : Option Nomm} {n : Nomm} {region : List Nat}
    (P : PartR env msup ctx (XM E msup) n region) : PartLM env msup ctx E n region :=
  ⟨fun goal g hi => crx_iff_mm.1 (P.link goal g hi), P.res⟩

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `runLC_n2_none` (`CompIndirect.lean`) for `runLCM env true`: the indirect call. -/
theorem runLCM_n2_none {env : CallEnv} {sup : Option Nomm} {p q : Nomm} {goal : CGoalL S} {region : List Nat}
    {g0 g' : Gen Map} {nex : NextL S}
    (h : runLCM env true sup (Nomm.n2 p q Option.none) goal region g0 = some (nex, g')) :
    ∃ (nex0 : NextL S) (g1 : Gen Map) (out pro : Nat) (g2 : Gen Map) (o : Nat) (g3 : Gen Map)
      (nexF : NextL S) (g4 : Gen Map) (nexF' : NextL S) (g5 : Gen Map) (nexS : NextL S) (g6 : Gen Map),
      simpleNextL goal g0 = some (nex0, g1) ∧ kerf nex0 g1 = some ((out, pro), g2) ∧
      emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3) ∧
      runLCM env true sup q (CGoalL.next (Lazy.ofSure (lazyReg (g2.re + 1))) (jmp0 o)) region g3 = some (nexF, g4) ∧
      pastL env.cod nexF p region g4 = some (nexF', g5) ∧
      runLCM env true sup p (CGoalL.next (Lazy.ofSure (lazyReg g2.re)) nexF'.th) region g5 = some (nexS, g6) ∧
      copyL nexS nexF'.laz g6 = some (nex, g') := by
  simp only [runLCM, callLM_none, callL] at h
  obtain ⟨nex0, g1, h1, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨rSub, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rFol, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o, g3, h3, h⟩ := bind_some h
  obtain ⟨nexF, g4, h4, h⟩ := bind_some h
  obtain ⟨nexF', g5, h5, h⟩ := bind_some h
  obtain ⟨nexS, g6, h6, h⟩ := bind_some h
  exact ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h⟩

/-- `runLC_cons_done` (`CompConsCallTop.lean`) for `runLCM env true`. -/
theorem runLCM_cons_done (env : CallEnv) (sup : Option Nomm) (p q : Nomm) (region : List Nat) :
    (runLCM env true sup (Nomm.cons p q) CGoalL.done region : CM Map (NextL S)) = (do
      let r ← re
      let o ← emit ⟨[], [], Termin.don r⟩
      runLCM env true sup (Nomm.cons p q) (CGoalL.next (Lazy.ofSure (lazyReg r)) (jmp0 o)) region) := by
  conv => lhs; unfold runLCM
  rfl

end

end Compiler
end Formalization
