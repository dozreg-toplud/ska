import lemmas.Ska.CompIndirectOut
import lemmas.Ska.CompIndirectBwd

/-!
# The backward relation of code that calls

README Gaps 12.16 (nineteenth session).  The backward half of the run
relation of a nomm with calls under a parent, the counterpart of `SemNC`.

The design.  The forward relation (`SemNC`) says: for an oracle with
`OracleFwd n`, if `+mink` returns `r` with fuel `n`, the code from the run's
jump meets `GoalSemCM` at `r`.  Determinism does not turn it into the
backward one.  An oracle with `OracleBwd` need not answer where `+mink`
returns (the oracle that never answers has `OracleBwd`), so it has no
`OracleFwd n`, and the forward relation cannot be applied to it; to apply
it one would extend the oracle with `+mink`'s answers where it has none,
which needs an interpreter tone related to every `+mink` tone (`ToneRel` is
not reflexive: a `%mean` frame of `+mink` whose trap neither is a bell's
call nor `+mack`s has no interpreter frame related to it) and the
monotonicity of the interpreter in the oracle.  And where `+mink` does not
halt, the code must be shown not to return, which is the whole backward
induction anyway (compose the `+mink` runs of the parts from the oracle's
answers).  So the backward relation is a second relation, with the same
core: **`SemNCB`, if the code from the run's jump returns at all, there is
a `+mink` result `r` on the formula with `GoalSemCM` at `r`**.  Since
`GoalSemCM` is the same predicate in both, a parent composes its parts the
same way in both directions: the step from the head's `GoalSemCM` at `rh`
to the cons's at `r` is the forward text, only the existence of `rh` (and
of `+mink`'s run of the cons from it) changes.  For example, for `[2 b c]`
the code from the jump returns, so the oracle answered the `%nok` on the
products `x`, `y` of `b`, `c`, `OracleBwd.nok` gives `+mink`'s run on
`[x y]`, `MinkN2.bwd` makes it a run on `[2 b c]`, and the block `out` gives
`GoalSemCM` as forward (`indirect_semGB`).

* `SemNCB`: the backward `sem`.
* `indirect_semGB`: `indirect_semG` backward.
* `indirect_runSB`, `indirect_runNB`, `indirect_runDB`, `indirect_runPB`:
  the indirect call under a fork-free `%next`, `%done` and `%pick` meets
  `SemNCB` (the counterparts of `indirect_runS`, `indirect_runN`,
  `indirect_runD`, `indirect_runP`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The backward `sem` of a run that calls, under a fork-free `%next`**:
for every oracle whose answers `+mink` returns (`OracleBwd`), if the code
from the run's jump returns, `+mink` returns some `r` on `[s f]` and the
code meets `GoalSemCM` at `r` (the same predicate as `SemNC`'s). -/
def SemNCB (lib : Lib) (P : Noun → Prop) (f : Noun) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map)
    (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem sur.ned x) st regs t tm nex.th
        (CGoal.next sur th) r

/-- **The indirect call at any goal, from the run's jump, backward**
(`indirect_semG` with `OracleBwd`): if the code returns, the oracle answered
the `%nok`, and `+mink` returns on the formula a tone at which the code
meets `GoalSemCM`. -/
theorem indirect_semGB {lib : Lib} {P : Noun → Prop} {f : Noun} {p q : Nomm} (M : MinkN2 lib P f p q)
    {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {gul : Noun}
    (hS : OracleSteps Inv ν O) (hB : OracleBwd lib Inv ν O) {c : Straight Map}
    {a b pro o out : Nat} (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.nok a b pro], Termin.hop (jmp0 out)⟩)
    {K K' : Nat → Prop} (hK : ∀ x, K x → K' x ∧ x ≠ pro)
    {goal : CGoal S} (Hout : OutGoal lib O c gul Inv ν K pro out goal)
    {st : σ} (hI : Inv st) {ti tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) ti tm)
    {s : Noun} (hs : P s) {je : Jmp} {regs : Map (Option Noun)}
    (G : GoalSem lib O c gul st K' regs ti je (CGoal.next (pairSure a b : Sure S) (jmp0 o))
      (pureEval (Nomm.cons p q) s))
    {res : Tone × σ} (hres : goJ lib O c gul st regs ti je = some res) :
    ∃ r, Mink lib gul tm s f r ∧ GoalSemCM lib O c gul Inv ν K st regs ti tm je goal r := by
  rw [pureEval_cons] at G
  cases ex : pureEval p s with
  | none =>
    rw [ex] at G
    have G' : goJ lib O c gul st regs ti je = some (Tone.two ti, st) := G
    exact ⟨_, M.crash hs (by rw [ex]; rfl),
      goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.two ti, st, hI, Needs.le_refl _, G', ToneRel.two htr⟩⟩
  | some x =>
    cases ey : pureEval q s with
    | none =>
      rw [ex, ey] at G
      have G' : goJ lib O c gul st regs ti je = some (Tone.two ti, st) := G
      exact ⟨_, M.crash hs (by rw [ex, ey]; rfl),
        goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.two ti, st, hI, Needs.le_refl _, G', ToneRel.two htr⟩⟩
    | some y =>
      rw [ex, ey] at G
      simp only [Option.bind_some] at G
      obtain ⟨regs', ⟨h2, h3⟩, hk', e⟩ := G.1 ⟨⟨trivial, trivial⟩, looks_empty _⟩
      have J := goJ_nok (lib := lib) (O := O) (gul := gul) hb st regs' ti h2 h3
      have hres' := hres
      rw [e, J] at hres'
      obtain ⟨⟨ton, st'⟩, hO, -⟩ := Option.bind_eq_some_iff.mp hres'
      obtain ⟨r0, ⟨k, hM⟩, hrel⟩ := hB.nok st x y gul ton st' hI hO
      obtain ⟨hI', hν⟩ := hS.nok st x y gul ton st' hI hO
      have Mk : Mink lib gul tm s f (r0.app tm) := M.bwd hs ex ey ⟨k, by rw [minkF_trace, hM]; rfl⟩
      rw [hO, Option.bind_some] at J
      refine ⟨_, Mk, ?_⟩
      cases hrel with
      | zero p' =>
        have J' : goJ lib O c gul st regs' ti (jmp0 o) =
            goJ lib O c gul st' (SkaModel.store pro p' regs') ti (jmp0 out) := J
        exact goalSemCM_step hν (fun z hz => by rw [read_store_ne (hK z hz).2, hk' z (hK z hz).1]) (e.trans J')
          goal _ (Hout st' (SkaModel.store pro p' regs') ti tm p' hI' (frames_mono hν htr)
            (read_store_eq pro p' regs'))
      | one p' =>
        exact goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.one p', st', hI', hν, e.trans J, ToneRel.one p'⟩
      | two hl =>
        exact goalSemCM_ret goal _ (fun _ h => by cases h)
          ⟨_, st', hI', hν, e.trans J, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩

/-- **The indirect call `[2 p q]` under a fork-free `%next sur th` meets
`SemNCB`** (the backward counterpart of `indirect_runS`, with the same
hypotheses): the blocks before the runs (`indirect_prefixN`), the runs of `p`
and `q` (`indirect_mid`), the block of `+kerf` (`outGoal_kerf`), then
`indirect_semGB`. -/
theorem indirect_runSB (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    {out pro o : Nat} {g2 g3 g4 g5 g6 : Gen Map} {nexF nexF' nexS : NextL S}
    (h2 : kerf (⟨ofSure sur, th⟩ : NextL S) g0 = some ((out, pro), g2))
    (h3 : emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3))
    (h4 : runLC env sup q (CGoalL.next (ofSure (lazyReg (g2.re + 1))) (jmp0 o)) region g3 = some (nexF, g4))
    (h5 : pastL env.cod nexF p region g4 = some (nexF', g5))
    (h6 : runLC env sup p (CGoalL.next (ofSure (lazyReg g2.re)) nexF'.th) region g5 = some (nexS, g6))
    (h7 : copyL nexS nexF'.laz g6 = some (nex, g')) :
    SemNCB lib P f sur th g0 g' nex := by
  have h1 : simpleNextL (CGoalL.next (ofSure sur) th) g0 = some (⟨ofSure sur, th⟩, g0) := rfl
  obtain ⟨-, -, rfl, rfl, rfl, l2, r3, b3, d3, cn3, k3o, k3out, k3lo, hk2, G3, u3, cb3⟩ :=
    indirect_prefixN h1 h2 h3 d0 hu hcb b0 hj
  have pp := up.pure
  have qp := uq.pure
  rw [runLC_eq env q (Nomm.noCall_of_pure q qp)] at h4
  rw [pastL_pure _ _ pp, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  rw [runLC_eq env p (Nomm.noCall_of_pure p pp)] at h6
  have nk : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => condBelow_none hcb hx
  have Rm := indirect_mid (a := g2.re) (b := g2.re + 1) (o := g0.bo + 1) lib up uq (by omega)
    (by omega) (by omega) (by omega) (by omega) hcount d3 u3 (hcl.growU G3) cb3
    (by rw [cn3]; exact nk _ (by omega)) (by rw [cn3]; exact nk _ (by omega)) h4 h6 h7
  have cf3 : ∀ k, k < g3.re → HoonMap.get g'.cond k = HoonMap.get g0.cond k := fun k hk => by
    rw [Rm.cfr.get_lt hk, cn3]
  intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
  have hcf6 : ∀ x, x < g3.re → HoonMap.get cf x = HoonMap.get g0.cond x := fun x hx => by
    rw [hcf x (by have := Rm.ext.1; omega), cf3 x hx]
  have ag3 : AgreeU lib O c gul st t cf ned g3 g' nex.laz s0 s :=
    AgreeU.part (ag st) (by omega) (Ext.refl g') (fun e he => he) (fun k _ _ hk => hk)
      (fun e he => Nat.lt_trans (Rm.labs e he).2.1 Rm.hi)
  have G := Rm.sem cf (fun k hk => hcf k hk) c ned σ O st t gul s0 s ag3 hned regs hh hn
  have nlab : ∀ k, k < g3.bo → k ∉ (entries nex.laz).map Prod.fst := fun k hk hm => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    have := (Rm.labs e he).1; omega
  have hbo : HoonMap.get c.blocks (g0.bo + 1) =
      some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ := by
    rw [(ag st).1 (g0.bo + 1) (by omega) (by have := Rm.ext.2.1; omega) (nlab _ (by omega)),
      Rm.ext.2.2.2 _ (by omega), k3o]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
      renJmp_nil _ (show (jmp0 g0.bo).args = [] from rfl)]
    rw [unproxy_none (by rw [hcf6 _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hcf6 _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hcf6 _ (by omega)]; exact nk _ (Nat.le_refl _))]
  have Hout := outGoal_kerf (Inv := Inv) (ν := ν) (lib := lib) (O := O) (gul := gul)
    (K := fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem sur.ned x) hk2 d0 hth hok.1 hok.2
    (cf := cf) (c := c)
    (by rw [(ag st).1 g0.bo (Nat.le_refl _) (by have := Rm.ext.2.1; omega) (nlab _ (by omega)),
      Rm.ext.2.2.2 _ (by omega), k3out])
    (fun x hx => by
      rcases hx with e | e | ⟨a, b⟩
      · rw [hcf6 _ (by omega)]; exact nk _ (by omega)
      · rw [hcf6 _ (by have := hok.2 x e; omega)]; exact hkg x e
      · rw [hcf6 _ (by omega)]; exact nk _ (by omega))
    (fun x hx => ⟨hx.2, by
      rcases hx.1 with e | e
      · exact Or.inl e
      · exact Or.inr (by have := hned x e; have := Rm.ext.1; omega)⟩)
  exact indirect_semGB M hS hB hbo (K' := fun x => (x < g3.re ∨ NMem ned x) ∧ ¬ NMem (pairSure g2.re (g2.re + 1) : Sure S).ned x)
    (fun x hx => ⟨⟨by
      rcases hx.1 with e | e
      · exact Or.inl (by omega)
      · exact Or.inr e, fun hm => by
      simp only [pairSure, NMem] at hm
      rcases hx.1 with e | e
      · omega
      · have := hned x e; have := Rm.ext.1; omega⟩, fun e => by
      subst e
      rcases hx.1 with e | e
      · omega
      · have := hned _ e; have := Rm.ext.1; omega⟩) Hout hI htr hs G hres

/-- **The indirect call `[2 p q]` under a fork-free `%next sur th` meets
`SemNCB`** (`indirect_runSB` after `runLC_n2_none`). -/
theorem indirect_runNB (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n2 p q Option.none) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g')) :
    SemNCB lib P f sur th g0 g' nex := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact indirect_runSB lib up uq M hcount hj hth hok b0 d0 hu hcl hcb hkg h2 h3 h4 h5 h6 h7

/-- **The indirect call `[2 p q]` under `%done`, backward**: the rest of
the run after the block `[don re]` of `+simple-next` (`indirect_runD`) meets
`SemNCB` under `%next (lazy-from-reg re)` into it (`indirect_runSB`). -/
theorem indirect_runDB (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n2 p q Option.none) CGoalL.done region g0 = some (nex, g')) :
    SemNCB lib P f (lazyReg g0.re) (jmp0 g0.bo)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' nex := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL] at h1
  obtain ⟨r, ga, ha, h1⟩ := bind_some h1
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨od, gb, hb, h1⟩ := bind_some h1
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  exact indirect_runSB (sur := lazyReg g0.re) (th := jmp0 g0.bo) lib up uq M hcount
    ⟨b0, by simp only [jmp0, Gen.emitted]; omega⟩ rfl
    ⟨trivial, fun x hx => by simp only [lazyReg, NMem] at hx; subst hx; simp only [Gen.emitted]; omega⟩
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      exact condBelow_none hcb (Nat.le_refl _)) h2 h3 h4 h5 h6 h7

/-- **The indirect call `[2 p q]` under `%pick z o`, backward**: the rest
of the run after the block `[brn re z o]` of `+simple-next`
(`indirect_runP`) meets `SemNCB` under `%next (lazy-from-reg re)` into it
(`indirect_runSB`). -/
theorem indirect_runPB (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {region : List Nat} {g0 g' : Gen Map} {nex : NextL S} {z o' : Jmp}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hjp : GJ g0.bo (CGoal.pick z o' : CGoal S))
    (h : runLC env sup (Nomm.n2 p q Option.none) (CGoalL.pick z o') region g0 = some (nex, g')) :
    SemNCB lib P f (lazyReg g0.re) (jmp0 g0.bo)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o'⟩) g' nex := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL] at h1
  obtain ⟨r, ga, ha, h1⟩ := bind_some h1
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨od, gb, hb, h1⟩ := bind_some h1
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o'⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.brn g0.re z o'⟩)
      (fun j hj => by
        simp only [finJumps, List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl
        · exact hjp.1
        · exact hjp.2) hu
  exact indirect_runSB (sur := lazyReg g0.re) (th := jmp0 g0.bo) lib up uq M hcount
    ⟨b0, by simp only [jmp0, Gen.emitted]; omega⟩ rfl
    ⟨trivial, fun x hx => by simp only [lazyReg, NMem] at hx; subst hx; simp only [Gen.emitted]; omega⟩
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      exact condBelow_none hcb (Nat.le_refl _)) h2 h3 h4 h5 h6 h7

end Comp
end SkaModel
end Formalization
