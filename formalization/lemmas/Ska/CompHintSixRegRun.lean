import lemmas.Ska.CompHintTen
import lemmas.Ska.CompHintEq
import lemmas.Ska.CompSixNxRun
import lemmas.Ska.CompHintSixRegCheck

/-!
# `[6 c a b]` under `%next` in `runLCH`, step by step (README Gaps 24.21)

The model half of the `%6` constructor of the hinted classes (checked in
`CompHintSixRegCheck.lean`):
* `runLCH_six_nextE`: at a goal with no entry the `%6` of `runLCH` is
  phase S, `sixNextSimpleC` over the runs of `runLCH` (the text of
  `runLC_six_nextE`).
* `forkSure_lazyReg`: `+fork-sure` of `lazy-from-reg rg` gives `lazy-from-reg`
  of two registers, so the branches of a `%6` under `%next (lazy-from-reg
  rg)` run under `%next (lazy-from-reg r0)` and `%next (lazy-from-reg r1)`.
* `pastFork_some_false`: a test with `hinted` `some false` leaves the fork.
* `runLCH_six_reg`: the run of `[6 c a b]` under `%next (lazy-from-reg rg)
  th`, the test hint-free and without a direct call: `+fork-sure`, `b`, `a`
  (each under `lazy-from-reg` of a fresh register), `+sect`, the test under
  `%pick` (a run of `runLC`), `+copy` of the fork (when it is not big).
* `SixNH`: what a branch gives (`SixN` for `runLCH` and `RunOKGBT`, the goal's
  sure need in a class `Ap`, the result not asked to be flat);
  `sixNH_of`: from `SurGBT`, a bound on the entries and the tag clause.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The `%6` of `runLCH` at a goal with no entry is phase S** (the text of
`runLC_six_nextE`). -/
theorem runLCH_six_nextE (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (mono : Bool) (sup : Option Nomm)
    (c a b : Nomm) {L : Lazy S} (he : entries L = []) (th : Jmp) (region : List Nat) :
    (runLCH env snd mono sup (Nomm.n6 c a b) (CGoalL.next L th) region : CM Map (NextL S)) =
      sixNextSimpleC env.cod (runLCH env snd mono sup c) (runLCH env snd mono sup a) (runLCH env snd mono sup b)
        c L th region := by
  have hf := entries_nil_flat he
  have eL : L = mk L.sure [] [] := by
    rcases L with ⟨s, F, B⟩
    obtain ⟨h1, _⟩ := hf
    simp only [fork_mk] at h1
    subst h1
    cases B with
    | nil => rfl
    | cons e B => cases e; simp [entries, bondEntries] at he
  rw [eL]
  simp only [runLCH]
  exact sixNextLC_fork_free env.cod _ _ _ c a b 2 L.sure th region

/-- **`+fork-sure` of `lazy-from-reg rg`** is `lazy-from-reg` of two registers. -/
theorem forkSure_lazyReg {rg o : Nat} {g g' : Gen Map} {s0 s1 : Sure S}
    (h : forkSure (lazyReg rg) o g.bo (g.bo + 1) { g with bo := g.bo + 2 } = some ((s0, s1), g'))
    (hd : g.drop = false) : ∃ r0 r1, s0 = lazyReg r0 ∧ s1 = lazyReg r1 := by
  obtain ⟨l0, l1, c0, c1, -⟩ := forkSure_spec h hd
  rcases s0 with ⟨n0, k0⟩
  rcases s1 with ⟨n1, k1⟩
  simp only [lazyReg] at l0 l1 c0 c1
  subst l0 l1
  cases n0 with
  | this r0 =>
    cases n1 with
    | this r1 => exact ⟨r0, r1, rfl, rfl⟩
    | _ => simp [NCopy] at c1
  | _ => simp [NCopy] at c0

/-- **A test with `hinted` `some false` leaves the fork as it is.** -/
theorem pastFork_some_false {cod : Bell → Option Bool} {c : Nomm} (hc : hinted cod c = some false)
    {lz lw : Lazy S} (h : pastFork cod lz c = some lw) : lw = lz := by
  simp only [pastFork, hc, Option.some.injEq] at h
  exact h.symm

/-- **The run of `[6 c a b]` under `%next (lazy-from-reg rg) th`, step by
step**: `+fork-sure` (two fresh registers `r0`, `r1`), the no branch `b`
under `%next (lazy-from-reg r1)`, the yes branch `a` under `%next
(lazy-from-reg r0)`, `+sect`, the test (hint-free, no direct call: a run of
`runLC`) under `%pick` of the two fork blocks, `+copy` of the fork. -/
theorem runLCH_six_reg {env : CallEnv} {snd : Nomm → NeedOrd → Bool} {sup : Option Nomm} {c a b : Nomm}
    (hch : c.noHint = true) (hcd : c.noDirect = true) (hcf : hinted env.cod c = some false)
    {rg : Nat} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S} (d0 : g0.drop = false)
    (h : runLCH env snd true sup (Nomm.n6 c a b) (CGoalL.next (ofSure (lazyReg rg)) th) region g0 =
      some (nex, g9)) :
    ∃ (r0 r1 : Nat) (x1 x0 xc : NextL S) (lz : Lazy S) (yes nuh : Nat) (gF gR gQ gS gC : Gen Map),
      forkSure (S := S) (lazyReg rg) th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 2 } =
        some ((lazyReg r0, lazyReg r1), gF) ∧
      runLCH env snd true sup b (CGoalL.next (ofSure (lazyReg r1)) (jmp0 (g0.bo + 1))) (gF.id :: region)
        { gF with id := gF.id + 1 } = some (x1, gR) ∧
      runLCH env snd true sup a (CGoalL.next (ofSure (lazyReg r0)) (jmp0 g0.bo)) (gF.id :: region) gR =
        some (x0, gQ) ∧
      sect x0 x1 g0.bo (g0.bo + 1) (gF.id :: region) gF.cond gR.cond gQ = some ((lz, yes, nuh), gS) ∧
      runLC env sup c (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region gS = some (xc, gC) ∧
      (lazyBig lz = false → copyL xc lz gC = some (nex, g9)) := by
  rw [runLCH_six_nextE env snd true sup c a b (entries_ofSure _) th region] at h
  obtain ⟨s0, s1, x1, x0, xc, lz, lw, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hw, hC, hk⟩ :=
    sixNextSimpleC_apart h
  have hF' : forkSure (lazyReg rg) th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 2 } = some ((s0, s1), gF) := hF
  obtain ⟨r0, r1, rfl, rfl⟩ := forkSure_lazyReg hF' d0
  have e := pastFork_some_false hcf hw
  subst e
  rw [runLCH_eq env snd true c hch, runLCM_eq env true c (by simp [hcd])] at hC
  exact ⟨r0, r1, x1, x0, xc, lw, yes, nuh, gF, gR, gQ, gS, gC, hF', hR, hQ, hS, hC, hk⟩

/-! ## What a branch gives -/

/-- **What a branch of phase S gives, hinted**: `SixN` for `runLCH` with
`RunOKGBT`, at the goals whose sure need is in `Ap`, the result not asked to
be flat (its bonds may nest). -/
abbrev SixNH (snd : Nomm → NeedOrd → Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop)
    (Ap : Sure S → Prop) (f : Noun) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct sur.ned →
    (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) → Clean sur.ned → Ap sur →
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    RunOKGBT lib N P f (CGoal.next sur th) g0 g1 nex ∧ (entries nex.laz).length ≤ k ∧
      CondTag region g0.cond g1.cond

/-- **A bound on the entries of the runs under `%next (ofSure sur)`, `sur` in
`Ap`.** -/
abbrev EntH (snd : Nomm → NeedOrd → Bool) (env : CallEnv) (Ap : Sure S → Prop) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Ap sur → runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure sur) th) region g0 =
      some (nex, g1) → (entries nex.laz).length ≤ k

/-- **The tag clause of the runs under `%next (ofSure sur)`, `sur` in `Ap`**
(every key the run adds to `cond` has a tag with its region as a suffix). -/
abbrev TagH (snd : Nomm → NeedOrd → Bool) (env : CallEnv) (Ap : Sure S → Prop) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Ap sur → runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure sur) th) region g0 =
      some (nex, g1) → CondTag region g0.cond g1.cond

/-- **A member of `SurGBT` with a bound on its entries and the tag clause
meets `SixNH`.** -/
theorem sixNH_of {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {Ap : Sure S → Prop} {f : Noun} {nm : Nomm} {k : Nat} (H : SurGBT (S := S) (Map := Map) snd lib N env P Ap f nm)
    (K : EntH (S := S) (Map := Map) snd env Ap nm k) (T : TagH (S := S) (Map := Map) snd env Ap nm) :
    SixNH (S := S) (Map := Map) snd lib N env P Ap f nm k :=
  fun _ b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hA hr =>
    ⟨H hA b0 d0 hu hcl hcb h1 h2 hta hsd hcs hsl hr, K hA hr, T hA hr⟩

/-- The class of the sure needs `lazy-from-reg r`. -/
def IsReg (sur : Sure S) : Prop := ∃ r, sur = lazyReg r

/-- **A member of `RegGBT` is in `SurGBT IsReg`.** -/
theorem RegGBT.toSur {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {f : Noun} {nm : Nomm} (H : RegGBT (S := S) (Map := Map) snd lib N env P f nm) :
    SurGBT (S := S) (Map := Map) snd lib N env P IsReg f nm := by
  intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr
  obtain ⟨r, rfl⟩ := hA
  have hm : NMem (lazyReg r : Sure S).ned r := by simp [lazyReg, NMem]
  exact H b0 d0 hu hcl hcb th1 th2 hta (hsl r hm).1 (hsl r hm).2 hr

/-- **A member of `SurGBT IsReg` is in `RegGBT`.** -/
theorem RegGBT.ofSur {snd : Nomm → NeedOrd → Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop}
    {f : Noun} {nm : Nomm} (H : SurGBT (S := S) (Map := Map) snd lib N env P IsReg f nm) :
    RegGBT (S := S) (Map := Map) snd lib N env P f nm := by
  intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr
  exact H ⟨rg, rfl⟩ b0 d0 hu hcl hcb th1 th2 hta trivial (by simp [lazyReg, Clean])
    (fun x hx => by simp only [lazyReg, NMem] at hx; subst hx; exact ⟨hr0, hc0⟩) hr

end Comp
end SkaModel
end Formalization
