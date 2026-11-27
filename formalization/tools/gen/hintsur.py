#!/usr/bin/env python3
"""Write lemmas/Ska/CompHintSur.lean (README Gaps 24.19): kept hints under a
general flat lazy goal `%next (ofSure sur) th`, and `[7 p q]` whose `p` is
one.

Run from formalization/:  python3 tools/gen/hintsur.py

Text copies, each replace with its count asserted:
* `runOKGBT_sevenG`: `runOKGC_sevenG` (CompSevenG.lean) for `RunOKGBT` (the
  agreement at every trace, `AgreeUB.part` for `AgreeU.part`, the `labs`
  bound at the state, the `N ≤ ν` premise passed on).
* `frameOK_goesR`: `frameOK_goes` (CompHintFrame.lean) with the fit asked of
  the formula's tone only (`r = zero p → FitsS sur p`), not of every noun.
* `runLCH_n11d_kept_sur`: `runLCH_n11d_kept_next` (CompHintReg.lean) with
  `lazy-from-reg rg` as any `sur` and `+past-if`'s test as a premise.
* `surGBT_n11dKept`: `regGBT_n11dKept` with the formula in `SurGBT`, the goal
  `%next (ofSure sur) th`, the fit from `FitP` (the promise of `+sound`).
The rest (`AgreeUB.part`, `SoundK`, `FitP`, `SurGBT`, `SurGBT.of_loksf`,
`surSeven_done`, `finishLUCH_contractSurSeven`) is written here as text.
"""
import re, sys

OUT = 'lemmas/Ska/CompHintSur.lean'
STOP = re.compile(r'^(theorem |def |structure |/--|/-!|end |section |variable |@\[|abbrev |namespace |open )')


def grab(path, name):
    lines = open(path).read().split('\n')
    i = next(k for k, l in enumerate(lines) if l.startswith('theorem ' + name + ' '))
    j = i + 1
    while j < len(lines) and not STOP.match(lines[j]):
        j += 1
    while lines[j - 1].strip() == '':
        j -= 1
    return '\n'.join(lines[i:j])


def rep(t, a, b, n):
    c = t.count(a)
    if c != n:
        sys.exit(f'count {c} != {n} for: {a[:80]!r}')
    return t.replace(a, b)


def rep1(t, a, b):
    if a not in t:
        sys.exit(f'missing: {a[:80]!r}')
    return t.replace(a, b, 1)


# runOKGBT_sevenG
t = grab('lemmas/Ska/CompSevenG.lean', 'runOKGC_sevenG')
t = rep(t, 'theorem runOKGC_sevenG {lib : Lib} {P : Noun → Prop}', 'theorem runOKGBT_sevenG {lib : Lib} {N : Needs} {P : Noun → Prop}', 1)
t = rep(t, '(Rq : RunOKGC (Map := Map) lib (Img lib P fb) fc goal g0 g1 nx)', '(Rq : RunOKGBT (Map := Map) lib N (Img lib P fb) fc goal g0 g1 nx)', 1)
t = rep(t, '(Rp : RunOKGC (Map := Map) lib P fb (CGoal.next', '(Rp : RunOKGBT (Map := Map) lib N P fb (CGoal.next', 1)
t = rep(t, 'RunOKGC lib P f goal g0 g2 nex := by', 'RunOKGBT lib N P f goal g0 g2 nex := by', 1)
t = rep(t, '''(t : Trace) (ned : Need) (s0 s : Noun), AgreeU lib O c gul st t cf ned g0 g2 nex.laz s0 s →
      AgreeU lib O c gul st t cf ned g1 g2 nex.laz s0 s :=''', '''(t : Trace) (ned : Need) (s0 s : Noun), AgreeUB lib O c gul st t cf ned g0 g2 nex.laz s0 s →
      AgreeUB lib O c gul st t cf ned g1 g2 nex.laz s0 s :=''', 1)
t = rep(t, 'AgreeU.part ag q2', 'AgreeUB.part ag q2', 1)
t = rep(t, '(fun e he => Nat.lt_trans (Rp.labs e he).2.1 Rp.hi)', '(fun e he => (Rp.labs e he).2.1)', 1)
t = rep(t, '''(t : Trace) (ned : Need) (s0 s u : Noun), AgreeU lib O c gul st t cf ned g0 g2 nex.laz s0 s →
      AgreeU lib O c gul st' t cf ned g0 g1 nx.laz s0 u := by
    intro cf c σ O gul st st' t ned s0 s u ag''', '''(t t' : Trace) (ned : Need) (s0 s u : Noun), AgreeUB lib O c gul st t cf ned g0 g2 nex.laz s0 s →
      AgreeUB lib O c gul st' t' cf ned g0 g1 nx.laz s0 u := by
    intro cf c σ O gul st st' t t' ned s0 s u ag''', 1)
t = rep(t, 'intro cf hcf c ned σ Inv ν O n gul hS hF st', 'intro cf hcf c ned σ Inv ν O n gul hN hS hF st', 1)
t = rep(t, 'Rp.sem cf hcf c ned σ Inv ν O n1 gul hS', 'Rp.sem cf hcf c ned σ Inv ν O n1 gul hN hS', 1)
t = rep(t, "(fun st' => agP cf c σ O gul st' t ned s0 s (ag st'))", "(fun st' t' => agP cf c σ O gul st' t' ned s0 s (ag st' t'))", 2)
t = rep(t, 'Rq.sem cf hcf1 c ned σ Inv ν O n2 gul hS', 'Rq.sem cf hcf1 c ned σ Inv ν O n2 gul hN hS', 1)
t = rep(t, "(fun st'' => agQ cf c σ O gul st st'' t ned s0 s u (ag st))", "(fun st'' t'' => agQ cf c σ O gul st st'' t t'' ned s0 s u (ag st t))", 2)
t = rep(t, 'intro cf hcf c ned σ Inv ν O gul hS hB st', 'intro cf hcf c ned σ Inv ν O gul hN hS hB st', 1)
t = rep(t, 'Rp.semB cf hcf c ned σ Inv ν O gul hS hB', 'Rp.semB cf hcf c ned σ Inv ν O gul hN hS hB', 1)
t = rep(t, 'Rq.semB cf hcf1 c ned σ Inv ν O gul hS hB', 'Rq.semB cf hcf1 c ned σ Inv ν O gul hN hS hB', 1)
SEVEN = t

# frameOK_goesR
t = grab('lemmas/Ska/CompHintFrame.lean', 'frameOK_goes')
t = rep(t, 'theorem frameOK_goes ', 'theorem frameOK_goesR ', 1)
t = rep(t, '{sur : Sure S} (hfit : ∀ p, FitsS sur p) {K', '{sur : Sure S} {r : Tone} (hfit : ∀ p, r = Tone.zero p → FitsS sur p) {K', 1)
t = rep(t, '{t tm : Trace} {r : Tone}', '{t tm : Trace}', 1)
t = rep(t, 'fun hf => absurd (hfit p) hf', 'fun hf => absurd (hfit p rfl) hf', 1)
FRAME = t

# runLCH_n11d_kept_sur
t = grab('lemmas/Ska/CompHintReg.lean', 'runLCH_n11d_kept_next')
t = rep(t, 'theorem runLCH_n11d_kept_next ', 'theorem runLCH_n11d_kept_sur ', 1)
t = rep(t, '(hsnd : snd q NeedOrd.this = true) {sup : Option Nomm} {rg : Nat}',
        '{sur : Sure S} (hp : HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true) {sup : Option Nomm}', 1)
t = rep(t, '(ofSure (lazyReg rg))', '(ofSure sur)', 2)
t = rep(t, '''have hp : HoonSet.small (ofSure (lazyReg rg) : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure (lazyReg rg) : Lazy S).sure.ned) = true :=
    ⟨(HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x), hsnd⟩''', '''have hp' : HoonSet.small (ofSure sur : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure sur : Lazy S).sure.ned) = true := hp''', 1)
t = rep(t, 'rw [if_pos hp] at h1', "rw [if_pos hp'] at h1", 1)
if re.search(r'\brg\b|hsnd', t):
    sys.exit('rg/hsnd left in runLCH_n11d_kept_sur')
RUNS = t

# surGBT_n11dKept
t = grab('lemmas/Ska/CompHintReg.lean', 'regGBT_n11dKept')
t = rep(t, 'theorem regGBT_n11dKept ', 'theorem surGBT_n11dKept ', 1)
t = rep(t, '(Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)',
        '{Ap : Sure S → Prop} (Hq : SurGBT (S := S) (Map := Map) snd lib N env P Ap fq q)', 1)
t = rep(t, 'RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 11) (C (A tag) fh) fq) (Nomm.n11d tag h q body) := by',
        'SurGBT (S := S) (Map := Map) snd lib N env P (fun sur => Ap sur ∧ SoundK snd q sur ∧ FitP lib P fq sur)\n      (n3 (A 11) (C (A tag) fh) fq) (Nomm.n11d tag h q body) := by', 1)
t = rep(t, 'intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr',
        'intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr', 1)
t = rep(t, 'runLCH_n11d_kept_next hs hsnd hr', 'runLCH_n11d_kept_sur hs hA.2.1 hr', 1)
t = rep(t, '''have RQ := Hq (by rw [boA]; omega) dA uA clA cbA (by simp only [jmp0]; omega) (by simp only [jmp0]; rw [boA]; omega)
    rfl (by rw [reA]; omega) (by simp only [genN, Gen.emitted]; exact hc0) h3''', '''have RQ := Hq hA.1 (by rw [boA]; omega) dA uA clA cbA (by simp only [jmp0]; omega)
    (by simp only [jmp0]; rw [boA]; omega) rfl hsd hcs
    (fun x hx => ⟨by have := (hsl x hx).1; rw [reA]; omega, by simp only [genN, Gen.emitted]; exact (hsl x hx).2⟩) h3''', 1)
t = rep(t, 'RQ.bound (fun x hx => by simp only [lazyReg, NMem] at hx; rw [reA]; omega)',
        'RQ.bound (fun x hx => by have := (hsl x hx).1; rw [reA]; omega)', 1)
t = rep(t, '(lazyReg rg : Sure S)', 'sur', 3)
t = rep(t, 'frameOK_goes F (fitsS_lazyReg rg) hh1 Gq', 'FITHERE', 2)
t = rep1(t, 'FITHERE', 'frameOK_goesR F (fun p e => hA.2.2 s hs gul _ p ⟨m, by rw [← e]; exact hm⟩) hh1 Gq')
t = rep1(t, 'FITHERE', 'frameOK_goesR F (fun p e => hA.2.2 s hs gul _ p (by rw [← e]; exact hmq)) hh1 Gq')
if re.search(r'\brg\b|hsnd|hr0|hc0', t):
    sys.exit('rg/hsnd/hr0/hc0 left in surGBT_n11dKept: ' + str(re.findall(r'.{30}(?:\brg\b|hsnd|hr0|hc0).{30}', t)))
KEPT = t

HEAD = '''import lemmas.Ska.CompHintRegKeep
import lemmas.Ska.CompSevenG

/-!
# Kept hints under a general flat goal, and `[7 p q]` with a hinted `p` (README Gaps 24.19)

Generated by `tools/gen/hintsur.py` (do not edit).

The `p` of a `[7 p q]` runs under `%next laz th`, `laz` the result of `q`.
When `laz` has no entries (every dumped `%7` and the 128 shapes of
`CompHintSevenCheck.lean`), that goal is `%next (ofSure sur) th`, `sur` any
sure need, not `lazy-from-reg`.  A kept hint there runs its formula under
`%next (ofSure sur) epil` when `+past-if` emits nothing (`SoundK`: the lock
small, `+sound` of the formula at the need), and then `frameOK_goes` needs
the formula's products to fit `sur`: `FitP`, the promise of `+sound`, a
premise (the check found it true wherever `+sound` holds, and false in 50
shapes where `+sound` fails and `+past-if` parks the need).

* `SurGBT snd lib N env P Ap f nm`: every run under `%next (ofSure sur) th`,
  `sur` with `Ap sur`, its registers allocated, free of conditions, distinct
  and clean, gives `RunOKGBT` at `%next sur th`.  Every member of `LOKSFH`
  is in it for any `Ap` (`SurGBT.of_loksf`).
* `surGBT_n11dKept`: a kept dynamic `stopTag` hint over a member of
  `SurGBT Ap` is in `SurGBT (Ap ∧ SoundK ∧ FitP)` (the text of
  `regGBT_n11dKept`); nested hints stack their conditions.
* `runOKGBT_sevenG`: `[7 p q]` for `RunOKGBT`, `q`'s result without
  entries, `p` at `%next q.sure q.th` (the text of `runOKGC_sevenG`).
* `surSeven_done`, `finishLUCH_contractSurSeven`: `[7 p q]` under `%done`
  with `p` in `SurGBT Ap`, `q` with `DoneAllT`, its result without entries
  and with `Ap` of its sure need; the contract at the top.

The case where `+sound` fails (the formula under a goal whose need is
parked in a bond, filled after the frame is popped) is not covered.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `AgreeUB` of a part of the run from the whole's (the text of `AgreeU.part`). -/
theorem AgreeUB.part {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cf : Map (Nat × List Nat)} {ned : Need} {g0 g3 ga gb : Gen Map} {L La : Lazy S} {s0 s : Noun}
    (ag : AgreeUB lib O c gul st t cf ned g0 g3 L s0 s) (h0 : g0.bo ≤ ga.bo) (eb : Ext gb g3)
    (hmem : ∀ e ∈ entries La, e ∈ entries L)
    (hout : ∀ k, ga.bo ≤ k → k < gb.bo → k ∈ (entries L).map Prod.fst → k ∈ (entries La).map Prod.fst)
    (hlab : ∀ e ∈ entries La, e.1 < gb.bo) :
    AgreeUB lib O c gul st t cf ned ga gb La s0 s := by
  refine ⟨fun o h0' h1 hn => by
    rw [ag.1 o (Nat.le_trans h0 h0') (Nat.lt_of_lt_of_le h1 eb.2.1) (fun hm => hn (hout o h0' h1 hm)),
      eb.2.2.2 o h1], fun e he => ?_⟩
  obtain ⟨A, B, th, h1, h2, h3⟩ := ag.2 e (hmem e he)
  exact ⟨A, B, th, by rw [← eb.2.2.2 _ (hlab e he)]; exact h1, h2, h3.mono eb.1⟩

/-- **`[7 p q]` with the agreement at every trace, `q`'s result without
entries** (the text of `runOKGC_sevenG` for `RunOKGBT`): `p` at the goal
`%next nx.laz.sure nx.th`, any `RunOKGBT` (a kept hint included). -/
'''

MID1 = '''

section Frame
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}

/-- **The frame part, the fit asked of the formula's tone only** (the text
of `frameOK_goes`): what `+sound` promises is about the products of the
formula, not about every noun. -/
'''

MID2 = '''

end Frame

/-! ## The class -/

/-- The test of `+past-if` that emits nothing: the lock small, `+sound` of
the formula at the need. -/
def SoundK (snd : Nomm → NeedOrd → Bool) (q : Nomm) (sur : Sure S) : Prop :=
  HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true

/-- **The promise of `+sound`**: every product of `f` on a subject of `P`,
at any trace, fits `sur`. -/
def FitP (lib : Lib) (P : Noun → Prop) (f : Noun) (sur : Sure S) : Prop :=
  ∀ s, P s → ∀ gul tm p, Mink lib gul tm s f (Tone.zero p) → FitsS sur p

/-- **Runs under a general flat goal**: every run under `%next (ofSure sur)
th`, for `sur` with `Ap sur`, its registers allocated and free of
conditions, gives `RunOKGBT` at `%next sur th`. -/
def SurGBT (snd : Nomm → NeedOrd → Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop)
    (Ap : Sure S → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Ap sur → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct sur.ned → Clean sur.ned →
    (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    runLCH (S := S) (Map := Map) env snd true sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    RunOKGBT lib N P f (CGoal.next sur th) g0 g1 nex

section Kept
variable {snd : Nomm → NeedOrd → Bool}

/-- **A member of `LOKSFH` is in `SurGBT`**, for any `Ap` (`RunOKLB.toGB`,
`RunOKGB.toT`; the text of `RegGBT.of_loksf`). -/
theorem SurGBT.of_loksf {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (Ap : Sure S → Prop) (H : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P f nm) (hc : sixCount nm ≤ 255) :
    SurGBT (S := S) (Map := Map) snd lib N env P Ap f nm := by
  intro sup sur th region g0 g1 nex _ b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr
  have e0 : entries (ofSure sur : Lazy S) = [] := entries_ofSure _
  obtain ⟨⟨Q, RS⟩, -, -, -, -⟩ := H.run (sup := sup) (L := ofSure sur) (th := th) (region := region)
    (Or.inr e0) hc b0 d0 hu hcl hcb th1 th2 hta (by rw [e0]; simp) hsd hsl
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) hcs (fun e he => by rw [e0] at he; cases he) hr
  exact (RS.toRunOKLB.toGB (fun x hx => (hsl x hx).1)).toT

/-- The run of a kept dynamic hint under `%next (ofSure sur) th` when
`+past-if` emits nothing (the text of `runLCH_n11d_kept_next`). -/
'''

MID3 = '''

/-- **A kept dynamic `stopTag` hint over a member of `SurGBT A` is in
`SurGBT (A ∧ SoundK ∧ FitP)`** (the text of `regGBT_n11dKept`, the goal
`%next (ofSure sur) th`, the fit of `frameOK_goesR` from `FitP`). -/
'''

TAIL = '''

end Kept

/-! ## `[7 p q]` under `%done` -/

section Seq
variable {snd : Nomm → NeedOrd → Bool}

/-- **`[7 p q]` under `%done` with `p` in `SurGBT Ap`**: `q` with `DoneAllT`,
its result without entries and with `Ap` of its sure need (`hq`); the
result `RunOKGBT` at `%done` (`runOKGBT_sevenG`). -/
theorem surSeven_done (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {b c : Noun} {p q : Nomm}
    {Ap : Sure S → Prop} (Hp : SurGBT (S := S) (Map := Map) snd lib N env P Ap b p)
    (Hq : DoneAllT (S := S) (Map := Map) lib N env snd (Img lib P b) c q)
    (hq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLCH (S := S) (Map := Map) env snd true sup q CGoalL.done region g0 = some (nx, g1) →
      entries nx.laz = [] ∧ Ap nx.laz.sure)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n7 p q) CGoalL.done region g0 = some (nex, g1)) :
    RunOKGBT lib N P (n3 (A 7) b c) CGoal.done g0 g1 nex := by
  rw [runLCH_n7] at hr
  obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
  have D := Hq b0 d0 hu hcl hcb h1
  have Rq := D.run
  obtain ⟨hne, hA⟩ := hq h1
  have hj : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  have h2' : runLCH (S := S) (Map := Map) env snd true sup p (CGoalL.next (ofSure nx.laz.sure) nx.th) region ga =
      some (nex, g1) := by
    rw [← eq_ofSure_of_entries hne]; exact h2
  have Rp := Hp hA (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow)
    (Rq.cfr.below hcb) Rq.lo Rq.hi hj Rq.dist D.clean
    (fun x hx => ⟨by
      rcases Rq.regs x hx with e | e
      · exact e.elim
      · exact e.2, Rq.ncond x hx⟩) h2'
  exact runOKGBT_sevenG (minkC7_seven lib P b c) Rq hne Rp (fun r hr => hr.elim)

/-- **The contract at the top of `[7 p q]` with `p` in `SurGBT Ap`**, traces
included. -/
theorem finishLUCH_contractSurSeven (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {b c : Noun}
    {p q : Nomm} {Ap : Sure S → Prop} (Hp : SurGBT (S := S) (Map := Map) snd lib N env P Ap b p)
    (Hq : DoneAllT (S := S) (Map := Map) lib N env snd (Img lib P b) c q)
    (hq : ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nx : NextL S},
      runLCH (S := S) (Map := Map) env snd true sup q CGoalL.done region g0 = some (nx, g1) →
      entries nx.laz = [] ∧ Ap nx.laz.sure)
    {cc : Straight Map} (hc : finishLUCH (S := S) env snd (Nomm.n7 p q) = some cc) :
    cc.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s (n3 (A 7) b c) [s] cc ∧
      ContractBwd lib N s (n3 (A 7) b c) [s] cc :=
  finishLUCH_contractGBT lib N
    (fun hr => surSeven_done lib Hp Hq hq (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc

end Seq

end Comp
end SkaModel
end Formalization
'''

open(OUT, 'w').write(HEAD + SEVEN + MID1 + FRAME + MID2 + RUNS + MID3 + KEPT + TAIL)
print('wrote', OUT)
