#!/usr/bin/env python3
"""Generate `lemmas/Ska/CompHintSurOps.lean` (README Gaps 24.21): the `SurGBT`
texts of the kept static hint (`regGBT_n11sKept`) and of the quiet kept dynamic
tag (`regGBT_n11dQuiet`), `CompHintRegKeep.lean`.  Run from `formalization/`.

The replacements are those of `tools/gen/hintsur.py` for `surGBT_n11dKept`:
the goal `%next (ofSure sur) th`, `sur` in `Ap ∧ SoundK` (`+past-if` emits
nothing), the formula in `SurGBT Ap`.  Neither frame asks a fit of the
formula's products (the static epilogue and the quiet frame are hops at the
same trace, `quietGoal`, `frameOKQ_goes`), so no `FitP`.
"""
import re, sys

OUT = 'lemmas/Ska/CompHintSurOps.lean'
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


def check(t, name):
    if re.search(r'\brg\b|hsnd|hr0|hc0', t):
        sys.exit(f'rg/hsnd/hr0/hc0 left in {name}: ' + str(re.findall(r'.{30}(?:\brg\b|hsnd|hr0|hc0).{30}', t)))


# runLCH_n11s_kept_sur
t = grab('lemmas/Ska/CompHintRegKeep.lean', 'runLCH_n11s_kept_next')
t = rep(t, 'theorem runLCH_n11s_kept_next ', 'theorem runLCH_n11s_kept_sur ', 1)
t = rep(t, '(hsnd : snd q NeedOrd.this = true) {sup : Option Nomm} {rg : Nat}',
        '{sur : Sure S} (hp : HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true) {sup : Option Nomm}', 1)
t = rep(t, '(ofSure (lazyReg rg))', '(ofSure sur)', 2)
t = rep(t, '''have hp : HoonSet.small (ofSure (lazyReg rg) : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure (lazyReg rg) : Lazy S).sure.ned) = true :=
    ⟨(HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x), hsnd⟩''', '''have hp' : HoonSet.small (ofSure sur : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure sur : Lazy S).sure.ned) = true := hp''', 1)
t = rep(t, 'rw [if_pos hp] at h1', "rw [if_pos hp'] at h1", 1)
check(t, 'runLCH_n11s_kept_sur')
RUNS = t

# surGBT_n11sKept
t = grab('lemmas/Ska/CompHintRegKeep.lean', 'regGBT_n11sKept')
t = rep(t, 'theorem regGBT_n11sKept ', 'theorem surGBT_n11sKept ', 1)
t = rep(t, '(Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)',
        '{Ap : Sure S → Prop} (Hq : SurGBT (S := S) (Map := Map) snd lib N env P Ap fq q)', 1)
t = rep(t, 'RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 11) (A tag) fq) (Nomm.n11s tag q body) := by',
        'SurGBT (S := S) (Map := Map) snd lib N env P (fun sur => Ap sur ∧ SoundK snd q sur)\n      (n3 (A 11) (A tag) fq) (Nomm.n11s tag q body) := by', 1)
t = rep(t, 'intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr',
        'intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr', 1)
t = rep(t, 'runLCH_n11s_kept_next hs hsnd hr', 'runLCH_n11s_kept_sur hs hA.2 hr', 1)
t = rep(t, '''have RQ := Hq (by simp only [Gen.emitted]; omega)''', '''have RQ := Hq hA.1 (by simp only [Gen.emitted]; omega)''', 1)
t = rep(t, '''(by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl (by simp only [Gen.emitted]; omega)
    (by simp only [Gen.emitted]; exact hc0) h3''', '''(by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted]; omega) rfl hsd hcs
    (fun x hx => ⟨by have := (hsl x hx).1; simp only [Gen.emitted]; omega, by simp only [Gen.emitted]; exact (hsl x hx).2⟩) h3''', 1)
t = rep(t, 'RQ.bound (fun x hx => by simp only [lazyReg, NMem] at hx; simp only [Gen.emitted]; omega)',
        'RQ.bound (fun x hx => by have := (hsl x hx).1; simp only [Gen.emitted]; omega)', 1)
check(t, 'surGBT_n11sKept')
STATIC = t

# surGBT_n11dQuiet
t = grab('lemmas/Ska/CompHintRegKeep.lean', 'regGBT_n11dQuiet')
t = rep(t, 'theorem regGBT_n11dQuiet ', 'theorem surGBT_n11dQuiet ', 1)
t = rep(t, '(Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)',
        '{Ap : Sure S → Prop} (Hq : SurGBT (S := S) (Map := Map) snd lib N env P Ap fq q)', 1)
t = rep(t, 'RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 11) (C (A tag) fh) fq) (Nomm.n11d tag h q body) := by',
        'SurGBT (S := S) (Map := Map) snd lib N env P (fun sur => Ap sur ∧ SoundK snd q sur)\n      (n3 (A 11) (C (A tag) fh) fq) (Nomm.n11d tag h q body) := by', 1)
t = rep(t, 'intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr',
        'intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr', 1)
t = rep(t, 'runLCH_n11d_kept_next hs hsnd hr', 'runLCH_n11d_kept_sur hs hA.2 hr', 1)
t = rep(t, '''have RQ := Hq (by rw [boA]; omega) dA uA clA cbA (by simp only [jmp0]; omega) (by simp only [jmp0]; rw [boA]; omega)
    rfl (by rw [reA]; omega) (by simp only [genN, Gen.emitted]; exact hc0) h3''', '''have RQ := Hq hA.1 (by rw [boA]; omega) dA uA clA cbA (by simp only [jmp0]; omega)
    (by simp only [jmp0]; rw [boA]; omega) rfl hsd hcs
    (fun x hx => ⟨by have := (hsl x hx).1; rw [reA]; omega, by simp only [genN, Gen.emitted]; exact (hsl x hx).2⟩) h3''', 1)
t = rep(t, 'RQ.bound (fun x hx => by simp only [lazyReg, NMem] at hx; rw [reA]; omega)',
        'RQ.bound (fun x hx => by have := (hsl x hx).1; rw [reA]; omega)', 1)
t = rep(t, '(lazyReg rg : Sure S)', 'sur', 3)
check(t, 'surGBT_n11dQuiet')
QUIET = t


# surGBT_four, surGBT_three: the goal `RegLike` (a `this` need, an empty lock)
PRE = """intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr
  obtain ⟨rg, hk, hl⟩ := hA
  rcases sur with ⟨ned, lok⟩
  simp only at hk hl
  subst hk
  have hr0 : rg < g0.re := (hsl rg rfl).1
  have hc0 : HoonMap.get g0.cond rg = Option.none := (hsl rg rfl).2"""
t = grab('lemmas/Ska/CompHintRegOps.lean', 'regGBT_four')
t = rep(t, 'theorem regGBT_four ', 'theorem surGBT_four ', 1)
t = rep(t, 'RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n4 p) := by',
        'SurGBT (S := S) (Map := Map) snd lib N env P RegLike f (Nomm.n4 p) := by', 1)
t = rep(t, 'intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr', PRE, 1)
t = rep(t, 'collapseL_lazyReg hta g0 d0', 'collapseL_regLike hl hta g0 d0', 1)
t = rep(t, 'fitsS_lazyReg _ _', 'fitsS_regLikeT hl _', 1)
FOUR = t
t = grab('lemmas/Ska/CompHintRegOps.lean', 'regGBT_three')
t = rep(t, 'theorem regGBT_three ', 'theorem surGBT_three ', 1)
t = rep(t, 'RegGBT (S := S) (Map := Map) snd lib N env P f (Nomm.n3 p) := by',
        'SurGBT (S := S) (Map := Map) snd lib N env P RegLike f (Nomm.n3 p) := by', 1)
t = rep(t, 'intro sup rg th region g0 g1 nex b0 d0 hu hcl hcb th1 th2 hta hr0 hc0 hr', PRE, 1)
t = rep(t, 'collapseL_lazyReg hta g0 d0', 'collapseL_regLike hl hta g0 d0', 1)
t = rep(t, 'fitsS_lazyReg _ _', 'fitsS_regLikeT hl _', 2)
t = rep(t, '(lazyReg rg : Sure S)', '(⟨Need.this rg, lok⟩ : Sure S)', 2)
t = rep(t, 'simp [noneEquivalent, lazyReg]', 'simp [noneEquivalent]', 1)
THREE = t
if 'lazyReg rg' in FOUR + THREE:
    sys.exit('lazyReg rg left in surGBT_four/three')

UNARY = """

/-- `+collapse-lazy-atom` of a `this` need with an empty lock is `(r,
th.there)`, the state unchanged (the text of `collapseL_lazyReg`). -/
theorem collapseL_regLike {rg : Nat} {lok : S} (hl : HoonSet.toList lok = []) {th : Jmp} (hta : th.args = [])
    (g : Gen Map) (d0 : g.drop = false) :
    collapseLazyAtomL (S := S) ⟨ofSure ⟨Need.this rg, lok⟩, th⟩ g = some (some (rg, th.there), g) := by
  have hne : noneEquivalentL (ofSure (⟨Need.this rg, lok⟩ : Sure S)) = false := by
    rw [noneEquivalentL_ofSure]; simp [noneEquivalent]
  unfold collapseLazyAtomL
  simp only [hta, ne_eq, not_true_eq_false, if_false, hne, Bool.false_eq_true]
  simp [sureRequireLook, ofSure, hl, bind_apply, pure_apply, walkLazy, collapseGate]
  rfl

/-- Every noun fits a `this` need with an empty lock. -/
theorem fitsS_regLikeT {rg : Nat} {lok : S} (hl : HoonSet.toList lok = []) (x : Noun) :
    FitsS (⟨Need.this rg, lok⟩ : Sure S) x :=
  ⟨trivial, fun a ha => absurd ha (by rw [hl]; exact List.not_mem_nil)⟩

/-- **`[4 p]` under `%next (ofSure sur) th`, `sur` `RegLike`, over a member
of `RegGBT`** (the text of `regGBT_four`: the operand runs under `%next
(lazy-from-reg a)` of a fresh `a`, the increment writes the goal's
register). -/
"""
MID3 = """

/-- **`[3 p]` under `%next (ofSure sur) th`, `sur` `RegLike`, over a member
of `RegGBT`** (the text of `regGBT_three`). -/
"""

HEAD = '''import lemmas.Ska.CompHintSur
import lemmas.Ska.CompHintDirectReg

/-!
# Kept static hints and quiet kept dynamic tags in `SurGBT` (README Gaps 24.21)

Generated by `tools/gen/hintsurops.py` (do not edit).  The texts of
`runLCH_n11s_kept_next`, `regGBT_n11sKept`, `regGBT_n11dQuiet`
(`CompHintRegKeep.lean`) under the goal `%next (ofSure sur) th`, with the
replacements `tools/gen/hintsur.py` makes for `surGBT_n11dKept`: `sur` in
`Ap ∧ SoundK` (`+past-if` emits nothing), the formula in `SurGBT Ap`.  The
static epilogue and the quiet frame are hops at the hint's own trace
(`RunOKGBT.quietGoal`, `frameOKQ_goes`, both for any `sur`), so neither asks
a fit of the formula's products: no `FitP` (unlike `surGBT_n11dKept`).

* `runLCH_n11s_kept_sur`: the run of a kept static hint under `%next (ofSure
  sur) th` when `+past-if` emits nothing.
* **`surGBT_n11sKept`**: a kept static hint over a member of `SurGBT Ap` is
  in `SurGBT (Ap ∧ SoundK)`.
* **`surGBT_n11dQuiet`**: a kept dynamic tag that is not `stopTag`, likewise.
* `collapseL_regLike`, `fitsS_regLikeT`; **`surGBT_four`**, **`surGBT_three`**: the
  texts of `regGBT_four`, `regGBT_three` at the goal `RegLike` (a `this` need,
  its lock with no element: `+collapse-lazy-atom` is then as for
  `lazy-from-reg`), the operand in `RegGBT`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section Ops
variable {snd : Nomm → NeedOrd → Bool}

/-- The run of a kept static hint under `%next (ofSure sur) th` when
`+past-if` emits nothing (the text of `runLCH_n11s_kept_next`). -/
'''

MID1 = '''

/-- **A kept static hint over a member of `SurGBT Ap` is in `SurGBT (Ap ∧
SoundK)`** (the text of `regGBT_n11sKept`, the goal `%next (ofSure sur)
th`). -/
'''

MID2 = '''

/-- **A kept dynamic tag that is not `stopTag` over a member of `SurGBT Ap`
is in `SurGBT (Ap ∧ SoundK)`** (the text of `regGBT_n11dQuiet`, the goal
`%next (ofSure sur) th`; the quiet frame asks no fit). -/
'''

TAIL = '''

end Ops

end Comp
end SkaModel
end Formalization
'''

open(OUT, 'w').write(HEAD + RUNS + MID1 + STATIC + MID2 + QUIET + UNARY + FOUR + MID3 + THREE + TAIL)
print('wrote', OUT)
