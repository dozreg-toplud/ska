#!/usr/bin/env python3
"""Write lemmas/Ska/CompSixNxS.lean: phase S of `[6 c a b]` under `%next`
with parts that call (README Gaps 12.36).  `sixNextSimpleC_apart` is the
text of `sixNextSimple_apart` (CompSixNext.lean) for `sixNextSimpleC cod`,
with `+past-fork` of the code table `cod` in place of `pastFork_pure`."""
import os
root = os.path.join(os.path.dirname(__file__), '..', '..')
s = open(os.path.join(root, 'lemmas/Ska/CompSixNext.lean')).read()
a = s.index('/-- **`sixNextSimple` taken apart.** -/'); b = s.index('end Comp', a)
t = s[a:b].rstrip() + '\n'
reps = [
 ('/-- **`sixNextSimple` taken apart.** -/', '/-- **`sixNextSimpleC` taken apart** (generated from `sixNextSimple_apart`). -/'),
 ('theorem sixNextSimple_apart {rp', 'theorem sixNextSimpleC_apart {cod : Bell → Option Bool} {rp'),
 ('    (hp : p.pure = true) {laz', '    {laz'),
 ('(h : sixNextSimple rp rq rr p laz', '(h : sixNextSimpleC cod rp rq rr p laz'),
 ('    ∃ (s0 s1 : Sure S) (x1 x0 xc : NextL S) (lz : Lazy S)', '    ∃ (s0 s1 : Sure S) (x1 x0 xc : NextL S) (lz lw : Lazy S)'),
 ('      rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region gS = some (xc, gC) ∧\n      (lazyBig lz = false → copyL xc lz gC = some (nex, g9)) := by',
  '      pastFork cod lz p = some lw ∧\n      rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region gS = some (xc, gC) ∧\n      (lazyBig lw = false → copyL xc lw gC = some (nex, g9)) := by'),
 ('  simp only [sixNextSimple] at h', '  simp only [sixNextSimpleC] at h'),
 ('  simp only [liftO, pastFork_pure _ _ hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP\n  obtain ⟨rfl, rfl⟩ := hP',
  '  simp only [liftO] at hP\n  obtain ⟨lw, hw, hP⟩ := Option.map_eq_some_iff.mp hP\n  simp only [Prod.mk.injEq] at hP\n  obtain ⟨rfl, rfl⟩ := hP'),
 ('  refine ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, fun hbig => ?_⟩',
  '  refine ⟨s0, s1, x1, x0, xc, lz, lw, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hw, hC, fun hbig => ?_⟩'),
]
for x, y in reps:
    assert t.count(x) == 1, x
    t = t.replace(x, y)
head = '''import lemmas.Ska.CompSixNxRel
import lemmas.Ska.CompSixNext
import lemmas.Ska.CompSixFuel
import lemmas.Ska.CompTagU

/-!
# `[6 c a b]` under `%next`, phase S: the pieces (generated in part)

README Gaps 12.36.  Written by `tools/gen/sixnxs.py`; do not edit by hand.
Phase S is the goal whose entries ask nothing; under a goal with no entry it
is the only phase (`sixNextLC_fork_free`).

* `sixNextSimpleC_apart`: the run taken apart (the text of
  `sixNextSimple_apart` with `+past-fork` of `cod`).
* `runLC_six_nextE`: at a goal with no entry `%6` is `sixNextSimpleC`.
* `TagLS`: every key a run under a goal with no entry adds to `cond` has a
  tag with its region as a suffix (what `+sect` needs of the branches to
  thread nothing, `sect_specV` through `sect_h0`, `sect_h1`), checked on the
  branches in `CompSixNxCheck.lean`; `sect_specS`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

'''
tail = '''
/-- **At a goal with no entry, `%6` is phase S.** -/
theorem runLC_six_nextE (env : CallEnv) (sup : Option Nomm) (c a b : Nomm) {L : Lazy S} (he : entries L = [])
    (th : Jmp) (region : List Nat) :
    (runLC env sup (Nomm.n6 c a b) (CGoalL.next L th) region : CM Map (NextL S)) =
      sixNextSimpleC env.cod (runLC env sup c) (runLC env sup a) (runLC env sup b) c L th region := by
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
  simp only [runLC]
  exact sixNextLC_fork_free env.cod _ _ _ c a b 2 L.sure th region

/-- **The tag clause of a run under a goal with no entry**: every key it adds
to `cond` has a tag with its region as a suffix. -/
abbrev TagLS (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → CondTag region g0.cond g1.cond

/-- **`+sect` of phase S threads nothing** when both branches meet the tag
clause from the states the run gives them (`sect_specV`). -/
theorem sect_specS {nex0 nex1 : NextL S} {o0 o1 rid : Nat} {region : List Nat} {cb cw : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat} (hd : g.drop = false)
    (t1 : CondTag (rid :: region) cb cw) (t0 : CondTag (rid :: region) cw g.cond)
    (h : sect nex0 nex1 o0 o1 (rid :: region) cb cw g = some ((lz, yes, nuh), g')) :
    yes = g.bo ∧ nuh = g.bo + 1 ∧ nex0.th.args = [] ∧ nex1.th.args = [] ∧
    lz = mk Sure.bunt [((g.bo, nex0.laz), (g.bo + 1, nex1.laz))] [] ∧
    SameBlocks (sixGenL g nex0.th nex1.th (rid :: region)) g' :=
  sect_specV hd (sect_h0 t0) (sect_h1 t1) h

end Comp
end SkaModel
end Formalization
'''
open(os.path.join(root, 'lemmas/Ska/CompSixNxS.lean'), 'w').write(head + t + tail)
print('ok')
