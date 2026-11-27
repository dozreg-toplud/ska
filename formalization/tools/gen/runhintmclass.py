"""The class with `%mean` (README Gaps 25): writes
`lemmas/Compiler/CompRunHintMeanClass.lean` from `CompRunHintCall.lean` (from `def
HintOkC` to its end) and `CompRunHintTab.lean` (from `theorem hintSound_of_tab` to
its end), every name `nC` as `nM` (`comp_run_hint_ana` as `comp_run_hint_anaM`, ...),
`HintSoundC ctx snd` as `HintSoundM env ctx snd`, and the case `%mean` added to each
definition and induction.  Counts asserted.

    python3 tools/gen/runhintmclass.py
"""
import re, os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
call = open(os.path.join(D, 'lemmas/Compiler/CompRunHintCall.lean')).read()
tab = open(os.path.join(D, 'lemmas/Compiler/CompRunHintTab.lean')).read()

def cut(s, start, end):
    i = s.index(start); j = s.rindex(end)
    return s[i:j]

body = cut(call, '/-- `HintOk` whose direct calls', 'end Compiler') if '/-- `HintOk` whose direct calls' in call \
    else cut(call, 'def HintOkC', 'end Compiler')
tb = cut(tab, '/-- **`HintSoundC` from a closed table**', 'end Compiler')
src = body + tb

ren = [('HintOkC', 'HintOkM', None), ('HintCallsC', 'HintCallsM', None), ('HintSoundC ctx snd', 'HintSoundM env ctx snd', None),
       ('HintSoundC ctx (sfSnd cod)', 'HintSoundM env ctx (sfSnd cod)', None), ('HintSoundC', 'HintSoundM', None),
       ('callCode_of_hintC', 'callCode_of_hintM', None), ('noAx0_of_hintC', 'noAx0_of_hintM', None),
       ('comp_run_hintC', 'comp_run_hintM', None), ('hintSound_of_tab', 'hintSound_of_tabM', None),
       ('entries_of_calls', 'entries_of_callsM', None), ('comp_run_hint_tab', 'comp_run_hint_tabM', None),
       ('comp_run_hint_anaX', 'comp_run_hint_anaXM', None), ('comp_run_hint_ana ', 'comp_run_hint_anaM ', None)]
for a, b, _ in ren:
    assert a in src, a
    src = src.replace(a, b)

def sub1(a, b):
    global src
    assert src.count(a) == 1, (src.count(a), a)
    src = src.replace(a, b)

# the definitions
sub1("  | Nomm.n12 p q => HintOkM p && HintOkM q\n  | _ => false",
     "  | Nomm.n12 p q => HintOkM p && HintOkM q\n  | Nomm.mean p _ q _ _ => HintOkM p && HintOkM q\n  | _ => false")
sub1("  | ms, Nomm.n12 p q => HintCallsM env cod ctx E ms p ∧ HintCallsM env cod ctx E ms q\n  | _, _ => True",
     "  | ms, Nomm.n12 p q => HintCallsM env cod ctx E ms p ∧ HintCallsM env cod ctx E ms q\n"
     "  | ms, Nomm.mean p b q _ k =>\n"
     "      (k.isSome = true → CodePure cod env b) ∧ HintCallsM env cod ctx E ms p ∧ HintCallsM env cod ctx E ms q\n"
     "  | _, _ => True")
sub1("def HintSoundM (ctx : Noun)", "def HintSoundM (env : CallEnv) (ctx : Noun)")
sub1("  | Nomm.n12 p q => HintSoundM env ctx snd p ∧ HintSoundM env ctx snd q\n  | _ => True",
     "  | Nomm.n12 p q => HintSoundM env ctx snd p ∧ HintSoundM env ctx snd q\n"
     "  | Nomm.mean p b q _ k => SoundAt ctx snd q ∧ SoundAt ctx snd p ∧\n"
     "      ((meanKonst env b k).isSome = true → snd p NeedOrd.none = true) ∧\n"
     "      HintSoundM env ctx snd p ∧ HintSoundM env ctx snd q\n"
     "  | _ => True")
# callCode, noAx0
sub1("  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [HintOkM] at h",
     "  | Nomm.mean _ _ _ _ _, _, _, _ => by simp only [CallCode]")
sub1("  | Nomm.mean _ _ _ _ _, h => by simp [HintOkM] at h",
     "  | Nomm.mean p _ q _ _, h => by\n"
     "    simp only [HintOkM, Bool.and_eq_true] at h; exact ⟨noAx0_of_hintM p h.1, noAx0_of_hintM q h.2⟩")
# the link
sub1("  | Nomm.mean _ _ _ _ _, h, _, _, _, hs => by simp [HintOkM] at h",
     "  | Nomm.mean p b q body k, h, msup, region, hd, hs => by\n"
     "    simp only [HintOkM, Bool.and_eq_true] at h; simp only [HintCallsM] at hd; simp only [HintSoundM] at hs\n"
     "    have P := comp_run_hintM h7 hcode env snd E p h.1 msup region hd.2.1 hs.2.2.2.1\n"
     "    have Q := comp_run_hintM h7 hcode env snd E q h.2 msup region hd.2.2 hs.2.2.2.2\n"
     "    exact partH_mean h7 hcode b body k hd.1 P Q hs.1 hs.2.1 hs.2.2.1 (callCode_of_hintM p h.1 msup hd.2.1)\n"
     "      (callCode_of_hintM q h.2 msup hd.2.2)")
# the table
sub1("  | Nomm.mean _ _ _ _ _, _, _ => by simp only [HintSoundM]",
     "  | Nomm.mean p b q _ k, ha, hb => by\n"
     "    simp only [Bake.NoAx0] at ha; simp only [hintBells, List.mem_append] at hb; simp only [HintSoundM]\n"
     "    exact ⟨soundAt_tab h7 hcode ht ha.2 fun b m => hb b (Or.inr m),\n"
     "      soundAt_tab h7 hcode ht ha.1 fun b m => hb b (Or.inl m), fun _ => sfSnd_none cod p,\n"
     "      hintSound_of_tabM h7 hcode ht p ha.1 fun b m => hb b (Or.inl m),\n"
     "      hintSound_of_tabM h7 hcode ht q ha.2 fun b m => hb b (Or.inr m)⟩")
sub1("  | Nomm.mean _ _ _ _ _, h, _, _, _, _ => by simp [HintOkM] at h",
     "  | Nomm.mean p _ q _ _, h, ms, hc, b, hb => by\n"
     "    simp only [HintOkM, Bool.and_eq_true] at h; simp only [HintCallsM] at hc\n"
     "    simp only [hintBells, List.mem_append] at hb\n"
     "    exact hb.elim (entries_of_callsM hana p h.1 ms hc.2.1 b) (entries_of_callsM hana q h.2 ms hc.2.2 b)")
assert src.count('theorem ') == 8, src.count('theorem ')
head = '''import lemmas.Compiler.CompRunHintMeanP

/-!
# The run link with hints and `%mean`: the class `HintOkM` (README Gaps 25)

Generated by `tools/gen/runhintmclass.py` from `CompRunHintCall.lean` and
`CompRunHintTab.lean`: `HintOkC` with `[%mean p b q body k]` (parts in the
class), `HintCallsM` (also the code entry of `b` when `k` is `some`),
`HintSoundM` (also `SoundAt` of `q` and `p` under a `%mean`, and `snd p
[%none ~]` on a constant), every name `nC` as `nM`.

* **`comp_run_hintM`**: every member of `HintOkM` is a `PartH` at `XM E
  msup` (the case `%mean` by `partH_mean`).
* `sfSnd_none`, **`hintSound_of_tabM`**, `entries_of_callsM`,
  **`comp_run_hint_tabM`**, **`comp_run_hint_anaM`**, `comp_run_hint_anaXM`:
  `HintSoundM` from the code table, as in `CompRunHintTab.lean`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- `+sound-far` of `[%none ~]` is `&`. -/
theorem sfSnd_none (cod : Noun) (n : Nomm) : sfSnd cod n NeedOrd.none = true := by
  cases n <;> simp [sfSnd, soundFar, sfAt]

'''
open(os.path.join(D, 'lemmas/Compiler/CompRunHintMeanClass.lean'), 'w').write(head + src + 'end Compiler\nend Formalization\n')
print('ok')
