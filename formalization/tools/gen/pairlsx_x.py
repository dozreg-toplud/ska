D = 'lemmas/Ska/'


def rep(t, o, n, k=1):
    assert t.count(o) == k, (o, t.count(o))
    return t.replace(o, n)


def xsec(sec):
    sec = rep(sec, '{nexq nexp : NextL S} {n : Next S}', '{nexq nexp : NextL S} {n : Next S} {x xp xq : Bool} {HW : Need}')
    sec = rep(sec, '(hq : RunOKLS (Map := Map) lib N P ft tel jt Qt false gb g1 nexq)',
              '(hq : RunOKLS (Map := Map) lib N P ft tel jt Qt xq gb g1 nexq)')
    sec = rep(sec, '(hp : RunOKLS (Map := Map) lib N P fh Lh nexq.th Qh false g1 g2 nexp)',
              '(hp : RunOKLS (Map := Map) lib N P fh Lh nexq.th Qh xp g1 g2 nexp)')
    sec = rep(sec, 'GoalSemCM lib O c gul Inv ν (Keep g0 g\' (CGoal.next L.sure th)) st regs t tm (jmp0 o) (CGoal.next L.sure th) r',
              'GoalSemCM lib O c gul Inv ν (fun z => Keep g0 g\' (CGoal.next L.sure th) z ∨ NMem HW z) st regs t tm (jmp0 o)\n          (CGoal.next L.sure th) r', 2)
    extra = '''    -- the halves in the witness and the parts' goal registers (README Gaps 12.32)
    (hHr : ∀ z, NMem HW z → g0.re ≤ z ∧ z < g'.re)
    (hHh : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN hed.sure.ned R a → HoldsN tel.sure.ned R b →
      HoldsN HW R (C a b))
    (hEH : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN (gsE x L) R (C a b) → HoldsN HW R (C a b) →
      HoldsN (gsE xp Lh) R a ∧ HoldsN (gsE xq tel) R b)
    (hG : ∀ e ∈ L.bond, ∀ z, NMem L.sure.ned z → ¬ NMem e.2.sure.ned z)
    (hPH : ∀ e ∈ L.bond, ∀ e1 ∈ nexp.laz.bond ++ nexq.laz.bond, e1.1 = e.1 → ∀ z,
      (NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z) → ¬ NMem e1.2.sure.ned z)
include'''
    sec = rep(sec, '\ninclude', '\n' + extra)
    sec = rep(sec, 'hnotF hnotB hA hAB', 'hnotF hnotB hA hAB hHr hHh hEH hG hPH')
    return sec


PRE = '''set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

'''
POST = '\nend\n\nend Comp\nend SkaModel\nend Formalization\n'

# ---- core
src = open(D + 'CompPairLSCore.lean').read()
v = src.index('variable {lib : Lib} {N : Needs} {P : Noun → Prop}')
a = src.rindex('section', 0, v)
c = src.index('theorem pairLS_core ')
c0 = src.rindex('/--', 0, c)
sec = xsec(src[a:c0])
d = src.index('\nend\n', c)
core = src[c0:d]
core = rep(core, 'theorem pairLS_core ', 'theorem pairLSX_core ')
core = rep(core, '(gsE false Lh)', '(gsE xp Lh)', 2)
core = rep(core, "have hn3' : HoldsN (Need.pair (Need.pair ned d) (gsE xp Lh)) R3 (C (C s0 w) x) := ⟨hn3, trivial⟩",
           "have hn3' : HoldsN (Need.pair (Need.pair ned d) (gsE xp Lh)) R3 (C (C s0 w) x) :=\n"
           "      ⟨hn3, by rw [hLe]; cases xp <;> trivial⟩")
hdr = '''import lemmas.Ska.CompPairLSXFronts

/-!
# A pair of runs under a flat lazy goal, parts of any flag: the shared part

README Gaps 12.32.  `pairLS_core` (`CompPairLSCore.lean`) with the section of
`CompPairLSXFronts.lean` (the parts' flags `xp`, `xq`, the halves `HW`).  The
one change in the proof: the head's front at the park block reads the goal
registers `gsE xp Lh`, which ask nothing there (the parked goal's sure part
is the bunt).
-/

'''
open(D + 'CompPairLSXCore.lean', 'w').write(hdr + PRE + sec + core + POST)

# ---- sem
src = open(D + 'CompPairLSSem.lean').read()
v = src.index('variable {lib : Lib} {N : Needs} {P : Noun → Prop}')
a = src.rindex('section', 0, v)
c0 = src.index('/-- The forward `sem` clause of `pairLS_ok`. -/')
sec = xsec(src[a:c0])
c1 = src.index('theorem pairLS_fronts ')
c1 = src.rindex('/--', 0, c1)
sem = src[c0:c1]
sem = rep(sem, 'theorem pairLS_sem ', 'theorem pairLSX_sem ')
sem = rep(sem, 'theorem pairLS_semB ', 'theorem pairLSX_semB ')
sem = rep(sem, '(pairWit C Qh Qt) g0 g3', '(pairWitX C HW Qh Qt) g0 g3', 2)
for ind in ['        ', '            ']:
    i2 = ind + '  '
    old = (ind + 'have AD := goalSemCMD_of_CM (Q := pairWit C Qh Qt s) (d := Need.pair d dq) (w := C w wq)\n' +
           i2 + '(fun z hz => by\n' +
           i2 + '  rcases hz with hz | hz\n' +
           i2 + '  · have := hp.dreg s x d w z hqd hz\n' +
           i2 + '    exact ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩\n' +
           i2 + '  · have := hq.dreg s y dq wq z hqq hz\n' +
           i2 + '    exact ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩)\n' +
           i2 + '⟨hdp4, hdq4⟩ (fun p hp\' => by\n')
    new = (ind + 'have AD := goalSemCMD_of_CM (Q := pairWitX C HW Qh Qt s) (d := Need.pair HW (Need.pair d dq))\n' +
           i2 + '(w := C (C x y) (C w wq))\n' +
           i2 + '(fun z hz => by\n' +
           i2 + '  rcases hz with hz | hz | hz\n' +
           i2 + '  · exact Or.inr hz\n' +
           i2 + '  · have := hp.dreg s x d w z hqd hz\n' +
           i2 + '    exact Or.inl ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩\n' +
           i2 + '  · have := hq.dreg s y dq wq z hqq hz\n' +
           i2 + '    exact Or.inl ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩)\n' +
           i2 + '⟨hHh R4 x y hx4 hy4, hdp4, hdq4⟩ (fun p hp\' => by\n')
    sem = rep(sem, old, new)
sem = rep(sem, "(AD.mono (fun z hz => ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) (fun _ _ _ h => h))",
          "(AD.mono (fun z hz => Or.inl ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) (fun _ _ _ h => h))", 2)
hdr = '''import lemmas.Ska.CompPairLSXCore

/-!
# A pair of runs under a flat lazy goal, parts of any flag: the `sem` clauses

README Gaps 12.32.  `pairLS_sem`, `pairLS_semB` (`CompPairLSSem.lean`) with
the section of `CompPairLSXFronts.lean` and the witness `pairWitX C HW`: at
the jump to the block `o` the halves hold the parts' products (`hHh`), and
the block `o` keeps them (`hA`, `hAB` with `Keep … ∨ NMem HW`).
-/

'''
open(D + 'CompPairLSXSem.lean', 'w').write(hdr + PRE + sec + sem.rstrip() + '\n' + POST)
print('ok')
