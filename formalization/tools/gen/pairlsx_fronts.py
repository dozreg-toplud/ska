D = 'lemmas/Ska/'
src = open(D + 'CompPairLSSem.lean').read()
a = src.index('section\n\nvariable {lib : Lib}')
b = src.index('/-- The forward `sem` clause of `pairLS_ok`. -/')
sec = src[a:b]
c = src.index('theorem pairLS_fronts ')
c0 = src.rindex('/--', 0, c)
d = src.index('\nend\n', c)
fr = src[c0:d]


def rep(t, o, n, k=1):
    assert t.count(o) == k, (o, t.count(o))
    return t.replace(o, n)


# the section: flags, halves, K' in hA/hAB, new hypotheses
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

fr = rep(fr, 'theorem pairLS_fronts ', 'theorem pairLSX_fronts ')
fr = rep(fr, '    FrontsS (Map := Map) (pairWit C Qh Qt) false g0 g3 L (pairRes n r nexq.laz.bond nexp.laz.bond) := by',
         '    FrontsS (Map := Map) (pairWitX C HW Qh Qt) x g0 g3 L (pairRes n r nexq.laz.bond nexp.laz.bond) := by')
fr = rep(fr, 'FrontS (Map := Map) Qt Need.none gb.re g1.re Lq', 'FrontS (Map := Map) Qt (gsE xq tel) gb.re g1.re Lq')
fr = rep(fr, 'FrontS (Map := Map) Qh Need.none g1.re g2.re Lp', 'FrontS (Map := Map) Qh (gsE xp Lh) g1.re g2.re Lp')
old = '''    have F1 := frontS_pair (comb := C) FPs FQs (lo0 := g0.re) (lo := g3.re) (Lb := e.2.sure) (Fs := PB e.1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun s v d w x hq' hx => hp.dreg s v d w x hq' hx) (fun s v d w x hq' hx => hq.dreg s v d w x hq' hx)
      hLh' hLt' SA.ht hM1 hM2 hM3 hM4 SA.fit SA.sem'''
new = '''    -- the parts' entries at the label are apart from the halves and the goals' registers
    have nP : ∀ z, (NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z) →
        ¬ NMem Lp.ned z ∧ ¬ NMem Lq.ned z := fun z hz => by
      refine ⟨fun hm => ?_, fun hm => ?_⟩
      · rcases mp' with h1 | ⟨_, rfl⟩
        · exact hPH e he _ (List.mem_append_left _ h1) rfl z hz (by simpa [ofSure] using hm)
        · simp [Sure.bunt, NMem] at hm
      · rcases mq' with h1 | ⟨_, rfl⟩
        · exact hPH e he _ (List.mem_append_right _ h1) rfl z hz (by simpa [ofSure] using hm)
        · simp [Sure.bunt, NMem] at hm
    have gm' : ∀ z, NMem L.sure.ned z → z < g0.re := fun z hz => hg.2 z hz
    have F1 := frontS_pairX (comb := C) FPs FQs (lo0 := g0.re) (lo := g3.re) (Lb := e.2.sure) (Fs := PB e.1)
      (H := HW) (E := gsE x L)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun s v d w x hq' hx => hp.dreg s v d w x hq' hx) (fun s v d w x hq' hx => hq.dreg s v d w x hq' hx)
      hLh' hLt' SA.ht hM1 hM2 hM3 hM4 SA.fit SA.sem
      (fun z hz => by
        obtain ⟨h1, h2⟩ := hHr z hz
        obtain ⟨n1, n2⟩ := nP z (Or.inl hz)
        refine ⟨h1, by omega, n1, n2, fun hm => ?_, fun hm => ?_⟩
        · rcases SA.mh z hm with a | a
          · have := (hLe z a).1; omega
          · omega
        · rcases SA.mt z hm with a | a
          · have := (hLe z a).1; omega
          · omega)
      (fun z hz => nP z (Or.inr (Or.inl hz)))
      (fun z hz => by
        obtain ⟨n1, n2⟩ := nP z (Or.inr (Or.inr (Or.inl hz)))
        have hz' : NMem tel.sure.ned z := by
          cases xq
          · exact hz.elim
          · exact hz
        refine ⟨?_, n1, n2, fun hm => ?_⟩
        · rcases hlq z hz' with a | ⟨_, a⟩
          · have := gm' z a; omega
          · omega
        · rcases SA.mh z hm with a | a
          · rcases hlq z hz' with b | ⟨b, _⟩
            · exact hG e he z b a
            · have := (hLe z a).1; omega
          · rcases hlq z hz' with b | ⟨_, b⟩
            · have := gm' z b; omega
            · omega)
      (fun R a b h1 h2 => hEH R a b h1 h2)'''
fr = rep(fr, old, new)

hdr = '''import lemmas.Ska.CompPairLSCore
import lemmas.Ska.CompFrontSX

/-!
# The fronts of a pair under a flat lazy goal, parts of any flag: `pairLSX_fronts`

README Gaps 12.32.  The first piece of `pairLS_ok` for parts of any flag:
`pairLS_fronts` (`CompPairLSSem.lean`) with the parts' `RunOKLS` at any
flags `xp`, `xq`, the parent's at any `x`, and the witness `pairWitX C HW`
(the halves `HW` that `+split` allocated, held with the parts' products),
through `frontS_pairX` at each goal label.  The section is
`CompPairLSSem.lean`'s with the flags, `HW`, the keep of `HW` by the block
`o` in `hA`/`hAB` (`Keep … ∨ NMem HW`), and the new hypotheses: `HW` in the
split's range (`hHr`), the halves hold it (`hHh`), the parts' goal
registers held from the parent's and `HW` (`hEH`), the goal's entries apart
from its sure need (`hG`), and the parts' result entries at the goal's
labels apart from `HW` and the goals' registers (`hPH`, the fact the scratch
test of `CompFrontSX.lean` found true at goal labels).
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
out = hdr + sec + fr + '\nend\n\nend Comp\nend SkaModel\nend Formalization\n'
open(D + 'CompPairLSXFronts.lean', 'w').write(out)
print('ok')
