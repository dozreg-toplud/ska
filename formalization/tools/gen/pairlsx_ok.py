D = 'lemmas/Ska/'


def rep(t, o, n, k=1):
    assert t.count(o) == k, (o, t.count(o))
    return t.replace(o, n)


src = open(D + 'CompPairLS.lean').read()
c = src.index('theorem pairLS_ok ')
c0 = src.rindex('/--', 0, c)
d = src.index('\nend Comp', c)
t = src[c0:d]
t = rep(t, 'theorem pairLS_ok ', 'theorem pairLSX_ok ')
t = rep(t, '{nexq nexp : NextL S} {n : Next S}', '{nexq nexp : NextL S} {n : Next S} {x xp xq : Bool} {HW : Need}')
t = rep(t, '(hq : RunOKLS (Map := Map) lib N P ft tel jt Qt false gb g1 nexq)',
        '(hq : RunOKLS (Map := Map) lib N P ft tel jt Qt xq gb g1 nexq)')
t = rep(t, '(hp : RunOKLS (Map := Map) lib N P fh Lh nexq.th Qh false g1 g2 nexp)',
        '(hp : RunOKLS (Map := Map) lib N P fh Lh nexq.th Qh xp g1 g2 nexp)')
t = rep(t, 'GoalSemCM lib O c gul Inv ν (Keep g0 g\' (CGoal.next L.sure th)) st regs t tm (jmp0 o) (CGoal.next L.sure th) r',
        'GoalSemCM lib O c gul Inv ν (fun z => Keep g0 g\' (CGoal.next L.sure th) z ∨ NMem HW z) st regs t tm (jmp0 o)\n          (CGoal.next L.sure th) r', 2)
extra = '''    -- the halves in the witness and the parts' goal registers (README Gaps 12.32)
    (hHr : ∀ z, NMem HW z → g0.re ≤ z ∧ z < g'.re)
    (hHh : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN hed.sure.ned R a → HoldsN tel.sure.ned R b →
      HoldsN HW R (C a b))
    (hEH : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN (gsE x L) R (C a b) → HoldsN HW R (C a b) →
      HoldsN (gsE xp Lh) R a ∧ HoldsN (gsE xq tel) R b)
    (hG : ∀ e ∈ L.bond, ∀ z, NMem L.sure.ned z → ¬ NMem e.2.sure.ned z)
    (hPH : ∀ e ∈ L.bond, ∀ e1 ∈ nexp.laz.bond ++ nexq.laz.bond, e1.1 = e.1 → ∀ z,
      (NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z) → ¬ NMem e1.2.sure.ned z) :
    RunOKLS (Map := Map) lib N P f L th (pairWitX C HW Qh Qt) x g0 g3'''
t = rep(t, ''' :
    RunOKLS (Map := Map) lib N P f L th (pairWit C Qh Qt) false g0 g3''', '\n' + extra)
t = rep(t, '''  have dregR : ∀ s v d w x, pairWit C Qh Qt s v d w → NMem d x → g0.re ≤ x ∧ x < g3.re := by
    intro s v d w x hq' hx
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq'
    rcases hx with hx | hx
''', '''  have dregR : ∀ s v d w x, pairWitX C HW Qh Qt s v d w → NMem d x → g0.re ≤ x ∧ x < g3.re := by
    intro s v d w x hq' hx
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq'
    rcases hx with hx | hx | hx
    · have := hHr x hx; exact ⟨by omega, by omega⟩
''')
for nm in ['core', 'sem', 'semB', 'fronts']:
    o = 'pairLS_%s (Mf := Mf)' % nm
    t = rep(t, o, 'pairLSX_%s (Mf := Mf)' % nm)
t = rep(t, '(hAB := hAB)', '(hAB := hAB) (hHr := hHr) (hHh := hHh) (hEH := hEH) (hG := hG) (hPH := hPH)', 4)
hle = '''  -- the result's entries at the goal's labels are apart from the goal registers the fronts read
  have hLEg : ∀ e ∈ entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz, e.1 ∈ (entries L).map Prod.fst →
      ∀ z, NMem (gsE x L) z → ¬ NMem e.2.sure.ned z := by
    intro e he hl z hz hm
    rw [eR] at he
    rw [eL] at hl
    obtain ⟨eb, heb, ebe⟩ := List.mem_map.mp hl
    have hz0 : z < g0.re := by
      cases x
      · exact hz.elim
      · exact gm z hz
    have hz' : NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z := Or.inr (Or.inr (Or.inr hz))
    rcases resE e he with ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, es1, es2, l1, l2, dd, bb, cpy, pp⟩
    · exact hPH eb heb e (List.mem_append_left _ h1) ebe.symm z hz' hm
    · exact hPH eb heb e (List.mem_append_right _ h1) ebe.symm z hz' hm
    · obtain ⟨A, gx, PA, CO, ex, lk, RA, RB⟩ := copyLazy_ok cpy dd
      rw [ee] at hm
      rcases CO.mem z (by simpa [ofSure] using hm) with (a | a) | ⟨a, a'⟩
      · exact hPH eb heb e1 (List.mem_append_left _ he1) (ee1.trans ebe.symm) z hz' (by rw [es1]; simpa [ofSure] using a)
      · exact hPH eb heb e2 (List.mem_append_right _ he2) (ee2.trans ebe.symm) z hz' (by rw [es2]; simpa [ofSure] using a)
      · omega
'''
t = rep(t, '  -- the shared part of the two `sem` clauses\n', hle + '  -- the shared part of the two `sem` clauses\n')
t = rep(t, 'front := FS.toFront (by omega) (fun x hx => gm x hx) (fun _ _ x hx => hx.elim) dregR',
        'front := FS.toFrontG (by omega) (fun x hx => gm x hx) hLEg dregR')
t = rep(t, '''/-- **A pair of runs under a flat lazy goal with entries** (see the header):
`RunOKLS` of the whole, its result flat with clean entries. -/''', '''/-- **`pairLS_ok` for parts of any flag** (README Gaps 12.32): the parts'
`RunOKLS` at any flags `xp`, `xq`, the whole's at any `x`, with the witness
`pairWitX C HW` (the halves `HW` that `+split` allocated, which the block `o`
keeps, `hA`/`hAB`), when the parts' goal registers are held from the
parent's and `HW` (`hEH`), the goal's entries are apart from its sure need
(`hG`), and the parts' result entries at the goal's labels are apart from
`HW` and the goals' registers (`hPH`). -/''')
hdr = '''import lemmas.Ska.CompPairLSXSem
import lemmas.Ska.CompPairLS

/-!
# A pair of runs under a flat lazy goal with entries, parts of any flag: `pairLSX_ok`

README Gaps 12.32.  `pairLS_ok` (`CompPairLS.lean`, copied by script) with
the parts at any flags and the witness `pairWitX C HW`, from
`pairLSX_core`, `pairLSX_sem`, `pairLSX_semB`, `pairLSX_fronts`.  The front
field comes from `FrontsS.toFrontG`: the result's entries at the goal's
labels are a part's entry there or the copy of two (`resE`, `copyLazy_ok`),
apart from the goal's registers by `hPH`.
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
open(D + 'CompPairLSX.lean', 'w').write(hdr + t.rstrip() + '\n\nend Comp\nend SkaModel\nend Formalization\n')
print('ok')
