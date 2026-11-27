#!/usr/bin/env python3
"""Track Q, InvBSR: the AnnotK strand of `skaPoke_sound` (PokeConv.lean) and of
`pokeDat_ok` (PokeBake.lean), for lemmas/Ska/AnnotSPoke.lean.  Prints the two
bodies; every replacement is asserted by its count.  Never edits the originals."""
import sys
root = sys.argv[1] if len(sys.argv) > 1 else '.'

def rep(s, old, new, n):
    c = s.count(old)
    assert c == n, (old, c, n)
    return s.replace(old, new)

pc = open(root + '/lemmas/Ska/PokeConv.lean').read()
i = pc.index('theorem skaPoke_sound ')
j = pc.index('/-- **The datums of a poke**')
t = pc[i:j]
# statement
t = rep(t, 'theorem skaPoke_sound {lib : Lib} (env : Env R)', 'theorem skaPoke_soundK {lib : Lib} (hK : FolTopK lib) (env : Env R)', 1)
t = rep(t, '(hinv : PokeInv lib memo code)', '(hinv : PokeInvK lib memo code)', 1)
t = rep(t, """    PokeInv lib memo' (extendCode code dats) ∧
    ∀ bl d, Treap.get dats bl = some d → ∀ x, Fits bl.less x → ∀ gul t r,
      (Mink lib gul t x bl.fol r ↔ ∃ m, nommF lib gul (extendCode code dats) m t x d.nomm = some r) := by
  unfold skaPoke at h""", """    PokeInvK lib memo' (extendCode code dats) ∧
    ∀ bl d, Treap.get dats bl = some d → AnnotK lib (extendCode code dats) (Fits bl.less) bl.fol d.nomm := by
  have hbase := (skaPoke_sound env hinv.base hw hnr hnvr h).1
  unfold skaPoke at h""", 1)
t = rep(t, 'generalize hcd : extendCode code (pokeMemo pr memo).1 = code\'\n',
        'generalize hcd : extendCode code (pokeMemo pr memo).1 = code\' at hbase ⊢\n', 1)
t = rep(t, "(hinv.ok m hm).mono_code hcc\n",
        "(hinv.base.ok m hm).mono_code hcc\n"
        "  have hokK' : ∀ m, MemEnt memo m → AnnotK lib code' (Fits m.d.less) m.fol m.d.nomm :=\n"
        "    fun m hm => (hinv.okK m hm).mono_code hcc\n", 1)
t = rep(t, 'env memo hinv.wf\n    hinv.memoNorm hinv.keys hok\'', 'env memo hinv.base.wf\n    hinv.base.memoNorm hinv.base.keys hok\'', 1)
t = rep(t, 'have hcode : CodeOK lib code\'', 'have hcode : CodeOKK lib code\'', 1)
t = rep(t, '(hinv.codeOK bl _ hc0).mono_code hcc', '(hinv.codeOKK bl _ hc0).mono_code hcc', 1)
t = rep(t, 'exact annot_of_graphM hG hhas hwf1 (hcovP i d hi)\n  have hdatG',
        'exact annotK_of_graphM hK hG hhas hwf1 hokK\' (hcovP i d hi)\n  have hdatG', 1)
# the conclusion: keep the AnnotK strand only
k = t.index('  have hdatG')
t = t[:k] + """  refine ⟨⟨hbase, fun m hm => ?_, hcode⟩, ?_⟩
  · obtain ⟨f, ms, s, ent, h1, h2, rfl⟩ := hm
    rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, hd, rfl, rfl⟩
    · exact hokK' _ ⟨f, ms', s, ent, e1, e2, rfl⟩
    · exact memoFinal_annotK hK hG hhas hwfG hokK' (hcovP i d hd) (fun bl nb h => ⟨nb, h⟩)
  · intro bl d hd
    obtain ⟨i, hi, rfl⟩ := d1 bl d hd
    exact annotK_of_graphM hK hG hhas hwf1 hokK' (hcovP i d hi)

"""
out1 = t

pb = open(root + '/lemmas/Ska/PokeBake.lean').read()
i = pb.index('theorem pokeDat_ok ')
j = pb.index('/-! ## Normal bakes -/')
u = pb[i:j]
u = rep(u, 'theorem pokeDat_ok ', 'theorem pokeDat_annotK ', 1)
u = rep(u, '(hinv : PokeInv lib memo code)', '(hinv : Ana.PokeInvK lib memo code)', 1)
u = rep(u, """    (hd : ∀ bl d, Treap.get dats bl = some d →
      Annot lib code (Fits bl.less) bl.fol d.nomm ∧
      ∀ y gul p, Fits bl.less y → Mink lib gul [] y bl.fol (Tone.zero p) → ProvR y d.prod d.map p) :
    DatOK lib (pokeDat dats memo) ∧
      ∀ t d, pokeDat dats memo t = some d → Annot lib code (Fits t.less) t.fol d.nomm := by
  -- a datum of `dat` is this poke's or a memo entry's, of the bell asked for
  have key : ∀ t d, pokeDat dats memo t = some d →
      Annot lib code (Fits t.less) t.fol d.nomm ∧
      ∀ y gul p, Fits t.less y → Mink lib gul [] y t.fol (Tone.zero p) → ProvR y d.prod d.map p := by
    intro t d h""", """    (hd : ∀ bl d, Treap.get dats bl = some d → AnnotK lib code (Fits bl.less) bl.fol d.nomm) :
    ∀ t d, pokeDat dats memo t = some d → AnnotK lib code (Fits t.less) t.fol d.nomm := by
    intro t d h""", 1)
u = rep(u, 'have hok := hinv.ok _ hmem\n', 'have ha := hinv.okK _ hmem\n', 1)
u = rep(u, 'have hf : ent.1.2 = t.fol := hinv.keys', 'have hf : ent.1.2 = t.fol := hinv.base.keys', 1)
u = rep(u, '        have ha := hok.annot\n        have hp := hok.prov\n', '', 1)
u = rep(u, 'simp only [entOf] at ha hp\n', 'simp only [entOf] at ha\n', 1)
u = rep(u, 'rw [hf] at ha hp\n', 'rw [hf] at ha\n', 1)
u = rep(u, 'rw [show (FDatum.core ent.2).less = t.less from hl] at ha hp\n        exact ⟨ha, hp⟩\n',
        'rw [show (FDatum.core ent.2).less = t.less from hl] at ha\n        exact ha\n', 1)
k = u.index('  exact ⟨datOK_of_prov')
u = u[:k].rstrip() + '\n\n'
out2 = u
sys.stdout.write(out1 + '\x00' + out2)
