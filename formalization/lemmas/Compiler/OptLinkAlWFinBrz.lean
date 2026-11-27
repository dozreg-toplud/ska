import lemmas.Compiler.OptLinkAlWFinBrn

/-!
# `+alias`: the end `%brz` (phase 14, README Gaps 13)

```hoon
        %brz
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (rn s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      =/  zero=(unit ?)
        ?^  has-imm.info-cond  `=(0 u.has-imm.info-cond)
        ?:(is-cell.info-cond `| ~)
      ?~  zero  [fin.bob(s cond-new) gen]
      =/  [go=@uwoo cut=@uwoo]
        ?:(u.zero [there.z there.o]:fin.bob [there.o there.z]:fin.bob)
      :-  [%hop ~ go]
      =.  folded.gen  &
      ?:  =(go cut)  gen
      gen(rev (~(del ju rev.gen) cut o))
```

* `alF_brz_run`: the Nock of the case on any `gen` noun.
* `alF_brz`: **`AlFinOK alFinBrz`**.  The case reads `is-cell` and
  `has-imm` only, which `InfoRel` fixes exactly.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem alF_brz_run (X1 X2 P B X4 X5 X6 NEW OLD INFO IMMS LOC IMML REV FL NA BL REVA TR : Noun)
    (f : Nat → Nat) (hO : OldRel OLD f) (s zt ot o : Nat) (ic : Opt.InfoReg) (lb : Bool) (hs ts : Noun)
    (hv : nock (C by.got.battery (C (A (f s)) (C by.battery (C LOC layer2)))) by.got.battery
      = some (infoN ic lb hs ts))
    (Dz Do : Noun) (hDz : alDel REV zt o = some Dz) (hDo : alDel REV ot o = some Do) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.brz s ⟨[], zt⟩ ⟨[], ot⟩)))) X4 X5 X6
        (alWS (genN NEW OLD INFO IMMS LOC IMML REV FL) NA BL REVA (C (A o) TR))) alFinBrz
      = some (match ic.hasImm with
          | some v => if v = A 0 then
              C (Termin.toNoun (Termin.hop ⟨[], zt⟩))
                (genN NEW OLD INFO IMMS LOC IMML (if zt = ot then REV else Do) (flag true))
            else C (Termin.toNoun (Termin.hop ⟨[], ot⟩))
                (genN NEW OLD INFO IMMS LOC IMML (if ot = zt then REV else Dz) (flag true))
          | none => if ic.isCell then
              C (Termin.toNoun (Termin.hop ⟨[], ot⟩))
                (genN NEW OLD INFO IMMS LOC IMML (if ot = zt then REV else Dz) (flag true))
            else C (Termin.toNoun (Termin.brz (f s) ⟨[], zt⟩ ⟨[], ot⟩)) (genN NEW OLD INFO IMMS LOC IMML REV FL)) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD (C INFO (C IMMS (C LOC (C IMML (C REV FL))))) alBodyCut
    (C NA (C BL (C REVA (C (A o) TR)))) f hO
  have hL2 := optC_layer2
  unfold alFS alWS genN
  rw [hB]
  generalize optC = OC at hrn hL2
  obtain ⟨isCell, isLoob, hedOf, telOf, hasHed, hasTel, decOf, hasImm⟩ := ic
  unfold infoN at hv
  unfold alDel at hDz hDo
  by_cases e : ot = zt
  · subst e
    have eD : Dz = Do := Option.some.inj (hDz.symm.trans hDo)
    subst eD
    cases isCell <;> rcases hasImm with _ | ⟨(_ | n) | ⟨a, b⟩⟩ <;>
      simp [nock_exec, alFinBrz, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, Tag.brz, hrn,
        flag, hL2, by.arm_at, by_arm, by.got.arm_at, got_arm, hv, unitNoun, ju.arm_at, ju_arm, ju.del.arm_at,
        ju_del_arm, hDz]
  · have e' : zt ≠ ot := fun h => e h.symm
    cases isCell <;> rcases hasImm with _ | ⟨(_ | n) | ⟨a, b⟩⟩ <;>
      simp [nock_exec, alFinBrz, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, Tag.brz, hrn,
        flag, hL2, by.arm_at, by_arm, by.got.arm_at, got_arm, hv, unitNoun, e, e', ju.arm_at, ju_arm,
        ju.del.arm_at, ju_del_arm, hDz, hDo]

/-- **The end `%brz`.** -/
theorem alF_brz (s : Nat) (z o' : Jmp) : AlFinOK alFinBrz (Termin.brz s z o') := by
  intro g loc imml N hG hnd X1 X2 P B X4 X5 X6 NA BL REVA TR o res hres
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, REV, rfl, hO, hI, hM, hR, hL, hIm⟩ := hG
  obtain ⟨za, zt⟩ := z
  obtain ⟨oa, ot⟩ := o'
  have hza : za = [] := by
    cases za with
    | nil => rfl
    | cons _ _ => simp [Opt.aliasFin] at hres
  have hoa : oa = [] := by
    cases oa with
    | nil => rfl
    | cons _ _ => simp [Opt.aliasFin] at hres
  subst hza hoa
  cases hc : loc (g.old s) with
  | none => simp [Opt.aliasFin, hc] at hres
  | some ic =>
    obtain ⟨v, hv, lb, hs, ts, rfl, -, -, hlb⟩ := alF_got hL hc
    obtain ⟨Dz, hDz1, hDz2⟩ := alF_jug_del hR zt o
    obtain ⟨Do, hDo1, hDo2⟩ := alF_jug_del hR ot o
    have hrun := alF_brz_run X1 X2 P B X4 X5 X6 (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV
      (flag g.folded) NA BL REVA TR g.old hO s zt ot o ic lb hs ts hv Dz Do hDz1 hDo1
    simp only [Opt.aliasFin, hc, ne_eq, not_true_eq_false, or_self, ↓reduceIte, Option.map_some,
      Option.some.injEq] at hres
    have hzero : ∀ go cut, Opt.aliasFold g.rev o go cut = res →
        (go = zt ∧ cut = ot ∨ go = ot ∧ cut = zt) →
        nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.brz s ⟨[], zt⟩ ⟨[], ot⟩)))) X4 X5 X6
          (alWS (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag g.folded)) NA BL REVA
            (C (A o) TR))) alFinBrz
          = some (C (Termin.toNoun (Termin.hop ⟨[], go⟩)) (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS
              LOC IMML (if go = cut then REV else if cut = ot then Do else Dz) (flag true))) →
        ∃ N', nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.brz s ⟨[], zt⟩ ⟨[], ot⟩)))) X4 X5 X6
            (alWS (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag g.folded)) NA BL REVA
              (C (A o) TR))) alFinBrz = some (C (Termin.toNoun res.1) N') ∧
          GenRelL { g with rev := res.2.1, folded := res.2.2 } loc imml N' := by
      intro go cut hgc hcase hn
      subst hgc
      refine ⟨_, hn, ?_⟩
      unfold Opt.aliasFold
      by_cases e : go = cut
      · simpa [e] using genRelL_fin hO hI hM hL hIm hR true
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst go cut
          simpa [e] using genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hDo2) true
        · subst go cut
          have e' : zt ≠ ot := fun h => e h.symm
          simpa [e, e'] using genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hDz2) true
    rcases hh : ic.hasImm with _ | v
    · simp only [hh] at hres hrun
      cases hb : ic.isCell
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hres hrun
        subst hres
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hR g.folded⟩
      · simp only [hb, ↓reduceIte] at hres hrun
        refine hzero ot zt hres (Or.inr ⟨rfl, rfl⟩) ?_
        rw [hrun]
        by_cases e : ot = zt
        · subst e; simp
        · have e' : zt ≠ ot := fun h => e h.symm
          simp [e, e']
    · by_cases hv0 : v = A 0
      · subst hv0
        simp only [hh, decide_true, ↓reduceIte] at hres hrun
        refine hzero zt ot hres (Or.inl ⟨rfl, rfl⟩) ?_
        rw [hrun]
        by_cases e : zt = ot
        · subst e; simp
        · simp [e]
      · simp only [hh, hv0, decide_false, ↓reduceIte] at hres hrun
        refine hzero ot zt hres (Or.inr ⟨rfl, rfl⟩) ?_
        rw [hrun]
        by_cases e : ot = zt
        · subst e; simp
        · have e' : zt ≠ ot := fun h => e h.symm
          simp [e, e']

end Compiler
end Formalization
