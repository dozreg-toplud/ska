import lemmas.Compiler.OptLinkAlFin

/-!
# `+alias`: the end `%clq` (phase 14, README Gaps 13)

```hoon
        %clq
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (rn s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      ?:  |(is-cell.info-cond ?=([~ ^] has-imm.info-cond))
        :-  [%hop ~ there.z.fin.bob]
        =.  folded.gen  &
        =.  folded.gen  &
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.o.fin.bob o))
      ?:  |(is-loob.info-cond ?=([~ @] has-imm.info-cond))
        :-  [%hop ~ there.o.fin.bob]
        =.  folded.gen  &
        ?:  =(there.o.fin.bob there.z.fin.bob)  gen
        gen(rev (~(del ju rev.gen) there.z.fin.bob o))
      [fin.bob(s cond-new) gen]
```

* `alF_clq_run`: the Nock of the case on any `gen` noun, with the facts of
  the test register an `infoN` noun and the two `+del:ju` given.
* `alF_clq`: **`AlFinOK alFinClq`**.  The Hoon reads `is-loob` where the
  model reads `isLoob`; `InfoRel` fixes it up to `loobImm`, which implies
  `atomImm`, so the second test is the same.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The `+del:ju` of the label `o` under `k` in `REV`. -/
abbrev alDel (REV : Noun) (k o : Nat) : Option Noun :=
  nock (C ju.del.battery (C (C (A k) (A o)) (C ju.battery (C REV layer2)))) ju.del.battery

theorem alF_clq_run (X1 X2 P B X4 X5 X6 NEW OLD INFO IMMS LOC IMML REV FL NA BL REVA TR : Noun)
    (f : Nat → Nat) (hO : OldRel OLD f) (s zt ot o : Nat) (ic : Opt.InfoReg) (lb : Bool) (hs ts : Noun)
    (hv : nock (C by.got.battery (C (A (f s)) (C by.battery (C LOC layer2)))) by.got.battery
      = some (infoN ic lb hs ts))
    (Dz Do : Noun) (hDz : alDel REV zt o = some Dz) (hDo : alDel REV ot o = some Do) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.clq s ⟨[], zt⟩ ⟨[], ot⟩)))) X4 X5 X6
        (alWS (genN NEW OLD INFO IMMS LOC IMML REV FL) NA BL REVA (C (A o) TR))) alFinClq
      = some (if ic.isCell || ic.cellImm then
          C (Termin.toNoun (Termin.hop ⟨[], zt⟩))
            (genN NEW OLD INFO IMMS LOC IMML (if zt = ot then REV else Do) (flag true))
        else if lb || ic.atomImm then
          C (Termin.toNoun (Termin.hop ⟨[], ot⟩))
            (genN NEW OLD INFO IMMS LOC IMML (if ot = zt then REV else Dz) (flag true))
        else C (Termin.toNoun (Termin.clq (f s) ⟨[], zt⟩ ⟨[], ot⟩)) (genN NEW OLD INFO IMMS LOC IMML REV FL)) := by
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
    cases isCell <;> cases lb <;> rcases hasImm with _ | ⟨_ | _⟩ <;>
      simp [nock_exec, alFinClq, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, hrn, flag, hL2,
        by.arm_at, by_arm, by.got.arm_at, got_arm, hv, Opt.InfoReg.cellImm, Opt.InfoReg.atomImm, unitNoun]
  · have e' : zt ≠ ot := fun h => e h.symm
    cases isCell <;> cases lb <;> rcases hasImm with _ | ⟨_ | _⟩ <;>
      simp [nock_exec, alFinClq, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, hrn, flag, hL2,
        by.arm_at, by_arm, by.got.arm_at, got_arm, hv, Opt.InfoReg.cellImm, Opt.InfoReg.atomImm, unitNoun,
        e, e', ju.arm_at, ju_arm, ju.del.arm_at, ju_del_arm, hDz, hDo]

/-- **The end `%clq`.** -/
theorem alF_clq (s : Nat) (z o' : Jmp) : AlFinOK alFinClq (Termin.clq s z o') := by
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
    have hrun := alF_clq_run X1 X2 P B X4 X5 X6 (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV
      (flag g.folded) NA BL REVA TR g.old hO s zt ot o ic lb hs ts hv Dz Do hDz1 hDo1
    rw [lb_atomImm hlb] at hrun
    simp only [Opt.aliasFin, hc, ne_eq, not_true_eq_false, or_self, ↓reduceIte, Option.map_some,
      Option.some.injEq] at hres
    by_cases h1 : (ic.isCell || ic.cellImm) = true
    · simp only [h1, ↓reduceIte, Opt.aliasFold] at hres
      subst hres
      by_cases e : zt = ot
      · exact ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag true),
          by rw [hrun]; simp only [h1, e, ↓reduceIte], by simpa [e] using genRelL_fin hO hI hM hL hIm hR true⟩
      · exact ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML Do (flag true),
          by rw [hrun]; simp only [h1, e, ↓reduceIte],
          by simpa [e] using genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hDo2) true⟩
    · by_cases h2 : (ic.isLoob || ic.atomImm) = true
      · simp only [h1, h2, ↓reduceIte, Opt.aliasFold] at hres
        subst hres
        by_cases e : ot = zt
        · exact ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag true),
            by rw [hrun]; simp only [h1, h2, e, ↓reduceIte, Bool.false_eq_true], by simpa [e] using genRelL_fin hO hI hM hL hIm hR true⟩
        · exact ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML Dz (flag true),
            by rw [hrun]; simp only [h1, h2, e, ↓reduceIte, Bool.false_eq_true],
            by simpa [e] using genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hDz2) true⟩
      · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] at hres
        subst hres
        exact ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag g.folded),
          by rw [hrun]; simp only [h1, h2, ↓reduceIte, Bool.false_eq_true], genRelL_fin hO hI hM hL hIm hR g.folded⟩

end Compiler
end Formalization
