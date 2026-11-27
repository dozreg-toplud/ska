import lemmas.Compiler.OptLinkAlFinClq

/-!
# `+alias`: the end `%brn` (phase 14, README Gaps 13)

```hoon
        %brn
      ?>  =(~ args.z.fin.bob)
      ?>  =(~ args.o.fin.bob)
      =/  cond-new  (rn s.fin.bob)
      =/  info-cond  (~(got by info-local.gen) cond-new)
      ?~  has-imm.info-cond
        ?.  is-loob.info-cond  [fin.bob(s cond-new) gen]
        [[%brz cond-new z.fin.bob o.fin.bob] gen(folded &)]
      ?-    u.has-imm.info-cond
          %&  :-  [%hop ~ there.z.fin.bob]  ...  (del ju rev.gen) there.o.fin.bob o
          %|  :-  [%hop ~ there.o.fin.bob]  ...  (del ju rev.gen) there.z.fin.bob o
          *   :-  [%bom ~]  (del there.o, then del there.z)  gen
      ==
```

* `alF_brn_run`: the Nock of the case on any `gen` noun.
* `alF_brn`: **`AlFinOK alFinBrn`**.  With no immediate, `InfoRel` fixes
  `is-loob` (`lb_none`); the `[%bom ~]` end deletes both edges, the second
  `+del:ju` on the product of the first, and keeps `folded`, as the model.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem alF_brn_run (X1 X2 P B X4 X5 X6 NEW OLD INFO IMMS LOC IMML REV FL NA BL REVA TR : Noun)
    (f : Nat → Nat) (hO : OldRel OLD f) (s zt ot o : Nat) (ic : Opt.InfoReg) (lb : Bool) (hs ts : Noun)
    (hv : nock (C by.got.battery (C (A (f s)) (C by.battery (C LOC layer2)))) by.got.battery
      = some (infoN ic lb hs ts))
    (Dz Do Doz : Noun) (hDz : alDel REV zt o = some Dz) (hDo : alDel REV ot o = some Do)
    (hDoz : alDel Do zt o = some Doz) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.brn s ⟨[], zt⟩ ⟨[], ot⟩)))) X4 X5 X6
        (alWS (genN NEW OLD INFO IMMS LOC IMML REV FL) NA BL REVA (C (A o) TR))) alFinBrn
      = some (match ic.hasImm with
          | none => if lb then
              C (Termin.toNoun (Termin.brz (f s) ⟨[], zt⟩ ⟨[], ot⟩)) (genN NEW OLD INFO IMMS LOC IMML REV (flag true))
            else C (Termin.toNoun (Termin.brn (f s) ⟨[], zt⟩ ⟨[], ot⟩)) (genN NEW OLD INFO IMMS LOC IMML REV FL)
          | some (Noun.atom 0) => C (Termin.toNoun (Termin.hop ⟨[], zt⟩))
              (genN NEW OLD INFO IMMS LOC IMML (if zt = ot then REV else Do) (flag true))
          | some (Noun.atom 1) => C (Termin.toNoun (Termin.hop ⟨[], ot⟩))
              (genN NEW OLD INFO IMMS LOC IMML (if ot = zt then REV else Dz) (flag true))
          | some _ => C (Termin.toNoun (Termin.bom none)) (genN NEW OLD INFO IMMS LOC IMML Doz FL)) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD (C INFO (C IMMS (C LOC (C IMML (C REV FL))))) alBodyCut
    (C NA (C BL (C REVA (C (A o) TR)))) f hO
  have hL2 := optC_layer2
  unfold alFS alWS genN
  rw [hB]
  generalize optC = OC at hrn hL2
  obtain ⟨isCell, isLoob, hedOf, telOf, hasHed, hasTel, decOf, hasImm⟩ := ic
  unfold infoN at hv
  unfold alDel at hDz hDo hDoz
  by_cases e : ot = zt
  · subst e
    have eD : Dz = Do := Option.some.inj (hDz.symm.trans hDo)
    subst eD
    cases lb <;> rcases hasImm with _ | ⟨(_ | _ | n) | ⟨a, b⟩⟩ <;>
      simp [nock_exec, alFinBrn, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, Tag.brz, Tag.bom, hrn,
        flag, hL2, by.arm_at, by_arm, by.got.arm_at, got_arm, hv, unitNoun, ju.arm_at, ju_arm, ju.del.arm_at,
        ju_del_arm, hDz, hDo, hDoz]
  · have e' : zt ≠ ot := fun h => e h.symm
    cases lb <;> rcases hasImm with _ | ⟨(_ | _ | n) | ⟨a, b⟩⟩ <;>
      simp [nock_exec, alFinBrn, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, Tag.brz, Tag.bom, hrn,
        flag, hL2, by.arm_at, by_arm, by.got.arm_at, got_arm, hv, unitNoun, e, e', ju.arm_at, ju_arm,
        ju.del.arm_at, ju_del_arm, hDz, hDo, hDoz]

/-- **The end `%brn`.** -/
theorem alF_brn (s : Nat) (z o' : Jmp) : AlFinOK alFinBrn (Termin.brn s z o') := by
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
    have hDo3 := jugRel_delJu hnd hDo2
    obtain ⟨Doz, hDoz1, hDoz2⟩ := alF_jug_del hDo3 zt o
    have hDoz3 := jugRel_delJu (Opt.revNodup_delJu hnd ot o) hDoz2
    have hrun := alF_brn_run X1 X2 P B X4 X5 X6 (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV
      (flag g.folded) NA BL REVA TR g.old hO s zt ot o ic lb hs ts hv Dz Do Doz hDz1 hDo1 hDoz1
    simp only [Opt.aliasFin, hc, ne_eq, not_true_eq_false, or_self, ↓reduceIte, Option.map_some,
      Option.some.injEq] at hres
    rcases hh : ic.hasImm with _ | ⟨(_ | _ | n) | ⟨a, b⟩⟩
    · have hl := lb_none hlb hh
      simp only [hh] at hres hrun
      subst hl
      cases hb : ic.isLoob
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hres hrun
        subst hres
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hR g.folded⟩
      · simp only [hb, ↓reduceIte] at hres hrun
        subst hres
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hR true⟩
    · simp only [hh, Opt.aliasFold] at hres hrun
      subst hres
      by_cases e : zt = ot
      · simp only [e, ↓reduceIte] at hrun ⊢
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hR true⟩
      · simp only [e, ↓reduceIte] at hrun ⊢
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hDo2) true⟩
    · simp only [hh, Opt.aliasFold] at hres hrun
      subst hres
      by_cases e : ot = zt
      · simp only [e, ↓reduceIte] at hrun ⊢
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hR true⟩
      · simp only [e, ↓reduceIte] at hrun ⊢
        exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hDz2) true⟩
    · simp only [hh] at hres hrun
      subst hres
      exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hDoz3 g.folded⟩
    · simp only [hh] at hres hrun
      subst hres
      exact ⟨_, hrun, genRelL_fin hO hI hM hL hIm hDoz3 g.folded⟩

end Compiler
end Formalization
