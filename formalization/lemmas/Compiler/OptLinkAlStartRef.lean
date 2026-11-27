import lemmas.Compiler.OptLinkAlStartImms
import lemmas.Compiler.OptLinkAlBodyLoc

/-!
# `+alias`: the refinement after one predecessor (phase 9 of the plan, README Gaps 13)

```hoon
    ?^  t.pre  info
    =/  pre-b  (~(got by new.gen) i.pre)
    ?:  ?=(%brn -.fin.pre-b)
      ...  (~(jab by info) s.fin.pre-b lens)  ...
    ?:  ?=(%brz -.fin.pre-b)  ...
    ?:  ?=(%clq -.fin.pre-b)  ...
    info
```

* `al_preb`: `pre-b` is the noun of the block `i.pre` of `new.gen`.
* `al_jbrn`, `al_jbrz`, `al_jclq`: the three cases, each against the model's
  branch of `aliasStart` (a `+jab:by` through `loc_jab` with one lens each:
  `alLsZ`, `alLsO`, `alLsL`, `alLsC`).  In the `%brz` case the Hoon reads
  `is-loob` of the test register, which `InfoRel` fixes when `loobImm` is
  false (`brzInv_loob`).  The model's `none` covers the `?>` and `~|`.
* `al_jnref`: **the refinement is the model's `aliasStart g o [p]`** from the
  facts `info.gen` of `p`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **`pre-b`**: `(~(got by new.gen) i.pre)` is the noun of the block. -/
theorem al_preb (INFO0 : Noun) (p : Nat) (t : List Nat) (new : TreapMap mugF Blob)
    (OLD INFO IMMS LOC IMML R F NA BL REV TOPO : Noun) :
    nock (C INFO0 (C (listNoun A (p :: t)) (alWS (genN (HoonMap.toNoun Blob.toNoun new) OLD INFO IMMS LOC IMML R F)
      NA BL REV TOPO))) alJnPreB = (HoonMap.get new p).map Blob.toNoun := by
  have hg := blocks_got new p
  have hL := optC_layer2
  unfold alWS genN
  generalize optC = OC at hL
  generalize HoonMap.toNoun Blob.toNoun new = NW at hg
  simp [nock_exec, alJnPreB, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]

/-! ## The lenses -/

theorem infoRel_imm {x : Opt.InfoReg} {lb : Bool} {hs ts : Noun} (hhs : SawRel hs x.hedOf)
    (hts : SawRel ts x.telOf) (n : Nat) (hn : n = 0 ∨ n = 1) :
    InfoRel (infoN { x with hasImm := some (Noun.atom n) } lb hs ts) { x with hasImm := some (Noun.atom n) } := by
  refine ⟨lb, hs, ts, rfl, hhs, hts, ?_⟩
  rcases hn with rfl | rfl <;> simp [Opt.InfoReg.loobImm]

theorem lsZ_run (x : Opt.InfoReg) (lb : Bool) (hs ts fc : Noun) :
    nock (C alLsZ (C (infoN x lb hs ts) fc)) alLsZ = some (infoN { x with hasImm := some (Noun.atom 0) } lb hs ts) := by
  simp [nock_exec, alLsZ, infoN, unitNoun]

theorem lsO_run (x : Opt.InfoReg) (lb : Bool) (hs ts fc : Noun) :
    nock (C alLsO (C (infoN x lb hs ts) fc)) alLsO = some (infoN { x with hasImm := some (Noun.atom 1) } lb hs ts) := by
  simp [nock_exec, alLsO, infoN, unitNoun]

theorem lsL_run (x : Opt.InfoReg) (lb : Bool) (hs ts fc : Noun) :
    nock (C alLsL (C (infoN x lb hs ts) fc)) alLsL = some (infoN { x with isLoob := true } true hs ts) := by
  simp [nock_exec, alLsL, infoN, flag]

theorem lsC_run (x : Opt.InfoReg) (lb : Bool) (hs ts fc : Noun) :
    nock (C alLsC (C (infoN x lb hs ts) fc)) alLsC = some (infoN { x with isCell := true } lb hs ts) := by
  simp [nock_exec, alLsC, infoN, flag]

/-! ## The three cases -/

/-- **The refinement after a `%brn`.** -/
theorem al_jbrn {INFO0 : Noun} {info : Opt.AInfo} (hI : InfoMapRel INFO0 info) (P1 P2 ZA OA PRE GEN NA BL REV T : Noun)
    (s zt ot o : Nat) {r : Opt.AInfo}
    (hr : (if zt = o ∧ ot ≠ o then Opt.jabA info s fun i => { i with hasImm := some (Noun.atom 0) }
      else if ot = o ∧ zt ≠ o then Opt.jabA info s fun i => { i with hasImm := some (Noun.atom 1) }
      else if zt = ot ∧ zt = o then Opt.jabA info s fun i => { i with isLoob := true }
      else none) = some r) :
    ∃ N, nock (C (C P1 (C P2 (C (A Tag.brn) (C (A s) (C (C ZA (A zt)) (C OA (A ot)))))))
      (C INFO0 (C PRE (alWS GEN NA BL REV (C (A o) T))))) alJnBrn = some N ∧ InfoMapRel N r := by
  cases hs : info s with
  | none =>
    exfalso
    revert hr
    by_cases h1 : zt = o <;> by_cases h2 : ot = o <;> simp [h1, h2, Opt.jabA, hs]
  | some x =>
    obtain ⟨N, hN, hrel, hgot⟩ := loc_got hI hs
    obtain ⟨p0, q0, l0, r0, hLOC⟩ := loc_node hN
    have hja := jab_arm_node by.battery layer2 p0 q0 l0 r0
    rw [← hLOC] at hja
    obtain ⟨lb, hs', ts, rfl, hhs, hts, hlb⟩ := hrel
    have hL := optC_layer2
    unfold alWS
    generalize optC = OC at hL
    rw [alJnBrn_cut]
    by_cases h1 : zt = o <;> by_cases h2 : ot = o
    · subst h1
      subst h2
      simp [Opt.jabA, hs] at hr
      subst hr
      obtain ⟨I', hj, hr'⟩ := loc_jab hI hN (infoN { x with isLoob := true } true hs' ts)
        (y := { x with isLoob := true }) ⟨true, hs', ts, rfl, hhs, hts, by simp⟩
      have hj' := fun fs fc => hj alLsL fs fc (lsL_run x lb hs' ts fc)
      refine ⟨I', ?_, hr'⟩
      simp [nock_exec, alJnBrnC, hL, by.arm_at, by_arm, by.jab.arm_at, hja, hj']
    · subst h1
      simp [h2, Opt.jabA, hs] at hr
      subst hr
      obtain ⟨I', hj, hr'⟩ := loc_jab hI hN _ (infoRel_imm (lb := lb) hhs hts 0 (Or.inl rfl))
      have hj' := fun fs fc => hj alLsZ fs fc (lsZ_run x lb hs' ts fc)
      refine ⟨I', ?_, hr'⟩
      simp [nock_exec, alJnBrnC, hL, by.arm_at, by_arm, by.jab.arm_at, hja, hj', h2]
    · subst h2
      simp [h1, Opt.jabA, hs] at hr
      subst hr
      obtain ⟨I', hj, hr'⟩ := loc_jab hI hN _ (infoRel_imm (lb := lb) hhs hts 1 (Or.inr rfl))
      have hj' := fun fs fc => hj alLsO fs fc (lsO_run x lb hs' ts fc)
      refine ⟨I', ?_, hr'⟩
      simp [nock_exec, alJnBrnC, hL, by.arm_at, by_arm, by.jab.arm_at, hja, hj', h1]
    · simp [h1, h2] at hr

/-- `+jab:by` on `info` at a register the model knows: the arm of the door,
the noun there, and `loc_jab` for each lens. -/
theorem info_jab_at {INFO0 : Noun} {info : Opt.AInfo} (hI : InfoMapRel INFO0 info) {s : Nat} {x : Opt.InfoReg}
    (hs : info s = some x) :
    ∃ lb hs' ts, SawRel hs' x.hedOf ∧ SawRel ts x.telOf ∧ (lb || x.loobImm) = (x.isLoob || x.loobImm) ∧
      Get INFO0 (A s) (infoN x lb hs' ts) ∧
      nock (C by.got.battery (C (A s) (C by.battery (C INFO0 layer2)))) by.got.battery = some (infoN x lb hs' ts) ∧
      ∃ p0 q0, nock (C by.battery (C INFO0 layer2)) by.jab.arm
        = some (C by.jab.battery (C (C p0 (C (C (A 0) (A 15)) (C q0 (C q0 q0)))) (C by.battery (C INFO0 layer2)))) := by
  obtain ⟨N, hN, hrel, hgot⟩ := loc_got hI hs
  obtain ⟨p0, q0, l0, r0, hLOC⟩ := loc_node hN
  have hja := jab_arm_node by.battery layer2 p0 q0 l0 r0
  rw [← hLOC] at hja
  obtain ⟨lb, hs', ts, rfl, hhs, hts, hlb⟩ := hrel
  exact ⟨lb, hs', ts, hhs, hts, hlb, hN, hgot, p0, q0, hja⟩

/-- **The refinement after a `%brz`**, given that the facts of its test
register have no loobean `has-imm` (`brzInv_loob`). -/
theorem al_jbrz {INFO0 : Noun} {info : Opt.AInfo} (hI : InfoMapRel INFO0 info) (P1 P2 ZA OA PRE GEN NA BL REV T : Noun)
    (s zt ot o : Nat) (hlo : ∀ si, info s = some si → si.loobImm = false) {r : Opt.AInfo}
    (hr : (if zt = o ∧ ot ≠ o then Opt.jabA info s fun i => { i with hasImm := some (Noun.atom 0) }
      else if ot = o ∧ zt ≠ o then
        (info s).bind fun si => if si.isLoob then Opt.jabA info s fun i => { i with hasImm := some (Noun.atom 1) }
          else some info
      else some info) = some r) :
    ∃ N, nock (C (C P1 (C P2 (C (A Tag.brz) (C (A s) (C (C ZA (A zt)) (C OA (A ot)))))))
      (C INFO0 (C PRE (alWS GEN NA BL REV (C (A o) T))))) alJnBrz = some N ∧ InfoMapRel N r := by
  have hL := optC_layer2
  unfold alWS
  generalize optC = OC at hL
  rw [alJnBrz_cut]
  by_cases h1 : zt = o <;> by_cases h2 : ot = o
  · subst h1
    subst h2
    simp at hr
    subst hr
    exact ⟨INFO0, by simp [nock_exec, alJnBrzC], hI⟩
  · subst h1
    cases hs : info s with
    | none => simp [h2, Opt.jabA, hs] at hr
    | some x =>
      obtain ⟨lb, hs', ts, hhs, hts, hlb, hN, hgot, p0, q0, hja⟩ := info_jab_at hI hs
      simp [h2, Opt.jabA, hs] at hr
      subst hr
      obtain ⟨I', hj, hr'⟩ := loc_jab hI hN _ (infoRel_imm (lb := lb) hhs hts 0 (Or.inl rfl))
      have hj' := fun fs fc => hj alLsZ fs fc (lsZ_run x lb hs' ts fc)
      refine ⟨I', ?_, hr'⟩
      simp [nock_exec, alJnBrzC, hL, by.arm_at, by_arm, by.jab.arm_at, hja, hj', h2]
  · subst h2
    cases hs : info s with
    | none => simp [h1, hs] at hr
    | some x =>
      obtain ⟨lb, hs', ts, hhs, hts, hlb, hN, hgot, p0, q0, hja⟩ := info_jab_at hI hs
      have hl := hlo x hs
      rw [hl, Bool.or_false, Bool.or_false] at hlb
      subst hlb
      cases hc : x.isLoob
      · simp [h1, hs, hc] at hr
        subst hr
        refine ⟨INFO0, ?_, hI⟩
        simp [nock_exec, alJnBrzC, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, h1, infoN, hc, flag]
      · simp [h1, hs, hc, Opt.jabA] at hr
        subst hr
        obtain ⟨I', hj, hr'⟩ := loc_jab hI hN _ (infoRel_imm (lb := x.isLoob) hhs hts 1 (Or.inr rfl))
        have hj' := fun fs fc => hj alLsO fs fc (lsO_run x x.isLoob hs' ts fc)
        refine ⟨I', ?_, by simpa only [hc] using hr'⟩
        simp [nock_exec, alJnBrzC, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, by.jab.arm_at, hja, hj',
          h1, infoN, hc, flag]
  · simp [h1, h2] at hr
    subst hr
    exact ⟨INFO0, by simp [nock_exec, alJnBrzC, h1, h2], hI⟩

/-- **The refinement after a `%clq`.** -/
theorem al_jclq {INFO0 : Noun} {info : Opt.AInfo} (hI : InfoMapRel INFO0 info) (P1 P2 ZA OA PRE GEN NA BL REV T : Noun)
    (s zt ot o : Nat) {r : Opt.AInfo}
    (hr : (if zt = o ∧ ot ≠ o then Opt.jabA info s fun i => { i with isCell := true }
      else if ot = o then some info else none) = some r) :
    ∃ N, nock (C (C P1 (C P2 (C (A Tag.clq) (C (A s) (C (C ZA (A zt)) (C OA (A ot)))))))
      (C INFO0 (C PRE (alWS GEN NA BL REV (C (A o) T))))) alJnClq = some N ∧ InfoMapRel N r := by
  have hL := optC_layer2
  unfold alWS
  generalize optC = OC at hL
  rw [alJnClq_cut]
  by_cases h1 : zt = o <;> by_cases h2 : ot = o
  · subst h1
    subst h2
    simp at hr
    subst hr
    exact ⟨INFO0, by simp [nock_exec, alJnClqC], hI⟩
  · subst h1
    cases hs : info s with
    | none => simp [h2, Opt.jabA, hs] at hr
    | some x =>
      obtain ⟨lb, hs', ts, hhs, hts, hlb, hN, hgot, p0, q0, hja⟩ := info_jab_at hI hs
      simp [h2, Opt.jabA, hs] at hr
      subst hr
      obtain ⟨I', hj, hr'⟩ := loc_jab hI hN (infoN { x with isCell := true } lb hs' ts)
        (y := { x with isCell := true }) ⟨lb, hs', ts, rfl, hhs, hts, hlb⟩
      have hj' := fun fs fc => hj alLsC fs fc (lsC_run x lb hs' ts fc)
      refine ⟨I', ?_, hr'⟩
      simp [nock_exec, alJnClqC, hL, by.arm_at, by_arm, by.jab.arm_at, hja, hj', h2]
  · subst h2
    simp [h1] at hr
    subst hr
    exact ⟨INFO0, by simp [nock_exec, alJnClqC, h1], hI⟩
  · simp [h1, h2] at hr

/-! ## The refinement -/

/-- **The refinement after one predecessor `p`**, from its facts `i0`: the
model's `aliasStart g o [p]`. -/
theorem al_jnref {g : Opt.AGen (TreapMap mugF)} (hb : Opt.BrzInv g) {INFO0 : Noun} {i0 : Opt.AInfo}
    (hI : InfoMapRel INFO0 i0) (p o : Nat) (h0 : g.info p = some i0) {r : Opt.AInfo}
    (hr : Opt.aliasStart g o [p] = some r) (OLD INFO IMMS LOC IMML R F NA BL REV T : Noun) :
    ∃ N, nock (C INFO0 (C (listNoun A [p]) (alWS (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML
      R F) NA BL REV (C (A o) T)))) alJnRef = some N ∧ InfoMapRel N r := by
  have hpb := al_preb INFO0 p [] g.new OLD INFO IMMS LOC IMML R F NA BL REV (C (A o) T)
  simp only [Opt.aliasStart, h0, Option.bind_some, List.foldlM_nil, pure, ne_eq, not_true_eq_false,
    ↓reduceIte] at hr
  cases e : HoonMap.get g.new p with
  | none => rw [e] at hr; simp at hr
  | some pb =>
    rw [e] at hr hpb
    simp only [Option.bind_some] at hr
    obtain ⟨par, body, fin⟩ := pb
    cases hf : fin with
    | brn s z o' =>
      rw [hf] at hr hpb
      obtain ⟨za, zt⟩ := z
      obtain ⟨oa, ot⟩ := o'
      obtain ⟨N, hN, hrel⟩ := al_jbrn hI (listNoun A par) (listNoun Pole.toNoun body) (listNoun (unitNoun A) za)
        (listNoun (unitNoun A) oa) (listNoun A [p]) (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML
        R F) NA BL REV T s zt ot o hr
      refine ⟨N, ?_, hrel⟩
      simp only [Tag.brn] at hN
      simp [nock_exec, alJnRef, hpb, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.brn, hN]
    | brz s z o' =>
      rw [hf] at hr hpb
      obtain ⟨si, hsi, hl⟩ := Opt.brzInv_loob hb e
        (show ({ par := par, body := body, fin := fin } : Blob).fin = Termin.brz s z o' from hf) h0
      obtain ⟨za, zt⟩ := z
      obtain ⟨oa, ot⟩ := o'
      obtain ⟨N, hN, hrel⟩ := al_jbrz hI (listNoun A par) (listNoun Pole.toNoun body) (listNoun (unitNoun A) za)
        (listNoun (unitNoun A) oa) (listNoun A [p]) (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML
        R F) NA BL REV T s zt ot o (fun si' h => by rw [hsi] at h; cases h; exact hl) hr
      refine ⟨N, ?_, hrel⟩
      simp only [Tag.brz] at hN
      simp [nock_exec, alJnRef, hpb, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.brn, Tag.brz, hN]
    | clq s z o' =>
      rw [hf] at hr hpb
      obtain ⟨za, zt⟩ := z
      obtain ⟨oa, ot⟩ := o'
      obtain ⟨N, hN, hrel⟩ := al_jclq hI (listNoun A par) (listNoun Pole.toNoun body) (listNoun (unitNoun A) za)
        (listNoun (unitNoun A) oa) (listNoun A [p]) (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML
        R F) NA BL REV T s zt ot o hr
      refine ⟨N, ?_, hrel⟩
      simp only [Tag.clq] at hN
      simp [nock_exec, alJnRef, hpb, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.brn, Tag.brz, Tag.clq, hN]
    | _ =>
      rw [hf] at hr hpb
      simp at hr
      subst hr
      refine ⟨INFO0, ?_, hI⟩
      simp [nock_exec, alJnRef, hpb, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.brn, Tag.brz, Tag.clq, Tag.eqq,
        Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

end Compiler
end Formalization
