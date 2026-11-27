import lemmas.Compiler.OptLinkAlState
import lemmas.Compiler.CompLift
import lemmas.Ska.OptAliasBrz

/-!
# `+alias`: the end of a block, the ends that rename and `%eqq` (phase 14, README Gaps 13)

```hoon
  =^  fin-new=termin  gen
    ?-    -.fin.bob
        ...
        %hop  [fin.bob(args.t (turn args.t.fin.bob (lift rn))) gen]
        %jmp  [fin.bob(v (turn v.fin.bob rn)) gen]
        %jmf  [fin.bob(v (turn v.fin.bob rn)) gen]
        %jsp  [fin.bob(s (rn s.fin.bob)) gen]
        %jsf  [fin.bob(s (rn s.fin.bob)) gen]
        %don  [fin.bob(s (rn s.fin.bob)) gen]
        %bom  [fin.bob gen]
    ==
```

The `?-` (`alFin`) runs in the subject `[body-new [par-new [bob [imms [info
[pre WALK]]]]]]` (`alFS`), where `WALK` is the core of the walk (axis `127`,
`alWS GEN NA BL REV TOPO` of `OptLinkAlState.lean`, `gen` its axis `6`):
`fin.bob` is at `59`, `gen` at `510`, `o = i.topo` at `262126` (seen
after two pushes), and `rn` is the arm `10` of `WALK`.

* `alFS`: the subject; `alBat_rn`, `al_rn_arm`, `al_rn_gate`: the arm `rn`
  and its slam (`al_rn`).
* `alF_hop`, `alF_jmp`, `alF_jmf`, `alF_jsp`, `alF_jsf`, `alF_don`,
  `alF_bom`: **each of these cases returns `[fin-new gen]` with `fin-new`
  the model's end**, the registers renamed by `f` where `old.gen` is
  `OldRel` to `f`, and `gen` unchanged (`+turn` with `rn` by
  `mr_turn_ren`, with `(lift rn)` by `lf_turn`).
* `alF_jug_del`: **`+del:ju`** on a `JugRel` jug: the filter of the list at
  the key; `jugRel_congr`, `jugRel_delJu` (on lists without duplicates,
  `RevNodup`, that is `Opt.delJu`).
* `alF_got`: `(~(got by info-local.gen) c)` on an `InfoMapRel` map, where
  the model has facts at `c`: an `InfoRel` noun.
* `lb_atomImm`, `lb_none`: what `InfoRel` fixes of `is-loob`.
* `AlFinOK FC fin`: **what the link of an end states**, on a `gen` noun
  `GenRelL g loc imml` with `RevNodup g.rev`: where `aliasFin g.old loc
  g.rev g.folded o fin` returns `res`, the case `FC` returns `[fin-new gen]`
  with `fin-new` the noun of `res.1` and `gen` again `GenRelL` to `g` with
  `rev := res.2.1` and `folded := res.2.2`.
* `alF_eqq`: **`AlFinOK alFinEqq`**.  The other two-way ends are in
  `OptLinkAlFinClq.lean`, `OptLinkAlFinBrn.lean`, `OptLinkAlFinBrz.lean`,
  the dispatch `al_fin` in `OptLinkAlFinAll.lean`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The subject of the end: `[body-new [par-new [bob [imms [info [pre WALK]]]]]]`,
`WALK` the core of the walk. -/
def alFS (X1 X2 BOB X4 X5 X6 WALK : Noun) : Noun :=
  C X1 (C X2 (C BOB (C X4 (C X5 (C X6 WALK)))))

/-- The arm `rn` of the battery. -/
def alRnArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alRnB) (C (A 0) (A 1))))

theorem alBat_rn : ∃ R1 R2, alBat = C R1 (C alRnArm R2) := ⟨_, _, rfl⟩

theorem al_rn_arm (d : Noun) : nock d alRnArm = some (C alRnB (C (A 0) d)) := by
  simp [alRnArm, nock_exec]

/-- `rn` as a gate: the slam on `r` of `[alRnB [0 WALK]]` is `f r`. -/
theorem al_rn_gate (R1 R2 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f) (r : Nat) :
    nock (C alRnB (C (A r) (C (C R1 (C alRnArm R2)) (C (C NEW (C OLD REST)) (C Y (C Z optC)))))) alRnB
      = some (A (f r)) :=
  al_rn _ Y Z NEW OLD REST f h r

/-! ## The ends that only rename -/

theorem alF_don (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (s : Nat) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.don s)))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        alFinDon
      = some (C (Termin.toNoun (Termin.don (f s))) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn
  simp [nock_exec, alFinDon, al_rn_arm, Termin.toNoun, hrn]

theorem alF_jsp (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (s : Nat) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jsp a s)))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        alFinJsp
      = some (C (Termin.toNoun (Termin.jsp a (f s))) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn
  simp [nock_exec, alFinJsp, al_rn_arm, Termin.toNoun, hrn]

theorem alF_jsf (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (s : Nat) (n : Ring) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jsf a s n)))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        alFinJsf
      = some (C (Termin.toNoun (Termin.jsf a (f s) n)) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn
  simp [nock_exec, alFinJsf, al_rn_arm, Termin.toNoun, hrn]

theorem alF_jmp (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (v : List Nat) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jmp a v)))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        alFinJmp
      = some (C (Termin.toNoun (Termin.jmp a (v.map f))) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  have ht := mr_turn_ren alRnB (A 0) _ f hrn v
  have hL := optC_layer2
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn ht hL
  simp [nock_exec, alFinJmp, al_rn_arm, Termin.toNoun, hL, turn.arm_at, turn_arm, ht]

theorem alF_jmf (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (v : List Nat) (n : Ring) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jmf a v n)))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        alFinJmf
      = some (C (Termin.toNoun (Termin.jmf a (v.map f) n)) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  have ht := mr_turn_ren alRnB (A 0) _ f hrn v
  have hL := optC_layer2
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn ht hL
  simp [nock_exec, alFinJmf, al_rn_arm, Termin.toNoun, hL, turn.arm_at, turn_arm, ht]

theorem alF_hop (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (t : Jmp) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.hop t)))) X4 X5 X6 (C alBat (C (C NEW (C OLD REST)) (C Y (C Z optC)))))
        alFinHop
      = some (C (Termin.toNoun (Termin.hop { t with args := t.args.map (Option.map f) }))
          (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  have ht := lf_turn alRnB (A 0) _ f hrn t.args
  have hL := optC_layer2
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn ht hL
  obtain ⟨args, there⟩ := t
  simp [nock_exec, alFinHop, al_rn_arm, Termin.toNoun, Jmp.toNoun, hL, turn.arm_at, turn_arm, lf_lift_at,
    lf_lift_slam, ht]

theorem alF_bom (X1 X2 P B X4 X5 X6 GEN Y Z : Noun) (fin : Termin) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun fin))) X4 X5 X6 (C alBat (C GEN (C Y (C Z optC))))) alFinLast
      = some (C (Termin.toNoun fin) GEN) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  unfold alFS
  rw [hB]
  generalize optC = OC
  cases fin <;> simp [nock_exec, alFinLast, Termin.toNoun]

/-! ## Helpers of the two-way ends -/

/-- **`+del:ju`** of the label `o` under the label `k`: the members of `f k`
other than `o`. -/
theorem alF_jug_del {J : Noun} {f : Nat → List Nat} (h : JugRel J f) (k o : Nat) :
    ∃ J', nock (C ju.del.battery (C (C (A k) (A o)) (C ju.battery (C J layer2)))) ju.del.battery = some J' ∧
      JugRel J' (Opt.updA f k ((f k).filter fun x => x ≠ o)) := by
  obtain ⟨out, hg, hS⟩ := h.2 k
  have hm : IsMap mugF (toMap (unUnit out)) := hS.1
  obtain ⟨out', hd, -, -⟩ := delF_spec (A o) hm
  rw [delF_toMap (A o) _ hS.1] at hd
  cases hx : delInF mugF (A o) (unUnit out) with
  | none => rw [hx] at hd; cases hd
  | some e =>
    obtain ⟨S', hn, hS'⟩ := saw_del hS o
    rw [del_in_gate layer2 gorIn_morIn_layer2 (A o) _ e hx] at hn
    cases hn
    by_cases e0 : e = A 0
    · obtain ⟨J', hdJ, hmJ, hgJ⟩ := delF_spec (A k) h.1
      have hj : juDelF mugF (A k) (A o) J = some J' := by
        simp [juDelF, juGetF, hg, hx, e0, hdJ]
      refine ⟨J', ju_del_gate layer2 juIn_layer2' _ _ _ _ hj, hmJ, fun p => ?_⟩
      have hga := getF_after_del h.1 hmJ hgJ (A p)
      by_cases e1 : p = k
      · subst e1
        refine ⟨A 0, by simp [hga], ?_⟩
        rw [e0] at hS'
        simpa [Opt.updA, unUnit] using hS'
      · have hne : A p ≠ A k := fun e => e1 (Noun.atom.inj e)
        obtain ⟨out2, hg2, hS2⟩ := h.2 p
        exact ⟨out2, by rw [hga, if_neg hne, hg2], by simpa [Opt.updA, e1] using hS2⟩
    · obtain ⟨J', hpJ, hmJ, hgJ⟩ := putF_spec mugF J (A k) e h.1
      have hj : juDelF mugF (A k) (A o) J = some J' := by
        simp [juDelF, juGetF, hg, hx, e0, hpJ]
      refine ⟨J', ju_del_gate layer2 juIn_layer2' _ _ _ _ hj, hmJ, fun p => ?_⟩
      have hga := getF_after_put h.1 hmJ hgJ (A p)
      by_cases e1 : p = k
      · subst e1
        exact ⟨C (A 0) e, by simp [hga], by simpa [Opt.updA, unUnit] using hS'⟩
      · have hne : A p ≠ A k := fun e => e1 (Noun.atom.inj e)
        obtain ⟨out2, hg2, hS2⟩ := h.2 p
        exact ⟨out2, by rw [hga, if_neg hne, hg2], by simpa [Opt.updA, e1] using hS2⟩

/-- `JugRel` reads only the members of the lists. -/
theorem jugRel_congr {J : Noun} {f g : Nat → List Nat} (h : JugRel J f) (hfg : ∀ p x, x ∈ f p ↔ x ∈ g p) :
    JugRel J g := by
  refine ⟨h.1, fun p => ?_⟩
  obtain ⟨out, hg, hS⟩ := h.2 p
  refine ⟨out, hg, hS.1, fun k => ?_⟩
  rw [hS.2 k]
  simp only [hfg]

/-- On lists without duplicates, the members of `delJu` are those of the filter. -/
theorem jugRel_delJu {J : Noun} {f : Nat → List Nat} (hnd : Opt.RevNodup f) {k o : Nat}
    (h : JugRel J (Opt.updA f k ((f k).filter fun x => x ≠ o))) : JugRel J (Opt.delJu f k o) := by
  refine jugRel_congr h fun p x => ?_
  unfold Opt.delJu Opt.updA
  by_cases e : p = k
  · subst e
    simp only [if_true, List.mem_filter, (hnd p).mem_erase_iff]
    simp [and_comm]
  · simp [e]

/-- `(~(got by info-local.gen) c)` on a register with facts. -/
theorem alF_got {LOC : Noun} {loc : Opt.AInfo} (h : InfoMapRel LOC loc) {c : Nat} {ic : Opt.InfoReg}
    (hc : loc c = some ic) :
    ∃ v, nock (C by.got.battery (C (A c) (C by.battery (C LOC layer2)))) by.got.battery = some v ∧
      InfoRel v ic := by
  obtain ⟨v, hv⟩ := h.2.2 c ic hc
  obtain ⟨r, x, e, hx, hr⟩ := h.2.1 _ _ hv
  cases e
  rw [hc] at hx
  cases hx
  exact ⟨v, got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _
    (getF_some h.1 hv), hr⟩

/-- The state after the end: `rev` and `folded` replaced. -/
theorem genRelL_fin {g : Opt.AGen (TreapMap mugF)} {loc : Opt.AInfo} {imml : Opt.AImms}
    {OLD INFO IMMS LOC IMML REV' : Noun} (hO : OldRel OLD g.old) (hI : InfoStoreRel INFO g.info)
    (hM : ImmsStoreRel IMMS g.imms) (hL : InfoMapRel LOC loc) (hIm : ImmsRel IMML imml)
    {rev' : Nat → List Nat} (hR : JugRel REV' rev') (f' : Bool) :
    GenRelL { g with rev := rev', folded := f' } loc imml
      (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV' (flag f')) :=
  ⟨OLD, INFO, IMMS, LOC, IMML, REV', rfl, hO, hI, hM, hR, hL, hIm⟩

/-- `InfoRel` fixes `is-loob` up to `loobImm`, so up to `atomImm`. -/
theorem lb_atomImm {lb : Bool} {ic : Opt.InfoReg} (h : (lb || ic.loobImm) = (ic.isLoob || ic.loobImm)) :
    (lb || ic.atomImm) = (ic.isLoob || ic.atomImm) := by
  unfold Opt.InfoReg.atomImm
  unfold Opt.InfoReg.loobImm at h
  rcases e : ic.hasImm with _ | ⟨n | _⟩ <;> simp [e] at h ⊢ <;> simp_all

/-- With no immediate, `InfoRel` fixes `is-loob`. -/
theorem lb_none {lb : Bool} {ic : Opt.InfoReg} (h : (lb || ic.loobImm) = (ic.isLoob || ic.loobImm))
    (e : ic.hasImm = none) : lb = ic.isLoob := by
  unfold Opt.InfoReg.loobImm at h
  simpa [e] using h

/-- **What the link of an end states**: where the model's `aliasFin` returns
`res`, the case `FC` returns `[fin-new gen]` with `fin-new` the noun of the
new end and `gen` related to the model's state with `rev` and `folded` of
`res`. -/
def AlFinOK (FC : Noun) (fin : Termin) : Prop :=
  ∀ (g : Opt.AGen (TreapMap mugF)) (loc : Opt.AInfo) (imml : Opt.AImms) (N : Noun), GenRelL g loc imml N →
    Opt.RevNodup g.rev →
    ∀ (X1 X2 P B X4 X5 X6 NA BL REVA TR : Noun) (o : Nat) (res : Termin × (Nat → List Nat) × Bool),
      Opt.aliasFin g.old loc g.rev g.folded o fin = some res →
      ∃ N', nock (alFS X1 X2 (C P (C B (Termin.toNoun fin))) X4 X5 X6 (alWS N NA BL REVA (C (A o) TR))) FC
          = some (C (Termin.toNoun res.1) N') ∧
        GenRelL { g with rev := res.2.1, folded := res.2.2 } loc imml N'

/-! ## `%eqq` -/

theorem alF_eqq (l r : Nat) (z o' : Jmp) : AlFinOK alFinEqq (Termin.eqq l r z o') := by
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
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 (HoonMap.toNoun Blob.toNoun g.new) OLD (C INFO (C IMMS (C LOC (C IMML
    (C REV (flag g.folded)))))) alBodyCut (C NA (C BL (C REVA (C (A o) TR)))) g.old hO
  have hL2 := optC_layer2
  by_cases e : g.old l = g.old r
  · simp [Opt.aliasFin, Opt.aliasFold, e] at hres
    subst hres
    by_cases e2 : ot = zt
    · subst e2
      refine ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag true), ?_,
        by simpa using genRelL_fin hO hI hM hL hIm hR true⟩
      unfold alFS alWS genN
      rw [hB]
      generalize HoonMap.toNoun Blob.toNoun g.new = NEW at hrn
      generalize optC = OC at hrn hL2
      generalize flag g.folded = FL at hrn
      simp [nock_exec, alFinEqq, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, hrn, e, flag]
    · obtain ⟨D, hD1, hD2⟩ := alF_jug_del hR ot o
      have e2' : zt ≠ ot := fun h => e2 h.symm
      refine ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML D (flag true), ?_,
        by simpa [e2'] using genRelL_fin hO hI hM hL hIm (jugRel_delJu hnd hD2) true⟩
      unfold alFS alWS genN
      rw [hB]
      generalize HoonMap.toNoun Blob.toNoun g.new = NEW at hrn
      generalize optC = OC at hrn hL2
      generalize flag g.folded = FL at hrn
      simp [nock_exec, alFinEqq, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.hop, hrn, e, e2, e2',
        flag, hL2, ju.arm_at, ju_arm, ju.del.arm_at, ju_del_arm, hD1]
  · simp [Opt.aliasFin, e] at hres
    subst hres
    refine ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag g.folded), ?_,
      genRelL_fin hO hI hM hL hIm hR g.folded⟩
    unfold alFS alWS genN
    rw [hB]
    generalize HoonMap.toNoun Blob.toNoun g.new = NEW at hrn
    generalize optC = OC at hrn hL2
    generalize flag g.folded = FL at hrn ⊢
    simp [nock_exec, alFinEqq, al_rn_arm, Termin.toNoun, Jmp.toNoun, listNoun, Tag.eqq, hrn, e]

end Compiler
end Formalization
