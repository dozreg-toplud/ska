import lemmas.Compiler.OptLinkSwUses

/-!
# `+switch-chains`: the gate `test-of`

```hoon
  =/  test-of
    |=  p=@uwoo
    ^-  (unit test)
    =/  b=blob  (~(got by blocks) p)
    ?.  ?=([%clq * [~ *] [~ *]] fin.b)  ~
    =/  y=@uwoo  there.z.fin.b
    =/  n=@uwoo  there.o.fin.b
    ?.  =(~[p] (~(get ja rev) y))  ~
    =/  yb=blob  (~(got by blocks) y)
    ?.  ?=(~ par.yb)  ~
    ?.  ?=([%eqq * * [~ *] [~ *]] fin.yb)  ~
    ?.  =(n there.o.fin.yb)  ~
    =/  bod=(list pole)  body.yb
    ?.  ?=([* * ~] bod)  ~
    =/  h=(unit [s=@uvre d=@uvre])  ..
    =/  m=(unit [n=* d=@uvre])  ..
    ?~  h  ~
    ?~  m  ~
    ?.  =(s.u.h s.fin.b)  ~
    =/  c=*  n.u.m
    ?.  ?=(@ c)  ~
    ?.  (lth c (bex 31))  ~
    ?.  ?|  =([l r]:fin.yb [d.u.h d.u.m])
            =([l r]:fin.yb [d.u.m d.u.h])
        ==
      ~
    ?.  ?&  =(2 (~(gut by uses) d.u.h 0))
            =(2 (~(gut by uses) d.u.m 0))
        ==
      ~
    `[s.fin.b c there.z.fin.yb n y d.u.h d.u.m]
```

The gate runs on `[p S3]` with `S3` the subject after `uses`
(`swS3`).  Each step is stated as the subject it starts from and the model
of the rest: `toC`, `toHM`, `toBod`, `toYb` (`test-of` from `c`, from `h`,
from `bod`, from `yb`), with `testOf_eq` restating the model's `testOf` by
them.

* `to_clq`, `to_eqq`: the tests of the terminators are `clqNA`, `eqqNA`.
* `to_h`, `to_m`: the units `h` and `m` are `hedOf2` and `immOf2`.
* `sw_test`: **the gate `test-of` is `testOf`**, crashes included.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem mulIn_below_layer2 : Below MulIn layer2 := arith_layer1.2.2.1

/-! ## The model, step by step -/

/-- A `%clq` with jumps that pass nothing. -/
def clqNA : Termin → Option (Nat × Nat × Nat)
  | Termin.clq s ⟨[], y⟩ ⟨[], n⟩ => some (s, y, n)
  | _ => none

/-- An `%eqq` with jumps that pass nothing. -/
def eqqNA : Termin → Option (Nat × Nat × Nat × Nat)
  | Termin.eqq l r ⟨[], hit⟩ ⟨[], n⟩ => some (l, r, hit, n)
  | _ => none

/-- `test-of` from `c`. -/
def toC (u : Nat → Nat) (s y n hit l r hd md : Nat) (mn : Noun) : Option Opt.STest :=
  match Opt.smallAtom mn with
  | some c =>
    if ¬ ((l, r) = (hd, md) ∨ (l, r) = (md, hd)) then none else
    if ¬ (u hd = 2 ∧ u md = 2) then none else
    some ⟨s, c, hit, n, y, hd, md⟩
  | none => none

/-- `test-of` from `h`. -/
def toHM (u : Nat → Nat) (s y n hit l r : Nat) (i0 i1 : Pole) : Option Opt.STest :=
  match Opt.hedOf2 i0 i1, Opt.immOf2 i0 i1 with
  | some (hs, hd), some (mn, md) => if hs ≠ s then none else toC u s y n hit l r hd md mn
  | _, _ => none

/-- `test-of` from `bod`. -/
def toBod (u : Nat → Nat) (s y n hit l r : Nat) : List Pole → Option Opt.STest
  | [i0, i1] => toHM u s y n hit l r i0 i1
  | _ => none

/-- `test-of` from `yb`. -/
def toYb (u : Nat → Nat) (s y n : Nat) (yb : Blob) : Option Opt.STest :=
  if yb.par ≠ [] then none else
  match eqqNA yb.fin with
  | some (l, r, hit, n') => if n ≠ n' then none else toBod u s y n hit l r yb.body
  | none => none

/-- The `%hed` of one op. -/
def hed1 : Pole → Option (Nat × Nat)
  | Pole.hed s d => some (s, d)
  | _ => none

/-- The `%imm` of one op. -/
def imm1 : Pole → Option (Noun × Nat)
  | Pole.imm n d => some (n, d)
  | _ => none

theorem hedOf2_eq (i0 i1 : Pole) : Opt.hedOf2 i0 i1 = (hed1 i0).or (hed1 i1) := by
  cases i0 <;> cases i1 <;> rfl

theorem immOf2_eq (i0 i1 : Pole) : Opt.immOf2 i0 i1 = (imm1 i0).or (imm1 i1) := by
  cases i0 <;> cases i1 <;> rfl

/-! ## The subjects -/

/-- The subject of the gate: `[swTOB [p S3]]`. -/
def toG (p : Nat) (BL TOPO REV USES : Noun) : Noun := C swTOB (C (A p) (swS3 BL TOPO REV USES))

/-- The noun of `h`. -/
def hN (h : Option (Nat × Nat)) : Noun := unitNoun (fun x => C (A x.1) (A x.2)) h

/-- The noun of `m`. -/
def mN (m : Option (Noun × Nat)) : Noun := unitNoun (fun x => C x.1 (A x.2)) m

/-- The subject from `yb` on: `[yb [n [y [b gate]]]]`, `yb` ending in an
`%eqq` and `b` in a `%clq`. -/
def toR (p s y n hit l r : Nat) (z o z2 : Jmp) (BP BB YP YB BL TOPO REV USES : Noun) : Noun :=
  C (C YP (C YB (Termin.eqq l r ⟨[], hit⟩ z2).toNoun)) (C (A n) (C (A y)
    (C (C BP (C BB (Termin.clq s z o).toNoun)) (toG p BL TOPO REV USES))))

/-- The subject from `bod` on: `[bod [yb [n [y [b gate]]]]]`. -/
def toX (p s y n hit l r : Nat) (z o z2 : Jmp) (BP BB YP YB BOD BL TOPO REV USES : Noun) : Noun :=
  C BOD (toR p s y n hit l r z o z2 BP BB YP YB BL TOPO REV USES)

/-! ## From `c` -/

theorem to_eq (c p s y n hit l r hs hd md : Nat) (z o z2 : Jmp) (BP BB YP YB BOD BL TOPO REV USES : Noun)
    (e : Bool) (he : e = true ↔ ((l, r) = (hd, md) ∨ (l, r) = (md, hd))) :
    nock (C (A c) (C (C (A 0) (C (A c) (A md))) (C (C (A 0) (C (A hs) (A hd)))
      (toX p s y n hit l r z o z2 BP BB YP YB BOD BL TOPO REV USES)))) swTOEq = some (loob e) := by
  unfold toX toR
  by_cases e1 : l = hd ∧ r = md
  · obtain ⟨rfl, rfl⟩ := e1
    have : e = true := he.2 (Or.inl rfl)
    subst this
    simp [nock_exec, swTOEq, Termin.toNoun, loob]
  · by_cases e2 : l = md ∧ r = hd
    · obtain ⟨rfl, rfl⟩ := e2
      have : e = true := he.2 (Or.inr rfl)
      subst this
      simp [nock_exec, swTOEq, Termin.toNoun, loob, eq_false e1]
    · have : e = false := by
        cases e
        · rfl
        · exfalso
          rcases he.1 rfl with h | h
          · simp only [Prod.mk.injEq] at h; exact e1 h
          · simp only [Prod.mk.injEq] at h; exact e2 h
      subst this
      simp [nock_exec, swTOEq, Termin.toNoun, loob, eq_false e1, eq_false e2]

theorem to_c (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl))
    (p s y n hit l r hs hd md : Nat) (mn : Noun) (z o z2 : Jmp) (BP BB YP YB BOD : Noun) :
    nock (C (C (A 0) (C mn (A md))) (C (C (A 0) (C (A hs) (A hd)))
      (toX p s y n hit l r z o z2 BP BB YP YB BOD (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES)))
      swTOC = some (unitNoun stestN (toC (Opt.usesOf bl) s y n hit l r hd md mn)) := by
  have hL := optC_layer2
  have hL1 := optC_layer1
  have hg1 := uses_gut hU hd
  have hg2 := uses_gut hU md
  cases mn with
  | cell a b =>
    unfold toX toR toG swS3 swG
    simp [nock_exec, swTOC, toC, Opt.smallAtom, unitNoun]
  | atom c =>
    have hlt := lth_gate layer1 decIn_layer1 c (2 ^ 31)
    have hbx := bex_gate layer2 mulIn_below_layer2 31
    have hk := to_eq c p s y n hit l r hs hd md z o z2 BP BB YP YB BOD (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES
      (decide ((l, r) = (hd, md) ∨ (l, r) = (md, hd))) (by simp)
    unfold toX toR toG swS3 swG at *
    generalize optC = OC at hL hL1 hk
    generalize HoonMap.toNoun Blob.toNoun bl = BL at hk
    generalize Opt.usesOf bl = u at hg1 hg2
    by_cases hc : c < 2 ^ 31
    · by_cases he : (l, r) = (hd, md) ∨ (l, r) = (md, hd)
      · simp only [decide_eq_true he] at hk
        by_cases hu : u hd = 2 ∧ u md = 2
        · have hm : toC u s y n hit l r hd md (A c) = some ⟨s, c, hit, n, y, hd, md⟩ := by
            unfold toC; simp only [Opt.smallAtom, hc, if_true]; rw [if_neg (not_not_intro he), if_neg (not_not_intro hu)]
          simp [nock_exec, swTOC, swTOLth, swTOUses, hm, unitNoun, hc, hu.1, hu.2, hL, hL1,
            lth.arm_at, lth_arm, hlt, bex.arm_at, bex_arm, hbx, by.arm_at, by_arm, by.gut.arm_at, gut_arm, hg1,
            hg2, hk, stestN, loob]
        · have hm : toC u s y n hit l r hd md (A c) = none := by
            unfold toC; simp only [Opt.smallAtom, hc, if_true]; rw [if_neg (not_not_intro he), if_pos hu]
          by_cases hu1 : u hd = 2
          · have hu2 : ¬ u md = 2 := fun h => hu ⟨hu1, h⟩
            simp [nock_exec, swTOC, swTOLth, swTOUses, hm, unitNoun, hc, hu1, hu2, Ne.symm hu2,
              hL, hL1, lth.arm_at, lth_arm, hlt, bex.arm_at, bex_arm, hbx, by.arm_at, by_arm, by.gut.arm_at, gut_arm,
              hg1, hg2, hk, stestN, loob]
          · simp [nock_exec, swTOC, swTOLth, swTOUses, hm, unitNoun, hc, hu1, Ne.symm hu1,
              hL, hL1, lth.arm_at, lth_arm, hlt, bex.arm_at, bex_arm, hbx, by.arm_at, by_arm, by.gut.arm_at, gut_arm,
              hg1, hg2, hk, stestN, loob]
      · simp only [decide_eq_false he] at hk
        have hm : toC u s y n hit l r hd md (A c) = none := by
          unfold toC; simp only [Opt.smallAtom, hc, if_true]; rw [if_pos he]
        simp [nock_exec, swTOC, swTOLth, hm, unitNoun, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
          bex.arm_at, bex_arm, hbx, hk, loob]
    · simp [nock_exec, swTOC, swTOLth, toC, Opt.smallAtom, unitNoun, hc, hL, hL1, lth.arm_at, lth_arm, hlt,
        bex.arm_at, bex_arm, hbx, loob]

/-! ## From `=(s.u.h s.fin.b)` -/

theorem to_s (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl))
    (p s y n hit l r hs hd md : Nat) (mn : Noun) (z o z2 : Jmp) (BP BB YP YB BOD : Noun) :
    nock (C (C (A 0) (C mn (A md))) (C (C (A 0) (C (A hs) (A hd)))
      (toX p s y n hit l r z o z2 BP BB YP YB BOD (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES)))
      swTOS = some (unitNoun stestN (if hs ≠ s then none else toC (Opt.usesOf bl) s y n hit l r hd md mn)) := by
  have hc := to_c bl TOPO REV USES hU p s y n hit l r hs hd md mn z o z2 BP BB YP YB BOD
  unfold toX toR at hc ⊢
  simp only [Termin.toNoun] at hc
  generalize toG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES = G at hc ⊢
  by_cases e : hs = s
  · subst e; simp [nock_exec, swTOS, hc, Termin.toNoun]
  · simp [nock_exec, swTOS, e, Termin.toNoun, unitNoun]

/-! ## `h` and `m` -/

theorem to_h1 (i1 : Pole) (Y Z W : Noun) : nock (C (C Y (C i1.toNoun Z)) W) swTOH1 = some (hN (hed1 i1)) := by
  unfold swTOH1
  cases i1 <;> simp [nock_exec, Pole.toNoun, hed1, hN, unitNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

theorem to_h (i0 i1 : Pole) (Z W : Noun) :
    nock (C (C i0.toNoun (C i1.toNoun Z)) W) swTOH = some (hN (Opt.hedOf2 i0 i1)) := by
  rw [hedOf2_eq]
  have h1 := to_h1 i1
  unfold swTOH
  generalize hed1 i1 = H1 at h1 ⊢
  generalize i1.toNoun = I1 at h1 ⊢
  cases i0 <;> simp [nock_exec, Pole.toNoun, hed1, hN, unitNoun, h1, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

theorem to_m1 (i1 : Pole) (H Y Z W : Noun) : nock (C H (C (C Y (C i1.toNoun Z)) W)) swTOM1 = some (mN (imm1 i1)) := by
  unfold swTOM1
  cases i1 <;> simp [nock_exec, Pole.toNoun, imm1, mN, unitNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

theorem to_m (i0 i1 : Pole) (H Z W : Noun) :
    nock (C H (C (C i0.toNoun (C i1.toNoun Z)) W)) swTOM = some (mN (Opt.immOf2 i0 i1)) := by
  rw [immOf2_eq]
  have h1 := to_m1 i1
  unfold swTOM
  generalize imm1 i1 = M1 at h1 ⊢
  generalize i1.toNoun = I1 at h1 ⊢
  cases i0 <;> simp [nock_exec, Pole.toNoun, imm1, mN, unitNoun, h1, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

/-! ## From `h` -/

theorem to_hm (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl))
    (p s y n hit l r : Nat) (z o z2 : Jmp) (BP BB YP YB : Noun) (i0 i1 : Pole) :
    nock (toX p s y n hit l r z o z2 BP BB YP YB (C i0.toNoun (C i1.toNoun (A 0))) (HoonMap.toNoun Blob.toNoun bl)
      TOPO REV USES) swTOHM = some (unitNoun stestN (toHM (Opt.usesOf bl) s y n hit l r i0 i1)) := by
  cases hh0 : Opt.hedOf2 i0 i1 with
  | none =>
    unfold toX
    simp [nock_exec, swTOHM, to_h, to_m, hh0, hN, unitNoun, toHM]
  | some hp =>
    obtain ⟨hs, hd⟩ := hp
    cases hm0 : Opt.immOf2 i0 i1 with
    | none =>
      unfold toX
      simp [nock_exec, swTOHM, to_h, to_m, hh0, hm0, hN, mN, unitNoun, toHM]
    | some mp =>
      obtain ⟨mn, md⟩ := mp
      have hs' := to_s bl TOPO REV USES hU p s y n hit l r hs hd md mn z o z2 BP BB YP YB
        (C i0.toNoun (C i1.toNoun (A 0)))
      unfold toX at hs' ⊢
      simp [nock_exec, swTOHM, to_h, to_m, hh0, hm0, hN, mN, unitNoun, hs', toHM]

/-! ## From `bod` -/

theorem to_bod (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl))
    (p s y n hit l r : Nat) (z o z2 : Jmp) (BP BB YP : Noun) (body : List Pole) :
    nock (toR p s y n hit l r z o z2 BP BB YP (listNoun Pole.toNoun body) (HoonMap.toNoun Blob.toNoun bl)
      TOPO REV USES) swTOBod = some (unitNoun stestN (toBod (Opt.usesOf bl) s y n hit l r body)) := by
  match body with
  | [i0, i1] =>
    have h := to_hm bl TOPO REV USES hU p s y n hit l r z o z2 BP BB YP (listNoun Pole.toNoun [i0, i1]) i0 i1
    unfold toX toR at h
    simp only [Termin.toNoun, listNoun] at h
    unfold toR
    simp [nock_exec, swTOBod, listNoun, h, toBod, Termin.toNoun]
  | [] =>
    unfold toR
    simp [nock_exec, swTOBod, listNoun, toBod, unitNoun, Termin.toNoun]
  | [i0] =>
    unfold toR
    simp [nock_exec, swTOBod, listNoun, toBod, unitNoun, Termin.toNoun]
  | i0 :: i1 :: i2 :: rest =>
    unfold toR
    simp [nock_exec, swTOBod, listNoun, toBod, unitNoun, Termin.toNoun]

/-! ## The tests of the terminators -/

theorem to_clq (t : Termin) (P BOD X : Noun) :
    nock (C (C P (C BOD t.toNoun)) X) swTOClq = some (loob (clqNA t).isSome) := by
  unfold swTOClq
  cases t with
  | clq s z o =>
    obtain ⟨za, zt⟩ := z
    obtain ⟨oa, ot⟩ := o
    cases za <;> cases oa <;> simp [nock_exec, Termin.toNoun, Jmp.toNoun, listNoun, clqNA, loob, eqCode, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]
  | _ => simp [nock_exec, Termin.toNoun, clqNA, loob, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

theorem to_eqq (t : Termin) (P BOD X : Noun) :
    nock (C (C P (C BOD t.toNoun)) X) swTOEqq = some (loob (eqqNA t).isSome) := by
  unfold swTOEqq
  cases t with
  | eqq l r z o =>
    obtain ⟨za, zt⟩ := z
    obtain ⟨oa, ot⟩ := o
    cases za <;> cases oa <;> simp [nock_exec, Termin.toNoun, Jmp.toNoun, listNoun, eqqNA, loob, eqCode, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]
  | _ => simp [nock_exec, Termin.toNoun, eqqNA, loob, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

theorem clqNA_some {t : Termin} {s y n : Nat} (h : clqNA t = some (s, y, n)) :
    t = Termin.clq s ⟨[], y⟩ ⟨[], n⟩ := by
  unfold clqNA at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · cases h

theorem eqqNA_some {t : Termin} {l r hit n : Nat} (h : eqqNA t = some (l, r, hit, n)) :
    t = Termin.eqq l r ⟨[], hit⟩ ⟨[], n⟩ := by
  unfold eqqNA at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  · cases h

/-! ## From `yb` -/

theorem to_yb (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) (hU : UsesRel USES (Opt.usesOf bl))
    (p s y n : Nat) (z o : Jmp) (BP BB : Noun) :
    nock (C (A n) (C (A y) (C (C BP (C BB (Termin.clq s z o).toNoun))
      (toG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES)))) swTOYb
      = (HoonMap.get bl y).map (fun yb => unitNoun stestN (toYb (Opt.usesOf bl) s y n yb)) := by
  have hg := blocks_got bl y
  have hL := optC_layer2
  cases hy : HoonMap.get bl y with
  | none =>
    rw [hy] at hg
    unfold toG swS3 swG
    generalize optC = OC at hL
    generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
    simp [nock_exec, swTOYb, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
  | some yb =>
    rw [hy] at hg
    obtain ⟨ypar, ybody, yfin⟩ := yb
    cases ypar with
    | cons a ypar =>
      unfold toG swS3 swG
      generalize optC = OC at hL
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
      simp only [Option.map_some, Blob.toNoun] at hg
      simp [nock_exec, swTOYb, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, listNoun, toYb, unitNoun]
    | nil =>
      have he := to_eqq yfin (A 0) (listNoun Pole.toNoun ybody)
        (C (A n) (C (A y) (C (C BP (C BB (Termin.clq s z o).toNoun)) (toG p (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES))))
      cases hq : eqqNA yfin with
      | none =>
        rw [hq] at he
        unfold toG swS3 swG at *
        generalize optC = OC at hL he
        generalize HoonMap.toNoun Blob.toNoun bl = BL at hg he
        simp only [Option.map_some, Blob.toNoun] at hg
        simp [nock_exec, swTOYb, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, listNoun, toYb, unitNoun, he,
          hq, loob]
      | some q =>
        obtain ⟨l, r, hit, n'⟩ := q
        have ht := eqqNA_some hq
        subst ht
        rw [hq] at he
        by_cases hn : n = n'
        · subst hn
          have hb := to_bod bl TOPO REV USES hU p s y n hit l r z o ⟨[], n⟩ BP BB (A 0) ybody
          unfold toR toG swS3 swG at *
          simp only [Termin.toNoun, Jmp.toNoun, listNoun] at he hb
          generalize optC = OC at hL he hb
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hg he hb
          simp only [Option.map_some, Blob.toNoun] at hg
          simp [nock_exec, swTOYb, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, listNoun, toYb, he, hq,
            loob, hb, Termin.toNoun, Jmp.toNoun]
        · unfold toG swS3 swG at *
          simp only [Termin.toNoun, Jmp.toNoun, listNoun] at he
          generalize optC = OC at hL he
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hg he
          simp only [Option.map_some, Blob.toNoun] at hg
          simp [nock_exec, swTOYb, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, listNoun, toYb, he, hq,
            loob, Termin.toNoun, Jmp.toNoun, hn, unitNoun]

/-! ## From `y` -/

theorem pair_eq_listNoun (p : Nat) : ∀ l : List Nat, (C (A p) (A 0) = listNoun A l) ↔ l = [p]
  | [] => by simp [listNoun]
  | [q] => by simp [listNoun, eq_comm]
  | q :: q' :: l => by simp [listNoun]

theorem to_y (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TOPO USES : Noun)
    (hU : UsesRel USES (Opt.usesOf bl)) (p s y n : Nat) (BP BB : Noun) :
    nock (C (C BP (C BB (Termin.clq s ⟨[], y⟩ ⟨[], n⟩).toNoun))
      (toG p (HoonMap.toNoun Blob.toNoun bl) TOPO (jarN rev) USES)) swTOY
      = if Opt.getJa rev y ≠ [p] then some (A 0)
        else (HoonMap.get bl y).map (fun yb => unitNoun stestN (toYb (Opt.usesOf bl) s y n yb)) := by
  have hj := jar_get rev y
  have hyb := to_yb bl TOPO (jarN rev) USES hU p s y n ⟨[], y⟩ ⟨[], n⟩ BP BB
  have hL := optC_layer2
  unfold toG swS3 swG at *
  simp only [Termin.toNoun, Jmp.toNoun, listNoun] at hyb
  generalize optC = OC at hL hyb
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hyb
  generalize (HoonMap.get bl y).map (fun yb => unitNoun stestN (toYb (Opt.usesOf bl) s y n yb)) = R at hyb
  by_cases hr : Opt.getJa rev y = [p]
  · rw [hr] at hj
    simp [nock_exec, swTOY, hL, ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, hyb, hr, Termin.toNoun,
      Jmp.toNoun, listNoun, eqCode]
  · simp [nock_exec, swTOY, hL, ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, hr, Termin.toNoun,
      Jmp.toNoun, listNoun, eqCode, pair_eq_listNoun]

/-! ## The gate -/

/-- `testOf` by the steps. -/
theorem testOf_eq (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (p : Nat) :
    Opt.testOf bl rev p = (HoonMap.get bl p).bind (fun b => match clqNA b.fin with
      | none => some none
      | some (s, y, n) => if Opt.getJa rev y ≠ [p] then some none
          else (HoonMap.get bl y).map (toYb (Opt.usesOf bl) s y n)) := by
  unfold Opt.testOf
  cases HoonMap.get bl p with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    obtain ⟨par, body, fin⟩ := b
    match fin with
    | .eqq .. | .brn .. | .brz .. | .hop .. | .jmp .. | .jmf .. | .jsp .. | .jsf .. | .don .. | .bom ..
    | .lti .. => rfl
    | .clq s ⟨_ :: _, y⟩ o => rfl
    | .clq s ⟨[], y⟩ ⟨_ :: _, n⟩ => rfl
    | .clq s ⟨[], y⟩ ⟨[], n⟩ =>
      simp only [clqNA]
      by_cases hr : Opt.getJa rev y = [p]
      · simp only [hr, ne_eq, not_true_eq_false, if_false]
        cases HoonMap.get bl y with
        | none => rfl
        | some yb =>
          simp only [Option.bind_some, Option.map_some]
          obtain ⟨ypar, ybody, yfin⟩ := yb
          unfold toYb
          cases ypar with
          | cons _ _ => simp
          | nil =>
            simp only [ne_eq, not_true_eq_false, if_false]
            match yfin with
            | .clq .. | .brn .. | .brz .. | .hop .. | .jmp .. | .jmf .. | .jsp .. | .jsf .. | .don .. | .bom ..
            | .lti .. => rfl
            | .eqq l r ⟨_ :: _, hit⟩ o2 => rfl
            | .eqq l r ⟨[], hit⟩ ⟨_ :: _, n'⟩ => rfl
            | .eqq l r ⟨[], hit⟩ ⟨[], n'⟩ =>
              simp only [eqqNA]
              by_cases hn : n = n'
              · subst hn
                simp only [ne_eq, not_true_eq_false, if_false]
                match ybody with
                | [] => rfl
                | [_] => rfl
                | _ :: _ :: _ :: _ => rfl
                | [i0, i1] =>
                  simp only [toBod, toHM]
                  cases Opt.hedOf2 i0 i1 with
                  | none => rfl
                  | some hp =>
                    cases Opt.immOf2 i0 i1 with
                    | none => rfl
                    | some mp =>
                      obtain ⟨hs, hd⟩ := hp
                      obtain ⟨mn, md⟩ := mp
                      by_cases hs' : hs = s
                      · subst hs'
                        simp only [ne_eq, not_true_eq_false, if_false, toC]
                        cases Opt.smallAtom mn with
                        | none => rfl
                        | some c =>
                          simp only
                          by_cases e1 : (l, r) = (hd, md) ∨ (l, r) = (md, hd)
                          · by_cases e2 : Opt.usesOf bl hd = 2 ∧ Opt.usesOf bl md = 2
                            · rw [if_neg (not_not_intro e1), if_neg (not_not_intro e2), if_neg (not_not_intro e1),
                                if_neg (not_not_intro e2)]
                            · rw [if_neg (not_not_intro e1), if_pos e2, if_neg (not_not_intro e1), if_pos e2]
                          · rw [if_pos e1, if_pos e1]
                      · simp only [ne_eq, hs', not_false_eq_true, if_true]
              · simp only [ne_eq, hn, not_false_eq_true, if_true]
      · simp only [hr, ne_eq, not_false_eq_true, if_true]

/-- **The gate `test-of`** on the noun of a label: the noun of `testOf`, and
a crash where the model crashes. -/
theorem sw_test (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TOPO USES : Noun)
    (hU : UsesRel USES (Opt.usesOf bl)) (p : Nat) :
    nock (toG p (HoonMap.toNoun Blob.toNoun bl) TOPO (jarN rev) USES) swTOB
      = (Opt.testOf bl rev p).map (unitNoun stestN) := by
  rw [testOf_eq]
  have hg := blocks_got bl p
  have hL := optC_layer2
  cases hb : HoonMap.get bl p with
  | none =>
    rw [hb] at hg
    unfold toG swS3 swG
    generalize optC = OC at hL
    generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
    conv => lhs; arg 2; unfold swTOB
    simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
  | some b =>
    rw [hb] at hg
    obtain ⟨par, body, fin⟩ := b
    have hc := to_clq fin (listNoun A par) (listNoun Pole.toNoun body)
      (toG p (HoonMap.toNoun Blob.toNoun bl) TOPO (jarN rev) USES)
    simp only [Option.map_some, Blob.toNoun] at hg
    cases hq : clqNA fin with
    | none =>
      rw [hq] at hc
      unfold toG swS3 swG at *
      generalize optC = OC at hL hc
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hc
      conv => lhs; arg 2; unfold swTOB
      simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, hc, loob, unitNoun, hq]
    | some q =>
      obtain ⟨s, y, n⟩ := q
      have ht := clqNA_some hq
      subst ht
      rw [hq] at hc
      have hy := to_y bl rev TOPO USES hU p s y n (listNoun A par) (listNoun Pole.toNoun body)
      unfold toG swS3 swG at *
      generalize optC = OC at hL hc hy
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hc hy
      by_cases hr : Opt.getJa rev y = [p]
      · simp only [hr, ne_eq, not_true_eq_false, if_false] at hy ⊢
        conv => lhs; arg 2; unfold swTOB
        simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, hc, loob, hy, Option.map_map, clqNA, hr]
        rfl
      · simp only [hr, ne_eq, not_false_eq_true, if_true] at hy ⊢
        conv => lhs; arg 2; unfold swTOB
        simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, hc, loob, hy, unitNoun, clqNA, hr]

end Compiler
end Formalization
