import lemmas.Compiler.CompCoerceLazy

/-!
# `+bake-need` when nothing is baked

`+bake-need` (arm `384468` of `K`, `%bake-need`, its gate body `bnBody`)
walks the need with the sock `k` that the bell knows of the part it is the
need of (`hed:so`, `tel:so` down the walk).  At each node it bakes the whole
part (`[%none ~]` and the leaves with their known values, the trap `bnAll`)
when `k` is a cell whose cape is wholly known (`all:ca`) and whose data has
the structure the need asks (`+need-fits`, arm `4` of `K`).  Otherwise
`%none` and `%this` are kept, a cell is rebuilt by `+cons-need`, and a
`%both` keeps its register: `[%both r x]` when `x = (cons-need h t)` is a
cell of needs, `[%this r]` when both halves were baked away.

`bn_gate`: on a need with no `[[%none ~] [%none ~]]` cell and no `%both`
with two `%none` halves (`NeedNorm`, which every need of
`+need-ord-alloc-regs` has, `needNorm_noar`), and a sock that is `%void` or
not wholly known at every node of the need (`NoBake`), the gate returns
`[ned ~]`: nothing is baked.  `NoBake` is a sufficient condition: it keeps
the test of each node from reaching `+need-fits`, which is not linked.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The side conditions -/

/-- The test of a node of `+bake-need` is false before `+need-fits`: the
sock is `%void`, or its cape is not wholly known. -/
def bnQuiet : Sock → Prop
  | Sock.void => True
  | Sock.mk c _ => Ca.all c = false

/-- **Nothing is baked**: at every node of the need, the sock that
`+bake-need` holds there (`hed:so` and `tel:so` down the walk) is quiet. -/
def NoBake : Need → Sock → Prop
  | Need.pair p q, k => bnQuiet k ∧ NoBake p (So.hed k) ∧ NoBake q (So.tel k)
  | Need.both _ h t, k => bnQuiet k ∧ NoBake h (So.hed k) ∧ NoBake t (So.tel k)
  | Need.none, k => bnQuiet k
  | Need.this _, k => bnQuiet k

/-- No cell of two `%none` and no `%both` with two `%none` halves. -/
def NeedNorm : Need → Prop
  | Need.pair p q => ¬ (p = Need.none ∧ q = Need.none) ∧ NeedNorm p ∧ NeedNorm q
  | Need.both _ h t => ¬ (h = Need.none ∧ t = Need.none) ∧ NeedNorm h ∧ NeedNorm t
  | Need.none => True
  | Need.this _ => True

/-- The needs of `+need-ord-alloc-regs` are normal. -/
theorem needNorm_noar : ∀ (ord : NeedOrd) (g g' : Gen (TreapMap mugF)) (n : Need),
    needOrdAllocRegs ord g = some (n, g') → NeedNorm n
  | NeedOrd.none, g, g', n, h => by
    simp [needOrdAllocRegs, pure, StateT.pure] at h; rw [← h.1]; trivial
  | NeedOrd.this, g, g', n, h => by
    simp [needOrdAllocRegs, re, bind, StateT.bind, pure, StateT.pure] at h; rw [← h.1]; trivial
  | NeedOrd.pair p q, g, g', n, h => by
    simp only [needOrdAllocRegs, bind, StateT.bind] at h
    cases e1 : needOrdAllocRegs p g with
    | none => rw [e1] at h; cases h
    | some r1 =>
      obtain ⟨a, g1⟩ := r1
      rw [e1] at h
      simp only [Option.bind_some] at h
      cases e2 : needOrdAllocRegs q g1 with
      | none => rw [e2] at h; cases h
      | some r2 =>
        obtain ⟨b, g2⟩ := r2
        rw [e2] at h
        simp only [Option.bind_some] at h
        by_cases c : a = Need.none ∧ b = Need.none
        · simp [c, crashM] at h
        · simp [c, pure, StateT.pure] at h
          rw [← h.1]
          exact ⟨c, needNorm_noar p g g1 a e1, needNorm_noar q g1 g2 b e2⟩
  | NeedOrd.both p q, g, g', n, h => by
    simp only [needOrdAllocRegs, bind, StateT.bind, re] at h
    simp only [Option.bind_some] at h
    cases e1 : needOrdAllocRegs p { g with re := g.re + 1 } with
    | none => rw [e1] at h; cases h
    | some r1 =>
      obtain ⟨a, g1⟩ := r1
      rw [e1] at h
      simp only [Option.bind_some] at h
      cases e2 : needOrdAllocRegs q g1 with
      | none => rw [e2] at h; cases h
      | some r2 =>
        obtain ⟨b, g2⟩ := r2
        rw [e2] at h
        simp only [Option.bind_some] at h
        by_cases c : a = Need.none ∧ b = Need.none
        · simp [c, crashM] at h
        · simp [c, pure, StateT.pure] at h
          rw [← h.1]
          exact ⟨c, needNorm_noar p _ g1 a e1, needNorm_noar q g1 g2 b e2⟩

theorem consNeed_norm {a b : Need} (h : ¬ (a = Need.none ∧ b = Need.none)) : consNeed a b = Need.pair a b := by
  unfold consNeed; simp [h]

/-! ## The nouns -/

def bnAll : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 1016)))) (C (C (A 0) (A 62)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 1016)))) (C (C (C (C (A 0) (A 1017)) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 1500) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 3))))) (C (A 0) (A 62))) (C (A 6) (C (C (A 3) (C (A 0) (A 1016))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 508) (C (A 0) (A 1017))) (C (A 10) (C (C (A 62) (C (A 9) (C (A 2) (C (A 10) (C (C (A 508) (C (A 0) (A 1016))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 8191)))) (C (A 9) (C (A 175) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 8191)))) (C (A 9) (C (A 23) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 1016))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (C (C (A 0) (A 2034)) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 1500) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 3))))) (C (A 0) (A 62)))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 508) (C (A 0) (A 4071))) (C (A 10) (C (C (A 62) (C (A 9) (C (A 2) (C (A 10) (C (C (A 508) (C (A 0) (A 4070))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 8191)))) (C (A 9) (C (A 175) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 8191)))) (C (A 9) (C (A 23) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))))))))))))))))))

def bnTest : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 6) (C (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 2047)))) (C (A 9) (C (A 22) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def bnYes : Noun :=
  (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 8) (C (C (A 0) (A 6)) (C (A 8) (C (C (A 1) bnAll) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))

def bnRec : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 248)))) (C (C (C (A 0) (A 124)) (C (A 0) (A 14))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 248)))) (C (C (C (A 0) (A 124)) (C (A 0) (A 14))) (C (A 6) (C (C (A 3) (C (A 0) (A 248))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 124) (C (A 0) (A 248))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 2047)))) (C (A 9) (C (A 175) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 124) (C (A 0) (A 505))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 4095)))) (C (A 9) (C (A 23) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2))))))))) (C (A 0) (A 3)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (A 0) (A 62))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 248))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 124) (C (A 0) (A 998))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 2047)))) (C (A 9) (C (A 175) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 124) (C (A 0) (A 2023))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 4095)))) (C (A 9) (C (A 23) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2))))))))) (C (A 0) (A 3)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 4082))) (C (A 0) (A 126))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 4082)) (C (A 0) (A 2)))) (C (A 0) (A 126)))))))))))))))))))))))))))))))))))

def bnLoop : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C bnTest (C bnYes bnRec)))))

def bnBody : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 0) (A 29)) (C (A 8) (C (C (A 1) bnLoop) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))

theorem bn_at : slot? 384468 compK = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0))))
    (C (C (A 1) bnBody) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465656e2d656b6162)
    (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1)))))) := by kernel_rfl

/-- The library core `lib` in `K`. -/
theorem compK_lib : slot? 63 compK = some lib := by
  have h := ana_lib7
  simp [compK, compTypes, nock_exec, h]

/-! ## The loop -/

/-- The test of a node is false on a quiet sock. -/
theorem bn_test (IMM NED KNOW : Noun) (k : Sock) (hq : bnQuiet k) (Y R : Noun) :
    nock (C bnLoop (C k.toNoun (C IMM (C bnBody (C (C NED KNOW) compK))))) (C (A 6) (C bnTest (C Y R)))
      = nock (C bnLoop (C k.toNoun (C IMM (C bnBody (C (C NED KNOW) compK))))) R := by
  have hl := compK_lib
  unfold bnTest
  generalize bnLoop = LP
  generalize bnBody = BD
  cases k with
  | void => simp [nock_exec, Sock.toNoun]
  | mk c d =>
    simp only [bnQuiet] at hq
    have ha := ca_all_gate (C ca.battery lib) c
    rw [hq] at ha
    generalize compK = KC at hl
    simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob]

theorem bn_unfold (S : Noun) : nock S bnLoop = nock S (C (A 6) (C bnTest (C bnYes bnRec))) := by
  unfold bnLoop
  generalize C (A 6) (C bnTest (C bnYes bnRec)) = F
  simp [nock_exec]

/-- **The loop of `+bake-need`** on a normal need under a sock that bakes
nothing: the need itself, the list `imm` unchanged. -/
theorem bn_loop (KNOW : Noun) : ∀ (ned : Need) (k : Sock) (IMM : Noun), NeedNorm ned → NoBake ned k →
    nock (C bnLoop (C k.toNoun (C IMM (C bnBody (C (C ned.toNoun KNOW) compK))))) bnLoop
      = some (C ned.toNoun IMM)
  | Need.none, k, IMM, hn, hb => by
    rw [bn_unfold, bn_test IMM _ KNOW k hb]
    unfold bnRec
    generalize bnLoop = LP
    generalize bnBody = BD
    simp [nock_exec, Need.toNoun, Tag.none]
  | Need.this r, k, IMM, hn, hb => by
    rw [bn_unfold, bn_test IMM _ KNOW k hb]
    unfold bnRec
    generalize bnLoop = LP
    generalize bnBody = BD
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this]
  | Need.pair p q, k, IMM, hn, hb => by
    obtain ⟨hpq, hnp, hnq⟩ := hn
    obtain ⟨hq0, hbp, hbq⟩ := hb
    have ihp := bn_loop KNOW p (So.hed k) IMM hnp hbp
    have ihq := bn_loop KNOW q (So.tel k) IMM hnq hbq
    have hcn := cn_gate compK p q
    rw [consNeed_norm hpq] at hcn
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    rw [hp] at ihp
    simp only [Need.toNoun] at hcn
    rw [hp] at hcn
    have hhed := so_hed_gate (C so.battery lib) k
    have htel := so_tel_gate (C so.battery lib) k
    have hl := compK_lib
    have hcna := compK_cn
    rw [bn_unfold, bn_test IMM _ KNOW k hq0]
    unfold bnRec
    unfold cnArm at hcna
    generalize bnLoop = LP at ihp ihq ⊢
    generalize bnBody = BD at ihp ihq ⊢
    generalize compK = KC at ihp ihq hcn hl hcna ⊢
    simp [nock_exec, Need.toNoun, hp, eqCode, hl, so.lib.arm_at, so_lib_arm, so.hed.arm_at, so_hed_arm, hhed,
      so.tel.arm_at, so_tel_arm, htel, ihp, ihq, hcna, hcn]
  | Need.both r h t, k, IMM, hn, hb => by
    obtain ⟨hht, hnh, hnt⟩ := hn
    obtain ⟨hq0, hbh, hbt⟩ := hb
    have ihh := bn_loop KNOW h (So.hed k) IMM hnh hbh
    have iht := bn_loop KNOW t (So.tel k) IMM hnt hbt
    have hcn := cn_gate compK h t
    rw [consNeed_norm hht] at hcn
    obtain ⟨a, b, hh⟩ := cd_need_cell h
    simp only [Need.toNoun] at hcn
    rw [hh] at ihh hcn
    have hhed := so_hed_gate (C so.battery lib) k
    have htel := so_tel_gate (C so.battery lib) k
    have hl := compK_lib
    have hcna := compK_cn
    rw [bn_unfold, bn_test IMM _ KNOW k hq0]
    unfold bnRec
    unfold cnArm at hcna
    generalize bnLoop = LP at ihh iht ⊢
    generalize bnBody = BD at ihh iht ⊢
    generalize compK = KC at ihh iht hcn hl hcna ⊢
    simp [nock_exec, Need.toNoun, hh, Tag.none, Tag.this, Tag.both, hl, so.lib.arm_at, so_lib_arm, so.hed.arm_at,
      so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihh, iht, hcna, hcn]

/-- **The gate of `+bake-need`** on a normal need and a sock that bakes
nothing: `[ned ~]`. -/
theorem bn_gate (ned : Need) (know : Sock) (hn : NeedNorm ned) (hb : NoBake ned know) :
    nock (C bnBody (C (C ned.toNoun know.toNoun) compK)) bnBody = some (C ned.toNoun (A 0)) := by
  have hl := bn_loop know.toNoun ned know (A 0) hn hb
  conv => { lhs; arg 2; unfold bnBody }
  generalize bnLoop = LP at hl
  generalize bnBody = BD at hl ⊢
  simp [nock_exec, hl]

/-- The arm builds its gate on `K`. -/
theorem bn_arm (d : Noun) : nock d (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0))))
    (C (C (A 1) bnBody) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465656e2d656b6162)
    (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))))
      = some (C bnBody (C (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0))) d)) := by
  generalize bnBody = B; simp [nock_exec]
