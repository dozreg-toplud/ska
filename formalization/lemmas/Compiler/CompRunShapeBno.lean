import lemmas.Compiler.CompRunShapeBnoCut
import lemmas.Compiler.CompBakeGate
import lemmas.Compiler.CompSccLoopMemShape

/-!
# `+bake-need-ord` against the model (track A, 2026-11-27)

`+bake-need-ord` (arm `1398` of `K`, `bno_at`, cut in `CompRunShapeBnoCut.lean`) on every
shape and sock is `bakeNeedOrd` (`Ska/BakeNeed.lean`), with no side condition.

* `nf_gate_ord`: `+need-fits` (arm `4` of `K`, `nf_at`) on the noun of a shape is the
  loobean of `ordFits` (a `%both` of a shape carries no register, so `halves` is `+.ned`).
* `bno_testG`: the test of a node (`?=(^ k)`, `all:ca`, `+need-fits`).
* **`bno_loop`**: the trap on every shape and sock: `bakeNeedOrd`.
* **`bno_gate`**: the gate on `[ned know]`: `(bakeNeedOrd ned know).toNoun`.
* `bno_arm`: the arm builds its gate on any core.
* **`bno_call`**: the call `msBno` of the sweeps' branch of `member`
  (`CompSccLoopMemShape.lean`), `(bake-need-ord collapsed less.b)`, on a subject with `K` at
  axis `0x3fff`, the shape at axis `2` and the sock at axis `2040`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `consOrdB` of the bake model is `consOrd` of `+sure-of`. -/
theorem consOrdB_eq (a b : NeedOrd) : consOrdB a b = consOrd a b := rfl

/-- **`+need-fits` on a shape**: the loobean of `ordFits`. -/
theorem nf_gate_ord : ∀ (ned : NeedOrd) (som : Noun),
    nock (C nfBody (C (C ned.toNoun som) compK)) nfBody = some (loob (ordFits ned som))
  | NeedOrd.none, som => by
    conv => { lhs; arg 2; unfold nfBody }
    generalize nfBody = B
    cases som <;> simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.both, Tag.this, ordFits, loob]
  | NeedOrd.this, som => by
    conv => { lhs; arg 2; unfold nfBody }
    generalize nfBody = B
    cases som <;> simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.both, Tag.this, ordFits, loob]
  | NeedOrd.pair p q, som => by
    obtain ⟨a, b, hp⟩ := nord_cell p
    cases som with
    | atom n =>
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B
      simp [nock_exec, NeedOrd.toNoun, hp, Tag.none, Tag.both, Tag.this, ordFits, loob]
    | cell x y =>
      have ihp := nf_gate_ord p x
      have ihq := nf_gate_ord q y
      rw [hp] at ihp
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B at ihp ihq ⊢
      cases e1 : ordFits p x <;> cases e2 : ordFits q y <;>
        simp [nock_exec, NeedOrd.toNoun, hp, Tag.none, Tag.both, Tag.this, ordFits, loob, ihp, ihq, e1, e2]
  | NeedOrd.both h t, som => by
    obtain ⟨a, b, hh⟩ := nord_cell h
    cases som with
    | atom n =>
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B
      simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.both, Tag.this, ordFits, loob]
    | cell x y =>
      have ihh := nf_gate_ord h x
      have iht := nf_gate_ord t y
      rw [hh] at ihh
      conv => { lhs; arg 2; unfold nfBody }
      generalize nfBody = B at ihh iht ⊢
      cases e1 : ordFits h x <;> cases e2 : ordFits t y <;>
        simp [nock_exec, NeedOrd.toNoun, hh, Tag.none, Tag.both, Tag.this, ordFits, loob, ihh, iht, e1, e2]

/-- The subject of the trap: `[bnoLoop [k [bnoBody [[ned KNOW] K]]]]`. -/
def bnoS (k NED KNOW : Noun) : Noun := C bnoLoop (C k (C bnoBody (C (C NED KNOW) compK)))

/-- **The test of a node of `+bake-need-ord`**. -/
theorem bno_testG (KNOW : Noun) (ned : NeedOrd) (k : Sock) (Y R : Noun) :
    nock (bnoS k.toNoun ned.toNoun KNOW) (C (A 6) (C bnoTest (C Y R)))
      = if bakeTest (ordFits ned) k then nock (bnoS k.toNoun ned.toNoun KNOW) Y
        else nock (bnoS k.toNoun ned.toNoun KNOW) R := by
  have hl := compK_lib
  have hnfat := nf_at
  unfold bnoTest bnoS
  generalize bnoLoop = LP
  generalize bnoBody = BD
  cases k with
  | void => simp [nock_exec, Sock.toNoun, bakeTest]
  | mk c d =>
    have ha := ca_all_gate (C ca.battery lib) c
    have hnf := nf_gate_ord ned d
    generalize nfBody = NB at hnf hnfat
    generalize compK = KC at hl hnf hnfat
    cases hc : Ca.all c with
    | false =>
      rw [hc] at ha
      simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob, bakeTest, hc]
    | true =>
      rw [hc] at ha
      cases hf : ordFits ned d with
      | false =>
        rw [hf] at hnf
        simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob, bakeTest,
          hc, hf, hnfat, hnf]
      | true =>
        rw [hf] at hnf
        simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob, bakeTest,
          hc, hf, hnfat, hnf]

theorem bno_unfold (S : Noun) :
    nock S bnoLoop = nock S (C (A 6) (C bnoTest (C (C (A 1) (C (A 0x656e6f6e) (A 0))) bnoRec))) := by
  rw [bnoLoop]

/-- **The trap of `+bake-need-ord`** on every shape and sock: `bakeNeedOrd`. -/
theorem bno_loop (KNOW : Noun) : ∀ (ned : NeedOrd) (k : Sock),
    nock (bnoS k.toNoun ned.toNoun KNOW) bnoLoop = some (bakeNeedOrd ned k).toNoun
  | NeedOrd.none, k => by
    rw [bno_unfold, bno_testG]
    split
    · simp [nock_exec, bakeNeedOrd, NeedOrd.toNoun, Tag.none]
    · unfold bnoRec bnoS
      generalize bnoPair = P
      generalize bnoBoth = BO
      generalize bnoLoop = LP
      generalize bnoBody = BD
      simp [nock_exec, NeedOrd.toNoun, Tag.none, bakeNeedOrd]
  | NeedOrd.this, k => by
    rw [bno_unfold, bno_testG]
    split
    · next ht => simp [nock_exec, bakeNeedOrd, NeedOrd.toNoun, Tag.none, ht]
    · next ht =>
      unfold bnoRec bnoS
      generalize bnoPair = P
      generalize bnoBoth = BO
      generalize bnoLoop = LP
      generalize bnoBody = BD
      simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, bakeNeedOrd, ht]
  | NeedOrd.pair p q, k => by
    rw [bno_unfold, bno_testG]
    split
    · next ht => simp [nock_exec, bakeNeedOrd, NeedOrd.toNoun, Tag.none, ht]
    · next ht =>
      have ihp := bno_loop KNOW p (So.hed k)
      have ihq := bno_loop KNOW q (So.tel k)
      have hcn := cn_gate_ord compK (bakeNeedOrd p (So.hed k)) (bakeNeedOrd q (So.tel k))
      obtain ⟨a, b, hp⟩ := nord_cell p
      have hhed := so_hed_gate (C so.battery lib) k
      have htel := so_tel_gate (C so.battery lib) k
      have hl := compK_lib
      have hcna := compK_cn
      unfold bnoS at ihp ihq
      rw [hp] at ihp
      unfold bnoRec bnoPair bnoHed bnoTel bnoS
      unfold cnArm at hcna
      generalize bnoBoth = BO
      generalize bnoLoop = LP at ihp ihq ⊢
      generalize bnoBody = BD at ihp ihq ⊢
      generalize compK = KC at ihp ihq hcn hl hcna ⊢
      simp [nock_exec, NeedOrd.toNoun, hp, eqCode, hl, so.lib.arm_at, so_lib_arm, so.hed.arm_at, so_hed_arm, hhed,
        so.tel.arm_at, so_tel_arm, htel, ihp, ihq, hcna, hcn, bakeNeedOrd, ht, consOrdB_eq]
  | NeedOrd.both h t, k => by
    rw [bno_unfold, bno_testG]
    split
    · next ht => simp [nock_exec, bakeNeedOrd, NeedOrd.toNoun, Tag.none, ht]
    · next ht =>
      have ihh := bno_loop KNOW h (So.hed k)
      have iht := bno_loop KNOW t (So.tel k)
      have hcn := cn_gate_ord compK (bakeNeedOrd h (So.hed k)) (bakeNeedOrd t (So.tel k))
      obtain ⟨a, b, hh⟩ := nord_cell h
      have hhed := so_hed_gate (C so.battery lib) k
      have htel := so_tel_gate (C so.battery lib) k
      have hl := compK_lib
      have hcna := compK_cn
      unfold bnoS at ihh iht
      rw [hh] at ihh
      unfold bnoRec bnoBoth bnoHed bnoTel bnoS
      unfold cnArm at hcna
      simp only [bakeNeedOrd, ht, if_false, Bool.false_eq_true, consOrdB_eq]
      generalize ex : consOrd (bakeNeedOrd h (So.hed k)) (bakeNeedOrd t (So.tel k)) = x at hcn
      generalize bnoPair = P
      generalize bnoLoop = LP at ihh iht ⊢
      generalize bnoBody = BD at ihh iht ⊢
      generalize compK = KC at ihh iht hcn hl hcna ⊢
      cases x with
      | pair x1 x2 =>
        obtain ⟨a1, b1, hx⟩ := nord_cell x1
        simp only [NeedOrd.toNoun] at hcn
        rw [hx] at hcn
        simp [nock_exec, NeedOrd.toNoun, hh, hx, Tag.none, Tag.this, Tag.both, hl, so.lib.arm_at, so_lib_arm,
          so.hed.arm_at, so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihh, iht, hcna, hcn, nock_op11_cell]
      | none =>
        simp [nock_exec, NeedOrd.toNoun, hh, Tag.none, Tag.this, Tag.both, hl, so.lib.arm_at, so_lib_arm,
          so.hed.arm_at, so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihh, iht, hcna, hcn, nock_op11_cell]
      | this => simp [consOrd] at ex; split at ex <;> cases ex
      | both _ _ => simp [consOrd] at ex; split at ex <;> cases ex

/-- **The gate of `+bake-need-ord`** on every shape and sock: `bakeNeedOrd`. -/
theorem bno_gate (ned : NeedOrd) (know : Sock) :
    nock (C bnoBody (C (C ned.toNoun know.toNoun) compK)) bnoBody = some (bakeNeedOrd ned know).toNoun := by
  have hl := bno_loop know.toNoun ned know
  unfold bnoS at hl
  conv => { lhs; arg 2; unfold bnoBody }
  generalize bnoLoop = LP at hl
  generalize bnoBody = BD at hl ⊢
  simp [nock_exec, hl]

/-- The arm builds its gate on any core. -/
theorem bno_arm (d : Noun) : nock d bnoArm = some (C bnoBody (C bnoBunt d)) := by
  unfold bnoArm bnoHint; generalize bnoBody = B; generalize bnoBunt = U; simp [nock_exec]

/-- **The call `(bake-need-ord collapsed less.b)` of the sweeps' branch** (`msBno`): on a
subject with `K` at axis `0x3fff`, the shape `ned` at axis `2` and the sock `know` at axis
`2040` (`less.b`), the product is `bakeNeedOrd ned know`. -/
theorem bno_call (S : Noun) (ned : NeedOrd) (know : Sock) (hk : slot? 0x3fff S = some compK)
    (hn : slot? 2 S = some ned.toNoun) (hl : slot? 2040 S = some know.toNoun) :
    nock S msBno = some (bakeNeedOrd ned know).toNoun := by
  have hg := bno_gate ned know
  have ha := bno_at
  have hb := bno_arm compK
  have e6 : ∀ x, slot? 6 (C x S) = slot? 2 S := fun x => rfl
  have e4088 : ∀ x, slot? 4088 (C x S) = slot? 2040 S := fun x => rfl
  unfold msBno
  simp [nock_exec, hk, ha, hb, e6, e4088, hn, hl, hg]

end Compiler
end Formalization
