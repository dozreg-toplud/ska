import lemmas.Compiler.CompSplit

/-!
# `+gep`, `+cons-need`, `+into-need`, `+into-sure`, `+into` of the door of `+comp`

`+into-sure` calls `+gep` and `+into-need` calls `+cons-need` (in its `roll`),
two arms of the core `K` in which `+comp` is defined (the `|%` at line 3222
of `nock-compilation.hoon`), at axis `7` of the door's context `ctx`
(`CompLib`: `+gep` at `5597`, `+cons-need` at `350` of `K`).  The generator
names none of these nouns: `gepBat`, `cnBat` and the batteries of the door's
arms (`innBat` with its loop `innL0` and the gate of its `roll` `innG0`,
`isBat` with the gate of its `+rep:in` `isG0`) are written here, each tied to
the pill by a kernel fact (`gep_arm_at`, `cn_arm_at` in `cor`, whose axis `63`
holds `K`; `comp_inn_at`, `comp_is_at` in `comp.door`).

None of these arms reads or writes `cache`, `soft` or `sofs`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

/-- The battery of the gate `+gep`, an arm of the core of `+comp`'s
gate (the core `K` at axis `7` of the door's context). -/
def gepBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 0) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 13)))) (C (C (A 1) (C (A 0) (A 1))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 79) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 10710) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 10710) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 21438) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 61)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 60)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 2676) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 1518) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2398) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 756) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 14)))) (C (A 0) (A 2))))))))))))) (C (A 1) (A 0)))))))))))))))))))))

/-- The arm `+gep`: the gate with the sample `[0 0]`. -/
def gepArm : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) gepBat) (C (A 0) (A 1))))

/-- `+gep` is arm `5597` of the core at axis `63` of `cor`. -/
theorem gep_arm_at : slot? 259549 cor = some gepArm := by kernel_rfl

/-- The battery of the wet gate `+cons-need` (arm `350` of the same core). -/
def cnBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 0) (A 12)) (C (A 0) (A 13))))))

def cnArm : Noun := C (A 8) (C (C (A 1) (C (C (A 0) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) cnBat) (C (A 0) (A 1))))

theorem cn_arm_at : slot? 16222 cor = some cnArm := by kernel_rfl

/-- What the arms of this file read of the core `K` at axis `7` of the door's
context: `+gep` at `5597` and `+cons-need` at `350`. -/
def CompLib (ctx : Noun) : Prop :=
  ∃ K, slot? 7 ctx = some K ∧ slot? 5597 K = some gepArm ∧ slot? 350 K = some cnArm

theorem ci_eqCode_need (n : Nat) (p : Need) : eqCode (A n) p.toNoun = A 1 := by
  obtain ⟨u, v, h⟩ := cd_need_cell p
  rw [h]; simp [eqCode]

theorem cn_gate (K : Noun) (a b : Need) :
    nock (C cnBat (C (C a.toNoun b.toNoun) K)) cnBat = some (consNeed a b).toNoun := by
  unfold cnBat
  cases a <;> cases b <;> simp [nock_exec, Need.toNoun, consNeed, eqCode_atom, eqCode_self, Tag.none,
    Tag.both, Tag.this, ci_eqCode_need]

/-- `+roll` with a gate known on the nouns of a type. -/
theorem ci_roll_loop {α σ : Type} (toE : α → Noun) (toS : σ → Noun) (c bp e bc : Noun)
    (f : α → σ → σ) : ∀ (l : List α) (acc : σ),
    (∀ x ∈ l, ∀ acc, nock (C bp (C (C (toE x) (toS acc)) bc)) bp = some (toS (f x acc))) →
    nock (C roll.loop (C roll.battery (C (C (listNoun toE l) (C bp (C (C e (toS acc)) bc))) c)))
      roll.loop = some (toS (l.foldl (fun acc x => f x acc) acc)) := by
  intro l
  induction l with
  | nil =>
    intro acc _
    nock_open roll.loop
    simp [nock_exec, listNoun]
  | cons x xs ih =>
    intro acc hf
    have hx := hf x (by simp)
    have hxs := ih (f x acc) (fun y hy => hf y (by simp [hy]))
    nock_open roll.loop
    simp [nock_exec, listNoun, hx, hxs]

theorem ci_roll_gate {α σ : Type} (toE : α → Noun) (toS : σ → Noun) (c bp e bc : Noun)
    (f : α → σ → σ) (l : List α) (acc : σ)
    (hf : ∀ x ∈ l, ∀ acc, nock (C bp (C (C (toE x) (toS acc)) bc)) bp = some (toS (f x acc))) :
    nock (C roll.battery (C (C (listNoun toE l) (C bp (C (C e (toS acc)) bc))) c)) roll.battery
      = some (toS (l.foldl (fun acc x => f x acc) acc)) := by
  nock_open roll.battery
  simp only [nock_exec, ci_roll_loop toE toS c bp e bc f l acc hf]

theorem ci_metF_mono : ∀ (b a : Nat), a ≤ b → metF 0 a ≤ metF 0 b := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a hab
    by_cases ha : a = 0
    · subst ha; rw [metF_zero]; omega
    · have hb : 0 < b := by omega
      rw [metF_pos 0 a (by omega), metF_pos 0 b hb]
      have := ih (b / 2 ^ 2 ^ 0) (by simp; omega) (a / 2 ^ 2 ^ 0) (by simp; omega)
      omega

theorem ci_layer2_K {ctx K : Noun} (hc : CompIn ctx) (hK : slot? 7 ctx = some K) :
    slot? 65535 K = some layer2 := by
  match ctx, hK with
  | Noun.cell _ (Noun.cell _ K'), hK =>
    simp only [nock_exec, Option.some.injEq] at hK
    subst hK
    simpa only [CompIn, nock_exec] using hc
  | Noun.atom _, hK => simp [nock_exec] at hK
  | Noun.cell _ (Noun.atom _), hK => simp [nock_exec] at hK

/-- The gate `+gep`, on two atoms, in a core with layer 2 at `65535`. -/
theorem gep_gate (K : Noun) (hK : slot? 65535 K = some layer2) (a b : Nat) :
    nock (C gepBat (C (C (A a) (A b)) K)) gepBat = (gep a b).map (unitNoun A) := by
  obtain ⟨ha, hs, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := arith_layer1
  have hbex : BexIn layer2 := ⟨bex.arm_at, hm⟩
  have hrsh : RshIn layer2 := ⟨rsh.arm_at, hbex, hdv⟩
  have hlsh : LshIn layer2 := ⟨lsh.arm_at, hbex⟩
  have hend : EndIn layer2 := ⟨end.arm_at, hbex, hmd⟩
  have hlog : LogicNeeds layer2 := ⟨hrsh, hlsh, hend, ha⟩
  have hl1 : slot? 131071 K = some layer1 := by
    have h := slot_bit 65535 (by decide) 1 (by decide) K
    rw [hK] at h
    rw [show (131071 : Nat) = 2 * 65535 + 1 from rfl, h]
    exact (slot_three layer2).symm.trans layer2_layer1
  unfold gepBat
  by_cases a0 : a = 0
  · subst a0; simp [nock_exec, eqCode_atom, eqCode_self, gep]
  have a0' : ¬ (0 = a) := fun h => a0 h.symm
  by_cases b0 : b = 0
  · subst b0; simp [nock_exec, eqCode_atom, eqCode_self, gep, a0, a0']
  have b0' : ¬ (0 = b) := fun h => b0 h.symm
  by_cases e : a = b
  · subst e; simp [nock_exec, eqCode_atom, eqCode_self, gep, a0, a0', unitNoun]
  by_cases lt : b < a
  · simp [nock_exec, eqCode_atom, eqCode_self, gep, a0, a0', b0, b0', e, lt, hl1, lth_arm, lth.arm_at, lth_gate _ decIn_layer1, unitNoun]
  have hm := ci_metF_mono b a (by omega)
  have hsub := sub_gate layer1 decIn_layer1 (metF 0 a) (metF 0 b) hm
  have hmb := met_gate layer2 hrsh 0 b
  have hma := met_gate layer2 hrsh 0 a
  have hlt := lth_gate layer1 decIn_layer1 b a
  generalize hd : metF 0 b - metF 0 a = d at hsub
  have hrs := rsh_gate layer2 hrsh (C (A 0) (A d)) 0 d b (BiteIs.cell 0 d)
  simp only [Nat.pow_zero, Nat.one_mul] at hrs
  have hbx := bex_gate layer2 hbex.2 d
  have hdc := dec_gate layer1 (2 ^ d) (Nat.two_pow_pos d)
  have hds := dis_gate layer2 hlog b (2 ^ d - 1)
  have hcn := con_gate layer2 hlog (b % 2 ^ d) (2 ^ d)
  by_cases et : b / 2 ^ d = a
  · simp [nock_exec, eqCode_atom, eqCode_self, gep, a0, a0', b0, b0', e, lt, hl1, hK, lth_arm,
      lth.arm_at, hlt, sub_arm, sub.arm_at, hsub, met_arm, met.arm_at, hmb, hma, hd, rsh_arm,
      rsh.arm_at, hrs, et, bex_arm, bex.arm_at, hbx, dec_arm, dec.arm_at, hdc, dis_arm, dis.arm_at,
      hds, con_arm, con.arm_at, hcn, unitNoun, loob]
  · have et' : ¬ (b / 2 ^ d = a) := et
    simp [nock_exec, eqCode_atom, eqCode_self, gep, a0, a0', b0, b0', e, lt, hl1, hK, lth_arm,
      lth.arm_at, hlt, sub_arm, sub.arm_at, hsub, met_arm, met.arm_at, hmb, hma, hd, rsh_arm,
      rsh.arm_at, hrs, et, bex_arm, bex.arm_at, hbx, dec_arm, dec.arm_at, hdc, dis_arm, dis.arm_at,
      hds, con_arm, con.arm_at, hcn, unitNoun, loob]


/-! ## `+into-need` -/

def innG0 : Noun :=
  (C (A 6) (C (C (A 0) (A 24)) (C (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 57)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))))))

def innL0 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 124)))) (C (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 9) (C (A 10990) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 507)) (C (A 0) (A 14)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (A 0x656e6f6e) (A 0))) (C (A 0x656e6f6e) (A 0)))) (C (C (A 1) innG0) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 506)) (C (A 0) (A 2))) (C (A 0) (A 510))))))) (C (A 8) (C (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))) (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))))) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 1012)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 124) (C (A 0) (A 5))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 4)) (C (A 0) (A 506))) (C (A 0) (A 30)))) (C (A 0) (A 3)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 1012)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 255)))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (C (A 1) (A 0x6e6f63)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 4085))))) (C (A 8) (C (C (A 8) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (C (A 0) (A 14)) (C (A 0) (A 6))) (C (C (A 0) (A 6)) (C (A 0) (A 14)))))) (C (C (A 0) (A 4)) (C (A 0) (A 5))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 250) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 4)))) (C (A 10) (C (C (A 124) (C (A 0) (A 125))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 124)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 5)))) (C (A 0) (A 510)))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 254)))) (C (A 0) (A 63)))))))))))))))))))))))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 1012))) (C (C (A 8) (C (C (A 8) (C (C (A 6) (C (C (A 0) (A 4)) (C (C (A 0) (A 506)) (C (C (A 0) (A 1013)) (C (A 0) (A 1012)))))) (C (C (A 0) (A 4)) (C (A 0) (A 5))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 250) (C (A 0) (A 4))) (C (A 10) (C (C (A 124) (C (A 0) (A 13))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 12)) (C (A 0) (A 5))) (C (A 0) (A 62)))) (C (A 0) (A 7)))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 1012))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x1555e) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8150))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x1555e) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 16343))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (C (A 1) (A 0x6e6f63)) (C (C (A 0) (A 12)) (C (C (A 0) (A 4)) (C (A 0) (A 8170))))) (C (A 8) (C (C (A 8) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (C (A 0) (A 29)) (C (A 0) (A 13))) (C (C (A 0) (A 13)) (C (A 0) (A 29)))))) (C (C (A 0) (A 4)) (C (A 0) (A 5))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 250) (C (A 0) (A 4))) (C (A 10) (C (C (A 124) (C (A 0) (A 125))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 124)) (C (A 0) (A 5))) (C (A 0) (A 510)))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 254)))) (C (A 0) (A 63))))))))))))))))))))))))))))))))))))))))))))))))

def innBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (C (C (C (A 0) (A 26)) (C (A 1) (C (A 0x656e6f6e) (A 0)))) (C (A 0) (A 30))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) innL0) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))

def innArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (A 0)))) (C (C (A 1) innBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465656e2d6f746e692d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

-- door axis 214, core axis 342
theorem comp_inn_at : slot? 214 comp.door = some innArm := by kernel_rfl

-- innL0 at 16381 of innBat
-- innG0 at 34355265277 of innBat

/-- An entry `[h n]` of the `tack` of `+into-need`. -/
def ciTackE (e : Bool × Need) : Noun := C (loob e.1) e.2.toNoun

/-- The gate of the `roll` at the end of `+into-need`. -/
theorem inn_roll_gate (L K : Noun) (hL : slot? 1023 L = some K) (hcn : slot? 350 K = some cnArm)
    (e : Bool × Need) (acc : Need) :
    nock (C innG0 (C (C (ciTackE e) acc.toNoun) L)) innG0 = some (side e.1 acc e.2).toNoun := by
  obtain ⟨h, n⟩ := e
  unfold innG0
  cases h <;> simp [nock_exec, ciTackE, loob, hL, hcn, cnArm, cn_gate, side]

theorem inn_roll (L K : Noun) (hL : slot? 1023 L = some K) (hcn : slot? 350 K = some cnArm)
    (tack : List (Bool × Need)) :
    nock (C roll.battery (C (C (listNoun ciTackE tack) (C innG0 (C (C (C (A 0) (C (A 0x656e6f6e)
      (A 0))) (C (A 0x656e6f6e) (A 0))) L))) layer2)) roll.battery = some (rollTack tack).toNoun := by
  have h := ci_roll_gate ciTackE Need.toNoun layer2 innG0 (C (A 0) (C (A 0x656e6f6e) (A 0))) L
    (fun e acc => side e.1 acc e.2) tack Need.none (fun e _ acc => inn_roll_gate L K hL hcn e acc)
  simp only [Need.toNoun, Tag.none] at h
  exact h

variable (x : GenRest)

variable {x} in
theorem inn_loop {ctx K : Noun} (hc : CompIn ctx) (hK : slot? 7 ctx = some K)
    (hcn : slot? 350 K = some cnArm) (B : Noun) (o : Nat) :
    ∀ axe, 1 ≤ axe → ∀ (ned : Need) (tack : List (Bool × Need)) (ops : List Pole)
      (g : Gen (TreapMap mugF)),
    nock (C innL0 (C (listNoun Pole.toNoun ops) (C (listNoun ciTackE tack) (C B
      (C (C (A axe) (C ned.toNoun (A o))) (compCore g x ctx)))))) innL0
      = (intoLoop o axe ned tack ops g).map
          fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x) := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha ned tack ops g
    by_cases a1 : axe = 1
    · subst a1
      have hao := comp_add_ops x hc g o ops
      nock_open innL0
      rw [intoLoop.eq_def]
      cases e : addOps (Map := TreapMap mugF) o ops g with
      | none =>
        rw [e] at hao
        simp [nock_exec, comp_add_ops_arm, hao, e, bind, StateT.bind]
      | some p =>
        obtain ⟨u, g'⟩ := p
        rw [e] at hao
        simp [nock_exec, comp_add_ops_arm, hao, e, bind, StateT.bind, hK, hcn, hc, roll_arm, roll.arm_at, inn_roll, pure,
          StateT.pure]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      have hna : ¬ (axe ≤ 1) := by omega
      nock_open innL0
      rw [intoLoop.eq_def]
      rcases capF_cases axe h2 with hc2 | hc3
      · cases ned with
        | none =>
          have IH := fun g' => ihm Need.none ((true, Need.none) :: tack) ops g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH]
        | this r =>
          have IH := fun g' => ihm (Need.this g.re) ((true, Need.this (g.re + 1)) :: tack)
            (Pole.con g.re (g.re + 1) r :: ops) g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH]
        | pair p q =>
          obtain ⟨u, v, hp⟩ := cd_need_cell p
          have IH := fun g' => ihm p ((true, q) :: tack) ops g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false, hp] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH, hp]
        | both r hh tt =>
          obtain ⟨⟨⟨r1, n1⟩, g1⟩, e1⟩ := cd_must_some hh g
          obtain ⟨⟨⟨r2, n2⟩, g2⟩, e2⟩ := cd_must_some tt g1
          have IH := fun g' => ihm n1 ((true, n2) :: tack) (Pole.con r1 r2 r :: ops) g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH, e1, e2]
      · cases ned with
        | none =>
          have IH := fun g' => ihm Need.none ((false, Need.none) :: tack) ops g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH]
        | this r =>
          have IH := fun g' => ihm (Need.this (g.re + 1)) ((false, Need.this g.re) :: tack)
            (Pole.con g.re (g.re + 1) r :: ops) g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH]
        | pair p q =>
          obtain ⟨u, v, hp⟩ := cd_need_cell p
          have IH := fun g' => ihm q ((false, p) :: tack) ops g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false, hp] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH, hp]
        | both r hh tt =>
          obtain ⟨⟨⟨r1, n1⟩, g1⟩, e1⟩ := cd_must_some hh g
          obtain ⟨⟨⟨r2, n2⟩, g2⟩, e2⟩ := cd_must_some tt g1
          have IH := fun g' => ihm n2 ((false, n1) :: tack) (Pole.con r1 r2 r :: ops) g'
          simp only [listNoun, ciTackE, Need.toNoun, Pole.toNoun, loob, Tag.none, Tag.this, Tag.both, Tag.con,
            compCore, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, Tag.con, Pole.toNoun, listNoun, ciTackE, loob, eqCode_atom, eqCode, comp_re' ctx x, comp_must_arm, comp_must' ctx x, bind, StateT.bind, re, pure, StateT.pure, IH, e1, e2]

variable {x} in
/-- `+into-need`: the needs of the donor and of the recipient. -/
theorem comp_into_need {ctx : Noun} (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF))
    (axe : Nat) (ned : Need) (o : Nat) :
    nock (C innBat (C (C (A axe) (C ned.toNoun (A o))) (compCore g x ctx))) innBat
      = (intoNeed axe ned o g).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x) := by
  obtain ⟨K, hK, _, hcn⟩ := hl
  nock_open innBat
  by_cases a0 : axe = 0
  · subst a0; simp [nock_exec, intoNeed]
  have a0' : ¬ (0 = axe) := fun h => a0 h.symm
  by_cases a1 : axe = 1
  · subst a1; simp [nock_exec, intoNeed, pure, StateT.pure, Need.toNoun, Tag.none]
  have a1' : ¬ (1 = axe) := fun h => a1 h.symm
  have hlp := inn_loop (x := x) hc hK hcn innBat o axe (by omega) ned [] [] g
  simp only [listNoun] at hlp
  simp [nock_exec, intoNeed, a0, a0', a1, a1', hlp]

/-! ## `+into-sure` -/

def isG0 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 58)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 5)))) (C (C (C (A 0) (A 58)) (C (A 0) (A 59))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2)))))))) (C (A 0) (A 59))))))))))))))

def isBat : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 117))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (A 0)))) (C (C (A 1) isG0) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 4)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 28)))) (C (C (A 0) (A 5)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 342) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 244)) (C (A 0) (A 123))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 4)) (C (A 0) (A 12))) (C (C (A 0) (A 5)) (C (A 0) (A 13)))) (C (A 0) (A 126)))))))))))))

def isArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0)))) (C (C (A 1) isBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x657275732d6f746e692d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

-- door axis 1769470, core axis 2818046
theorem comp_is_at : slot? 1769470 comp.door = some isArm := by kernel_rfl

-- isG0 at 221053 of isBat

/-- One step of the `+rep:in` of `+into-sure`, on a look that is not `0`,
with `axe` not `0`. -/
noncomputable def isStep (axe l : Nat) (s : CSet × CSet) : CSet × CSet :=
  match gep axe l with
  | some (some r) => if r = 1 then s else (HoonSet.put s.1 r, s.2)
  | _ => (s.1, HoonSet.put s.2 l)

theorem is_intoStep {axe l : Nat} (ha : axe ≠ 0) (hl : l ≠ 0) (s : CSet × CSet) :
    intoStep axe (some s) l = some (isStep axe l s) := by
  obtain ⟨d, r⟩ := s
  have hg : gep axe l ≠ Option.none := fun h => by
    rcases gep_crash.1 h with h | h
    · exact ha h
    · exact hl h
  unfold intoStep isStep
  cases e : gep axe l with
  | none => exact absurd e hg
  | some u =>
    cases u with
    | none => simp [ha]
    | some r => by_cases r1 : r = 1 <;> simp [ha, r1]

theorem is_intoLok {axe : Nat} (lok : CSet) (ha : axe ≠ 0) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    intoLok axe lok = some ((HoonSet.toList lok).foldl (fun s y => isStep axe y s)
      (HoonSet.empty, HoonSet.empty)) := by
  unfold intoLok
  generalize ((HoonSet.empty, HoonSet.empty) : CSet × CSet) = acc
  generalize HoonSet.toList lok = l at h0 ⊢
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    rw [List.foldl_cons, List.foldl_cons, is_intoStep ha (h0 y List.mem_cons_self)]
    exact ih (isStep axe y acc) (fun z hz => h0 z (List.mem_cons_of_mem _ hz))

/-- One slam of the gate of the `+rep:in` of `+into-sure`. -/
theorem is_gate {ctx : Noun} (hc : CompIn ctx) (hl : CompLib ctx) (B R G : Noun) (axe l : Nat)
    (ha : axe ≠ 0) (hl0 : l ≠ 0) (s : CSet × CSet) :
    nock (C isG0 (C (C (A l) (ssN s)) (C B (C (C (A axe) R) (C comp.door (C G ctx)))))) isG0
      = some (ssN (isStep axe l s)) := by
  obtain ⟨K, hK, hgep, _⟩ := hl
  have hgg := gep_gate K (ci_layer2_K hc hK) axe l
  obtain ⟨d, r⟩ := s
  have ha' : ¬ (0 = axe) := fun h => ha h.symm
  unfold isG0
  cases e : gep axe l with
  | none =>
    rcases gep_crash.1 e with h | h
    · exact absurd h ha
    · exact absurd h hl0
  | some u =>
    rw [e] at hgg
    have hpd := fun (m : CSet) (y : Nat) => put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF m y)
    cases u with
    | none =>
      simp [nock_exec, ha', hK, hgep, gepArm, hgg, unitNoun, isStep, e, ssN, hc, in_arm, in.arm_at,
        put_in_arm, hpd]
    | some r =>
      by_cases r1 : r = 1
      · subst r1
        simp [nock_exec, ha', hK, hgep, gepArm, hgg, unitNoun, isStep, e, ssN, eqCode_atom]
      · have r1' : ¬ (1 = r) := fun h => r1 h.symm
        simp [nock_exec, ha', hK, hgep, gepArm, hgg, unitNoun, isStep, e, ssN, hc, in_arm, in.arm_at,
          put_in_arm, hpd, eqCode_atom, r1, r1']


/-- The arm `into-need` builds its gate. -/
theorem comp_inn_arm (d : Noun) : nock d innArm =
    some (C innBat (C (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (A 0))) d)) := by
  unfold innArm; simp only [nock_exec]

variable {x} in
/-- `+into-sure`: the looks split by `+rep:in` with `+gep`, `axe` put in the
recipient's looks unless it is `1`, then `+into-need`; with `axe` not `0` and
no look at axis `0`. -/
theorem comp_into_sure (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF)) (axe : Nat)
    (sur : Sure CSet) (o : Nat) (ha : axe ≠ 0) (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C isBat (C (C (A axe) (C sur.toNoun (A o))) (compCore g x ctx))) isBat
      = (intoSure axe sur o g).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x) := by
  obtain ⟨ned, lok⟩ := sur
  simp only at h0
  have hrep := rep_gate_on ssN (fun n s => match n with | Noun.atom y => isStep axe y s | _ => s)
    in.battery layer2 isG0 (A 0)
    (C isBat (C (C (A axe) (C (C ned.toNoun (HoonSet.toNoun lok)) (A o)))
      (C comp.door (C (genNoun g x) ctx))))
    (HoonSet.toNoun lok) (cs_tree lok) (HoonSet.empty, HoonSet.empty) (by
      intro n hn s
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact is_gate hc hl _ _ _ axe y ha (h0 y hy) s)
  rw [cs_preorder, List.foldl_map] at hrep
  have hil := is_intoLok (axe := axe) lok ha h0
  generalize (HoonSet.toList lok).foldl (fun s y => isStep axe y s) (HoonSet.empty, HoonSet.empty) = F
    at hrep hil
  obtain ⟨ld, lr⟩ := F
  simp only [ssN, HoonSet.toNoun_empty] at hrep
  have hin := comp_into_need (x := x) hc hl g axe ned o
  have hpt := put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF lr axe)
  simp only [Sure.toNoun]
  nock_open isBat
  have hD := comp_inn_at
  simp only [compCore] at hin ⊢
  generalize comp.door = D at hD hrep hin ⊢
  by_cases a1 : axe = 1
  · subst a1
    cases e : intoNeed 1 ned o g with
    | none =>
      rw [e] at hin
      simp [nock_exec, intoSure, hil, e, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep,
        hD, comp_inn_arm, hin]
    | some p =>
      obtain ⟨⟨nd, nr⟩, g'⟩ := p
      rw [e] at hin
      simp [nock_exec, intoSure, hil, e, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep,
        hD, comp_inn_arm, hin, Sure.toNoun]
  · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
    cases e : intoNeed axe ned o g with
    | none =>
      rw [e] at hin
      simp [nock_exec, intoSure, hil, e, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep,
        hD, comp_inn_arm, hin, a1, a1', put_in_arm, hpt]
    | some p =>
      obtain ⟨⟨nd, nr⟩, g'⟩ := p
      rw [e] at hin
      simp [nock_exec, intoSure, hil, e, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep,
        hD, comp_inn_arm, hin, Sure.toNoun, a1, a1', put_in_arm, hpt]


/-! ## `+into` -/

def intL0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2afffe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (C (A 0) (A 28)) (C (A 0) (A 30))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 58)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 59)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (C (C (A 0) (A 4)) (C (A 1) (C (A 0) (A 0)))) (C (C (A 0) (A 5)) (C (A 1) (C (A 0) (A 0))))) (C (A 0) (A 510))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (C (A 0) (A 1022)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 510))) (C (C (A 1) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 48))) (C (A 10) (C (C (A 6) (C (A 0) (A 49))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 114))) (C (A 10) (C (C (A 6) (C (A 0) (A 115))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (C (A 0) (A 240)) (C (A 0) (A 12))) (C (C (A 0) (A 242)) (C (A 0) (A 4)))) (C (C (C (A 0) (A 240)) (C (A 0) (A 13))) (C (C (A 0) (A 242)) (C (A 0) (A 5))))) (C (A 0) (A 8190)))))))))))))))))))))))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 251)) (C (C (A 0) (A 2046)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 1022))) (C (C (A 1) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 24))) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 56)) (C (A 0) (A 4))) (C (C (A 0) (A 56)) (C (A 0) (A 5)))) (C (A 0) (A 8190)))))))))))))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 28)) (C (A 0) (A 12))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (C (A 0) (A 29)) (C (A 0) (A 13))))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046))))))))))))))))))))))))))))))))))))

def intBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 43690) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 115)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 114)) (C (A 8) (C (C (A 1) intL0) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (C (C (A 0) (A 8)) (C (C (A 0) (A 9)) (C (A 0) (A 6)))) (C (A 0) (A 5)))))))))))))

def intArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (A 0))) (C (C (A 1) intBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6f746e692d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

-- door axis 860, core axis 1372
theorem comp_int_at : slot? 860 comp.door = some intArm := by kernel_rfl

-- intL0 at 65501 of intBat

/-- The arm `into-sure` builds its gate. -/
theorem comp_is_arm (d : Noun) : nock d isArm =
    some (C isBat (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0))) d)) := by
  unfold isArm; simp only [nock_exec]

variable {x} in
/-- The loop `split-loop` of `+into` on a fork-free lazy need `[sure ~ ~]`:
`+into-sure`, then the test `&(?=(~ fork.laz) ?=(~ bond.laz))`, which holds. -/
theorem cit_loop (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF)) (sur : Sure CSet)
    (o : Nat) (L B N : Noun) (axe : Nat) (ha : axe ≠ 0) (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C L (C (lazyNoun sur) (C (A o) (C B (C (C N (A axe)) (compCore g x ctx)))))) intL0
      = (intoSure axe sur o g).map fun p => C (C (lazyNoun p.1.1) (lazyNoun p.1.2)) (genNoun p.2 x) := by
  have his := comp_into_sure (x := x) hc hl g axe sur o ha h0
  unfold intL0
  have hD := comp_is_at
  simp only [compCore] at his ⊢
  generalize comp.door = D at hD his ⊢
  cases e : intoSure axe sur o g with
  | none =>
    rw [e] at his
    simp [nock_exec, lazyNoun, hD, comp_is_arm, his]
  | some p =>
    obtain ⟨⟨sd, sr⟩, g'⟩ := p
    rw [e] at his
    simp [nock_exec, lazyNoun, hD, comp_is_arm, his]

variable {x} in
/-- `+into` on a `next` whose lazy need is fork-free: `+emit` of `[~ ~ %hop
then.nex]`, then the loop, with `axe` not `0` and no look at axis `0`.  It
returns `[[don ~ ~] [rec ~ ~] o]`. -/
theorem comp_into (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF)) (nex : Next CSet)
    (axe : Nat) (ha : axe ≠ 0) (h0 : ∀ y ∈ HoonSet.toList nex.laz.lok, y ≠ 0) :
    nock (C intBat (C (C nex.goal.toNoun (A axe)) (compCore g x ctx))) intBat
      = (into nex axe g).map fun p =>
          C (C (lazyNoun p.1.1) (C (lazyNoun p.1.2.1) (A p.1.2.2))) (genNoun p.2 x) := by
  obtain ⟨laz, th⟩ := nex
  have he := comp_emit x hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
  rw [cd_emit_eq] at he
  generalize hg1 : (if g.drop = true then { g with bo := g.bo + 1 }
      else { g with bo := g.bo + 1, blocks := HoonMap.put g.blocks g.bo ⟨[], [], Termin.hop th⟩ })
      = g1 at he
  have hlp := fun L B N => cit_loop (x := x) hc hl g1 laz g.bo L B N axe ha h0
  simp only [Next.goal, CGoal.toNoun]
  unfold intBat
  cases e : intoSure axe laz g.bo g1 with
  | none =>
    rw [e] at hlp
    simp [nock_exec, comp_emit_arm, he, hlp, into, cd_emit_eq, hg1, bind, StateT.bind, e]
  | some p =>
    obtain ⟨⟨sd, sr⟩, g2⟩ := p
    rw [e] at hlp
    simp [nock_exec, comp_emit_arm, he, hlp, into, cd_emit_eq, hg1, bind, StateT.bind, e, pure,
      StateT.pure]

end Compiler
end Formalization
