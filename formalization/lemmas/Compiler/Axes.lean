import lemmas.Compiler.So
import lemmas.Hoon.Axis
import lemmas.Hoon.Lists

/-!
The arms of `+ca` and `+so` that walk an axis with `+cap` and `+mas` of
`hoon.hoon`: `pat` and `lot` of `+ca`, `pull` of `+so`.  They compute track
B's models in `lemmas/Ska/Sock.lean`, with a crash (`none`) on axis `0`.  And
`yea` of `+ca`, which builds axes with `+peg` and joins lists with `+weld`.

These arms read `+cap` and `+mas` from layer 1 of `hoon.hoon`, below the
library core: `AxisOf lib` says that the noun at `ca.lib.layer1.axis` in the
library core `lib` holds `+cap` and `+mas` and what they read.

B's models use their own `cap` and `mas`; `capF_eq_cap` and `masF_eq_mas` tie
them to the models `capF` and `masF` of `lemmas/Hoon/Axis.lean`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-! ## The two models of `+cap` and `+mas` agree -/

theorem capF_eq_cap (a : Nat) : Hoon.capF a = SkaModel.cap a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    match a with
    | 0 => rw [Hoon.capF_eq]; simp [SkaModel.cap]
    | 1 => rw [Hoon.capF_eq]; simp [SkaModel.cap]
    | 2 => rw [Hoon.capF_eq]; simp [SkaModel.cap]
    | 3 => rw [Hoon.capF_eq]; simp [SkaModel.cap]
    | a + 4 =>
      rw [Hoon.capF_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        ih ((a + 4) / 2) (by omega)]
      simp only [SkaModel.cap]

theorem masF_eq_mas (a : Nat) : Hoon.masF a = SkaModel.mas a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    match a with
    | 0 => rw [Hoon.masF_eq]; simp [SkaModel.mas]
    | 1 => rw [Hoon.masF_eq]; simp [SkaModel.mas]
    | 2 => rw [Hoon.masF_eq]; simp [SkaModel.mas]
    | 3 => rw [Hoon.masF_eq]; simp [SkaModel.mas]
    | a + 4 =>
      rw [Hoon.masF_eq, if_neg (by omega), if_neg (by omega), ih ((a + 4) / 2) (by omega)]
      simp only [SkaModel.mas]

theorem cap_cases (a : Nat) (h : 2 ≤ a) : SkaModel.cap a = 2 ∨ SkaModel.cap a = 3 := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    match a, h with
    | 2, _ => simp [SkaModel.cap]
    | 3, _ => simp [SkaModel.cap]
    | a + 4, _ =>
      simp only [SkaModel.cap]
      exact ih ((a + 4) / 2) (by omega) (by omega)

/-! ## What the arms read -/

/-- The library core `lib` holds layer 1 of `hoon.hoon` at `ca.lib.layer1.axis`,
with `+cap` and `+mas`. -/
abbrev AxisOf (lib : Noun) : Prop :=
  ∃ l1, slot? ca.lib.layer1.axis lib = some l1 ∧ Hoon.CapIn l1 ∧ Hoon.MasIn l1

/-- What `pat`, `lot`, `pull` read from their context, the core of `+ca` or `+so`. -/
abbrev AxisIn (c : Noun) : Prop := Hoon.Below AxisOf c

/-! ## `+pull:so` -/

@[nock_exec] theorem so_pull_arm (c : Noun) :
    nock c so.pull.arm = some (C so.pull.battery (C (C (C (A 1) (A 0)) (A 0)) c)) := by
  nock_open so.pull.arm; simp only [nock_exec]

theorem so_pull_loop (ctx : Noun) (hc : AxisIn ctx) : ∀ (axe : Nat), 1 ≤ axe →
    ∀ (c : Cape) (d : Noun),
    nock (C so.pull.loop (C so.pull.battery (C (C (C c.toNoun d) (A axe)) ctx))) so.pull.loop
      = some (So.pullLoop c d axe).toNoun := by
  obtain ⟨bat, lib, rfl, l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩ := hc.elim
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro h1 c d
    nock_open so.pull.loop
    by_cases a1 : axe = 1
    · subst a1; rw [So.pullLoop.eq_def]; simp [nock_exec, sock_toNoun_mk]
    have h2 : 2 ≤ axe := by omega
    have hcap' := Hoon.cap_gate l1 hdiv axe h2
    have hmas' := Hoon.mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ axe h2
    rw [capF_eq_cap] at hcap'
    rw [masF_eq_mas] at hmas'
    have ih' := ih (SkaModel.mas axe) (SkaModel.mas_lt axe h2) (SkaModel.mas_pos axe h2)
    have ihy := ih' Cape.yes
    simp only [Cape.toNoun] at ihy
    have hne : ¬ (1 = axe) := by omega
    rw [So.pullLoop.eq_def, if_neg (by omega)]
    rcases cap_cases axe h2 with hc2 | hc3
    · rcases c with _ | _ | ⟨ch, ct⟩ <;> rcases d with k | ⟨dh, dt⟩ <;>
        simp [nock_exec, Cape.toNoun, sock_toNoun_mk, Sock.dunno, hne, hl, hcap, hmas,
          Hoon.cap_arm, Hoon.mas_arm, hcap', hmas', hc2, ih', ihy]
    · rcases c with _ | _ | ⟨ch, ct⟩ <;> rcases d with k | ⟨dh, dt⟩ <;>
        simp [nock_exec, Cape.toNoun, sock_toNoun_mk, Sock.dunno, hne, hl, hcap, hmas,
          Hoon.cap_arm, Hoon.mas_arm, hcap', hmas', hc3, ih', ihy]

theorem so_pull_gate (ctx : Noun) (hc : AxisIn ctx) (s : Sock) (axe : Nat) :
    nock (C so.pull.battery (C (C s.toNoun (A axe)) ctx)) so.pull.battery
      = (So.pull s axe).map Sock.toNoun := by
  nock_open so.pull.battery
  by_cases a0 : axe = 0
  · subst a0; simp [nock_exec, So.pull]
  have hne : ¬ (0 = axe) := by omega
  rcases s with _ | ⟨c, d⟩
  · simp [nock_exec, So.pull, a0, hne, sock_toNoun_void]
  · simp [nock_exec, So.pull, a0, hne, sock_toNoun_mk,
      so_pull_loop ctx hc axe (by omega) c d]

/-! ## `+pat:ca` -/

@[nock_exec] theorem ca_pat_arm (c : Noun) :
    nock c ca.pat.arm = some (C ca.pat.battery (C (C (A 1) (A 0)) c)) := by
  nock_open ca.pat.arm; simp only [nock_exec]

theorem ca_pat_loop (ctx : Noun) (hc : AxisIn ctx) (c : Cape) : ∀ (a : Nat), 1 ≤ a →
    nock (C ca.pat.loop (C ca.pat.battery (C (C c.toNoun (A a)) ctx))) ca.pat.loop
      = some (Ca.patLoop c a).toNoun := by
  obtain ⟨bat, lib, rfl, l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩ := hc.elim
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro h1
    nock_open ca.pat.loop
    by_cases a1 : a = 1
    · subst a1; rw [Ca.patLoop.eq_def]; simp [nock_exec]
    have h2 : 2 ≤ a := by omega
    have hcap' := Hoon.cap_gate l1 hdiv a h2
    have hmas' := Hoon.mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ a h2
    rw [capF_eq_cap] at hcap'
    rw [masF_eq_mas] at hmas'
    have ih' := ih (SkaModel.mas a) (SkaModel.mas_lt a h2) (SkaModel.mas_pos a h2)
    have hne : ¬ (1 = a) := by omega
    rw [Ca.patLoop.eq_def, dif_neg (by omega)]
    rcases cap_cases a h2 with hc2 | hc3
    · simp [nock_exec, Cape.toNoun, hne, hl, hcap, hmas, Hoon.cap_arm, Hoon.mas_arm, hcap', hmas',
        hc2, ih']
    · simp [nock_exec, Cape.toNoun, hne, hl, hcap, hmas, Hoon.cap_arm, Hoon.mas_arm, hcap', hmas',
        hc3, ih']

theorem ca_pat_gate (ctx : Noun) (hc : AxisIn ctx) (c : Cape) (a : Nat) :
    nock (C ca.pat.battery (C (C c.toNoun (A a)) ctx)) ca.pat.battery
      = (Ca.pat c a).map Cape.toNoun := by
  nock_open ca.pat.battery
  by_cases a0 : a = 0
  · subst a0; simp [nock_exec, Ca.pat]
  have hne : ¬ (0 = a) := by omega
  by_cases hno : c = Cape.no
  · subst hno; simp [nock_exec, Ca.pat, a0, hne, Cape.toNoun]
  have hno1 : ¬ (A 1 = c.toNoun) := fun h => hno (cape_toNoun_inj (a := c) (b := Cape.no) h.symm)
  simp [nock_exec, Ca.pat, a0, hne, hno, hno1, ca_pat_loop ctx hc c a (by omega)]

/-! ## `+lot:ca` -/

@[nock_exec] theorem ca_lot_arm (c : Noun) :
    nock c ca.lot.arm = some (C ca.lot.battery (C (C (A 1) (A 0)) c)) := by
  nock_open ca.lot.arm; simp only [nock_exec]

theorem ca_lot_loop (ctx : Noun) (hc : AxisIn ctx) : ∀ (axe : Nat), 1 ≤ axe → ∀ (c : Cape),
    nock (C ca.lot.battery (C (C c.toNoun (A axe)) ctx)) ca.lot.battery
      = some (Ca.lot.lotLoop c axe).toNoun := by
  obtain ⟨bat, lib, rfl, l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩ := hc.elim
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro h1 c
    nock_open ca.lot.battery
    have hne0 : ¬ (0 = axe) := by omega
    by_cases a1 : axe = 1
    · subst a1; rw [Ca.lot.lotLoop.eq_def]; simp [nock_exec]
    have h2 : 2 ≤ axe := by omega
    have hcap' := Hoon.cap_gate l1 hdiv axe h2
    have hmas' := Hoon.mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ axe h2
    rw [capF_eq_cap] at hcap'
    rw [masF_eq_mas] at hmas'
    have ih' := ih (SkaModel.mas axe) (SkaModel.mas_lt axe h2) (SkaModel.mas_pos axe h2)
    have hne : ¬ (1 = axe) := by omega
    rw [Ca.lot.lotLoop.eq_def, if_neg (by omega)]
    rcases cap_cases axe h2 with hc2 | hc3
    · cases c <;> simp [nock_exec, Cape.toNoun, hne0, hne, hl, hcap, hmas, Hoon.cap_arm,
        Hoon.mas_arm, hcap', hmas', hc2, ih']
    · cases c <;> simp [nock_exec, Cape.toNoun, hne0, hne, hl, hcap, hmas, Hoon.cap_arm,
        Hoon.mas_arm, hcap', hmas', hc3, ih']

theorem ca_lot_gate (ctx : Noun) (hc : AxisIn ctx) (c : Cape) (axe : Nat) :
    nock (C ca.lot.battery (C (C c.toNoun (A axe)) ctx)) ca.lot.battery
      = (Ca.lot c axe).map Cape.toNoun := by
  by_cases a0 : axe = 0
  · subst a0; nock_open ca.lot.battery; simp [nock_exec, Ca.lot]
  rw [ca_lot_loop ctx hc axe (by omega) c]
  simp [Ca.lot, a0]

/-! ## `+yea:ca` -/

theorem pegF_two (a : Nat) : Hoon.pegF a 2 = a * 2 := by rw [Hoon.pegF_eq]; simp

theorem pegF_three (a : Nat) : Hoon.pegF a 3 = a * 2 + 1 := by rw [Hoon.pegF_eq]; simp

/-- The library core `lib` holds layer 2 of `hoon.hoon` with `+weld`, and
layer 1 with `+peg`. -/
abbrev YeaOf (lib : Noun) : Prop :=
  ∃ l2 l1, slot? ca.lib.layer2.axis lib = some l2 ∧ slot? weld.axis l2 = some weld.arm ∧
    slot? ca.lib.layer1.axis lib = some l1 ∧ Hoon.PegIn l1

abbrev YeaIn (c : Noun) : Prop := Hoon.Below YeaOf c

@[nock_exec] theorem ca_yea_arm (c : Noun) :
    nock c ca.yea.arm = some (C ca.yea.battery (C (A 1) c)) := by
  nock_open ca.yea.arm; simp only [nock_exec]

theorem ca_yea_loop (ctx : Noun) (hc : YeaIn ctx) : ∀ (c : Cape) (axe : Nat), 1 ≤ axe →
    nock (C ca.yea.loop (C (A axe) (C ca.yea.battery (C c.toNoun ctx)))) ca.yea.loop
      = some (Hoon.listN ((Ca.yeaAt c axe).map A)) := by
  obtain ⟨bat, lib, rfl, l2, l1, hl2, hweld, hl1, hpeg⟩ := hc.elim
  intro c
  induction c with
  | no => intro axe _; nock_open ca.yea.loop; simp [nock_exec, Cape.toNoun, Ca.yeaAt]
  | yes => intro axe _; nock_open ca.yea.loop; simp [nock_exec, Cape.toNoun, Ca.yeaAt]
  | cell h t ih it =>
    intro axe h1
    have p2 := Hoon.peg_gate l1 hpeg.2 axe h1 2 (by omega)
    have p3 := Hoon.peg_gate l1 hpeg.2 axe h1 3 (by omega)
    rw [pegF_two] at p2
    rw [pegF_three] at p3
    nock_open ca.yea.loop
    simp [nock_exec, Cape.toNoun, Ca.yeaAt, hl2, hweld, hl1, hpeg.1, Hoon.peg_arm, Hoon.weld_arm,
      p2, p3, ih (axe * 2) (by omega), it (axe * 2 + 1) (by omega), Hoon.weld_gate_list]

/-- Slamming `yea` of `+ca` on a cape: its list of known axes. -/
theorem ca_yea_gate (ctx : Noun) (hc : YeaIn ctx) (c : Cape) :
    nock (C ca.yea.battery (C c.toNoun ctx)) ca.yea.battery
      = some (Hoon.listN ((Ca.yea c).map A)) := by
  nock_open ca.yea.battery
  simp only [nock_exec, ca_yea_loop ctx hc c 1 (by omega), Ca.yea]

end Compiler
end Formalization
