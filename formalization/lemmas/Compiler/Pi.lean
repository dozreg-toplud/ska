import lemmas.Compiler.Axes
import lemmas.Pill.Arm.Pi
import lemmas.Ska.Pi

/-!
The arms `cons`, `hed`, `tel` of the provenance core `+pi` compute the models
of `lemmas/Ska/Pi.lean`.  `hed` and `tel` read `+peg` of layer 1 through the
library core (`PegOf`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-- The two models of `+peg` agree. -/
theorem pegF_eq_peg (a : Nat) : ∀ b, Hoon.pegF a b = SkaModel.peg a b := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    match b with
    | 0 => rw [Hoon.pegF_eq]; simp [SkaModel.peg]
    | 1 => rw [Hoon.pegF_eq]; simp [SkaModel.peg]
    | 2 => rw [Hoon.pegF_eq]; simp [SkaModel.peg]
    | 3 => rw [Hoon.pegF_eq]; simp [SkaModel.peg]
    | b + 4 =>
      rw [Hoon.pegF_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        ih ((b + 4) / 2) (by omega)]
      simp only [SkaModel.peg]

/-- The library core `lib` holds layer 1 of `hoon.hoon` with `+peg`. -/
abbrev PegOf (lib : Noun) : Prop :=
  ∃ l1, slot? ca.lib.layer1.axis lib = some l1 ∧ Hoon.PegIn l1

/-- What `hed` and `tel` of `+pi` read from their context, the core of `+pi`. -/
abbrev PiPegIn (c : Noun) : Prop := Hoon.Below PegOf c

@[nock_exec] theorem pi_cons_arm (c : Noun) :
    nock c pi.cons.arm = some (C pi.cons.battery (C (C (A 0) (A 0)) c)) := by
  nock_open pi.cons.arm; simp only [nock_exec]

@[nock_exec] theorem pi_hed_arm (c : Noun) :
    nock c pi.hed.arm = some (C pi.hed.battery (C (A 0) c)) := by
  nock_open pi.hed.arm; simp only [nock_exec]

@[nock_exec] theorem pi_tel_arm (c : Noun) :
    nock c pi.tel.arm = some (C pi.tel.battery (C (A 0) c)) := by
  nock_open pi.tel.arm; simp only [nock_exec]

theorem pi_cons_gate (ctx a b : Noun) :
    nock (C pi.cons.battery (C (C a b) ctx)) pi.cons.battery = some (Pi.cons a b) := by
  nock_open pi.cons.battery
  by_cases ha : A 0 = a <;> by_cases hb : A 0 = b
  · subst ha hb; simp [nock_exec, Pi.cons]
  · subst ha; simp [nock_exec, Pi.cons, hb, Ne.symm hb]
  · subst hb; simp [nock_exec, Pi.cons, ha, Ne.symm ha]
  · simp [nock_exec, Pi.cons, ha, hb, Ne.symm ha]

theorem pi_hed_gate (ctx : Noun) (hc : PiPegIn ctx) (n : Noun) :
    nock (C pi.hed.battery (C n ctx)) pi.hed.battery = some (Pi.hed n) := by
  obtain ⟨bat, lib, rfl, l1, hl, hpeg, hpegs⟩ := hc.elim
  nock_open pi.hed.battery
  rcases n with (_ | p) | ⟨h, t⟩
  · simp [nock_exec, Pi.hed]
  · have hg := Hoon.peg_gate l1 hpegs (p + 1) (by omega) 2 (by omega)
    rw [pegF_eq_peg] at hg
    simp [nock_exec, Pi.hed, hl, hpeg, Hoon.peg_arm, hg]
  · simp [nock_exec, Pi.hed]

theorem pi_tel_gate (ctx : Noun) (hc : PiPegIn ctx) (n : Noun) :
    nock (C pi.tel.battery (C n ctx)) pi.tel.battery = some (Pi.tel n) := by
  obtain ⟨bat, lib, rfl, l1, hl, hpeg, hpegs⟩ := hc.elim
  nock_open pi.tel.battery
  rcases n with (_ | p) | ⟨h, t⟩
  · simp [nock_exec, Pi.tel]
  · have hg := Hoon.peg_gate l1 hpegs (p + 1) (by omega) 3 (by omega)
    rw [pegF_eq_peg] at hg
    simp [nock_exec, Pi.tel, hl, hpeg, Hoon.peg_arm, hg]
  · simp [nock_exec, Pi.tel]

/-! ## `slot` -/

/-- What `slot` of `+pi` reads from its context: `+cap`, `+mas`, `+peg`. -/
abbrev PiSlotIn (c : Noun) : Prop := Hoon.Below (fun lib => AxisOf lib ∧ PegOf lib) c

@[nock_exec] theorem pi_slot_arm (c : Noun) :
    nock c pi.slot.arm = some (C pi.slot.battery (C (C (A 0) (A 0)) c)) := by
  nock_open pi.slot.arm; simp only [nock_exec]

/-- Slamming `slot` of `+pi` on a provenance and an axis `ax ≥ 1`. -/
theorem pi_slot_gate (ctx : Noun) (hc : PiSlotIn ctx) : ∀ (ax : Nat), 1 ≤ ax → ∀ (pin : Noun),
    nock (C pi.slot.battery (C (C pin (A ax)) ctx)) pi.slot.battery = some (Pi.slot pin ax) := by
  obtain ⟨bat, lib, rfl, ⟨l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩, l1', hl', hpeg,
    hpegs⟩ := hc.elim
  rw [hl] at hl'
  cases hl'
  intro ax
  induction ax using Nat.strongRecOn with
  | ind ax ih =>
    intro h1 pin
    nock_open pi.slot.battery
    by_cases a1 : ax = 1
    · subst a1; rw [Pi.slot.eq_def]; simp [nock_exec]
    have h2 : 2 ≤ ax := by omega
    have hne : ¬ (ax = 1) := a1
    have hcap' := Hoon.cap_gate l1 hdiv ax h2
    have hmas' := Hoon.mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ ax h2
    rw [capF_eq_cap] at hcap'
    rw [masF_eq_mas] at hmas'
    have ih' := ih (SkaModel.mas ax) (SkaModel.mas_lt ax h2) (SkaModel.mas_pos ax h2)
    rw [Pi.slot.eq_def, if_neg a1]
    rcases pin with (_ | p) | ⟨h, t⟩
    · simp [nock_exec, hne]
    · have hg := Hoon.peg_gate l1 hpegs (p + 1) (by omega) ax (by omega)
      rw [pegF_eq_peg] at hg
      simp [nock_exec, hne, hl, hpeg, Hoon.peg_arm, hg]
    · have hlt : ¬ ax < 2 := by omega
      rcases cap_cases ax h2 with hc2 | hc3
      · simp [nock_exec, hne, hlt, hl, hcap, hmas, Hoon.cap_arm, Hoon.mas_arm, hcap', hmas', hc2, ih']
      · simp [nock_exec, hne, hlt, hl, hcap, hmas, Hoon.cap_arm, Hoon.mas_arm, hcap', hmas', hc3,
          ih']

/-! ## `compose` -/

/-- What `compose` of `+pi` reads from its context, the core of `+pi`: its arms
`slot` and `cons`, and what `slot` reads. -/
abbrev ComposeIn (c : Noun) : Prop :=
  slot? pi.slot.axis c = some pi.slot.arm ∧ slot? pi.cons.axis c = some pi.cons.arm ∧ PiSlotIn c

@[nock_exec] theorem pi_compose_arm (c : Noun) :
    nock c pi.compose.arm = some (C pi.compose.battery (C (C (A 0) (A 0)) c)) := by
  nock_open pi.compose.arm; simp only [nock_exec]

theorem pi_compose_loop (ctx : Noun) (hc : ComposeIn ctx) (b : Noun) : ∀ (a : Noun),
    nock (C pi.compose.loop (C pi.compose.battery (C (C a b) ctx))) pi.compose.loop
      = some (Pi.composeLoop b a) := by
  obtain ⟨hs, hcons, hsl⟩ := hc
  intro a
  induction a with
  | atom p =>
    nock_open pi.compose.loop
    rcases p with _ | p
    · simp [nock_exec, Pi.composeLoop]
    · simp [nock_exec, Pi.composeLoop, hs, pi_slot_arm, pi_slot_gate ctx hsl (p + 1) (by omega)]
  | cell h t ih it =>
    nock_open pi.compose.loop
    simp [nock_exec, Pi.composeLoop, hcons, pi_cons_arm, ih, it, pi_cons_gate]

/-- Slamming `compose` of `+pi` on two provenances. -/
theorem pi_compose_gate (ctx : Noun) (hc : ComposeIn ctx) (a b : Noun) :
    nock (C pi.compose.battery (C (C a b) ctx)) pi.compose.battery = some (Pi.compose a b) := by
  nock_open pi.compose.battery
  by_cases hb : A 0 = b
  · subst hb; simp [nock_exec, Pi.compose]
  · simp [nock_exec, Pi.compose, hb, Ne.symm hb, pi_compose_loop ctx hc b a]

end Compiler
end Formalization
