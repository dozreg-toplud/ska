module

public import lemmas.Hoon.Rip
public import lemmas.Hoon.Lists
public import lemmas.Iter
import all lemmas.Pill.Arm.Dec
import all lemmas.Pill.Arm.Lth
import all lemmas.Pill.Arm.Dvr
import all lemmas.Pill.Arm.Mod
import all lemmas.Pill.Arm.End
import all lemmas.Pill.Arm.Rip
import all lemmas.Pill.Arm.Lent

/-!
# Arithmetic on a cell

The gates of the library that take atoms do not check their samples, so a
cell can reach them.  `+dec` of a cell never returns: its loop counts up from
`0` and compares each count with the cell (`dec_gate_cell`, by induction on
the depth of the calls, `iterN`).  So `+lth`, `+dvr`, `+mod`, `+end` and
`+rip` crash on a cell where they would call `+dec` on it:
`(rip 3 [x y])` reaches `(end 3 [x y])`, then `(mod [x y] 256)`,
`(dvr [x y] 256)`, `(lth [x y] 256)` and `(dec [x y])`.

`+lent` crashes on a noun that is not a list: on an atom other than `0` it
reads the tail of the atom (`lent_gate_bad`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## `+dec` -/

/-- The loop of `+dec` on a cell, with every counter and at every depth of
calls, does not return. -/
theorem dec_loop_cell (c x y : Noun) : ∀ (k b : Nat),
    iterN k (C dec.loop (C (A b) (C dec.battery (C (C x y) c)))) dec.loop = none := by
  intro k
  induction k with
  | zero => intro b; rfl
  | succ k ih =>
    intro b
    rw [iterN_succ]
    conv => { lhs; arg 3; unfold dec.loop }
    simp [nock_exec, ih]

/-- `+dec` of a cell does not return. -/
theorem dec_gate_cell (c x y : Noun) :
    nock (C dec.battery (C (C x y) c)) dec.battery = none := by
  cases h : nock (C dec.battery (C (C x y) c)) dec.battery with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨k, hk⟩ := iterN_complete h
    cases k with
    | zero => simp [iterN] at hk
    | succ k =>
      rw [iterN_succ] at hk
      conv at hk => { lhs; arg 3; unfold dec.battery }
      simp [nock_exec, dec_loop_cell] at hk

/-! ## `+lth`, `+dvr`, `+mod` -/

theorem lth_loop_cell (c : Noun) (hc : DecIn c) (x y : Noun) (n : Nat) (hn : 0 < n) :
    nock (C lth.loop (C lth.battery (C (C (C x y) (A n)) c))) lth.loop = none := by
  have h2 : ¬ (0 = n) := by omega
  nock_open lth.loop
  simp [nock_exec, h2, hc, dec_arm, dec_gate_cell]

/-- `(lth [x y] n)` crashes on a positive `n`. -/
theorem lth_gate_cell (c : Noun) (hc : DecIn c) (x y : Noun) (n : Nat) (hn : 0 < n) :
    nock (C lth.battery (C (C (C x y) (A n)) c)) lth.battery = none := by
  nock_open lth.battery
  simp [nock_exec, lth_loop_cell c hc x y n hn]

theorem dvr_loop_cell (c : Noun) (hc : LthIn c ∧ SubIn c) (x y : Noun) (n k : Nat) (hn : 0 < n) :
    nock (C dvr.loop (C (A k) (C dvr.battery (C (C (C x y) (A n)) c)))) dvr.loop = none := by
  nock_open dvr.loop
  simp [nock_exec, hc, lth_arm, lth_gate_cell c hc.1.2 x y n hn]

/-- `(dvr [x y] n)` crashes on a positive `n`. -/
theorem dvr_gate_cell (c : Noun) (hc : LthIn c ∧ SubIn c) (x y : Noun) (n : Nat) (hn : 0 < n) :
    nock (C dvr.battery (C (C (C x y) (A n)) c)) dvr.battery = none := by
  have h1 : ¬ (0 = n) := by omega
  nock_open dvr.battery
  simp [nock_exec, h1, dvr_loop_cell c hc x y n 0 hn]

/-- `(mod [x y] n)` crashes on a positive `n`. -/
theorem mod_gate_cell (c : Noun) (hc : DvrIn c) (x y : Noun) (n : Nat) (hn : 0 < n) :
    nock (C mod.battery (C (C (C x y) (A n)) c)) mod.battery = none := by
  nock_open mod.battery
  simp [nock_exec, hc, dvr_arm, dvr_gate_cell c hc.2 x y n hn]

/-! ## `+end`, `+rip` -/

/-- `(end a [x y])` crashes on a bite `a`. -/
theorem end_gate_cell (c : Noun) (hc : EndIn c) (a : Noun) (bl st : Nat) (ha : BiteIs a bl st)
    (x y : Noun) :
    nock (C end.battery (C (C a (C x y)) c)) end.battery = none := by
  have hbex := bex_gate c hc.2.1.2
  obtain ⟨_, ⟨hb, hm⟩, hd⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := hm.elim
  have hd : ModIn t := hd
  rcases ha with rfl | ⟨rfl, rfl⟩
  all_goals
    nock_open end.battery
    simp [nock_exec, hb, hbex, ht, hd, mul_arm, bex_arm, mod_arm, mul_gate t ht.2,
      mod_gate_cell t hd.2 _ _ _ (Nat.two_pow_pos _)]

/-- `(rip a [x y])` crashes on a bite `a`. -/
theorem rip_gate_cell (c : Noun) (hc : EndIn c ∧ RshIn c) (a : Noun) (bl st : Nat)
    (ha : BiteIs a bl st) (x y : Noun) :
    nock (C rip.battery (C (C a (C x y)) c)) rip.battery = none := by
  nock_open rip.battery
  simp [nock_exec, hc.1, end_arm, end_gate_cell c hc.1 a bl st ha x y]

/-! ## `+lent` -/

/-- The loop of `+lent` on a noun that is no list crashes. -/
theorem lent_loop_bad (c : Noun) : ∀ (n : Noun), (∀ l, n ≠ listN l) → ∀ (k : Nat),
    nock (C lent.loop (C (A k) (C lent.battery (C n c)))) lent.loop = none := by
  intro n
  induction n with
  | atom a =>
    intro hn k
    have ha : a ≠ 0 := fun e => hn [] (by subst e; rfl)
    have ha' : ¬ (0 = a) := fun e => ha e.symm
    nock_open lent.loop
    simp [nock_exec, ha']
  | cell h t _ iht =>
    intro hn k
    have ht : ∀ l, t ≠ listN l := fun l e => hn (h :: l) (by rw [e]; rfl)
    nock_open lent.loop
    simp [nock_exec, iht ht]

/-- `+lent` of a noun that is no list crashes. -/
theorem lent_gate_bad (c n : Noun) (hn : ∀ l, n ≠ listN l) :
    nock (C lent.battery (C n c)) lent.battery = none := by
  nock_open lent.battery
  simp only [nock_exec, lent_loop_bad c n hn 0]

end Hoon
end Formalization

end
