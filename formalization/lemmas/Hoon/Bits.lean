import lemmas.Hoon.Lists

/-!
The bit arithmetic of the pill's `hoon.hoon`, against `Nat`:

| arm | model |
| --- | --- |
| `+bex` | `2 ^ a` |
| `+lsh` | `b * 2 ^ (2 ^ bloq * step)` |
| `+rsh` | `b / 2 ^ (2 ^ bloq * step)` |
| `+end` | `b % 2 ^ (2 ^ bloq * step)` |
| `+met` | `metF a b`, the number of blocks of `2 ^ a` bits in `b` |
| `+cut` | `d / 2 ^ (2 ^ a * b) % 2 ^ (2 ^ a * c)` |
| `+cat` | `c * 2 ^ (2 ^ a * metF a b) + b` |
| `+mix`, `+dis`, `+con` | `a ^^^ b`, `a &&& b`, `a ||| b` |

The arms live in the library's second layer and call `+mul`, `+div`, `+mod`
and `+add` of the first layer through the tail of their context.

A `bite` is a bloq `a`, which means the step `1`, or a cell `[bloq step]`:
`BiteIs x bloq step`.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## What the gates read from their context -/

abbrev BexIn (c : Noun) : Prop := slot? bex.axis c = some bex.arm ∧ Below MulIn c
abbrev LshIn (c : Noun) : Prop := slot? lsh.axis c = some lsh.arm ∧ BexIn c
abbrev RshIn (c : Noun) : Prop := slot? rsh.axis c = some rsh.arm ∧ BexIn c ∧ Below DivIn c
abbrev EndIn (c : Noun) : Prop := slot? end.axis c = some end.arm ∧ BexIn c ∧ Below ModIn c
abbrev MetIn (c : Noun) : Prop := slot? met.axis c = some met.arm ∧ RshIn c
abbrev CutIn (c : Noun) : Prop := slot? cut.axis c = some cut.arm ∧ EndIn c ∧ RshIn c
abbrev CatIn (c : Noun) : Prop :=
  slot? cat.axis c = some cat.arm ∧ LshIn c ∧ MetIn c ∧ Below AddIn c

/-- The noun `x` is a `bite` with bloq `bl` and step `st`. -/
def BiteIs (x : Noun) (bl st : Nat) : Prop := x = C (A bl) (A st) ∨ (x = A bl ∧ st = 1)

theorem BiteIs.cell (bl st : Nat) : BiteIs (C (A bl) (A st)) bl st := Or.inl rfl

theorem BiteIs.atom (bl : Nat) : BiteIs (A bl) bl 1 := Or.inr ⟨rfl, rfl⟩

/-! ## The arms build their gates -/

@[nock_exec] theorem bex_arm (c : Noun) :
    nock c bex.arm = some (C bex.battery (C (A 0) c)) := by
  nock_open bex.arm; simp only [nock_exec]

@[nock_exec] theorem lsh_arm (c : Noun) :
    nock c lsh.arm = some (C lsh.battery (C (C (A 0) (A 0)) c)) := by
  nock_open lsh.arm; simp only [nock_exec]

@[nock_exec] theorem rsh_arm (c : Noun) :
    nock c rsh.arm = some (C rsh.battery (C (C (A 0) (A 0)) c)) := by
  nock_open rsh.arm; simp only [nock_exec]

@[nock_exec] theorem end_arm (c : Noun) :
    nock c end.arm = some (C end.battery (C (C (A 0) (A 0)) c)) := by
  nock_open end.arm; simp only [nock_exec]

@[nock_exec] theorem met_arm (c : Noun) :
    nock c met.arm = some (C met.battery (C (C (A 0) (A 0)) c)) := by
  nock_open met.arm; simp only [nock_exec]

@[nock_exec] theorem cut_arm (c : Noun) :
    nock c cut.arm = some (C cut.battery (C (C (A 0) (C (C (A 1) (A 1)) (A 0))) c)) := by
  nock_open cut.arm; simp only [nock_exec]

@[nock_exec] theorem cat_arm (c : Noun) :
    nock c cat.arm = some (C cat.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open cat.arm; simp only [nock_exec]

/-! ## `+bex` -/

/-- Slamming the `+bex` gate on an atom. -/
theorem bex_gate (c : Noun) (hc : Below MulIn c) : ∀ (a : Nat),
    nock (C bex.battery (C (A a) c)) bex.battery = some (A (2 ^ a)) := by
  obtain ⟨bat, t, rfl, ht⟩ := hc.elim
  intro a
  induction a with
  | zero =>
    nock_open bex.battery
    simp [nock_exec]
  | succ a ih =>
    have h1 : ¬ (0 = a + 1) := by omega
    nock_open bex.battery
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, ht, dec_arm, mul_arm,
      dec_gate t (a + 1) (by omega), Nat.add_sub_cancel, ih, mul_gate t ht.2]
    rw [Nat.pow_succ, Nat.mul_comm]

/-! ## `+lsh`, `+rsh`, `+end` -/

/-- Slamming the `+lsh` gate on a bite and an atom. -/
theorem lsh_gate (c : Noun) (hc : BexIn c) (x : Noun) (bl st b : Nat) (hx : BiteIs x bl st) :
    nock (C lsh.battery (C (C x (A b)) c)) lsh.battery = some (A (b * 2 ^ (2 ^ bl * st))) := by
  have hbex := bex_gate c hc.2
  obtain ⟨hb, hm⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := hm.elim
  rcases hx with rfl | ⟨rfl, rfl⟩
  all_goals
    nock_open lsh.battery
    simp [nock_exec, hb, hbex, ht, mul_arm, bex_arm, mul_gate t ht.2]

/-- Slamming the `+rsh` gate on a bite and an atom. -/
theorem rsh_gate (c : Noun) (hc : RshIn c) (x : Noun) (bl st b : Nat) (hx : BiteIs x bl st) :
    nock (C rsh.battery (C (C x (A b)) c)) rsh.battery = some (A (b / 2 ^ (2 ^ bl * st))) := by
  have hbex := bex_gate c hc.2.1.2
  obtain ⟨_, ⟨hb, hm⟩, hd⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := hm.elim
  have hd : DivIn t := hd
  rcases hx with rfl | ⟨rfl, rfl⟩
  all_goals
    nock_open rsh.battery
    simp [nock_exec, hb, hbex, ht, hd, mul_arm, bex_arm, div_arm, mul_gate t ht.2,
      div_gate t hd.2 _ _ (Nat.two_pow_pos _)]

/-- Slamming the `+end` gate on a bite and an atom. -/
theorem end_gate (c : Noun) (hc : EndIn c) (x : Noun) (bl st b : Nat) (hx : BiteIs x bl st) :
    nock (C end.battery (C (C x (A b)) c)) end.battery = some (A (b % 2 ^ (2 ^ bl * st))) := by
  have hbex := bex_gate c hc.2.1.2
  obtain ⟨_, ⟨hb, hm⟩, hd⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := hm.elim
  have hd : ModIn t := hd
  rcases hx with rfl | ⟨rfl, rfl⟩
  all_goals
    nock_open end.battery
    simp [nock_exec, hb, hbex, ht, hd, mul_arm, bex_arm, mod_arm, mul_gate t ht.2,
      mod_gate t hd.2 _ _ (Nat.two_pow_pos _)]

/-! ## `+met` -/

/-- The number of blocks of `2 ^ a` bits in `b`. -/
def metF (a b : Nat) : Nat :=
  if h : b = 0 then 0 else metF a (b / 2 ^ (2 ^ a)) + 1
termination_by b
decreasing_by
  have : 1 < 2 ^ (2 ^ a) := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos a))
  exact Nat.div_lt_self (by omega) this

theorem metF_zero (a : Nat) : metF a 0 = 0 := by
  rw [metF]; simp

theorem metF_pos (a b : Nat) (h : 0 < b) : metF a b = metF a (b / 2 ^ (2 ^ a)) + 1 := by
  rw [metF]; simp [Nat.pos_iff_ne_zero.mp h]

theorem met_loop (c : Noun) (hc : RshIn c) (a : Nat) : ∀ (b k : Nat),
    nock (C met.loop (C (A k) (C met.battery (C (C (A a) (A b)) c)))) met.loop
      = some (A (k + metF a b)) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro k
    nock_open met.loop
    by_cases hb : b = 0
    · subst hb
      simp [nock_exec, metF_zero]
    · have h1 : ¬ (0 = b) := by omega
      have hlt : b / 2 ^ (2 ^ a) < b := by
        have : 1 < 2 ^ (2 ^ a) := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos a))
        exact Nat.div_lt_self (by omega) this
      have hrsh := rsh_gate c hc (A a) a 1 b (BiteIs.atom a)
      rw [Nat.mul_one] at hrsh
      simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hc, rsh_arm, hrsh, ih _ hlt,
        metF_pos a b (by omega)]
      congr 2
      omega

/-- Slamming the `+met` gate on a bloq and an atom. -/
theorem met_gate (c : Noun) (hc : RshIn c) (a b : Nat) :
    nock (C met.battery (C (C (A a) (A b)) c)) met.battery = some (A (metF a b)) := by
  nock_open met.battery
  simp only [nock_exec, met_loop c hc a b 0, Nat.zero_add]

/-! ## `+cut`, `+cat` -/

/-- Slamming the `+cut` gate on `[a [b c] d]`. -/
theorem cut_gate (c : Noun) (hc : EndIn c ∧ RshIn c) (a b cc d : Nat) :
    nock (C cut.battery (C (C (A a) (C (C (A b) (A cc)) (A d))) c)) cut.battery
      = some (A (d / 2 ^ (2 ^ a * b) % 2 ^ (2 ^ a * cc))) := by
  nock_open cut.battery
  simp only [nock_exec, hc, end_arm, rsh_arm,
    rsh_gate c hc.2 _ a b d (BiteIs.cell a b), end_gate c hc.1 _ a cc _ (BiteIs.cell a cc)]

/-- Slamming the `+cat` gate on `[a b c]`. -/
theorem cat_gate (c : Noun) (hc : LshIn c ∧ MetIn c ∧ Below AddIn c) (a b cc : Nat) :
    nock (C cat.battery (C (C (A a) (C (A b) (A cc))) c)) cat.battery
      = some (A (cc * 2 ^ (2 ^ a * metF a b) + b)) := by
  obtain ⟨hl, hm, ha⟩ := hc
  have hlsh := lsh_gate c hl.2
  have hmet := met_gate c hm.2
  obtain ⟨bat, t, rfl, ht⟩ := ha.elim
  nock_open cat.battery
  simp only [nock_exec, hl, hm, ht, lsh_arm, met_arm, add_arm, hmet,
    hlsh _ a (metF a b) cc (BiteIs.cell a _), add_gate t ht.2]

/-! ## `+mix`, `+dis`, `+con` -/

abbrev LogicNeeds (c : Noun) : Prop := RshIn c ∧ LshIn c ∧ EndIn c ∧ Below AddIn c
abbrev MixIn (c : Noun) : Prop := slot? mix.axis c = some mix.arm ∧ LogicNeeds c
abbrev DisIn (c : Noun) : Prop := slot? dis.axis c = some dis.arm ∧ LogicNeeds c
abbrev ConIn (c : Noun) : Prop := slot? con.axis c = some con.arm ∧ LogicNeeds c

@[nock_exec] theorem mix_arm (c : Noun) :
    nock c mix.arm = some (C mix.battery (C (C (A 0) (A 0)) c)) := by
  nock_open mix.arm; simp only [nock_exec]

@[nock_exec] theorem dis_arm (c : Noun) :
    nock c dis.arm = some (C dis.battery (C (C (A 0) (A 0)) c)) := by
  nock_open dis.arm; simp only [nock_exec]

@[nock_exec] theorem con_arm (c : Noun) :
    nock c con.arm = some (C con.battery (C (C (A 0) (A 0)) c)) := by
  nock_open con.arm; simp only [nock_exec]

theorem mod_two_pow_one (a : Nat) : a % 2 ^ 1 = a % 2 := by simp

theorem xor_split (a b : Nat) : a ^^^ b = 2 * (a / 2 ^^^ b / 2) + (a % 2 ^^^ b % 2) := by
  have h1 := Nat.div_add_mod (a ^^^ b) 2
  have h2 : (a ^^^ b) % 2 = a % 2 ^^^ b % 2 := by
    simpa using @Nat.xor_mod_two_pow a b 1
  rw [Nat.xor_div_two, h2] at h1
  omega

theorem and_split (a b : Nat) : a &&& b = 2 * (a / 2 &&& b / 2) + (a % 2 &&& b % 2) := by
  have h1 := Nat.div_add_mod (a &&& b) 2
  have h2 : (a &&& b) % 2 = a % 2 &&& b % 2 := by
    simpa using @Nat.and_mod_two_pow a b 1
  have h3 : (a &&& b) / 2 = a / 2 &&& b / 2 := by
    simpa using @Nat.and_div_two_pow a b 1
  rw [h3, h2] at h1
  omega

theorem or_split (a b : Nat) : a ||| b = 2 * (a / 2 ||| b / 2) + (a % 2 ||| b % 2) := by
  have h1 := Nat.div_add_mod (a ||| b) 2
  have h2 : (a ||| b) % 2 = a % 2 ||| b % 2 := by
    simpa using @Nat.or_mod_two_pow a b 1
  have h3 : (a ||| b) / 2 = a / 2 ||| b / 2 := by
    simpa using @Nat.or_div_two_pow a b 1
  rw [h3, h2] at h1
  omega

theorem bits_step (d P X bit : Nat) : d + bit * P + P * 2 * X = d + P * (2 * X + bit) := by
  rw [Nat.mul_add, Nat.mul_comm bit P, ← Nat.mul_assoc]
  omega

theorem mix_loop (ctx : Noun) (hc : LogicNeeds ctx) : ∀ (n a b k d : Nat), a + b < n →
    nock (C mix.loop (C (C (A k) (A d)) (C mix.battery (C (C (A a) (A b)) ctx)))) mix.loop
      = some (A (d + 2 ^ k * (a ^^^ b))) := by
  have hrsh := rsh_gate ctx hc.1
  have hlsh := lsh_gate ctx hc.2.1.2
  have hend := end_gate ctx hc.2.2.1
  obtain ⟨hr, hl, he, ha⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := ha.elim
  intro n
  induction n with
  | zero => intro a b k d h; omega
  | succ n ih =>
    intro a b k d h
    nock_open mix.loop
    by_cases h0 : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [nock_exec]
    · have hlt : a / 2 + b / 2 < n := by omega
      have hnz : (¬ 0 = a) ∨ ((0 = a ↔ True) ∧ ¬ 0 = b) := by
        by_cases h1 : a = 0
        · exact Or.inr ⟨by simp [h1], by omega⟩
        · exact Or.inl (by omega)
      rcases Nat.mod_two_eq_zero_or_one a with ma | ma <;>
      rcases Nat.mod_two_eq_zero_or_one b with mb | mb <;>
      rcases hnz with hnz | ⟨hz, hnz⟩
      all_goals first
        | (exfalso; omega)
        | simp [nock_exec, eqCode_atom, hnz, hz, hr, hl, he, ht, rsh_arm, lsh_arm, end_arm, add_arm,
            hrsh _ 0 1 _ (BiteIs.atom 0), hend _ 0 1 _ (BiteIs.atom 0),
            hlsh _ 0 _ _ (BiteIs.cell 0 _), add_gate t ht.2, ma, mb,
            ih (a / 2) (b / 2) (k + 1) _ hlt]
        | simp [nock_exec, eqCode_atom, hnz, hr, hl, he, ht, rsh_arm, lsh_arm, end_arm, add_arm,
            hrsh _ 0 1 _ (BiteIs.atom 0), hend _ 0 1 _ (BiteIs.atom 0),
            hlsh _ 0 _ _ (BiteIs.cell 0 _), add_gate t ht.2, ma, mb,
            ih (a / 2) (b / 2) (k + 1) _ hlt]
      all_goals
        rw [xor_split a b, ma, mb, Nat.pow_succ]
        simp only [Nat.reduceXor, Nat.mul_add, Nat.mul_one, Nat.add_zero, Nat.mul_assoc]
        try omega

/-- Slamming the `+mix` gate on two atoms. -/
theorem mix_gate (c : Noun) (hc : LogicNeeds c) (a b : Nat) :
    nock (C mix.battery (C (C (A a) (A b)) c)) mix.battery = some (A (a ^^^ b)) := by
  nock_open mix.battery
  simp [nock_exec, mix_loop c hc (a + b + 1) a b 0 0 (by omega)]

theorem dis_loop (ctx : Noun) (hc : LogicNeeds ctx) : ∀ (n a b k d : Nat), a + b < n →
    nock (C dis.loop (C (C (A k) (A d)) (C dis.battery (C (C (A a) (A b)) ctx)))) dis.loop
      = some (A (d + 2 ^ k * (a &&& b))) := by
  have hrsh := rsh_gate ctx hc.1
  have hlsh := lsh_gate ctx hc.2.1.2
  have hend := end_gate ctx hc.2.2.1
  obtain ⟨hr, hl, he, ha⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := ha.elim
  intro n
  induction n with
  | zero => intro a b k d h; omega
  | succ n ih =>
    intro a b k d h
    nock_open dis.loop
    by_cases h0 : a = 0
    · subst h0
      simp [nock_exec]
    · have h0' : ¬ 0 = a := by omega
      by_cases h1 : b = 0
      · subst h1
        simp [nock_exec, h0']
      · have h1' : ¬ 0 = b := by omega
        have hlt : a / 2 + b / 2 < n := by omega
        rcases Nat.mod_two_eq_zero_or_one a with ma | ma <;>
        rcases Nat.mod_two_eq_zero_or_one b with mb | mb
        all_goals
          simp [nock_exec, h0', h1', hr, hl, he, ht, rsh_arm, lsh_arm, end_arm, add_arm,
            hrsh _ 0 1 _ (BiteIs.atom 0), hend _ 0 1 _ (BiteIs.atom 0),
            hlsh _ 0 _ _ (BiteIs.cell 0 _), add_gate t ht.2, ma, mb,
            ih (a / 2) (b / 2) (k + 1) _ hlt]
        all_goals
          rw [and_split a b, ma, mb, Nat.pow_succ]
          simp only [Nat.reduceAnd, Nat.mul_add, Nat.mul_one, Nat.add_zero, Nat.mul_assoc]
          try omega

/-- Slamming the `+dis` gate on two atoms. -/
theorem dis_gate (c : Noun) (hc : LogicNeeds c) (a b : Nat) :
    nock (C dis.battery (C (C (A a) (A b)) c)) dis.battery = some (A (a &&& b)) := by
  nock_open dis.battery
  simp [nock_exec, dis_loop c hc (a + b + 1) a b 0 0 (by omega)]

theorem con_loop (ctx : Noun) (hc : LogicNeeds ctx) : ∀ (n a b k d : Nat), a + b < n →
    nock (C con.loop (C (C (A k) (A d)) (C con.battery (C (C (A a) (A b)) ctx)))) con.loop
      = some (A (d + 2 ^ k * (a ||| b))) := by
  have hrsh := rsh_gate ctx hc.1
  have hlsh := lsh_gate ctx hc.2.1.2
  have hend := end_gate ctx hc.2.2.1
  obtain ⟨hr, hl, he, ha⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := ha.elim
  intro n
  induction n with
  | zero => intro a b k d h; omega
  | succ n ih =>
    intro a b k d h
    nock_open con.loop
    by_cases h0 : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [nock_exec]
    · have hlt : a / 2 + b / 2 < n := by omega
      have hnz : (¬ 0 = a) ∨ ((0 = a ↔ True) ∧ ¬ 0 = b) := by
        by_cases h1 : a = 0
        · exact Or.inr ⟨by simp [h1], by omega⟩
        · exact Or.inl (by omega)
      rcases Nat.mod_two_eq_zero_or_one a with ma | ma <;>
      rcases Nat.mod_two_eq_zero_or_one b with mb | mb <;>
      rcases hnz with hnz | ⟨hz, hnz⟩
      all_goals first
        | (exfalso; omega)
        | simp [nock_exec, eqCode_atom, hnz, hz, hr, hl, he, ht, rsh_arm, lsh_arm, end_arm,
            add_arm, hrsh _ 0 1 _ (BiteIs.atom 0), hend _ 0 1 _ (BiteIs.atom 0),
            hlsh _ 0 _ _ (BiteIs.cell 0 _), add_gate t ht.2, ma, mb,
            ih (a / 2) (b / 2) (k + 1) _ hlt]
        | simp [nock_exec, eqCode_atom, hnz, hr, hl, he, ht, rsh_arm, lsh_arm, end_arm,
            add_arm, hrsh _ 0 1 _ (BiteIs.atom 0), hend _ 0 1 _ (BiteIs.atom 0),
            hlsh _ 0 _ _ (BiteIs.cell 0 _), add_gate t ht.2, ma, mb,
            ih (a / 2) (b / 2) (k + 1) _ hlt]
      all_goals
        rw [or_split a b, ma, mb, Nat.pow_succ]
        simp only [Nat.reduceOr, Nat.mul_add, Nat.mul_one, Nat.add_zero, Nat.mul_assoc]
        try omega

/-- Slamming the `+con` gate on two atoms. -/
theorem con_gate (c : Noun) (hc : LogicNeeds c) (a b : Nat) :
    nock (C con.battery (C (C (A a) (A b)) c)) con.battery = some (A (a ||| b)) := by
  nock_open con.battery
  simp [nock_exec, con_loop c hc (a + b + 1) a b 0 0 (by omega)]

/-! ## `+can` -/

/-- `+can`: assemble the list of `[step atom]` pairs, low blocks first. -/
def canF (a : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (p, q) :: r => q % 2 ^ (2 ^ a * p) + canF a r * 2 ^ (2 ^ a * p)

/-- The noun of a pair of atoms. -/
def pairN (x : Nat × Nat) : Noun := C (A x.1) (A x.2)

@[nock_exec] theorem can_arm (c : Noun) :
    nock c can.arm = some (C can.battery (C (C (A 0) (A 0)) c)) := by
  nock_open can.arm; simp only [nock_exec]

/-- Slamming the `+can` gate on a bloq and a list of `[step atom]` pairs. -/
theorem can_gate (c : Noun) (hc : EndIn c ∧ LshIn c ∧ Below AddIn c) (a : Nat) :
    ∀ (l : List (Nat × Nat)),
      nock (C can.battery (C (C (A a) (listN (l.map pairN))) c)) can.battery
        = some (A (canF a l)) := by
  obtain ⟨he, hl, ha⟩ := hc
  have hend := end_gate c he
  have hlsh := lsh_gate c hl.2
  obtain ⟨bat, t, rfl, ht⟩ := ha.elim
  intro l
  induction l with
  | nil =>
    nock_open can.battery
    simp [nock_exec, canF]
  | cons x r ih =>
    obtain ⟨p, q⟩ := x
    nock_open can.battery
    simp [nock_exec, pairN, he, hl, ht, end_arm, lsh_arm, add_arm, ih,
      hend _ a p q (BiteIs.cell a p), hlsh _ a p _ (BiteIs.cell a p), add_gate t ht.2, canF]

end Hoon
end Formalization
