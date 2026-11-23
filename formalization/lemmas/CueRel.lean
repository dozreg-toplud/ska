module

public import core.Cue
public import core.Pill
/-!
# `cue` in pieces

`cue` of `core/Cue.lean` cannot be run by the kernel on the whole pill.  This
file gives a relation `Dec` that says which noun the bits of an atom encode
from one position to another, and proves once that `cue` returns any noun that
`Dec` accepts for the whole atom (`cue_of_dec`).  `Dec` is built from small
pieces: a derivation of `Dec` for a noun is made of derivations for its head
and its tail, so the generated lemmas of `lemmas/Pill/Cue/` can each check a
part of the pill and refer to the parts below it by name.

## The table of back-references

`cueAt` keeps a table of the nouns decoded so far, keyed by the bit where each
starts.  `Dec` does not mention that table.  It is parameterised instead by a
fixed list `KV` of the nouns that are referred to back, in the order in which
their decoding ends, with the bit where each starts: `KV j = (q, n)` says that
the `j`-th noun to be referred to back starts at bit `q` and is `n`.  A
derivation threads a count `i` of the entries of `KV` decoded so far: a noun
whose start and value are `KV i` may move the count to `i + 1`, and a
back-reference may use only an entry below the count.  Any entry that the
derivation does not move past is simply never used, so nothing has to be
checked about the positions that `KV` does not list.

## Reading bits through windows

The token lemmas at the end (`tokA`, `tokC`, `tokR` and the variants that move
the count) read the bits of the atom through a window: a number `W` that
holds the `16384` bits of the atom from bit `o` up (`WinOK`).  Their side
conditions are equations between booleans that the kernel decides with
arithmetic on the window, which is small, instead of on the whole atom.
-/

@[expose] public section

set_option exponentiation.threshold 20000

namespace Formalization
namespace Nock
namespace CueRel

/-! ## The relation -/

/-- `Dec a KV b n e i i'`: the bits of `a` from `b` up to `e` encode `n`, when
the entries of `KV` below `i` have been decoded before `b`; the count of the
entries decoded at the end is `i'`. -/
inductive Dec (a : Nat) (KV : Nat → Nat × Noun) : Nat → Noun → Nat → Nat → Nat → Prop
  /-- An atom. -/
  | atom {b p x i : Nat} : bits a b 1 = 0 → rub a (b + 1) = some (p, x) →
      Dec a KV b (A x) (b + 1 + p) i i
  /-- An atom that is the next entry of the table. -/
  | atomK {b p x i : Nat} : bits a b 1 = 0 → rub a (b + 1) = some (p, x) →
      KV i = (b, A x) → Dec a KV b (A x) (b + 1 + p) i (i + 1)
  /-- A cell: its head, then its tail. -/
  | cell {b e₁ e i i₁ i₂ : Nat} {h t : Noun} : bits a b 1 = 1 → bits a (b + 1) 1 = 0 →
      Dec a KV (b + 2) h e₁ i i₁ → Dec a KV e₁ t e i₁ i₂ → Dec a KV b (C h t) e i i₂
  /-- A cell that is the next entry of the table once its tail is decoded. -/
  | cellK {b e₁ e i i₁ i₂ : Nat} {h t : Noun} : bits a b 1 = 1 → bits a (b + 1) 1 = 0 →
      Dec a KV (b + 2) h e₁ i i₁ → Dec a KV e₁ t e i₁ i₂ → KV i₂ = (b, C h t) →
      Dec a KV b (C h t) e i (i₂ + 1)
  /-- A reference back to an entry of the table decoded before. -/
  | ref {b p q j i : Nat} {n : Noun} : bits a b 1 = 1 → bits a (b + 1) 1 = 1 →
      rub a (b + 2) = some (p, q) → j < i → KV j = (q, n) → Dec a KV b n (b + 2 + p) i i

theorem rub_len {a i p x : Nat} (h : rub a i = some (p, x)) : 1 ≤ p := by
  unfold rub at h
  split at h
  · simp at h
  · simp at h; omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨h, -⟩ := h
    subst h; generalize 2 ^ _ + _ = e; omega

/-- Every noun takes at least two bits. -/
theorem Dec.len {a : Nat} {KV : Nat → Nat × Noun} {b e i i' : Nat} {n : Noun}
    (d : Dec a KV b n e i i') : b + 2 ≤ e := by
  induction d with
  | atom _ hr => have := rub_len hr; omega
  | atomK _ hr _ => have := rub_len hr; omega
  | cell _ _ _ _ ih₁ ih₂ => omega
  | cellK _ _ _ _ _ ih₁ ih₂ => omega
  | ref _ _ hr _ _ => have := rub_len hr; omega

/-- The count only grows, and the entries it moves past start between `b`
and `e`. -/
theorem Dec.keys {a : Nat} {KV : Nat → Nat × Noun} {b e i i' : Nat} {n : Noun}
    (d : Dec a KV b n e i i') :
    i ≤ i' ∧ ∀ j, i ≤ j → j < i' → b ≤ (KV j).1 ∧ (KV j).1 < e := by
  induction d with
  | atom => exact ⟨Nat.le_refl _, fun j h1 h2 => absurd h2 (by omega)⟩
  | @atomK b p x i _ hr hk =>
    have := rub_len hr
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    have : j = i := by omega
    subst this; rw [hk]; simp; omega
  | @cell b e₁ e i i₁ i₂ h t _ _ d₁ d₂ ih₁ ih₂ =>
    have l₁ := d₁.len; have l₂ := d₂.len
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    by_cases hj : j < i₁
    · have := ih₁.2 j h1 hj; omega
    · have := ih₂.2 j (by omega) h2; omega
  | @cellK b e₁ e i i₁ i₂ h t _ _ d₁ d₂ hk ih₁ ih₂ =>
    have l₁ := d₁.len; have l₂ := d₂.len
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    by_cases hj : j < i₁
    · have := ih₁.2 j h1 hj; omega
    · by_cases hj' : j < i₂
      · have := ih₂.2 j (by omega) hj'; omega
      · have : j = i₂ := by omega
        subst this; rw [hk]; simp; omega
  | ref => exact ⟨Nat.le_refl _, fun j h1 h2 => absurd h2 (by omega)⟩

/-- What the table of `cueAt` holds at bit `b` when the count is `i`: every
entry below the count, at its bit, which is below `b`. -/
def Inv (KV : Nat → Nat × Noun) (m : Nat → Option Noun) (b i : Nat) : Prop :=
  ∀ j, j < i → (KV j).1 < b ∧ m (KV j).1 = some (KV j).2

theorem Inv.mono {KV : Nat → Nat × Noun} {m : Nat → Option Noun} {b b' i : Nat}
    (h : Inv KV m b i) (hb : b ≤ b') : Inv KV m b' i :=
  fun j hj => let ⟨h1, h2⟩ := h j hj; ⟨by omega, h2⟩

/-- `cueAt` returns what `Dec` says, given enough fuel and a table that holds
the entries below the count. -/
theorem dec_sound {a : Nat} {KV : Nat → Nat × Noun} {b e i i' : Nat} {n : Noun}
    (d : Dec a KV b n e i i') :
    ∀ (fuel : Nat) (m : Nat → Option Noun), e - b ≤ fuel → Inv KV m b i →
      ∃ m', cueAt a fuel b m = some (e - b, n, m') ∧ Inv KV m' e i' := by
  induction d with
  | @atom b p x i h0 hr =>
    intro fuel m hf hm
    have := rub_len hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨put m b (A x), ?_, ?_⟩
    · simp only [cueAt, h0, if_true, hr]
      congr 2; omega
    · intro j hj
      have ⟨h1, h2⟩ := hm j hj
      refine ⟨by omega, ?_⟩
      simp only [put]; rw [if_neg (by omega)]; exact h2
  | @atomK b p x i h0 hr hk =>
    intro fuel m hf hm
    have := rub_len hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨put m b (A x), ?_, ?_⟩
    · simp only [cueAt, h0, if_true, hr]
      congr 2; omega
    · intro j hj
      by_cases hji : j < i
      · have ⟨h1, h2⟩ := hm j hji
        refine ⟨by omega, ?_⟩
        simp only [put]; rw [if_neg (by omega)]; exact h2
      · have : j = i := by omega
        subst this; rw [hk]; simp [put]; omega
  | @cell b e₁ e i i₁ i₂ h t h0 h1 d₁ d₂ ih₁ ih₂ =>
    intro fuel m hf hm
    have l₁ := d₁.len; have l₂ := d₂.len
    have k₁ := d₁.keys; have k₂ := d₂.keys
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨m₁, c₁, hm₁⟩ := ih₁ f m (by omega) (hm.mono (by omega))
    obtain ⟨m₂, c₂, hm₂⟩ := ih₂ f m₁ (by omega) hm₁
    refine ⟨put m₂ b (C h t), ?_, ?_⟩
    · have hb : b + 2 + (e₁ - (b + 2)) = e₁ := by omega
      simp only [cueAt, h0, h1, c₁, hb, c₂]
      simp only [Nat.one_ne_zero, if_false, if_true]
      congr 2; omega
    · intro j hj
      have ⟨hp, hv⟩ := hm₂ j hj
      refine ⟨hp, ?_⟩
      have hne : (KV j).1 ≠ b := by
        by_cases a1 : j < i
        · have := (hm j a1).1; omega
        · by_cases a2 : j < i₁
          · have := k₁.2 j (by omega) a2; omega
          · have := k₂.2 j (by omega) hj; omega
      simp only [put]; rw [if_neg hne]; exact hv
  | @cellK b e₁ e i i₁ i₂ h t h0 h1 d₁ d₂ hk ih₁ ih₂ =>
    intro fuel m hf hm
    have l₁ := d₁.len; have l₂ := d₂.len
    have k₁ := d₁.keys; have k₂ := d₂.keys
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨m₁, c₁, hm₁⟩ := ih₁ f m (by omega) (hm.mono (by omega))
    obtain ⟨m₂, c₂, hm₂⟩ := ih₂ f m₁ (by omega) hm₁
    refine ⟨put m₂ b (C h t), ?_, ?_⟩
    · have hb : b + 2 + (e₁ - (b + 2)) = e₁ := by omega
      simp only [cueAt, h0, h1, c₁, hb, c₂]
      simp only [Nat.one_ne_zero, if_false, if_true]
      congr 2; omega
    · intro j hj
      by_cases hj2 : j < i₂
      · have ⟨hp, hv⟩ := hm₂ j hj2
        refine ⟨hp, ?_⟩
        have hne : (KV j).1 ≠ b := by
          by_cases a1 : j < i
          · have := (hm j a1).1; omega
          · by_cases a2 : j < i₁
            · have := k₁.2 j (by omega) a2; omega
            · have := k₂.2 j (by omega) hj2; omega
        simp only [put]; rw [if_neg hne]; exact hv
      · have : j = i₂ := by omega
        subst this; rw [hk]; simp [put]; omega
  | @ref b p q j i n h0 h1 hr hj hk =>
    intro fuel m hf hm
    have := rub_len hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hq := (hm j hj).2
    rw [hk] at hq
    refine ⟨m, ?_, hm.mono (by omega)⟩
    simp only [cueAt, h0, h1, hr, hq]
    simp only [Nat.one_ne_zero, if_false]
    congr 2; omega

/-! ## Bits -/

theorem bits_testBit (x s n k : Nat) :
    (bits x s n).testBit k = (decide (k < n) && x.testBit (s + k)) := by
  simp [bits, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

/-- The bits of a run of bits are bits of the atom. -/
theorem bits_bits {x s n j m : Nat} (h : j + m ≤ n) :
    bits (bits x s n) j m = bits x (s + j) m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [bits_testBit, bits_testBit, bits_testBit]
  by_cases hk : k < m
  · have : j + k < n := by omega
    simp [hk, this, Nat.add_assoc]
  · simp [hk]

theorem bits_one (x i : Nat) : bits x i 1 = if x.testBit i then 1 else 0 := by
  have h2 : bits x i 1 < 2 := by unfold bits; exact Nat.mod_lt _ (by decide)
  have ht := bits_testBit x i 1 0
  simp at ht
  rcases Nat.lt_two_iff.mp h2 with h | h <;> rw [h] at ht ⊢ <;> simp at ht <;> simp [← ht]
  where Nat.lt_two_iff {n : Nat} : n < 2 ↔ n = 0 ∨ n = 1 := by omega

theorem le_log2_of_bit {a k : Nat} (h : bits a k 1 = 1) : k ≤ a.log2 := by
  rw [bits_one] at h
  split at h
  · rename_i ht
    have hge : 2 ^ k ≤ a := Nat.ge_two_pow_of_testBit ht
    have ha : a ≠ 0 := by intro h0; subst h0; simp at ht
    exact (Nat.le_log2 ha).mpr hge
  · simp at h

/-- `bits x s (z + 1) = 2 ^ z`: `z` zero bits from `s`, then a one. -/
theorem bits_pow {x s z : Nat} (h : bits x s (z + 1) = 2 ^ z) :
    (∀ j, j < z → bits x (s + j) 1 = 0) ∧ bits x (s + z) 1 = 1 := by
  constructor
  · intro j hj
    rw [← bits_bits (n := z + 1) (by omega), h, bits_one, Nat.testBit_two_pow]
    simp; omega
  · rw [← bits_bits (n := z + 1) (by omega), h, bits_one, Nat.testBit_two_pow]
    simp

theorem zeros_of {a : Nat} : ∀ {z i fuel : Nat}, (∀ j, j < z → bits a (i + j) 1 = 0) →
    bits a (i + z) 1 = 1 → z < fuel → zeros a i fuel = some z
  | 0, i, fuel + 1, _, h1, _ => by simp only [Nat.add_zero] at h1; simp [zeros, h1]
  | z + 1, i, fuel + 1, h0, h1, hf => by
    have hi : bits a i 1 = 0 := by simpa using h0 0 (by omega)
    have ih := zeros_of (z := z) (i := i + 1) (fuel := fuel)
      (fun j hj => by rw [Nat.add_assoc, Nat.add_comm 1 j]; exact h0 (j + 1) (by omega))
      (by rw [Nat.add_assoc, Nat.add_comm 1 z]; exact h1) (by omega)
    simp [zeros, hi, ih]
  | _, _, 0, _, _, hf => absurd hf (Nat.not_lt_zero _)

/-! ## Windows -/

/-- `W` holds the bits of `a` from `o` up to `o + 16384`: two chunks of the
pill file. -/
def WinOK (a W o : Nat) : Prop :=
  ∀ i n, o ≤ i → i + n ≤ o + 16384 → bits a i n = bits W (i - o) n

theorem winOK_of_bits {a W o : Nat} (h : bits a o 16384 = W) : WinOK a W o := by
  intro i n h1 h2
  rw [← h, bits_bits (by omega)]
  congr 1; omega

theorem glue_split : ∀ (L : List Nat) (k : Nat),
    glue L = glue (L.take k) + 2 ^ (8192 * k) * glue (L.drop k)
  | [], k => by simp [glue]
  | c :: L, 0 => by simp [glue]
  | c :: L, k + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, glue]
    rw [glue_split L k, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
    have : 8192 + 8192 * k = 8192 * (k + 1) := by omega
    rw [this]; omega

theorem glue_lt : ∀ (L : List Nat), (∀ c ∈ L, c < 2 ^ 8192) →
    glue L < 2 ^ (8192 * L.length)
  | [], _ => by simp [glue]
  | c :: L, h => by
    simp only [glue, List.length_cons]
    have hc := h c (by simp)
    have ih := glue_lt L (fun c' hc' => h c' (by simp [hc']))
    have : 8192 * (L.length + 1) = 8192 + 8192 * L.length := by omega
    rw [this, Nat.pow_add]
    have : 2 ^ 8192 * glue L + 2 ^ 8192 ≤ 2 ^ 8192 * 2 ^ (8192 * L.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    omega

theorem glue_low {L : List Nat} (hL : ∀ c ∈ L, c < 2 ^ 8192) (k : Nat) :
    glue (L.take k) < 2 ^ (8192 * k) := by
  have := glue_lt (L.take k) (fun c hc => hL c (List.mem_of_mem_take hc))
  have hl : (L.take k).length ≤ k := by simp [Nat.min_le_left]
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))

/-- The window of chunks `k` and `k + 1` of a glued atom. -/
theorem bits_glue {L : List Nat} (hL : ∀ c ∈ L, c < 2 ^ 8192) (k : Nat) :
    bits (glue L) (8192 * k) 16384 = glue ((L.drop k).take 2) := by
  unfold bits
  rw [Nat.shiftRight_eq_div_pow, glue_split L k,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (glue_low hL k), Nat.zero_add]
  have hM : ∀ c ∈ L.drop k, c < 2 ^ 8192 := fun c hc => hL c (List.mem_of_mem_drop hc)
  rw [glue_split (L.drop k) 2, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (glue_low hM 2)

theorem winOK_glue {L : List Nat} (hL : ∀ c ∈ L, c < 2 ^ 8192) (k W : Nat)
    (h : glue ((L.drop k).take 2) = W) : WinOK (glue L) W (8192 * k) :=
  winOK_of_bits ((bits_glue hL k).trans h)

/-! ## Length-prefixed atoms through a window

The checks are written with `Nat.beq`, `Nat.ble`, `Nat.add`, `Nat.shiftRight`
and the like, which the kernel computes on literals directly, rather than with
the notation, whose instances it would have to unfold first. -/

/-- `bits`, written with the functions that the kernel computes on literals. -/
def bitsK (w i n : Nat) : Nat := Nat.mod (Nat.shiftRight w i) (Nat.pow 2 n)

theorem bitsK_eq (w i n : Nat) : bitsK w i n = bits w i n := rfl

/-- The length-prefixed atom at bit `s` of `W` has `z` leading zeros, takes
`p` bits and is `x`. -/
def matOK (W s z p x : Nat) : Bool :=
  cond (Nat.beq z 0)
    (Nat.beq (bitsK W s 1) 1 && Nat.beq p 1 && Nat.beq x 0)
    (Nat.beq (bitsK W s (Nat.add z 1)) (Nat.pow 2 z) &&
      Nat.beq p (Nat.add (Nat.mul 2 z)
        (Nat.add (Nat.pow 2 (Nat.sub z 1)) (bitsK W (Nat.add (Nat.add s z) 1) (Nat.sub z 1)))) &&
      Nat.beq x (bitsK W (Nat.add s (Nat.mul 2 z))
        (Nat.add (Nat.pow 2 (Nat.sub z 1)) (bitsK W (Nat.add (Nat.add s z) 1) (Nat.sub z 1)))))

theorem matOK_cases {W s z p x : Nat} (h : matOK W s z p x = true) :
    (z = 0 ∧ bits W s 1 = 1 ∧ p = 1 ∧ x = 0) ∨
    (∃ c, z = c + 1 ∧ bits W s (c + 2) = 2 ^ (c + 1) ∧
      p = 2 * (c + 1) + (2 ^ c + bits W (s + (c + 1) + 1) c) ∧
      x = bits W (s + 2 * (c + 1)) (2 ^ c + bits W (s + (c + 1) + 1) c)) := by
  unfold matOK at h
  cases hz : Nat.beq z 0 with
  | true =>
    rw [hz] at h
    simp only [cond_true, Bool.and_eq_true, Nat.beq_eq, bitsK_eq] at h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hz, h.1.1, h.1.2, h.2⟩
  | false =>
    rw [hz] at h
    have hz' := Nat.ne_of_beq_eq_false hz
    obtain ⟨c, rfl⟩ : ∃ c, z = c + 1 := ⟨z - 1, by omega⟩
    simp only [cond_false, Bool.and_eq_true, Nat.beq_eq, bitsK_eq, Nat.add_eq, Nat.mul_eq,
      Nat.sub_eq, Nat.pow_eq, Nat.add_sub_cancel] at h
    exact Or.inr ⟨c, rfl, h.1.1, h.1.2, h.2⟩

theorem matOK_len {W s z p x : Nat} (h : matOK W s z p x = true) : 1 ≤ p := by
  rcases matOK_cases h with ⟨_, _, rfl, _⟩ | ⟨c, _, _, rfl, _⟩
  · exact Nat.le_refl 1
  · generalize 2 ^ c + _ = e; omega

theorem rub_win {a W o s z p x : Nat} (hW : WinOK a W o) (h : matOK W s z p x = true)
    (hs : s + p ≤ 16384) : rub a (o + s) = some (p, x) := by
  rcases matOK_cases h with ⟨rfl, h1, rfl, rfl⟩ | ⟨c, rfl, h1, hp, hx⟩
  · have ha : bits a (o + s) 1 = 1 := by
      rw [hW (o + s) 1 (by omega) (by omega)]; simpa using h1
    have hz := zeros_of (a := a) (z := 0) (i := o + s) (fuel := a.log2 + 2)
      (fun j hj => absurd hj (by omega)) (by simpa using ha) (by omega)
    simp [rub, hz]
  · have hlen : bits W (s + (c + 1) + 1) c = bits a (o + s + (c + 1) + 1) c := by
      rw [hW (o + s + (c + 1) + 1) c (by omega) (by omega)]; congr 1; omega
    have hpow : bits a (o + s) (c + 1 + 1) = 2 ^ (c + 1) := by
      rw [hW (o + s) _ (by omega) (by omega)]; simpa using h1
    obtain ⟨hz0, hz1⟩ := bits_pow hpow
    have hlog := le_log2_of_bit hz1
    have hzeros := zeros_of hz0 hz1 (fuel := a.log2 + 2) (by omega)
    simp only [rub, hzeros]
    rw [← hlen]
    have hval : bits W (s + 2 * (c + 1)) (2 ^ c + bits W (s + (c + 1) + 1) c) =
        bits a (o + s + (c + 1) + 1 + c) (2 ^ c + bits W (s + (c + 1) + 1) c) := by
      rw [hW (o + s + (c + 1) + 1 + c) _ (by omega) (by omega)]; congr 1; omega
    rw [hx, hval, hp]
    congr 2; omega

/-! ## Tokens through a window

Each lemma checks one token of the jam with a boolean that the kernel
evaluates on the window, and assembles the step of `Dec`. -/

/-- An atom from `b` to `e`. -/
theorem tokA {a : Nat} {KV : Nat → Nat × Noun} (W o b z p x e i : Nat) (hW : WinOK a W o)
    (h : (Nat.ble o b && Nat.ble e (Nat.add o 16384) && Nat.beq (bitsK W (Nat.sub b o) 1) 0 &&
      matOK W (Nat.add (Nat.sub b o) 1) z p x && Nat.beq e (Nat.add (Nat.add b 1) p)) = true) :
    Dec a KV b (A x) e i i := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq, bitsK_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩ := h
  have := matOK_len h4
  have hb : bits a b 1 = 0 := by rw [hW b 1 h1 (by omega)]; exact h3
  have hr := rub_win hW h4 (by omega)
  rw [show o + (b - o + 1) = b + 1 by omega] at hr
  exact Dec.atom hb hr

/-- An atom from `b` to `e` that is the entry `i` of the table. -/
theorem tokAK {a : Nat} {KV : Nat → Nat × Noun} (W o b z p x e i i' : Nat) (hW : WinOK a W o)
    (h : (Nat.ble o b && Nat.ble e (Nat.add o 16384) && Nat.beq (bitsK W (Nat.sub b o) 1) 0 &&
      matOK W (Nat.add (Nat.sub b o) 1) z p x && Nat.beq e (Nat.add (Nat.add b 1) p) &&
      Nat.beq i' (Nat.add i 1)) = true)
    (hk : KV i = (b, A x)) :
    Dec a KV b (A x) e i i' := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq, bitsK_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩, rfl⟩ := h
  have := matOK_len h4
  have hb : bits a b 1 = 0 := by rw [hW b 1 h1 (by omega)]; exact h3
  have hr := rub_win hW h4 (by omega)
  rw [show o + (b - o + 1) = b + 1 by omega] at hr
  exact Dec.atomK hb hr hk

theorem cell_bits {a W o b : Nat} (hW : WinOK a W o) (h1 : o ≤ b) (h2 : b + 2 ≤ o + 16384)
    (h : bits W (b - o) 2 = 1) : bits a b 1 = 1 ∧ bits a (b + 1) 1 = 0 := by
  have h' : bits a b 2 = 1 := by rw [hW b 2 h1 h2]; exact h
  constructor
  · rw [← Nat.add_zero b, ← bits_bits (n := 2) (by omega), h']; decide
  · rw [← bits_bits (n := 2) (by omega), h']; decide

/-- A cell from `b` to `e`, whose head starts at `b₂ = b + 2`. -/
theorem tokC {a : Nat} {KV : Nat → Nat × Noun} (W o b b₂ e₁ e i i₁ i₂ : Nat) (hd tl : Noun)
    (hW : WinOK a W o)
    (h : (Nat.ble o b && Nat.ble (Nat.add b 2) (Nat.add o 16384) &&
      Nat.beq (bitsK W (Nat.sub b o) 2) 1 && Nat.beq b₂ (Nat.add b 2)) = true)
    (d₁ : Dec a KV b₂ hd e₁ i i₁) (d₂ : Dec a KV e₁ tl e i₁ i₂) :
    Dec a KV b (C hd tl) e i i₂ := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq, bitsK_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩ := h
  obtain ⟨c1, c2⟩ := cell_bits hW h1 h2 h3
  exact Dec.cell c1 c2 d₁ d₂

/-- A cell from `b` to `e` that is the entry `i₂` of the table. -/
theorem tokCK {a : Nat} {KV : Nat → Nat × Noun} (W o b b₂ e₁ e i i₁ i₂ i₃ : Nat)
    (hd tl : Noun) (hW : WinOK a W o)
    (h : (Nat.ble o b && Nat.ble (Nat.add b 2) (Nat.add o 16384) &&
      Nat.beq (bitsK W (Nat.sub b o) 2) 1 && Nat.beq b₂ (Nat.add b 2) &&
      Nat.beq i₃ (Nat.add i₂ 1)) = true)
    (d₁ : Dec a KV b₂ hd e₁ i i₁) (d₂ : Dec a KV e₁ tl e i₁ i₂) (hk : KV i₂ = (b, C hd tl)) :
    Dec a KV b (C hd tl) e i i₃ := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq, bitsK_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩, rfl⟩ := h
  obtain ⟨c1, c2⟩ := cell_bits hW h1 h2 h3
  exact Dec.cellK c1 c2 d₁ d₂ hk

/-- A reference from `b` to `e` back to the entry `j` of the table. -/
theorem tokR {a : Nat} {KV : Nat → Nat × Noun} (W o b z p q e j i : Nat) (n : Noun)
    (hW : WinOK a W o)
    (h : (Nat.ble o b && Nat.ble e (Nat.add o 16384) && Nat.beq (bitsK W (Nat.sub b o) 2) 3 &&
      matOK W (Nat.add (Nat.sub b o) 2) z p q && Nat.beq e (Nat.add (Nat.add b 2) p) &&
      Nat.ble (Nat.add j 1) i) = true)
    (hk : KV j = (q, n)) :
    Dec a KV b n e i i := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.sub_eq, bitsK_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩, h5⟩ := h
  have := matOK_len h4
  have h' : bits a b 2 = 3 := by rw [hW b 2 h1 (by omega)]; exact h3
  have c1 : bits a b 1 = 1 := by
    rw [← Nat.add_zero b, ← bits_bits (n := 2) (by omega), h']; decide
  have c2 : bits a (b + 1) 1 = 1 := by
    rw [← bits_bits (n := 2) (by omega), h']; decide
  have hr := rub_win hW h4 (by omega)
  rw [show o + (b - o + 2) = b + 2 by omega] at hr
  exact Dec.ref c1 c2 hr (by omega) hk

/-! ## The whole atom -/

/-- `cue` returns the noun of a derivation that starts at bit `0` with an
empty count and ends on a one bit. -/
theorem cue_of_dec {a : Nat} {KV : Nat → Nat × Noun} {n : Noun} {E i : Nat}
    (d : Dec a KV 0 n E 0 i) (hE : bits a (E - 1) 1 = 1) : cue a = some n := by
  have hl := d.len
  have hlog := le_log2_of_bit hE
  obtain ⟨m', hc, -⟩ := dec_sound d (a.log2 + 2) (fun _ => none) (by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero _))
  simp [cue, hc]

end CueRel
end Nock
end Formalization
