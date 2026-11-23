import lemmas.Ska.CompSim

/-!
# The block relation of `+comp` through cons, `%3`, `%4` and `%5`

Composition rules for `CompRel` (from `CompSim.lean`), each for the blocks
that the case of `run` in `+comp` emits, read from the Hoon:

* `compRel_cons_next`: `[p q]` for the goal `%next` with a pair need: `p`
  runs first into the head's registers and goes on in `q`'s block, which
  puts its product in the tail's registers (the `%next` branch of the case
  `[^ *]`: `p` with the goal into `then.nex-2`, `q`'s code).
  `compRel_done_of_con`: `%done` from that, through a block
  `[%con h t r] [%don r]`.
* `compRel_n4_done`: `[4 p]` for `%done`: a block `[%inc arg pro] [%don pro]`
  and `p` for `%next` into `this+arg`.
* `compRel_n3_pick`: `[3 p]` for `%pick`: a block `[%clq r z o]` and `p`
  for `%next` into `this+r`.
* `compRel_n5_pick`: `[5 p q]` for `%pick`: a block `[%eqq r-p r-q z o]`,
  `q` for `%next` into `this+r-q`, and `p` before it into `this+r-p`.
* `compRel_done_of_pick`: `%done` from `%pick` into the two blocks
  `[%imm 0 r-0] [%don r-0]` and `[%imm 1 r-1] [%don r-1]`, which the cases
  `%3` and `%5` emit for `%done`, for a nomm whose value is a loobean.

What is modelled is the shape of the blocks each case emits, from the Hoon;
what is assumed is that the needs (`RNeed`) are what `+split`, `+past` and
`+copy` resolve the lazy needs to, and the registers kept (`keep`), which
is what the fresh registers of `re` give.
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel

open Nock

section
variable {Map : Type → Type} [HoonMap Map]

/-- **`[p q]` for the goal `%next` with a pair need**: `p` puts its product
in the head's registers and goes on in the block `kq` of `q`, keeping the
subject's registers; `q` puts its product in the tail's registers and goes
on in `k`, keeping the head's. -/
theorem compRel_cons_next {lib : Lib} {c : Straight Map} {p q : Nomm} {bp bq : Blob}
    {nd ndh ndt : RNeed} {K Kp Kq : Nat → Prop} {kq k : Nat} (hkq : HoonMap.get c.blocks kq = some bq)
    (hp : CompRel lib c p (Goal.next ndh kq) bp nd Kp) (hq : CompRel lib c q (Goal.next ndt k) bq nd Kq)
    (hK : ∀ r, K r → Kp r ∧ Kq r) (hnd : ∀ r, nd.Mem r → Kp r) (hh : ∀ r, ndh.Mem r → Kq r) :
    CompRel lib c (Nomm.cons p q) (Goal.next (RNeed.pair ndh ndt) k) bp nd K := by
  intro σ O st s regs t gul hs
  have Hp := hp σ O st s regs t gul hs
  simp only [pureEval]
  cases e : pureEval p s with
  | none =>
    rw [e] at Hp
    exact goalRel_crash _ Hp
  | some a =>
    rw [e] at Hp
    obtain ⟨regs1, bk, hbk, hh1, hk1, he1⟩ := Hp
    rw [hkq] at hbk; cases hbk
    have Hq := hq σ O st s regs1 t gul (Holds.agree nd (fun x hx => hk1 x (hnd x hx)) hs)
    simp only [Option.bind_some]
    cases e2 : pureEval q s with
    | none =>
      rw [e2] at Hq
      simp only [GoalRel] at Hq ⊢
      rw [he1]; exact Hq
    | some b =>
      rw [e2] at Hq
      obtain ⟨regs2, bk2, hbk2, hh2, hk2, he2⟩ := Hq
      simp only [Option.bind_some, GoalRel]
      exact ⟨regs2, bk2, hbk2, ⟨Holds.agree ndh (fun x hx => hk2 x (hh x hx)) hh1, hh2⟩,
        fun r hr => (hk2 r (hK r hr).2).trans (hk1 r (hK r hr).1), he1.trans he2⟩

/-- **`%done` from `%next` with a pair need of two registers**, into a
block that conses them into a register and returns it. -/
theorem compRel_done_of_con {lib : Lib} {c : Straight Map} {nm : Nomm} {b : Blob} {nd : RNeed}
    {K : Nat → Prop} {h tr r k : Nat}
    (hk : HoonMap.get c.blocks k = some ⟨[], [Pole.con h tr r], Termin.don r⟩)
    (hrel : CompRel lib c nm (Goal.next (RNeed.pair (RNeed.this h) (RNeed.this tr)) k) b nd K)
    (hcell : ∀ s v, pureEval nm s = some v → ∃ x y, v = C x y) :
    CompRel lib c nm Goal.done b nd K := by
  intro σ O st s regs t gul hs
  have H := hrel σ O st s regs t gul hs
  cases e : pureEval nm s with
  | none => rw [e] at H; exact goalRel_crash _ H
  | some v =>
    rw [e] at H
    obtain ⟨x, y, rfl⟩ := hcell s _ e
    obtain ⟨regs', bk, hbk, hh, _, he⟩ := H
    rw [hk] at hbk; cases hbk
    simp only [Holds, SkaModel.read] at hh
    simp only [GoalRel, toneOf]
    rw [he, execBlob_body]
    simp [execPole, localPole, hh.1, hh.2, execBlob_don, store, SkaModel.read, HoonMap.get_put]

/-- **`[4 p]` for `%done`.** -/
theorem compRel_n4_done {lib : Lib} {c : Straight Map} {p : Nomm} {bp : Blob} {nd : RNeed}
    {K Kp : Nat → Prop} {arg pro o : Nat}
    (ho : HoonMap.get c.blocks o = some ⟨[], [Pole.inc arg pro], Termin.don pro⟩)
    (hp : CompRel lib c p (Goal.next (RNeed.this arg) o) bp nd Kp) :
    CompRel lib c (Nomm.n4 p) Goal.done bp nd K := by
  intro σ O st s regs t gul hs
  have Hp := hp σ O st s regs t gul hs
  simp only [pureEval]
  cases e : pureEval p s with
  | none => rw [e] at Hp; exact goalRel_crash _ Hp
  | some x =>
    rw [e] at Hp
    obtain ⟨regs', bk, hbk, hh, _, he⟩ := Hp
    rw [ho] at hbk; cases hbk
    simp only [Holds, SkaModel.read] at hh
    simp only [GoalRel, Option.bind_some]
    rw [he, execBlob_body]
    cases x with
    | atom a => simp [execPole, localPole, hh, execBlob_don, store, SkaModel.read, HoonMap.get_put, toneOf]
    | cell a b => simp [execPole, localPole, SkaModel.read, hh, toneOf]

/-- **`[3 p]` for `%pick`**: `p` into a register that `[%clq r z o]` tests;
`[3 p]` is `0` on a cell. -/
theorem compRel_n3_pick {lib : Lib} {c : Straight Map} {p : Nomm} {bp bz bo : Blob} {nd : RNeed}
    {K Kp : Nat → Prop} {r o z o' : Nat}
    (ho : HoonMap.get c.blocks o = some ⟨[], [], Termin.clq r ⟨[], z⟩ ⟨[], o'⟩⟩)
    (hz : HoonMap.get c.blocks z = some bz) (ho' : HoonMap.get c.blocks o' = some bo)
    (hp : CompRel lib c p (Goal.next (RNeed.this r) o) bp nd Kp) (hK : ∀ x, K x → Kp x) :
    CompRel lib c (Nomm.n3 p) (Goal.pick z o') bp nd K := by
  intro σ O st s regs t gul hs
  have Hp := hp σ O st s regs t gul hs
  simp only [pureEval]
  cases e : pureEval p s with
  | none => rw [e] at Hp; exact goalRel_crash _ Hp
  | some x =>
    rw [e] at Hp
    obtain ⟨regs', bk, hbk, hh, hk, he⟩ := Hp
    rw [ho] at hbk; cases hbk
    simp only [Holds, SkaModel.read] at hh
    simp only [Option.bind_some]
    cases x with
    | atom a =>
      refine ⟨regs', bo, ho', fun x hx => hk x (hK x hx), ?_⟩
      rw [he, execBlob]; simp [SkaModel.read, hh, ho']
    | cell a b =>
      refine ⟨regs', bz, hz, fun x hx => hk x (hK x hx), ?_⟩
      rw [he, execBlob]; simp [SkaModel.read, hh, hz]

/-- **`[5 p q]` for `%pick`**: `p` into `r-p` and on to `q`'s block, `q`
into `r-q` and on to the block `[%eqq r-p r-q z o]`; `q` keeps `r-p`. -/
theorem compRel_n5_pick {lib : Lib} {c : Straight Map} {p q : Nomm} {bp bq bz bo : Blob}
    {nd : RNeed} {K Kp Kq : Nat → Prop} {rp rq o kq z o' : Nat}
    (ho : HoonMap.get c.blocks o = some ⟨[], [], Termin.eqq rp rq ⟨[], z⟩ ⟨[], o'⟩⟩)
    (hkq : HoonMap.get c.blocks kq = some bq)
    (hz : HoonMap.get c.blocks z = some bz) (ho' : HoonMap.get c.blocks o' = some bo)
    (hp : CompRel lib c p (Goal.next (RNeed.this rp) kq) bp nd Kp)
    (hq : CompRel lib c q (Goal.next (RNeed.this rq) o) bq nd Kq)
    (hK : ∀ x, K x → Kp x ∧ Kq x) (hnd : ∀ x, nd.Mem x → Kp x) (hrp : Kq rp) :
    CompRel lib c (Nomm.n5 p q) (Goal.pick z o') bp nd K := by
  intro σ O st s regs t gul hs
  have Hp := hp σ O st s regs t gul hs
  simp only [pureEval]
  cases e : pureEval p s with
  | none => rw [e] at Hp; exact goalRel_crash _ Hp
  | some x =>
    rw [e] at Hp
    obtain ⟨regs1, bk, hbk, hh1, hk1, he1⟩ := Hp
    rw [hkq] at hbk; cases hbk
    have Hq := hq σ O st s regs1 t gul (Holds.agree nd (fun x hx => hk1 x (hnd x hx)) hs)
    simp only [Option.bind_some]
    cases e2 : pureEval q s with
    | none =>
      rw [e2] at Hq
      simp only [GoalRel] at Hq ⊢
      rw [he1]; exact Hq
    | some y =>
      rw [e2] at Hq
      obtain ⟨regs2, bk2, hbk2, hh2, hk2, he2⟩ := Hq
      rw [ho] at hbk2; cases hbk2
      simp only [Holds, SkaModel.read] at hh1 hh2
      have hx : HoonMap.get regs2 rp = some x := by
        have := hk2 rp hrp; simp only [SkaModel.read] at this; rw [this]; exact hh1
      simp only [Option.bind_some, eqCode]
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true]
        refine ⟨regs2, bz, hz, fun r hr => (hk2 r (hK r hr).2).trans (hk1 r (hK r hr).1), ?_⟩
        rw [he1, he2, execBlob]; simp [SkaModel.read, hx, hh2, hz]
      · simp only [if_neg hxy]
        refine ⟨regs2, bo, ho', fun r hr => (hk2 r (hK r hr).2).trans (hk1 r (hK r hr).1), ?_⟩
        rw [he1, he2, execBlob]; simp [SkaModel.read, hx, hh2, ho', hxy]

/-- **`%done` from `%pick`** into the blocks that return `0` and `1`, for a
nomm whose value is a loobean (`[3 p]`, `[5 p q]`). -/
theorem compRel_done_of_pick {lib : Lib} {c : Straight Map} {nm : Nomm} {b : Blob} {nd : RNeed}
    {K : Nat → Prop} {z o r0 r1 : Nat}
    (h0 : HoonMap.get c.blocks z = some ⟨[], [Pole.imm (A 0) r0], Termin.don r0⟩)
    (h1 : HoonMap.get c.blocks o = some ⟨[], [Pole.imm (A 1) r1], Termin.don r1⟩)
    (hrel : CompRel lib c nm (Goal.pick z o) b nd K)
    (hloob : ∀ s v, pureEval nm s = some v → v = A 0 ∨ v = A 1) :
    CompRel lib c nm Goal.done b nd K := by
  intro σ O st s regs t gul hs
  have H := hrel σ O st s regs t gul hs
  cases e : pureEval nm s with
  | none => rw [e] at H; exact goalRel_crash _ H
  | some v =>
    rw [e] at H
    simp only [GoalRel, toneOf]
    rcases hloob s v e with rfl | rfl
    · obtain ⟨regs', bk, hbk, _, he⟩ := H
      rw [h0] at hbk; cases hbk
      rw [he, execBlob_body]
      simp [execPole_imm, execBlob_don, store, SkaModel.read, HoonMap.get_put]
    · obtain ⟨regs', bk, hbk, _, he⟩ := H
      rw [h1] at hbk; cases hbk
      rw [he, execBlob_body]
      simp [execPole_imm, execBlob_don, store, SkaModel.read, HoonMap.get_put]

/-- **`[3 p]` for `%done`**, as the case `%3` emits it: the two blocks that
return `0` and `1`, the `%clq` block, and `p` into its register. -/
theorem compRel_n3_done {lib : Lib} {c : Straight Map} {p : Nomm} {bp : Blob} {nd : RNeed}
    {K Kp : Nat → Prop} {r o z o' r0 r1 : Nat}
    (h0 : HoonMap.get c.blocks z = some ⟨[], [Pole.imm (A 0) r0], Termin.don r0⟩)
    (h1 : HoonMap.get c.blocks o' = some ⟨[], [Pole.imm (A 1) r1], Termin.don r1⟩)
    (ho : HoonMap.get c.blocks o = some ⟨[], [], Termin.clq r ⟨[], z⟩ ⟨[], o'⟩⟩)
    (hp : CompRel lib c p (Goal.next (RNeed.this r) o) bp nd Kp) (hK : ∀ x, K x → Kp x) :
    CompRel lib c (Nomm.n3 p) Goal.done bp nd K :=
  compRel_done_of_pick h0 h1 (compRel_n3_pick ho h0 h1 hp hK) fun s v e => by
    simp only [pureEval, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨x, _, rfl⟩ := e
    cases x <;> simp [wut]

/-- **`[5 p q]` for `%done`**, as the case `%5` emits it. -/
theorem compRel_n5_done {lib : Lib} {c : Straight Map} {p q : Nomm} {bp bq : Blob}
    {nd : RNeed} {K Kp Kq : Nat → Prop} {rp rq o kq z o' r0 r1 : Nat}
    (h0 : HoonMap.get c.blocks z = some ⟨[], [Pole.imm (A 0) r0], Termin.don r0⟩)
    (h1 : HoonMap.get c.blocks o' = some ⟨[], [Pole.imm (A 1) r1], Termin.don r1⟩)
    (ho : HoonMap.get c.blocks o = some ⟨[], [], Termin.eqq rp rq ⟨[], z⟩ ⟨[], o'⟩⟩)
    (hkq : HoonMap.get c.blocks kq = some bq)
    (hp : CompRel lib c p (Goal.next (RNeed.this rp) kq) bp nd Kp)
    (hq : CompRel lib c q (Goal.next (RNeed.this rq) o) bq nd Kq)
    (hK : ∀ x, K x → Kp x ∧ Kq x) (hnd : ∀ x, nd.Mem x → Kp x) (hrp : Kq rp) :
    CompRel lib c (Nomm.n5 p q) Goal.done bp nd K :=
  compRel_done_of_pick h0 h1 (compRel_n5_pick ho hkq h0 h1 hp hq hK hnd hrp) fun s v e => by
    simp only [pureEval, Option.bind_eq_some_iff, Option.some.injEq] at e
    obtain ⟨x, _, y, _, rfl⟩ := e
    unfold eqCode; split <;> simp

end

end SkaModel
end Formalization
