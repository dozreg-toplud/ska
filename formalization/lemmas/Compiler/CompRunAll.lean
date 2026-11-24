import lemmas.Compiler.CompRunCons

/-!
# `+run` on every nomm of the fragment

The summary of the cases of `+run` linked so far (`%0`, `%1`, `%3`, `%4`,
`%5`, `%7`, `%10` and the cons): by induction on the nomm, `CompRunAt` holds
for every pure nomm with no `%6` (`Nomm.pure` is `false` on `%2`, `%6`,
`%11`, `%12` and `%mean`, `noSix` rules out `%6`), on every fork-free goal
with no look at `0` and every state, given `CrSide n`.

The side condition (b) of the cases, no look at `0` in the needs that `+split`
and `+into` return and in the goal that `%7` hands `p`, is discharged here:
`crc_split_lok`, `cra_into_lok` and the invariant `cra_run_lok` (a run of the
model from a goal with no look at `0` returns a `next` with none).  What is
left is `CrSide n`: the axis of every `%10` is not `0`, and the side
condition of `+copy` (`CrCopyOk`) holds at every `+copy` of `%5`, `%10` and
the cons, for every fork-free goal with no look at `0` and every state from
which the case runs.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- No look at axis `0`. -/
def CrLok (s : Sure CSet) : Prop := ∀ y ∈ HoonSet.toList s.lok, y ≠ 0

theorem cra_bind {α β : Type} (x : CM (TreapMap mugF) α) (f : α → CM (TreapMap mugF) β)
    (g : Gen (TreapMap mugF)) (r : β × Gen (TreapMap mugF)) :
    (x >>= f) g = some r ↔ ∃ a g1, x g = some (a, g1) ∧ f a g1 = some r := by
  simp only [bind, StateT.bind]
  cases e : x g with
  | none => simp
  | some p =>
    obtain ⟨a, g1⟩ := p
    simp only [Option.bind_some]
    constructor
    · intro h; exact ⟨a, g1, rfl, h⟩
    · rintro ⟨a', g1', e', h⟩; cases e'; exact h

theorem cra_lok_empty : CrLok (⟨Need.none, HoonSet.empty⟩ : Sure CSet) :=
  fun y hy => absurd hy (HoonSet.mem_empty y)

theorem cra_lok_bunt : CrLok (Sure.bunt : Sure CSet) := fun y hy => absurd hy (HoonSet.mem_empty y)

theorem cra_lok_reg (r : Nat) : CrLok (lazyReg r : Sure CSet) := fun y hy => absurd hy (HoonSet.mem_empty y)

/-- `+copy` unites the looks of its two needs. -/
theorem cra_copy_lok {f : Next CSet} {s : Sure CSet} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : copy f s g = some (nex, g')) (hf : CrLok f.laz) (hs : CrLok s) : CrLok nex.laz := by
  simp only [copy, copyLazy, cra_bind, cf_emit_g] at h
  obtain ⟨o, g1, e1, a, g2, e2, e3⟩ := h
  obtain ⟨⟨ned, ops⟩, g3, e4, u, g4, e5, e6⟩ := e2
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e6 e3
  obtain ⟨rfl, rfl⟩ := e6
  obtain ⟨rfl, rfl⟩ := e3
  intro y hy
  rcases (HoonSet.mem_uni _ _ y).1 hy with hy | hy
  · exact hf y hy
  · exact hs y hy

/-! ## `+into` makes no look at `0` -/

theorem cra_gep_some_none {a l : Nat} (h : gep a l = some Option.none) : l ≠ 0 := by
  unfold gep at h
  intro hl; subst hl
  by_cases a0 : a = 0 <;> simp [a0] at h

theorem cra_gep_some_some {a l r : Nat} (h : gep a l = some (some r)) : r ≠ 0 := by
  unfold gep at h
  by_cases a0 : a = 0
  · simp [a0] at h
  by_cases l0 : l = 0
  · simp [a0, l0] at h
  by_cases e : a = l
  · simp [a0, l0, e] at h; omega
  by_cases lt : l < a
  · simp [a0, l0, e, lt] at h
  simp only [a0, l0, e, lt, if_false] at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    rw [← h]
    intro h0
    have := (Nat.or_eq_zero_iff.1 h0).2
    have := Nat.two_pow_pos (Hoon.metF 0 l - Hoon.metF 0 a)
    omega

theorem cra_intoLok {axe : Nat} {lok ld lr : CSet} (h : intoLok axe lok = some (ld, lr)) :
    (∀ y ∈ HoonSet.toList ld, y ≠ 0) ∧ ∀ y ∈ HoonSet.toList lr, y ≠ 0 := by
  unfold intoLok at h
  have key : ∀ (l : List Nat) (a b c d : CSet), (∀ y ∈ HoonSet.toList a, y ≠ 0) →
      (∀ y ∈ HoonSet.toList b, y ≠ 0) → l.foldl (intoStep axe) (some (a, b)) = some (c, d) →
      (∀ y ∈ HoonSet.toList c, y ≠ 0) ∧ ∀ y ∈ HoonSet.toList d, y ≠ 0 := by
    intro l
    induction l with
    | nil =>
      intro a b c d ha hb e
      simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e; exact ⟨ha, hb⟩
    | cons y l ih =>
      intro a b c d ha hb e
      have hnone : ∀ (l : List Nat), l.foldl (intoStep axe) (Option.none : Option (CSet × CSet)) = Option.none := by
        intro l; induction l with
        | nil => rfl
        | cons _ _ ih' => simpa [intoStep] using ih'
      simp only [List.foldl_cons] at e
      by_cases a0 : axe = 0
      · have : intoStep axe (some (a, b)) y = Option.none := by simp [intoStep, a0]
        rw [this, hnone] at e; cases e
      cases eg : gep axe y with
      | none =>
        have : intoStep axe (some (a, b)) y = Option.none := by simp [intoStep, a0, eg]
        rw [this, hnone] at e; cases e
      | some v =>
        cases v with
        | none =>
          have : intoStep axe (some (a, b)) y = some (a, HoonSet.put b y) := by simp [intoStep, a0, eg]
          rw [this] at e
          refine ih a (HoonSet.put b y) c d ha (fun z hz => ?_) e
          rcases (HoonSet.mem_put _ _ _).1 hz with rfl | hz
          · exact cra_gep_some_none eg
          · exact hb z hz
        | some r =>
          by_cases r1 : r = 1
          · have : intoStep axe (some (a, b)) y = some (a, b) := by simp [intoStep, a0, eg, r1]
            rw [this] at e; exact ih a b c d ha hb e
          · have : intoStep axe (some (a, b)) y = some (HoonSet.put a r, b) := by simp [intoStep, a0, eg, r1]
            rw [this] at e
            refine ih (HoonSet.put a r) b c d (fun z hz => ?_) hb e
            rcases (HoonSet.mem_put _ _ _).1 hz with rfl | hz
            · exact cra_gep_some_some eg
            · exact ha z hz
  exact key _ _ _ _ _ (fun y hy => absurd hy (HoonSet.mem_empty y))
    (fun y hy => absurd hy (HoonSet.mem_empty y)) h

/-- **`+into` returns needs with no look at `0`** (it crashes on one, and on
axis `0`). -/
theorem cra_into_lok {nex : Next CSet} {a : Nat} {g g' : Gen (TreapMap mugF)} {don rec : Sure CSet} {o : Nat}
    (h : into nex a g = some ((don, rec, o), g')) : CrLok don ∧ CrLok rec := by
  simp only [into, intoSure, cra_bind, cf_emit_g] at h
  obtain ⟨o', g1, -, ⟨d, r⟩, g2, e2, e3⟩ := h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
  obtain ⟨⟨rfl, rfl, -⟩, -⟩ := e3
  cases el : intoLok a nex.laz.lok with
  | none => simp [el] at e2
  | some ll =>
    obtain ⟨ld, lr⟩ := ll
    obtain ⟨hd, hr⟩ := cra_intoLok el
    by_cases a0 : a = 0
    · subst a0; simp [el, intoNeed] at e2
    cases en : intoNeed a nex.laz.ned o' g1 with
    | none => simp [el, en] at e2
    | some pn =>
      simp [el, en] at e2
      obtain ⟨⟨rfl, rfl⟩, -⟩ := e2
      refine ⟨hd, fun y hy => ?_⟩
      simp only at hy
      split at hy
      · exact hr y hy
      · rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy
        · exact a0
        · exact hr y hy

/-! ## The invariant: a run returns no look at `0` -/

theorem cra_bomb_lok {miss : Option Nat} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : bomb miss g = some (nex, g')) : CrLok nex.laz := by
  simp only [bomb, cra_bind, cf_emit_g, pure, StateT.pure] at h
  obtain ⟨o, g1, -, h⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact cra_lok_bunt

/-- **A run of the model from a fork-free goal with no look at `0` returns a
`next` with none**, for every pure nomm with no `%6`: the new looks come
from `+from` (`fromSure_lok_ne0`), `+split` (`crc_split_lok`), `+into`
(`cra_into_lok`) and the union of `+copy` (`cra_copy_lok`). -/
theorem cra_run_lok : ∀ (n : Nomm), n.pure = true → noSix n = true → ∀ (gl : CGoal CSet)
    (g g' : Gen (TreapMap mugF)) (nex : Next CSet), run n gl g = some (nex, g') → crLokOk gl → CrLok nex.laz
  | Nomm.cons p q, hpu, h6, gl, g, g', nex, h, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := cra_run_lok p hpu.1 h6.1
    have ihq := cra_run_lok q hpu.2 h6.2
    have hnext : ∀ s th g, run (Nomm.cons p q) (CGoal.next s th) g = some (nex, g') → CrLok nex.laz := by
      intro s th g h
      rw [crc_run_next p q hpu.1 hpu.2] at h
      simp only [cra_bind] at h
      obtain ⟨⟨hed, tel, o⟩, g1, e1, nex2, g2, e2, nex1, g3, e3, e4⟩ := h
      obtain ⟨hh, ht⟩ := crc_split_lok _ g g1 hed tel o e1
      exact cra_copy_lok e4 (ihp _ _ _ _ e3 hh) (ihq _ _ _ _ e2 ht)
    cases gl with
    | next s th => exact hnext s th g h
    | done => rw [crc_run_done] at h; exact hnext _ _ _ h
    | pick z o =>
      rw [crc_run_pick p q hpu.1] at h
      simp only [cra_bind] at h
      obtain ⟨nex2, g2, e2, nex1, g3, e3, e4⟩ := h
      exact cra_copy_lok e4 (ihp _ _ _ _ e3 cra_lok_bunt) (ihq _ _ _ _ e2 cra_lok_bunt)
  | Nomm.n0 ax, _, _, gl, g, g', nex, h, hlok => by
    simp only [run] at h
    split at h
    · exact cra_bomb_lok h
    · rw [cra_bind] at h
      obtain ⟨nex0, g1, e1, h⟩ := h
      have h0 := cr_sn_lok gl hlok g nex0 g1 e1
      split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; exact h0
      · cases ef : «from» ax nex0.laz with
        | none => simp [ef] at h
        | some laz =>
          simp [ef, pure, StateT.pure] at h
          obtain ⟨rfl, -⟩ := h
          exact fromSure_lok_ne0 ef h0
  | Nomm.n1 k, _, _, gl, g, g', nex, h, hlok => by
    cases gl with
    | done =>
      simp only [run, cra_bind, pure, StateT.pure] at h
      obtain ⟨r, g1, -, o, g2, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; exact cra_lok_bunt
    | pick z o =>
      simp only [run] at h
      split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; exact cra_lok_bunt
      · split at h
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h; exact cra_lok_bunt
        · exact cra_bomb_lok h
    | next laz th =>
      simp only [run, cra_bind, pure, StateT.pure] at h
      obtain ⟨o, g1, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; exact cra_lok_bunt
  | Nomm.n3 p, hpu, h6, gl, g, g', nex, h, hlok => by
    have ih := cra_run_lok p hpu h6
    cases gl with
    | next laz th =>
      simp only [run] at h
      split at h
      · exact ih _ _ _ _ h hlok
      · rw [cra_bind] at h
        obtain ⟨a, g1, -, h⟩ := h
        rcases a with _ | ⟨r, o⟩
        · cases h
        · simp only [cra_bind] at h
          obtain ⟨⟨z, o'⟩, g2, -, r', g3, -, oc, g4, -, h⟩ := h
          exact ih _ _ _ _ h (cra_lok_reg r')
    | pick z o =>
      simp only [run, cra_bind] at h
      obtain ⟨r, g1, -, oc, g2, -, h⟩ := h
      exact ih _ _ _ _ h (cra_lok_reg r)
    | done =>
      simp only [run, cra_bind] at h
      obtain ⟨⟨o0, o1⟩, g1, -, r, g2, -, oc, g3, -, h⟩ := h
      exact ih _ _ _ _ h (cra_lok_reg r)
  | Nomm.n4 p, hpu, h6, gl, g, g', nex, h, hlok => by
    have ih := cra_run_lok p hpu h6
    cases gl with
    | done =>
      simp only [run, cra_bind] at h
      obtain ⟨pro, g1, -, arg, g2, -, o, g3, -, h⟩ := h
      exact ih _ _ _ _ h (cra_lok_reg arg)
    | pick z o =>
      simp only [run, cra_bind] at h
      obtain ⟨pro, g1, -, arg, g2, -, o', g3, -, h⟩ := h
      exact ih _ _ _ _ h (cra_lok_reg arg)
    | next laz th =>
      simp only [run, cra_bind] at h
      obtain ⟨a, g1, -, ⟨pro, th'⟩, g2, -, arg, g3, -, o, g4, -, h⟩ := h
      exact ih _ _ _ _ h (cra_lok_reg arg)
  | Nomm.n5 p q, hpu, h6, gl, g, g', nex, h, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := cra_run_lok p hpu.1 h6.1
    have ihq := cra_run_lok q hpu.2 h6.2
    rw [cr_run_n5_eq p q hpu.1] at h
    simp only [cra_bind] at h
    obtain ⟨o, g1, -, nexq, g2, e2, nexp, g3, e3, e4⟩ := h
    exact cra_copy_lok e4 (ihp _ _ _ _ e3 (cra_lok_reg _)) (ihq _ _ _ _ e2 (cra_lok_reg _))
  | Nomm.n7 p q, hpu, h6, gl, g, g', nex, h, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := cra_run_lok p hpu.1 h6.1
    have ihq := cra_run_lok q hpu.2 h6.2
    simp only [run, cra_bind] at h
    obtain ⟨nex1, g1, e1, h⟩ := h
    exact ihp _ _ _ _ h (ihq _ _ _ _ e1 hlok)
  | Nomm.n10 a v q, hpu, h6, gl, g, g', nex, h, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihv := cra_run_lok v hpu.1 h6.1
    have ihq := cra_run_lok q hpu.2 h6.2
    rw [cr_run_n10_eq a v q hpu.1 hpu.2] at h
    simp only [cra_bind] at h
    obtain ⟨nex0, g1, -, ⟨don, rec, o⟩, g2, e2, nexD, g3, e3, nexR, g4, e4, e5⟩ := h
    obtain ⟨hd, hr⟩ := cra_into_lok e2
    exact cra_copy_lok e5 (ihq _ _ _ _ e4 hr) (ihv _ _ _ _ e3 hd)
  | Nomm.n2 _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n6 _ _ _, _, h6, _, _, _, _, _, _ => by simp [noSix] at h6
  | Nomm.n11s _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n11d _ _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n12 _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.mean _ _ _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu

/-! ## The summary -/

/-- **What is left of the side conditions of the cases of `+run`**, by
recursion on the nomm: the axis of a `%10` is not `0`, and the `+copy` of
`%5`, `%10` and the cons meets `CrCopyOk` (`cnLt` of both needs at the
counter and `cnMeet`) at every state the model reaches from a fork-free goal
with no look at `0` and any state.  The nomms outside the fragment carry
`True` (the theorem rules them out by `Nomm.pure` and `noSix`). -/
def CrSide : Nomm → Prop
  | Nomm.cons p q => CrSide p ∧ CrSide q ∧ ∀ gl g, crLokOk gl → CrcCopy p q gl g
  | Nomm.n3 p => CrSide p
  | Nomm.n4 p => CrSide p
  | Nomm.n5 p q => CrSide p ∧ CrSide q ∧ ∀ (gl : CGoal CSet) (g : Gen (TreapMap mugF)), crLokOk gl →
      ∀ o g1 nexq g2 nexp g3, cr5BrM g.re (g.re + 1) gl { g with re := g.re + 1 + 1 } = some (o, g1) →
      run q (CGoal.next (lazyReg (g.re + 1)) (jmp0 o)) g1 = some (nexq, g2) →
      run p (CGoal.next (lazyReg g.re) nexq.th) g2 = some (nexp, g3) → CrCopyOk g3 nexp nexq.laz
  | Nomm.n7 p q => CrSide p ∧ CrSide q
  | Nomm.n10 a v q => a ≠ 0 ∧ CrSide v ∧ CrSide q ∧ ∀ (gl : CGoal CSet) (g : Gen (TreapMap mugF)),
      crLokOk gl → ∀ nex g1 don rec o g2 nexD g3 nexR g4, simpleNext gl g = some (nex, g1) →
      into nex a g1 = some ((don, rec, o), g2) → run v (CGoal.next don (jmp0 o)) g2 = some (nexD, g3) →
      run q (CGoal.next rec nexD.th) g3 = some (nexR, g4) → CrCopyOk g4 nexR nexD.laz
  | _ => True

/-- **`+run` on every nomm of the fragment**: for every pure nomm with no
`%6` (built from `%0`, `%1`, `%3`, `%4`, `%5`, `%7`, `%10` and cons) with
`CrSide n`, on every fork-free goal with no look at `0`, in every region
and from every state, the `$` arm of `+run` is `runL` (for every `mono`,
`sup` and rest of the state with an empty `soft`). -/
theorem comp_run_all (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) :
    ∀ (n : Nomm), n.pure = true → noSix n = true → CrSide n → ∀ (gl : CGoal CSet) (region : List Nat)
      (g : Gen (TreapMap mugF)), crLokOk gl → CompRunAt ctx n (CGoal.toL gl) region g
  | Nomm.cons p q, hpu, h6, hs, gl, region, g, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := comp_run_all h7 hcode p hpu.1 h6.1 hs.1
    have ihq := comp_run_all h7 hcode q hpu.2 h6.2 hs.2.1
    exact comp_run_cons h7 hcode p q hpu.1 hpu.2 h6.1 h6.2 gl region g hlok
      (fun s th g1 hl => ihp (CGoal.next s th) region g1 hl)
      (fun s th g1 hl => ihq (CGoal.next s th) region g1 hl) (hs.2.2 gl g hlok)
  | Nomm.n0 ax, _, _, _, gl, region, g, hlok => comp_run_n0 h7 ax gl region g hlok
  | Nomm.n1 k, _, _, _, gl, region, g, hlok => comp_run_n1 h7 k gl region g hlok
  | Nomm.n3 p, hpu, h6, hs, gl, region, g, hlok => by
    have ih := comp_run_all h7 hcode p hpu h6 hs
    exact comp_run_n3 h7 p gl region g hlok (ih gl region g hlok)
      (fun r o g1 => ih (CGoal.next (lazyReg r) (jmp0 o)) region g1 (cra_lok_reg r))
  | Nomm.n4 p, hpu, h6, hs, gl, region, g, hlok => by
    have ih := comp_run_all h7 hcode p hpu h6 hs
    exact comp_run_n4 h7 p gl region g hlok
      (fun r o g1 => ih (CGoal.next (lazyReg r) (jmp0 o)) region g1 (cra_lok_reg r))
  | Nomm.n5 p q, hpu, h6, hs, gl, region, g, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := comp_run_all h7 hcode p hpu.1 h6.1 hs.1
    have ihq := comp_run_all h7 hcode q hpu.2 h6.2 hs.2.1
    exact comp_run_n5 h7 hcode p q hpu.1 hpu.2 h6.1 h6.2 gl region g hlok
      (fun r o g1 => ihq (CGoal.next (lazyReg r) (jmp0 o)) region g1 (cra_lok_reg r))
      (fun r th g1 => ihp (CGoal.next (lazyReg r) th) region g1 (cra_lok_reg r)) (hs.2.2 gl g hlok)
  | Nomm.n7 p q, hpu, h6, hs, gl, region, g, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := comp_run_all h7 hcode p hpu.1 h6.1 hs.1
    have ihq := comp_run_all h7 hcode q hpu.2 h6.2 hs.2
    refine comp_run_n7 p q (CGoal.toL gl) region g (ihq gl region g hlok) (fun nex g1 e => ?_)
    rw [runL_toL q hpu.2 h6.2, map_apply] at e
    cases eq : run (S := CSet) (Map := TreapMap mugF) q gl g with
    | none => rw [eq] at e; cases e
    | some r =>
      obtain ⟨nex', g1'⟩ := r
      rw [eq] at e
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ihp (Next.goal nex') region g1' (cra_run_lok q hpu.2 h6.2 gl g g1' nex' eq hlok)
  | Nomm.n10 a v q, hpu, h6, hs, gl, region, g, hlok => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihv := comp_run_all h7 hcode v hpu.1 h6.1 hs.2.1
    have ihq := comp_run_all h7 hcode q hpu.2 h6.2 hs.2.2.1
    exact comp_run_n10 h7 hcode a hs.1 v q hpu.1 hpu.2 h6.1 h6.2 gl region g hlok
      (fun s th g1 hl => ihv (CGoal.next s th) region g1 hl)
      (fun s th g1 hl => ihq (CGoal.next s th) region g1 hl)
      (fun _ _ _ _ _ _ _ ei => cra_into_lok ei) (hs.2.2.2 gl g hlok)
  | Nomm.n2 _ _ _, hpu, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n6 _ _ _, _, h6, _, _, _, _, _ => by simp [noSix] at h6
  | Nomm.n11s _ _ _, hpu, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n11d _ _ _ _, hpu, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n12 _ _, hpu, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.mean _ _ _ _ _, hpu, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu

end Compiler
end Formalization
