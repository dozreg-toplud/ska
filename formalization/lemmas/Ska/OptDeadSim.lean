import lemmas.Ska.OptDead
import lemmas.Ska.OptMiddleSim

/-!
# `+remove-dead-code` keeps the code

`deadF`: the inner `|-` of `+remove-dead-code` read forward (`deadBody_rev`:
the loop over the reversed body is `deadF` of the body).  `deadF l S` is the
body kept and the set `saw` after the walk of `l` from its end, starting from
`S`: an op is dropped exactly when `+get-reg-safe-assignment` names a register
that no later kept op, end or later block mentions.

The walk over `(flop topo)` (`dead_walk`): there is a set `Sf o` for every
block `o` of `topo` (the `saw` at its start: `+get-regs` of its end and all
that was walked before) such that the block after is the block before with the
body `(deadF body (Sf o)).1`, the end's registers lie in `Sf o`, and for every
jump to `t` the set `(deadF body_t (Sf t)).2` lies in `Sf o`: `t` comes later
in `topo` (`TopoOK`), so it was walked before `o`, and `saw` only grows.

The simulation (`DeadI`): the same label, arguments, trace and state, the
same block but for the body, which after is `deadF` of the body before, and
registers that agree on what is live (`(deadF body (Sf lab)).2` off the
parameters still to pass, and the registers the pending arguments name).  A
step before is a step after or, for a dropped op, no step: the dropped op
writes only its register, which is not live (`safe_frame`).  Backward, the code
before first runs the dropped ops at its head, which do not crash by
`LocalOK` (`dead_norm`), and then matches the step after.

**`dead_keeps`**: `+remove-dead-code` on `(flop topo)` keeps the code
(`Keeps`) when `topo` meets `TopoOK`; `deadKeeps` is the statement
`DeadKeeps`.  `LocalOK` is used for the dropped ops; `ReadsOK` and `ArgsOK`
only to be kept.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-! ## The body, forward -/

/-- The inner loop of `+remove-dead-code`, read forward: the body kept and
the final `saw`. -/
def deadF : List Pole → List Nat → List Pole × List Nat
  | [], S => ([], S)
  | p :: rest, S =>
    match safeAssign p with
    | some d =>
      if d ∈ (deadF rest S).2 then (p :: (deadF rest S).1, poleRegs p ++ (deadF rest S).2) else deadF rest S
    | none => (p :: (deadF rest S).1, poleRegs p ++ (deadF rest S).2)

theorem deadBody_append : ∀ (l1 l2 nb : List Pole) (S : List Nat),
    deadBody (l1 ++ l2) nb S = deadBody l2 (deadBody l1 nb S).1 (deadBody l1 nb S).2
  | [], _, _, _ => rfl
  | op :: l1, l2, nb, S => by
    simp only [List.cons_append, deadBody]
    cases safeAssign op with
    | some d =>
      simp only
      by_cases hd : d ∈ S
      · simp only [hd, if_true]; exact deadBody_append l1 l2 _ _
      · simp only [hd, if_false]; exact deadBody_append l1 l2 _ _
    | none => exact deadBody_append l1 l2 _ _

/-- **The loop over the reversed body is `deadF`.** -/
theorem deadBody_rev : ∀ (l nb : List Pole) (S : List Nat),
    deadBody l.reverse nb S = ((deadF l S).1 ++ nb, (deadF l S).2)
  | [], nb, S => by simp [deadBody, deadF]
  | p :: rest, nb, S => by
    rw [List.reverse_cons, deadBody_append, deadBody_rev rest nb S]
    simp only [deadBody, deadF]
    cases safeAssign p with
    | some d =>
      simp only
      by_cases hd : d ∈ (deadF rest S).2
      · simp [hd]
      · simp [hd]
    | none => simp

theorem deadF_sup : ∀ (l : List Pole) (S : List Nat), ∀ k ∈ S, k ∈ (deadF l S).2
  | [], S, k, hk => hk
  | p :: rest, S, k, hk => by
    have ih := deadF_sup rest S k hk
    simp only [deadF]
    cases safeAssign p with
    | some d =>
      simp only
      split
      · exact List.mem_append_right _ ih
      · exact ih
    | none => exact List.mem_append_right _ ih

/-- The head of `deadF`: kept, or dropped. -/
theorem deadF_cons (p : Pole) (rest : List Pole) (S : List Nat) :
    (deadF (p :: rest) S = (p :: (deadF rest S).1, poleRegs p ++ (deadF rest S).2)) ∨
      (∃ d, safeAssign p = some d ∧ d ∉ (deadF rest S).2 ∧ deadF (p :: rest) S = deadF rest S) := by
  simp only [deadF]
  cases h : safeAssign p with
  | some d =>
    simp only
    by_cases hd : d ∈ (deadF rest S).2
    · left; simp [hd]
    · right; exact ⟨d, rfl, hd, by simp [hd]⟩
  | none => left; rfl

/-! ## The walk over `(flop topo)` -/

theorem deadFold_spec (bl : Map Blob) : ∀ (l : List Nat) (acc r : Map Blob × List Nat), l.Nodup →
    l.foldlM (fun (acc : Map Blob × List Nat) o =>
      (HoonMap.get bl o).map fun b =>
        let r := deadBody b.body.reverse [] (finRegs b.fin ++ acc.2)
        (HoonMap.put acc.1 o { b with body := r.1 }, r.2)) acc = some r →
    ∃ Sf : Nat → List Nat,
      (∀ k ∈ l, ∃ b, HoonMap.get bl k = some b ∧
        HoonMap.get r.1 k = some { b with body := (deadF b.body (Sf k)).1 } ∧
        (∀ x ∈ finRegs b.fin, x ∈ Sf k) ∧ (∀ x ∈ acc.2, x ∈ Sf k) ∧ (∀ x ∈ (deadF b.body (Sf k)).2, x ∈ r.2)) ∧
      (∀ k, k ∉ l → HoonMap.get r.1 k = HoonMap.get acc.1 k) ∧
      (∀ x ∈ acc.2, x ∈ r.2) ∧
      (∀ (i j k1 k2 : Nat) (b1 : Blob), i < j → l[i]? = some k1 → l[j]? = some k2 → HoonMap.get bl k1 = some b1 →
        ∀ x ∈ (deadF b1.body (Sf k1)).2, x ∈ Sf k2)
  | [], acc, r, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => [], fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, fun _ h => h,
      fun i j _ _ _ _ hi _ => by simp at hi⟩
  | o :: l, acc, r, hn, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h1
    have hn' := List.nodup_cons.mp hn
    obtain ⟨Sf1, A1, B1, D1, E1⟩ := deadFold_spec bl l _ r hn'.2 h
    simp only [deadBody_rev, List.append_nil] at A1 B1 D1 E1 ⊢
    let S0 := finRegs b.fin ++ acc.2
    refine ⟨fun k => if k = o then S0 else Sf1 k, fun k hk => ?_, fun k hk => ?_, fun x hx => ?_,
      fun i j k1 k2 b1 hij hi hj hb1 x hx => ?_⟩
    · rcases List.mem_cons.mp hk with rfl | hk
      · refine ⟨b, hb, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
        · rw [B1 k hn'.1]; simp [HoonMap.get_put, S0]
        · simp only [if_true]; exact List.mem_append_left _ hx
        · simp only [if_true]; exact List.mem_append_right _ hx
        · simp only [if_true] at hx; exact D1 x hx
      · have hko : k ≠ o := fun e => hn'.1 (e ▸ hk)
        obtain ⟨b', hb', i1, i2, i3, i4⟩ := A1 k hk
        refine ⟨b', hb', ?_, ?_, fun x hx => ?_, ?_⟩
        · simp only [hko, if_false]; exact i1
        · simp only [hko, if_false]; exact i2
        · simp only [hko, if_false]
          exact i3 x (deadF_sup b.body S0 x (List.mem_append_right _ hx))
        · simp only [hko, if_false]; exact i4
    · have hko : k ≠ o := fun e => hk (e ▸ List.mem_cons_self)
      rw [B1 k (fun h' => hk (List.mem_cons_of_mem _ h'))]
      simp [HoonMap.get_put, hko]
    · exact D1 x (deadF_sup b.body S0 x (List.mem_append_right _ hx))
    · cases j with
      | zero => omega
      | succ j' =>
        rw [List.getElem?_cons_succ] at hj
        have hk2 : k2 ∈ l := List.mem_iff_getElem?.mpr ⟨j', hj⟩
        have hk2o : k2 ≠ o := fun e => hn'.1 (e ▸ hk2)
        simp only [hk2o, if_false]
        cases i with
        | zero =>
          rw [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          rw [hb] at hb1; cases hb1
          simp only [if_true] at hx
          exact (A1 k2 hk2).choose_spec.2.2.2.1 x hx
        | succ i' =>
          rw [List.getElem?_cons_succ] at hi
          have hk1 : k1 ∈ l := List.mem_iff_getElem?.mpr ⟨i', hi⟩
          have hk1o : k1 ≠ o := fun e => hn'.1 (e ▸ hk1)
          simp only [hk1o, if_false] at hx
          exact E1 i' j' k1 k2 b1 (by omega) hi hj hb1 x hx

/-- What the walk gives: the block after at every label of `topo`, the
registers of its end in its set, and the live sets of its successors in it. -/
structure DeadW (bl bl' : Map Blob) (topo : List Nat) (Sf : Nat → List Nat) : Prop where
  ok : TopoOK bl topo
  blk : ∀ o ∈ topo, ∃ b, HoonMap.get bl o = some b ∧ HoonMap.get bl' o = some { b with body := (deadF b.body (Sf o)).1 } ∧
    ∀ x ∈ finRegs b.fin, x ∈ Sf o
  jmp : ∀ o b j bt, o ∈ topo → HoonMap.get bl o = some b → j ∈ getJmps b.fin → HoonMap.get bl j.there = some bt →
    ∀ x ∈ (deadF bt.body (Sf j.there)).2, x ∈ Sf o

/-- **The walk over `(flop topo)`**, on a `topo` with `TopoOK`. -/
theorem dead_walk {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') : ∃ Sf, DeadW bl bl' topo Sf := by
  unfold removeDeadCode at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨Sf, A, -, -, E⟩ := deadFold_spec bl topo.reverse _ r (List.pairwise_reverse.mpr (ht.1.imp fun h e => h e.symm)) hr
  refine ⟨Sf, ht, fun o ho => ?_, fun o b j bt ho hb hj hbt x hx => ?_⟩
  · obtain ⟨b, hb, i1, i2, -⟩ := A o (List.mem_reverse.mpr ho)
    exact ⟨b, hb, i1, i2⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    obtain ⟨k, hik, hk⟩ := ht.2.2.2.2 i o b j hi hb hj
    have hk' : k < topo.length := (List.getElem?_eq_some_iff.mp hk).1
    refine E (topo.length - 1 - k) (topo.length - 1 - i) j.there o bt (by omega) ?_ ?_ hbt x hx
    · rw [List.getElem?_reverse (l := topo) (by omega),
        show topo.length - 1 - (topo.length - 1 - k) = k by omega]
      exact hk
    · have hi' : i < topo.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.getElem?_reverse (l := topo) (by omega),
        show topo.length - 1 - (topo.length - 1 - i) = i by omega]
      exact hi

/-! ## The dropped ops -/

section
variable {σ : Type}

/-- **A dropped op writes only its register**, keeps the trace and the state,
and returns `%0` when it does not crash. -/
theorem safe_frame {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {p : Pole} {d : Nat} (hd : safeAssign p = some d)
    {R : Map (Option Noun)} {t : Trace} {ton : Tone} {R2 : Map (Option Noun)} {t2 : Trace} {st2 : σ}
    (h : execPole lib O gul st p R t = some (ton, R2, t2, st2)) :
    ton = Tone.zero (A 0) ∧ t2 = t ∧ st2 = st ∧ ∀ k, k ≠ d → HoonMap.get R2 k = HoonMap.get R k := by
  have put_ne : ∀ (u : Option Noun) k, k ≠ d → HoonMap.get (HoonMap.put R d u) k = HoonMap.get R k :=
    fun u k hk => by simp [HoonMap.get_put, hk]
  cases p with
  | imm n d' =>
    simp only [safeAssign, Option.some.injEq] at hd; subst hd
    simp only [execPole, localPole, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, fun k hk => put_ne _ k hk⟩
  | mov s d' =>
    simp only [safeAssign, Option.some.injEq] at hd; subst hd
    simp only [execPole, localPole, move] at h
    cases e : HoonMap.get R s with
    | none => simp [e] at h
    | some u =>
      simp only [e, Option.map_some, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, fun k hk => put_ne _ k hk⟩
  | con a b d' =>
    simp only [safeAssign, Option.some.injEq] at hd; subst hd
    simp only [execPole, localPole] at h
    cases ea : read a R <;> cases eb : read b R <;> simp [ea, eb] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, fun k hk => put_ne _ k hk⟩
  | hed s d' =>
    simp only [safeAssign, Option.some.injEq] at hd; subst hd
    simp only [execPole, localPole] at h
    cases e : read s R with
    | none => simp [e] at h
    | some v =>
      cases v <;> simp [e] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, fun k hk => put_ne _ k hk⟩
  | tal s d' =>
    simp only [safeAssign, Option.some.injEq] at hd; subst hd
    simp only [execPole, localPole] at h
    cases e : read s R with
    | none => simp [e] at h
    | some v =>
      cases v <;> simp [e] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, fun k hk => put_ne _ k hk⟩
  | _ => simp [safeAssign] at hd

end

/-! ## The simulation -/

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map} {topo : List Nat}
  {Sf : Nat → List Nat}

/-- The registers that must agree at `x`: the live set of the rest of the
block, off the parameters still to pass, and those the pending arguments
name. -/
def DLive (Sf : Nat → List Nat) (x : Cfg σ Map) (k : Nat) : Prop :=
  (k ∈ (deadF x.b.body (Sf x.lab)).2 ∧ k ∉ x.b.par) ∨ some k ∈ x.params

/-- **The relation.** -/
def DeadI (bl : Map Blob) (Sf : Nat → List Nat) (x x' : Cfg σ Map) : Prop :=
  x'.lab = x.lab ∧ x'.params = x.params ∧ x'.t = x.t ∧ x'.st = x.st ∧ Reach bl x.lab ∧
  (∃ b0, HoonMap.get bl x.lab = some b0 ∧ x.b.fin = b0.fin) ∧
  x'.b = { x.b with body := (deadF x.b.body (Sf x.lab)).1 } ∧ Agr (DLive Sf x) x.regs x'.regs

/-- The head of the body before is a dropped op. -/
def Dropped (Sf : Nat → List Nat) (x : Cfg σ Map) : Prop :=
  x.params = [] ∧ x.b.par = [] ∧ ∃ p rest d, x.b.body = p :: rest ∧ safeAssign p = some d ∧
    d ∉ (deadF rest (Sf x.lab)).2

theorem evalPass_check {A : List (Option Nat)} {P : List Nat} {R R1 : Map (Option Noun)}
    (h : evalPass A P R = some R1) : (∀ a ∈ A, ∀ k, a = some k → k ∉ P) ∧ evalPassLoop A P R = some R1 := by
  unfold evalPass at h
  split at h
  · rename_i hc
    refine ⟨fun a ha k e => ?_, h⟩
    rw [List.all_eq_true] at hc
    have := hc a ha
    subst e
    simpa using this
  · cases h

/-- The relation after a pass. -/
theorem deadI_pass {lab : Nat} {b : Blob} {params : List (Option Nat)} {R R' R1 R1' : Map (Option Noun)}
    {t : Trace} {st : σ} (hreach : Reach c.blocks lab) (hb0 : ∃ b0, HoonMap.get c.blocks lab = some b0 ∧ b.fin = b0.fin)
    (hag : Agr (DLive Sf (⟨lab, b, params, R, t, st⟩ : Cfg σ Map)) R R')
    (hR : evalPassLoop params b.par R = some R1) (hR' : evalPassLoop params b.par R' = some R1')
    (hpar : ∀ k ∈ b.par, HoonMap.get R1 k = HoonMap.get R1' k) :
    DeadI c.blocks Sf (⟨lab, { b with par := [] }, [], R1, t, st⟩ : Cfg σ Map)
      ⟨lab, { b with par := [], body := (deadF b.body (Sf lab)).1 }, [], R1', t, st⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, hreach, hb0, rfl, fun k hk => ?_⟩
  rcases hk with ⟨hk, -⟩ | hk
  · by_cases hkp : k ∈ b.par
    · exact hpar k hkp
    · rw [Comp.evalPassLoop_frame _ _ _ _ hR k hkp, Comp.evalPassLoop_frame _ _ _ _ hR' k hkp]
      exact hag k (Or.inl ⟨hk, hkp⟩)
  · simp at hk

/-- The relation after a dropped op: the code after does not move. -/
theorem deadI_drop {x x' : Cfg σ Map} {p : Pole} {rest : List Pole} {d : Nat} {ton : Tone}
    {R2 : Map (Option Noun)} {t2 : Trace} {st2 : σ} (hr : DeadI c.blocks Sf x x') (hp : x.params = [])
    (hq : x.b.par = []) (hb : x.b.body = p :: rest) (hd : safeAssign p = some d)
    (hdn : d ∉ (deadF rest (Sf x.lab)).2) (h : execPole lib O gul x.st p x.regs x.t = some (ton, R2, t2, st2)) :
    ton = Tone.zero (A 0) ∧ DeadI c.blocks Sf ⟨x.lab, { x.b with body := rest }, x.params, R2, t2, st2⟩ x' := by
  obtain ⟨hl, hpe, ht, hst, hreach, hb0, hb', hag⟩ := hr
  obtain ⟨hz, rfl, rfl, hfr⟩ := safe_frame hd h
  have hdrop : deadF x.b.body (Sf x.lab) = deadF rest (Sf x.lab) := by
    rw [hb]
    rcases deadF_cons p rest (Sf x.lab) with h1 | ⟨d', hd', -, h1⟩
    · simp only [deadF, hd] at h1 ⊢
      simp only [hdn, if_false] at h1 ⊢
    · exact h1
  refine ⟨hz, hl, hpe, ht, hst, hreach, hb0, ?_, fun k hk => ?_⟩
  · rw [hb', hdrop]
  · simp only [DLive, hp, List.not_mem_nil, or_false] at hk
    have hkd : k ≠ d := fun e => hdn (e ▸ hk.1)
    rw [hfr k hkd]
    refine hag k (Or.inl ⟨?_, hk.2⟩)
    rw [hdrop]; exact hk.1

/-- The relation after a kept op. -/
theorem deadI_keep {lab : Nat} {b : Blob} {p : Pole} {rest : List Pole} {R2 R2' : Map (Option Noun)}
    {t2 : Trace} {st2 : σ} {params : List (Option Nat)} (hreach : Reach c.blocks lab)
    (hb0 : ∃ b0, HoonMap.get c.blocks lab = some b0 ∧ b.fin = b0.fin) (hq : b.par = [])
    (hag : Agr (fun k => k ∈ poleRegs p ++ (deadF rest (Sf lab)).2) R2 R2') (hp : params = []) :
    DeadI c.blocks Sf (⟨lab, { b with body := rest }, params, R2, t2, st2⟩ : Cfg σ Map)
      ⟨lab, { b with body := (deadF rest (Sf lab)).1 }, params, R2', t2, st2⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, hreach, hb0, rfl, fun k hk => ?_⟩
  subst hp
  simp only [DLive, List.not_mem_nil, or_false] at hk
  exact hag k (List.mem_append_right _ hk.1)

theorem taken_agr {S : Nat → Prop} {R R' : Map (Option Noun)} (hag : Agr S R R') {f : Termin}
    (hS : ∀ k ∈ finRegs f, S k) : taken R' f = taken R f := by
  cases f <;> simp only [taken] <;>
    first
    | rfl
    | (rw [hag.rd (hS _ (by simp [finRegs])), hag.rd (hS _ (by simp [finRegs]))]; done)
    | (rw [hag.rd (hS _ (by simp [finRegs]))]; done)

variable (DW : DeadW c.blocks c'.blocks topo Sf)
include DW

/-- The jump after from the jump before. -/
theorem dead_jump {lab : Nat} {b0 b2 : Blob} {j : Jmp} {R R' : Map (Option Noun)} {t : Trace} {st : σ}
    (hreach : Reach c.blocks lab) (hb0 : HoonMap.get c.blocks lab = some b0) (hj : j ∈ getJmps b0.fin)
    (hb2 : HoonMap.get c.blocks j.there = some b2) (hag : Agr (fun k => k ∈ Sf lab) R R') :
    HoonMap.get c'.blocks j.there = some { b2 with body := (deadF b2.body (Sf j.there)).1 } ∧
    DeadI c.blocks Sf (⟨j.there, b2, j.args, R, t, st⟩ : Cfg σ Map)
      ⟨j.there, { b2 with body := (deadF b2.body (Sf j.there)).1 }, j.args, R', t, st⟩ := by
  have hreach2 : Reach c.blocks j.there := Reach.jump hreach hb0 hj
  have ho : lab ∈ topo := DW.ok.2.2.2.1 lab hreach
  obtain ⟨b2', hb2', hb2'', -⟩ := DW.blk j.there (DW.ok.2.2.2.1 _ hreach2)
  rw [hb2] at hb2'; cases hb2'
  obtain ⟨-, -, -, hfin0⟩ := DW.blk lab ho
  refine ⟨hb2'', rfl, rfl, rfl, rfl, hreach2, ⟨b2, hb2, rfl⟩, rfl, fun k hk => hag k ?_⟩
  rcases hk with ⟨hk, -⟩ | hk
  · exact DW.jmp lab b0 j b2 ho hb0 hj hb2 k hk
  · obtain ⟨b0', hb0', -, hf⟩ := DW.blk lab ho
    rw [hb0] at hb0'; cases hb0'
    exact hf k (jmp_finRegs hj hk)

/-- **Forward**: a step of the code before is a step after or none. -/
theorem dead_fwd_step {x y x' : Cfg σ Map} {es : List (Nat × Nat)} (hs : Step lib O c gul x es y)
    (hr : DeadI c.blocks Sf x x') : ∃ es' y', Steps lib O c' gul x' es' y' ∧ DeadI c.blocks Sf y y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  have hr0 := hr
  obtain ⟨hl, hpe, ht, hst, hreach, hb0, hb', hag⟩ := hr
  simp only at hl hpe ht hst hreach hb0 hb' hag
  subst lab' params' t' st' b'
  cases hs with
  | pass hne hR =>
    simp only at hne hR
    obtain ⟨hck, hR⟩ := evalPass_check hR
    have hm : params.map (argU regs) = params.map (argU regs') := List.map_congr_left (fun a ha => by
      cases a with
      | none => rfl
      | some k => exact hag k (Or.inr ha))
    obtain ⟨R1', hR1', hpar⟩ := OAg.fwd (passLoop_agr params params b.par regs regs' hck hck hm) hR
    exact ⟨_, _, Steps.step (Step.pass (x := ⟨lab, { b with body := (deadF b.body (Sf lab)).1 }, params, regs', t, st⟩)
      hne (by rw [evalPass_ok hck]; exact hR1')) (Steps.refl _), deadI_pass hreach hb0 hag hR hR1' hpar⟩
  | @op p rest n R2 t2 st2 hp hq hbd hpole =>
    simp only at hp hq hbd hpole
    subst hp
    rcases deadF_cons p rest (Sf lab) with hk | ⟨d, hd, hdn, hdr⟩
    · have hS : ∀ k ∈ poleRegs p, DLive Sf (⟨lab, b, [], regs, t, st⟩ : Cfg σ Map) k :=
        fun k hk' => Or.inl ⟨by simp only; rw [hbd, hk]; exact List.mem_append_left _ hk', by simp [hq]⟩
      have hag' : Agr (fun k => k ∈ poleRegs p ++ (deadF rest (Sf lab)).2) regs regs' :=
        fun k hk' => hag k (Or.inl ⟨by simp only; rw [hbd, hk]; exact hk', by simp [hq]⟩)
      obtain ⟨R2', hR2', hag2⟩ := PAg.fwd (execPole_agr lib O gul st p t hag'
        (fun k hk' => List.mem_append_left _ hk')) hpole
      refine ⟨_, _, Steps.step (Step.op (x := ⟨lab, { b with body := (deadF b.body (Sf lab)).1 }, [], regs', t, st⟩)
        (rest := (deadF rest (Sf lab)).1) rfl hq (by simp only; rw [hbd, hk]) hR2') (Steps.refl _), ?_⟩
      have := deadI_keep (c := c) (Sf := Sf) (b := b) (lab := lab) (t2 := t2) (st2 := st2) hreach hb0 hq hag2 rfl
      exact this
    · obtain ⟨-, hdr'⟩ := deadI_drop (lib := lib) (O := O) (gul := gul) hr0 rfl hq hbd hd hdn hpole
      exact ⟨[], _, Steps.refl _, hdr'⟩
  | @jump j b2 hp hq hbd htk hb2 =>
    simp only at hp hq hbd htk hb2
    subst hp
    obtain ⟨b0, hb0', hfin⟩ := hb0
    have hSf : Agr (fun k => k ∈ Sf lab) regs regs' := fun k hk => hag k (Or.inl ⟨by simp only [hbd, deadF]; exact hk,
      by simp [hq]⟩)
    have ho : lab ∈ topo := DW.ok.2.2.2.1 lab hreach
    have hF : ∀ k ∈ finRegs b.fin, k ∈ Sf lab := by
      obtain ⟨b0', hb0'', -, hf⟩ := DW.blk lab ho
      rw [hb0'] at hb0''; cases hb0''
      rw [hfin]; exact hf
    have htk' : taken regs' b.fin = some j := by rw [taken_agr hSf hF]; exact htk
    rw [hfin] at htk
    obtain ⟨hb2', hr2⟩ := dead_jump DW (t := t) (st := st) hreach hb0' (taken_mem htk) hb2 hSf
    refine ⟨_, _, Steps.step (Step.jump (x := ⟨lab, { b with body := (deadF b.body (Sf lab)).1 }, [], regs', t, st⟩)
      rfl hq (by simp only [hbd, deadF]) htk' hb2') (Steps.refl _), hr2⟩

end Sim

end Opt
end SkaModel
end Formalization
