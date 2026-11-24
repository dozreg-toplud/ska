import lemmas.Ska.OptAliasAll

/-!
# Toward the simulation of `+alias`: the agreement relation through the body

The simulation of `+alias` relates a configuration of the code before (values
`R`) with one of the code after (values `R'`).  The code after reads through
`old` and skips the dropped ops, so `R'` differs from `R` at the destinations
of the dropped ops.  What the code after needs is **`AKept`**
(`OptAliasAll.lean`): `R'` equals `R` at every register of an immediate, every
register a fact names, and the `old` of every done register.  This file
proves that `AKept` follows the body walk.

* **`ACov st Done x`**: `x` is one of those registers (covered).
  `akept_of_cov` and `akept_cov` turn `AKept` into agreement on `ACov`.
* **`acov_op`**: after one step of `aliasOp` a covered register was covered
  before, or it is the destination of a kept op.  A dropped op renames its
  destination to a covered register: a dropped `%imm n d` to `pick (imml n)`,
  a dropped `%mov s d` to `old s` of a done source, a dropped `%inc`,
  `%hed`, `%tal` to a register its argument's fact names, a dropped `%con` to
  a member of `hedOf`.  A kept op names only covered registers and its
  destination (a kept `%con h t d` names `old h` and `old t`).
* **`akept_op`**: one step of `aliasOp` keeps `AKept`, when the code before
  writes the destination and the code after writes it with the same value if
  the op is kept, and leaves it alone if the op is dropped (the destination
  is fresh, `AFresh`, so it is not covered before).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

/-! ## Covered registers -/

/-- **A covered register** at a walk state: a register of an immediate, a
register a fact names, or the `old` of a done register. -/
def ACov (st : ABody) (Done : Nat → Prop) (x : Nat) : Prop :=
  (∃ n, x ∈ st.imml n) ∨ (∃ r i, st.loc r = some i ∧ ANames i x) ∨ (∃ d, Done d ∧ st.old d = x)

theorem akept_of_cov {st : ABody} {R R' : Nat → Option Noun} {Done : Nat → Prop}
    (h : ∀ x, ACov st Done x → R' x = R x) : AKept st R R' Done :=
  ⟨fun n r hr => h r (Or.inl ⟨n, hr⟩), fun r i x hr hx => h x (Or.inr (Or.inl ⟨r, i, hr, hx⟩)),
    fun d hd => h _ (Or.inr (Or.inr ⟨d, hd, rfl⟩))⟩

theorem akept_cov {st : ABody} {R R' : Nat → Option Noun} {Done : Nat → Prop} (h : AKept st R R' Done) :
    ∀ x, ACov st Done x → R' x = R x := by
  rintro x (⟨n, hx⟩ | ⟨r, i, hr, hx⟩ | ⟨d, hd, rfl⟩)
  · exact h.imm n x hx
  · exact h.names r i x hr hx
  · exact h.old d hd

/-- A fresh destination is not covered. -/
theorem acov_fresh {st : ABody} {Done : Nat → Prop} {e : Nat} (hf : AFresh st Done e) : ¬ ACov st Done e := by
  rintro (⟨n, hx⟩ | ⟨r, i, hr, hx⟩ | ⟨d, hd, he⟩)
  · exact hf.imm n hx
  · exact hf.names r i hr hx
  · exact hf.old d hd he

/-! ## Names through updates of the facts -/

/-- The names of `m2` are names of `m` or meet `P`. -/
def NSub (m m2 : AInfo) (P : Nat → Prop) : Prop :=
  ∀ r i y, m2 r = some i → ANames i y → (∃ r' i', m r' = some i' ∧ ANames i' y) ∨ P y

theorem nsub_refl (m : AInfo) (P : Nat → Prop) : NSub m m P := fun r i x hr hx => Or.inl ⟨r, i, hr, hx⟩

theorem nsub_trans {m m1 m2 : AInfo} {P : Nat → Prop} (h1 : NSub m m1 P) (h2 : NSub m1 m2 P) : NSub m m2 P := by
  intro r i x hr hx
  rcases h2 r i x hr hx with ⟨r', i', hr', hx'⟩ | hp
  · exact h1 r' i' x hr' hx'
  · exact Or.inr hp

theorem nsub_upd {m : AInfo} {P : Nat → Prop} {k : Nat} {i : InfoReg} (hi : ∀ x, ANames i x → P x) :
    NSub m (updA m k (some i)) P := by
  intro r i' x hr hx
  by_cases e : r = k
  · subst e; rw [as_upd_self] at hr; cases hr; exact Or.inr (hi x hx)
  · rw [as_upd_other _ _ e] at hr; exact Or.inl ⟨r, i', hr, hx⟩

theorem nsub_jab {m m2 : AInfo} {P : Nat → Prop} {k : Nat} {f : InfoReg → InfoReg} (h : jabA m k f = some m2)
    (hf : ∀ i x, ANames (f i) x → ANames i x ∨ P x) : NSub m m2 P := by
  obtain ⟨i0, hi0, rfl⟩ := as_jab h
  intro r i x hr hx
  by_cases e : r = k
  · subst e; rw [as_upd_self] at hr; cases hr
    rcases hf i0 x hx with h1 | h1
    · exact Or.inl ⟨r, i0, hi0, h1⟩
    · exact Or.inr h1
  · rw [as_upd_other _ _ e] at hr; exact Or.inl ⟨r, i, hr, hx⟩

theorem anames_empty {x : Nat} : ¬ ANames ({} : InfoReg) x := by
  rintro (h | h | h | h | h) <;> simp at h

theorem anames_insN {l : List Nat} {d x : Nat} (h : x ∈ insN l d) : x ∈ l ∨ x = d := by
  unfold insN at h; split at h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-! ## Coverage through one op -/

section
variable {st st2 : ABody} {Done : Nat → Prop}

/-- The `old` clause when `old` is unchanged. -/
theorem acov_old_same {op : Pole} (hold : st2.old = st.old) {z x : Nat}
    (hz : Done z ∨ (aliasDst op = some z ∧ st.old z = z)) (hx : st2.old z = x) :
    (∃ d, Done d ∧ st.old d = x) ∨ aliasDst op = some x := by
  rw [hold] at hx
  rcases hz with hz | ⟨hz, hs⟩
  · exact Or.inl ⟨z, hz, hx⟩
  · rw [hs] at hx; subst hx; exact Or.inr hz

/-- The `old` clause when a dropped op renames its destination `e` to `y`. -/
theorem acov_old_drop {op : Pole} {e y : Nat} (he : aliasDst op = some e) (hold : st2.old = updA st.old e y)
    (hnd : ¬ Done e) {z x : Nat} (hz : Done z ∨ (aliasDst op = some z ∧ st.old z = z)) (hx : st2.old z = x) :
    (∃ d, Done d ∧ st.old d = x) ∨ x = y := by
  rw [hold] at hx
  rcases hz with hz | ⟨hz, -⟩
  · have hze : z ≠ e := fun h => hnd (h ▸ hz)
    rw [as_upd_other _ _ hze] at hx; exact Or.inl ⟨z, hz, hx⟩
  · rw [he] at hz; cases hz; rw [as_upd_self] at hx; exact Or.inr hx.symm

end

theorem anm_dec {i : InfoReg} {d x : Nat} (h : ANames { i with decOf := some d } x) : ANames i x ∨ x = d := by
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Option.some.inj h).symm

theorem anm_hasHed {i : InfoReg} {d x : Nat} (h : ANames { i with hasHed := some d } x) : ANames i x ∨ x = d := by
  rcases h with h | h | h | h | h
  · exact Or.inr (Option.some.inj h).symm
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem anm_hasTel {i : InfoReg} {d x : Nat} (h : ANames { i with hasTel := some d } x) : ANames i x ∨ x = d := by
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Option.some.inj h).symm
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem anm_hedOf {i : InfoReg} {d x : Nat} (h : ANames { i with hedOf := insN i.hedOf d } x) :
    ANames i x ∨ x = d := by
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · rcases anames_insN h with h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr h
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem anm_telOf {i : InfoReg} {d x : Nat} (h : ANames { i with telOf := insN i.telOf d } x) :
    ANames i x ∨ x = d := by
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · rcases anames_insN h with h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr h
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- **Coverage through one step of `aliasOp`**: a register covered after was
covered before, or is the destination of a kept op. -/
theorem acov_op {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {st st2 : ABody} {op : Pole} {res : Option Pole} {Done : Nat → Prop}
    (h : aliasOp pick st op = some (res, st2)) (hsrc : ∀ x ∈ asSrc op, Done x)
    (hnd : ∀ e, aliasDst op = some e → ¬ Done e) :
    ∀ x, ACov st2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) x →
      ACov st Done x ∨ (aliasDst op = some x ∧ res.isSome) := by
  generalize hT : (fun x => ACov st Done x ∨ (aliasDst op = some x ∧ res.isSome)) = T
  have hT' : ∀ x, T x → ACov st Done x ∨ (aliasDst op = some x ∧ res.isSome) := fun x hx => by rw [← hT] at hx; exact hx
  have gen : (∀ n r, r ∈ st2.imml n → (∃ n', r ∈ st.imml n') ∨ T r) → NSub st.loc st2.loc T →
      (∀ z x, (Done z ∨ (aliasDst op = some z ∧ st.old z = z)) → st2.old z = x →
        (∃ d, Done d ∧ st.old d = x) ∨ T x) →
      ∀ x, ACov st2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) x →
        ACov st Done x ∨ (aliasDst op = some x ∧ res.isSome) := by
    intro himm hloc hold x hx
    rcases hx with ⟨n, hx⟩ | ⟨r, i, hr, hx⟩ | ⟨z, hz, hzx⟩
    · rcases himm n x hx with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact hT' x h1
    · rcases hloc r i x hr hx with h1 | h1
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact hT' x h1
    · rcases hold z x hz hzx with h1 | h1
      · exact Or.inl (Or.inr (Or.inr h1))
      · exact hT' x h1
  have cov : ∀ x, ACov st Done x → T x := fun x hx => by rw [← hT]; exact Or.inl hx
  have srcC : ∀ s ∈ asSrc op, T (st.old s) := fun s hs => cov _ (Or.inr (Or.inr ⟨s, hsrc s hs, rfl⟩))
  have nmC : ∀ r i x, st.loc r = some i → ANames i x → T x := fun r i x hr hx => cov x (Or.inr (Or.inl ⟨r, i, hr, hx⟩))
  have dstC : ∀ x, aliasDst op = some x → res.isSome → T x := fun x h1 h2 => by rw [← hT]; exact Or.inr ⟨h1, h2⟩
  -- `old` unchanged
  have oldS : st2.old = st.old → (∀ x, aliasDst op = some x → res.isSome) →
      ∀ z x, (Done z ∨ (aliasDst op = some z ∧ st.old z = z)) → st2.old z = x → (∃ d, Done d ∧ st.old d = x) ∨ T x :=
    fun ho hk z x hz hx => (acov_old_same ho hz hx).imp_right fun h => dstC x h (hk x h)
  -- a dropped op renamed to a covered `y`
  have oldD : ∀ e y, aliasDst op = some e → st2.old = updA st.old e y → T y →
      ∀ z x, (Done z ∨ (aliasDst op = some z ∧ st.old z = z)) → st2.old z = x → (∃ d, Done d ∧ st.old d = x) ∨ T x :=
    fun e y he ho hy z x hz hx => (acov_old_drop he ho (hnd e he) hz hx).imp_right fun h => by rw [h]; exact hy
  have immS : ∀ n r, r ∈ st.imml n → (∃ n', r ∈ st.imml n') ∨ T r := fun n r h => Or.inl ⟨n, h⟩
  have blank : ∀ d, aliasDst op = some d → res.isSome → st2 = { st with loc := updA st.loc d (some {}) } →
      ∀ x, ACov st2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) x →
        ACov st Done x ∨ (aliasDst op = some x ∧ res.isSome) := by
    intro d hd hk e; subst e
    exact gen immS (nsub_upd fun x hx => absurd hx anames_empty) (oldS rfl fun x h => hk)
  cases op with
  | imm n d =>
    simp only [aliasOp] at h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldD d _ rfl rfl (cov _ (Or.inl ⟨n, hpick _ hne⟩)))
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine gen (fun m r hr => ?_) (nsub_upd fun x hx => ?_) (oldS rfl fun _ _ => rfl)
      · dsimp only at hr
        split at hr
        · rename_i hm; subst hm
          rcases anames_insN hr with hr | hr
          · exact Or.inl ⟨_, hr⟩
          · exact Or.inr (dstC r (by rw [hr]; rfl) rfl)
        · exact Or.inl ⟨m, hr⟩
      · rcases hx with h | h | h | h | h <;> simp at h
  | mov s d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldD d _ rfl rfl (srcC s (by simp [asSrc])))
  | inc s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldD d _ rfl rfl (nmC _ ai x hai (Or.inr (Or.inr (Or.inr (Or.inr hx))))))
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact gen immS (nsub_trans (nsub_upd fun x hx => absurd hx anames_empty)
        (nsub_jab hj fun i x hx => (anm_dec hx).imp_right fun e => dstC x (by rw [e]; rfl) rfl))
        (oldS rfl fun _ _ => rfl)
  | con h0 t0 d =>
    simp only [aliasOp] at h
    obtain ⟨hi, hhi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ti, hti, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hp := hpick _ hne
      obtain ⟨hp1, -⟩ := List.mem_filter.mp hp
      exact gen immS (nsub_refl _ _) (oldD d _ rfl rfl (nmC _ hi _ hhi (Or.inr (Or.inr (Or.inl hp1)))))
    · obtain ⟨l1, hj1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l2, hj2, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine gen immS (nsub_trans (nsub_trans (nsub_upd fun x hx => ?_)
        (nsub_jab hj1 fun i x hx => (anm_hedOf hx).imp_right fun e => dstC x (by rw [e]; rfl) rfl))
        (nsub_jab hj2 fun i x hx => (anm_telOf hx).imp_right fun e => dstC x (by rw [e]; rfl) rfl))
        (oldS rfl fun _ _ => rfl)
      rcases hx with h | h | h | h | h <;> simp at h
      · subst h; exact srcC h0 (by simp [asSrc])
      · subst h; exact srcC t0 (by simp [asSrc])
  | hed s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldD d _ rfl rfl (nmC _ ai x hai (Or.inl hx)))
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine gen immS (nsub_trans (nsub_upd fun x hx => ?_)
        (nsub_jab hj fun i x hx => (anm_hasHed hx).imp_right fun e => dstC x (by rw [e]; rfl) rfl))
        (oldS rfl fun _ _ => rfl)
      rcases hx with h | h | h | h | h <;> simp at h
      subst h; exact srcC s (by simp [asSrc])
  | tal s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldD d _ rfl rfl (nmC _ ai x hai (Or.inr (Or.inl hx))))
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine gen immS (nsub_trans (nsub_upd fun x hx => ?_)
        (nsub_jab hj fun i x hx => (anm_hasTel hx).imp_right fun e => dstC x (by rw [e]; rfl) rfl))
        (oldS rfl fun _ _ => rfl)
      rcases hx with h | h | h | h | h <;> simp at h
      subst h; exact srcC s (by simp [asSrc])
  | cel p =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_jab hj fun i x hx => Or.inl hx) (oldS rfl fun _ e => by cases e)
  | lob p =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_jab hj fun i x hx => Or.inl hx) (oldS rfl fun _ e => by cases e)
  | equ l r =>
    simp only [aliasOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hsp =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hse =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hdp =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hde =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hmp =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hme =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hcp =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | hce =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact gen immS (nsub_refl _ _) (oldS rfl fun _ e => by cases e)
  | spy _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | nok _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | cal _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | caf _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | cam _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | csl _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | csf _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl
  | csm _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact blank d rfl rfl rfl

/-- **One step of `aliasOp` keeps `AKept`**: the code before writes the
destination of the op (`R2`), the code after writes it with the same value
when the op is kept and leaves its values alone when the op is dropped
(`R'2`); the destination is fresh. -/
theorem akept_op {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {st st2 : ABody} {op : Pole} {res : Option Pole} {Done : Nat → Prop} {R R' R2 R'2 : Nat → Option Noun}
    (h : aliasOp pick st op = some (res, st2)) (hsrc : ∀ x ∈ asSrc op, Done x)
    (hf : ∀ e, aliasDst op = some e → AFresh st Done e) (hk : AKept st R R' Done)
    (hR2 : ∀ x, aliasDst op ≠ some x → R2 x = R x)
    (hR2' : ∀ x, (aliasDst op ≠ some x ∨ res = none) → R'2 x = R' x)
    (hd : ∀ e, aliasDst op = some e → res.isSome → R'2 e = R2 e) :
    AKept st2 R2 R'2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) := by
  apply akept_of_cov
  intro x hx
  rcases acov_op hpick h hsrc (fun e he => (hf e he).done) x hx with hc | ⟨he, hs⟩
  · have hne : aliasDst op ≠ some x := fun he => acov_fresh (hf x he) hc
    rw [hR2' x (Or.inl hne), hR2 x hne]
    exact akept_cov hk x hc
  · exact hd x he hs

/-! ## A kept op after runs as the op before -/

section
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

/-- The write of an op: none, or a value into a register. -/
def wrX (W : Option (Nat × Noun)) (regs : Map (Option Noun)) : Map (Option Noun) :=
  match W with
  | none => regs
  | some (d, v) => store d v regs

/-- **The results of an op before and of the op kept after**: both crash, or
the same tone, trace and state, with the same write on each register file. -/
def XRel (r r' : Option (Tone × Map (Option Noun) × Trace × σ)) (regs regs' : Map (Option Noun)) : Prop :=
  (r = none ∧ r' = none) ∨
    ∃ ton t2 s2 W, r = some (ton, wrX W regs, t2, s2) ∧ r' = some (ton, wrX W regs', t2, s2)

theorem akx_mapM {old : Nat → Nat} {R R' : Nat → Option Noun} :
    ∀ v : List Nat, (∀ x ∈ v, R' (old x) = R x) → (v.map old).mapM R' = v.mapM R
  | [], _ => rfl
  | x :: v, h => by
    simp only [List.map_cons, List.mapM_cons, h x List.mem_cons_self,
      akx_mapM v fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem akx_reads_dst {op : Pole} {d x : Nat} {l : List Nat} (hl : poleRegs op = l ++ [d])
    (hd : aliasDst op = some d) (hx : x ∈ l) : x ∈ aliasReads op := by
  unfold aliasReads; rw [hd]; dsimp only; rw [hl]
  by_cases e : x = d
  · subst e; rw [List.erase_append_left _ hx]; simp
  · exact (List.mem_erase_of_ne e).mpr (List.mem_append_left _ hx)

theorem akx_reads_call {op : Pole} {d x : Nat} {v : List Nat} (hl : poleRegs op = d :: v)
    (hd : aliasDst op = some d) (hx : x ∈ v) : x ∈ aliasReads op := by
  unfold aliasReads; rw [hd]; dsimp only; rw [hl, List.erase_cons_head]; exact hx

theorem akx_reads_none {op : Pole} {x : Nat} (hd : aliasDst op = none) (hx : x ∈ poleRegs op) :
    x ∈ aliasReads op := by
  unfold aliasReads; rw [hd]; exact hx

theorem xrel_none {r : Option (Tone × Map (Option Noun) × Trace × σ)} {regs regs' : Map (Option Noun)}
    (h : r = none) : XRel r r regs regs' := Or.inl ⟨h, h⟩

/-- **A kept op after runs as the op before**: when every register the op
reads reads, through `old`, the value it has before, the op kept by
`aliasOp` gives the same tone, trace, state and write on the file after. -/
theorem akx_exec {pick : List Nat → Nat} {st st2 : ABody} {op op' : Pole}
    (h : aliasOp pick st op = some (some op', st2)) (lib : Lib) (O : Oracle σ) (gul : Noun) (s : σ)
    {regs regs' : Map (Option Noun)} (t : Trace)
    (hrd : ∀ x ∈ aliasReads op, read (st.old x) regs' = read x regs) :
    XRel (execPole lib O gul s op regs t) (execPole lib O gul s op' regs' t) regs regs' := by
  have one : ∀ x, x ∈ aliasReads op → read (st.old x) regs' = read x regs := hrd
  have call : ∀ {α : Type} (r : Option α) (f : α → Option (Tone × σ)) (d : Nat),
      XRel (r.bind fun vs => (f vs).bind fun (ton, st') => afterCall st' regs t d ton)
        (r.bind fun vs => (f vs).bind fun (ton, st') => afterCall st' regs' t d ton) regs regs' := by
    intro α r f d
    rcases r with _ | vs
    · exact Or.inl ⟨rfl, rfl⟩
    · simp only [Option.bind_some]
      rcases f vs with _ | ⟨ton, st'⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · simp only [Option.bind_some]
        cases ton with
        | zero p => exact Or.inr ⟨_, _, _, some (d, p), rfl, rfl⟩
        | one b => exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
        | two tr => exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  cases op with
  | imm n d =>
    simp only [aliasOp] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inr ⟨_, _, _, some (d, n), rfl, rfl⟩
  | mov s d => simp [aliasOp] at h
  | inc s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e := one s (akx_reads_dst (l := [s]) rfl rfl List.mem_cons_self)
      simp only [execPole, localPole, e]
      rcases read s regs with _ | (a | ⟨x, y⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, some (d, _), rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | con h0 t0 d =>
    simp only [aliasOp] at h
    obtain ⟨hi, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ti, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨l1, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l2, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e1 := one h0 (akx_reads_dst (l := [h0, t0]) rfl rfl (by simp))
      have e2 := one t0 (akx_reads_dst (l := [h0, t0]) rfl rfl (by simp))
      simp only [execPole, localPole, e1, e2]
      rcases read h0 regs with _ | x
      · exact Or.inl ⟨rfl, rfl⟩
      · rcases read t0 regs with _ | y
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨_, _, _, some (d, _), rfl, rfl⟩
  | hed s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e := one s (akx_reads_dst (l := [s]) rfl rfl List.mem_cons_self)
      simp only [execPole, localPole, e]
      rcases read s regs with _ | (a | ⟨x, y⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, some (d, _), rfl, rfl⟩
  | tal s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e := one s (akx_reads_dst (l := [s]) rfl rfl List.mem_cons_self)
      simp only [execPole, localPole, e]
      rcases read s regs with _ | (a | ⟨x, y⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, some (d, _), rfl, rfl⟩
  | cel p =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e := one p (akx_reads_none rfl List.mem_cons_self)
      simp only [execPole, localPole, e]
      rcases read p regs with _ | (a | ⟨x, y⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | lob p =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e := one p (akx_reads_none rfl List.mem_cons_self)
      simp only [execPole, localPole, e]
      rcases read p regs with _ | v
      · exact Or.inl ⟨rfl, rfl⟩
      · simp only [Option.bind_some]
        split
        · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
        · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | equ l r =>
    simp only [aliasOp] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have e1 := one l (akx_reads_none rfl (by simp [poleRegs]))
      have e2 := one r (akx_reads_none rfl (by simp [poleRegs]))
      simp only [execPole, localPole, e1, e2]
      rcases read l regs with _ | x
      · exact Or.inl ⟨rfl, rfl⟩
      · rcases read r regs with _ | y
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hsp n f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hse n f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hcp n f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hce n f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, localPole]
    rcases popTrace t with _ | t1
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hdp n p f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have e := one p (akx_reads_none rfl List.mem_cons_self)
    simp only [execPole, localPole, e]
    split
    · rcases read p regs with _ | v
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
    · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hde n p f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, localPole]
    split
    · rcases popTrace t with _ | t1
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
    · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hmp a v f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have e := akx_mapM (old := st.old) (R := fun x => read x regs) (R' := fun x => read x regs') v
      (fun x hx => one x (akx_reads_none rfl hx))
    simp only [execPole, localPole, e]
    rcases v.mapM (fun x => read x regs) with _ | vs
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | hme a v f =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, localPole]
    rcases popTrace t with _ | t1
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | spy e0 p d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have e1 := one e0 (akx_reads_dst (l := [e0, p]) rfl rfl (by simp))
    have e2 := one p (akx_reads_dst (l := [e0, p]) rfl rfl (by simp))
    simp only [execPole, localPole, e1, e2]
    split
    · exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
    · rcases read e0 regs with _ | x
      · exact Or.inl ⟨rfl, rfl⟩
      · rcases read p regs with _ | y
        · exact Or.inl ⟨rfl, rfl⟩
        · simp only [Option.bind_some]
          rcases lib.slam gul (C x y) with _ | res
          · exact Or.inl ⟨rfl, rfl⟩
          · simp only [Option.bind_some]
            rcases scryDecode res with _ | dr
            · exact Or.inl ⟨rfl, rfl⟩
            · simp only [Option.bind_some]
              cases dr with
              | block => exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
              | hunk => exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
              | val w => exact Or.inr ⟨_, _, _, some (d, w), rfl, rfl⟩
  | nok u f d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have e1 := one u (akx_reads_dst (l := [u, f]) rfl rfl (by simp))
    have e2 := one f (akx_reads_dst (l := [u, f]) rfl rfl (by simp))
    simp only [execPole, e1, e2]
    rcases read u regs with _ | x
    · exact Or.inl ⟨rfl, rfl⟩
    · rcases read f regs with _ | y
      · exact Or.inl ⟨rfl, rfl⟩
      · simp only [Option.bind_some]
        rcases O.nok s x y gul with _ | ⟨ton, s2⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · simp only [Option.bind_some]
          cases ton with
          | zero q => exact Or.inr ⟨_, _, _, some (d, q), rfl, rfl⟩
          | one b => exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
          | two tr => exact Or.inr ⟨_, _, _, none, rfl, rfl⟩
  | cal a v d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, akx_mapM (old := st.old) (R := fun x => read x regs) (R' := fun x => read x regs') v
      (fun x hx => one x (akx_reads_call rfl rfl hx))]
    exact call _ _ d
  | caf a v d n =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, akx_mapM (old := st.old) (R := fun x => read x regs) (R' := fun x => read x regs') v
      (fun x hx => one x (akx_reads_call rfl rfl hx))]
    exact call _ _ d
  | cam a v d n =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, akx_mapM (old := st.old) (R := fun x => read x regs) (R' := fun x => read x regs') v
      (fun x hx => one x (akx_reads_call rfl rfl hx))]
    exact call _ _ d
  | csl a s0 d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, one s0 (akx_reads_dst (l := [s0]) rfl rfl List.mem_cons_self)]
    exact call _ _ d
  | csf a s0 d n =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, one s0 (akx_reads_dst (l := [s0]) rfl rfl List.mem_cons_self)]
    exact call _ _ d
  | csm a s0 d n =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [execPole, one s0 (akx_reads_dst (l := [s0]) rfl rfl List.mem_cons_self)]
    exact call _ _ d

end

end Opt
end SkaModel
end Formalization
