import lemmas.Ska.OptAliasSound

/-!
# The body fold of `+alias` (step (c), the body half)

`as_op` keeps `AOK` for one op given a fresh destination (`AFresh`) and
sources read correctly through `old` (`hrd`).  Here both come from a
structural invariant of the walk state, **`ABInv st Def Done Cl`**, with
`Def` the registers defined so far on the path (every register no definition
writes counts as defined), `Done ⊆ Def` the registers whose `old` is tracked,
and `Cl` the registers whose `old` is not disturbed before their definition:

* every register of `imml` is in `Def`, every register a fact names is in
  `Def`, every key with a non-empty fact is in `Def` (`ALoc`);
* `old` maps `Done` into `Def`;
* a register outside `Def` that is in `Cl` keeps its own name in `old`.

`Cl` is needed because `old` is global to the walk: a dead fill
(`[%cel a] [%imm 0 a] .. [%bom ~]`) of a register that is never read may be
walked before the register's one live definition and rename it; such a
register is not `Cl`, and is not added to `Done` at its definition (nothing
reads it).

**`ab_op`**: `aliasOp` keeps `ABInv` when the op's sources are done and its
destination is not defined (the destination is added to `Def`, and to `Done`
when it is in `Cl`).  **`ab_fresh`** and **`ab_src`** turn `ABInv` into the
hypotheses of `as_op`.  **`as_body`**: along a run of the ops of a body
(`OpsRun`, one `OpSem` per op) that meets `BodyOK` (each op's sources done,
each destination not yet defined, `Def` and `Done` growing op by op),
`aliasBody` keeps `AOK` and `ABInv`; `aliasBody_append` splits the walk of a
body at any place, so `as_body` applies to every prefix, which is what the
simulation reads at each op.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

/-- The facts of `loc` name only registers of `Def`, and a key with a
non-empty fact is in `Def`. -/
def ALoc (Def : Nat → Prop) (loc : AInfo) : Prop :=
  (∀ r i x, loc r = some i → ANames i x → Def x) ∧ (∀ r i, loc r = some i → i = {} ∨ Def r)

/-- **The structural invariant of the body walk.** -/
structure ABInv (st : ABody) (Def Done Cl : Nat → Prop) : Prop where
  imm : ∀ n r, r ∈ st.imml n → Def r
  loc : ALoc Def st.loc
  old : ∀ d, Done d → Def (st.old d)
  done : ∀ d, Done d → Def d
  self : ∀ d, ¬ Def d → Cl d → st.old d = d

section
variable {Def Def' Done Cl : Nat → Prop}

theorem ab_loc_mono {m : AInfo} (h : ALoc Def m) (hD : ∀ x, Def x → Def' x) : ALoc Def' m :=
  ⟨fun r i x hr hx => hD _ (h.1 r i x hr hx), fun r i hr => (h.2 r i hr).imp_right (hD r)⟩

theorem ab_loc_upd {m : AInfo} {k : Nat} {ik : InfoReg} (h : ALoc Def m) (hn : ∀ x, ANames ik x → Def x)
    (hk : ik = {} ∨ Def k) : ALoc Def (updA m k (some ik)) := by
  refine ⟨fun r i x hr hx => ?_, fun r i hr => ?_⟩
  · by_cases e : r = k
    · subst e; rw [as_upd_self] at hr; cases hr; exact hn x hx
    · rw [as_upd_other _ _ e] at hr; exact h.1 r i x hr hx
  · by_cases e : r = k
    · subst e; rw [as_upd_self] at hr; cases hr; exact hk
    · rw [as_upd_other _ _ e] at hr; exact h.2 r i hr

theorem ab_loc_jab {m m2 : AInfo} {k : Nat} {g : InfoReg → InfoReg} (h : ALoc Def m) (hj : jabA m k g = some m2)
    (hn : ∀ i x, ANames (g i) x → ANames i x ∨ Def x) (hk : Def k) : ALoc Def m2 := by
  obtain ⟨i, hi, rfl⟩ := as_jab hj
  refine ab_loc_upd h (fun x hx => ?_) (Or.inr hk)
  rcases hn i x hx with hx | hx
  · exact h.1 k i x hi hx
  · exact hx

theorem ab_mem_insN {l : List Nat} {d x : Nat} (h : x ∈ insN l d) : x ∈ l ∨ x = d := by
  unfold insN at h; split at h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem ab_nm_empty {x : Nat} : ¬ ANames {} x := by
  intro h; rcases h with h | h | h | h | h <;> simp at h

/-- Facts that only set flags or an immediate name nothing. -/
theorem ab_nm_flag {i : InfoReg} {x : Nat} (c l : Bool) (n : Option Noun)
    (h : ANames { i with isCell := c, isLoob := l, hasImm := n } x) : ANames i x := h

end

section
variable {st : ABody} {Def Done Cl : Nat → Prop}

/-- **`ABInv` gives a fresh destination** for a register not yet defined. -/
theorem ab_fresh (hi : ABInv st Def Done Cl) {e : Nat} (he : ¬ Def e) : AFresh st Done e where
  imm := fun n h => he (hi.imm n e h)
  names := fun r i hr hn => he (hi.loc.1 r i e hr hn)
  loc := by
    cases h : st.loc e with
    | none => exact Or.inl rfl
    | some i =>
      rcases hi.loc.2 e i h with h' | h'
      · exact Or.inr (by rw [h'])
      · exact absurd h' he
  done := fun hd => he (hi.done e hd)
  old := fun d hd h => he (h ▸ hi.old d hd)

/-- **`ABInv` and `AOK` give the source condition** of `as_op` for a done
source and an undefined destination. -/
theorem ab_src {R : Nat → Option Noun} (hok : AOK st R Done) (hi : ABInv st Def Done Cl) {x e : Nat}
    (hx : Done x) (he : ¬ Def e) : R (st.old x) = R x ∧ st.old x ≠ e :=
  ⟨hok.old x hx, fun h => he (h ▸ hi.old x hx)⟩

/-- `AOK` for fewer done registers. -/
theorem aok_mono {R : Nat → Option Noun} {D D' : Nat → Prop} (h : AOK st R D) (hD : ∀ x, D' x → D x) :
    AOK st R D' :=
  ⟨h.imm, h.info, fun d hd => h.old d (hD d hd)⟩

/-- A step that keeps `old` and adds at most the registers of `E` to `imml`
and to the keys and names of `loc`. -/
theorem ab_mk_same {st2 : ABody} {E : Nat → Prop} (hi : ABInv st Def Done Cl) (hE : ∀ x, E x → ¬ Def x)
    (himm : ∀ n r, r ∈ st2.imml n → Def r ∨ E r) (hloc : ALoc (fun x => Def x ∨ E x) st2.loc)
    (hold : st2.old = st.old) :
    ABInv st2 (fun x => Def x ∨ E x) (fun x => Done x ∨ (E x ∧ Cl x)) Cl where
  imm := himm
  loc := hloc
  old := fun d hd => by
    rw [hold]
    rcases hd with hd | ⟨hd, hc⟩
    · exact Or.inl (hi.old d hd)
    · rw [hi.self d (hE d hd) hc]; exact Or.inr hd
  done := fun d hd => hd.imp (hi.done d) (fun h => h.1)
  self := fun d hd hc => by rw [hold]; exact hi.self d (fun h => hd (Or.inl h)) hc

/-- A step that drops the op writing `d`, renaming `d` to a defined `y`. -/
theorem ab_mk_drop {st2 : ABody} {E : Nat → Prop} {d y : Nat} (hi : ABInv st Def Done Cl)
    (hEd : E d) (hEu : ∀ x, E x → x = d) (hy : Def y) (himm : st2.imml = st.imml) (hloc : st2.loc = st.loc)
    (hold : st2.old = updA st.old d y) :
    ABInv st2 (fun x => Def x ∨ E x) (fun x => Done x ∨ (E x ∧ Cl x)) Cl where
  imm := fun n r h => by rw [himm] at h; exact Or.inl (hi.imm n r h)
  loc := by rw [hloc]; exact ab_loc_mono hi.loc (fun _ h => Or.inl h)
  old := fun d' hd => by
    rw [hold]
    by_cases e : d' = d
    · subst e; rw [as_upd_self]; exact Or.inl hy
    · rw [as_upd_other _ _ e]
      rcases hd with hd | ⟨hd, _⟩
      · exact Or.inl (hi.old d' hd)
      · exact absurd (hEu d' hd) e
  done := fun d hd => hd.imp (hi.done d) (fun h => h.1)
  self := fun d' hd hc => by
    rw [hold]
    by_cases e : d' = d
    · subst e; exact absurd (Or.inr hEd) hd
    · rw [as_upd_other _ _ e]; exact hi.self d' (fun h => hd (Or.inl h)) hc


/-- **`aliasOp` keeps `ABInv`**, the destination added to `Def` (and to
`Done` when it is in `Cl`), given done sources and an undefined
destination. -/
theorem ab_op {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {st st2 : ABody} {op : Pole} {res : Option Pole} {Def Done Cl : Nat → Prop}
    (h : aliasOp pick st op = some (res, st2)) (hi : ABInv st Def Done Cl)
    (hsrc : ∀ x ∈ asSrc op, Done x) (hdst : ∀ e, aliasDst op = some e → ¬ Def e) :
    ABInv st2 (fun x => Def x ∨ aliasDst op = some x) (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x)) Cl := by
  have hE : ∀ x, aliasDst op = some x → ¬ Def x := hdst
  have sD : ∀ x ∈ asSrc op, Def (st.old x) := fun x hx => hi.old x (hsrc x hx)
  -- no destination, state unchanged
  have same : st2 = st → (∀ e, aliasDst op ≠ some e) →
      ABInv st2 (fun x => Def x ∨ aliasDst op = some x) (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x)) Cl :=
    fun e1 hn => by
      subst e1
      exact ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h)) (ab_loc_mono hi.loc (fun _ h => Or.inl h)) rfl
  have blank : ∀ d, aliasDst op = some d → st2 = { st with loc := updA st.loc d (some {}) } →
      ABInv st2 (fun x => Def x ∨ aliasDst op = some x) (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x)) Cl :=
    fun d hd e => by
      subst e
      exact ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h))
        (ab_loc_upd (ab_loc_mono hi.loc (fun _ h => Or.inl h)) (fun x hx => absurd hx ab_nm_empty) (Or.inl rfl)) rfl
  cases op with
  | imm n d =>
    simp only [aliasOp] at h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ab_mk_drop (d := d) hi rfl (fun x e => by cases e; rfl) (hi.imm n _ (hpick _ hne)) rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ab_mk_same hi hE (fun m r hr => ?_) (ab_loc_upd (ab_loc_mono hi.loc (fun _ h => Or.inl h))
        (fun x hx => ?_) (Or.inr (Or.inr rfl))) rfl
      · dsimp only at hr
        split at hr
        · rename_i hm; subst hm
          rcases ab_mem_insN hr with hr | hr
          · exact Or.inl (hi.imm _ _ hr)
          · subst hr; exact Or.inr rfl
        · exact Or.inl (hi.imm _ _ hr)
      · rcases hx with hx | hx | hx | hx | hx <;> simp at hx
  | mov s d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ab_mk_drop (d := d) hi rfl (fun x e => by cases e; rfl) (sD s (by simp [asSrc])) rfl rfl rfl
  | inc s d =>
    have hsd := sD s (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ab_mk_drop (d := d) hi rfl (fun x e => by cases e; rfl)
        (hi.loc.1 _ ai x hai (Or.inr (Or.inr (Or.inr (Or.inr hx))))) rfl rfl rfl
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h)) ?_ rfl
      refine ab_loc_jab (ab_loc_upd (ab_loc_mono hi.loc (fun _ h => Or.inl h)) (fun x hx => absurd hx ab_nm_empty)
        (Or.inl rfl)) hj (fun i x hx => ?_) (Or.inl hsd)
      rcases hx with hx | hx | hx | hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
      · simp only [Option.some.injEq] at hx; subst hx; exact Or.inr (Or.inr rfl)
  | con h0 t0 d =>
    have hhd := sD h0 (by simp [asSrc])
    have htd := sD t0 (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨hi', hhi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ti, hti, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hp := hpick _ hne
      exact ab_mk_drop (d := d) hi rfl (fun x e => by cases e; rfl)
        (hi.loc.1 _ hi' _ hhi (Or.inr (Or.inr (Or.inl (List.mem_filter.mp hp).1)))) rfl rfl rfl
    · obtain ⟨l1, hj1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l2, hj2, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h)) ?_ rfl
      have L0 := ab_loc_upd (k := d) (ik := { hasHed := some (st.old h0), hasTel := some (st.old t0), isCell := true })
        (ab_loc_mono (Def' := fun x => Def x ∨ aliasDst (Pole.con h0 t0 d) = some x) hi.loc (fun _ h => Or.inl h))
        (fun x hx => by
          rcases hx with hx | hx | hx | hx | hx <;> simp only [Option.some.injEq] at hx
          · subst hx; exact Or.inl hhd
          · subst hx; exact Or.inl htd
          all_goals simp at hx) (Or.inr (Or.inr rfl))
      have L1 := ab_loc_jab L0 hj1 (fun i x hx => by
        rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · rcases ab_mem_insN hx with hx | hx
          · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
          · subst hx; exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))) (Or.inl hhd)
      exact ab_loc_jab L1 hj2 (fun i x hx => by
        rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · rcases ab_mem_insN hx with hx | hx
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
          · subst hx; exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))) (Or.inl htd)
  | hed s d =>
    have hsd := sD s (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ab_mk_drop (d := d) hi rfl (fun x e => by cases e; rfl) (hi.loc.1 _ ai z hai (Or.inl hz)) rfl rfl rfl
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h)) ?_ rfl
      refine ab_loc_jab (ab_loc_upd (ab_loc_mono hi.loc (fun _ h => Or.inl h)) (fun x hx => ?_)
        (Or.inr (Or.inr rfl))) hj (fun i x hx => ?_) (Or.inl hsd)
      · rcases hx with hx | hx | hx | hx | hx <;> simp at hx
        subst hx; exact Or.inl hsd
      · rcases hx with hx | hx | hx | hx | hx
        · simp only [Option.some.injEq] at hx; subst hx; exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  | tal s d =>
    have hsd := sD s (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ab_mk_drop (d := d) hi rfl (fun x e => by cases e; rfl)
        (hi.loc.1 _ ai z hai (Or.inr (Or.inl hz))) rfl rfl rfl
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h)) ?_ rfl
      refine ab_loc_jab (ab_loc_upd (ab_loc_mono hi.loc (fun _ h => Or.inl h)) (fun x hx => ?_)
        (Or.inr (Or.inr rfl))) hj (fun i x hx => ?_) (Or.inl hsd)
      · rcases hx with hx | hx | hx | hx | hx <;> simp at hx
        subst hx; exact Or.inl hsd
      · rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · simp only [Option.some.injEq] at hx; subst hx; exact Or.inr (Or.inr rfl)
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  | cel p =>
    have hsd := sD p (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact same h.2.symm (fun _ e => by cases e)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h))
        (ab_loc_jab (ab_loc_mono hi.loc (fun _ h => Or.inl h)) hj (fun i x hx => Or.inl hx) (Or.inl hsd)) rfl
  | lob p =>
    have hsd := sD p (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact same h.2.symm (fun _ e => by cases e)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ab_mk_same hi hE (fun n r h => Or.inl (hi.imm n r h))
        (ab_loc_jab (ab_loc_mono hi.loc (fun _ h => Or.inl h)) hj (fun i x hx => Or.inl hx) (Or.inl hsd)) rfl
  | equ l r =>
    simp only [aliasOp] at h
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e))
  | hsp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hse => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hdp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hde => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hmp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hme => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hcp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | hce => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm (fun _ e => by cases e)
  | spy _ _ d => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | nok _ _ d => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | cal _ _ d => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | caf _ _ d _ => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | cam _ _ d _ => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | csl _ _ d => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | csf _ _ d _ => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm
  | csm _ _ d _ => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact blank d rfl h.2.symm


/-! ## The fold over a body -/

/-- The values through a run of ops: one `OpSem` per op. -/
inductive OpsRun : List Pole → (Nat → Option Noun) → (Nat → Option Noun) → Prop
  | nil (R : Nat → Option Noun) : OpsRun [] R R
  | cons {op : Pole} {l : List Pole} {R R1 R2 : Nat → Option Noun} :
      OpSem op R R1 → OpsRun l R1 R2 → OpsRun (op :: l) R R2

/-- `Def` after a list of ops: every destination added. -/
def bodyDef : List Pole → (Nat → Prop) → (Nat → Prop)
  | [], Def => Def
  | op :: l, Def => bodyDef l (fun x => Def x ∨ aliasDst op = some x)

/-- `Done` after a list of ops: every destination in `Cl` added. -/
def bodyDone (Cl : Nat → Prop) : List Pole → (Nat → Prop) → (Nat → Prop)
  | [], Done => Done
  | op :: l, Done => bodyDone Cl l (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x))

/-- **What single assignment must give along a body**: each op's sources
(`asSrc`) are done, and its destination is not yet defined. -/
def BodyOK (Cl : Nat → Prop) : List Pole → (Nat → Prop) → (Nat → Prop) → Prop
  | [], _, _ => True
  | op :: l, Def, Done => (∀ x ∈ asSrc op, Done x) ∧ (∀ e, aliasDst op = some e → ¬ Def e) ∧
      BodyOK Cl l (fun x => Def x ∨ aliasDst op = some x) (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x))

/-- **The body fold**: along a run of the ops of a body that meets
`BodyOK`, `aliasBody` keeps `AOK` and `ABInv`. -/
theorem as_body {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {Cl : Nat → Prop} :
    ∀ (ops : List Pole) (st : ABody) (R : Nat → Option Noun) (Def Done : Nat → Prop) (out : List Pole)
      (st' : ABody) (R' : Nat → Option Noun),
    aliasBody pick ops st = some (out, st') → AOK st R Done → ABInv st Def Done Cl → BodyOK Cl ops Def Done →
    OpsRun ops R R' → AOK st' R' (bodyDone Cl ops Done) ∧ ABInv st' (bodyDef ops Def) (bodyDone Cl ops Done) Cl
  | [], st, R, Def, Done, out, st', R', h, hok, hi, _, hr => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases hr
    exact ⟨hok, hi⟩
  | op :: l, st, R, Def, Done, out, st', R', h, hok, hi, hb, hr => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    obtain ⟨hsrc, hdst, hb⟩ := hb
    cases hr with
    | cons hs hr =>
      have hok1 := as_op hpick h1 hok
        (fun x hx => ⟨hok.old x (hsrc x hx),
          fun e he => (ab_src (st := st) hok hi (hsrc x hx) (hdst e he)).2⟩)
        (fun e he => ab_fresh hi (hdst e he)) hs
      have hok1' : AOK st1 _ (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x)) :=
        aok_mono (st := st1) hok1 (fun x hx => Or.imp_right (fun h => ⟨h.1, hi.self x (hdst x h.1) h.2⟩) hx)
      exact as_body hpick l st1 _ _ _ out2 st2 R' h2 hok1' (ab_op hpick h1 hi hsrc hdst) hb hr

/-- `aliasBody` of a concatenation walks the first part, then the second. -/
theorem aliasBody_append (pick : List Nat → Nat) : ∀ (a b : List Pole) (st : ABody),
    aliasBody pick (a ++ b) st =
      (aliasBody pick a st).bind fun r => (aliasBody pick b r.2).map fun r2 => (r.1 ++ r2.1, r2.2)
  | [], b, st => by
    simp only [List.nil_append, aliasBody, Option.bind_some, List.nil_append]
    cases aliasBody pick b st <;> rfl
  | op :: a, b, st => by
    simp only [List.cons_append, aliasBody]
    cases h : aliasOp pick st op with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, aliasBody_append pick a b r.2]
      cases aliasBody pick a r.2 with
      | none => rfl
      | some r1 =>
        simp only [Option.bind_some, Option.map_some]
        cases aliasBody pick b r1.2 with
        | none => rfl
        | some r2 => simp [List.append_assoc]

theorem bodyOK_append {Cl : Nat → Prop} : ∀ (a b : List Pole) (Def Done : Nat → Prop),
    BodyOK Cl (a ++ b) Def Done ↔ BodyOK Cl a Def Done ∧ BodyOK Cl b (bodyDef a Def) (bodyDone Cl a Done)
  | [], b, Def, Done => by simp [BodyOK, bodyDef, bodyDone]
  | op :: a, b, Def, Done => by
    simp only [List.cons_append, BodyOK, bodyDef, bodyDone, bodyOK_append a b]
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩, fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

theorem opsRun_append : ∀ {a b : List Pole} {R R' : Nat → Option Noun}, OpsRun (a ++ b) R R' →
    ∃ Rm, OpsRun a R Rm ∧ OpsRun b Rm R'
  | [], _, R, _, h => ⟨R, OpsRun.nil R, h⟩
  | _ :: _, _, _, _, OpsRun.cons hs hr => by
    obtain ⟨Rm, h1, h2⟩ := opsRun_append hr
    exact ⟨Rm, OpsRun.cons hs h1, h2⟩

/-- **At every place of a body** the walk state so far meets `AOK`, so every
done register read there reads, through `old`, the value it holds. -/
theorem as_body_at {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {Cl : Nat → Prop}
    {a b : List Pole} {st : ABody} {R R' : Nat → Option Noun} {Def Done : Nat → Prop} {out : List Pole}
    {st' : ABody} (h : aliasBody pick (a ++ b) st = some (out, st')) (hok : AOK st R Done)
    (hi : ABInv st Def Done Cl) (hb : BodyOK Cl (a ++ b) Def Done) (hr : OpsRun a R R') :
    ∃ outa sta, aliasBody pick a st = some (outa, sta) ∧ AOK sta R' (bodyDone Cl a Done) ∧
      ABInv sta (bodyDef a Def) (bodyDone Cl a Done) Cl := by
  rw [aliasBody_append] at h
  obtain ⟨⟨outa, sta⟩, ha, -⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨outa, sta, ha, as_body hpick a st R Def Done outa sta R' ha hok hi ((bodyOK_append a b Def Done).mp hb).1 hr⟩

end

end Opt
end SkaModel
end Formalization
