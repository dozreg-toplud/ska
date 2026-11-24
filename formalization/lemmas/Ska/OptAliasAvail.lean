import lemmas.Ska.OptAliasTrim

/-!
# The registers `+alias` renames to are defined in the code after

`DefFirst` of the blocks `+alias` returns asks that every register a block
after reads is defined before on every path of blocks of the result.  A read
after is a read before renamed by `old` at the op (`aop_rename`), and `old`
renames a register only to an immediate (`imml`), to a register a fact names,
or to the `old` of a register the op reads.  **`TAv st A Done`**: every such
target is in `A`, the registers available at the point of the walk.  Along a
body (**`tav_op`**, **`tav_body`**) `A` grows by the destinations of the ops
kept, and a dropped op renames its destination to a target already in `A`.

This file: `TAv`, `tav_op`, `tav_body`, and the renamed reads
(`aliasDst_rename`, `areads_rename`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- **The targets of renaming are available**: the immediates, the registers
facts name, and the `old` of every done register are in `A`. -/
structure TAv (st : ABody) (A Done : Nat → Prop) : Prop where
  imm : ∀ n r, r ∈ st.imml n → A r
  names : ∀ r i x, st.loc r = some i → ANames i x → A x
  old : ∀ d, Done d → A (st.old d)

theorem tav_mono {st : ABody} {A A' Done Done' : Nat → Prop} (h : TAv st A Done) (hA : ∀ y, A y → A' y)
    (hD : ∀ x, Done' x → Done x) : TAv st A' Done' :=
  ⟨fun n r hr => hA r (h.imm n r hr), fun r i x hr hx => hA x (h.names r i x hr hx), fun d hd => hA _ (h.old d (hD d hd))⟩

theorem aliasDst_rename (σ : Nat → Nat) (op : Pole) : aliasDst (renameP σ op) = aliasDst op := by
  cases op <;> rfl

/-- `TAv` after a step, from the pieces. -/
theorem tv_mk {st st2 : ABody} {A A' Done Cl : Nat → Prop} {dst : Option Nat}
    (hT : TAv st A Done) (hA : ∀ y, A y → A' y)
    (himm : ∀ n r, r ∈ st2.imml n → A' r) (hnames : ∀ r i x, st2.loc r = some i → ANames i x → A' x)
    (hold : ∀ d, Done d → st2.old d = st.old d) (hnew : ∀ d, dst = some d → Cl d → A' (st2.old d)) :
    TAv st2 A' (fun x => Done x ∨ (dst = some x ∧ Cl x)) :=
  ⟨himm, hnames, fun d hd => by
    rcases hd with hd | ⟨hd, hc⟩
    · rw [hold d hd]; exact hA _ (hT.old d hd)
    · exact hnew d hd hc⟩

theorem tv_names_upd {m : AInfo} {k : Nat} {ik : InfoReg} {A : Nat → Prop}
    (h : ∀ r i x, m r = some i → ANames i x → A x) (hk : ∀ x, ANames ik x → A x) :
    ∀ r i x, updA m k (some ik) r = some i → ANames i x → A x := by
  intro r i x hr hx
  by_cases e : r = k
  · subst e; rw [as_upd_self] at hr; cases hr; exact hk x hx
  · rw [as_upd_other _ _ e] at hr; exact h r i x hr hx

theorem tv_names_jab {m m2 : AInfo} {k : Nat} {g : InfoReg → InfoReg} {A : Nat → Prop}
    (h : ∀ r i x, m r = some i → ANames i x → A x) (hj : jabA m k g = some m2)
    (hg : ∀ i x, ANames (g i) x → ANames i x ∨ A x) : ∀ r i x, m2 r = some i → ANames i x → A x := by
  obtain ⟨i, hi, rfl⟩ := as_jab hj
  refine tv_names_upd h (fun x hx => ?_)
  rcases hg i x hx with hx | hx
  · exact h k i x hi hx
  · exact hx

/-- **One op keeps `TAv`**, `A` growing by the destination of a kept op, given
done sources, a destination not done, and a kept destination of `Cl` keeping
its own name. -/
theorem tav_op {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {st st2 : ABody} {op : Pole} {res : Option Pole} {A Done Cl : Nat → Prop}
    (h : aliasOp pick st op = some (res, st2)) (hT : TAv st A Done)
    (hsrc : ∀ x ∈ asSrc op, Done x) (hnd : ∀ e, aliasDst op = some e → ¬ Done e)
    (hself : ∀ e, aliasDst op = some e → res.isSome → Cl e → st.old e = e) :
    TAv st2 (fun y => A y ∨ (res.isSome ∧ aliasDst op = some y))
      (fun x => Done x ∨ (aliasDst op = some x ∧ Cl x)) := by
  have hA : ∀ y, A y → A y ∨ (res.isSome ∧ aliasDst op = some y) := fun y hy => Or.inl hy
  have hold : ∀ d, Done d → st2.old d = st.old d := fun d hd =>
    awk_op_old h d (fun e => hnd d e hd)
  have sA : ∀ x ∈ asSrc op, A (st.old x) := fun x hx => hT.old x (hsrc x hx)
  -- a kept op leaves `old` alone
  have kept : res.isSome → st2.old = st.old → ∀ d, aliasDst op = some d → Cl d →
      A (st2.old d) ∨ (res.isSome ∧ aliasDst op = some (st2.old d)) := fun hk e d hd hc => by
    rw [e, hself d hd hk hc]; exact Or.inr ⟨hk, hd⟩
  cases op with
  | imm n d =>
    simp only [aliasOp] at h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d' hd _ => ?_)
      cases hd
      simp only [as_upd_self]
      exact Or.inl (hT.imm n _ (hpick _ hne))
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => ?_) ?_ hold (kept rfl rfl)
      · dsimp only at hr
        split at hr
        · rename_i hm; subst hm
          rcases ab_mem_insN hr with hr | hr
          · exact Or.inl (hT.imm _ _ hr)
          · subst hr; exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl (hT.imm _ _ hr)
      · exact tv_names_upd (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
          (fun x hx => by rcases hx with hx | hx | hx | hx | hx <;> simp at hx)
  | mov s d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
      hold (fun d' hd _ => ?_)
    cases hd
    simp only [as_upd_self]
    exact Or.inl (sA s (by simp [asSrc]))
  | inc s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d' hd _ => ?_)
      cases hd
      simp only [as_upd_self]
      exact Or.inl (hT.names _ ai x hai (Or.inr (Or.inr (Or.inr (Or.inr hx)))))
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) ?_ hold (kept rfl rfl)
      refine tv_names_jab (tv_names_upd (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        (fun x hx => absurd hx ab_nm_empty)) hj (fun i x hx => ?_)
      rcases hx with hx | hx | hx | hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
      · simp only [Option.some.injEq] at hx; subst hx; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | con h0 t0 d =>
    have hhd := sA h0 (by simp [asSrc])
    have htd := sA t0 (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨hi', hhi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ti, hti, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d' hd _ => ?_)
      cases hd
      simp only [as_upd_self]
      exact Or.inl (hT.names _ hi' _ hhi (Or.inr (Or.inr (Or.inl (List.mem_filter.mp (hpick _ hne)).1))))
    · obtain ⟨l1, hj1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l2, hj2, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) ?_ hold (kept rfl rfl)
      have L0 := tv_names_upd (k := d) (ik := { hasHed := some (st.old h0), hasTel := some (st.old t0), isCell := true })
        (A := fun y => A y ∨ ((some (Pole.con (st.old h0) (st.old t0) d)).isSome ∧ aliasDst (Pole.con h0 t0 d) = some y))
        (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        (fun x hx => by
          rcases hx with hx | hx | hx | hx | hx <;> simp only [Option.some.injEq] at hx
          · subst hx; exact Or.inl hhd
          · subst hx; exact Or.inl htd
          all_goals simp at hx)
      have L1 := tv_names_jab L0 hj1 (fun i x hx => by
        rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · rcases ab_mem_insN hx with hx | hx
          · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
          · subst hx; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx)))))
      exact tv_names_jab L1 hj2 (fun i x hx => by
        rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · rcases ab_mem_insN hx with hx | hx
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
          · subst hx; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx)))))
  | hed s d =>
    have hsd := sA s (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d' hd _ => ?_)
      cases hd
      simp only [as_upd_self]
      exact Or.inl (hT.names _ ai z hai (Or.inl hz))
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) ?_ hold (kept rfl rfl)
      refine tv_names_jab (tv_names_upd (fun r i x hr hx => Or.inl (hT.names r i x hr hx)) (fun x hx => ?_)) hj
        (fun i x hx => ?_)
      · rcases hx with hx | hx | hx | hx | hx <;> simp at hx
        subst hx; exact Or.inl hsd
      · rcases hx with hx | hx | hx | hx | hx
        · simp only [Option.some.injEq] at hx; subst hx; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  | tal s d =>
    have hsd := sA s (by simp [asSrc])
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d' hd _ => ?_)
      cases hd
      simp only [as_upd_self]
      exact Or.inl (hT.names _ ai z hai (Or.inr (Or.inl hz)))
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) ?_ hold (kept rfl rfl)
      refine tv_names_jab (tv_names_upd (fun r i x hr hx => Or.inl (hT.names r i x hr hx)) (fun x hx => ?_)) hj
        (fun i x hx => ?_)
      · rcases hx with hx | hx | hx | hx | hx <;> simp at hx
        subst hx; exact Or.inl hsd
      · rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · simp only [Option.some.injEq] at hx; subst hx; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  | cel p =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d hd => by cases hd)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr))
        (tv_names_jab (fun r i x hr hx => Or.inl (hT.names r i x hr hx)) hj (fun i x hx => Or.inl hx))
        hold (fun d hd => by cases hd)
  | lob p =>
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d hd => by cases hd)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr))
        (tv_names_jab (fun r i x hr hx => Or.inl (hT.names r i x hr hx)) hj (fun i x hx => Or.inl hx))
        hold (fun d hd => by cases hd)
  | equ l r =>
    simp only [aliasOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d hd => by cases hd)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
        hold (fun d hd => by cases hd)
  | spy _ _ d | nok _ _ d | cal _ _ d | caf _ _ d _ | cam _ _ d _ | csl _ _ d | csf _ _ d _ | csm _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr))
      (tv_names_upd (fun r i x hr hx => Or.inl (hT.names r i x hr hx)) (fun x hx => absurd hx ab_nm_empty))
      hold (kept rfl rfl)
  | hsp | hse | hdp | hde | hmp | hme | hcp | hce =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact tv_mk hT hA (fun m r hr => Or.inl (hT.imm m r hr)) (fun r i x hr hx => Or.inl (hT.names r i x hr hx))
      hold (fun d hd => by cases hd)

/-- **Along a body that meets `BodyOK`, `TAv` holds at the end** with `A`
grown by the destinations of the ops kept. -/
theorem tav_body {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {Cl : Nat → Prop} :
    ∀ (ops : List Pole) (st : ABody) (Def Done A : Nat → Prop) (out : List Pole) (st' : ABody),
    aliasBody pick ops st = some (out, st') → ABInv st Def Done Cl → BodyOK Cl ops Def Done → TAv st A Done →
    TAv st' (fun y => A y ∨ y ∈ out.filterMap aliasDst) (bodyDone Cl ops Done)
  | [], st, Def, Done, A, out, st', h, _, _, hT => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact tav_mono hT (fun y hy => Or.inl hy) (fun _ h => h)
  | op :: l, st, Def, Done, A, out, st', h, hi, hb, hT => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hsrc, hdst, hb⟩ := hb
    have hT1 := tav_op hpick h1 hT hsrc (fun e he hd => hdst e he (hi.done e hd))
      (fun e he _ hc => hi.self e (hdst e he) hc)
    have ih := tav_body hpick l st1 _ _ _ out2 st2 h2 (ab_op hpick h1 hi hsrc hdst) hb hT1
    refine tav_mono ih (fun y hy => ?_) (fun _ h => h)
    rcases hy with (hy | ⟨hk, hd⟩) | hy
    · exact Or.inl hy
    · right
      cases res with
      | none => cases hk
      | some op' =>
        have e := aop_rename h1
        subst e
        simp only [Option.toList_some, List.cons_append, List.nil_append, List.filterMap_cons, aliasDst_rename, hd]
        exact List.mem_cons_self
    · right
      rw [List.filterMap_append]
      exact List.mem_append_right _ hy

/-! ## The reads of a renamed op -/

theorem av_erase2 {a d x : Nat} : x ∈ [a, d].erase d ↔ x = a := by
  by_cases e : a = d
  · subst e; simp
  · rw [List.erase_cons_tail (by simpa using e)]; simp

theorem av_erase3 {a b d x : Nat} : x ∈ [a, b, d].erase d ↔ x = a ∨ x = b := by
  by_cases e1 : a = d
  · subst e1; simp only [List.erase_cons_head, List.mem_cons, List.not_mem_nil, or_false]; exact or_comm
  · rw [List.erase_cons_tail (by simpa using e1)]
    by_cases e2 : b = d
    · subst e2; simp
    · rw [List.erase_cons_tail (by simpa using e2)]; simp

theorem av_erase_cons {d x : Nat} {v : List Nat} : x ∈ (d :: v).erase d ↔ x ∈ v := by simp

/-- **The registers a renamed op reads** are renamings of the registers the op
reads. -/
theorem areads_rename (σ : Nat → Nat) (op : Pole) {x : Nat} (hx : x ∈ aliasReads (renameP σ op)) :
    ∃ y ∈ aliasReads op, x = σ y := by
  cases op <;> simp only [renameP, aliasReads, aliasDst, poleRegs] at hx ⊢
  case imm n d => simp at hx
  case mov s d => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case inc s d => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case con h t d =>
    rcases av_erase3.mp hx with e | e
    · exact ⟨h, av_erase3.mpr (Or.inl rfl), e⟩
    · exact ⟨t, av_erase3.mpr (Or.inr rfl), e⟩
  case hed s d => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case tal s d => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case spy e p d =>
    rcases av_erase3.mp hx with h | h
    · exact ⟨e, av_erase3.mpr (Or.inl rfl), h⟩
    · exact ⟨p, av_erase3.mpr (Or.inr rfl), h⟩
  case nok u f d =>
    rcases av_erase3.mp hx with h | h
    · exact ⟨u, av_erase3.mpr (Or.inl rfl), h⟩
    · exact ⟨f, av_erase3.mpr (Or.inr rfl), h⟩
  case cal a v d =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (av_erase_cons.mp hx)
    exact ⟨y, av_erase_cons.mpr hy, rfl⟩
  case caf a v d n =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (av_erase_cons.mp hx)
    exact ⟨y, av_erase_cons.mpr hy, rfl⟩
  case cam a v d k =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (av_erase_cons.mp hx)
    exact ⟨y, av_erase_cons.mpr hy, rfl⟩
  case csl a s d => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case csf a s d n => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case csm a s d k => exact ⟨s, av_erase2.mpr rfl, av_erase2.mp hx⟩
  case cel p => simp at hx; exact ⟨p, by simp, hx⟩
  case lob p => simp at hx; exact ⟨p, by simp, hx⟩
  case equ l r =>
    simp at hx
    rcases hx with h | h
    · exact ⟨l, by simp, h⟩
    · exact ⟨r, by simp, h⟩
  case hdp n p f => simp at hx; exact ⟨p, by simp, hx⟩
  case hde n p f => simp at hx; exact ⟨p, by simp, hx⟩
  case hmp a v f => obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ⟨y, hy, rfl⟩
  case hme a v f => obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ⟨y, hy, rfl⟩
  all_goals simp at hx

/-- **The `i`-th op kept** comes from an op `k` of the body, walked from the
state after the first `k` ops, which keep `i` ops. -/
theorem abody_at {pick : List Nat → Nat} : ∀ (ops : List Pole) (st : ABody) (out : List Pole) (st' : ABody),
    aliasBody pick ops st = some (out, st') → ∀ (i : Nat) (op' : Pole), out[i]? = some op' →
    ∃ (k : Nat) (op : Pole) (sta : ABody) (outa : List Pole) (st1 : ABody), ops[k]? = some op ∧
      aliasBody pick (ops.take k) st = some (outa, sta) ∧ outa.length = i ∧
      aliasOp pick sta op = some (some op', st1)
  | [], st, out, st', h, i, op', hi => by
    simp only [aliasBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp at hi
  | op :: l, st, out, st', h, i, op', hi => by
    simp only [aliasBody] at h
    obtain ⟨⟨res, st1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨out2, st2⟩, h2, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    cases res with
    | none =>
      simp only [Option.toList_none, List.nil_append] at hi
      obtain ⟨k, op0, sta, outa, st3, hk, hb, hl, ho⟩ := abody_at l st1 out2 st2 h2 i op' hi
      refine ⟨k + 1, op0, sta, outa, st3, by simpa using hk, ?_, hl, ho⟩
      simp only [List.take_succ_cons, aliasBody, h1, Option.bind_some, hb, Option.map_some,
        Option.toList_none, List.nil_append]
    | some o0 =>
      simp only [Option.toList_some, List.cons_append, List.nil_append] at hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨0, op, st, [], st1, rfl, by simp [aliasBody], rfl, h1⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨k, op0, sta, outa, st3, hk, hb, hl, ho⟩ := abody_at l st1 out2 st2 h2 i op' hi
        refine ⟨k + 1, op0, sta, o0 :: outa, st3, by simpa using hk, ?_, by simp [hl], ho⟩
        simp only [List.take_succ_cons, aliasBody, h1, Option.bind_some, hb, Option.map_some,
          Option.toList_some, List.cons_append, List.nil_append]

/-- The destinations of the ops kept are destinations of the body. -/
theorem abody_dsts {pick : List Nat → Nat} {ops : List Pole} {st : ABody} {out : List Pole} {st' : ABody}
    (h : aliasBody pick ops st = some (out, st')) {x : Nat} (hx : x ∈ out.filterMap aliasDst) :
    x ∈ ops.filterMap aliasDst := by
  obtain ⟨op', hop', hd⟩ := List.mem_filterMap.mp hx
  obtain ⟨op, hop, σ, rfl⟩ := abody_kept ops st out st' h op' hop'
  rw [aliasDst_rename] at hd
  exact List.mem_filterMap.mpr ⟨op, hop, hd⟩

/-! ## Availability along the paths of the result -/

section
variable [MapKeys Map]

/-- **The registers available at the end of a path** `p` of blocks of `G`
(the last block first): no definition before, or a definition after in a block
of `p`. -/
def AvP (bl G : Map Blob) (p : List Nat) (y : Nat) : Prop :=
  y ∉ allDefs bl ∨ ∃ o' ∈ p, ∃ b', HoonMap.get G o' = some b' ∧ y ∈ blockDefs b'

theorem AvP.mono {bl G : Map Blob} {p p' : List Nat} (h : ∀ x ∈ p, x ∈ p') {y : Nat} (hy : AvP bl G p y) :
    AvP bl G p' y := by
  rcases hy with hy | ⟨o', ho', b', hb', hd⟩
  · exact Or.inl hy
  · exact Or.inr ⟨o', h o' ho', b', hb', hd⟩

theorem bpath_sub {bl G : Map Blob} (hs : TargetsSub bl G) {L : List Nat} (h : BPath G L) : BPath bl L := by
  induction h with
  | start => exact BPath.start
  | step _ hb hj ih =>
    obtain ⟨b0, hb0, hjs⟩ := hs _ _ hb
    obtain ⟨j0, hj0, he⟩ := hjs _ hj
    rw [← he]; exact BPath.step ih hb0 hj0

theorem bpath_suffix {G : Map Blob} : ∀ {L : List Nat}, BPath G L → ∀ {o p}, L = o :: p → ∀ o' ∈ p,
    ∃ p', BPath G (o' :: p') ∧ ∀ x ∈ o' :: p', x ∈ p
  | _, BPath.start, _, _, e, o', h => by cases e; cases h
  | _, BPath.step (o := o1) (p := p1) hp _ _, o, p, e, o', h => by
    cases e
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨p1, hp, fun x hx => hx⟩
    · obtain ⟨p', hp', hsub⟩ := bpath_suffix hp rfl o' h
      exact ⟨p', hp', fun x hx => List.mem_cons_of_mem _ (hsub x hx)⟩

/-- **The availability invariant** at the point `pre` of the walk with state
`g`, relative to the blocks `G` the walk returns: every edge of a walked block
after to a block not walked yet is listed; at the end of every walked jumping
block, along every path of `G` to it, the immediates and the registers facts
name are available; and the `old` of every register a walked jumping block
defines is available along every path of `G` to that block. -/
structure TInvA (bl G : Map Blob) (pre : List Nat) (g : AGen Map) : Prop where
  lst : ∀ q pb j, q ∈ pre → HoonMap.get g.new q = some pb → j ∈ getJmps pb.fin → j.there ∉ pre →
    q ∈ g.rev j.there
  ends : ∀ q b j lq mq p, q ∈ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin →
    g.info q = some lq → g.imms q = some mq → BPath G (q :: p) →
    (∀ n r, r ∈ mq n → AvP bl G (q :: p) r) ∧ (∀ r i x, lq r = some i → ANames i x → AvP bl G (q :: p) x)
  glob : ∀ d q b j p, q ∈ pre → HoonMap.get bl q = some b → j ∈ getJmps b.fin → d ∈ blockDefs b →
    ClR bl d → (∀ o' i, DeadFill bl d o' i → o' ∉ pre) → BPath G (q :: p) → AvP bl G (q :: p) (g.old d)

theorem tav_init {bl G : Map Blob} {rev : Map (List Nat)} : TInvA bl G [] (aliasInit (Map := Map) rev) where
  lst := fun _ _ _ hq => absurd hq List.not_mem_nil
  ends := fun _ _ _ _ _ _ hq => absurd hq List.not_mem_nil
  glob := fun _ _ _ _ _ hq => absurd hq List.not_mem_nil

/-- A register no block defines keeps its own name. -/
theorem tav_undef {bl : Map Blob} {pre : List Nat} {g : AGen Map} (hw : OldW bl pre g) {d : Nat}
    (hd : d ∉ allDefs bl) : g.old d = d :=
  Classical.byContradiction fun hne => by
    obtain ⟨o, -, -, b, hb, hm⟩ := hw d hne
    exact hd (bdef_allDefs hb (List.mem_append_right _ hm))

/-- **`TAv` at the start of a walked block** along a path of `G` to it. -/
theorem tav_start {bl G : Map Blob} (hS : AliasSSAB bl) (hGs : TargetsSub bl G) {nargs : Nat} {pre l : List Nat}
    {o : Nat} {g : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hI : SInv bl (pre ++ o :: l) pre g)
    (hA : TInvA bl G pre g) (hGq : ∀ q ∈ pre, HoonMap.get G q = HoonMap.get g.new q) {b : Blob}
    (hb : HoonMap.get bl o = some b) {p : List Nat} (hπG : BPath G (o :: p))
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : (if g.rev o = [] then some (entryInfo nargs) else aliasStart g o (g.rev o)) = some info)
    (him : aliasStartImms g (g.rev o) = some imms) (hed : aliasEdges g o (g.rev o) = some edges)
    (hpa : aliasPars g b.par edges info = some loc0) :
    TAv ⟨g.old, loc0, imms⟩ (fun y => AvP bl G p y ∨ y ∈ b.par) (DoneS bl pre p b) := by
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hπ : BPath bl (o :: p) := bpath_sub hGs hπG
  have hR : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hparold : ∀ x ∈ b.par, ClR bl x → g.old x = x := fun x hx hc =>
    awi_self hS ht hI.oldw hc (awi_par_notDefW hS.1 hR hb hx hopre)
  -- the `old` of a register done along the path
  have hold : ∀ d, DoneS bl pre p b d → AvP bl G p (g.old d) ∨ g.old d ∈ b.par := by
    intro d ⟨hd, hc, hf⟩
    rcases hd with hd | hd | ⟨o'', ho'', b'', hb'', hd⟩
    · rw [tav_undef hI.oldw hd]; exact Or.inl (Or.inl hd)
    · rw [hparold d hd hc]; exact Or.inr hd
    · left
      obtain ⟨b3, j3, hb3, hj3⟩ := bdef_jumps hπ rfl o'' ho''
      rw [hb''] at hb3; cases hb3
      obtain ⟨p'', hp'', hsub⟩ := bpath_suffix hπG rfl o'' ho''
      exact AvP.mono hsub (hA.glob d o'' b'' j3 p'' (sst_path_pre ht hopre hπ o'' ho'') hb'' hj3 hd hc hf hp'')
  cases p with
  | nil =>
    have ho0 : o = 0 := by cases hπG; rfl
    subst ho0
    have h0 : g.rev 0 = [] := awa_rev_zero ht hI.rev
    rw [if_pos h0] at hst
    cases hst
    rw [h0] at him hed
    simp only [aliasStartImms, Option.some.injEq] at him
    subst him
    simp [aliasEdges] at hed
    subst hed
    have hloc : ∀ r i, loc0 r = some i → i = {} := by
      intro r i hr
      rcases sst_pars_nil b.par _ loc0 hpa r i hr with hr | ⟨-, hr⟩
      · simp only [entryInfo] at hr
        split at hr
        · cases hr; rfl
        · cases hr
      · exact hr
    exact ⟨fun n r hr => absurd hr List.not_mem_nil,
      fun r i x hr hx => by rw [hloc r i hr] at hx; exact absurd hx ab_nm_empty, hold⟩
  | cons q p' =>
    obtain ⟨hπq, pbq, jg, hpbq, hjg, hjgo⟩ : BPath G (q :: p') ∧ ∃ pb j, HoonMap.get G q = some pb ∧
        j ∈ getJmps pb.fin ∧ j.there = o := by
      cases hπG with
      | step hp hb' hj => exact ⟨hp, _, _, hb', hj, rfl⟩
    obtain ⟨bq, jq, hbq, hjq, hjqo⟩ : ∃ bq jq, HoonMap.get bl q = some bq ∧ jq ∈ getJmps bq.fin ∧ jq.there = o := by
      cases hπ with
      | step _ hb' hj => exact ⟨_, _, hb', hj, rfl⟩
    have hRq : Reach bl q := ssk_bpath_reach hπ q (List.mem_cons_of_mem _ List.mem_cons_self)
    have hqpre : q ∈ pre := awr_pre ht (ht.2.2.2.1 q hRq) hbq hjq hjqo
    have hpbq' : HoonMap.get g.new q = some pbq := by rw [← hGq q hqpre]; exact hpbq
    have hq : q ∈ g.rev o := by rw [← hjgo]; exact hA.lst q pbq jg hqpre hpbq' hjg (hjgo ▸ hopre)
    have h0 : g.rev o ≠ [] := List.ne_nil_of_mem hq
    rw [if_neg h0] at hst
    obtain ⟨lq, mq, hlq, hmq, -, -, -⟩ := hI.ends q bq jq pbq hqpre hbq hjq hpbq'
    obtain ⟨himq, hnq⟩ := hA.ends q bq jq lq mq p' hqpre hbq hjq hlq hmq hπq
    refine ⟨fun n r hr => Or.inl (himq n r (ast_imms_sub him hq hmq n r hr)), ?_, hold⟩
    have hN := ast_start_names hst hq hlq
    exact (ast_pars_names (D := fun y => AvP bl G (q :: p') y ∨ y ∈ b.par) hlq
      (fun r i y hr hy => Or.inl (hnq r i y hr hy)) b.par edges info loc0 jg.args hpa
      (aedge_mem hed hq hpbq' hjg hjgo) (fun r i y hr hy => by
        obtain ⟨i', hi', hy'⟩ := hN r i y hr hy
        exact Or.inl (hnq r i' y hi' hy'))).1

/-- **`TAv` at a place of a walked block** before every dead fill, along a
path of `G` to it: the targets are available along the path, as parameters, or
as destinations of the ops kept so far. -/
theorem tav_pre {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {bl G : Map Blob}
    (hD : DInvS bl) (hGs : TargetsSub bl G) {nargs : Nat} {pre l : List Nat}
    {o : Nat} {g : AGen Map} (ht : TopoOK bl (pre ++ o :: l)) (hI : SInv bl (pre ++ o :: l) pre g)
    (hA : TInvA bl G pre g) (hGq : ∀ q ∈ pre, HoonMap.get G q = HoonMap.get g.new q) {b : Blob}
    (hb : HoonMap.get bl o = some b) {p : List Nat} (hπG : BPath G (o :: p))
    {info : AInfo} {imms : AImms} {edges : List (Nat × List (Option Nat))} {loc0 : AInfo}
    (hst : (if g.rev o = [] then some (entryInfo nargs) else aliasStart g o (g.rev o)) = some info)
    (him : aliasStartImms g (g.rev o) = some imms) (hed : aliasEdges g o (g.rev o) = some edges)
    (hpa : aliasPars g b.par edges info = some loc0) {m : Nat} (hm : ∀ k r, k < m → ¬ DeadFill bl r o k)
    {outa : List Pole} {sta : ABody}
    (hba : aliasBody pick (b.body.take m) ⟨g.old, loc0, imms⟩ = some (outa, sta)) :
    TAv sta (fun y => AvP bl G p y ∨ y ∈ b.par ∨ y ∈ outa.filterMap aliasDst)
      (bodyDone (ClR bl) (b.body.take m) (DoneS bl pre p b)) := by
  have hS : AliasSSAB bl := hD.2.1
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hπ : BPath bl (o :: p) := bpath_sub hGs hπG
  have hR : Reach bl o := ssk_bpath_reach hπ o List.mem_cons_self
  have hab0 := awa_abinv_mono (sst_start hS ht hI hb hR hst him hed hpa) (fun _ h => h)
    (fun x hx => sst_doneS ht hopre hπ hx)
  have hBO := awi_bodyOK hS hD.1.1.2.1 hπ hb hm hopre (Done := DoneS bl pre p b) (awi_doneS_body hopre)
  have hT0 := tav_start hS hGs ht hI hA hGq hb hπG hst him hed hpa
  refine tav_mono (tav_body hpick _ _ _ _ _ outa sta hba hab0 hBO hT0) (fun y hy => ?_) (fun _ h => h)
  rcases hy with (hy | hy) | hy
  · exact Or.inl hy
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr hy)

end

/-! ## The induction over `topo` and `DefFirst` of the result -/

section
variable [MapKeys Map] {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
  {rev : Map (List Nat)} {gF : AGen Map}

theorem sst_pre (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    {pre l : List Nat} {o : Nat} {g : AGen Map} (hto : topo = pre ++ o :: l)
    (h1 : aliasWalk pick nargs bl pre (aliasInit rev) = some g) : SInv bl (pre ++ o :: l) pre g := by
  subst hto
  have := sst_walk_part hpick hD pre [] (o :: l) _ g (by simpa using hT.1.1)
    (by simpa using sst_init (Map := Map) hT) h1
  simpa using this

/-- Every block of a path of the result is a block of the result. -/
theorem bpathG_some (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) :
    ∀ {L : List Nat}, BPath gF.new L → ∀ {x p}, L = x :: p → (HoonMap.get gF.new x).isSome
  | _, BPath.start, x, p, e => by
    cases e
    obtain ⟨_l, _g2, _b0, _st0, _rb, _rf, _e1, _e2, _e3, _e4, _e5, _e6, _e7, hg0⟩ := alias_zero hT.1.1 h
    rw [hg0]; rfl
  | _, BPath.step _ hb hj, x, p, e => by
    cases e
    exact alias_closed hT h hb hj

/-- The definitions of the result are definitions before. -/
theorem alias_allDefs (hT : TopoInvR bl topo rev) (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF)
    {r : Nat} (hr : r ∈ allDefs gF.new) : r ∈ allDefs bl := by
  unfold allDefs at hr
  obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp hr
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp ((MapKeys.mem_keys gF.new k).mp hk)
  rw [hb'] at hmem
  simp only [Option.map_some, Option.getD_some] at hmem
  obtain ⟨_pre, _l, _g1, _g2, b, _st0, rb, _rf, _e1, _e2, _e3, _e4, _e5, hb, _e7, hrb, _e9, _e10, rfl⟩ :=
    aw_new hT.1.1 hT.2 h hb'
  rcases List.mem_append.mp hmem with hm | hm
  · exact bdef_allDefs hb (List.mem_append_left _ hm)
  · exact bdef_allDefs hb (List.mem_append_right _ (abody_dsts hrb hm))

/-- **One block of the walk keeps `TInvA`.** -/
theorem tav_step (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) {pre l : List Nat} {o : Nat} {g g' : AGen Map}
    (hto : topo = pre ++ o :: l) (h1 : aliasWalk pick nargs bl pre (aliasInit rev) = some g)
    (h2 : aliasBlock pick nargs bl g o = some g') (hA : TInvA bl gF.new pre g) :
    TInvA bl gF.new (pre ++ [o]) g' := by
  have hS : AliasSSAB bl := hD.2.1
  have ht : TopoOK bl (pre ++ o :: l) := hto ▸ hT.1.1
  have hI := sst_pre hpick hD hT hto h1
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht.1).2.2 o h' o List.mem_cons_self rfl
  have hol : o ∉ l := fun h' => ((List.nodup_append.mp ht.1).2.1 |> List.nodup_cons.mp).1 h'
  have hoT : o ∈ pre ++ o :: l := List.mem_append_right _ List.mem_cons_self
  have hoo : o ∈ pre ++ [o] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have h3 : aliasWalk pick nargs bl l g' = some gF := by
    have e := h
    rw [hto, awa_walk_append, h1, Option.bind_some] at e
    simp only [aliasWalk, h2, Option.bind_some] at e
    exact e
  have hGs : TargetsSub bl gF.new := alias_targetsSub hT h
  have hGo : HoonMap.get gF.new o = HoonMap.get g'.new o := ((awk_walk l g' gF h3).2 o hol).2.2
  have hGq : ∀ q ∈ pre, HoonMap.get gF.new q = HoonMap.get g.new q := by
    intro q hq
    have hql : q ∉ l := fun h' => (List.nodup_append.mp ht.1).2.2 q hq q (List.mem_cons_of_mem _ h') rfl
    have hqo : q ≠ o := fun e => hopre (e ▸ hq)
    rw [((awk_walk l g' gF h3).2 q hql).2.2, ((awk_block h2).2 q hqo).2.2]
  have hinfo0 : g.info o = none := by
    rw [((awk_walk pre _ g h1).2 o hopre).1]; rfl
  have hnew0 : HoonMap.get g.new o = none := by
    cases e : HoonMap.get g.new o with
    | none => rfl
    | some _ => exact absurd (hI.news o (by rw [e]; rfl)) hopre
  -- the parts of the walk of `o` that a path of the result through `o` needs
  have walked : ∀ p, BPath gF.new (o :: p) → ¬ (g.rev o = [] ∧ o ≠ 0) := by
    intro p hπ hd
    have := bpathG_some hT h hπ rfl
    rw [hGo, sst_drop_new h2 hd, hnew0] at this
    cases this
  refine ⟨fun q pb j hq hpb hj hjn => ?_, fun q b j lq mq p hq hb hj hlq hmq hπ => ?_,
    fun d q b j p hq hb hj hdd hc hf hπ => ?_⟩
  · -- the edges of the walked blocks stay listed
    rcases List.mem_append.mp hq with hq | hq
    · have hqo : q ≠ o := fun e => hopre (e ▸ hq)
      rw [((awk_block h2).2 q hqo).2.2] at hpb
      exact awa_rev_keep h2 (hA.lst q pb j hq hpb hj (fun h' => hjn (List.mem_append_left _ h'))) hqo
    · have e := List.mem_singleton.mp hq
      subst e
      by_cases hd : g.rev q = [] ∧ q ≠ 0
      · rw [sst_drop_new h2 hd, hnew0] at hpb; cases hpb
      · obtain ⟨info, imms, b, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h2 hd
        subst e8
        simp only [HoonMap.get_put, if_true, Option.some.injEq] at hpb
        subst hpb
        obtain ⟨⟨j0, hj0, hj0t⟩, hkeep⟩ := afin_jmps e7 hj
        exact hkeep (by rw [← hj0t]; exact hI.pend q b j0 hoT hopre e3 hj0)
  · -- the facts at the end of a walked jumping block
    rcases List.mem_append.mp hq with hq | hq
    · have hqo : q ≠ o := fun e => hopre (e ▸ hq)
      obtain ⟨c1, c2, -⟩ := (awk_block h2).2 q hqo
      exact hA.ends q b j lq mq p hq hb hj (c1 ▸ hlq) (c2 ▸ hmq) hπ
    · have e := List.mem_singleton.mp hq
      subst e
      have hd := walked p hπ
      obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h2 hd
      rw [hb] at e3; cases e3
      subst e8
      simp only [as_upd_self, Option.some.injEq] at hlq hmq
      subst hlq hmq
      have hnf : ∀ k r, k < b.body.length → ¬ DeadFill bl r q k := fun k r _ hdf => by
        obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
        rw [hb] at hb3; cases hb3; rw [hu] at hj; simp [getJmps] at hj
      have hT0 := tav_pre hpick hD hGs ht hI hA hGq hb hπ e1 e2 e4 e5 hnf (by rw [List.take_length]; exact e6)
      have hGo' : HoonMap.get gF.new q = some { par := b.par, body := rb.1, fin := rf.1 } := by
        rw [hGo]; simp only [HoonMap.get_put, if_true]
      have lift : ∀ y, (AvP bl gF.new p y ∨ y ∈ b.par ∨ y ∈ rb.1.filterMap aliasDst) → AvP bl gF.new (q :: p) y := by
        intro y hy
        rcases hy with hy | hy | hy
        · exact AvP.mono (fun x hx => List.mem_cons_of_mem _ hx) hy
        · exact Or.inr ⟨q, List.mem_cons_self, _, hGo', List.mem_append_left _ hy⟩
        · exact Or.inr ⟨q, List.mem_cons_self, _, hGo', List.mem_append_right _ hy⟩
      exact ⟨fun n r hr => lift r (hT0.imm n r hr), fun r i x hr hx => lift x (hT0.names r i x hr hx)⟩
  · -- the `old` of the definitions of a walked jumping block
    have hπb : BPath bl (q :: p) := bpath_sub hGs hπ
    have hRq : Reach bl q := ssk_bpath_reach hπb q List.mem_cons_self
    rcases List.mem_append.mp hq with hq | hq
    · have hqo : q ≠ o := fun e => hopre (e ▸ hq)
      have hlive : ∃ s, LiveDef bl d s ∧ s.1 = q := by
        rcases List.mem_append.mp hdd with hm | hm
        · exact ⟨(q, none), awi_par_live hRq hb hm, rfl⟩
        · obtain ⟨i, op, hi, he⟩ := bdef_idx hm
          exact ⟨(q, some i), awi_jump_live hRq hb hj hi he, rfl⟩
      obtain ⟨s, hs, hsq⟩ := hlive
      rw [awi_frame_step ht hI.rev h2 (fun hR b' hb' hm => by
        obtain ⟨k, op, hk, he⟩ := bdef_idx hm
        by_cases hdf : DeadFill bl d o k
        · exact hf o k hdf hoo
        · have e := hS.1 d s (o, some k) hs ⟨hR, ⟨b', op, hb', hk, he⟩, fun i hi => by cases hi; exact hdf⟩
          rw [e] at hsq
          exact hqo hsq.symm)]
      exact hA.glob d q b j p hq hb hj hdd hc (fun o' i hdf ho' => hf o' i hdf (List.mem_append_left _ ho')) hπ
    · have e := List.mem_singleton.mp hq
      subst e
      have hd := walked p hπ
      obtain ⟨info, imms, b1, edges, loc0, rb, rf, e1, e2, e3, e4, e5, e6, e7, e8⟩ := awa_block_parts h2 hd
      rw [hb] at e3; cases e3
      subst e8
      have hGo' : HoonMap.get gF.new q = some { par := b.par, body := rb.1, fin := rf.1 } := by
        rw [hGo]; simp only [HoonMap.get_put, if_true]
      show AvP bl gF.new (q :: p) (rb.2.old d)
      rcases List.mem_append.mp hdd with hm | hm
      · -- a parameter keeps its own name
        have hnd : d ∉ b.body.filterMap aliasDst := fun hm2 => by
          obtain ⟨k, op, hk, he⟩ := bdef_idx hm2
          by_cases hdf : DeadFill bl d q k
          · exact hf q k hdf hoo
          · have e := hS.1 d (q, none) (q, some k) (awi_par_live hRq hb hm)
              ⟨hRq, ⟨b, op, hb, hk, he⟩, fun i hi => by cases hi; exact hdf⟩
            simp at e
        rw [awk_body_old b.body _ rb.1 rb.2 e6 d hnd]
        dsimp only
        rw [awi_self hS ht hI.oldw hc (awi_par_notDefW hS.1 hRq hb hm hopre)]
        exact Or.inr ⟨q, List.mem_cons_self, _, hGo', List.mem_append_left _ hm⟩
      · have hnf : ∀ k r, k < b.body.length → ¬ DeadFill bl r q k := fun k r _ hdf => by
          obtain ⟨b3, hb3, ⟨u, hu⟩, -⟩ := hdf
          rw [hb] at hb3; cases hb3; rw [hu] at hj; simp [getJmps] at hj
        have hT0 := tav_pre hpick hD hGs ht hI hA hGq hb hπ e1 e2 e4 e5 hnf (by rw [List.take_length]; exact e6)
        rw [List.take_length] at hT0
        rcases hT0.old d (awa_bodyDone_dst _ _ _ hm hc) with hy | hy | hy
        · exact AvP.mono (fun x hx => List.mem_cons_of_mem _ hx) hy
        · exact Or.inr ⟨q, List.mem_cons_self, _, hGo', List.mem_append_left _ hy⟩
        · exact Or.inr ⟨q, List.mem_cons_self, _, hGo', List.mem_append_right _ hy⟩
end

end Opt
end SkaModel
end Formalization
