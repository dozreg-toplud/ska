import lemmas.Ska.RawInvCLSARunSteps

/-!
# Single assignment with calls: the counts of `+kerf` and `+collapse-lazy-atom`

README Gaps 14 (b), track D.  Two fields of `SarStepsW` (`RawInvCLSARun.lean`).

* `sckf_both`, **`sckf_loop`** (`+kern-need`: the ops' definitions are the
  need's registers, with repetitions, and fresh ones), `sckf_proxy`,
  `sckf_ops`, `sckf_gate` (the gate of `+kern` consumes its entry's need),
  **`sckf_kerf`**: the field `kerf`.
* `sccl_srl` (`+sure-require-look` on `this r` adds only fresh registers
  besides `r`), `sccl_root` (the root gate of `+collapse-lazy-atom` defines
  nothing of `r`), `sccl_gate` (the other gates consume their entry's need),
  `sccl_walk`, **`sccl_collapse`**: the field `collapse`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-! ## `+kern-need` -/

/-- What a run of `+kern-need` from `acc` does: ops `A` in front of `acc`,
no trace op, only `re` grows, and the ops define the registers `l` and fresh
ones. -/
def sckfK (l : List Nat) (acc ops : List Pole) (g g' : Comp.Gen Map) : Prop :=
  ∃ A, ops = A ++ acc ∧ g' = { g with re := g'.re } ∧ g.re ≤ g'.re ∧ (∀ op ∈ A, trOp op = false) ∧
    ∀ y, (defsOf A).count y ≤ l.count y + fr g.re g'.re y

theorem sckf_fr1 (a y : Nat) : ([a] : List Nat).count y = fr a (a + 1) y := by
  unfold fr
  by_cases h : a = y
  · subst h; simp
  · rw [List.count_singleton]
    have : ¬ (a ≤ y ∧ y < a + 1) := fun h' => h (by omega)
    simp [h, this]

theorem sckf_ifc {c : Prop} [Decidable c] (p : Pole) (x : Nat) (hp : aliasDst p = some x) (l : List Pole) (y : Nat) :
    (defsOf (if c then p :: l else l)).count y ≤ (defsOf l).count y + ([x] : List Nat).count y := by
  split
  · rw [defsOf_cons, hp, Option.toList_some, List.count_append]; omega
  · omega

theorem sckf_both {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)} {lh lt : List Nat}
    (Kh : ∀ x acc g g' ops, kh x acc g = some (ops, g') → sckfK (Map := Map) lh acc ops g g')
    (Kt : ∀ x acc g g' ops, kt x acc g = some (ops, g') → sckfK (Map := Map) lt acc ops g g')
    {acc ops : List Pole} {g g' : Comp.Gen Map} (hk : kernBoth r d kh kt acc g = some (ops, g')) :
    sckfK (Map := Map) (d :: (lh ++ lt)) acc ops g g' := by
  simp only [kernBoth] at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨ops1, g2, h2, hk⟩ := bind_some hk
  obtain ⟨At, rfl, e2, l2, t2, c2⟩ := Kt _ _ _ _ _ h2
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  rw [re_apply] at h3; simp only [Option.some.injEq, Prod.mk.injEq] at h3; obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨ops3, g4, h4, hk⟩ := bind_some hk
  obtain ⟨Ah, eAh, e4, l4, t4, c4⟩ := Kh _ _ _ _ _ h4
  by_cases hrd : r = d
  · simp [hrd] at hk; cases hk
  simp only [hrd, if_false, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  simp only at l2 l4 c2 c4
  have eT : (if At ++ acc ≠ acc then Pole.tal d g.re :: (At ++ acc) else At ++ acc) =
      (if At = [] then [] else Pole.tal d g.re :: At) ++ acc := by
    by_cases e : At = [] <;> simp [e]
  rw [eT] at eAh
  have eH : (if ops3 ≠ (if At = [] then [] else Pole.tal d g.re :: At) ++ acc then Pole.hed d g2.re :: ops3 else ops3)
      = (if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++ ((if At = [] then [] else Pole.tal d g.re :: At) ++ acc) := by
    rw [eAh]; by_cases e : Ah = [] <;> simp [e]
  rw [eT, eH]
  refine ⟨Pole.mov r d :: Pole.cel d :: ((if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++
    (if At = [] then [] else Pole.tal d g.re :: At)), by simp, ?_, by omega, ?_, fun y => ?_⟩
  · rw [e4, e2]
  · intro op hop
    simp only [List.mem_cons, List.mem_append] at hop
    rcases hop with rfl | rfl | hop | hop
    · rfl
    · rfl
    · split at hop
      · exact absurd hop List.not_mem_nil
      · rcases List.mem_cons.mp hop with rfl | hop
        · rfl
        · exact t4 op hop
    · split at hop
      · exact absurd hop List.not_mem_nil
      · rcases List.mem_cons.mp hop with rfl | hop
        · rfl
        · exact t2 op hop
  · have hA : ∀ (p : Pole) (x : Nat) (B : List Pole), aliasDst p = some x →
        (defsOf (if B = [] then [] else p :: B)).count y ≤ (defsOf B).count y + ([x] : List Nat).count y := by
      intro p x B hp
      split
      · simp [defsOf]
      · rw [defsOf_cons, hp, Option.toList_some, List.count_append]; omega
    have a1 := hA (Pole.tal d g.re) g.re At rfl
    have a2 := hA (Pole.hed d g2.re) g2.re Ah rfl
    have f1 := sckf_fr1 g.re y
    have f2 := sckf_fr1 g2.re y
    have q1 := fr_add (Nat.le_add_right g.re 1) l2 y
    have q2 := fr_add (Nat.le_add_right g2.re 1) l4 y
    have q3 := fr_add (Nat.le_trans (Nat.le_add_right g.re 1) l2) (Nat.le_trans (Nat.le_add_right g2.re 1) l4) y
    have : (defsOf (Pole.mov r d :: Pole.cel d :: ((if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++
        (if At = [] then [] else Pole.tal d g.re :: At)))).count y =
        ([d] : List Nat).count y + ((defsOf (if Ah = [] then [] else Pole.hed d g2.re :: Ah)).count y +
          (defsOf (if At = [] then [] else Pole.tal d g.re :: At)).count y) := by
      rw [defsOf_cons, defsOf_cons, defsOf_append]
      simp only [aliasDst, Option.toList_some, Option.toList_none, List.nil_append, List.count_append]
    rw [this]
    have e5 : (d :: (lh ++ lt)).count y = ([d] : List Nat).count y + (lh.count y + lt.count y) := by
      rw [← List.singleton_append, List.count_append, List.count_append]
    rw [e5]
    have := c2 y
    have := c4 y
    omega

/-- **The loop of `+kern-need`**: its ops define the need's registers (with
repetitions) and fresh ones, with no hypothesis. -/
theorem sckf_loop : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Comp.Gen Map) (ops : List Pole),
    kernLoop r tgt acc g = some (ops, g') → sckfK (Map := Map) (flattenNeed tgt) acc ops g g' := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, Nat.le_refl _, fun _ h => absurd h List.not_mem_nil, fun y => by simp [defsOf]⟩
  | this d =>
    intro r acc g g' ops h
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[Pole.mov r d], rfl, rfl, Nat.le_refl _, fun op hop => ?_, fun y => ?_⟩
    · simp at hop; subst hop; rfl
    · simp [defsOf, aliasDst, flattenNeed]
  | pair p q ihp ihq =>
    intro r acc g g' ops h
    simp only [kernLoop] at h
    obtain ⟨rn, g1, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨A, eA, e1, l1, t1, c1⟩ := sckf_both (fun x acc g g' ops h => ihp x acc g g' ops h)
      (fun x acc g g' ops h => ihq x acc g g' ops h) h
    refine ⟨A, eA, e1, by simp only at l1; omega, t1, fun y => ?_⟩
    have := c1 y
    simp only at this
    have f1 := sckf_fr1 g.re y
    have hq := fr_add (Nat.le_add_right g.re 1) l1 y
    have e5 : (g.re :: (flattenNeed p ++ flattenNeed q)).count y =
        ([g.re] : List Nat).count y + ((flattenNeed p).count y + (flattenNeed q).count y) := by
      rw [← List.singleton_append, List.count_append, List.count_append]
    rw [e5] at this
    simp only [flattenNeed, List.count_append]
    omega
  | both d h t ihh iht =>
    intro r acc g g' ops hk
    simp only [kernLoop] at hk
    exact sckf_both (fun x acc g g' ops h => ihh x acc g g' ops h) (fun x acc g g' ops h => iht x acc g g' ops h) hk

/-! ## The gate of `+kern` -/

theorem sckf_proxy (ri : List Nat) (r o : Nat) : SCR (Map := Map) ri (proxy r o) (fun _ => ri) := by
  intro g x g' s e
  unfold proxy at e
  simp only [s.drop, Bool.false_eq_true, if_false] at e
  obtain ⟨tag, -, he⟩ := Option.map_eq_some_iff.mp e
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨⟨rfl, s.lab, s.tr, s.args⟩, Nat.le_succ _, fun y => Nat.le_add_right _ _⟩

theorem sckf_ops (src : Nat) (ned : Need) (o : Nat) :
    SCR (Map := Map) (flattenNeed ned) (kernNeed src ned >>= fun ops => addOps o ops) (fun _ => []) := by
  intro g x g' s e
  obtain ⟨ops, g1, h1, h2⟩ := bind_some e
  obtain ⟨A, eA, e1, l1, t1, c1⟩ := sckf_loop ned src [] g g1 ops h1
  rw [List.append_nil] at eA
  subst eA
  have s1 : SarSt g1 := by rw [e1]; exact ⟨s.drop, s.lab, s.tr, s.args⟩
  obtain ⟨s2, l2, c2⟩ := sc_addOps (Map := Map) (o := o) (ri := defsOf ops) (ro := []) t1
    (fun y => by simp) g1 x g' s1 h2
  refine ⟨s2, Nat.le_trans l1 l2, fun y => ?_⟩
  have hb : g1.blocks = g.blocks := by rw [e1]
  have := c1 y
  have := c2 y
  have := fr_add l1 l2 y
  rw [hb] at *
  simp only [List.count_nil] at *
  omega

/-- **The gate of `+kern` consumes its entry's need.** -/
theorem sckf_gate (r o oLaz : Nat) (sur : Sure S) :
    SCR (Map := Map) (flattenNeed sur.ned) (kernGate r o oLaz sur) (fun _ => []) := by
  unfold kernGate
  refine sc_bind (sc_sureRequireLook sur) fun ned => ?_
  refine sc_ite _ (sc_pure fun _ => by simp) ?_
  refine sc_bind (r1 := fun _ => flattenNeed ned) (sc_ite _ (sc_pure fun _ => Nat.le_refl _) (sckf_proxy _ _ _))
    fun src => ?_
  exact sc_ite _ sc_fail (sckf_ops src ned oLaz)

/-- **The field `kerf`.** -/
theorem sckf_kerf : ∀ (nex : NextL S), nex.th.args = [] →
    SCR (Map := Map) (sarR nex.laz) (kerf nex) (fun x => [x.2]) := by
  intro nex ha
  unfold kerf
  refine sc_bind (sc_emit (ro := sarR nex.laz) (by simp) (by simp [getJmps, ha]) fun y => by simp [blockDefs])
    fun o => ?_
  refine sc_bind (r1 := fun r => [r]) ?_ fun r => sc_pure fun y => Nat.le_refl _
  rw [kern_eq]
  refine sc_bind (sc_re _) fun r => ?_
  refine sc_bind (sc_get _) fun g => ?_
  refine sc_ite _ (sc_pure fun y => by simp [List.count_append]) ?_
  refine sc_bind (sc_mono (sc_frame (sc_walkLazy (fun oL s => sckf_gate r o oL s) o nex.laz) [r])
    (ri' := sarR nex.laz ++ [r]) (ro' := fun _ => [r]) (fun _ => Nat.le_refl _) (fun _ _ => by simp)) fun _ => ?_
  exact sc_pure fun _ => Nat.le_refl _

/-! ## `+collapse-lazy-atom` -/

/-- `+sure-require-look` on `this r` adds only fresh registers besides `r`. -/
theorem sccl_srl (r : Nat) (lok : S) :
    SCR (Map := Map) [] (sureRequireLook (⟨Need.this r, lok⟩ : Sure S)) (fun n => (flattenNeed n).filter (· != r)) := by
  intro g x g' s e
  obtain ⟨s1, l1, c1⟩ := sc_sureRequireLook (Map := Map) (⟨Need.this r, lok⟩ : Sure S) g x g' s e
  obtain ⟨k, hk⟩ := (sureRequireLook_spec e).gen
  have hb : g'.blocks = g.blocks := by rw [hk]
  refine ⟨s1, l1, fun y => ?_⟩
  have := c1 y
  rw [hb] at this ⊢
  simp only [flattenNeed, List.count_singleton] at this
  by_cases hy : y = r
  · subst hy
    have : ((flattenNeed x).filter (· != y)).count y = 0 :=
      List.count_eq_zero.mpr fun hm => by simp at hm
    rw [this]; simp
  · have : ((flattenNeed x).filter (· != r)).count y = (flattenNeed x).count y := by
      rw [List.count_filter]; simp [hy]
    rw [this]
    simp [Ne.symm hy] at *
    omega

theorem sccl_crash (o p : Nat) (ned : Need) :
    SCR (Map := Map) ((flattenNeed ned).filter (· != p)) (crashNeed o (Sum.inr p) ned) (fun _ => []) := by
  simp only [crashNeed]
  refine sc_addOps (fun op hop => by
    simp only [List.mem_cons, List.mem_map] at hop
    rcases hop with rfl | ⟨x, -, rfl⟩ <;> rfl) fun y => ?_
  have e : defsOf (Pole.cel p :: ((flattenNeed ned).filter (· != p)).map fun x => Pole.imm (A 0) x) =
      (flattenNeed ned).filter (· != p) := sar_fm_imm _ _
  rw [e]
  simp

/-- **The root gate of `+collapse-lazy-atom` defines nothing of `r`.** -/
theorem sccl_root (r o : Nat) (lok : S) :
    SCR (Map := Map) [] (collapseGate r o o (⟨Need.this r, lok⟩ : Sure S)) (fun _ => []) := by
  unfold collapseGate
  refine sc_bind (sccl_srl r lok) fun ned => ?_
  cases ned with
  | none => exact sc_pure fun _ => by simp
  | this r' =>
    by_cases hr : r = r'
    · simp only [hr, if_true]; exact sc_pure fun _ => by simp
    · simp only [hr, if_false, if_true, pure_bind]
      refine sc_addOps (by simp [trOp]) fun y => ?_
      have : (r' != r) = true := by simp [Ne.symm hr]
      simp [defsOf, aliasDst, flattenNeed, List.filter, this]
  | pair a b =>
    simp only [if_true, pure_bind]
    exact sccl_crash o r _
  | both x a b =>
    simp only [if_true, pure_bind]
    exact sccl_crash o r _

/-- **A gate of `+collapse-lazy-atom` consumes its entry's need.** -/
theorem sccl_gate (r o oLaz : Nat) (sur : Sure S) :
    SCR (Map := Map) (flattenNeed sur.ned) (collapseGate r o oLaz sur) (fun _ => []) := by
  unfold collapseGate
  refine sc_bind (sc_sureRequireLook sur) fun ned => ?_
  have hsrc : ∀ (L : List Nat), SCR (Map := Map) L (if oLaz = o then pure r else proxy r oLaz : CM Map Nat)
      (fun _ => L) := fun L => sc_ite _ (sc_pure fun _ => Nat.le_refl _) (sckf_proxy _ _ _)
  cases ned with
  | none => exact sc_pure fun _ => by simp
  | this r' =>
    refine sc_ite _ (sc_pure fun _ => by simp) ?_
    exact sc_bind (hsrc _) fun src => sc_addOps (by simp [trOp]) fun y => by simp [defsOf, aliasDst, flattenNeed]
  | pair a b =>
    exact sc_bind (hsrc _) fun src => sc_crashNeed oLaz _ _
  | both x a b =>
    exact sc_bind (hsrc _) fun src => sc_crashNeed oLaz _ _

theorem sccl_walk (r there : Nat) (lok : S) (fk : List (ForkE S)) (bd : List (Nat × Lazy S)) :
    SCR (Map := Map) (r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk)))
      (walkLazy (collapseGate r there) there (mk ⟨Need.this r, lok⟩ fk bd)) (fun _ => [r]) := by
  rw [walkLazy]
  have hf : ∀ (o : Nat) (s : Sure S), SCR (Map := Map) (flattenNeed s.ned) (collapseGate r there o s) (fun _ => []) :=
    fun o s => sccl_gate r there o s
  refine sc_bind (sc_mono (sc_frame (sccl_root r there lok) (r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk))))
    (ri' := r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk)))
    (ro' := fun _ => r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk))) (fun y => by simp)
    (fun _ y => by simp)) fun _ => ?_
  refine sc_ite _ (sc_pure fun y => ?_) ?_
  · simp only [List.count_cons, List.count_append, List.count_nil]; omega
  refine sc_bind (sc_mono (sc_walkForks hf fk (L := r :: regsL (bondEntries bd)))
    (ri' := r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk))) (ro' := fun _ => r :: regsL (bondEntries bd))
    (fun y => by simp only [List.count_cons, List.count_append]; omega) (fun _ _ => Nat.le_refl _)) fun _ => ?_
  exact sc_mono (sc_frame (sc_walkBonds hf bd) [r]) (ri' := r :: regsL (bondEntries bd)) (ro' := fun _ => [r])
    (fun y => by simp only [List.count_cons, List.count_append, List.count_singleton, List.count_nil]; omega)
    (fun _ y => by simp)

/-- **The field `collapse`.** -/
theorem sccl_collapse : ∀ (nex : NextL S), SCR (Map := Map) (sarR nex.laz) (collapseLazyAtomL nex)
    (fun a => match a with | some x => [x.1] | Option.none => []) := by
  rintro ⟨⟨s, fk, bd⟩, th⟩
  unfold collapseLazyAtomL
  refine sc_ite _ sc_fail ?_
  refine sc_ite _ (sc_pure fun y => by simp) ?_
  rw [sarR_mk]
  refine sc_bind (sc_frame (sc_sureRequireLook s) (regsL (bondEntries bd) ++ regsL (forkEntries fk))) fun ned => ?_
  refine sc_bind (r1 := fun p : Nat × Nat => p.1 :: (regsL (bondEntries bd) ++ regsL (forkEntries fk))) ?_
    fun p => ?_
  · cases ned with
    | this r => exact sc_pure fun y => by simp [flattenNeed]
    | none =>
      exact sc_bind (sc_re _) fun r => sc_pure fun y => by
        simp only [flattenNeed, List.nil_append, List.count_cons, List.count_append, List.count_singleton,
          List.count_nil]; omega
    | pair a b =>
      refine sc_bind (sc_re _) fun r => ?_
      refine sc_bind (sc_emit (ro := r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk))) (by simp)
        (by simp [getJmps]) fun y => ?_) fun o => sc_pure fun y => Nat.le_refl _
      simp only [blockDefs, List.append_nil, List.count_nil, Nat.zero_add, List.filterMap_nil, flattenNeed,
        List.count_cons, List.count_append, List.count_singleton]
      omega
    | both r a b =>
      refine sc_bind (sc_emit (ro := r :: (regsL (bondEntries bd) ++ regsL (forkEntries fk))) (by simp)
        (by simp [getJmps]) fun y => ?_) fun o => sc_pure fun y => Nat.le_refl _
      simp only [blockDefs, List.append_nil, List.count_nil, Nat.zero_add, List.filterMap_nil, flattenNeed,
        List.cons_append, List.count_cons, List.count_append]
      omega
  · obtain ⟨r, there⟩ := p
    refine sc_bind (sc_get _) fun g => sc_ite _ (sc_pure fun y => ?_) ?_
    · simp only [List.count_cons, List.count_append, List.count_nil]; omega
    · exact sc_bind (sccl_walk r there s.lok fk bd) fun _ => sc_pure fun _ => Nat.le_refl _

end Raw
end SkaModel
end Formalization
