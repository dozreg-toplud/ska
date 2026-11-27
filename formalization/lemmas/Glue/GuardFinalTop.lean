import lemmas.Glue.GuardFinal
import lemmas.Glue.GuardTop

/-!
# `GuardFinalU`, `GuardFinalF` proved; `CompHyp` on `FragX` with no guard leaf (track G, step 6)

* **`guardFinalU`**: the whole-subject final pass.  `+kerf` emits a hop block
  to the run's entry (it passes no `~`: `JOK`), `+kern` walks the lazy tree
  under track D's `KI` (`kernListG`), and `+to-straight` takes its map path,
  which on the run `[sub]` is the renaming path by `renReg ∘ unproxy`
  (`toStraightF_run`).  `RenOK` holds: `unproxy` fixes every defined register
  (no defined register is a key of `cond`, `KI`) and sends every other one to
  itself or to `sub`, which is not defined (`KI`); `renReg` is injective.
* **`guardFinalF`**: the n-ary final pass.  `+need-ord-alloc-regs` only takes
  registers; `+coerce-lazy` goes entry by entry under track D's `CoI`
  (`coerceLazyLG`); the `+add-ops` of `[]` changes no body; `+to-straight`
  takes its renaming path (no proxies: `cond` stays empty, `R.cnd`; the
  inputs are a run, `isRun_needOrdAllocRegs`) by the injective `renReg`.
* **`guardMonoX`, `guardNaryX`**, and **`compHyp_of_fragX₃`**: `CompHyp` on
  `FragX` from `CompRestOE` alone.

The proof of `guardFinalU` follows track D's `optIn_finishLUX`
(`RawInvWholeX.lean`) up to the end of the walk, with `BlocksOK` carried
along; that of `guardFinalF` follows `optIn_finishLFX_of` (`RawInvFinishX.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Opt Comp Raw Lazy

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

variable {S : Type} [Comp.HoonSet S]

/-- **The whole-subject final pass keeps the guard.** -/
theorem guardFinalU : GuardFinalU S Map := by
  intro nm nex g1 g2 o sub c hf hc h1 hI hJ h2 h
  have R : RunOKP (Map := Map) lib0 nm (CGoal.done : CGoal S) gen0 g1 nex :=
    (runX_ok lib0 hf).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
  obtain ⟨LA, LD⟩ := lazOK_run hf hc h1
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := runX_rawIHX_up (S := S) (Map := Map) hf CGoal.done [] gen0 g1 nex
    (fun _ _ => False) (KVan.none _) sip_gen0X trivial trivial trivial trivial (fun _ _ e => e) hc trivial h1
  have hcnd : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by
    rw [R.cnd]; simp [gen0, HoonMap.get_empty]
  -- `+kerf`: the hop block
  simp only [kerf] at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  have gee : ge = g1.emitted ⟨[], [], Termin.hop nex.th⟩ := by
    have he' := he
    rw [emit_apply] at he'
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    exact he'.2.symm
  obtain ⟨Se, eo, ee, qe, boe⟩ := sip_emit S1 (emitOK_hop a1 hi1) he
  obtain ⟨r, g3, h3, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨e2o, e2s⟩, e2g⟩ := h2
  subst e2o e2s e2g eo
  rw [kern_eq] at h3
  obtain ⟨r0, g5, h5, h3⟩ := bind_some h3
  have c5 : g5.cond = g1.cond := by
    rw [re_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    rw [← h5.2, gee]; rfl
  obtain ⟨S5, er0, q5, b5, o5⟩ := sip_re Se h5
  subst er0
  obtain ⟨g6, g6', h6, h3⟩ := bind_some h3
  rw [get_apply] at h6
  simp only [Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rw [S5.drop] at h3
  simp only [Bool.false_eq_true, if_false] at h3
  obtain ⟨⟨⟩, g7', h7, h3⟩ := bind_some h3
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨e3r, e3g⟩ := h3
  subst e3r
  rw [walkLazy_flat, e3g] at h7
  have h7' : walkList (kernGate ge.re g1.bo) ((g1.bo, nex.laz) :: wentries nex.laz) g5 = some ((), g3) := by
    simp only [walkList]; exact h7
  -- the state before the walk (as in `optIn_finishLUX`)
  have hbo5 : HoonMap.get g5.blocks g1.bo = some ⟨[], [], Termin.hop nex.th⟩ := by rw [b5, ee]; exact get_put_self
  have below5 : ∀ k, k < g1.bo → HoonMap.get g5.blocks k = HoonMap.get g1.blocks k := fun k hk => by
    rw [b5, ee, get_put_ne (by omega)]
  have dd5 : ∀ y, Defd g5.blocks y ↔ Defd g1.blocks y := fun y => by
    rw [b5, ee, defd_put (S1.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have I0 : KI (S := S) Xup (upRk g1.blocks) g1.bo ge.re ((g1.bo, nex.laz) :: wentries nex.laz) g5 := by
    refine ⟨S5, by omega, fun k v hv => ?_, fun y _ => by rw [c5, hcnd], fun d => ?_, ?_, fun e he => ?_⟩
    · rw [c5, hcnd] at hv; cases hv
    · have := S1.defd_lt ((dd5 _).mp d); omega
    · have LA' := List.pairwise_cons.mp LA
      exact needsApart_perm ((wentries_perm nex.laz).symm.cons _) (List.pairwise_cons.mpr ⟨LA'.1, LA'.2⟩)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨⟨_, hbo5⟩, R.dist, fun y hy => ⟨by have := (R.regs y hy).2; omega,
          fun d => LD (nex.th.there, nex.laz) List.mem_cons_self y hy ((dd5 y).mp d)⟩⟩
      · have hm : e ∈ entries nex.laz := (wentries_perm nex.laz).mem_iff.mp he'
        obtain ⟨-, lt, th', hb⟩ := R.labs e hm
        exact ⟨⟨_, by rw [below5 _ (by omega)]; exact hb⟩, (R.eregs e hm).1, fun y hy =>
          ⟨by have := ((R.eregs e hm).2 y hy).2; omega,
            fun d => LD e (List.mem_cons_of_mem _ hm) y hy ((dd5 y).mp d)⟩⟩
  -- the guard before the walk: the run's blocks and the hop block
  have B5 : BlocksOK g5.blocks := by
    rw [b5, ee]
    refine blocksOK_put hI.1 ⟨fun j hj => ?_, guardedBody_nil⟩
    simp only [getJmps, List.mem_singleton] at hj
    subst hj; exact hJ
  have B3 := kernListG ge.re g1.bo _ g5 g3 I0 B5 h7'
  obtain ⟨I7, -⟩ := kernList_prep ge.re g1.bo _ g5 g3 I0 h7'
  obtain ⟨S7, -, ck7, dk7, ns7, -, -⟩ := I7
  -- the final pass: the map path is the renaming path by `renReg ∘ unproxy`
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at h
  simp only [flattenNeed, List.headD, List.length] at h
  obtain ⟨start, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  generalize hu : (fun r => if hasProxies g3.cond then unproxy g3.cond r else r) = u
  have uN : ∀ x, HoonMap.get g3.cond x = Option.none → u x = x := fun x hx => by
    rw [← hu]; simp only; split
    · exact unproxy_none hx
    · rfl
  have uK : ∀ x v, HoonMap.get g3.cond x = some v → u x = v.1 := fun x v hx => by
    have hp : hasProxies g3.cond = true := by
      unfold hasProxies
      cases e : HoonMapKeys.keys g3.cond with
      | nil =>
        have := (HoonMapKeys.mem_keys g3.cond x).mpr (by simp [hx])
        rw [e] at this; cases this
      | cons _ _ => rfl
    rw [← hu]; simp only [hp, if_true, unproxy, hx]
  have uD : ∀ x, Defd g3.blocks x → u x = x := fun x d => uN x (dk7 x d)
  have hpr : proxRen g3.cond (hasProxies g3.cond) (renReg ge.re 1) = renReg ge.re 1 ∘ u := by
    rw [← hu]; rfl
  rw [hpr] at hnew
  have BN := blocksOK_rename (blocksOK_start B3 hst) (fun k b hb q hq x hx s e => ?_) hnew
  · exact ⟨noPoison_of_blocksOK BN, celGuard_of_blocksOK BN⟩
  -- `RenOK`: a written register is defined, so fixed; any other goes to itself or to `sub`
  have hk : ∃ k', HoonMap.get g3.blocks k' = some b := by
    rw [HoonMap.get_put] at hb
    split at hb
    · cases hb; exact ⟨_, hst⟩
    · rw [HoonMap.get_del] at hb
      split at hb
      · cases hb
      · exact ⟨_, hb⟩
  obtain ⟨k', hk'⟩ := hk
  have dx : Defd g3.blocks x :=
    defd_iff.mpr ⟨k', b, hk', by simp only [blockDefs, List.mem_append, List.mem_filterMap]; exact Or.inr ⟨q, hq, hx⟩⟩
  have eu : u x = u s := renReg_inj ge.re 1 _ _ e
  rw [uD x dx] at eu
  cases ec : HoonMap.get g3.cond s with
  | none => rw [uN s ec] at eu; exact eu
  | some v =>
    rw [uK s v ec, (ck7 s v ec).2.2] at eu
    subst eu; exact absurd dx ns7

/-- **The n-ary final pass keeps the guard.** -/
theorem guardFinalF : GuardFinalF S Map := by
  intro nm ord less bake nex g1 g2 g3 g4 nedF c hf hc hbake h1 hI hJ hargs h2 h3 h4 h
  have R : RunOKP (Map := Map) lib0 nm (CGoal.done : CGoal S) gen0 g1 nex :=
    (runX_ok lib0 hf).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
  obtain ⟨LA, LD⟩ := lazOK_run hf hc h1
  obtain ⟨S1, -, -, -, -⟩ := runX_rawIHX_up (S := S) (Map := Map) hf CGoal.done [] gen0 g1 nex (fun _ _ => False)
    (KVan.none _) sip_gen0X trivial trivial trivial trivial (fun _ _ e => e) hc trivial h1
  have hr := isRun_needOrdAllocRegs h2
  have c2 := (kc_needOrdAllocRegs ord).keep g1 nedF g2 h2
  have c3 := (kc_coerceLazyL nedF less _ _).keep g2 () g3 h3
  -- the input need (as in `optIn_finishLFX_of`)
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  subst e2
  have l2' : g1.re ≤ k2 := l2
  have I0 : CoI (Xup (Map := Map)) (upRk g1.blocks) g1.bo nedF k2 ((nex.th.there, nex.laz) :: entries nex.laz)
      { g1 with re := k2 } := by
    refine ⟨sip_reg S1 l2, Nat.le_refl _, fun r hr => ⟨(mF r hr).2, fun d => ?_⟩, LA, fun e he => ?_⟩
    · have := S1.defd_lt d; have := (mF r hr).1; omega
    · have rg : ∀ r, NMem e.2.sure.ned r → r < g1.re := fun r hr => by
        rcases List.mem_cons.mp he with rfl | he'
        · exact (R.regs r hr).2
        · exact ((R.eregs e he').2 r hr).2
      refine ⟨?_, ?_, fun r hr => ⟨by have := rg r hr; omega, fun m => ?_, LD e he r hr⟩⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · rcases R.ent with ⟨b, hb, -, -⟩ | hj
          · exact ⟨b, hb⟩
          · exact hj.elim
        · obtain ⟨-, -, th, hb⟩ := R.labs e he'
          exact ⟨_, hb⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · exact R.dist
        · exact (R.eregs e he').1
      · have := rg r hr; have := (mF r m).1; omega
  -- `+coerce-lazy`
  have B3 := coerceLazyLG I0 hI.1 h3
  -- the empty bake
  rw [hbake] at h4 h
  dsimp only at h4 h
  simp only [List.map_nil] at h4
  have c4 := (KC.addOps' _ _).keep g3 () g4 h4
  have B4 : BlocksOK g4.blocks := (addOps_ok B3 guardedBody_nil h4).1
  -- `+to-straight`: no proxies, a run of inputs, so the renaming path by `renReg`
  rw [toStraightF_eq (fun k => by rw [c4, c3, c2, R.cnd]; exact HoonMap.get_empty k) hr] at h
  unfold toStraight at h
  simp only [hr, Bool.true_eq_false, if_false] at h
  obtain ⟨start, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  have BN := blocksOK_rename (blocksOK_start B4 hst) (fun k b hb q hq x hx s e => renReg_inj _ _ _ _ e) hnew
  exact ⟨noPoison_of_blocksOK BN, celGuard_of_blocksOK BN⟩

theorem guardMonoX : GuardMonoX S Map := guardMonoX_of guardFinalU

theorem guardNaryX : GuardNaryX S Map := guardNaryX_of guardFinalF

section
variable (A : Arms M Map J H CR)

/-- **`CompHyp` when every nomm compiled is in `FragX`**, with no guard
leaf left: from `CompRestOE` alone. -/
theorem compHyp_of_fragX₃ {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} (P : CompRestOE S M' A lib ref D (FragXM S) (FragXN S)) : CompHyp A lib ref :=
  compHyp_of_fragX'' A P guardFinalU guardFinalF

end

/-- **One concrete `FragX` formula with a `%6`**: `[6 [0 2] [6 [0 6] [0 3]
[0 1]] [1 0]]`, a `%6` in a branch of a `%6`.  Its whole-subject code passes
no `~` and guards every split. -/
example {c : Straight Map}
    (h : finishLU (S := S) (Map := Map) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n1 (A 0))) = some c) : NoPoison c.blocks ∧ CelGuard c.blocks :=
  guardMonoX _ c fragX_sixSix (by decide) h

/-- The same formula's n-ary code, nothing baked. -/
example {c : Straight Map} {ord : NeedOrd} {less : Cape}
    (h : finishLF (S := S) (Map := Map) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n1 (A 0))) ord less (fun ned => (ned, [])) = some c) : NoPoison c.blocks ∧ CelGuard c.blocks :=
  guardNaryX _ ord less _ c fragX_sixSix (by decide) (fun _ => rfl) h

end Glue
end SkaModel
end Formalization
