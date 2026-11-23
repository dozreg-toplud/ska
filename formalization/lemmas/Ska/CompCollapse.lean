import lemmas.Ska.CompUnaryMore

/-!
# `+collapse-lazy-atom`

`collapse_ok`: what `+collapse-lazy-atom` returns for a goal `[%next laz th]`
and an atom.  Either it returns `~`, and then the lazy need asks nothing; or
it returns a register `r` and a label `o` such that entering `o` with an
atom in `r` does for the goal what the goal asks of that atom.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem ext_reg_le {g : Gen Map} {k : Nat} (h : g.re ≤ k) : Ext g { g with re := k } :=
  ⟨h, Nat.le_refl _, rfl, fun _ _ => rfl⟩

/-- The end of `+collapse-lazy-atom`, after the register and the block are
chosen. -/
def collapseTail (lok : S) (r there : Nat) : CM Map (Option (Nat × Nat)) := do
  let g ← get
  if g.drop then pure (some (r, there)) else do
    let ned' ← sureRequireLook (⟨Need.this r, lok⟩ : Sure S)
    match ned' with
    | Need.none => pure (some (r, there))
    | Need.this r' =>
        if r = r' then pure (some (r, there)) else do
          addOps there [Pole.mov r r']
          pure (some (r, there))
    | _ => do
        crashNeed there (Sum.inr r) ned'
        pure (some (r, there))

/-- When every look is at axis `1`, the end does nothing but allocate. -/
theorem collapseTail_one {lok : S} {r there : Nat} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (hall : ∀ x ∈ HoonSet.toList lok, x = 1) (h : collapseTail lok r there g = some (a, g')) :
    a = some (r, there) ∧ ∃ k, g' = { g with re := k } ∧ g.re ≤ k := by
  unfold collapseTail at h
  obtain ⟨g1, g1', h1, h⟩ := bind_some h
  rw [get_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  by_cases hd : g.drop = true
  · simp only [hd, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, g.re, rfl, Nat.le_refl _⟩
  · simp only [hd, Bool.false_eq_true, if_false] at h
    obtain ⟨ned', g2, h2, h⟩ := bind_some h
    have L := sureRequireLook_spec h2
    have e := L.same hall
    simp only at e
    subst e
    obtain ⟨k, rfl⟩ := L.gen
    simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, k, rfl, L.le⟩

/-- When some look is below axis `1`, the end puts in front of `there` ops
that crash when `r` holds an atom. -/
theorem collapseTail_big {lok : S} {r there : Nat} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (hx : ∃ x ∈ HoonSet.toList lok, 2 ≤ x) (h : collapseTail lok r there g = some (a, g'))
    (hd : g.drop = false) :
    a = some (r, there) ∧ ∃ ops, Front there g g' ops ∧ ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map)
      gul st t regs n, SkaModel.read r regs = some (A n) → Crashes lib O c gul st t ops regs := by
  unfold collapseTail at h
  obtain ⟨g1, g1', h1, h⟩ := bind_some h
  rw [get_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  simp only [hd, Bool.false_eq_true, if_false] at h
  obtain ⟨ned', g2, h2, h⟩ := bind_some h
  have L := sureRequireLook_spec h2
  obtain ⟨k, rfl⟩ := L.gen
  have F0 : Front there g { g with re := k } [] :=
    ⟨fun B fin hb => by simpa using hb, fun _ _ => rfl, rfl, rfl, L.le⟩
  have crashOps : ∀ fill : List Pole, ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map)
      gul st t regs n, SkaModel.read r regs = some (A n) →
      Crashes lib O c gul st t (Pole.cel r :: fill) regs := fun fill lib σ O c gul st t regs n hr =>
    Crashes.append_left (B := fill) (crashes_cel hr)
  rcases L.big hx with ⟨p, q, rfl⟩ | ⟨x, p, q, rfl⟩
  · simp only at h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have F1 := F0.trans (front_addOps h3 hd)
    exact ⟨rfl, _, F1, fun lib σ O c gul st t regs n hr => by simpa using crashOps _ lib σ O c gul st t regs n hr⟩
  · simp only at h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have F1 := F0.trans (front_addOps h3 hd)
    exact ⟨rfl, _, F1, fun lib σ O c gul st t regs n hr => by simpa using crashOps _ lib σ O c gul st t regs n hr⟩


theorem fits_some : ∀ (ned : Need), ∃ n, Comp.Fits ned n
  | Need.none => ⟨A 0, trivial⟩
  | Need.this _ => ⟨A 0, trivial⟩
  | Need.pair p q => by
    obtain ⟨a, ha⟩ := fits_some p; obtain ⟨b, hb⟩ := fits_some q; exact ⟨C a b, ha, hb⟩
  | Need.both _ p q => by
    obtain ⟨a, ha⟩ := fits_some p; obtain ⟨b, hb⟩ := fits_some q; exact ⟨C a b, ha, hb⟩

/-- A run of `+sure-require-look` that did not crash saw no look at axis `0`. -/
theorem sure_no_zero {ned0 ned : Need} {xs : List Nat} {g g' : Gen Map} (L : SureOK ned0 xs g g' ned) :
    ∀ x ∈ xs, x ≠ 0 := by
  intro x hx e
  subst e
  obtain ⟨n, hn⟩ := fits_some ned
  have := ((L.fits n).mp hn).2 0 hx
  simp [slot?_zero] at this

/-- The end of `+collapse-lazy-atom` on a block `%bom` it just made. -/
theorem collapse_bom {lok : S} {r : Nat} {gX g' : Gen Map} {a : Option (Nat × Nat)}
    (h0 : ∀ x ∈ HoonSet.toList lok, x ≠ 0)
    (h : collapseTail lok r gX.bo (gX.emitted ⟨[], [], Termin.bom Option.none⟩) = some (a, g')) :
    a = some (r, gX.bo) ∧ Ext gX g' ∧ g'.bo = gX.bo + 1 ∧
    (gX.drop = false → ∀ (c : Straight Map), HoonMap.get c.blocks gX.bo = HoonMap.get g'.blocks gX.bo →
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ) regs t gul n, SkaModel.read r regs = some (A n) →
        goJ lib O c gul st regs t (jmp0 gX.bo) = some (Tone.two t, st)) := by
  have E := ext_emit gX ⟨[], [], Termin.bom Option.none⟩
  by_cases hbig : ∃ x ∈ HoonSet.toList lok, 2 ≤ x
  · by_cases hd : gX.drop = false
    · obtain ⟨rfl, ops, F, cr⟩ := collapseTail_big hbig h ((emitted_drop _ _).trans hd)
      refine ⟨rfl, ⟨Nat.le_trans E.1 F.le, by rw [F.bo]; exact E.2.1, F.drop.trans E.2.2.1, fun o' ho' => ?_⟩,
        by rw [F.bo]; rfl, fun _ c hc lib σ O st regs t gul n hr => ?_⟩
      · rw [F.other o' (by omega)]; exact E.2.2.2 o' ho'
      · have hb := F.blk [] _ (emitted_get gX _ hd)
        rw [← hc] at hb
        rw [goJ_jmp0 _ _ _ _ hb]
        exact cr lib σ O c gul st t regs n hr [] _
    · simp only [Bool.not_eq_false] at hd
      unfold collapseTail at h
      simp only [bind_apply, get_apply, Option.bind_some, emitted_drop, hd, if_true, pure_apply,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, E, rfl, fun h => absurd (hd.symm.trans h) (by simp)⟩
  · have hall : ∀ x ∈ HoonSet.toList lok, x = 1 := fun x hx => by
      have := h0 x hx; have : ¬ 2 ≤ x := fun h2 => hbig ⟨x, hx, h2⟩; omega
    obtain ⟨rfl, k, rfl, hk⟩ := collapseTail_one hall h
    refine ⟨rfl, ⟨Nat.le_trans E.1 hk, E.2.1, E.2.2.1, E.2.2.2⟩, rfl, fun hd c hc lib σ O st regs t gul n _ => ?_⟩
    have hb : HoonMap.get c.blocks gX.bo = some ⟨[], [], Termin.bom Option.none⟩ := by
      rw [hc]; exact emitted_get gX _ hd
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_bom']

theorem jmp0_of_args {th : Jmp} (h : th.args = []) : jmp0 th.there = th := by
  rcases th with ⟨args, there⟩; simp only at h; subst h; rfl

/-- **`+collapse-lazy-atom`.** -/
theorem collapse_ok {laz : Sure S} {th : Jmp} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtom ⟨laz, th⟩ g = some (a, g')) :
    Ext g g' ∧ th.args = [] ∧ (a = Option.none → laz.ned = Need.none ∧ ∀ x ∈ HoonSet.toList laz.lok, x = 1) ∧
    ∀ r o, a = some (r, o) → (NMem laz.ned r ∨ (g.re ≤ r ∧ r < g'.re)) ∧ (o = th.there ∨ (g.bo ≤ o ∧ o < g'.bo)) ∧
      (g.drop = false → ∀ (c : Straight Map), Agree c g g' → ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ)
        regs t gul n, SkaModel.read r regs = some (A n) → ∀ {K : Nat → Prop},
        GoalSem lib O c gul st K regs t (jmp0 o) (CGoal.next laz th) (some (A n))) := by
  unfold collapseLazyAtom at h
  dsimp only at h
  by_cases ea : th.args ≠ []
  · rw [if_pos ea] at h; cases h
  rw [if_neg ea] at h
  have ea' : th.args = [] := by simpa using ea
  by_cases en : noneEquivalent laz = true
  · rw [if_pos en] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [noneEquivalent, Bool.and_eq_true, decide_eq_true_eq, HoonSet.small_iff] at en
    exact ⟨Ext.refl g, ea', fun _ => en, fun r o e => by cases e⟩
  rw [if_neg en] at h
  obtain ⟨nedS, g1, h1, h⟩ := bind_some h
  have L := sureRequireLook_spec h1
  have h0 := sure_no_zero L
  obtain ⟨k1, rfl⟩ := L.gen
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have ht : collapseTail laz.lok r there g2 = some (a, g') := h
  -- the looks of a need that takes no cell apart are at axis 1
  have small : (∀ p q, nedS ≠ Need.pair p q) → (∀ x p q, nedS ≠ Need.both x p q) →
      ∀ x ∈ HoonSet.toList laz.lok, x = 1 := fun hp hb x hx => by
    have := h0 x hx
    by_cases h2' : 2 ≤ x
    · rcases L.big ⟨x, hx, h2'⟩ with ⟨p, q, e⟩ | ⟨y, p, q, e⟩
      · exact absurd e (hp p q)
      · exact absurd e (hb y p q)
    · omega
  -- the case where `r` takes the atom and the goal's block follows
  have direct : ∀ (r' : Nat), (∀ (regs : Map Noun) v, SkaModel.read r' regs = some v → HoldsN nedS regs v) →
      ∀ (c : Straight Map) (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ) regs t gul n,
        SkaModel.read r' regs = some (A n) → ∀ {K : Nat → Prop},
        GoalSem lib O c gul st K regs t (jmp0 th.there)
          (CGoal.next laz th) (some (A n)) := by
    intro r' hh c lib σ O st regs t gul n hr K
    have hs := hh regs (A n) hr
    refine ⟨fun _ => ⟨regs, L.holds regs (A n) hs, fun _ _ => rfl, by rw [jmp0_of_args ea']⟩, fun hn => ?_⟩
    exact absurd (holdsS_of_sure L hs |> fitsS_of_holdsS) hn
  cases nedS with
  | this x =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨rfl, k, rfl, hk⟩ := collapseTail_one (small (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)) ht
    refine ⟨⟨Nat.le_trans L.le hk, Nat.le_refl _, rfl, fun _ _ => rfl⟩, ea', (fun e => by cases e), ?_⟩
    intro r o e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨?_, Or.inl rfl, fun _ c _ lib σ O st regs t gul n hr K => ?_⟩
    · rcases L.mem _ rfl with hm | hm
      · exact Or.inl hm
      · exact Or.inr ⟨hm.1, Nat.lt_of_lt_of_le hm.2 hk⟩
    · have D := direct x (fun regs v hr' => hr') c lib σ O st regs t gul n hr (K := K)
      exact GoalSem.transfer rfl (fun _ _ => rfl) (by simpa using D)
  | none =>
    simp only [bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨rfl, k, rfl, hk⟩ := collapseTail_one (small (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)) ht
    have l1 : g.re ≤ k1 := L.le
    have l2 : k1 + 1 ≤ k := hk
    refine ⟨⟨show g.re ≤ k by omega, Nat.le_refl _, rfl, fun _ _ => rfl⟩, ea', (fun e => by cases e), ?_⟩
    intro r o e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨Or.inr ⟨l1, show k1 < k by omega⟩, Or.inl rfl, fun _ c _ lib σ O st regs t gul n hr K => ?_⟩
    have D := direct k1 (fun regs v _ => trivial) c lib σ O st regs t gul n hr (K := K)
    exact GoalSem.transfer rfl (fun _ _ => rfl) (by simpa using D)
  | pair p q =>
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨rfl, E, eb, B⟩ := collapse_bom h0 ht
    refine ⟨(ext_reg_le L.le).trans ((ext_re _).trans E), ea', (fun e => by cases e), ?_⟩
    intro r o e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨Or.inr ⟨L.le, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E.1⟩, Or.inr ⟨Nat.le_refl _, by rw [eb]; simp⟩,
      fun hd c hc lib σ O st regs t gul n hr => ⟨fun hf => ?_, fun _ => ?_⟩⟩
    · exact absurd ((L.fits (A n)).mpr ⟨hf.1, hf.2⟩) id
    · exact B hd c (hc g.bo (Nat.le_refl _) (by rw [eb]; simp)) lib σ O st regs t gul n hr
  | both x p q =>
    simp only [bind_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨rfl, E, eb, B⟩ := collapse_bom h0 ht
    refine ⟨(ext_reg_le L.le).trans E, ea', (fun e => by cases e), ?_⟩
    intro r o e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨?_, Or.inr ⟨Nat.le_refl _, by rw [eb]; simp⟩,
      fun hd c hc lib σ O st regs t gul n hr => ⟨fun hf => ?_, fun _ => ?_⟩⟩
    · rcases L.mem _ (Or.inl rfl) with hm | hm
      · exact Or.inl hm
      · exact Or.inr ⟨hm.1, Nat.lt_of_lt_of_le hm.2 E.1⟩
    · exact absurd ((L.fits (A n)).mpr ⟨hf.1, hf.2⟩) id
    · exact B hd c (hc g.bo (Nat.le_refl _) (by rw [eb]; simp)) lib σ O st regs t gul n hr


/-- **`[4 p]` for `%next`.** -/
theorem run_n4_next_ok {lib : Lib} {p : Nomm} {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n4 p) (CGoal.next laz th) g0 = some (nex, g1))
    (ih : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n4 p) (CGoal.next laz th) g0 g1 nex := by
  simp only [run] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, hnone, hsome⟩ := collapse_ok h2
  obtain ⟨⟨pro, th'⟩, g3, h3, h⟩ := bind_some h
  -- the register of the product and the block after the increment
  have P : Ext g2 g3 ∧ (NMem laz.ned pro ∨ (g0.re ≤ pro ∧ pro < g3.re)) ∧
      (g0.drop = false → ∀ (c : Straight Map), Agree c g0 g2 → ∀ (σ : Type) (O : Oracle σ) (st : σ) regs t gul n,
        SkaModel.read pro regs = some (A n) → ∀ {K : Nat → Prop},
        GoalSem lib O c gul st K regs t (jmp0 th') (CGoal.next laz th) (some (A n))) := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨e1, rfl⟩ := h3
      subst e1
      obtain ⟨hm, _, hs⟩ := hsome pro th' rfl
      exact ⟨Ext.refl _, hm, fun hd c hc σ O st regs t gul n hr => hs hd c hc lib σ O st regs t gul n hr⟩
    | none =>
      obtain ⟨hn, hl⟩ := hnone rfl
      simp only [bind_apply, re_apply, Option.bind_some, ea, if_true, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h3
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
      refine ⟨ext_re _, Or.inr ⟨E2.1, Nat.lt_succ_self _⟩, fun _ c _ σ O st regs t gul n hr => ?_⟩
      refine ⟨fun _ => ⟨regs, by rw [hn]; trivial, fun _ _ => rfl, by rw [jmp0_of_args ea]⟩, fun hf => ?_⟩
      exact absurd ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩ hf
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  refine unary_ok (pureEval_n4 p) (E2.trans (P.1.trans ((ext_re _).trans (ext_emit _ _)))) ⟨by have := E2.1; have := P.1.1; omega, by simp [emitted_re]⟩
    (by simp [emitted_bo])
    (ih _ _ _ _ _ ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩ trivial h) ?_
    (by have := E2.2.1; have := P.1.2.1; show g0.bo ≤ g3.bo; omega)
  intro c hc hd σ O st regs t gul x hx
  have hd3 : g3.drop = false := P.1.2.2.1.trans (E2.2.2.1.trans hd)
  have hb := emitted_get' (by simpa using hd3)
    (hc _ (by have := E2.2.1; have := P.1.2.1; show g0.bo ≤ g3.bo; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_hop] at hj
    refine GoalSem.transfer hj (fun r ⟨h1, h2⟩ => read_store_ne (fun e => ?_) _ _)
      (P.2.2 hd c (hc.left E2 (P.1.trans ((ext_re _).trans (ext_emit _ _)))) σ O st
        (store pro (A (n + 1)) regs) t gul (n + 1) (read_store_eq _ _ _))
    subst e
    rcases P.2.1 with hm | ⟨hm, hm'⟩
    · exact h2 hm
    · simp [emitted_re] at h1; omega
  | cell u v =>
    apply goalSem_crash
    rw [hj, show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]

end Comp
end SkaModel
end Formalization
