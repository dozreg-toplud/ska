import lemmas.Ska.OptHopsBlocks

/-!
# `+remove-hops` keeps the code

A simulation on paths, on the template of `OptBranch.lean`.  The code before
runs the blocks of a chain one after the other; the code after runs their
merge.  The relation (`HopRel`) has two cases.

* `HopI`: the same position.  The configuration before is in the block `b0`
  of its label, whose chain has the tail `T` and the end `F` (`MTail`); the
  block after is what is left of the block before with `T` appended and the
  end `F`; the same arguments, trace and state; registers in the order
  `RegLe` (the same unit, or poison before and a value after).
* `HopII`: the code before has jumped through a merged hop and has its pass
  pending; the code after runs the moves of the hop (`PassRel`).

Forward (`hop_fwd_step`, `hop_fwd_end`) needs no hypothesis on the reads: a
step of the code before that does not crash read values.  At the end of a
chain the code before jumps to a block that is no merged one (`Wit`): its only
predecessor in `rev` would be the block that jumps, whose chain would not
have stopped there.  Backward, a configuration is first brought to a normal
form (`hop_norm`: the code before takes the merged hops that pass nothing,
which the code after has already passed), where each step after is matched by
at most one step before (`hop_bwd_step`), using `ReadsOK` of the code before
at real reads, where a register poisoned before holds `0` after.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-- What the simulation needs of the blocks, `topo` and `rev`. -/
structure HopsHyp (bl : Map Blob) (rev : Map (List Nat)) (topo : List Nat) : Prop where
  reach : ∀ o, Reach bl o → o ∈ topo
  rev : ∀ o b j, o ∈ topo → HoonMap.get bl o = some b → j ∈ getJmps b.fin → o ∈ getJa rev j.there
  nodup : ParNodup bl
  pass : PassOK bl

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map} {rev : Map (List Nat)}
  {topo : List Nat}

/-- The same position. -/
def HopI (bl : Map Blob) (rev : Map (List Nat)) (x x' : Cfg σ Map) (b0 : Blob) (T : List Pole) (F : Termin) :
    Prop :=
  x'.t = x.t ∧ x'.st = x.st ∧ Reach bl x.lab ∧ HoonMap.get bl x.lab = some b0 ∧ MTail bl rev x.lab b0 T F ∧
  x'.params = x.params ∧ RegLe x.regs x'.regs ∧ x.b.fin = b0.fin ∧
  x'.b = { x.b with body := x.b.body ++ T, fin := F }

/-- A pass pending before, its moves running after. -/
def HopII (bl : Map Blob) (rev : Map (List Nat)) (x x' : Cfg σ Map) : Prop :=
  x'.t = x.t ∧ x'.st = x.st ∧ Reach bl x.lab ∧ ∃ b0 T F ops, HoonMap.get bl x.lab = some b0 ∧
  MTail bl rev x.lab b0 T F ∧ x.params ≠ [] ∧ x.b = b0 ∧ x'.params = [] ∧ ops ≠ [] ∧ MovOps ops ∧
  x'.b = ⟨[], ops ++ (b0.body ++ T), F⟩ ∧ PassRel x.params b0.par x.regs ops x'.regs

def HopRel (bl : Map Blob) (rev : Map (List Nat)) (x x' : Cfg σ Map) : Prop :=
  (∃ b0 T F, HopI bl rev x x' b0 T F) ∨ HopII bl rev x x'

/-- The normal form of the backward direction. -/
def HopN (bl : Map Blob) (rev : Map (List Nat)) (x x' : Cfg σ Map) : Prop :=
  HopII bl rev x x' ∨ ∃ b0 T F, HopI bl rev x x' b0 T F ∧
    (x.params ≠ [] ∨ x.b.par ≠ [] ∨ x.b.body ≠ [] ∨ (T = [] ∧ F = x.b.fin))

/-! ## The moves -/

theorem moves_steps {ops : List Pole} (hm : MovOps ops) : ∀ {R Ra : Map (Option Noun)} {lab : Nat}
    {rest : List Pole} {F : Termin} {t : Trace} {st : σ}, runMoves ops R = some Ra →
    Steps lib O c' gul ⟨lab, ⟨[], ops ++ rest, F⟩, [], R, t, st⟩ [] ⟨lab, ⟨[], rest, F⟩, [], Ra, t, st⟩ := by
  induction ops with
  | nil => intro R Ra lab rest F t st h; cases h; exact Steps.refl _
  | cons q ops ih =>
    intro R Ra lab rest F t st h
    have hm' : MovOps ops := fun q' hq' => hm q' (List.mem_cons_of_mem _ hq')
    rcases hm q List.mem_cons_self with ⟨n, d, rfl⟩ | ⟨s, d, rfl⟩
    · have hs := Step.op (lib := lib) (O := O) (c := c') (gul := gul)
        (x := ⟨lab, ⟨[], Pole.imm n d :: (ops ++ rest), F⟩, [], R, t, st⟩) (p := Pole.imm n d)
        (rest := ops ++ rest) (n := A 0) (R := store d n R) (t' := t) (st' := st) rfl rfl rfl
        (by simp [execPole, localPole])
      exact Steps.step hs (ih hm' h)
    · simp only [runMoves] at h
      obtain ⟨R1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      have hs := Step.op (lib := lib) (O := O) (c := c') (gul := gul)
        (x := ⟨lab, ⟨[], Pole.mov s d :: (ops ++ rest), F⟩, [], R, t, st⟩) (p := Pole.mov s d)
        (rest := ops ++ rest) (n := A 0) (R := R1) (t' := t) (st' := st) rfl rfl rfl
        (by simp [execPole, localPole, h1])
      exact Steps.step hs (ih hm' h2)

theorem movop_step {q : Pole} (hq : (∃ n d, q = Pole.imm n d) ∨ (∃ s d, q = Pole.mov s d)) {st st3 : σ}
    {R R3 : Map (Option Noun)} {t t3 : Trace} {ton : Tone} (h : execPole lib O gul st q R t = some (ton, R3, t3, st3)) :
    ton = Tone.zero (A 0) ∧ t3 = t ∧ st3 = st ∧ ∀ ops, runMoves (q :: ops) R = runMoves ops R3 := by
  rcases hq with ⟨n, d, rfl⟩ | ⟨s, d, rfl⟩
  · simp only [execPole, localPole, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, b, c⟩, ⟨R1, h1, h2⟩, h3⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2 h3
    obtain ⟨rfl, rfl, rfl⟩ := h2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h3
    exact ⟨rfl, rfl, rfl, fun _ => by simp [runMoves, h1]⟩

theorem movop_endOf {q : Pole} (hq : (∃ n d, q = Pole.imm n d) ∨ (∃ s d, q = Pole.mov s d)) {x : Cfg σ Map}
    {rest : List Pole} (hb : x.b.body = q :: rest) : endOf lib O gul x = none := by
  unfold endOf
  split
  · rfl
  rw [hb]
  simp only
  cases e : execPole lib O gul x.st q x.regs x.t with
  | none => rfl
  | some r =>
    obtain ⟨ton, R3, t3, st3⟩ := r
    obtain ⟨rfl, -, -, -⟩ := movop_step hq e
    rfl

theorem movop_reads {q : Pole} (hq : (∃ n d, q = Pole.imm n d) ∨ (∃ s d, q = Pole.mov s d)) :
    poleReads gul q = [] := by
  rcases hq with ⟨n, d, rfl⟩ | ⟨s, d, rfl⟩ <;> rfl

/-! ## Through a merged hop -/

/-- The code before takes a merged hop: the pass pending is related to the
moves of the code after, or there is none. -/
theorem link_rel (HH : HopsHyp c.blocks rev topo) {lab : Nat} {b : Blob} {params : List (Option Nat)}
    {regs : Map (Option Noun)} {t : Trace} {st : σ} {x' : Cfg σ Map} {b0 b1 : Blob} {t1 : Jmp}
    {ops T1 : List Pole} {F1 : Termin}
    (hI : HopI c.blocks rev ⟨lab, b, params, regs, t, st⟩ x' b0 (ops ++ b1.body ++ T1) F1)
    (hf : b0.fin = Termin.hop t1) (hb1 : HoonMap.get c.blocks t1.there = some b1)
    (hseg : hopSeg t1.args b1.par [] = some ops) (hm1 : MTail c.blocks rev t1.there b1 T1 F1)
    (hp : params = []) (hq : b.par = []) (hb : b.body = []) :
    HopI c.blocks rev ⟨t1.there, b1, t1.args, regs, t, st⟩ x' b1 T1 F1 ∨
      HopII c.blocks rev ⟨t1.there, b1, t1.args, regs, t, st⟩ x' := by
  obtain ⟨ht', hst', hreach, hb0, -, hp', hR, hfin, hb'⟩ := hI
  simp only at ht' hst' hreach hb0 hp' hR hfin hb'
  have hj : t1 ∈ getJmps b0.fin := by rw [hf]; simp [getJmps]
  have hreach1 : Reach c.blocks t1.there := Reach.jump hreach hb0 hj
  have hpass := HH.pass lab b0 t1 b1 hb0 hj hb1
  obtain ⟨hmov, hlen, hnil, hpr⟩ := passRel_init hR (HH.nodup _ _ hb1) hpass hseg
  by_cases ha : t1.args = []
  · have hops : ops = [] := hnil.mpr ha
    have hpar : b1.par = [] := by
      rw [ha] at hlen; exact List.eq_nil_of_length_eq_zero hlen.symm
    subst hops
    refine Or.inl ⟨ht', hst', hreach1, hb1, hm1, by rw [hp', hp, ha], hR, rfl, ?_⟩
    rw [hb']
    obtain ⟨p1, bd1, f1⟩ := b1
    simp only at hpar ⊢
    subst hpar
    simp [hq, hb]
  · refine Or.inr ⟨ht', hst', hreach1, b1, T1, F1, ops, hb1, hm1, ha, rfl, by rw [hp', hp], ?_, hmov, ?_, hpr⟩
    · intro e; exact ha (hnil.mp e)
    · rw [hb']; simp [hq, hb]

/-! ## Forward -/

variable (HH : HopsHyp c.blocks rev topo) (H : HopsBlocks c.blocks rev topo c'.blocks)
include HH H

/-- **Forward**: a step of the code before is matched by steps after. -/
theorem hop_fwd_step {x y x' : Cfg σ Map} {es : List (Nat × Nat)} (hs : Step lib O c gul x es y)
    (hr : HopRel c.blocks rev x x') : ∃ es' y', Steps lib O c' gul x' es' y' ∧ HopRel c.blocks rev y y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  rcases hr with ⟨b0, T, F, hI⟩ | hII
  · have hI0 := hI
    obtain ⟨ht', hst', hreach, hb0, hm, hp', hR, hfin, hb'⟩ := hI
    obtain ⟨lab', b', params', regs', t', st'⟩ := x'
    simp only at ht' hst' hreach hb0 hm hp' hR hfin hb'
    subst t' st' params' b'
    cases hs with
    | pass hne hRp =>
      obtain ⟨R1, hR1, hle⟩ := (evalPass_le _ _ hR).fwd hRp
      exact ⟨[], ⟨lab', ⟨[], b.body ++ T, F⟩, [], R1, t, st⟩,
        Steps.step (Step.pass (x := ⟨lab', { b with body := b.body ++ T, fin := F }, params, regs', t, st⟩)
        hne hR1) (Steps.refl _), Or.inl ⟨b0, T, F, rfl, rfl, hreach, hb0, hm, rfl, hle, hfin, rfl⟩⟩
    | @op p rest n R2 t2 st2 hp hq hbd hpole =>
      have hrd := execPole_reads (by rw [hpole]; rfl)
      obtain ⟨R1, hR1, hle⟩ := (execPole_le lib O gul _ _ _ hR hrd).fwd hpole
      simp only at hbd hp hq
      refine ⟨[], ⟨lab', ⟨b.par, rest ++ T, F⟩, params, R1, t2, st2⟩,
        Steps.step (Step.op (x := ⟨lab', { b with body := b.body ++ T, fin := F }, params, regs', t, st⟩)
        (rest := rest ++ T) hp hq (by simp [hbd]) hR1) (Steps.refl _),
        Or.inl ⟨b0, T, F, rfl, rfl, hreach, hb0, hm, rfl, hle, hfin, rfl⟩⟩
    | @jump j b2 hp hq hbd ht hb2 =>
      simp only at hp hq hbd ht hb2
      have hjf : j ∈ getJmps b0.fin := hfin ▸ taken_mem ht
      have hreach2 : Reach c.blocks j.there := Reach.jump hreach hb0 hjf
      cases hm with
      | stop hstop =>
        have ht2 : taken regs' b0.fin = some j := by rw [← hfin, taken_le hR _ (taken_reads ht)]; exact ht
        rcases H.cover j.there (HH.reach _ hreach2) with ⟨m, hm', b2', T2, F2, hb2', hmt, rfl⟩ | ⟨p, bp, t1, hpre, hbp, hfp, hth⟩
        · rw [hb2] at hb2'; cases hb2'
          refine ⟨_, ⟨j.there, merge b2 T2 F2, j.args, regs', t, st⟩,
            Steps.step (Step.jump (x := ⟨lab', { b with body := b.body ++ [], fin := b0.fin }, params, regs', t, st⟩)
            hp hq (by simp [hbd]) ht2 hm') (Steps.refl _), Or.inl ⟨b2, T2, F2, rfl, rfl, hreach2, hb2, hmt, rfl, hR, rfl, rfl⟩⟩
        · exfalso
          have hl := HH.rev lab b0 j (HH.reach _ hreach) hb0 hjf
          rw [hpre, List.mem_singleton] at hl
          subst hl
          rw [hb0] at hbp; cases hbp
          exact hstop t1 hfp (by rw [hth, hpre])
      | link hf hpre hb1 hseg hm1 =>
        rw [hfin, hf] at ht
        simp only [taken, Option.some.injEq] at ht
        subst ht
        rw [hb1] at hb2; cases hb2
        refine ⟨[], _, Steps.refl _, ?_⟩
        rcases link_rel HH hI0 hf hb1 hseg hm1 hp hq hbd with h | h
        · exact Or.inl ⟨_, _, _, h⟩
        · exact Or.inr h
  · obtain ⟨ht', hst', hreach, b0, T, F, ops, hb0, hm, hpne, hxb, hp', hne, hmov, hb', hpr⟩ := hII
    obtain ⟨lab', b', params', regs', t', st'⟩ := x'
    simp only at ht' hst' hreach hb0 hm hpne hxb hp' hb' hpr
    subst t' st' params' b' b
    cases hs with
    | pass hne' hRp =>
      obtain ⟨Ra, hRa, hle⟩ := hpr.1 _ hRp
      exact ⟨[], ⟨lab', ⟨[], b0.body ++ T, F⟩, [], Ra, t, st⟩, moves_steps hmov hRa,
        Or.inl ⟨b0, T, F, rfl, rfl, hreach, hb0, hm, rfl, hle, rfl, rfl⟩⟩
    | op hp => exact absurd hp hpne
    | jump hp => exact absurd hp hpne

/-- **Forward, at an end.** -/
theorem hop_fwd_end {x x' : Cfg σ Map} {r : Tone × σ} (he : endOf lib O gul x = some r)
    (hr : HopRel c.blocks rev x x') : ∃ es' y', Steps lib O c' gul x' es' y' ∧ endOf lib O gul y' = some r := by
  refine ⟨[], x', Steps.refl _, ?_⟩
  rcases hr with ⟨b0, T, F, ht', hst', hreach, hb0, hm, hp', hR, hfin, hb'⟩ | ⟨-, -, -, b0, T, F, ops, -, -, hpne, -⟩
  · have hrd := endOf_reads he
    by_cases hpq : x.params ≠ [] ∨ x.b.par ≠ []
    · simp [endOf, hpq] at he
    · simp only [not_or, ne_eq, Decidable.not_not] at hpq
      rw [← he]
      apply endOf_le hR hrd hp' (by rw [hb']) ht' hst'
      cases hbd : x.b.body with
      | cons p rest => exact Or.inr ⟨p, rest, rest ++ T, rfl, by rw [hb']; simp [hbd]⟩
      | nil =>
        left
        refine ⟨rfl, ?_⟩
        cases hm with
        | stop => rw [hb']; simp [hbd, hfin]
        | link hf =>
          exfalso
          unfold endOf at he
          rw [if_neg (by simp [hpq.1, hpq.2]), hbd, hfin, hf] at he
          cases he
  · simp [endOf, hpne] at he

/-! ## Backward -/

/-- **The normal form**: the code before takes the merged hops that pass
nothing. -/
theorem hop_norm : ∀ (lab : Nat) (b0 : Blob) (T : List Pole) (F : Termin), MTail c.blocks rev lab b0 T F →
    ∀ (x x' : Cfg σ Map), x.lab = lab → HopI c.blocks rev x x' b0 T F →
      ∃ es y, Steps lib O c gul x es y ∧ HopN c.blocks rev y x' := by
  intro lab b0 T F hm
  induction hm with
  | stop hstop =>
    intro x x' _ hI
    exact ⟨[], x, Steps.refl _, Or.inr ⟨_, _, _, hI, Or.inr (Or.inr (Or.inr ⟨rfl, hI.2.2.2.2.2.2.2.1.symm⟩))⟩⟩
  | @link o b t1 b1 ops T1 F1 hf hpre hb1 hseg hm1 ih =>
    intro x x' hlab hI
    by_cases hnf : x.params ≠ [] ∨ x.b.par ≠ [] ∨ x.b.body ≠ []
    · exact ⟨[], x, Steps.refl _, Or.inr ⟨_, _, _, hI,
        by rcases hnf with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))⟩⟩
    · simp only [not_or, ne_eq, Decidable.not_not] at hnf
      obtain ⟨hp, hq, hbd⟩ := hnf
      obtain ⟨lab0, bx, params, regs, t, st⟩ := x
      simp only at hlab hp hq hbd
      subst hlab
      have hfin := hI.2.2.2.2.2.2.2.1
      simp only at hfin
      have hstep : Step lib O c gul ⟨lab0, bx, params, regs, t, st⟩ [(lab0, t1.there)]
          ⟨t1.there, b1, t1.args, regs, t, st⟩ :=
        Step.jump hp hq hbd (by simp [taken, hfin, hf]) hb1
      rcases link_rel HH hI hf hb1 hseg hm1 hp hq hbd with hI2 | hII
      · obtain ⟨es, y, hs, hn⟩ := ih _ x' rfl hI2
        exact ⟨_, y, Steps.step hstep hs, hn⟩
      · exact ⟨_, _, Steps.step hstep (Steps.refl _), Or.inl hII⟩

/-- Bring a related configuration to the normal form. -/
theorem hop_toN {x0 x x' : Cfg σ Map} {es : List (Nat × Nat)} (h : Steps lib O c gul x0 es x)
    (hr : HopRel c.blocks rev x x') : ∃ es2 z, Steps lib O c gul x0 es2 z ∧ HopN c.blocks rev z x' := by
  rcases hr with ⟨b0, T, F, hI⟩ | hII
  · obtain ⟨es1, z, hz, hn⟩ := hop_norm HH H x.lab b0 T F hI.2.2.2.2.1 x x' rfl hI
    exact ⟨_, z, steps_trans h hz, hn⟩
  · exact ⟨es, x, h, Or.inl hII⟩

/-- **Backward**: from the normal form, a step of the code after is matched by
at most one step before. -/
theorem hop_bwd_step {x x' y' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Step lib O c' gul x' es' y')
    (hn : HopN c.blocks rev x x') (hok : ∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v) :
    ∃ es y, Steps lib O c gul x es y ∧ HopRel c.blocks rev y y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  rcases hn with ⟨ht', hst', hreach, b0, T, F, ops, hb0, hm, hpne, hxb, hp', hne, hmov, hb', hpr⟩ | ⟨b0, T, F, hI, hnf⟩
  · obtain ⟨lab', b', params', regs', t', st'⟩ := x'
    simp only at ht' hst' hreach hb0 hm hpne hxb hp' hb' hpr
    subst t' st' params' b' b
    obtain ⟨q, ops', rfl⟩ : ∃ q ops', ops = q :: ops' := by
      cases ops with
      | nil => exact absurd rfl hne
      | cons q ops' => exact ⟨q, ops', rfl⟩
    have hq : (∃ n d, q = Pole.imm n d) ∨ (∃ s d, q = Pole.mov s d) := hmov q List.mem_cons_self
    cases hs with
    | pass hne' => simp at hne'
    | @op p rest n R3 t3 st3 hp hq' hbd hpole =>
      simp only [List.cons_append, List.cons.injEq] at hbd
      obtain ⟨rfl, rfl⟩ := hbd
      obtain ⟨-, rfl, rfl, hrun⟩ := movop_step hq hpole
      by_cases hops' : ops' = []
      · subst hops'
        obtain ⟨Rb, hRb, hle⟩ := hpr.2 R3 (by rw [hrun]; rfl)
        exact ⟨[], ⟨lab, ⟨[], b0.body, b0.fin⟩, [], Rb, t3, st3⟩,
          Steps.step (Step.pass (x := ⟨lab, b0, params, regs, t3, st3⟩) (Or.inl hpne) hRb) (Steps.refl _),
          Or.inl ⟨b0, T, F, rfl, rfl, hreach, hb0, hm, rfl, hle, rfl, rfl⟩⟩
      · refine ⟨[], ⟨lab, b0, params, regs, t3, st3⟩, Steps.refl _, Or.inr ⟨rfl, rfl, hreach, b0, T, F, ops', hb0, hm,
          hpne, rfl, rfl, hops', fun q' h => hmov q' (List.mem_cons_of_mem _ h), rfl, ?_⟩⟩
        exact ⟨fun Rb h => by rw [← hrun ops']; exact hpr.1 Rb h,
          fun Ra h => hpr.2 Ra (by rw [hrun ops']; exact h)⟩
    | jump hp hq' hbd => simp at hbd
  · obtain ⟨ht', hst', hreach, hb0, hm, hp', hR, hfin, hb'⟩ := hI
    obtain ⟨lab', b', params', regs', t', st'⟩ := x'
    simp only at ht' hst' hreach hb0 hm hp' hR hfin hb' hnf hok
    subst t' st' params' b'
    cases hs with
    | @pass R' hne hR' =>
      obtain ⟨R1, hR1, hle⟩ := (evalPass_le params b.par hR).bwd hR'
      exact ⟨[], ⟨lab, ⟨[], b.body, b.fin⟩, [], R1, t, st⟩,
        Steps.step (Step.pass (x := ⟨lab, b, params, regs, t, st⟩) hne hR1) (Steps.refl _),
        Or.inl ⟨b0, T, F, rfl, rfl, hreach, hb0, hm, rfl, hle, hfin, rfl⟩⟩
    | @op p rest n R' t2 st2 hp hq hbd hpole =>
      simp only at hp hq hbd
      cases hbb : b.body with
      | nil =>
        rcases hnf with h | h | h | ⟨rfl, -⟩
        · exact absurd hp h
        · exact absurd hq h
        · exact absurd hbb h
        · rw [hbb] at hbd; cases hbd
      | cons p0 rest0 =>
        rw [hbb] at hbd
        simp only [List.cons_append, List.cons.injEq] at hbd
        obtain ⟨rfl, rfl⟩ := hbd
        have hrd : ∀ k ∈ poleReads gul p0, ∃ v, read k regs = some v :=
          fun k hk => hok k ⟨hp, hq, Or.inl ⟨p0, rest0, hbb, hk⟩⟩
        obtain ⟨R1, hR1, hle⟩ := (execPole_le lib O gul _ _ _ hR hrd).bwd hpole
        exact ⟨[], ⟨lab, ⟨b.par, rest0, b.fin⟩, params, R1, t2, st2⟩,
          Steps.step (Step.op (x := ⟨lab, b, params, regs, t, st⟩) hp hq hbb hR1) (Steps.refl _),
          Or.inl ⟨b0, T, F, rfl, rfl, hreach, hb0, hm, rfl, hle, hfin, rfl⟩⟩
    | @jump j m hp hq hbd ht hm' =>
      simp only at hp hq hbd ht hm'
      have hb1 : b.body = [] := (List.append_eq_nil_iff.mp hbd).1
      have hT : T = [] ∧ F = b.fin := by
        rcases hnf with h | h | h | h
        · exact absurd hp h
        · exact absurd hq h
        · exact absurd hb1 h
        · exact h
      obtain ⟨rfl, rfl⟩ := hT
      have hrd : ∀ k ∈ finReads b.fin, ∃ v, read k regs = some v := fun k hk => hok k ⟨hp, hq, Or.inr ⟨hb1, hk⟩⟩
      rw [taken_le hR _ hrd] at ht
      obtain ⟨b2, T2, F2, hb2, hmt, rfl⟩ := H.back _ _ hm'
      have hreach2 : Reach c.blocks j.there := Reach.jump hreach hb0 (hfin ▸ taken_mem ht)
      exact ⟨_, ⟨j.there, b2, j.args, regs, t, st⟩,
        Steps.step (Step.jump (x := ⟨lab, b, params, regs, t, st⟩) hp hq hb1 ht hb2) (Steps.refl _),
        Or.inl ⟨b2, T2, F2, rfl, rfl, hreach2, hb2, hmt, rfl, hR, rfl, rfl⟩⟩

/-- **Backward, at an end.** -/
theorem hop_bwd_end {x x' : Cfg σ Map} {r : Tone × σ} (he : endOf lib O gul x' = some r)
    (hn : HopN c.blocks rev x x') (hok : ∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v) :
    endOf lib O gul x = some r := by
  rcases hn with ⟨-, -, -, b0, T, F, ops, -, -, -, -, -, hne, hmov, hb', -⟩ | ⟨b0, T, F, hI, hnf⟩
  · exfalso
    obtain ⟨q, ops', rfl⟩ : ∃ q ops', ops = q :: ops' := by
      cases ops with
      | nil => exact absurd rfl hne
      | cons q ops' => exact ⟨q, ops', rfl⟩
    rw [movop_endOf (hmov q List.mem_cons_self) (by rw [hb']; rfl)] at he; cases he
  · obtain ⟨ht', hst', -, -, -, hp', hR, -, hb'⟩ := hI
    by_cases hpq : x.params ≠ [] ∨ x.b.par ≠ []
    · exfalso
      have : x'.params ≠ [] ∨ x'.b.par ≠ [] := by rw [hp', hb']; exact hpq
      simp [endOf, this] at he
    · simp only [not_or, ne_eq, Decidable.not_not] at hpq
      rw [← endOf_le hR hok hp' (by rw [hb']) ht' hst' ?_]
      · exact he
      cases hbd : x.b.body with
      | cons p rest => exact Or.inr ⟨p, rest, rest ++ T, rfl, by rw [hb']; simp [hbd]⟩
      | nil =>
        rcases hnf with h | h | h | ⟨rfl, rfl⟩
        · exact absurd hpq.1 h
        · exact absurd hpq.2 h
        · exact absurd hbd h
        · exact Or.inl ⟨rfl, by rw [hb']; simp [hbd], by rw [hb']⟩

/-- A real read after is a real read before, of registers below. -/
theorem hop_bwd_reads {x x' : Cfg σ Map} {k : Nat} (hn : HopN c.blocks rev x x') (hk : ReadsAt gul x' k) :
    ReadsAt gul x k ∧ RegLe x.regs x'.regs := by
  rcases hn with ⟨-, -, -, b0, T, F, ops, -, -, -, -, -, hne, hmov, hb', -⟩ | ⟨b0, T, F, hI, hnf⟩
  · exfalso
    obtain ⟨q, ops', rfl⟩ : ∃ q ops', ops = q :: ops' := by
      cases ops with
      | nil => exact absurd rfl hne
      | cons q ops' => exact ⟨q, ops', rfl⟩
    obtain ⟨-, -, hk⟩ := hk
    rw [hb'] at hk
    rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, -⟩
    · simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      rw [movop_reads (hmov _ List.mem_cons_self)] at hk; exact absurd hk List.not_mem_nil
    · simp at hb
  · obtain ⟨-, -, -, -, -, hp', hR, -, hb'⟩ := hI
    refine ⟨?_, hR⟩
    obtain ⟨hp, hq, hk⟩ := hk
    rw [hp'] at hp
    rw [hb'] at hq hk
    simp only at hq hk
    refine ⟨hp, hq, ?_⟩
    cases hbd : x.b.body with
    | cons p0 rest0 =>
      rw [hbd] at hk
      rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, -⟩
      · simp only [List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, -⟩ := hb
        exact Or.inl ⟨p0, rest0, rfl, hk⟩
      · simp at hb
    | nil =>
      rcases hnf with h | h | h | ⟨rfl, rfl⟩
      · exact absurd hp h
      · exact absurd hq h
      · exact absurd hbd h
      · rw [hbd] at hk
        rcases hk with ⟨p, rest, hb, -⟩ | ⟨-, hk⟩
        · simp at hb
        · exact Or.inr ⟨rfl, hk⟩

/-- **Forward, on paths.** -/
theorem hop_fwd {x y : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es y) {r : Tone × σ}
    (he : endOf lib O gul y = some r) :
    ∀ {x' : Cfg σ Map}, HopRel c.blocks rev x x' →
      ∃ es' y', Steps lib O c' gul x' es' y' ∧ endOf lib O gul y' = some r := by
  induction hs with
  | refl => intro x' hr; exact hop_fwd_end HH H he hr
  | step s _ ih =>
    intro x' hr
    obtain ⟨es1, y1, hs1, hr1⟩ := hop_fwd_step HH H s hr
    obtain ⟨es2, y2, hs2, he2⟩ := ih he hr1
    exact ⟨_, y2, steps_trans hs1 hs2, he2⟩

/-- **Backward, on paths**, to the normal form. -/
theorem hop_bwd {x0 : Cfg σ Map}
    (hok : ∀ es y k, Steps lib O c gul x0 es y → ReadsAt gul y k → ∃ v, read k y.regs = some v)
    {x' y' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Steps lib O c' gul x' es' y') :
    ∀ {x : Cfg σ Map} {es : List (Nat × Nat)}, Steps lib O c gul x0 es x → HopRel c.blocks rev x x' →
      ∃ es2 y, Steps lib O c gul x0 es2 y ∧ HopN c.blocks rev y y' := by
  induction hs with
  | refl => intro x es h hr; exact hop_toN HH H h hr
  | step s _ ih =>
    intro x es h hr
    obtain ⟨es1, z, hz, hn⟩ := hop_toN HH H h hr
    obtain ⟨es2, y1, hs1, hr1⟩ := hop_bwd_step HH H s hn (fun k hk => hok _ z k hz hk)
    exact ih (steps_trans hz hs1) hr1

end Sim

/-- **`+remove-hops` keeps the code**, on a `topo` with `TopoOK`, its
`+rev-cfg`, distinct parameters and jumps that pass the check of
`+eval-pass`. -/
theorem hops_keeps [MapKeys Map] {fuel : Nat} (c : Straight Map) {topo : List Nat} {ch : Bool} {bl' : Map Blob}
    (ht : TopoOK c.blocks topo) (hnd : ParNodup c.blocks) (hpc : PassOK c.blocks)
    (h : removeHops fuel c.blocks (revCfg c.blocks topo) topo = some (ch, bl')) : Keeps c (withBlocks c bl') := by
  have HH : HopsHyp c.blocks (revCfg c.blocks topo) topo :=
    ⟨ht.2.2.2.1, fun o b j ho hb hj => revCfg_mem ho hb hj, hnd, hpc⟩
  have H : HopsBlocks c.blocks (revCfg c.blocks topo) topo (withBlocks c bl').blocks := hops_blocks ht.1 ht.2.1 h
  obtain ⟨m0, hm0, b0, T, F, hb0, hmt, rfl⟩ := H.zero
  refine ⟨rfl, rfl, by rw [hm0, hb0]; rfl, ?_⟩
  intro lib σ O gul st vals t hok
  let x0 : Path.Cfg σ Map := ⟨0, b0, [], regsOf vals, t, st⟩
  let x0' : Path.Cfg σ Map := ⟨0, merge b0 T F, [], regsOf vals, t, st⟩
  have hr0 : HopRel c.blocks (revCfg c.blocks topo) x0 x0' :=
    Or.inl ⟨b0, T, F, rfl, rfl, Reach.zero, hb0, hmt, rfl, RegLe.refl _, rfl, rfl⟩
  have hok' : ∀ es y k, Steps lib O c gul x0 es y → ReadsAt gul y k → ∃ v, read k y.regs = some v :=
    fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
  have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c bl') (gul := gul) st vals t es' y' →
      ∃ es y, Steps lib O c gul x0 es y ∧ HopN c.blocks (revCfg c.blocks topo) y y' := by
    rintro es' y' ⟨b0'', hb0'', hs'⟩
    rw [hm0] at hb0''; cases hb0''
    exact hop_bwd (c' := withBlocks c bl') HH H hok' hs' (Steps.refl x0) hr0
  refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, ?_⟩
  · obtain ⟨es', y', hy', he'⟩ := (execEntry_iff_path (c := withBlocks c bl') st vals t r).mp h'
    obtain ⟨es, y, hs, hn⟩ := back es' y' hy'
    exact (execEntry_iff_path (c := c) st vals t r).mpr
      ⟨es, y, ⟨b0, hb0, hs⟩, hop_bwd_end (c' := withBlocks c bl') HH H he' hn (fun k hk => hok' es y k hs hk)⟩
  · obtain ⟨es, y, ⟨b0'', hb0'', hs⟩, he⟩ := (execEntry_iff_path (c := c) st vals t r).mp h'
    rw [hb0] at hb0''; cases hb0''
    obtain ⟨es', y', hs', he'⟩ := hop_fwd (c' := withBlocks c bl') HH H hs he hr0
    exact (execEntry_iff_path (c := withBlocks c bl') st vals t r).mpr ⟨es', y', ⟨_, hm0, hs'⟩, he'⟩
  · intro es' y' k hy' hk
    obtain ⟨es, y, hs, hn⟩ := back es' y' hy'
    obtain ⟨hk', hle⟩ := hop_bwd_reads (c' := withBlocks c bl') HH H hn hk
    obtain ⟨v, hv⟩ := hok' es y k hs hk'
    exact ⟨v, hle.rd hv⟩

/-- **The preservation statement of `+remove-hops` holds.** -/
theorem hopsKeeps [MapKeys Map] (fuel : Nat) : HopsKeeps (Map := Map) fuel :=
  fun c _ _ _ ht hnd hpc h => hops_keeps c ht hnd hpc h

end Opt
end SkaModel
end Formalization
