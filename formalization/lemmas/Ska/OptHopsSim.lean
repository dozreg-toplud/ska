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

end Sim

end Opt
end SkaModel
end Formalization
