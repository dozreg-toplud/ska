import lemmas.Ska.OptSwitchTree
import lemmas.Ska.OptDeadSim

/-!
# `+switch-chains`: a region of blocks replaced, kept by a simulation

The pass replaces a region of blocks (a chain) by another (a search tree),
entered only through one block, the head, whose end is a `%clq` in both codes
(only its targets change).  This file proves, for any such replacement, that
the code is kept (`region_keeps`), given the macro step at the head
(`HeadStep`): from the end of a head, the code before runs through its region
to a block `T` outside it, the code after runs through its own region to the
same `T`, the two arriving in the relation `SwA`, and every configuration the
code after passes on the way meets `GoodAt` (its reads read values, its
pending arguments are there, its first op does not crash when
`+remove-dead-code` may drop it).

`RegionHyp M M' I H Z`: the labels `I` are inside the region, `H` are the
heads, `Z` the registers only the region mentions.  Outside `I` and `H` a
block is unchanged; a head keeps its parameters and body and ends in a `%clq`
on the same register before and after; no reachable block outside `I` and `H`
jumps into `I`; no reachable block outside `I` mentions `Z`; block `0` is not
in `I`.

The relation `SwA` (the two codes at the same place outside `I`, registers
agreeing off `Z`) is matched step for step, but at the end of a head, where
the macro step runs.  `SwR x x'` says that the code before goes on from `x`
to some `xT`, the code after from `x'` to some `x'T` through good
configurations, and `SwA xT x'T`: either side may be behind.  For example on
a tagged chain, after the `%clq` of the head took its yes side, the code
before is at the first test while the code after still runs its tree.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

section
variable {σ : Type}

/-- What a configuration of the code after must meet: `ReadsOK`, `ArgsOK`
and `LocalOK` at it. -/
def GoodAt (lib : Lib) (O : Oracle σ) (gul : Noun) (x : Cfg σ Map) : Prop :=
  (∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v) ∧
  (∀ k, some k ∈ x.params → (HoonMap.get x.regs k).isSome) ∧
  (∀ p rest, x.params = [] → x.b.par = [] → x.b.body = p :: rest → (safeAssign p).isSome →
    (execPole lib O gul x.st p x.regs x.t).isSome)

/-- A path of steps every configuration of which but the last is good. -/
inductive GoodTo (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) : Cfg σ Map → Cfg σ Map → Prop
  | here (x : Cfg σ Map) : GoodTo lib O c gul x x
  | step {x y z : Cfg σ Map} {e : List (Nat × Nat)} : GoodAt lib O gul x → Step lib O c gul x e y →
      GoodTo lib O c gul y z → GoodTo lib O c gul x z

theorem GoodTo.steps {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {x z : Cfg σ Map}
    (h : GoodTo lib O c gul x z) : ∃ es, Steps lib O c gul x es z := by
  induction h with
  | here => exact ⟨[], Steps.refl _⟩
  | step _ s _ ih => obtain ⟨es, h⟩ := ih; exact ⟨_, Steps.step s h⟩

end

/-- **What the replacement of a region must meet.** -/
structure RegionHyp (M M' : Map Blob) (I H Z : Nat → Prop) : Prop where
  same : ∀ k, ¬ I k → ¬ H k → HoonMap.get M' k = HoonMap.get M k
  head : ∀ k, H k → ¬ I k ∧ ∃ b s z o z' o', HoonMap.get M k = some b ∧ b.fin = Termin.clq s z o ∧
    HoonMap.get M' k = some { b with fin := Termin.clq s z' o' }
  noI : ∀ k b j, Reach M k → ¬ I k → ¬ H k → HoonMap.get M k = some b → j ∈ getJmps b.fin → ¬ I j.there
  ment : ∀ k b, Reach M k → ¬ I k → HoonMap.get M k = some b → ∀ r ∈ blobMentions b, ¬ Z r
  zero : ¬ I 0

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map} {I H Z : Nat → Prop}

/-- **The two codes at the same place**, outside the region: the same label,
pending arguments, trace and state, a reachable block, the same remaining
block but for the end (which after is the end of the block after), registers
agreeing off `Z`. -/
def SwA (M M' : Map Blob) (I Z : Nat → Prop) (x x' : Cfg σ Map) : Prop :=
  x'.lab = x.lab ∧ x'.params = x.params ∧ x'.t = x.t ∧ x'.st = x.st ∧ Reach M x.lab ∧ ¬ I x.lab ∧
  (∃ b0 b0', HoonMap.get M x.lab = some b0 ∧ HoonMap.get M' x.lab = some b0' ∧ x.b.fin = b0.fin ∧
    x'.b = { x.b with fin := b0'.fin } ∧ ∀ r ∈ blobMentions x.b, r ∈ blobMentions b0) ∧
  (∀ k, some k ∈ x.params → ¬ Z k) ∧ Agr (fun k => ¬ Z k) x.regs x'.regs

/-- **The macro step at the end of a head**, which a region must supply. -/
def HeadStep (lib : Lib) (O : Oracle σ) (gul : Noun) (c c' : Straight Map) (I H Z : Nat → Prop) : Prop :=
  ∀ x x' : Cfg σ Map, SwA c.blocks c'.blocks I Z x x' → H x.lab → x.params = [] → x.b.par = [] →
    x.b.body = [] → ((taken x.regs x.b.fin).isSome ∨ (taken x'.regs x'.b.fin).isSome) →
    ∃ xT x'T es, Steps lib O c gul x es xT ∧ GoodTo lib O c' gul x' x'T ∧
      SwA c.blocks c'.blocks I Z xT x'T ∧ xT.lab ≠ x.lab ∧ x'T.lab ≠ x'.lab

/-- **Either side may be behind.** -/
def SwR (lib : Lib) (O : Oracle σ) (gul : Noun) (c c' : Straight Map) (I Z : Nat → Prop) (x x' : Cfg σ Map) :
    Prop :=
  ∃ xT x'T es, Steps lib O c gul x es xT ∧ GoodTo lib O c' gul x' x'T ∧ SwA c.blocks c'.blocks I Z xT x'T

theorem swR_of_A {x x' : Cfg σ Map} (h : SwA c.blocks c'.blocks I Z x x') : SwR lib O gul c c' I Z x x' :=
  ⟨x, x', [], Steps.refl _, GoodTo.here _, h⟩

theorem mentions_par (b : Blob) : ∀ r ∈ blobMentions { b with par := [] }, r ∈ blobMentions b := by
  intro r hr
  simp only [blobMentions, List.mem_append, List.nil_append] at hr ⊢
  rcases hr with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem mentions_body {b : Blob} {p : Pole} {rest : List Pole} (hb : b.body = p :: rest) :
    ∀ r ∈ blobMentions { b with body := rest }, r ∈ blobMentions b := by
  intro r hr
  simp only [blobMentions, List.mem_append, List.mem_flatMap, hb, List.mem_cons] at hr ⊢
  rcases hr with (h | h) | ⟨q, hq, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨q, Or.inr hq, h⟩

theorem mentions_op {b : Blob} {p : Pole} {rest : List Pole} (hb : b.body = p :: rest) :
    ∀ r ∈ poleRegs p, r ∈ blobMentions b := by
  intro r hr
  simp only [blobMentions, List.mem_append, List.mem_flatMap, hb, List.mem_cons]
  exact Or.inr ⟨p, Or.inl rfl, hr⟩

theorem mentions_fin (b : Blob) : ∀ r ∈ finRegs b.fin, r ∈ blobMentions b := by
  intro r hr
  simp only [blobMentions, List.mem_append]
  exact Or.inl (Or.inr hr)

variable (hR : RegionHyp c.blocks c'.blocks I H Z)
include hR

/-- The block after at a label outside the region, from the block before. -/
theorem region_blk {k : Nat} {b : Blob} (hk : ¬ I k) (hb : HoonMap.get c.blocks k = some b) :
    ∃ b', HoonMap.get c'.blocks k = some b' ∧ b' = { b with fin := b'.fin } ∧ b'.par = b.par := by
  by_cases hh : H k
  · obtain ⟨-, b1, s, z, o, z', o', hb1, -, hb1'⟩ := hR.head k hh
    rw [hb] at hb1; cases hb1
    exact ⟨_, hb1', rfl, rfl⟩
  · exact ⟨b, by rw [hR.same k hk hh, hb], rfl, rfl⟩

/-- The block before at a label outside the region, from the block after. -/
theorem region_blk' {k : Nat} {b' : Blob} (hk : ¬ I k) (hb' : HoonMap.get c'.blocks k = some b') :
    ∃ b, HoonMap.get c.blocks k = some b ∧ b' = { b with fin := b'.fin } := by
  by_cases hh : H k
  · obtain ⟨-, b1, s, z, o, z', o', hb1, -, hb1'⟩ := hR.head k hh
    rw [hb'] at hb1'; cases hb1'
    exact ⟨b1, hb1, rfl⟩
  · rw [hR.same k hk hh] at hb'
    exact ⟨b', hb', rfl⟩

/-- The relation at the start of a block reached by a jump from outside the
region. -/
theorem swA_jump {lab : Nat} {b0 b2 : Blob} {j : Jmp} {R R' : Map (Option Noun)} {t : Trace} {st : σ}
    (hreach : Reach c.blocks lab) (hI : ¬ I lab) (hb0 : HoonMap.get c.blocks lab = some b0)
    (hj : j ∈ getJmps b0.fin) (hI2 : ¬ I j.there) (hb2 : HoonMap.get c.blocks j.there = some b2)
    {b2' : Blob} (hb2' : HoonMap.get c'.blocks j.there = some b2') (he : b2' = { b2 with fin := b2'.fin })
    (hag : Agr (fun k => ¬ Z k) R R') :
    SwA c.blocks c'.blocks I Z (⟨j.there, b2, j.args, R, t, st⟩ : Cfg σ Map) ⟨j.there, b2', j.args, R', t, st⟩ :=
  ⟨rfl, rfl, rfl, rfl, Reach.jump hreach hb0 hj, hI2, ⟨b2, b2', hb2, hb2', rfl, he, fun _ h => h⟩,
    fun k hk => hR.ment lab b0 hreach hI hb0 k (mentions_fin b0 k (jmp_finRegs hj hk)), hag⟩

/-- The end of the block after, outside a head, is that of the block before. -/
theorem swA_fin {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') (hh : ¬ H x.lab) :
    x'.b = x.b := by
  obtain ⟨-, -, -, -, -, hI, ⟨b0, b0', hb0, hb0', hf, hb', -⟩, -, -⟩ := hA
  rw [hR.same _ hI hh, hb0] at hb0'
  cases hb0'
  rw [hb', ← hf]

/-- The registers the remaining block mentions are off `Z`. -/
theorem swA_ment {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') :
    ∀ r ∈ blobMentions x.b, ¬ Z r := by
  obtain ⟨-, -, -, -, hreach, hI, ⟨b0, b0', hb0, -, -, -, hm⟩, -, -⟩ := hA
  exact fun r hr => hR.ment _ b0 hreach hI hb0 r (hm r hr)

/-- A head ends in a `%clq` on one register, before and after. -/
theorem swA_head {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') (hh : H x.lab) :
    ∃ s z o z' o', x.b.fin = Termin.clq s z o ∧ x'.b = { x.b with fin := Termin.clq s z' o' } := by
  obtain ⟨-, -, -, -, -, -, ⟨b0, b0', hb0, hb0', hf, hb', -⟩, -, -⟩ := hA
  obtain ⟨-, b1, s, z, o, z', o', hb1, hf1, hb1'⟩ := hR.head _ hh
  rw [hb0] at hb1; cases hb1
  rw [hb0'] at hb1'; cases hb1'
  exact ⟨s, z, o, z', o', by rw [hf, hf1], hb'⟩

/-- After a pass. -/
theorem swA_pass {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') {R R' : Map (Option Noun)}
    (hR1 : evalPassLoop x.params x.b.par x.regs = some R) (hR1' : evalPassLoop x.params x.b.par x'.regs = some R')
    (hpar : ∀ k ∈ x.b.par, HoonMap.get R k = HoonMap.get R' k) :
    SwA c.blocks c'.blocks I Z { x with b := { x.b with par := [] }, params := [], regs := R }
      { x' with b := { x'.b with par := [] }, params := [], regs := R' } := by
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  refine ⟨hl, rfl, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, by rw [hb'], fun r hr => hm r (mentions_par _ r hr)⟩,
    fun k hk => by simp at hk, fun k hk => ?_⟩
  by_cases hkp : k ∈ x.b.par
  · exact hpar k hkp
  · rw [Comp.evalPassLoop_frame _ _ _ _ hR1 k hkp, Comp.evalPassLoop_frame _ _ _ _ hR1' k hkp]
    exact hag k hk

/-- After an op. -/
theorem swA_op {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') {p : Pole} {rest : List Pole}
    (hb : x.b.body = p :: rest) {R R' : Map (Option Noun)} {t2 : Trace} {st2 : σ}
    (hag2 : Agr (fun k => ¬ Z k) R R') :
    SwA c.blocks c'.blocks I Z { x with b := { x.b with body := rest }, regs := R, t := t2, st := st2 }
      { x' with b := { x'.b with body := rest }, regs := R', t := t2, st := st2 } := by
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  exact ⟨hl, hpe, rfl, rfl, hreach, hI, ⟨b0, b0', hb0, hb0', hf, by rw [hb'],
    fun r hr => hm r (mentions_body hb r hr)⟩, hz, hag2⟩

/-- The pending arguments pass the same units. -/
theorem swA_argU {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') :
    x.params.map (argU x.regs) = x.params.map (argU x'.regs) := by
  obtain ⟨-, -, -, -, -, -, -, hz, hag⟩ := hA
  exact List.map_congr_left (fun a ha => by
    cases a with
    | none => rfl
    | some k => exact hag k (hz k ha))

/-- **Forward, out of a head's end**: a step of the code before is matched. -/
theorem swA_fwd (HS : HeadStep lib O gul c c' I H Z) {x y x' : Cfg σ Map} {e : List (Nat × Nat)}
    (hs : Step lib O c gul x e y) (hA : SwA c.blocks c'.blocks I Z x x') :
    ∃ es' y', Steps lib O c' gul x' es' y' ∧ SwR lib O gul c c' I Z y y' := by
  have hA0 := hA
  have hM := swA_ment hR hA
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  cases hs with
  | @pass R hne hR1 =>
    obtain ⟨hck, hR1⟩ := evalPass_check hR1
    obtain ⟨R', hR1', hpar⟩ := OAg.fwd (passLoop_agr x.params x.params x.b.par x.regs x'.regs hck hck
      (swA_argU hR hA0)) hR1
    have hne' : x'.params ≠ [] ∨ x'.b.par ≠ [] := by rw [hpe, hb']; exact hne
    refine ⟨_, _, Steps.step (Step.pass hne' (R := R') (by rw [hpe, hb', evalPass_ok hck]; exact hR1'))
      (Steps.refl _), swR_of_A (swA_pass hR hA0 hR1 hR1' hpar)⟩
  | @op p rest n R2 t2 st2 hp hq hbd hpole =>
    obtain ⟨R2', hR2', hag2⟩ := PAg.fwd (execPole_agr lib O gul x.st p x.t hag
      (fun k hk => hM k (mentions_op hbd k hk))) hpole
    have hbd' : x'.b.body = p :: rest := by rw [hb']; exact hbd
    refine ⟨_, _, Steps.step (Step.op (by rw [hpe]; exact hp) (by rw [hb']; exact hq) hbd'
      (by rw [hst, ht]; exact hR2')) (Steps.refl _), swR_of_A ?_⟩
    exact swA_op hR hA0 hbd hag2
  | @jump j b2 hp hq hbd htk hb2 =>
    by_cases hh : H x.lab
    · obtain ⟨xT, x'T, es, hT, hg, hAT, hlT, -⟩ := HS x x' hA0 hh hp hq hbd (Or.inl (by rw [htk]; rfl))
      cases hT with
      | refl => exact absurd rfl hlT
      | step s1 rest1 =>
        have s0 : Step lib O c gul x [(x.lab, j.there)] ⟨j.there, b2, j.args, x.regs, x.t, x.st⟩ :=
          Step.jump hp hq hbd htk hb2
        obtain ⟨-, rfl⟩ := step_det s0 s1
        exact ⟨[], x', Steps.refl _, _, _, _, rest1, hg, hAT⟩
    · have hfx : x'.b = x.b := swA_fin hR hA0 hh
      have htk' : taken x'.regs x'.b.fin = some j := by
        rw [hfx, taken_agr hag (fun k hk => hM k (mentions_fin _ k hk))]; exact htk
      rw [hf] at htk
      have hI2 := hR.noI x.lab b0 j hreach hI hh hb0 (taken_mem htk)
      obtain ⟨b2', hb2', he, -⟩ := region_blk hR hI2 hb2
      have s' : Step lib O c' gul x' [(x'.lab, j.there)] ⟨j.there, b2', j.args, x'.regs, x'.t, x'.st⟩ :=
        Step.jump (by rw [hpe]; exact hp) (by rw [hfx]; exact hq) (by rw [hfx]; exact hbd) htk' hb2'
      refine ⟨_, _, Steps.step s' (Steps.refl _), swR_of_A ?_⟩
      rw [ht, hst]
      exact swA_jump hR hreach hI hb0 (taken_mem htk) hI2 hb2 hb2' he hag

/-- **Backward, out of a head's end**: a step of the code after is matched. -/
theorem swA_bwd (HS : HeadStep lib O gul c c' I H Z) {x x' y' : Cfg σ Map} {e : List (Nat × Nat)}
    (hs : Step lib O c' gul x' e y') (hA : SwA c.blocks c'.blocks I Z x x') :
    ∃ es y, Steps lib O c gul x es y ∧ SwR lib O gul c c' I Z y y' := by
  have hA0 := hA
  have hM := swA_ment hR hA
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  cases hs with
  | @pass R' hne hR1' =>
    have hR2 : evalPass x.params x.b.par x'.regs = some R' := by rw [hpe, hb'] at hR1'; exact hR1'
    have hne0 : x.params ≠ [] ∨ x.b.par ≠ [] := by rw [hpe, hb'] at hne; exact hne
    obtain ⟨hck, hR1''⟩ := evalPass_check hR2
    obtain ⟨R, hR1, hpar⟩ := OAg.bwd (passLoop_agr x.params x.params x.b.par x.regs x'.regs hck hck
      (swA_argU hR hA0)) hR1''
    exact ⟨_, _, Steps.step (Step.pass hne0 (R := R) (by rw [evalPass_ok hck]; exact hR1)) (Steps.refl _),
      swR_of_A (swA_pass hR hA0 hR1 hR1'' hpar)⟩
  | @op p rest n R2' t2 st2 hp hq hbd hpole =>
    have hq0 : x.b.par = [] := by rw [hb'] at hq; exact hq
    have hbd0 : x.b.body = p :: rest := by rw [hb'] at hbd; exact hbd
    rw [hpe] at hp
    rw [hst, ht] at hpole
    obtain ⟨R2, hR2, hag2⟩ := PAg.bwd (execPole_agr lib O gul x.st p x.t hag
      (fun k hk => hM k (mentions_op hbd0 k hk))) hpole
    refine ⟨_, _, Steps.step (Step.op hp hq0 hbd0 hR2) (Steps.refl _), swR_of_A ?_⟩
    have := swA_op hR hA0 hbd0 (t2 := t2) (st2 := st2) hag2
    rw [hb'] at this ⊢
    exact this
  | @jump j b2' hp hq hbd htk' hb2' =>
    have hp0 : x.params = [] := by rw [← hpe]; exact hp
    have hq0 : x.b.par = [] := by rw [hb'] at hq; exact hq
    have hbd0 : x.b.body = [] := by rw [hb'] at hbd; exact hbd
    by_cases hh : H x.lab
    · obtain ⟨xT, x'T, es, hT, hg, hAT, -, hlT⟩ := HS x x' hA0 hh hp0 hq0 hbd0 (Or.inr (by rw [htk']; rfl))
      cases hg with
      | here => exact absurd rfl hlT
      | step _ s1 rest1 =>
        have s0 : Step lib O c' gul x' [(x'.lab, j.there)] ⟨j.there, b2', j.args, x'.regs, x'.t, x'.st⟩ :=
          Step.jump hp hq hbd htk' hb2'
        obtain ⟨-, rfl⟩ := step_det s0 s1
        exact ⟨[], x, Steps.refl _, _, _, _, hT, rest1, hAT⟩
    · have hfx : x'.b = x.b := swA_fin hR hA0 hh
      rw [hfx] at htk'
      have htk : taken x.regs x.b.fin = some j := by
        rw [← taken_agr hag (fun k hk => hM k (mentions_fin _ k hk))]; exact htk'
      have htk0 := htk
      rw [hf] at htk0
      have hI2 := hR.noI x.lab b0 j hreach hI hh hb0 (taken_mem htk0)
      obtain ⟨b2, hb2, he⟩ := region_blk' hR hI2 hb2'
      refine ⟨_, _, Steps.step (Step.jump hp0 hq0 hbd0 htk hb2) (Steps.refl _), swR_of_A ?_⟩
      rw [ht, hst]
      exact swA_jump hR hreach hI hb0 (taken_mem htk0) hI2 hb2 hb2' he hag

/-- The end of a `%clq` does not depend on its targets. -/
theorem endOf_clq (x : Cfg σ Map) (b : Blob) {s : Nat} {z o z' o' : Jmp} (h : b.fin = Termin.clq s z o)
    (h' : x.b = { b with fin := Termin.clq s z' o' }) :
    endOf lib O gul x = endOf lib O gul { x with b := b } := by
  obtain ⟨lab, xb, params, regs, t, st⟩ := x
  obtain ⟨par, body, fin⟩ := b
  simp only at h h' ⊢
  subst h h'
  unfold endOf
  simp only
  try (split <;> (try rfl) <;> (cases body <;> rfl))

/-- **The same end.** -/
theorem swA_endOf {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') :
    endOf lib O gul x' = endOf lib O gul x := by
  have hA0 := hA
  have hM := swA_ment hR hA
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  have core : ∀ y : Cfg σ Map, y.b = x.b → y.params = x.params → y.t = x.t → y.st = x.st →
      Agr (fun k => ¬ Z k) x.regs y.regs → endOf lib O gul y = endOf lib O gul x := by
    intro y e1 e2 e3 e4 e5
    refine endOf_agr e2 (by rw [e1]) (by rw [e1]) e3 e4 e5 (fun _ _ => ?_)
    cases hbd : x.b.body with
    | nil => exact Or.inl ⟨rfl, by rw [e1, hbd], fun k hk => hM k (mentions_fin _ k hk)⟩
    | cons p rest => exact Or.inr ⟨p, rest, rest, rfl, by rw [e1, hbd], fun k hk => hM k (mentions_op hbd k hk)⟩
  by_cases hh : H x.lab
  · obtain ⟨s, z, o, z', o', hfc, hb2⟩ := swA_head hR hA0 hh
    rw [endOf_clq hR x' x.b hfc hb2]
    exact core { x' with b := x.b } rfl hpe ht hst hag
  · exact core x' (swA_fin hR hA0 hh) hpe ht hst hag

/-- **The same reads.** -/
theorem swA_reads {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') {k : Nat} (hk : ReadsAt gul x' k) :
    ReadsAt gul x k ∧ read k x'.regs = read k x.regs := by
  have hA0 := hA
  have hM := swA_ment hR hA
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  have hfr : finReads x'.b.fin = finReads x.b.fin := by
    by_cases hh : H x.lab
    · obtain ⟨s, z, o, z', o', hfc, hb2⟩ := swA_head hR hA0 hh
      rw [hb2, hfc]; rfl
    · rw [swA_fin hR hA0 hh]
  obtain ⟨hp, hq, hk⟩ := hk
  rw [hb'] at hq
  rw [hpe] at hp
  rcases hk with ⟨p, rest, hbd, hk⟩ | ⟨hbd, hk⟩
  · have hbd : x.b.body = p :: rest := by rw [hb'] at hbd; exact hbd
    exact ⟨⟨hp, hq, Or.inl ⟨p, rest, hbd, hk⟩⟩, hag.rd (hM k (mentions_op hbd k (poleReads_sub hk)))⟩
  · rw [hb'] at hbd
    rw [hfr] at hk
    exact ⟨⟨hp, hq, Or.inr ⟨hbd, hk⟩⟩, hag.rd (hM k (mentions_fin _ k (finReads_sub hk)))⟩

/-- The same op, on registers that agree on what it mentions. -/
theorem swA_local {x x' : Cfg σ Map} (hA : SwA c.blocks c'.blocks I Z x x') {p : Pole} {rest : List Pole}
    (hbd : x'.b.body = p :: rest) (h : (execPole lib O gul x.st p x.regs x.t).isSome) :
    (execPole lib O gul x'.st p x'.regs x'.t).isSome := by
  have hM := swA_ment hR hA
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hb', hm⟩, hz, hag⟩ := hA
  have hbd : x.b.body = p :: rest := by rw [hb'] at hbd; exact hbd
  obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨ton, R1, t1, s1⟩ := r1
  obtain ⟨R1', hR1', -⟩ := (execPole_agr lib O gul x.st p x.t hag
    (fun k hk => hM k (mentions_op hbd k hk))).fwd hr1
  rw [ht, hst, hR1']; rfl

variable (HS : HeadStep lib O gul c c' I H Z)
include HS

theorem swR_fwd_step {x y x' : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c gul x e y)
    (hr : SwR lib O gul c c' I Z x x') : ∃ es' y', Steps lib O c' gul x' es' y' ∧ SwR lib O gul c c' I Z y y' := by
  obtain ⟨xT, x'T, es, hT, hg, hA⟩ := hr
  cases hT with
  | refl =>
    obtain ⟨es1, hs1⟩ := hg.steps
    obtain ⟨es2, y', hs2, hr2⟩ := swA_fwd hR HS hs hA
    exact ⟨_, y', steps_trans hs1 hs2, hr2⟩
  | step s1 rest1 =>
    obtain ⟨-, rfl⟩ := step_det hs s1
    exact ⟨[], x', Steps.refl _, _, _, _, rest1, hg, hA⟩

theorem swR_bwd_step {x x' y' : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c' gul x' e y')
    (hr : SwR lib O gul c c' I Z x x') : ∃ es y, Steps lib O c gul x es y ∧ SwR lib O gul c c' I Z y y' := by
  obtain ⟨xT, x'T, es, hT, hg, hA⟩ := hr
  cases hg with
  | here =>
    obtain ⟨es2, y, hs2, hr2⟩ := swA_bwd hR HS hs hA
    exact ⟨_, y, steps_trans hT hs2, hr2⟩
  | step _ s1 rest1 =>
    obtain ⟨-, rfl⟩ := step_det hs s1
    exact ⟨[], x, Steps.refl _, _, _, _, hT, rest1, hA⟩

theorem swR_fwd {x z : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es z) {r : Tone × σ}
    (he : endOf lib O gul z = some r) : ∀ {x' : Cfg σ Map}, SwR lib O gul c c' I Z x x' →
      ∃ es' z', Steps lib O c' gul x' es' z' ∧ endOf lib O gul z' = some r := by
  induction hs with
  | refl =>
    intro x' hr
    obtain ⟨xT, x'T, es, hT, hg, hA⟩ := hr
    cases hT with
    | refl =>
      obtain ⟨es1, hs1⟩ := hg.steps
      exact ⟨_, _, hs1, by rw [swA_endOf hR hA]; exact he⟩
    | step s1 _ =>
      rw [step_endOf_none s1] at he; cases he
  | step s _ ih =>
    intro x' hr
    obtain ⟨es1, y', hs1, hr1⟩ := swR_fwd_step hR HS s hr
    obtain ⟨es2, z', hs2, he'⟩ := ih he hr1
    exact ⟨_, z', steps_trans hs1 hs2, he'⟩

theorem swR_bwd {x' z' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Steps lib O c' gul x' es' z') :
    ∀ {x : Cfg σ Map}, SwR lib O gul c c' I Z x x' → ∃ es z, Steps lib O c gul x es z ∧ SwR lib O gul c c' I Z z z' := by
  induction hs with
  | refl => intro x hr; exact ⟨[], x, Steps.refl _, hr⟩
  | step s _ ih =>
    intro x hr
    obtain ⟨es1, y, hs1, hr1⟩ := swR_bwd_step hR HS s hr
    obtain ⟨es2, z, hs2, hr2⟩ := ih hr1
    exact ⟨_, z, steps_trans hs1 hs2, hr2⟩

end Sim

/-- **A region replaced keeps the code**, given the macro step at its heads. -/
theorem region_keeps (c : Straight Map) (M' : Map Blob) {I H Z : Nat → Prop}
    (hR : RegionHyp c.blocks M' I H Z)
    (HS : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun), HeadStep lib O gul c (withBlocks c M') I H Z) :
    Keeps c (withBlocks c M') := by
  have hR' : RegionHyp c.blocks (withBlocks c M').blocks I H Z := hR
  refine ⟨rfl, rfl, ?_, fun lib σ O gul st vals t ⟨hok, hargs, hloc⟩ => ?_⟩
  · show (HoonMap.get M' 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par
    cases hb : HoonMap.get c.blocks 0 with
    | none =>
      cases hb' : HoonMap.get M' 0 with
      | none => rfl
      | some b' =>
        obtain ⟨b, hb2, -⟩ := region_blk' hR' hR.zero hb'
        rw [hb] at hb2; cases hb2
    | some b =>
      obtain ⟨b', hb', -, hp⟩ := region_blk hR' hR.zero hb
      have : HoonMap.get M' 0 = some b' := hb'
      rw [this]; simp [hp]
  have HS' := HS lib σ O gul
  have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c M') (gul := gul) st vals t es' y' →
      ∃ b0 es y, HoonMap.get c.blocks 0 = some b0 ∧ Path.Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y ∧
        SwR lib O gul c (withBlocks c M') I Z y y' := by
    rintro es' y' ⟨b0', hb0', hs'⟩
    obtain ⟨b0, hb0, he⟩ := region_blk' hR' hR.zero hb0'
    have hA : SwA c.blocks (withBlocks c M').blocks I Z (⟨0, b0, [], regsOf vals, t, st⟩ : Cfg σ Map)
        ⟨0, b0', [], regsOf vals, t, st⟩ :=
      ⟨rfl, rfl, rfl, rfl, Reach.zero, hR.zero, ⟨b0, b0', hb0, hb0', rfl, he, fun _ h => h⟩,
        fun k hk => by simp at hk, fun _ _ => rfl⟩
    obtain ⟨es, y, hs, hr⟩ := swR_bwd hR' HS' hs' (swR_of_A hA)
    exact ⟨b0, es, y, hb0, hs, hr⟩
  refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, fun es' y' k hy' hk => ?_,
    fun es' y' k hy' hk => ?_, fun es' y' p rest hy' hp hq hb hsa => ?_⟩
  · obtain ⟨es', y', hy', he'⟩ := (Path.execEntry_iff_path (c := withBlocks c M') st vals t r).mp h'
    obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      exact (Path.execEntry_iff_path (c := c) st vals t r).mpr
        ⟨_, yT, ⟨b0, hb0, steps_trans hs hT⟩, by rw [← swA_endOf hR' hA]; exact he'⟩
    | step _ s1 _ => rw [step_endOf_none s1] at he'; cases he'
  · obtain ⟨es, y, ⟨b0, hb0, hs⟩, he⟩ := (Path.execEntry_iff_path (c := c) st vals t r).mp h'
    obtain ⟨b0', hb0', he0, -⟩ := region_blk hR' hR.zero hb0
    have hA : SwA c.blocks (withBlocks c M').blocks I Z (⟨0, b0, [], regsOf vals, t, st⟩ : Cfg σ Map)
        ⟨0, b0', [], regsOf vals, t, st⟩ :=
      ⟨rfl, rfl, rfl, rfl, Reach.zero, hR.zero, ⟨b0, b0', hb0, hb0', rfl, he0, fun _ h => h⟩,
        fun k hk => by simp at hk, fun _ _ => rfl⟩
    obtain ⟨es', z', hs', he'⟩ := swR_fwd hR' HS' hs he (swR_of_A hA)
    exact (Path.execEntry_iff_path (c := withBlocks c M') st vals t r).mpr ⟨es', z', ⟨_, hb0', hs'⟩, he'⟩
  · obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      obtain ⟨hk', hrd⟩ := swA_reads hR' hA hk
      obtain ⟨v, hv⟩ := hok _ yT k ⟨b0, hb0, steps_trans hs hT⟩ hk'
      exact ⟨v, by rw [hrd, hv]⟩
    | step hgood _ _ => exact hgood.1 k hk
  · obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      obtain ⟨-, hpe, -, -, -, -, -, hz, hag⟩ := hA
      have hk0 : some k ∈ yT.params := by rw [← hpe]; exact hk
      rw [← hag k (hz k hk0)]
      exact hargs _ yT k ⟨b0, hb0, steps_trans hs hT⟩ hk0
    | step hgood _ _ => exact hgood.2.1 k hk
  · obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      have hA0 := hA
      obtain ⟨-, hpe, -, -, -, -, ⟨b1, b1', -, -, -, hb', -⟩, -, -⟩ := hA
      have hp0 : yT.params = [] := by rw [← hpe]; exact hp
      have hq0 : yT.b.par = [] := by rw [hb'] at hq; exact hq
      have hb0' : yT.b.body = p :: rest := by rw [hb'] at hb; exact hb
      exact swA_local hR' hA0 hb (hloc _ yT p rest ⟨b0, hb0, steps_trans hs hT⟩ hp0 hq0 hb0' hsa)
    | step hgood _ _ => exact hgood.2.2 p rest hp hq hb hsa

end Opt
end SkaModel
end Formalization
