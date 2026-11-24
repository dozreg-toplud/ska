import lemmas.Ska.OptSwitchTag

/-!
# `+switch-chains`: a region replaced, with heads whose body changes

`OptSwitchSim.lean` proves `region_keeps` for heads that keep their body and
change only the targets of their `%clq`.  A plain chain changes its head's
body too: the code after drops the `%imm` of the first constant (the `filter`
of `switchPlain`) and appends the root's ops, and the head's end becomes the
root's end.  This file proves the same theorem for such heads
(`region_keepsG`).

The body after of a head `k` is `gBody D E k`: the ops of the body before
that `D k` keeps, then `E k`.  A dropped op is an `%imm` into a register of
`Z` (`RegionHypG.drop`), so the code before runs it alone, and the relation
lets it run ahead: `SwG` holds only where the next op of the code before (if
it has no parameters to pass) is one the code after keeps.  The head's end
before, and the appended ops and end after, are the business of the macro
step (`HeadStepG`), which starts at the end of the head's body before, as
`HeadStep` does, and is given that the reads of the code before there read
values (`ReadsOK` of the code before, threaded as `RdOK`).  At that point the
two codes are never compared otherwise: the macro step always moves both.
For example on a plain chain at a head `o` with body `[%imm 9 r15]` and end
`%eqq r15 d` (the dump of `switchcheck.hoon`'s `pla5`, before), the code
after has body `[]` and the end `%lti 5 d`: the code before runs the `%imm`
alone, and both meet again at the hit or the final miss.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- The body after at a head: the ops of the body before that `D` keeps, then
`E`. -/
def gBody (D : Nat → Pole → Bool) (E : Nat → List Pole) (k : Nat) (B : List Pole) : List Pole :=
  B.filter (fun p => !D k p) ++ E k

theorem gBody_keep {D : Nat → Pole → Bool} {E : Nat → List Pole} {k : Nat} {p : Pole} {rest : List Pole}
    (h : D k p = false) : gBody D E k (p :: rest) = p :: gBody D E k rest := by
  simp [gBody, List.filter_cons, h]

theorem gBody_drop {D : Nat → Pole → Bool} {E : Nat → List Pole} {k : Nat} {p : Pole} {rest : List Pole}
    (h : D k p = true) : gBody D E k (p :: rest) = gBody D E k rest := by
  simp [gBody, List.filter_cons, h]

theorem gBody_off {D : Nat → Pole → Bool} {E : Nat → List Pole} {k : Nat} (hD : ∀ p, D k p = false)
    (hE : E k = []) : ∀ B, gBody D E k B = B
  | [] => by simp [gBody, hE]
  | p :: rest => by rw [gBody_keep (hD p), gBody_off hD hE rest]

/-- **What the replacement of a region must meet**, heads with a new body. -/
structure RegionHypG (M M' : Map Blob) (I H Z : Nat → Prop) (D : Nat → Pole → Bool) (E : Nat → List Pole) :
    Prop where
  same : ∀ k, ¬ I k → ¬ H k → HoonMap.get M' k = HoonMap.get M k
  head : ∀ k, H k → ¬ I k ∧ ∃ b b', HoonMap.get M k = some b ∧ HoonMap.get M' k = some b' ∧
    b'.par = b.par ∧ b'.body = gBody D E k b.body
  off : ∀ k, ¬ H k → (∀ p, D k p = false) ∧ E k = []
  drop : ∀ k p, D k p = true → ∃ n r, p = Pole.imm n r ∧ Z r
  noI : ∀ k b j, Reach M k → ¬ I k → ¬ H k → HoonMap.get M k = some b → j ∈ getJmps b.fin → ¬ I j.there
  ment : ∀ k b, Reach M k → ¬ I k → ¬ H k → HoonMap.get M k = some b → ∀ r ∈ blobMentions b, ¬ Z r
  mentH : ∀ k b, Reach M k → H k → HoonMap.get M k = some b →
    (∀ r ∈ b.par, ¬ Z r) ∧ ∀ p ∈ b.body, D k p = false → ∀ r ∈ poleRegs p, ¬ Z r
  zero : ¬ I 0

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map} {I H Z : Nat → Prop}
  {D : Nat → Pole → Bool} {E : Nat → List Pole}

/-- The two codes at the same place, outside the region, before the
normalization: the remaining block before is a suffix of its block (with its
parameters or none), the block after has the same parameters, the body
`gBody` of it and the end of the block after. -/
def SwB (M M' : Map Blob) (I Z : Nat → Prop) (D : Nat → Pole → Bool) (E : Nat → List Pole)
    (x x' : Cfg σ Map) : Prop :=
  x'.lab = x.lab ∧ x'.params = x.params ∧ x'.t = x.t ∧ x'.st = x.st ∧ Reach M x.lab ∧ ¬ I x.lab ∧
  (∃ b0 b0', HoonMap.get M x.lab = some b0 ∧ HoonMap.get M' x.lab = some b0' ∧ x.b.fin = b0.fin ∧
    (x.b.par = b0.par ∨ x.b.par = []) ∧ (∃ pre, b0.body = pre ++ x.b.body) ∧
    x'.b = ⟨x.b.par, gBody D E x.lab x.b.body, b0'.fin⟩) ∧
  (∀ k, some k ∈ x.params → ¬ Z k) ∧ Agr (fun k => ¬ Z k) x.regs x'.regs

/-- **The two codes at the same place**: `SwB`, and the next op of the code
before, once nothing is left to pass, is kept. -/
def SwG (M M' : Map Blob) (I Z : Nat → Prop) (D : Nat → Pole → Bool) (E : Nat → List Pole)
    (x x' : Cfg σ Map) : Prop :=
  SwB M M' I Z D E x x' ∧ (x.params = [] → x.b.par = [] → ∀ p rest, x.b.body = p :: rest → D x.lab p = false)

/-- The reads of every configuration the code before reaches from `x` read
values. -/
def RdOK (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (x : Cfg σ Map) : Prop :=
  ∀ es z k, Steps lib O c gul x es z → ReadsAt gul z k → ∃ v, read k z.regs = some v

theorem RdOK.steps {x y : Cfg σ Map} {es : List (Nat × Nat)} (h : RdOK lib O c gul x)
    (hs : Steps lib O c gul x es y) : RdOK lib O c gul y :=
  fun _ z k hz hk => h _ z k (steps_trans hs hz) hk

theorem RdOK.here {x : Cfg σ Map} (h : RdOK lib O c gul x) : ∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v :=
  fun k hk => h [] x k (Steps.refl _) hk

/-- **The macro step at the end of a head's body**, which a region must
supply. -/
def HeadStepG (lib : Lib) (O : Oracle σ) (gul : Noun) (c c' : Straight Map) (I H Z : Nat → Prop)
    (D : Nat → Pole → Bool) (E : Nat → List Pole) : Prop :=
  ∀ x x' : Cfg σ Map, SwG c.blocks c'.blocks I Z D E x x' → H x.lab → x.params = [] → x.b.par = [] →
    x.b.body = [] → (∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v) →
    ∃ xT x'T es, Steps lib O c gul x es xT ∧ GoodTo lib O c' gul x' x'T ∧
      SwG c.blocks c'.blocks I Z D E xT x'T ∧ xT.lab ≠ x.lab ∧ x'T.lab ≠ x'.lab

/-- Either side may be behind. -/
def SwRG (lib : Lib) (O : Oracle σ) (gul : Noun) (c c' : Straight Map) (I Z : Nat → Prop)
    (D : Nat → Pole → Bool) (E : Nat → List Pole) (x x' : Cfg σ Map) : Prop :=
  ∃ xT x'T es, Steps lib O c gul x es xT ∧ GoodTo lib O c' gul x' x'T ∧ SwG c.blocks c'.blocks I Z D E xT x'T

variable (hR : RegionHypG c.blocks c'.blocks I H Z D E)
include hR

/-- The block after at a label outside the region. -/
theorem regionG_blk {k : Nat} {b : Blob} (hk : ¬ I k) (hb : HoonMap.get c.blocks k = some b) :
    ∃ b', HoonMap.get c'.blocks k = some b' ∧ b' = ⟨b.par, gBody D E k b.body, b'.fin⟩ := by
  by_cases hh : H k
  · obtain ⟨-, b1, b1', hb1, hb1', hp, hbd⟩ := hR.head k hh
    rw [hb] at hb1; cases hb1
    exact ⟨b1', hb1', by rw [← hp, ← hbd]⟩
  · obtain ⟨hD, hE⟩ := hR.off k hh
    exact ⟨b, by rw [hR.same k hk hh, hb], by rw [gBody_off hD hE]⟩

/-- The block before at a label outside the region. -/
theorem regionG_blk' {k : Nat} {b' : Blob} (hk : ¬ I k) (hb' : HoonMap.get c'.blocks k = some b') :
    ∃ b, HoonMap.get c.blocks k = some b ∧ b' = ⟨b.par, gBody D E k b.body, b'.fin⟩ := by
  by_cases hh : H k
  · obtain ⟨-, b1, b1', hb1, hb1', hp, hbd⟩ := hR.head k hh
    rw [hb'] at hb1'; cases hb1'
    exact ⟨b1, hb1, by rw [← hp, ← hbd]⟩
  · obtain ⟨hD, hE⟩ := hR.off k hh
    rw [hR.same k hk hh] at hb'
    exact ⟨b', hb', by rw [gBody_off hD hE]⟩

/-- Off the heads, the block after is the block before. -/
theorem swB_off {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') (hh : ¬ H x.lab) : x'.b = x.b := by
  obtain ⟨-, -, -, -, -, hI, ⟨b0, b0', hb0, hb0', hf, -, -, hb'⟩, -, -⟩ := hA
  obtain ⟨hD, hE⟩ := hR.off _ hh
  rw [hR.same _ hI hh, hb0] at hb0'
  cases hb0'
  rw [hb', gBody_off hD hE, ← hf]

/-- The registers the remaining block mentions, but for dropped ops and a
head's end, are off `Z`. -/
theorem swB_ment {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') :
    (∀ r ∈ x.b.par, ¬ Z r) ∧ (∀ p ∈ x.b.body, D x.lab p = false → ∀ r ∈ poleRegs p, ¬ Z r) ∧
      (¬ H x.lab → ∀ r ∈ finRegs x.b.fin, ¬ Z r) := by
  obtain ⟨-, -, -, -, hreach, hI, ⟨b0, b0', hb0, -, hf, hpar, ⟨pre, hpre⟩, -⟩, -, -⟩ := hA
  have hsub : ∀ p ∈ x.b.body, p ∈ b0.body := fun p hp => by rw [hpre]; exact List.mem_append_right _ hp
  have hpar' : ∀ r ∈ x.b.par, r ∈ b0.par := by
    rcases hpar with e | e <;> rw [e]
    · exact fun _ h => h
    · intro _ h; simp at h
  by_cases hh : H x.lab
  · obtain ⟨h1, h2⟩ := hR.mentH _ b0 hreach hh hb0
    exact ⟨fun r hr => h1 r (hpar' r hr), fun p hp hd r hr => h2 p (hsub p hp) hd r hr, fun h => absurd hh h⟩
  · have hm := hR.ment _ b0 hreach hI hh hb0
    refine ⟨fun r hr => hm r ?_, fun p hp _ r hr => hm r ?_, fun _ r hr => hm r ?_⟩
    · simp only [blobMentions, List.mem_append]; exact Or.inl (Or.inl (hpar' r hr))
    · simp only [blobMentions, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨p, hsub p hp, hr⟩
    · simp only [blobMentions, List.mem_append]; rw [← hf]; exact Or.inl (Or.inr hr)

/-- The relation at the start of a block reached by a jump from outside the
region and the heads. -/
theorem swB_jump {lab : Nat} {b0 b2 : Blob} {j : Jmp} {R R' : Map (Option Noun)} {t : Trace} {st : σ}
    (hreach : Reach c.blocks lab) (hI : ¬ I lab) (hh : ¬ H lab) (hb0 : HoonMap.get c.blocks lab = some b0)
    (hj : j ∈ getJmps b0.fin) (hI2 : ¬ I j.there) (hb2 : HoonMap.get c.blocks j.there = some b2)
    {b2' : Blob} (hb2' : HoonMap.get c'.blocks j.there = some b2')
    (he : b2' = ⟨b2.par, gBody D E j.there b2.body, b2'.fin⟩)
    (hag : Agr (fun k => ¬ Z k) R R') :
    SwB c.blocks c'.blocks I Z D E (⟨j.there, b2, j.args, R, t, st⟩ : Cfg σ Map) ⟨j.there, b2', j.args, R', t, st⟩ :=
  ⟨rfl, rfl, rfl, rfl, Reach.jump hreach hb0 hj, hI2,
    ⟨b2, b2', hb2, hb2', rfl, Or.inl rfl, ⟨[], rfl⟩, he⟩,
    fun k hk => hR.ment lab b0 hreach hI hh hb0 k (mentions_fin b0 k (jmp_finRegs hj hk)), hag⟩

/-- After a pass. -/
theorem swB_pass {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') {R R' : Map (Option Noun)}
    (hR1 : evalPassLoop x.params x.b.par x.regs = some R) (hR1' : evalPassLoop x.params x.b.par x'.regs = some R')
    (hpar : ∀ k ∈ x.b.par, HoonMap.get R k = HoonMap.get R' k) :
    SwB c.blocks c'.blocks I Z D E { x with b := { x.b with par := [] }, params := [], regs := R }
      { x' with b := { x'.b with par := [] }, params := [], regs := R' } := by
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, -, hpre, hb'⟩, hz, hag⟩ := hA
  refine ⟨hl, rfl, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, Or.inr rfl, hpre, by rw [hb']⟩,
    fun k hk => by simp at hk, fun k hk => ?_⟩
  by_cases hkp : k ∈ x.b.par
  · exact hpar k hkp
  · rw [Comp.evalPassLoop_frame _ _ _ _ hR1 k hkp, Comp.evalPassLoop_frame _ _ _ _ hR1' k hkp]
    exact hag k hk

/-- After a kept op on both sides. -/
theorem swB_op {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') {p : Pole} {rest : List Pole}
    (hb : x.b.body = p :: rest) (_hd : D x.lab p = false) {R R' : Map (Option Noun)} {t2 : Trace} {st2 : σ}
    (hag2 : Agr (fun k => ¬ Z k) R R') :
    SwB c.blocks c'.blocks I Z D E { x with b := { x.b with body := rest }, regs := R, t := t2, st := st2 }
      { x' with b := { x'.b with body := gBody D E x.lab rest }, regs := R', t := t2, st := st2 } := by
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hpar, ⟨pre, hpre⟩, hb'⟩, hz, hag⟩ := hA
  refine ⟨hl, hpe, rfl, rfl, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hpar, ⟨pre ++ [p], ?_⟩, by rw [hb']⟩, hz, hag2⟩
  rw [hpre, hb]; simp

/-- The body after of a remaining block. -/
theorem swB_body {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') :
    x'.b.body = gBody D E x.lab x.b.body ∧ x'.b.par = x.b.par := by
  obtain ⟨-, -, -, -, -, -, ⟨b0, b0', -, -, -, -, -, hb'⟩, -, -⟩ := hA
  rw [hb']; exact ⟨rfl, rfl⟩

/-- **The normalization**: the code before runs the dropped ops alone. -/
theorem swB_norm : ∀ (n : Nat) (x x' : Cfg σ Map), x.b.body.length = n → SwB c.blocks c'.blocks I Z D E x x' →
    ∃ es xT, Steps lib O c gul x es xT ∧ SwG c.blocks c'.blocks I Z D E xT x'
  | n, x, x', hn, hA => by
    by_cases hc : x.params = [] ∧ x.b.par = []
    · obtain ⟨hp, hq⟩ := hc
      cases hbd : x.b.body with
      | nil => exact ⟨[], x, Steps.refl _, hA, fun _ _ p rest h => by rw [hbd] at h; cases h⟩
      | cons p rest =>
        cases hd : D x.lab p with
        | false => exact ⟨[], x, Steps.refl _, hA, fun _ _ p' rest' h => by rw [hbd] at h; cases h; exact hd⟩
        | true =>
          obtain ⟨nn, r, rfl, hzr⟩ := hR.drop _ _ hd
          have s1 := Step.op (lib := lib) (O := O) (c := c) (gul := gul) (x := x) hp hq hbd
            (execPole_imm lib O gul x.st nn r x.regs x.t)
          obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hpar, ⟨pre, hpre⟩, hb'⟩, hz, hag⟩ := hA
          have hA2 : SwB c.blocks c'.blocks I Z D E
              { x with b := { x.b with body := rest }, regs := store r nn x.regs, t := x.t, st := x.st } x' := by
            refine ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, hpar, ⟨pre ++ [Pole.imm nn r], ?_⟩, ?_⟩,
              hz, fun k hk => ?_⟩
            · rw [hpre, hbd]; simp
            · rw [hb', hbd, gBody_drop hd]
            · have hkr : k ≠ r := fun e => hk (e ▸ hzr)
              rw [get_store_ne hkr]; exact hag k hk
          cases n with
          | zero => rw [hbd] at hn; cases hn
          | succ n =>
            obtain ⟨es, xT, hs, hG⟩ := swB_norm n _ x' (by simp only; rw [hbd] at hn; simpa using hn) hA2
            exact ⟨_, xT, Steps.step s1 hs, hG⟩
    · exact ⟨[], x, Steps.refl _, hA, fun hp hq => absurd ⟨hp, hq⟩ hc⟩

theorem swB_toG {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') :
    ∃ es xT, Steps lib O c gul x es xT ∧ SwG c.blocks c'.blocks I Z D E xT x' :=
  swB_norm hR _ x x' rfl hA

theorem swB_rg {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') :
    SwRG lib O gul c c' I Z D E x x' := by
  obtain ⟨es, xT, hs, hG⟩ := swB_toG (lib := lib) (O := O) (gul := gul) hR hA
  exact ⟨xT, x', es, hs, GoodTo.here _, hG⟩

/-- The pending arguments pass the same units. -/
theorem swB_argU {x x' : Cfg σ Map} (hA : SwB c.blocks c'.blocks I Z D E x x') :
    x.params.map (argU x.regs) = x.params.map (argU x'.regs) := by
  obtain ⟨-, -, -, -, -, -, -, hz, hag⟩ := hA
  exact List.map_congr_left (fun a ha => by
    cases a with
    | none => rfl
    | some k => exact hag k (hz k ha))

omit hR in
/-- The end does not matter where the next action is a pass or an op. -/
theorem endOf_fin_irrel (x : Cfg σ Map) (f : Termin) (h : x.b.body ≠ [] ∨ x.params ≠ [] ∨ x.b.par ≠ []) :
    endOf lib O gul { x with b := { x.b with fin := f } } = endOf lib O gul x := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at h
  rcases h with h | h | h
  · cases body with
    | nil => exact absurd rfl h
    | cons p rest => rfl
  · unfold endOf; simp [h]
  · unfold endOf; simp [h]

/-- **The same end**, but at the end of a head's body. -/
theorem swG_endOf {x x' : Cfg σ Map} (hA : SwG c.blocks c'.blocks I Z D E x x')
    (hh0 : ¬ (H x.lab ∧ x.params = [] ∧ x.b.par = [] ∧ x.b.body = [])) :
    endOf lib O gul x' = endOf lib O gul x := by
  obtain ⟨hB, hN⟩ := hA
  have hB0 := hB
  obtain ⟨hM1, hM2, hM3⟩ := swB_ment hR hB
  obtain ⟨hbody, hparx⟩ := swB_body hR hB
  obtain ⟨hl, hpe, ht, hst, -, -, -, -, hag⟩ := hB
  have hcons : x.params = [] → x.b.par = [] → ∀ p rest, x.b.body = p :: rest →
      x'.b.body = p :: gBody D E x.lab rest ∧ ∀ k ∈ poleRegs p, ¬ Z k := by
    intro hp hq p rest hxb
    have hd := hN hp hq p rest hxb
    exact ⟨by rw [hbody, hxb, gBody_keep hd], fun k hk => hM2 p (by rw [hxb]; exact List.mem_cons_self) hd k hk⟩
  by_cases hh : H x.lab
  · have hne : x'.b.body ≠ [] ∨ x'.params ≠ [] ∨ x'.b.par ≠ [] := by
      by_cases hc : x.params = [] ∧ x.b.par = []
      · obtain ⟨hp, hq⟩ := hc
        cases hxb : x.b.body with
        | nil => exact absurd ⟨hh, hp, hq, hxb⟩ hh0
        | cons p rest => exact Or.inl (by rw [(hcons hp hq p rest hxb).1]; exact List.cons_ne_nil _ _)
      · right; rw [hpe, hparx]
        by_cases hp : x.params = []
        · exact Or.inr (fun hq => hc ⟨hp, hq⟩)
        · exact Or.inl hp
    rw [← endOf_fin_irrel x' x.b.fin hne]
    refine endOf_agr hpe hparx rfl ht hst hag (fun hp hq => ?_)
    cases hxb : x.b.body with
    | nil => exact absurd ⟨hh, hp, hq, hxb⟩ hh0
    | cons p rest =>
      obtain ⟨h1, h2⟩ := hcons hp hq p rest hxb
      exact Or.inr ⟨p, rest, _, rfl, h1, h2⟩
  · have hfx : x'.b = x.b := swB_off hR hB0 hh
    refine endOf_agr hpe (by rw [hfx]) (by rw [hfx]) ht hst hag (fun hp hq => ?_)
    cases hxb : x.b.body with
    | nil => exact Or.inl ⟨rfl, by rw [hfx, hxb], fun k hk => hM3 hh k hk⟩
    | cons p rest =>
      have h2 := (hcons hp hq p rest hxb).2
      exact Or.inr ⟨p, rest, rest, rfl, by rw [hfx, hxb], h2⟩

/-- **The same reads**, but at the end of a head's body. -/
theorem swG_reads {x x' : Cfg σ Map} (hA : SwG c.blocks c'.blocks I Z D E x x')
    (hh0 : ¬ (H x.lab ∧ x.params = [] ∧ x.b.par = [] ∧ x.b.body = [])) {k : Nat} (hk : ReadsAt gul x' k) :
    ReadsAt gul x k ∧ read k x'.regs = read k x.regs := by
  obtain ⟨hB, hN⟩ := hA
  have hB0 := hB
  obtain ⟨hM1, hM2, hM3⟩ := swB_ment hR hB
  obtain ⟨hbody, hparx⟩ := swB_body hR hB
  obtain ⟨hl, hpe, ht, hst, -, -, -, -, hag⟩ := hB
  obtain ⟨hp, hq, hk⟩ := hk
  have hp0 : x.params = [] := by rw [← hpe]; exact hp
  have hq0 : x.b.par = [] := by rw [← hparx]; exact hq
  cases hxb : x.b.body with
  | nil =>
    have hh : ¬ H x.lab := fun hh => hh0 ⟨hh, hp0, hq0, hxb⟩
    have hfx : x'.b = x.b := swB_off hR hB0 hh
    rw [hfx, hxb] at hk
    rcases hk with ⟨p, rest, hb2, -⟩ | ⟨-, hk⟩
    · cases hb2
    · exact ⟨⟨hp0, hq0, Or.inr ⟨hxb, hk⟩⟩, hag.rd (hM3 hh k (finReads_sub hk))⟩
  | cons p rest =>
    have hd := hN hp0 hq0 p rest hxb
    have hb2 : x'.b.body = p :: gBody D E x.lab rest := by rw [hbody, hxb, gBody_keep hd]
    rw [hb2] at hk
    rcases hk with ⟨p', rest', hb3, hk⟩ | ⟨hb3, -⟩
    · simp only [List.cons.injEq] at hb3; obtain ⟨rfl, -⟩ := hb3
      exact ⟨⟨hp0, hq0, Or.inl ⟨p, rest, hxb, hk⟩⟩,
        hag.rd (hM2 p (by rw [hxb]; exact List.mem_cons_self) hd k (poleReads_sub hk))⟩
    · cases hb3

/-- **The same op**, but at the end of a head's body. -/
theorem swG_local {x x' : Cfg σ Map} (hA : SwG c.blocks c'.blocks I Z D E x x')
    (hh0 : ¬ (H x.lab ∧ x.params = [] ∧ x.b.par = [] ∧ x.b.body = [])) {p : Pole} {rest : List Pole}
    (hp : x'.params = []) (hq : x'.b.par = []) (hbd : x'.b.body = p :: rest) :
    x.params = [] ∧ x.b.par = [] ∧ ∃ rest0, x.b.body = p :: rest0 ∧
      ((execPole lib O gul x.st p x.regs x.t).isSome → (execPole lib O gul x'.st p x'.regs x'.t).isSome) := by
  obtain ⟨hB, hN⟩ := hA
  have hB0 := hB
  obtain ⟨hM1, hM2, hM3⟩ := swB_ment hR hB
  obtain ⟨hbody, hparx⟩ := swB_body hR hB
  obtain ⟨hl, hpe, ht, hst, -, -, -, -, hag⟩ := hB
  have hp0 : x.params = [] := by rw [← hpe]; exact hp
  have hq0 : x.b.par = [] := by rw [← hparx]; exact hq
  cases hxb : x.b.body with
  | nil =>
    have hh : ¬ H x.lab := fun hh => hh0 ⟨hh, hp0, hq0, hxb⟩
    rw [swB_off hR hB0 hh, hxb] at hbd; cases hbd
  | cons p0 rest0 =>
    have hd := hN hp0 hq0 p0 rest0 hxb
    rw [hbody, hxb, gBody_keep hd] at hbd
    simp only [List.cons.injEq] at hbd
    obtain ⟨rfl, -⟩ := hbd
    refine ⟨hp0, hq0, rest0, rfl, fun h => ?_⟩
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨ton, R1, t1, s1⟩ := r1
    obtain ⟨R1', hR1', -⟩ := (execPole_agr lib O gul x.st p0 x.t hag
      (fun k hk => hM2 p0 (by rw [hxb]; exact List.mem_cons_self) hd k hk)).fwd hr1
    rw [ht, hst, hR1']; rfl

variable (HS : HeadStepG lib O gul c c' I H Z D E)
include HS

/-- **Forward**: a step of the code before is matched. -/
theorem swG_fwd {x y x' : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c gul x e y)
    (hA : SwG c.blocks c'.blocks I Z D E x x') (hok : RdOK lib O c gul x) :
    ∃ es' y', Steps lib O c' gul x' es' y' ∧ SwRG lib O gul c c' I Z D E y y' := by
  obtain ⟨hB, hN⟩ := hA
  have hB0 := hB
  obtain ⟨hM1, hM2, hM3⟩ := swB_ment hR hB
  obtain ⟨hbody, hparx⟩ := swB_body hR hB
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, -, -, hb'⟩, hz, hag⟩ := hB
  cases hs with
  | @pass R hne hR1 =>
    obtain ⟨hck, hR1⟩ := evalPass_check hR1
    obtain ⟨R', hR1', hpar⟩ := OAg.fwd (passLoop_agr x.params x.params x.b.par x.regs x'.regs hck hck
      (swB_argU hR hB0)) hR1
    have hne' : x'.params ≠ [] ∨ x'.b.par ≠ [] := by rw [hpe, hparx]; exact hne
    refine ⟨_, _, Steps.step (Step.pass hne' (R := R') (by rw [hpe, hparx, evalPass_ok hck]; exact hR1'))
      (Steps.refl _), swB_rg hR (swB_pass hR hB0 hR1 hR1' hpar)⟩
  | @op p rest n R2 t2 st2 hp hq hbd hpole =>
    have hd := hN hp hq p rest hbd
    obtain ⟨R2', hR2', hag2⟩ := PAg.fwd (execPole_agr lib O gul x.st p x.t hag
      (fun k hk => hM2 p (by rw [hbd]; exact List.mem_cons_self) hd k hk)) hpole
    have hbd' : x'.b.body = p :: gBody D E x.lab rest := by rw [hbody, hbd, gBody_keep hd]
    refine ⟨_, _, Steps.step (Step.op (by rw [hpe]; exact hp) (by rw [hparx]; exact hq) hbd'
      (by rw [hst, ht]; exact hR2')) (Steps.refl _), swB_rg hR ?_⟩
    exact swB_op hR hB0 hbd hd hag2
  | @jump j b2 hp hq hbd htk hb2 =>
    by_cases hh : H x.lab
    · obtain ⟨xT, x'T, es, hT, hg, hAT, hlT, -⟩ := HS x x' ⟨hB0, hN⟩ hh hp hq hbd hok.here
      cases hT with
      | refl => exact absurd rfl hlT
      | step s1 rest1 =>
        have s0 : Step lib O c gul x [(x.lab, j.there)] ⟨j.there, b2, j.args, x.regs, x.t, x.st⟩ :=
          Step.jump hp hq hbd htk hb2
        obtain ⟨-, rfl⟩ := step_det s0 s1
        exact ⟨[], x', Steps.refl _, _, _, _, rest1, hg, hAT⟩
    · have hfx : x'.b = x.b := swB_off hR hB0 hh
      have htk' : taken x'.regs x'.b.fin = some j := by
        rw [hfx, taken_agr hag (fun k hk => hM3 hh k hk)]; exact htk
      rw [hf] at htk
      have hI2 := hR.noI x.lab b0 j hreach hI hh hb0 (taken_mem htk)
      obtain ⟨b2', hb2', he⟩ := regionG_blk hR hI2 hb2
      have s' : Step lib O c' gul x' [(x'.lab, j.there)] ⟨j.there, b2', j.args, x'.regs, x'.t, x'.st⟩ :=
        Step.jump (by rw [hpe]; exact hp) (by rw [hfx]; exact hq) (by rw [hfx]; exact hbd) htk' hb2'
      refine ⟨_, _, Steps.step s' (Steps.refl _), swB_rg hR ?_⟩
      rw [ht, hst]
      exact swB_jump hR hreach hI hh hb0 (taken_mem htk) hI2 hb2 hb2' he hag

/-- **Backward**: a step of the code after is matched. -/
theorem swG_bwd {x x' y' : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c' gul x' e y')
    (hA : SwG c.blocks c'.blocks I Z D E x x') (hok : RdOK lib O c gul x) :
    ∃ es y, Steps lib O c gul x es y ∧ SwRG lib O gul c c' I Z D E y y' := by
  by_cases hh0 : H x.lab ∧ x.params = [] ∧ x.b.par = [] ∧ x.b.body = []
  · obtain ⟨hh, hp, hq, hbd⟩ := hh0
    obtain ⟨xT, x'T, es, hT, hg, hAT, -, hlT⟩ := HS x x' hA hh hp hq hbd hok.here
    cases hg with
    | here => exact absurd rfl hlT
    | step _ s1 rest1 =>
      obtain ⟨-, rfl⟩ := step_det hs s1
      exact ⟨[], x, Steps.refl _, _, _, _, hT, rest1, hAT⟩
  obtain ⟨hB, hN⟩ := hA
  have hB0 := hB
  obtain ⟨hM1, hM2, hM3⟩ := swB_ment hR hB
  obtain ⟨hbody, hparx⟩ := swB_body hR hB
  obtain ⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, -, -, hb'⟩, hz, hag⟩ := hB
  cases hs with
  | @pass R' hne hR1' =>
    have hR2 : evalPass x.params x.b.par x'.regs = some R' := by rw [hpe, hparx] at hR1'; exact hR1'
    have hne0 : x.params ≠ [] ∨ x.b.par ≠ [] := by rw [hpe, hparx] at hne; exact hne
    obtain ⟨hck, hR1''⟩ := evalPass_check hR2
    obtain ⟨R, hR1, hpar⟩ := OAg.bwd (passLoop_agr x.params x.params x.b.par x.regs x'.regs hck hck
      (swB_argU hR hB0)) hR1''
    obtain ⟨es2, y, hs2, hG2⟩ := swB_toG (lib := lib) (O := O) (gul := gul) hR (swB_pass hR hB0 hR1 hR1'' hpar)
    exact ⟨_, _, Steps.step (Step.pass hne0 (R := R) (by rw [evalPass_ok hck]; exact hR1)) hs2,
      _, _, _, Steps.refl _, GoodTo.here _, hG2⟩
  | @op p' rest' n R2' t2 st2 hp hq hbd hpole =>
    have hp0 : x.params = [] := by rw [← hpe]; exact hp
    have hq0 : x.b.par = [] := by rw [← hparx]; exact hq
    cases hxb : x.b.body with
    | nil =>
      have hhx : H x.lab := by
        refine Classical.byContradiction fun hh => ?_
        rw [swB_off hR hB0 hh, hxb] at hbd; cases hbd
      exact absurd ⟨hhx, hp0, hq0, hxb⟩ hh0
    | cons p rest =>
      have hd := hN hp0 hq0 p rest hxb
      rw [hbody, hxb, gBody_keep hd] at hbd
      simp only [List.cons.injEq] at hbd
      obtain ⟨rfl, rfl⟩ := hbd
      rw [hst, ht] at hpole
      obtain ⟨R2, hR2, hag2⟩ := PAg.bwd (execPole_agr lib O gul x.st p x.t hag
        (fun k hk => hM2 p (by rw [hxb]; exact List.mem_cons_self) hd k hk)) hpole
      obtain ⟨es2, y, hs2, hG2⟩ := swB_toG (lib := lib) (O := O) (gul := gul) hR (swB_op hR hB0 hxb hd hag2
        (t2 := t2) (st2 := st2))
      refine ⟨_, _, Steps.step (Step.op hp0 hq0 hxb hR2) hs2, _, _, _, Steps.refl _, GoodTo.here _, ?_⟩
      have e1 : ({ x' with b := { x'.b with body := gBody D E x.lab rest }, regs := R2', t := t2, st := st2 } :
          Cfg σ Map) = ⟨x'.lab, { x'.b with body := gBody D E x.lab rest }, x'.params, R2', t2, st2⟩ := rfl
      rw [← e1]; exact hG2
  | @jump j b2' hp hq hbd htk' hb2' =>
    have hp0 : x.params = [] := by rw [← hpe]; exact hp
    have hq0 : x.b.par = [] := by rw [← hparx]; exact hq
    have hbd0 : x.b.body = [] := by
      cases hxb : x.b.body with
      | nil => rfl
      | cons p rest =>
        have hd := hN hp0 hq0 p rest hxb
        rw [hbody, hxb, gBody_keep hd] at hbd; cases hbd
    have hh : ¬ H x.lab := fun hh => hh0 ⟨hh, hp0, hq0, hbd0⟩
    have hfx : x'.b = x.b := swB_off hR hB0 hh
    rw [hfx] at htk'
    have htk : taken x.regs x.b.fin = some j := by
      rw [← taken_agr hag (fun k hk => hM3 hh k hk)]; exact htk'
    have htk0 := htk
    rw [hf] at htk0
    have hI2 := hR.noI x.lab b0 j hreach hI hh hb0 (taken_mem htk0)
    obtain ⟨b2, hb2, he⟩ := regionG_blk' hR hI2 hb2'
    refine ⟨_, _, Steps.step (Step.jump hp0 hq0 hbd0 htk hb2) (Steps.refl _), swB_rg hR ?_⟩
    rw [ht, hst]
    exact swB_jump hR hreach hI hh hb0 (taken_mem htk0) hI2 hb2 hb2' he hag

theorem swRG_fwd_step {x y x' : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c gul x e y)
    (hr : SwRG lib O gul c c' I Z D E x x') (hok : RdOK lib O c gul x) :
    ∃ es' y', Steps lib O c' gul x' es' y' ∧ SwRG lib O gul c c' I Z D E y y' := by
  obtain ⟨xT, x'T, es, hT, hg, hA⟩ := hr
  cases hT with
  | refl =>
    obtain ⟨es1, hs1⟩ := hg.steps
    obtain ⟨es2, y', hs2, hr2⟩ := swG_fwd hR HS hs hA hok
    exact ⟨_, y', steps_trans hs1 hs2, hr2⟩
  | step s1 rest1 =>
    obtain ⟨-, rfl⟩ := step_det hs s1
    exact ⟨[], x', Steps.refl _, _, _, _, rest1, hg, hA⟩

theorem swRG_bwd_step {x x' y' : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c' gul x' e y')
    (hr : SwRG lib O gul c c' I Z D E x x') (hok : RdOK lib O c gul x) :
    ∃ es y, Steps lib O c gul x es y ∧ SwRG lib O gul c c' I Z D E y y' := by
  obtain ⟨xT, x'T, es, hT, hg, hA⟩ := hr
  cases hg with
  | here =>
    obtain ⟨es2, y, hs2, hr2⟩ := swG_bwd hR HS hs hA (hok.steps hT)
    exact ⟨_, y, steps_trans hT hs2, hr2⟩
  | step _ s1 rest1 =>
    obtain ⟨-, rfl⟩ := step_det hs s1
    exact ⟨[], x, Steps.refl _, _, _, _, hT, rest1, hA⟩

/-- At the end of a head's body the code after steps, so it is good and has
no end. -/
theorem swG_atHead {x x' : Cfg σ Map} (hA : SwG c.blocks c'.blocks I Z D E x x') (hok : RdOK lib O c gul x)
    (hh0 : H x.lab ∧ x.params = [] ∧ x.b.par = [] ∧ x.b.body = []) :
    GoodAt lib O gul x' ∧ ∃ e y', Step lib O c' gul x' e y' := by
  obtain ⟨hh, hp, hq, hbd⟩ := hh0
  obtain ⟨_, x'T, _, -, hg2, -, -, hl2⟩ := HS x x' hA hh hp hq hbd hok.here
  cases hg2 with
  | here => exact absurd rfl hl2
  | step hgood s1 _ => exact ⟨hgood, _, _, s1⟩

theorem swRG_fwd {x z : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es z) {r : Tone × σ}
    (he : endOf lib O gul z = some r) : ∀ {x' : Cfg σ Map}, SwRG lib O gul c c' I Z D E x x' →
      RdOK lib O c gul x → ∃ es' z', Steps lib O c' gul x' es' z' ∧ endOf lib O gul z' = some r := by
  induction hs with
  | refl x0 =>
    intro x' hr hok
    obtain ⟨xT, x'T, es, hT, hg, hA⟩ := hr
    cases hT with
    | refl =>
      obtain ⟨es1, hs1⟩ := hg.steps
      by_cases hh0 : H x0.lab ∧ x0.params = [] ∧ x0.b.par = [] ∧ x0.b.body = []
      · obtain ⟨hh, hp, hq, hbd⟩ := hh0
        obtain ⟨xT2, _, _, hT2, -, -, hl2, -⟩ := HS x0 x'T hA hh hp hq hbd hok.here
        cases hT2 with
        | refl => exact absurd rfl hl2
        | step s1 _ => rw [step_endOf_none s1] at he; cases he
      · exact ⟨_, _, hs1, by rw [swG_endOf hR hA hh0]; exact he⟩
    | step s1 _ =>
      rw [step_endOf_none s1] at he; cases he
  | step s _ ih =>
    intro x' hr hok
    obtain ⟨es1, y', hs1, hr1⟩ := swRG_fwd_step hR HS s hr hok
    obtain ⟨es2, z', hs2, he'⟩ := ih he hr1 (hok.steps (Steps.step s (Steps.refl _)))
    exact ⟨_, z', steps_trans hs1 hs2, he'⟩

theorem swRG_bwd {x' z' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Steps lib O c' gul x' es' z') :
    ∀ {x : Cfg σ Map}, SwRG lib O gul c c' I Z D E x x' → RdOK lib O c gul x →
      ∃ es z, Steps lib O c gul x es z ∧ SwRG lib O gul c c' I Z D E z z' := by
  induction hs with
  | refl => intro x hr _; exact ⟨[], x, Steps.refl _, hr⟩
  | step s _ ih =>
    intro x hr hok
    obtain ⟨es1, y, hs1, hr1⟩ := swRG_bwd_step hR HS s hr hok
    obtain ⟨es2, z, hs2, hr2⟩ := ih hr1 (hok.steps hs1)
    exact ⟨_, z, steps_trans hs1 hs2, hr2⟩

end Sim

/-- **A region replaced keeps the code**, heads with a new body, given the
macro step at the end of their body. -/
theorem region_keepsG (c : Straight Map) (M' : Map Blob) {I H Z : Nat → Prop} {D : Nat → Pole → Bool}
    {E : Nat → List Pole} (hR : RegionHypG c.blocks M' I H Z D E)
    (HS : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun), HeadStepG lib O gul c (withBlocks c M') I H Z D E) :
    Keeps c (withBlocks c M') := by
  have hR' : RegionHypG c.blocks (withBlocks c M').blocks I H Z D E := hR
  refine ⟨rfl, rfl, ?_, fun lib σ O gul st vals t ⟨hok, hargs, hloc⟩ => ?_⟩
  · show (HoonMap.get M' 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par
    cases hb : HoonMap.get c.blocks 0 with
    | none =>
      cases hb' : HoonMap.get M' 0 with
      | none => rfl
      | some b' =>
        obtain ⟨b, hb2, -⟩ := regionG_blk' hR' hR.zero hb'
        rw [hb] at hb2; cases hb2
    | some b =>
      obtain ⟨b', hb', he⟩ := regionG_blk hR' hR.zero hb
      have h1 : HoonMap.get M' 0 = some b' := hb'
      have hp : b'.par = b.par := by rw [he]
      rw [h1]; simp [hp]
  have HS' := HS lib σ O gul
  have rd0 : ∀ b0, HoonMap.get c.blocks 0 = some b0 →
      RdOK lib O c gul (⟨0, b0, [], regsOf vals, t, st⟩ : Cfg σ Map) :=
    fun b0 hb0 es z k hz hk => hok es z k ⟨b0, hb0, hz⟩ hk
  have entry : ∀ b0 b0', HoonMap.get c.blocks 0 = some b0 → HoonMap.get M' 0 = some b0' →
      b0' = ⟨b0.par, gBody D E 0 b0.body, b0'.fin⟩ →
      SwRG lib O gul c (withBlocks c M') I Z D E (⟨0, b0, [], regsOf vals, t, st⟩ : Cfg σ Map)
        ⟨0, b0', [], regsOf vals, t, st⟩ := by
    intro b0 b0' hb0 hb0' he
    exact swB_rg hR' ⟨rfl, rfl, rfl, rfl, Reach.zero, hR.zero, ⟨b0, b0', hb0, hb0', rfl, Or.inl rfl, ⟨[], rfl⟩, he⟩,
      fun k hk => by simp at hk, fun _ _ => rfl⟩
  have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c M') (gul := gul) st vals t es' y' →
      ∃ b0 es y, HoonMap.get c.blocks 0 = some b0 ∧ Path.Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y ∧
        SwRG lib O gul c (withBlocks c M') I Z D E y y' := by
    rintro es' y' ⟨b0', hb0', hs'⟩
    obtain ⟨b0, hb0, he⟩ := regionG_blk' hR' hR.zero hb0'
    obtain ⟨es, y, hs, hr⟩ := swRG_bwd hR' HS' hs' (entry b0 b0' hb0 hb0' he) (rd0 b0 hb0)
    exact ⟨b0, es, y, hb0, hs, hr⟩
  refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, fun es' y' k hy' hk => ?_,
    fun es' y' k hy' hk => ?_, fun es' y' p rest hy' hp hq hb hsa => ?_⟩
  · obtain ⟨es', y', hy', he'⟩ := (Path.execEntry_iff_path (c := withBlocks c M') st vals t r).mp h'
    obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      have hok' : RdOK lib O c gul yT := (rd0 b0 hb0).steps (steps_trans hs hT)
      by_cases hh0 : H yT.lab ∧ yT.params = [] ∧ yT.b.par = [] ∧ yT.b.body = []
      · obtain ⟨-, e, y2, s1⟩ := swG_atHead hR' HS' hA hok' hh0
        rw [step_endOf_none s1] at he'; cases he'
      · exact (Path.execEntry_iff_path (c := c) st vals t r).mpr
          ⟨_, yT, ⟨b0, hb0, steps_trans hs hT⟩, by rw [← swG_endOf hR' hA hh0]; exact he'⟩
    | step _ s1 _ => rw [step_endOf_none s1] at he'; cases he'
  · obtain ⟨es, y, ⟨b0, hb0, hs⟩, he⟩ := (Path.execEntry_iff_path (c := c) st vals t r).mp h'
    obtain ⟨b0', hb0', he0⟩ := regionG_blk hR' hR.zero hb0
    obtain ⟨es', z', hs', he'⟩ := swRG_fwd hR' HS' hs he (entry b0 b0' hb0 hb0' he0) (rd0 b0 hb0)
    exact (Path.execEntry_iff_path (c := withBlocks c M') st vals t r).mpr ⟨es', z', ⟨_, hb0', hs'⟩, he'⟩
  · obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      have hok' : RdOK lib O c gul yT := (rd0 b0 hb0).steps (steps_trans hs hT)
      by_cases hh0 : H yT.lab ∧ yT.params = [] ∧ yT.b.par = [] ∧ yT.b.body = []
      · exact (swG_atHead hR' HS' hA hok' hh0).1.1 k hk
      · obtain ⟨hk', hrd⟩ := swG_reads hR' hA hh0 hk
        obtain ⟨v, hv⟩ := hok'.here k hk'
        exact ⟨v, by rw [hrd, hv]⟩
    | step hgood _ _ => exact hgood.1 k hk
  · obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      obtain ⟨⟨-, hpe, -, -, -, -, -, hz, hag⟩, -⟩ := hA
      have hk0 : some k ∈ yT.params := by rw [← hpe]; exact hk
      rw [← hag k (hz k hk0)]
      exact hargs _ yT k ⟨b0, hb0, steps_trans hs hT⟩ hk0
    | step hgood _ _ => exact hgood.2.1 k hk
  · obtain ⟨b0, es, y, hb0, hs, yT, y'T, es2, hT, hg, hA⟩ := back es' y' hy'
    cases hg with
    | here =>
      have hok' : RdOK lib O c gul yT := (rd0 b0 hb0).steps (steps_trans hs hT)
      by_cases hh0 : H yT.lab ∧ yT.params = [] ∧ yT.b.par = [] ∧ yT.b.body = []
      · exact (swG_atHead hR' HS' hA hok' hh0).1.2.2 p rest hp hq hb hsa
      · obtain ⟨hp0, hq0, rest0, hb0', himp⟩ := swG_local hR' hA hh0 hp hq hb
        exact himp (hloc _ yT p rest0 ⟨b0, hb0, steps_trans hs hT⟩ hp0 hq0 hb0' hsa)
    | step hgood _ _ => exact hgood.2.2 p rest hp hq hb hsa

end Opt
end SkaModel
end Formalization
