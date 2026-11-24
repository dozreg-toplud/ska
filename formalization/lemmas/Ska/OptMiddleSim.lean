import lemmas.Ska.OptMiddleWalk

/-!
# `+remove-empty-middle` keeps the code

A simulation on paths, on the template of `OptHopsSim.lean`, with one
relation (`MidI`): the same label, the same remaining parameters and body,
the end after the one `middleFin` makes of the end of the block before,
pending arguments that pass the same units (`argU`), and registers that agree
(`Agr`) off the bypassable parameters (`Byp`) and, once the pass of the block
is done, on every register the block mentions (`Live`).  A step of either
code is matched by at most one step of the other after the code before has
walked through the bypassed blocks (`jump_walk`, `hop_walk`), so there is no
normal form to reach first: `mid_fwd_step` and `mid_bwd_step` are symmetric,
and an end is the same end (`mid_endOf`).

What the pass needs, beyond the shape of its result (`mid_blocks`):

* `PassOK` of the input: the code before passes the check of `+eval-pass` at
  each bypassed block, a check the code after no longer makes.
* `PassOK` of the result: the substituted arguments pass the check at the
  new target.
* `ArgsOK` of the entry: every register a pass on a path from the entry
  moves is there.  Without it the pass is unsound: block `0` hops `[0v5]` to
  an empty block `1` with parameters `[0v7]`, which nothing mentions, and
  `1` hops `[]` to block `2`, which returns argument `0v0`.  The code before
  crashes at the pass into `1` (register `0v5` is not there), the code after
  hops from `0` straight to `2` and returns.  `ArgsOK` is kept by the pass
  (`middle_keeps_of`), but it is not part of `Keeps`, whose only hypothesis is
  `ReadsOK`, so the field `middle` of `DriverHyp` waits for `Keeps` to be
  widened.

`ReadsOK` is not needed: the registers the code after reads are equal to
those before, not only above them.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map} {fuel : Nat}

/-- The registers that must agree at `x`: those off the bypassable
parameters, and, once the pass is done, those the block mentions. -/
def Live (bl : Map Blob) (x : Cfg σ Map) (k : Nat) : Prop :=
  ¬ Byp bl k ∨ (x.params = [] ∧ x.b.par = [] ∧ k ∈ blobRegs x.b)

/-- **The relation**: the same position. -/
def MidI (fuel : Nat) (bl : Map Blob) (x x' : Cfg σ Map) : Prop :=
  x'.lab = x.lab ∧ x'.t = x.t ∧ x'.st = x.st ∧ x.params.map (argU x.regs) = x'.params.map (argU x'.regs) ∧
  (∀ k, some k ∈ x.params → k ∉ x.b.par) ∧ (∀ k, some k ∈ x'.params → k ∉ x.b.par) ∧
  Agr (Live bl x) x.regs x'.regs ∧
  ∃ b0 f', HoonMap.get bl x.lab = some b0 ∧ middleFin bl (readersOf bl) fuel b0.fin = some f' ∧
    (x.b = b0 ∨ (x.b.par = [] ∧ x.b.fin = b0.fin)) ∧ x'.b = { x.b with fin := f' }

theorem midI_start (HB : MidBlocks fuel c.blocks c'.blocks) {L : Nat} {b b' : Blob} {P P' : List (Option Nat)}
    {R R' : Map (Option Noun)} {t : Trace} {st : σ}
    (hb : HoonMap.get c.blocks L = some b) (hb' : HoonMap.get c'.blocks L = some b')
    (hm : P.map (argU R) = P'.map (argU R')) (hc : ∀ k, some k ∈ P → k ∉ b.par)
    (hc' : ∀ k, some k ∈ P' → k ∉ b'.par) (hag : Agr (fun k => ¬ Byp c.blocks k) R R') :
    MidI fuel c.blocks (⟨L, b, P, R, t, st⟩ : Cfg σ Map) ⟨L, b', P', R', t, st⟩ := by
  obtain ⟨f', hf', hb''⟩ := (HB L).2 b hb
  rw [hb''] at hb'; cases hb'
  refine ⟨rfl, rfl, rfl, hm, hc, hc', ?_, b, f', hb, hf', Or.inl rfl, rfl⟩
  intro k hk
  rcases hk with h | ⟨-, hp, hk⟩
  · exact hag k h
  · refine hag k (fun hy => ?_)
    have := byp_owner hy hb hk
    simp only at hp
    rw [hp] at this; simp at this

theorem midI_pass {lab : Nat} {b0 : Blob} {f' : Termin} {params params' : List (Option Nat)}
    {regs regs' R1 R1' : Map (Option Noun)} {t : Trace} {st : σ}
    (hb0 : HoonMap.get c.blocks lab = some b0) (hf' : middleFin c.blocks (readersOf c.blocks) fuel b0.fin = some f')
    (hR : evalPassLoop params b0.par regs = some R1) (hR' : evalPassLoop params' b0.par regs' = some R1')
    (hpar : ∀ k ∈ b0.par, HoonMap.get R1 k = HoonMap.get R1' k)
    (hag : Agr (Live c.blocks (⟨lab, b0, params, regs, t, st⟩ : Cfg σ Map)) regs regs') :
    MidI fuel c.blocks (⟨lab, { b0 with par := [] }, [], R1, t, st⟩ : Cfg σ Map)
      ⟨lab, { b0 with fin := f', par := [] }, [], R1', t, st⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, by simp, by simp, ?_, b0, f', hb0, hf', Or.inr ⟨rfl, rfl⟩, rfl⟩
  intro k hk
  by_cases hkp : k ∈ b0.par
  · exact hpar k hkp
  · rw [Comp.evalPassLoop_frame _ _ _ _ hR k hkp, Comp.evalPassLoop_frame _ _ _ _ hR' k hkp]
    apply hag k
    rcases hk with h | ⟨-, -, h⟩
    · exact Or.inl h
    · by_cases hy : Byp c.blocks k
      · exact absurd (byp_owner hy hb0 h) hkp
      · exact Or.inl hy

theorem midI_op {lab : Nat} {b b0 : Blob} {f' : Termin} {p : Pole} {rest : List Pole}
    {R2 R2' regs : Map (Option Noun)} {t t2 : Trace} {st st2 : σ}
    (hb0 : HoonMap.get c.blocks lab = some b0) (hf' : middleFin c.blocks (readersOf c.blocks) fuel b0.fin = some f')
    (hbb : b = b0 ∨ (b.par = [] ∧ b.fin = b0.fin)) (hq : b.par = []) (hbd : b.body = p :: rest)
    (hag : Agr (Live c.blocks (⟨lab, b, [], regs, t, st⟩ : Cfg σ Map)) R2 R2') :
    MidI fuel c.blocks (⟨lab, { b with body := rest }, [], R2, t2, st2⟩ : Cfg σ Map)
      ⟨lab, { b with fin := f', body := rest }, [], R2', t2, st2⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, by simp, by simp, ?_, b0, f', hb0, hf', Or.inr ⟨hq, ?_⟩, rfl⟩
  · intro k hk
    apply hag k
    rcases hk with h | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hq, tail_blobRegs hbd h⟩
  · rcases hbb with h | ⟨-, h⟩
    · subst h; rfl
    · exact h

/-- **A jump**: the code before walks to where the code after jumps. -/
theorem mid_jump (HB : MidBlocks fuel c.blocks c'.blocks) (hpc : PassOK c.blocks) (hpc' : PassOK c'.blocks)
    {lab : Nat} {b0 b2 : Blob} {f' : Termin} {j j' : Jmp} {regs regs' : Map (Option Noun)} {t : Trace} {st : σ}
    (hb0 : HoonMap.get c.blocks lab = some b0) (hf' : middleFin c.blocks (readersOf c.blocks) fuel b0.fin = some f')
    (hj : j ∈ getJmps b0.fin) (hj' : j' ∈ getJmps f') (hJ : JRel c.blocks fuel b0.fin j j')
    (hb2 : HoonMap.get c.blocks j.there = some b2) (hjm : j.args.map (argU regs) = j.args.map (argU regs'))
    (hagB : Agr (fun k => ¬ Byp c.blocks k) regs regs')
    (hargs : ∀ es z k, Steps lib O c gul ⟨j.there, b2, j.args, regs, t, st⟩ es z → some k ∈ z.params →
      (HoonMap.get z.regs k).isSome) :
    ∃ bb', HoonMap.get c'.blocks j'.there = some bb' ∧ ∃ es2 z,
      Steps lib O c gul ⟨j.there, b2, j.args, regs, t, st⟩ es2 z ∧
      MidI fuel c.blocks z ⟨j'.there, bb', j'.args, regs', t, st⟩ := by
  have hlab' : HoonMap.get c'.blocks lab = some { b0 with fin := f' } := by
    obtain ⟨f'', hf'', e⟩ := (HB lab).2 b0 hb0
    rw [hf'] at hf''; cases hf''; exact e
  have hck' : ∀ bb, HoonMap.get c'.blocks j'.there = some bb → ∀ k, some k ∈ j'.args → k ∉ bb.par :=
    fun bb hbb k hk => hpc' lab _ j' bb hlab' hj' hbb k hk
  have hck : ∀ k, some k ∈ j.args → k ∉ b2.par := fun k hk => hpc lab b0 j b2 hb0 hj hb2 k hk
  have back : ∀ {b3 : Blob}, HoonMap.get c.blocks j'.there = some b3 →
      ∃ bb', HoonMap.get c'.blocks j'.there = some bb' ∧ bb'.par = b3.par := fun {b3} hb3 => by
    obtain ⟨f3, -, e⟩ := (HB j'.there).2 b3 hb3
    exact ⟨_, e, rfl⟩
  rcases hJ with rfl | hJ | ⟨-, hJ⟩
  · obtain ⟨bb', hbb', -⟩ := back hb2
    exact ⟨bb', hbb', [], _, Steps.refl _, midI_start HB hb2 hbb' hjm hck (hck' _ hbb') hagB⟩
  · obtain ⟨b3, hb3, ha3, hw⟩ := jump_walk (lib := lib) (O := O) (gul := gul) fuel j j' hJ b2 hb2
    obtain ⟨bb', hbb', hpar⟩ := back hb3
    obtain ⟨es2, hs2⟩ := hw regs t st
    refine ⟨bb', hbb', es2, _, hs2, midI_start HB hb3 hbb' (by rw [ha3]; exact hjm) (fun k hk => ?_)
      (hck' _ hbb') hagB⟩
    rw [← hpar]; exact hck' _ hbb' k hk
  · obtain ⟨es2, J2, b3, R3, hs2, hb3, hm3, hc3, hag3⟩ :=
      hop_walk hpc fuel j j' hJ j.args b2 regs regs' t st hb2 hjm hck hagB hargs
    obtain ⟨bb', hbb', -⟩ := back hb3
    exact ⟨bb', hbb', es2, _, hs2, midI_start HB hb3 hbb' hm3 hc3 (hck' _ hbb') hag3⟩

theorem nil_of_map {A A' : List (Option Nat)} {R R' : Map (Option Noun)} (hm : A.map (argU R) = A'.map (argU R')) :
    A = [] ↔ A' = [] := by
  constructor <;> intro e <;> subst e
  · cases A' with
    | nil => rfl
    | cons => simp at hm
  · cases A with
    | nil => rfl
    | cons => simp at hm

/-- **Forward**: a step of the code before is matched by at most one step
after, the code before then walking to the related position. -/
theorem mid_fwd_step (HB : MidBlocks fuel c.blocks c'.blocks) (hpc : PassOK c.blocks) (hpc' : PassOK c'.blocks)
    {x y x' : Cfg σ Map} {es : List (Nat × Nat)} (hs : Step lib O c gul x es y) (hr : MidI fuel c.blocks x x')
    (hargs : ∀ es z k, Steps lib O c gul y es z → some k ∈ z.params → (HoonMap.get z.regs k).isSome) :
    ∃ es' y', Steps lib O c' gul x' es' y' ∧ ∃ es2 z, Steps lib O c gul y es2 z ∧ MidI fuel c.blocks z y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨hl, ht, hst, hm, hc, hc', hag, b0, f', hb0, hf', hbb, hb'⟩ := hr
  simp only at hl ht hst hm hc hc' hag hb0 hbb hb'
  subst lab' t' st' b'
  cases hs with
  | pass hne hR =>
    simp only at hne hR
    have hck : ∀ a ∈ params, ∀ k, a = some k → k ∉ b.par := fun a ha k e => hc k (e ▸ ha)
    have hck' : ∀ a ∈ params', ∀ k, a = some k → k ∉ b.par := fun a ha k e => hc' k (e ▸ ha)
    rw [evalPass_ok hck] at hR
    have hbe : b = b0 := by
      rcases hbb with h | ⟨hp, -⟩
      · exact h
      · exfalso
        rw [hp] at hR hne
        cases params with
        | nil => simp at hne
        | cons a as => simp [evalPassLoop] at hR
    subst hbe
    obtain ⟨R1', hR1', hpar⟩ := OAg.fwd (passLoop_agr params params' b.par regs regs' hck hck' hm) hR
    have hne' : params' ≠ [] ∨ b.par ≠ [] := by
      rcases hne with h | h
      · exact Or.inl (fun e => h ((nil_of_map hm).mpr e))
      · exact Or.inr h
    exact ⟨_, _, Steps.step (Step.pass (x := ⟨lab, { b with fin := f' }, params', regs', t, st⟩) hne'
      (by rw [evalPass_ok hck']; exact hR1')) (Steps.refl _), [], _, Steps.refl _,
      midI_pass hb0 hf' hR hR1' hpar hag⟩
  | @op p rest n R2 t2 st2 hp hq hbd hpole =>
    simp only at hp hq hbd hpole
    subst hp
    have hp' : params' = [] := (nil_of_map hm).mp rfl
    subst hp'
    have hS : ∀ k ∈ poleRegs p, Live c.blocks (⟨lab, b, [], regs, t, st⟩ : Cfg σ Map) k :=
      fun k hk => Or.inr ⟨rfl, hq, op_blobRegs hbd hk⟩
    obtain ⟨R2', hR2', hag2⟩ := PAg.fwd (execPole_agr lib O gul st p t hag hS) hpole
    exact ⟨_, _, Steps.step (Step.op (x := ⟨lab, { b with fin := f' }, [], regs', t, st⟩) (rest := rest) rfl hq hbd
      hR2') (Steps.refl _), [], _, Steps.refl _, midI_op hb0 hf' hbb hq hbd hag2⟩
  | @jump j b2 hp hq hbd htk hb2 =>
    simp only at hp hq hbd htk hb2
    subst hp
    have hp' : params' = [] := (nil_of_map hm).mp rfl
    subst hp'
    have hfin : b.fin = b0.fin := by
      rcases hbb with h | ⟨-, h⟩
      · rw [h]
      · exact h
    have hS : ∀ k ∈ finRegs b0.fin, Live c.blocks (⟨lab, b, [], regs, t, st⟩ : Cfg σ Map) k :=
      fun k hk => Or.inr ⟨rfl, hq, fin_blobRegs (by rw [hfin]; exact hk)⟩
    have hR : ∀ k ∈ finRegs b0.fin, read k regs' = read k regs := fun k hk => hag.rd (hS k hk)
    rw [hfin] at htk
    obtain ⟨j', htk', hJ⟩ := (taken_mid hf' hR).1 j htk
    have hjm : j.args.map (argU regs) = j.args.map (argU regs') := List.map_congr_left (fun a ha => by
      cases a with
      | none => rfl
      | some k => exact hag k (hS k (jmp_finRegs (taken_mem htk) ha)))
    obtain ⟨bb', hbb', es2, z, hs2, hz⟩ := mid_jump HB hpc hpc' hb0 hf' (taken_mem htk) (taken_mem htk') hJ hb2
      hjm (fun k hk => hag k (Or.inl hk)) hargs
    exact ⟨_, _, Steps.step (Step.jump (x := ⟨lab, { b with fin := f' }, [], regs', t, st⟩) rfl hq hbd htk' hbb')
      (Steps.refl _), es2, z, hs2, hz⟩

/-- **Backward**: a step of the code after is matched by steps before. -/
theorem mid_bwd_step (HB : MidBlocks fuel c.blocks c'.blocks) (hpc : PassOK c.blocks) (hpc' : PassOK c'.blocks)
    {x x' y' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Step lib O c' gul x' es' y') (hr : MidI fuel c.blocks x x')
    (hargs : ∀ es z k, Steps lib O c gul x es z → some k ∈ z.params → (HoonMap.get z.regs k).isSome) :
    ∃ es z, Steps lib O c gul x es z ∧ MidI fuel c.blocks z y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨hl, ht, hst, hm, hc, hc', hag, b0, f', hb0, hf', hbb, hb'⟩ := hr
  simp only at hl ht hst hm hc hc' hag hb0 hbb hb'
  subst lab' t' st' b'
  cases hs with
  | @pass R1' hne hR' =>
    simp only at hne hR'
    have hck : ∀ a ∈ params, ∀ k, a = some k → k ∉ b.par := fun a ha k e => hc k (e ▸ ha)
    have hck' : ∀ a ∈ params', ∀ k, a = some k → k ∉ b.par := fun a ha k e => hc' k (e ▸ ha)
    rw [evalPass_ok hck'] at hR'
    have hbe : b = b0 := by
      rcases hbb with h | ⟨hp, -⟩
      · exact h
      · exfalso
        rw [hp] at hR' hne
        cases params' with
        | nil => simp at hne
        | cons a as => simp [evalPassLoop] at hR'
    subst hbe
    obtain ⟨R1, hR1, hpar⟩ := OAg.bwd (passLoop_agr params params' b.par regs regs' hck hck' hm) hR'
    have hne0 : params ≠ [] ∨ b.par ≠ [] := by
      rcases hne with h | h
      · exact Or.inl (fun e => h ((nil_of_map hm).mp e))
      · exact Or.inr h
    exact ⟨_, _, Steps.step (Step.pass (x := ⟨lab, b, params, regs, t, st⟩) hne0
      (by rw [evalPass_ok hck]; exact hR1)) (Steps.refl _), midI_pass hb0 hf' hR1 hR' hpar hag⟩
  | @op p rest n R2' t2 st2 hp hq hbd hpole =>
    simp only at hp hq hbd hpole
    subst hp
    have hp0 : params = [] := (nil_of_map hm).mpr rfl
    subst hp0
    have hS : ∀ k ∈ poleRegs p, Live c.blocks (⟨lab, b, [], regs, t, st⟩ : Cfg σ Map) k :=
      fun k hk => Or.inr ⟨rfl, hq, op_blobRegs hbd hk⟩
    obtain ⟨R2, hR2, hag2⟩ := PAg.bwd (execPole_agr lib O gul st p t hag hS) hpole
    exact ⟨_, _, Steps.step (Step.op (x := ⟨lab, b, [], regs, t, st⟩) (rest := rest) rfl hq hbd hR2) (Steps.refl _),
      midI_op hb0 hf' hbb hq hbd hag2⟩
  | @jump j' bb' hp hq hbd htk' hbb' =>
    simp only at hp hq hbd htk' hbb'
    subst hp
    have hp0 : params = [] := (nil_of_map hm).mpr rfl
    subst hp0
    have hfin : b.fin = b0.fin := by
      rcases hbb with h | ⟨-, h⟩
      · rw [h]
      · exact h
    have hS : ∀ k ∈ finRegs b0.fin, Live c.blocks (⟨lab, b, [], regs, t, st⟩ : Cfg σ Map) k :=
      fun k hk => Or.inr ⟨rfl, hq, fin_blobRegs (by rw [hfin]; exact hk)⟩
    have hR : ∀ k ∈ finRegs b0.fin, read k regs' = read k regs := fun k hk => hag.rd (hS k hk)
    obtain ⟨j, htk, hJ⟩ := (taken_mid hf' hR).2 j' htk'
    have hb2 : ∃ b2, HoonMap.get c.blocks j.there = some b2 := by
      rcases hJ with rfl | hJ | ⟨-, hJ⟩
      · obtain ⟨b2, -, hb2, -, -⟩ := HB.back hbb'
        exact ⟨b2, hb2⟩
      · by_cases ha : j.args = []
        · exact rewriteJump_start hJ ha
        · have := rewriteJump_args hJ ha
          subst this
          obtain ⟨b2, -, hb2, -, -⟩ := HB.back hbb'
          exact ⟨b2, hb2⟩
      · exact rewriteHop_start hJ
    obtain ⟨b2, hb2⟩ := hb2
    have hjm : j.args.map (argU regs) = j.args.map (argU regs') := List.map_congr_left (fun a ha => by
      cases a with
      | none => rfl
      | some k => exact hag k (hS k (jmp_finRegs (taken_mem htk) ha)))
    have hstep : Step lib O c gul ⟨lab, b, [], regs, t, st⟩ [(lab, j.there)] ⟨j.there, b2, j.args, regs, t, st⟩ :=
      Step.jump rfl hq hbd (by rw [hfin]; exact htk) hb2
    obtain ⟨bb'', hbb'', es2, z, hs2, hz⟩ := mid_jump HB hpc hpc' hb0 hf' (taken_mem htk) (taken_mem htk') hJ hb2
      hjm (fun k hk => hag k (Or.inl hk)) (fun es z k hz hk => hargs _ z k (Steps.step hstep hz) hk)
    rw [hbb'] at hbb''; cases hbb''
    exact ⟨_, z, Steps.step hstep hs2, hz⟩

/-- **An end is the same end.** -/
theorem mid_endOf {x x' : Cfg σ Map} (hr : MidI fuel c.blocks x x') : endOf lib O gul x' = endOf lib O gul x := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨hl, ht, hst, hm, -, -, hag, b0, f', hb0, hf', hbb, hb'⟩ := hr
  simp only at hl ht hst hm hag hb0 hbb hb'
  subst lab' t' st' b'
  have hpe := nil_of_map hm
  unfold endOf
  simp only
  by_cases hne : params ≠ [] ∨ par ≠ []
  · have hne' : params' ≠ [] ∨ par ≠ [] := by
      rcases hne with h | h
      · exact Or.inl (fun e => h (hpe.mpr e))
      · exact Or.inr h
    rw [if_pos hne, if_pos hne']
  · have hne' : ¬ (params' ≠ [] ∨ par ≠ []) := by
      intro h; apply hne
      rcases h with h | h
      · exact Or.inl (fun e => h (hpe.mp e))
      · exact Or.inr h
    rw [if_neg hne, if_neg hne']
    simp only [not_or, ne_eq, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    have hfin : fin = b0.fin := by
      rcases hbb with h | ⟨-, h⟩
      · subst h; rfl
      · exact h
    cases body with
    | cons p rest =>
      have hS : ∀ k ∈ poleRegs p, Live c.blocks
          (⟨lab, ⟨[], p :: rest, fin⟩, [], regs, t, st⟩ : Cfg σ Map) k :=
        fun k hk => Or.inr ⟨rfl, rfl, op_blobRegs rfl hk⟩
      have hp' := execPole_agr lib O gul st p t hag hS
      simp only
      revert hp'
      cases execPole lib O gul st p regs t <;> cases execPole lib O gul st p regs' t
      · simp
      · simp [PAg]
      · simp [PAg]
      · rename_i a b
        obtain ⟨ta, Ra, tra, sa⟩ := a
        obtain ⟨tb, Rb, trb, sb⟩ := b
        simp only [PAg]
        rintro ⟨rfl, rfl, rfl, -⟩
        cases ta <;> rfl
    | nil =>
      have hL : ∀ k ∈ finRegs fin, Live c.blocks (⟨lab, ⟨[], [], fin⟩, [], regs, t, st⟩ : Cfg σ Map) k :=
        fun k hk => Or.inr ⟨rfl, rfl, fin_blobRegs hk⟩
      rw [← hfin] at hf'
      simp only
      cases fin with
      | brn s z o =>
        simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf'
        obtain ⟨z', -, o', -, rfl⟩ := hf'
        simp only [hag.rd (hL s (by simp [finRegs]))]
      | clq s z o =>
        simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf'
        obtain ⟨z', -, o', -, rfl⟩ := hf'; rfl
      | eqq l r z o =>
        simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf'
        obtain ⟨z', -, o', -, rfl⟩ := hf'; rfl
      | brz s z o =>
        simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf'
        obtain ⟨z', -, o', -, rfl⟩ := hf'; rfl
      | hop t0 =>
        simp only [middleFin, Option.map_eq_some_iff] at hf'
        obtain ⟨t', -, rfl⟩ := hf'; rfl
      | lti n s z o => simp only [middleFin, Option.some.injEq] at hf'; subst hf'; rfl
      | jmp a v =>
        simp only [middleFin, Option.some.injEq] at hf'; subst hf'
        simp only [hag.mapM v (fun k hk => hL k (by simpa [finRegs] using hk))]
      | jmf a v n =>
        simp only [middleFin, Option.some.injEq] at hf'; subst hf'
        simp only [hag.mapM v (fun k hk => hL k (by simpa [finRegs] using hk))]
      | jsp a s =>
        simp only [middleFin, Option.some.injEq] at hf'; subst hf'
        simp only [hag.rd (hL s (by simp [finRegs]))]
      | jsf a s n =>
        simp only [middleFin, Option.some.injEq] at hf'; subst hf'
        simp only [hag.rd (hL s (by simp [finRegs]))]
      | don s =>
        simp only [middleFin, Option.some.injEq] at hf'; subst hf'
        simp only [hag.rd (hL s (by simp [finRegs]))]
      | bom o => simp only [middleFin, Option.some.injEq] at hf'; subst hf'; rfl

/-- A real read after is a real read before, of the same value. -/
theorem mid_reads {x x' : Cfg σ Map} {k : Nat} (hr : MidI fuel c.blocks x x') (hk : ReadsAt gul x' k) :
    ReadsAt gul x k ∧ read k x'.regs = read k x.regs := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  obtain ⟨hl, ht, hst, hm, -, -, hag, b0, f', hb0, hf', hbb, hb'⟩ := hr
  simp only at hl ht hst hm hag hb0 hbb hb'
  subst lab' t' st' b'
  obtain ⟨hp, hq, hk⟩ := hk
  simp only at hp hq hk ⊢
  subst hp hq
  have hp0 : params = [] := (nil_of_map hm).mpr rfl
  subst hp0
  have hfin : fin = b0.fin := by
    rcases hbb with h | ⟨-, h⟩
    · subst h; rfl
    · exact h
  rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, hk⟩
  · subst hb
    exact ⟨⟨rfl, rfl, Or.inl ⟨p, rest, rfl, hk⟩⟩, hag.rd (Or.inr ⟨rfl, rfl, op_blobRegs rfl (poleReads_sub hk)⟩)⟩
  · subst hb
    rw [← hfin] at hf'
    rw [finReads_mid hf'] at hk
    exact ⟨⟨rfl, rfl, Or.inr ⟨rfl, hk⟩⟩, hag.rd (Or.inr ⟨rfl, rfl, fin_blobRegs (finReads_sub hk)⟩)⟩

theorem step_endOf_none {x y : Cfg σ Map} {e : List (Nat × Nat)} (h : Step lib O c gul x e y) :
    endOf lib O gul x = none := by
  cases h with
  | pass hne => simp [endOf, hne]
  | op hp hq hb hpole => simp [endOf, hp, hq, hb, hpole]
  | jump hp hq hb ht => exact endOf_taken (lib := lib) (O := O) (gul := gul) hp hq hb (by rw [ht]; rfl)

/-- **Forward, on paths.** -/
theorem mid_fwd (HB : MidBlocks fuel c.blocks c'.blocks) (hpc : PassOK c.blocks) (hpc' : PassOK c'.blocks)
    {x z : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es z) {r : Tone × σ}
    (he : endOf lib O gul z = some r) :
    ∀ {x' y : Cfg σ Map} {es1 : List (Nat × Nat)},
      (∀ es z k, Steps lib O c gul x es z → some k ∈ z.params → (HoonMap.get z.regs k).isSome) →
      Steps lib O c gul x es1 y → MidI fuel c.blocks y x' →
      ∃ es' z', Steps lib O c' gul x' es' z' ∧ endOf lib O gul z' = some r := by
  induction hs with
  | refl x =>
    intro x' y es1 _ hy hr
    cases hy with
    | refl => exact ⟨[], x', Steps.refl _, by rw [mid_endOf hr]; exact he⟩
    | step s _ => rw [step_endOf_none s] at he; cases he
  | @step x x1 z e es s rest ih =>
    intro x' y es1 hargs hy hr
    have hargs1 : ∀ es z k, Steps lib O c gul x1 es z → some k ∈ z.params → (HoonMap.get z.regs k).isSome :=
      fun es z k hz hk => hargs _ z k (Steps.step s hz) hk
    cases hy with
    | refl =>
      obtain ⟨es', y', hs', es2, z2, hz2, hr2⟩ := mid_fwd_step HB hpc hpc' s hr hargs1
      obtain ⟨es'', z', hs'', he'⟩ := ih he hargs1 hz2 hr2
      exact ⟨_, z', steps_trans hs' hs'', he'⟩
    | step s' rest' =>
      obtain ⟨-, rfl⟩ := step_det s s'
      exact ih he hargs1 rest' hr

/-- **Backward, on paths.** -/
theorem mid_bwd (HB : MidBlocks fuel c.blocks c'.blocks) (hpc : PassOK c.blocks) (hpc' : PassOK c'.blocks)
    {x' z' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Steps lib O c' gul x' es' z') :
    ∀ {x : Cfg σ Map}, (∀ es z k, Steps lib O c gul x es z → some k ∈ z.params → (HoonMap.get z.regs k).isSome) →
      MidI fuel c.blocks x x' → ∃ es z, Steps lib O c gul x es z ∧ MidI fuel c.blocks z z' := by
  induction hs with
  | refl => intro x _ hr; exact ⟨[], x, Steps.refl _, hr⟩
  | step s _ ih =>
    intro x hargs hr
    obtain ⟨es1, y, hy, hr1⟩ := mid_bwd_step HB hpc hpc' s hr hargs
    obtain ⟨es2, z, hz, hr2⟩ := ih (fun es z k hz hk => hargs _ z k (steps_trans hy hz) hk) hr1
    exact ⟨_, z, steps_trans hy hz, hr2⟩

end Sim

/-- **`+remove-empty-middle` keeps the code** on the entries where the moves
of the passes find their registers (`ArgsOK`), given the check of
`+eval-pass` before (`PassOK` of the input) and after (`PassOK` of the
result); it keeps `ReadsOK` and `ArgsOK`. -/
theorem middle_keeps_of {fuel : Nat} (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeEmptyMiddle fuel c.blocks = some (ch, bl')) (hpc : PassOK c.blocks) (hpc' : PassOK bl') :
    (HoonMap.get bl' 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par ∧
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (vals : List Noun) (t : Trace),
      ArgsOK lib O c gul st vals t →
        execEntry lib O st (withBlocks c bl') vals t gul = execEntry lib O st c vals t gul ∧
        (ReadsOK lib O c gul st vals t → ReadsOK lib O (withBlocks c bl') gul st vals t) ∧
        ArgsOK lib O (withBlocks c bl') gul st vals t := by
  have HB : MidBlocks fuel c.blocks (withBlocks c bl').blocks := mid_blocks h
  refine ⟨?_, fun lib σ O gul st vals t hargs => ?_⟩
  · cases e : HoonMap.get c.blocks 0 with
    | none =>
      have e' : HoonMap.get (withBlocks c bl').blocks 0 = none := (HB 0).1 e
      exact (show (HoonMap.get (withBlocks c bl').blocks 0).map Blob.par = none by rw [e']; rfl)
    | some b0 =>
      obtain ⟨f', -, e'⟩ := (HB 0).2 b0 e
      exact (show (HoonMap.get (withBlocks c bl').blocks 0).map Blob.par = some b0.par by rw [e']; rfl)
  cases e : HoonMap.get c.blocks 0 with
  | none =>
    have e' : HoonMap.get (withBlocks c bl').blocks 0 = none := (HB 0).1 e
    refine ⟨?_, fun _ es y k hy _ => ?_, fun es y k hy _ => ?_⟩
    · unfold execEntry; rw [e, e']; rfl
    · obtain ⟨b, hb, -⟩ := hy; rw [e'] at hb; cases hb
    · obtain ⟨b, hb, -⟩ := hy; rw [e'] at hb; cases hb
  | some b0 =>
    obtain ⟨f', hf', e'⟩ := (HB 0).2 b0 e
    let x0 : Path.Cfg σ Map := ⟨0, b0, [], regsOf vals, t, st⟩
    let x0' : Path.Cfg σ Map := ⟨0, { b0 with fin := f' }, [], regsOf vals, t, st⟩
    have hr0 : MidI fuel c.blocks x0 x0' :=
      ⟨rfl, rfl, rfl, rfl, by simp [x0], by simp [x0'], fun k _ => rfl, b0, f', e, hf', Or.inl rfl, rfl⟩
    have hargs0 : ∀ es z k, Path.Steps lib O c gul x0 es z → some k ∈ z.params → (HoonMap.get z.regs k).isSome :=
      fun es z k hz hk => hargs es z k ⟨b0, e, hz⟩ hk
    have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c bl') (gul := gul) st vals t es' y' →
        ∃ es y, Path.Steps lib O c gul x0 es y ∧ MidI fuel c.blocks y y' := by
      rintro es' y' ⟨b0'', hb0'', hs'⟩
      rw [e'] at hb0''; cases hb0''
      exact mid_bwd HB hpc hpc' hs' hargs0 hr0
    refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, fun hok => ?_, ?_⟩
    · obtain ⟨es', y', hy', he'⟩ := (Path.execEntry_iff_path (c := withBlocks c bl') st vals t r).mp h'
      obtain ⟨es, y, hs, hn⟩ := back es' y' hy'
      exact (Path.execEntry_iff_path (c := c) st vals t r).mpr ⟨es, y, ⟨b0, e, hs⟩, by rw [← mid_endOf hn]; exact he'⟩
    · obtain ⟨es, y, ⟨b0'', hb0'', hs⟩, he⟩ := (Path.execEntry_iff_path (c := c) st vals t r).mp h'
      rw [e] at hb0''; cases hb0''
      obtain ⟨es', y', hs', he'⟩ := mid_fwd HB hpc hpc' hs he hargs0 (Path.Steps.refl _) hr0
      exact (Path.execEntry_iff_path (c := withBlocks c bl') st vals t r).mpr ⟨es', y', ⟨_, e', hs'⟩, he'⟩
    · intro es' y' k hy' hk
      obtain ⟨es, y, hs, hn⟩ := back es' y' hy'
      obtain ⟨hk', hrd⟩ := mid_reads hn hk
      obtain ⟨v, hv⟩ := hok es y k ⟨b0, e, hs⟩ hk'
      exact ⟨v, by rw [hrd, hv]⟩
    · intro es' y' k hy' hk
      obtain ⟨es, y, hs, hn⟩ := back es' y' hy'
      exact argU_isSome _ _ _ _ hn.2.2.2.1 (fun k hk => hargs es y k ⟨b0, e, hs⟩ hk) k hk

/-- **The preservation statement of `+remove-empty-middle` holds.** -/
theorem middleKeeps (fuel : Nat) : MiddleKeeps (Map := Map) fuel :=
  fun c _ _ h hpc hpc' => middle_keeps_of c h hpc hpc'

end Opt
end SkaModel
end Formalization
