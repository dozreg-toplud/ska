import lemmas.Ska.CompIndirectNext

/-!
# The block `out` of `+kerf` under a fork-free `%next`

README Gaps 12.13 (seventeenth session).  Under a goal `%next (ofSure sur)
th` the case `%2` of `runLC` makes the block `out = [hop th]` and `+kern`
puts in front of it the ops of `+kern-need` from the product register
`pro`.  The lazy need has no entries, so `+kern` walks the block `out` only,
takes `pro` itself as its source and makes no proxy.

* `runs_keep`: ops of `+kern-need` (moves, `cel`, `hed`, `tal`: `KOp`)
  change no register they do not write (`Runs` is an equation of the
  interpreter, so the registers after the ops are read through a `%don`).
  `KernSemS` only keeps the registers below the ops' fresh registers; a
  parent needs more, the registers of `ned` (the subject whole, which the
  lazy blocks read) lie above every register of the run.
* `kernLoop_kop`: the ops of `+kern-need` are `KOp`.
* `outGoal_next_of_fill`: a block `[ops; hop th]` whose ops fill `sur` from
  `pro` and keep `K` meets `OutGoal` for `%next sur th`.
* `kerf_ofSure`: what `+kerf` makes for a fork-free `%next`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Ops that change only what they write -/

/-- The ops of `+kern-need`. -/
def KOp : Pole → Prop
  | Pole.mov _ _ => True
  | Pole.hed _ _ => True
  | Pole.tal _ _ => True
  | Pole.cel _ => True
  | _ => False

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}

theorem kop_exec {p : Pole} (hp : KOp p) (st : σ) (R : Map (Option Noun)) (t : Trace) :
    execPole lib O gul st p R t =
      (localPole lib gul p R t).map fun (ton, regs', trace') => (ton, regs', trace', st) := by
  cases p <;> first | rfl | exact hp.elim

theorem kop_local {p : Pole} (hp : KOp p) (R : Map (Option Noun)) (t : Trace) :
    (∃ R1, localPole lib gul p R t = some (Tone.zero (A 0), R1, t)) ∨
    localPole lib gul p R t = some (Tone.two t, R, t) ∨ localPole lib gul p R t = Option.none := by
  cases p with
  | mov s d =>
    cases e : move s d R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some R1 => exact Or.inl ⟨R1, by simp [localPole, e]⟩
  | hed s d =>
    cases e : SkaModel.read s R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some v =>
      cases v with
      | atom a => exact Or.inr (Or.inr (by simp [localPole, e]))
      | cell x y => exact Or.inl ⟨store d x R, by simp [localPole, e]⟩
  | tal s d =>
    cases e : SkaModel.read s R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some v =>
      cases v with
      | atom a => exact Or.inr (Or.inr (by simp [localPole, e]))
      | cell x y => exact Or.inl ⟨store d y R, by simp [localPole, e]⟩
  | cel s =>
    cases e : SkaModel.read s R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some v =>
      cases v with
      | atom a => exact Or.inr (Or.inl (by simp [localPole, e]))
      | cell x y => exact Or.inl ⟨R, by simp [localPole, e]⟩
  | _ => exact hp.elim

theorem execBlob_imm_don (st : σ) (R : Map (Option Noun)) (t : Trace) (n : Noun) (x : Nat) :
    execBlob lib O c gul st R t ⟨[], [Pole.imm n x], Termin.don x⟩ [] = some (Tone.zero n, st) := by
  rw [execBlob_cons]
  simp [execPole, localPole, execBlob_don', read_store_eq]

/-- The code after some ops cannot be the same whatever follows them. -/
theorem execBlob_not_const {st : σ} {R : Map (Option Noun)} {t : Trace} {X : Option (Tone × σ)}
    (h : ∀ (rest : List Pole) (fin : Termin), execBlob lib O c gul st R t ⟨[], rest, fin⟩ [] = X) : False := by
  have h0 := h [Pole.imm (A 0) 0] (Termin.don 0)
  have h1 := h [Pole.imm (A 1) 0] (Termin.don 0)
  rw [execBlob_imm_don] at h0 h1
  rw [← h0] at h1
  simp at h1

/-- **Ops of `+kern-need` keep every register they do not write.** -/
theorem runs_keep {st : σ} {t : Trace} : ∀ (A : List Pole) (R R' : Map (Option Noun)), (∀ p ∈ A, KOp p) →
    Runs lib O c gul st t A R R' → ∀ x, (∀ p ∈ A, x ∉ poleWr p) → SkaModel.read x R' = SkaModel.read x R
  | [], R, R', _, h, x, _ => by
    have e := h [] (Termin.don x)
    simp only [List.nil_append, execBlob_don'] at e
    cases h1 : SkaModel.read x R <;> cases h2 : SkaModel.read x R' <;> simp_all
  | p :: A, R, R', hk, h, x, hw => by
    have hp : KOp p := hk p List.mem_cons_self
    rcases kop_local (lib := lib) (gul := gul) hp R t with ⟨R1, e⟩ | e | e
    · have R1' : Runs lib O c gul st t A R1 R' := fun rest fin => by
        have := h rest fin
        rw [List.cons_append, execBlob_cons, kop_exec hp, e] at this
        exact this
      have k1 := runs_keep A R1 R' (fun q hq => hk q (List.mem_cons_of_mem _ hq)) R1' x
        (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      have k2 := localPole_frame lib gul e x (hw p List.mem_cons_self)
      rw [k1]; unfold SkaModel.read; rw [k2]
    · exact (execBlob_not_const (X := some (Tone.two t, st)) fun rest fin => by
        rw [← h rest fin, List.cons_append, execBlob_cons, kop_exec hp, e]; rfl).elim
    · exact (execBlob_not_const (X := Option.none) fun rest fin => by
        rw [← h rest fin, List.cons_append, execBlob_cons, kop_exec hp, e]; rfl).elim

end

/-! ## The ops of `+kern-need` are `KOp` -/

theorem kernBoth_kop {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)}
    (sh : ∀ r' acc (g g' : Gen Map) ops, kh r' acc g = some (ops, g') → (∀ p ∈ acc, KOp p) → ∀ p ∈ ops, KOp p)
    (st : ∀ r' acc (g g' : Gen Map) ops, kt r' acc g = some (ops, g') → (∀ p ∈ acc, KOp p) → ∀ p ∈ ops, KOp p)
    {acc : List Pole} {g g' : Gen Map} {ops : List Pole} (hk : kernBoth r d kh kt acc g = some (ops, g'))
    (ha : ∀ p ∈ acc, KOp p) : ∀ p ∈ ops, KOp p := by
  unfold kernBoth at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  obtain ⟨o1, g2, h2, hk⟩ := bind_some hk
  have A2 := st _ _ _ _ _ h2 ha
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  obtain ⟨o2, g4, h4, hk⟩ := bind_some hk
  have A2' : ∀ p ∈ (if o1 ≠ acc then Pole.tal d rt :: o1 else o1), KOp p := by
    split
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · trivial
      · exact A2 p hp
    · exact A2
  have A4 := sh _ _ _ _ _ h4 A2'
  by_cases e : r = d
  · rw [if_pos e] at hk; cases hk
  rw [if_neg e] at hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · trivial
  · trivial
  · by_cases e2 : o2 ≠ (if o1 ≠ acc then Pole.tal d rt :: o1 else o1)
    · rw [if_pos e2] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · trivial
      · exact A4 p hp
    · rw [if_neg e2] at hp; exact A4 p hp

theorem kernLoop_kop : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Gen Map) (ops : List Pole),
    kernLoop r tgt acc g = some (ops, g') → (∀ p ∈ acc, KOp p) → ∀ p ∈ ops, KOp p := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h ha
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ha
  | this d =>
    intro r acc g g' ops h ha
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · trivial
    · exact ha p hp
  | pair p q ihp ihq =>
    intro r acc g g' ops h ha
    simp only [kernLoop] at h
    obtain ⟨rn, g1, _, h⟩ := bind_some h
    exact kernBoth_kop (fun r' acc g g' ops h => ihp r' acc g g' ops h)
      (fun r' acc g g' ops h => ihq r' acc g g' ops h) h ha
  | both d h t ihh iht =>
    intro r acc g g' ops hk ha
    simp only [kernLoop] at hk
    exact kernBoth_kop (fun r' acc g g' ops h' => ihh r' acc g g' ops h')
      (fun r' acc g g' ops h' => iht r' acc g g' ops h') hk ha

/-! ## `OutGoal` of a block that fills the need -/

/-- **A block `[ops; hop th]` whose ops fill `sur` from `pro` and keep the
registers of `K` meets `OutGoal` for `%next sur th`.** -/
theorem outGoal_next_of_fill {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K : Nat → Prop} {pro out : Nat} {sur : Sure S} {th : Jmp}
    {A : List Pole} (hb : HoonMap.get c.blocks out = some ⟨[], A, Termin.hop th⟩)
    (hfill : ∀ (st : σ) (t : Trace) (R : Map (Option Noun)) (v : Noun), SkaModel.read pro R = some v →
      (FitsS sur v → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsS sur R' v ∧
        ∀ x, K x → SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ FitsS sur v → Crashes lib O c gul st t A R)) :
    OutGoal lib O c gul Inv ν K pro out (CGoal.next sur th) := by
  intro st regs ti tm p hI htr hp
  obtain ⟨F1, F2⟩ := hfill st ti regs p hp
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨R', hr, hh, hk⟩ := F1 hf
    refine ⟨st, R', hI, Needs.le_refl _, hh.1, hk, ?_⟩
    have e1 := hr [] (Termin.hop th)
    simp only [List.append_nil] at e1
    rw [goJ_jmp0 _ _ _ _ hb, e1, execBlob_hop]
  · have e2 := F2 hf [] (Termin.hop th)
    simp only [List.append_nil] at e2
    exact ⟨Tone.two ti, st, hI, Needs.le_refl _, by rw [goJ_jmp0 _ _ _ _ hb, e2], ToneRel.two htr⟩

end Comp
end SkaModel
end Formalization
