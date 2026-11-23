import lemmas.Ska.CompModel

/-!
# What the code of `run` does: the relation and its first facts

The relation that the model of `run` (`CompModel.lean`) establishes for the
blocks it emits, against the interpreter's `execBlob`.

* `HoldsN ned regs n`: the registers hold the noun `n` as the need `ned`
  asks; `Fits ned n`: `n` has the cells the need takes apart.  `Looks lok n`:
  `n` has every axis of `lok`.  `HoldsS`, `FitsS`: both, for a `sure`.
* `GoalSem`: what entering the jump `je` does for a goal when the value of
  the nomm is `v`.  On `%next` the product must be put in registers as the
  goal's need asks, where it has the shape that need and its looks ask, and
  the code must crash where it has not: the code that follows takes it
  apart without checking.
* `RunOK nm goal g0 g1 nex`: `run` went from the state `g0` to `g1` and
  returned `nex`.  The state only grew (`Ext`), the registers of the need
  of the subject are the goal's or fresh, a subject that has not the shape
  or the looks of that need is one on which the nomm crashes or makes a
  product that has not those of the goal (`nec`), and, in any program that
  holds the blocks of `g1` at the labels `run` allocated, entering `nex`
  with the subject held does what `GoalSem` says, keeping the registers
  allocated before `g0` that the goal does not name (`sem`).
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Needs and nouns -/

/-- The cells a need takes apart. -/
def Fits : Need → Noun → Prop
  | Need.none, _ => True
  | Need.this _, _ => True
  | Need.pair p q, Noun.cell h t => Fits p h ∧ Fits q t
  | Need.both _ p q, Noun.cell h t => Fits p h ∧ Fits q t
  | _, _ => False

/-- The registers `regs` hold `n` as the need asks. -/
def HoldsN : Need → Map Noun → Noun → Prop
  | Need.none, _, _ => True
  | Need.this r, regs, n => SkaModel.read r regs = some n
  | Need.pair p q, regs, Noun.cell h t => HoldsN p regs h ∧ HoldsN q regs t
  | Need.both r p q, regs, Noun.cell h t =>
      SkaModel.read r regs = some (C h t) ∧ HoldsN p regs h ∧ HoldsN q regs t
  | _, _, _ => False

/-- The registers of a need. -/
def NMem : Need → Nat → Prop
  | Need.none, _ => False
  | Need.this r, x => x = r
  | Need.pair p q, x => NMem p x ∨ NMem q x
  | Need.both r p q, x => x = r ∨ NMem p x ∨ NMem q x

/-- No register appears twice in a need. -/
def Distinct : Need → Prop
  | Need.none => True
  | Need.this _ => True
  | Need.pair p q => Distinct p ∧ Distinct q ∧ ∀ x, NMem p x → ¬ NMem q x
  | Need.both r p q => Distinct p ∧ Distinct q ∧ (∀ x, NMem p x → ¬ NMem q x) ∧ ¬ NMem p r ∧ ¬ NMem q r

def Looks (lok : S) (n : Noun) : Prop := ∀ a ∈ HoonSet.toList lok, (slot? a n).isSome

def FitsS (s : Sure S) (n : Noun) : Prop := Fits s.ned n ∧ Looks s.lok n

def HoldsS (s : Sure S) (regs : Map Noun) (n : Noun) : Prop := HoldsN s.ned regs n ∧ Looks s.lok n

theorem fits_of_holds : ∀ (ned : Need) {regs : Map Noun} {n : Noun}, HoldsN ned regs n → Fits ned n
  | Need.none, _, _, _ => trivial
  | Need.this _, _, _, _ => trivial
  | Need.pair p q, _, Noun.cell _ _, h => ⟨fits_of_holds p h.1, fits_of_holds q h.2⟩
  | Need.both _ p q, _, Noun.cell _ _, h => ⟨fits_of_holds p h.2.1, fits_of_holds q h.2.2⟩
  | Need.pair _ _, _, Noun.atom _, h => h.elim
  | Need.both _ _ _, _, Noun.atom _, h => h.elim

theorem fitsS_of_holdsS {s : Sure S} {regs : Map Noun} {n : Noun} (h : HoldsS s regs n) : FitsS s n :=
  ⟨fits_of_holds _ h.1, h.2⟩

/-- Registers that agree on a need's registers hold what it holds. -/
theorem HoldsN.agree : ∀ (ned : Need) {regs regs' : Map Noun} {n : Noun},
    (∀ x, NMem ned x → SkaModel.read x regs' = SkaModel.read x regs) → HoldsN ned regs n →
    HoldsN ned regs' n
  | Need.none, _, _, _, _, h => h
  | Need.this r, _, _, _, ha, h => by
    simp only [HoldsN] at h ⊢; rw [ha r rfl]; exact h
  | Need.pair p q, _, _, Noun.cell a b, ha, h =>
    ⟨HoldsN.agree p (fun x hx => ha x (Or.inl hx)) h.1, HoldsN.agree q (fun x hx => ha x (Or.inr hx)) h.2⟩
  | Need.both r p q, _, _, Noun.cell a b, ha, h =>
    ⟨by rw [ha r (Or.inl rfl)]; exact h.1, HoldsN.agree p (fun x hx => ha x (Or.inr (Or.inl hx))) h.2.1,
      HoldsN.agree q (fun x hx => ha x (Or.inr (Or.inr hx))) h.2.2⟩
  | Need.pair _ _, _, _, Noun.atom _, _, h => h.elim
  | Need.both _ _ _, _, _, Noun.atom _, _, h => h.elim

theorem looks_empty (n : Noun) : Looks (HoonSet.empty : S) n := fun a ha =>
  absurd ha (HoonSet.mem_empty a)

theorem fitsS_bunt (n : Noun) : FitsS (Sure.bunt : Sure S) n := ⟨trivial, looks_empty n⟩

theorem holdsS_bunt (regs : Map Noun) (n : Noun) : HoldsS (Sure.bunt : Sure S) regs n :=
  ⟨trivial, looks_empty n⟩

theorem mem_setRun (f : Nat → Nat) (s : S) (y : Nat) :
    y ∈ HoonSet.toList (setRun f s) ↔ ∃ x ∈ HoonSet.toList s, y = f x := by
  unfold setRun
  induction HoonSet.toList s with
  | nil => simp [HoonSet.mem_empty]
  | cons a l ih => simp [List.foldr, HoonSet.mem_put, ih]

theorem mem_setOne (x y : Nat) : y ∈ HoonSet.toList (setOne x : S) ↔ y = x := by
  simp [setOne, HoonSet.mem_put, HoonSet.mem_empty]

/-! ## Goals -/

/-- The registers a goal names. -/
def GMem : CGoal S → Nat → Prop
  | CGoal.next laz _, r => NMem laz.ned r
  | _, _ => False

/-- A need with no subterm `pair none none`. -/
def Clean : Need → Prop
  | Need.none => True
  | Need.this _ => True
  | Need.pair p q => ¬ (p = Need.none ∧ q = Need.none) ∧ Clean p ∧ Clean q
  | Need.both _ p q => Clean p ∧ Clean q

/-- The need of a goal `%next` is clean. -/
def GClean : CGoal S → Prop
  | CGoal.next laz _ => Clean laz.ned
  | _ => True

/-- A product that has not the shape or the looks the goal asks. -/
def GNot : CGoal S → Noun → Prop
  | CGoal.next laz _, p => ¬ FitsS laz p
  | _, _ => False

/-- The registers that the code for a goal keeps: allocated before it, and
not named by the goal. -/
def Keep (g0 : Gen Map) (goal : CGoal S) (r : Nat) : Prop := r < g0.re ∧ ¬ GMem goal r

section Exec
variable (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ)

/-- Going to the target of a jump with its arguments. -/
def goJ (regs : Map Noun) (t : Trace) (j : Jmp) : Option (Tone × σ) :=
  (HoonMap.get c.blocks j.there).bind fun b => execBlob lib O c gul st regs t b j.args

/-- **What entering `je` does for the goal**, for the value `v` of the
nomm.  `K` are the registers kept. -/
def GoalSem (K : Nat → Prop) (regs : Map Noun) (t : Trace) (je : Jmp) : CGoal S → Option Noun → Prop
  | CGoal.done, v => goJ lib O c gul st regs t je = some (toneOf t v, st)
  | CGoal.next laz th, some p =>
      (FitsS laz p → ∃ regs', HoldsN laz.ned regs' p ∧
        (∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs) ∧
        goJ lib O c gul st regs t je = goJ lib O c gul st regs' t th) ∧
      (¬ FitsS laz p → goJ lib O c gul st regs t je = some (Tone.two t, st))
  | CGoal.pick z _, some (Noun.atom 0) => ∃ regs',
      (∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      goJ lib O c gul st regs t je = goJ lib O c gul st regs' t z
  | CGoal.pick _ o, some (Noun.atom 1) => ∃ regs',
      (∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      goJ lib O c gul st regs t je = goJ lib O c gul st regs' t o
  | _, _ => goJ lib O c gul st regs t je = some (Tone.two t, st)

end Exec

/-! ## The state -/

/-- The state only grew: more registers and labels, the same mode, and the
blocks of the labels allocated before kept. -/
def Ext (g0 g1 : Gen Map) : Prop :=
  g0.re ≤ g1.re ∧ g0.bo ≤ g1.bo ∧ g1.drop = g0.drop ∧
    ∀ o, o < g0.bo → HoonMap.get g1.blocks o = HoonMap.get g0.blocks o

theorem Ext.refl (g : Gen Map) : Ext g g := ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ => rfl⟩

theorem Ext.trans {g0 g1 g2 : Gen Map} (a : Ext g0 g1) (b : Ext g1 g2) : Ext g0 g2 :=
  ⟨Nat.le_trans a.1 b.1, Nat.le_trans a.2.1 b.2.1, b.2.2.1.trans a.2.2.1,
    fun o ho => (b.2.2.2 o (Nat.lt_of_lt_of_le ho a.2.1)).trans (a.2.2.2 o ho)⟩

/-- The program `c` holds the blocks of `g1` at the labels allocated from
`g0` on. -/
def Agree (c : Straight Map) (g0 g1 : Gen Map) : Prop :=
  ∀ o, g0.bo ≤ o → o < g1.bo → HoonMap.get c.blocks o = HoonMap.get g1.blocks o

theorem Agree.left {c : Straight Map} {g0 g1 g2 : Gen Map} (h : Agree c g0 g2) (e01 : Ext g0 g1)
    (e12 : Ext g1 g2) : Agree c g0 g1 := fun o h0 h1 =>
  (h o h0 (Nat.lt_of_lt_of_le h1 e12.2.1)).trans (e12.2.2.2 o h1)

theorem Agree.right {c : Straight Map} {g0 g1 g2 : Gen Map} (h : Agree c g0 g2) (e01 : Ext g0 g1) :
    Agree c g1 g2 := fun o h0 h1 => h o (Nat.le_trans e01.2.1 h0) h1

/-- What `run` assumes of its goal: the registers it names are allocated
and distinct. -/
def GoalOK (g0 : Gen Map) : CGoal S → Prop
  | CGoal.next laz _ => Distinct laz.ned ∧ ∀ r, NMem laz.ned r → r < g0.re
  | _ => True

/-- **The relation for one run.** -/
structure RunOK (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : Next S) : Prop where
  ext : Ext g0 g1
  regs : ∀ r, NMem nex.laz.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  nec : ∀ s, ¬ FitsS nex.laz s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ GNot goal p
  dist : Distinct nex.laz.ned
  sem : g0.drop = false → ∀ (c : Straight Map), Agree c g0 g1 → ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun)
    (regs : Map Noun) (t : Trace) (gul : Noun), HoldsS nex.laz regs s →
    GoalSem lib O c gul st (Keep g0 goal) regs t nex.th goal (pureEval nm s)

/-! ## The monad -/

theorem bind_apply {α β : Type} (x : CM Map α) (f : α → CM Map β) (g : Gen Map) :
    (x >>= f) g = (x g).bind fun p => f p.1 p.2 := rfl

theorem pure_apply {α : Type} (a : α) (g : Gen Map) : (pure a : CM Map α) g = some (a, g) := rfl

theorem re_apply (g : Gen Map) : (re : CM Map Nat) g = some (g.re, { g with re := g.re + 1 }) := rfl

/-- The state after `(emit b)`. -/
def Gen.emitted (g : Gen Map) (b : Blob) : Gen Map :=
  { g with bo := g.bo + 1, blocks := (if g.drop then g.blocks else HoonMap.put g.blocks g.bo b) }

theorem emit_apply (b : Blob) (g : Gen Map) : (emit b : CM Map Nat) g =
    some (g.bo, g.emitted b) := by
  rcases g with ⟨re, bo, id, drop, blocks⟩
  cases drop <;> rfl

theorem ext_re (g : Gen Map) : Ext g { g with re := g.re + 1 } :=
  ⟨Nat.le_succ _, Nat.le_refl _, rfl, fun _ _ => rfl⟩

theorem ext_emit (g : Gen Map) (b : Blob) :
    Ext g (g.emitted b) :=
  ⟨Nat.le_refl _, Nat.le_succ _, rfl, fun o ho => by
    simp only [Gen.emitted]; cases g.drop <;> simp [HoonMap.get_put, Nat.ne_of_lt ho]⟩

/-! ## Executing blocks -/

section Exec
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

theorem execBlob_hop (regs : Map Noun) (t : Trace) (j : Jmp) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.hop j⟩ [] = goJ lib O c gul st regs t j := by
  rw [execBlob]; simp [goJ]

theorem execBlob_don' (regs : Map Noun) (t : Trace) (r : Nat) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.don r⟩ [] =
      (SkaModel.read r regs).bind fun v => some (Tone.zero v, st) := by
  rw [execBlob]; simp

theorem execBlob_bom' (regs : Map Noun) (t : Trace) (o : Option Nat) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.bom o⟩ [] = some (Tone.two t, st) := by
  rw [execBlob]; simp

theorem execBlob_brn (regs : Map Noun) (t : Trace) (r : Nat) (z o : Jmp) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.brn r z o⟩ [] =
      (SkaModel.read r regs).bind fun v =>
        if v = A 0 then goJ lib O c gul st regs t z
        else if v = A 1 then goJ lib O c gul st regs t o else some (Tone.two t, st) := by
  rw [execBlob]; simp [goJ]

theorem execBlob_cons (p : Pole) (rest : List Pole) (fin : Termin) (regs : Map Noun) (t : Trace) :
    execBlob lib O c gul st regs t ⟨[], p :: rest, fin⟩ [] =
      (execPole lib O gul st p regs t).bind fun (ton, regs', t', st') =>
        match ton with
        | Tone.zero _ => execBlob lib O c gul st' regs' t' ⟨[], rest, fin⟩ []
        | _ => some (ton, st') := by
  rw [execBlob]; rfl

theorem goJ_jmp0 (regs : Map Noun) (t : Trace) (o : Nat) (b : Blob) (hb : HoonMap.get c.blocks o = some b) :
    goJ lib O c gul st regs t (jmp0 o) = execBlob lib O c gul st regs t b [] := by
  simp [goJ, jmp0, hb]

end Exec

/-! ## `+from` -/

theorem fromPath_one (ned : Need) : fromPath ned 1 = ned := by rw [fromPath]; simp

theorem fromPath_step (ned : Need) {axe : Nat} (h : 2 ≤ axe) :
    fromPath ned axe = if cap axe = 2 then Need.pair (fromPath ned (mas axe)) Need.none
      else Need.pair Need.none (fromPath ned (mas axe)) := by
  rw [fromPath]; simp [show ¬ axe ≤ 1 by omega]

/-- The need `fromPath ned axe` holds `s` exactly when `s` has the axis and
`ned` holds what is there. -/
theorem holds_fromPath (ned : Need) (regs : Map Noun) : ∀ (axe : Nat), 1 ≤ axe → ∀ (s : Noun),
    HoldsN (fromPath ned axe) regs s ↔ ∃ p, slot? axe s = some p ∧ HoldsN ned regs p := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha s
    by_cases h1 : axe = 1
    · subst h1; simp [fromPath_one, slot?_one]
    · have h2 : 2 ≤ axe := by omega
      rw [fromPath_step ned h2, slot?_cap h2]
      have ihm := ih (mas axe) (mas_lt axe h2) (mas_pos axe h2)
      rcases cap_cases _ h2 with hc | hc <;> cases s with
      | atom _ => simp [HoldsN, hc]
      | cell a b => simp [HoldsN, hc, ihm]

theorem fits_fromPath (ned : Need) : ∀ (axe : Nat), 1 ≤ axe → ∀ (s : Noun),
    Fits (fromPath ned axe) s ↔ ∃ p, slot? axe s = some p ∧ Fits ned p := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha s
    by_cases h1 : axe = 1
    · subst h1; simp [fromPath_one, slot?_one]
    · have h2 : 2 ≤ axe := by omega
      rw [fromPath_step ned h2, slot?_cap h2]
      have ihm := ih (mas axe) (mas_lt axe h2) (mas_pos axe h2)
      rcases cap_cases _ h2 with hc | hc <;> cases s with
      | atom _ => simp [Fits, hc]
      | cell a b => simp [Fits, hc, ihm]

theorem nmem_fromPath (ned : Need) : ∀ (axe : Nat) (r : Nat), NMem (fromPath ned axe) r → NMem ned r := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro r hr
    by_cases h1 : axe ≤ 1
    · rw [fromPath] at hr; simp [h1] at hr; exact hr
    · rw [fromPath_step ned (by omega)] at hr
      split at hr <;> simp only [NMem, false_or, or_false] at hr <;> exact ih _ (mas_lt axe (by omega)) r hr

theorem pegF_zero (a : Nat) : Hoon.pegF a 0 = 0 := by rw [Hoon.pegF_eq]; simp

/-- Looks under `peg`: the looks of the noun at `axe`, pegged, are looks of
the whole that has it. -/
theorem looks_setRun_peg {axe : Nat} (ha : 1 ≤ axe) (lok : S) (s p : Noun) (hp : slot? axe s = some p) :
    Looks (setRun (Hoon.pegF axe) lok) s ↔ Looks lok p := by
  constructor
  · intro h x hx
    have := h (Hoon.pegF axe x) ((mem_setRun _ _ _).mpr ⟨x, hx, rfl⟩)
    by_cases hx0 : x = 0
    · subst hx0; rw [pegF_zero] at this; simp [slot?_zero] at this
    · rw [Hoon.slot_pegF axe ha s x (by omega), hp] at this; simpa using this
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := (mem_setRun _ _ _).mp hy
    have hx' := h x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [slot?_zero] at hx'
    · rw [Hoon.slot_pegF axe ha s x (by omega), hp]; simpa using hx'

theorem slot_isSome_of_peg {axe : Nat} (ha : 1 ≤ axe) {lok : S} {s : Noun}
    (hl : Looks (setRun (Hoon.pegF axe) lok) s) {x : Nat} (hx : x ∈ HoonSet.toList lok) :
    (slot? axe s).isSome := by
  have := hl (Hoon.pegF axe x) ((mem_setRun _ _ _).mpr ⟨x, hx, rfl⟩)
  by_cases hx0 : x = 0
  · subst hx0; rw [pegF_zero] at this; simp [slot?_zero] at this
  · rw [Hoon.slot_pegF axe ha s x (by omega)] at this
    cases e : slot? axe s <;> simp_all

/-- **`+from-sure`**: the sure need of the subject of `[0 axe]` holds the
subject when the need of the product holds the noun at `axe`; and a subject
that has not its shape and looks lacks the axis, or has there a noun that
has not those of the product's. -/
theorem fromSure_spec {axe : Nat} {sur sur' : Sure S} (h : fromSure axe sur = some sur') :
    1 ≤ axe ∧
    (∀ (regs : Map Noun) s, HoldsS sur' regs s → ∃ p, slot? axe s = some p ∧ HoldsS sur regs p) ∧
    (∀ s p, slot? axe s = some p → FitsS sur p → FitsS sur' s) ∧
    (∀ r, NMem sur'.ned r → NMem sur.ned r) := by
  unfold fromSure at h
  by_cases h0 : axe = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  have ha : 1 ≤ axe := by omega
  refine ⟨ha, ?_⟩
  by_cases hn : sur.ned = Need.none
  · simp only [hn, if_true] at h
    by_cases h1 : axe = 1
    · simp [h1] at h
    simp only [h1, if_false, Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, fun r hr => by simp [NMem] at hr⟩
    · intro regs s ⟨_, hl⟩
      have hs : (slot? axe s).isSome := by
        by_cases he : HoonSet.isEmpty sur.lok = true
        · simp only [he, if_true] at hl
          exact hl axe ((mem_setOne axe axe).mpr rfl)
        · simp only [he, if_false] at hl
          have hne : HoonSet.toList sur.lok ≠ [] := fun e => he ((HoonSet.isEmpty_iff _).mpr e)
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
          exact slot_isSome_of_peg ha hl hx
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
      refine ⟨p, hp, by rw [hn]; trivial, ?_⟩
      by_cases he : HoonSet.isEmpty sur.lok = true
      · intro x hx; rw [(HoonSet.isEmpty_iff _).mp he] at hx; cases hx
      · simp only [he, if_false] at hl
        exact (looks_setRun_peg ha _ s p hp).mp hl
    · intro s p hp ⟨_, hl⟩
      refine ⟨trivial, ?_⟩
      by_cases he : HoonSet.isEmpty sur.lok = true
      · simp only [he, if_true]
        intro y hy; rw [(mem_setOne axe y).mp hy, hp]; rfl
      · simp only [he, if_false]
        exact (looks_setRun_peg ha _ s p hp).mpr hl
  · simp only [hn, if_false, Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_, fun r hr => nmem_fromPath _ axe r hr⟩
    · intro regs s ⟨hh, hl⟩
      obtain ⟨p, hp, hh'⟩ := (holds_fromPath _ regs axe ha s).mp hh
      exact ⟨p, hp, hh', (looks_setRun_peg ha _ s p hp).mp hl⟩
    · intro s p hp ⟨hf, hl⟩
      exact ⟨(fits_fromPath _ axe ha s).mpr ⟨p, hp, hf⟩, (looks_setRun_peg ha _ s p hp).mpr hl⟩

/-! ## Ops that do not leave the block -/

section Ops
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

/-- The ops `A` run from `regs` to `regs'`, whatever follows them. -/
def Runs (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (A : List Pole) (regs regs' : Map Noun) : Prop :=
  ∀ (rest : List Pole) (fin : Termin), execBlob lib O c gul st regs t ⟨[], A ++ rest, fin⟩ [] =
    execBlob lib O c gul st regs' t ⟨[], rest, fin⟩ []

/-- The ops `A` crash from `regs`, with the trace the block was entered with. -/
def Crashes (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (A : List Pole) (regs : Map Noun) : Prop :=
  ∀ (rest : List Pole) (fin : Termin), execBlob lib O c gul st regs t ⟨[], A ++ rest, fin⟩ [] =
    some (Tone.two t, st)

theorem Runs.nil (regs : Map Noun) : Runs lib O c gul st t [] regs regs := fun _ _ => rfl

theorem Runs.append {A B : List Pole} {r0 r1 r2 : Map Noun} (a : Runs lib O c gul st t A r0 r1)
    (b : Runs lib O c gul st t B r1 r2) : Runs lib O c gul st t (A ++ B) r0 r2 := fun rest fin => by
  rw [List.append_assoc, a, b]

theorem Crashes.append_left {A B : List Pole} {r0 : Map Noun} (a : Crashes lib O c gul st t A r0) :
    Crashes lib O c gul st t (A ++ B) r0 := fun rest fin => by rw [List.append_assoc, a]

theorem Crashes.append_right {A B : List Pole} {r0 r1 : Map Noun} (a : Runs lib O c gul st t A r0 r1)
    (b : Crashes lib O c gul st t B r1) : Crashes lib O c gul st t (A ++ B) r0 := fun rest fin => by
  rw [List.append_assoc, a, b]

/-- One local op that ends with `[%0 ~]` runs on. -/
theorem Runs.one {p : Pole} {regs regs' : Map Noun}
    (h : localPole lib gul p regs t = some (Tone.zero (A 0), regs', t))
    (hl : ∀ u f d, p ≠ Pole.nok u f d) (hc : ∀ a v d, p ≠ Pole.cal a v d) :
    Runs lib O c gul st t [p] regs regs' := fun rest fin => by
  rw [List.singleton_append, execBlob_cons]
  have : execPole lib O gul st p regs t = some (Tone.zero (A 0), regs', t, st) := by
    cases p <;> first | (simp_all [execPole]; done) | (simp [localPole] at h)
  rw [this]; rfl

theorem runs_imm (n : Noun) (d : Nat) (regs : Map Noun) :
    Runs lib O c gul st t [Pole.imm n d] regs (store d n regs) :=
  Runs.one rfl (by simp) (by simp)

theorem runs_mov {s d : Nat} {regs : Map Noun} {v : Noun} (h : SkaModel.read s regs = some v) :
    Runs lib O c gul st t [Pole.mov s d] regs (store d v regs) :=
  Runs.one (by simp [localPole, move, h]) (by simp) (by simp)

theorem runs_con {h tl d : Nat} {regs : Map Noun} {a b : Noun} (ha : SkaModel.read h regs = some a)
    (hb : SkaModel.read tl regs = some b) :
    Runs lib O c gul st t [Pole.con h tl d] regs (store d (C a b) regs) :=
  Runs.one (by simp [localPole, ha, hb]) (by simp) (by simp)

theorem runs_cel {p : Nat} {regs : Map Noun} {a b : Noun} (h : SkaModel.read p regs = some (C a b)) :
    Runs lib O c gul st t [Pole.cel p] regs regs :=
  Runs.one (by simp [localPole, h]) (by simp) (by simp)

theorem crashes_cel {p : Nat} {regs : Map Noun} {a : Nat} (h : SkaModel.read p regs = some (A a)) :
    Crashes lib O c gul st t [Pole.cel p] regs := fun rest fin => by
  rw [List.singleton_append, execBlob_cons]
  simp [execPole, localPole, h]

theorem runs_inc {s d : Nat} {regs : Map Noun} {a : Nat} (h : SkaModel.read s regs = some (A a)) :
    Runs lib O c gul st t [Pole.inc s d] regs (store d (A (a + 1)) regs) :=
  Runs.one (by simp [localPole, h]) (by simp) (by simp)

theorem crashes_inc {s d : Nat} {regs : Map Noun} {a b : Noun} (h : SkaModel.read s regs = some (C a b)) :
    Crashes lib O c gul st t [Pole.inc s d] regs := fun rest fin => by
  rw [List.singleton_append, execBlob_cons]
  simp [execPole, localPole, h]

theorem runs_hed {s d : Nat} {regs : Map Noun} {a b : Noun} (h : SkaModel.read s regs = some (C a b)) :
    Runs lib O c gul st t [Pole.hed s d] regs (store d a regs) :=
  Runs.one (by simp [localPole, h]) (by simp) (by simp)

theorem runs_tal {s d : Nat} {regs : Map Noun} {a b : Noun} (h : SkaModel.read s regs = some (C a b)) :
    Runs lib O c gul st t [Pole.tal s d] regs (store d b regs) :=
  Runs.one (by simp [localPole, h]) (by simp) (by simp)

theorem runs_equ {l r : Nat} {regs : Map Noun} {a b : Noun} (ha : SkaModel.read l regs = some a)
    (hb : SkaModel.read r regs = some b) : Runs lib O c gul st t [Pole.equ l r] regs regs :=
  Runs.one (by simp [localPole, ha, hb]) (by simp) (by simp)

theorem read_store_eq (r : Nat) (v : Noun) (regs : Map Noun) : SkaModel.read r (store r v regs) = some v := by
  simp [SkaModel.read, store, HoonMap.get_put]

theorem read_store_ne {r r' : Nat} (h : r' ≠ r) (v : Noun) (regs : Map Noun) :
    SkaModel.read r' (store r v regs) = SkaModel.read r' regs := by
  simp [SkaModel.read, store, HoonMap.get_put, h]

end Ops

end Comp
end SkaModel
end Formalization
