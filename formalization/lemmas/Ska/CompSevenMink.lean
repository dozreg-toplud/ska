import lemmas.Ska.CompSevenG
import lemmas.Ska.CompBondCall

/-!
# `+mink` on the forms of the nomm `[7 p q]`, and `UOKC` on every `Annot`

README Gaps 12.21.  The nomm `[7 p q]` stands for six formulas (`Annot`):
`[7 b c]` (`n7`), an inlined `[2 b c]` whose formula part returns `g` on
every subject (`inline`), `[8 b c]` (`n8`, the nomm `[7 [p [0 1]] q]`; `n8g`,
the nomm `[7 [p r] q]` with `r` for `[0 1]`; `n8l`, the nomm `[7 [1 [y d]] q]`
when `b` returns `y` and the subject is `d`), and `[9 a c]` (`n9`, the nomm
`[7 q r]` with `r` for `[2 [0 1] [0 a]]`), and the wrappers (`memo`, `six0`,
`six1`).  For each form the composition `MinkC7` holds with the formula of
the nomm's `p` part as `fb` and of its `q` part as `fc`, and the products of
`fb` are among the subjects the `q` part is annotated on:

* `n7`: `fb = b`, `fc = c` (`minkC7_seven`).
* `inline`: `fb = b`, `fc = g` (`minkC7_inline`).
* `n8`, `n8g` with `b` a cell: `fb = [b [0 1]]`, `fc = c` (`minkC7_eight`,
  `img_eight`); with `b` an atom both crash at once: `fb = 0`, `fc = c`
  (`minkC7_eightAtom`, `img_atom`), and the `p` part is call-free
  (`annot_atom`, `annot_slot_pure`).
* `n8l`: `fb = [1 [y d]]`, `fc = c` (`minkC7_eightL`, `img_eightL`).
* `n9`: `fb = c`, `fc = [2 [0 1] [0 a]]` (`minkC7_nine`).

`UOKC.mono`: `UOKC` on fewer subjects.  `uokc_sevenA`: `UOKC` (and `EntNew`
from the parts') of `[7 p q]` on every `Annot`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+mink` facts -/

/-- `+mink` on an atom crashes at once. -/
theorem mink_atom {lib : Lib} {gul : Noun} {tm : Trace} {s : Noun} {k : Nat} {r : Tone} :
    Mink lib gul tm s (A k) r ↔ r = Tone.two tm := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [minkF] at h
    | succ n => rw [minkF_succ_eq] at h; simp only [minkStep, Option.some.injEq] at h; exact h.symm
  · rintro rfl
    exact ⟨1, by rw [minkF_succ_eq]; rfl⟩

theorem minkF_atom {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s : Noun} {k : Nat} :
    minkF lib gul (n + 1) tm s (A k) = some (Tone.two tm) := by
  rw [minkF_succ_eq]; rfl

/-- A run of `+mink` that returns has fuel. -/
theorem minkF_pos {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s f : Noun} {r : Tone}
    (h : minkF lib gul n tm s f = some r) : ∃ k, n = k + 1 := by
  cases n with
  | zero => simp [minkF] at h
  | succ k => exact ⟨k, rfl⟩

/-! ## The six forms -/

/-- **An inlined call `[2 b c]`** whose formula part returns `g` on every
subject runs `b`, then `g` on its product. -/
theorem minkC7_inline (lib : Lib) {P : Noun → Prop} {b c g : Noun}
    (hg : ∀ x gul, P x → Mink lib gul [] x c (Tone.zero g)) : MinkC7 lib P (n3 (A 2) b c) b g where
  fwd := fun {s gul n tm r} hs h => by
    obtain ⟨n', hn, rb, hb, h | ⟨x, rfl, rc, hc, h' | ⟨y, rfl, hr⟩⟩⟩ := (minkC2_indirect lib P b c).fwd hs h
    · exact ⟨n', Nat.le_of_lt hn, rb, hb, Or.inl h⟩
    · exact absurd (mink_det_zero (hg s gul hs) hc) (h'.1 g)
    · cases mink_det_zero (hg s gul hs) hc
      exact ⟨n', Nat.le_of_lt hn, _, hb, Or.inr ⟨x, rfl, n', Nat.le_of_lt hn, hr⟩⟩
  bwd := fun {s gul tm rb} hs hb => by
    have B := (minkC2_indirect lib P b c).bwd hs hb
    refine ⟨B.1, fun u r eu hr => ?_⟩
    obtain ⟨k, hk⟩ := hg s gul hs
    exact ((B.2 u (Tone.zero g) eu ⟨k, mink_t_of_nil_zero tm hk⟩).2 g r rfl hr)

/-- **`[8 b c]` with `b` a cell** is `[b [0 1]]`, then `c`. -/
theorem minkC7_eight (lib : Lib) (P : Noun → Prop) (a1 a2 c : Noun) :
    MinkC7 lib P (n3 (A 8) (C a1 a2) c) (C (C a1 a2) (slot 1)) c where
  fwd := fun {s gul n tm r} _ h => by
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    rcases tbind_eq_some h with ⟨y, hy, h1⟩ | ⟨hb, hnz⟩
    · obtain ⟨k, rfl⟩ := minkF_pos hy
      refine ⟨k + 1 + 1, Nat.le_refl _, Tone.zero (C y s), ?_, Or.inr ⟨C y s, rfl, k + 1, by omega, h1⟩⟩
      rw [minkF_succ_eq]; simp only [minkStep]; rw [hy, tbind_zero, minkF_slot1', tbind_zero]
    · obtain ⟨k, rfl⟩ := minkF_pos hb
      refine ⟨k + 1 + 1, Nat.le_refl _, r, ?_, Or.inl ⟨hnz, rfl⟩⟩
      rw [minkF_succ_eq]; simp only [minkStep]; rw [hb, tbind_nonzero' hnz]
  bwd := fun {s gul tm rb} _ hb => by
    obtain ⟨n, h⟩ := hb
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    rcases tbind_eq_some h with ⟨y, hy, h1⟩ | ⟨hb', hnz⟩
    · obtain ⟨k, rfl⟩ := minkF_pos hy
      rw [minkF_slot1', tbind_zero, Option.some.injEq] at h1
      subst h1
      refine ⟨fun hn => absurd rfl (hn _), fun u r eu hr => ?_⟩
      cases eu
      obtain ⟨n2, e2⟩ := hr
      have e1' := minkF_le lib gul (Nat.le_max_left (k + 1) n2) tm s (C a1 a2) _ hy
      have e2' := minkF_le lib gul (Nat.le_max_right (k + 1) n2) tm (C y s) c _ e2
      exact ⟨max (k + 1) n2 + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']⟩
    · refine ⟨fun _ => ⟨m + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [hb', tbind_nonzero' hnz]⟩,
        fun u r eu _ => absurd eu (hnz u)⟩

/-- **`[8 b c]` with `b` an atom** crashes at once, as the atom `0` does. -/
theorem minkC7_eightAtom (lib : Lib) (P : Noun → Prop) (k : Nat) (c : Noun) :
    MinkC7 lib P (n3 (A 8) (A k) c) (A 0) c where
  fwd := fun {s gul n tm r} _ h => by
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := by
      cases m with
      | zero => simp [minkF, tbind] at h
      | succ j => exact ⟨j, rfl⟩
    rw [minkF_atom] at h
    simp only [tbind, Option.some.injEq] at h
    subst h
    exact ⟨j + 1 + 1, Nat.le_refl _, _, minkF_atom, Or.inl ⟨(fun _ e => by cases e), rfl⟩⟩
  bwd := fun {s gul tm rb} _ hb => by
    rw [mink_atom] at hb
    subst hb
    refine ⟨fun _ => ⟨2, ?_⟩, fun u r eu _ => by cases eu⟩
    rw [minkF_succ_eq]; simp only [minkStep]; rw [minkF_atom]; rfl

/-- **`[8 b c]` whose `b` returns `y` on every subject, the subject being
`d`**, is `[1 [y d]]`, then `c`. -/
theorem minkC7_eightL (lib : Lib) {P : Noun → Prop} {b c y d : Noun}
    (hb : ∀ x gul, P x → Mink lib gul [] x b (Tone.zero y) ∧ x = d) :
    MinkC7 lib P (n3 (A 8) b c) (quote (C y d)) c where
  fwd := fun {s gul n tm r} hs h => by
    obtain ⟨hby, rfl⟩ := hb s gul hs
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    rcases tbind_eq_some h with ⟨y', hy', h1⟩ | ⟨hb', hnz⟩
    · cases mink_det_zero hby hy'
      obtain ⟨k, rfl⟩ := minkF_pos hy'
      refine ⟨k + 1, by omega, Tone.zero (C y s), by rw [minkF_succ_eq]; rfl,
        Or.inr ⟨C y s, rfl, k + 1, by omega, h1⟩⟩
    · exact absurd (mink_det_zero hby hb') (hnz _)
  bwd := fun {s gul tm rb} hs hq => by
    obtain ⟨hby, rfl⟩ := hb s gul hs
    obtain ⟨n, h⟩ := hq
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [minkStep, Option.some.injEq] at h
    subst h
    refine ⟨fun hn => absurd rfl (hn _), fun u r eu hr => ?_⟩
    cases eu
    obtain ⟨n1, e1⟩ := hby
    obtain ⟨n2, e2⟩ := hr
    have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s b _ (mink_t_of_nil_zero tm e1)
    have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm (C y s) c _ e2
    exact ⟨max n1 n2 + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']⟩

/-- **`[9 a c]`** is `c`, then `[2 [0 1] [0 a]]` on its product. -/
theorem minkC7_nine (lib : Lib) (P : Noun → Prop) (axis : Nat) (c : Noun) :
    MinkC7 lib P (n3 (A 9) (A axis) c) c (n3 (A 2) (slot 1) (slot axis)) where
  fwd := fun {s gul n tm r} _ h => by
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    rcases tbind_eq_some h with ⟨core, hc, h1⟩ | ⟨hc, hnz⟩
    · obtain ⟨k, rfl⟩ := minkF_pos hc
      refine ⟨k + 1, by omega, _, hc, Or.inr ⟨core, rfl, k + 2, by omega, ?_⟩⟩
      rw [minkF_invoke]
      exact h1
    · exact ⟨m, by omega, r, hc, Or.inl ⟨hnz, rfl⟩⟩
  bwd := fun {s gul tm rb} _ hb => by
    obtain ⟨n1, e1⟩ := hb
    refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun u r eu hr => ?_⟩
    · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1, tbind_nonzero' hn]
    · subst eu
      obtain ⟨n2, e2⟩ := hr
      obtain ⟨k2, rfl⟩ := minkF_pos e2
      obtain ⟨k, rfl⟩ : ∃ k, k2 = k + 1 := by
        cases k2 with
        | zero => simp [minkF_succ_eq, minkStep, minkF, tbind] at e2
        | succ k => exact ⟨k, rfl⟩
      rw [minkF_invoke] at e2
      have e1' := minkF_le lib gul (Nat.le_max_left n1 (k + 1)) tm s c _ e1
      refine ⟨max n1 (k + 1) + 1, ?_⟩
      rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero]
      revert e2
      cases slot? axis u with
      | none => exact id
      | some arm => exact fun e2 => minkF_le lib gul (Nat.le_max_right n1 (k + 1)) tm u arm _ e2

/-! ## The products of the first formula -/

theorem img_eight {lib : Lib} {P : Noun → Prop} {a1 a2 u : Noun}
    (h : Img lib P (C (C a1 a2) (slot 1)) u) : Img8 lib P (C a1 a2) u := by
  obtain ⟨x, gul, hx, n, e⟩ := h
  obtain ⟨n', _, rh, eh, h1 | ⟨y, rfl, rt, et, h2 | ⟨z, rfl, e3⟩⟩⟩ := minkF_consG ⟨a1, a2, rfl⟩ e
  · exact absurd h1.2.symm (h1.1 u)
  · exact absurd h2.2.symm (h2.1 u)
  · obtain ⟨k, rfl⟩ := minkF_pos et
    rw [minkF_slot1', Option.some.injEq, Tone.zero.injEq] at et
    subst et
    cases e3
    exact ⟨x, y, gul, hx, ⟨k + 1, eh⟩, rfl⟩

theorem img_atom {lib : Lib} {P : Noun → Prop} {u : Noun} (h : Img lib P (A 0) u) : False := by
  obtain ⟨x, gul, _, hm⟩ := h
  cases mink_atom.mp hm

theorem img_eightL {lib : Lib} {P : Noun → Prop} {b y d u : Noun}
    (hb : ∀ x gul, P x → Mink lib gul [] x b (Tone.zero y) ∧ x = d) (h : Img lib P (quote (C y d)) u) :
    Img8 lib P b u := by
  obtain ⟨x, gul, hx, n, e⟩ := h
  obtain ⟨k, rfl⟩ := minkF_pos e
  rw [minkF_succ_eq] at e
  simp only [minkStep, Option.some.injEq, Tone.zero.injEq] at e
  subst e
  obtain ⟨hby, rfl⟩ := hb x gul hx
  exact ⟨x, y, gul, hx, hby, rfl⟩

/-! ## `UOKC` on fewer subjects -/

theorem RunOKGC.mono {lib : Lib} {P P' : Noun → Prop} {f : Noun} {goal : CGoal S} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKGC (Map := Map) lib P f goal g0 g1 nex) (h : ∀ s, P' s → P s) :
    RunOKGC lib P' f goal g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    fun s hs hf => R.nec s (h s hs) hf, R.ncond, R.econd,
    fun cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs =>
      R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr (h s hs),
    fun cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs =>
      R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr (h s hs)⟩

/-- **`UOKC` on fewer subjects.** -/
theorem UOKC.mono {lib : Lib} {env : CallEnv} {P P' : Noun → Prop} {f : Noun} {nm : Nomm}
    (U : UOKC (S := S) (Map := Map) lib env P f nm) (h : ∀ s, P' s → P s) :
    UOKC (S := S) (Map := Map) lib env P' f nm := by
  refine ⟨?_, U.clean, fun hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg hr =>
    (U.run hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg hr).mono h⟩
  rcases U.kind with ⟨u, M⟩ | k
  · exact Or.inl ⟨u, fun s hs => M s (h s hs)⟩
  · exact Or.inr k

/-! ## The `p` part when `b` is an atom -/

/-- **A nomm for an atom formula** is the crash `[0 0]` or a literal. -/
theorem annot_atom {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {k : Nat} {nm : Nomm}
    (h : Annot lib code P (A k) nm) : nm.pure = true := by
  generalize e : A k = f at h
  cases h <;> (try subst e) <;> simp_all [isBare, Nomm.pure]

/-- **A nomm for `[0 1]`** is call-free. -/
theorem annot_slot1_pure {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {nm : Nomm}
    (h : Annot lib code P (slot 1) nm) : nm.pure = true := by
  generalize e : slot 1 = f at h
  cases h <;> (try subst e) <;> simp_all [isBare, Nomm.pure]

/-- **The pair `[p r]` of `[8 b c]` with `b` an atom** meets `UOKC` for the
formula `0`: `p`, for an atom, crashes on every subject (`mink_pure`). -/
theorem uokc_atomPair {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv)
    {P : Noun → Prop} {k : Nat} {p r : Nomm} (hb : Annot lib code P (A k) p) (hr : r.pure = true)
    (hpu : (Nomm.cons p r).pure = true → UOK (S := S) (Map := Map) lib (Nomm.cons p r)) :
    UOKC (S := S) (Map := Map) lib env P (A 0) (Nomm.cons p r) := by
  have hp := annot_atom hb
  have hpr : (Nomm.cons p r).pure = true := by simp only [Nomm.pure, hp, hr, Bool.and_self]
  refine uokc_of_uok lib env (hpu hpr) (fun s hs gul tm t => ?_)
  have e0 : pureEval p s = none := by
    have := (mink_pure hok hp hb hs gul tm (Tone.two tm)).mp (mink_atom.mpr rfl)
    simp only [pureTone] at this
    revert this
    cases pureEval p s with
    | none => exact fun _ => rfl
    | some v => intro h; cases h
  rw [mink_atom, pureEval_cons, e0]
  rfl

end Comp
end SkaModel
end Formalization
