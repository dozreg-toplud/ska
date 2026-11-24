import lemmas.Ska.CompBelowRun
import lemmas.Ska.CompFragX

/-!
# Fact (i5) over `FragX`, case by case

The induction over `FragX` (as `runX_clean`) for fact (i5), with the
invariant of `CompBelowRun.lean`: a run keeps every `BelowIn lo` (`Keeps`).
`KeepX nm`: every run of `runL nm` for a fork-free goal whose registers are
below `re`, from a state that does not drop, when `nm` has at most 255 `%6`,
keeps every `BelowIn lo`, returns a `next` whose registers (its sure need, the
needs of its lazy entries, its jump's arguments) are below the new `re`,
keeps `cond`, has at most `2 * sixCount nm` lazy entries, at labels allocated
in the run (`KeepR`).  The case lemmas (`keepX_frag`, `keepX_seven`,
`keepX_sevenFrom`, `keepX_four`, `keepX_three`) each take `KeepX` of the
parts; the induction itself waits for the cases `six`, `cons`, `five`, `ten`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The registers of a lazy need (its sure need and the needs of its
entries) are below `n`. -/
def LazyIn (n : Nat) (l : Lazy S) : Prop := NB n l.sure.ned ∧ ∀ e ∈ entries l, NB n e.2.sure.ned

/-- The registers of a `next` over lazy needs are below `n`. -/
def NextInL (n : Nat) (nex : NextL S) : Prop := LazyIn n nex.laz ∧ JmpIn (· < n) nex.th

/-- What the induction proves of one run. -/
structure KeepR (g0 g1 : Gen Map) (nex : NextL S) (n : Nat) : Prop where
  keeps : Keeps g0 g1
  out : NextInL g1.re nex
  cnd : g1.cond = g0.cond
  size : (entries nex.laz).length ≤ 2 * n
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo

/-- **Every run of `nm` for a fork-free goal keeps (i5).** -/
abbrev KeepX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    g0.drop = false → GoalIn g0.re goal → sixCount nm ≤ 255 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → KeepR g0 g1 nex (sixCount nm)

theorem KeepR.pre {g0 g g1 : Gen Map} {nex : NextL S} {n n' : Nat} (k : Keeps g0 g) (c : g.cond = g0.cond)
    (R : KeepR g g1 nex n) (hn : n ≤ n') : KeepR g0 g1 nex n' :=
  ⟨k.trans R.keeps, R.out, R.cnd.trans c, by have := R.size; omega,
    fun e he => ⟨Nat.le_trans k.bo (R.labs e he).1, (R.labs e he).2⟩⟩

/-- A run with a fork-free result. -/
theorem keepR_toL {g0 g1 : Gen Map} {n : Next S} (k : Keeps g0 g1) (o : NextIn g1.re n) (c : g1.cond = g0.cond)
    (m : Nat) : KeepR g0 g1 (Next.toL n) m :=
  ⟨k, ⟨⟨o.1, fun e he => by simp [Next.toL, entries_ofSure] at he⟩, o.2⟩, c,
    by simp [Next.toL, entries_ofSure], fun e he => by simp [Next.toL, entries_ofSure] at he⟩

/-! ## The cases -/

/-- **The leaves: every nomm of `Frag`**, through `run_keeps`. -/
theorem keepX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : KeepX S Map nm := by
  intro goal region g0 g1 nex hd hg _ h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k, o⟩ := run_keeps nm goal g0 g n hd hg hr
  exact keepR_toL k o ((kc_run nm goal).keep g0 n g hr) _

theorem keepX_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : KeepX S Map p) :
    KeepX S Map (Nomm.n7 p q) := by
  intro goal region g0 g1 nex hd hg hc h
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag (hq goal)] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := run_keeps q goal g0 g' n hd hg hr
  have R := ihp (goal := CGoal.next n.laz n.th) (k1.dropF hd) n1 (by simp only [sixCount] at hc; omega) h2
  exact R.pre k1 ((kc_run q goal).keep g0 n g' hr) (by simp only [sixCount]; omega)

theorem keepX_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : KeepX S Map q) :
    KeepX S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region g0 g1 nex hd hg hc h
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha h
  have R := ihq hd hg (by simp only [sixCount] at hc; omega) h1
  have E := fromL_ent axe _ _ hl
  refine ⟨R.keeps, ⟨⟨nb_fromSure (fromL_sure hl) R.out.1.1, fun e he => ?_⟩, R.out.2⟩, R.cnd, ?_, fun e he => ?_⟩
  · obtain ⟨l, hl', he'⟩ := E.mem_right he
    exact nb_fromSure (fromL_sure hl') (R.out.1.2 _ he')
  · simp only [sixCount]; rw [E.length_eq]; have := R.size; omega
  · obtain ⟨l, _, he'⟩ := E.mem_right he
    exact R.labs (e.1, l) he'

end Comp
end SkaModel
end Formalization
