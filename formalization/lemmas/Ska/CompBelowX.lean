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

/-- The tail of `%3` and `%4`: a block whose terminator reads the fresh
register `arg`, then the run of the operand for it. -/
theorem keepX_tail {p : Nomm} (ih : KeepX S Map p) {b : Blob} {arg : Nat} {region : List Nat} {g g1 g2 : Gen Map}
    {o : Nat} {nex : NextL S} (hd : g.drop = false) (hb : BlobIn (· < g.re) b) (ha : arg < g.re)
    (hc : sixCount p ≤ 255) (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region g1 = some (nex, g2)) :
    KeepR g g2 nex (sixCount p) := by
  obtain ⟨k1, q1⟩ := keeps_emit hd hb h1
  exact (ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) (k1.dropF hd) ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ hc h).pre
    k1 ((KC.emit' _).keep _ _ _ h1) (Nat.le_refl _)

theorem keepX_four {p : Nomm} (ih : KeepX S Map p) : KeepX S Map (Nomm.n4 p) := by
  intro goal region g0 g1 nex hd hg hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  show KeepR g0 g1 nex (sixCount p)
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o, gc, h3, h⟩ := bind_some h
    have R := keepX_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      (show pro < gb.re by omega)) (by omega) hcp h3 h
    exact R.pre (k1.trans k2) (by rw [(KC.re').keep _ _ _ h2, (KC.re').keep _ _ _ h1]) (Nat.le_refl _)
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o', gc, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g0.re → x < gb.re := fun x hx => by omega
    have R := keepX_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      ⟨show pro < gb.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) hcp h3 h
    exact R.pre (k1.trans k2) (by rw [(KC.re').keep _ _ _ h2, (KC.re').keep _ _ _ h1]) (Nat.le_refl _)
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 h1
    have c1 := (kc_collapseLazyAtom _).keep _ _ _ h1
    obtain ⟨⟨pro, th'⟩, gb, h2, h⟩ := bind_some h
    have hp : Keeps ga gb ∧ pro < gb.re ∧ gb.cond = ga.cond := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨Keeps.refl _, r1 _ _ rfl, rfl⟩
      | none =>
        simp only at h2
        obtain ⟨r, g3, h3, h2⟩ := bind_some h2
        obtain ⟨e3, q3, k3⟩ := keeps_re h3
        have c3 := (KC.re').keep _ _ _ h3
        by_cases ht : th.args = []
        · rw [if_pos ht] at h2
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨k3, by omega, c3⟩
        · rw [if_neg ht] at h2; cases h2
    obtain ⟨k2, p2, c2⟩ := hp
    obtain ⟨arg, gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨o, gd, h4, h⟩ := bind_some h
    have R := keepX_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
        (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (jmpIn_jmp0 _ _)) (by omega) hcp h4 h
    exact R.pre (k1.trans (k2.trans k3)) (by rw [(KC.re').keep _ _ _ h3, c2, c1]) (Nat.le_refl _)

theorem keepX_three {p : Nomm} (ih : KeepX S Map p) : KeepX S Map (Nomm.n3 p) := by
  intro goal region g0 g1 nex hd hg hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  show KeepR g0 g1 nex (sixCount p)
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨⟨o0, o1⟩, ga, h1, h⟩ := bind_some h
    have k1 := keeps_doneBlocks hd h1
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    have R := keepX_tail ih ((k1.trans k2).dropF hd)
      (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show r < gb.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) hcp h3 h
    exact R.pre (k1.trans k2) (by rw [(KC.re').keep _ _ _ h2, kc_doneBlocks.keep _ _ _ h1]) (Nat.le_refl _)
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g0.re → x < gb.re := fun x hx => by omega
    have R := keepX_tail ih (k2.dropF hd)
      (blobIn_fin (f := Termin.clq r z o) ⟨show r < gb.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) hcp h3 h
    exact R.pre k2 ((KC.re').keep _ _ _ h2) (Nat.le_refl _)
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    dsimp only at h
    revert h; split
    · exact fun h => ih (goal := CGoal.next sur th) hd hg hcp h
    intro h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 h1
    have c1 := (kc_collapseLazyAtom _).keep _ _ _ h1
    rcases a with _ | ⟨r, o⟩
    · cases h
    simp only at h
    obtain ⟨⟨z, o'⟩, gb, h2, h⟩ := bind_some h
    have k2 := keeps_forl (k1.dropF hd) (r1 r o rfl) h2
    have c2 := (kc_forl _ _).keep _ _ _ h2
    obtain ⟨r', gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨oc, gd, h4, h⟩ := bind_some h
    have R := keepX_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show r' < gc.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) hcp h4 h
    exact R.pre (k1.trans (k2.trans k3)) (by rw [(KC.re').keep _ _ _ h3, c2, c1]) (Nat.le_refl _)

end Comp
end SkaModel
end Formalization
