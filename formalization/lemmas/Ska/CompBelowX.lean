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
in the run (`KeepR`).  The case lemmas (`keepX_frag`, `keepX_sixP`,
`keepX_sixN`, `keepX_four`, `keepX_three`, `keepX_seven`, `keepX_cons`,
`keepX_five`, `keepX_ten`, `keepX_sevenFrom`) each take `KeepX` of the parts,
and `runX_keeps` is the induction.  `runX_below`: fact (i5) on `FragX`;
`runX_okU`: the run of the top meets `RunOKU` and (i5).

The induction assumes that the run does not drop (`g0.drop = false`, kept by
every step: `Keeps.drop`), as the top run from `gen0` does, and at most 255
`%6`, so that no fork is big and `+lazy-shut` makes no proxy; then `cond` is
kept and `+sect` changes no block (`sect_spec`).
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

/-! ## `+copy` of two lazy needs, and the binary cases -/

theorem fork_in_entries {l : Lazy S} {e : ForkE S} (h : e ∈ l.fork) : e.1 ∈ entries l := by
  rcases l with ⟨s, f, b⟩
  simp only [entries, List.mem_append]
  exact Or.inr (fork_mem_entries h)

theorem bond_in_entries {l : Lazy S} {e : Nat × Lazy S} (h : e ∈ l.bond) : e ∈ entries l := by
  rcases l with ⟨s, f, b⟩
  simp only [entries, List.mem_append]
  exact Or.inl (bond_mem_entries h)

/-- **`+copy` of a lazy need into the result of a later run**: the entries
of the two lie apart (`mid`), so the copy is that of the sure needs with
the entries side by side (`copyL_apart_some`). -/
theorem keep_copyL {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S} {lo mid : Nat}
    (hd : g.drop = false) (h1 : NextInL g.re first) (h2 : LazyIn g.re second) (hlm : lo ≤ mid) (hmg : mid ≤ g.bo)
    (l1 : ∀ e ∈ entries first.laz, mid ≤ e.1 ∧ e.1 < g.bo) (l2 : ∀ e ∈ entries second, lo ≤ e.1 ∧ e.1 < mid)
    (h : copyL first second g = some (nex, g')) :
    Keeps g g' ∧ NextInL g'.re nex ∧ g'.cond = g.cond ∧
      (entries nex.laz).length = (entries first.laz).length + (entries second).length ∧
      ∀ e ∈ entries nex.laz, lo ≤ e.1 ∧ e.1 < g'.bo := by
  obtain ⟨n, hc, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := (l1 _ (fork_in_entries he)).1
      have b := (l2 _ (fork_in_entries he')).2
      omega)
    (fun e he e' he' => by
      have a := (l1 _ (bond_in_entries he)).1
      have b := (l2 _ (bond_in_entries he')).2
      omega) h
  obtain ⟨k, o⟩ := keeps_copy hd ⟨h1.1.1, h1.2⟩ h2.1 hc
  have P := entries_side_perm n.laz first.laz second
  refine ⟨k, ⟨⟨o.1, fun e he => ?_⟩, o.2⟩, (kc_copy _ _).keep _ _ _ hc, by rw [P.length_eq, List.length_append],
    fun e he => ?_⟩
  · rcases List.mem_append.mp (P.mem_iff.mp he) with a | a
    · exact (h1.1.2 e a).mono k.le
    · exact (h2.2 e a).mono k.le
  · rcases List.mem_append.mp (P.mem_iff.mp he) with a | a
    · have := l1 e a; have := k.bo; omega
    · have := l2 e a; have := k.bo; omega

/-- The two runs and the copy of cons, `%5` and `%10`: `q` (or `v`) first for
`nq`, then `p` for `np`, whose jump is that of the first result, then the
copy. -/
theorem keepX_binary {p q : Nomm} (ihp : KeepX S Map p) (ihq : KeepX S Map q) {region : List Nat}
    {g0 g1 g2 g3 : Gen Map} {nq np : Sure S} {th : Jmp} {nex2 nex1 nex : NextL S}
    (hd : g0.drop = false) (hc : sixCount p + sixCount q ≤ 255) (hnq : NB g0.re nq.ned) (hnp : NB g0.re np.ned)
    (hj : JmpIn (· < g0.re) th)
    (h2 : runL q (CGoalL.next (ofSure nq) th) region g0 = some (nex2, g1))
    (h3 : runL p (CGoalL.next (ofSure np) nex2.th) region g1 = some (nex1, g2))
    (h4 : copyL nex1 nex2.laz g2 = some (nex, g3)) : KeepR g0 g3 nex (sixCount p + sixCount q) := by
  have Rq := ihq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have d1 := Rq.keeps.dropF hd
  have Rp := ihp (goal := CGoal.next np nex2.th) d1 ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩ (by omega) h3
  have d2 := Rp.keeps.dropF d1
  obtain ⟨k, o, c, sz, lb⟩ := keep_copyL (lo := g0.bo) (mid := g1.bo) d2 Rp.out
    ⟨Rq.out.1.1.mono Rp.keeps.le, fun e he => (Rq.out.1.2 e he).mono Rp.keeps.le⟩ Rq.keeps.bo Rp.keeps.bo
    (fun e he => Rp.labs e he) (fun e he => Rq.labs e he) h4
  exact ⟨Rq.keeps.trans (Rp.keeps.trans k), o, c.trans (Rp.cnd.trans Rq.cnd),
    by rw [sz]; have := Rp.size; have := Rq.size; omega, lb⟩

theorem keepX_consBody {p q : Nomm} (ihp : KeepX S Map p) (ihq : KeepX S Map q) (hpp : p.pure = true)
    (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th)) (hc : sixCount p + sixCount q ≤ 255)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : KeepR g0 g1 nex (sixCount p + sixCount q) := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hg.1 hg.2 hs2
  have c2 := (kc_split _).keep _ _ _ hs2
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hqp, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  exact (keepX_binary ihp ihq (k2.dropF hd) hc nt (nh.mono (Nat.le_refl _)) (jmpIn_jmp0 _ _) h3 h4 hcp).pre k2 c2
    (Nat.le_refl _)

theorem keepX_cons {p q : Nomm} (ihp : KeepX S Map p) (ihq : KeepX S Map q) (hpp : p.pure = true)
    (hqp : q.pure = true) : KeepX S Map (Nomm.cons p q) := by
  intro goal region g0 g1 nex hd hg hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  show KeepR g0 g1 nex (sixCount p + sixCount q)
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at h
    rw [runL_cons_next] at h
    exact keepX_consBody ihp ihq hpp hqp hd hg hc' h
  | done =>
    simp only [CGoal.toL] at h
    rw [runL_cons_done] at h
    obtain ⟨r, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o, gb, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keeps_emit (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show r < ga.re by omega)) h2
    rw [runL_cons_next] at h
    exact (keepX_consBody (sur := lazyReg r) ihp ihq hpp hqp ((k1.trans k2).dropF hd)
      ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ hc' h).pre (k1.trans k2)
      (by rw [(KC.emit' _).keep _ _ _ h2, (KC.re').keep _ _ _ h1]) (Nat.le_refl _)
  | pick z o =>
    simp only [CGoal.toL] at h
    rw [runL_cons_pick] at h
    obtain ⟨o', ga, h1, h⟩ := bind_some h
    obtain ⟨k1, _⟩ := keeps_emit hd (blobIn_fin (f := Termin.bom Option.none) trivial) h1
    obtain ⟨nex2, gb, h3, h⟩ := bind_some h
    obtain ⟨nex2', gb', hp2, h⟩ := bind_some h
    rw [pastL_pure _ _ hpp, pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nex1, gc, h4, h⟩ := bind_some h
    exact (keepX_binary (nq := Sure.bunt) (np := Sure.bunt) ihp ihq (k1.dropF hd) hc' (nb_none _) (nb_none _)
      (jmpIn_jmp0 _ _) h3 h4 h).pre k1 ((KC.emit' _).keep _ _ _ h1) (Nat.le_refl _)

theorem keeps_n5Pre {rp rq : Nat} {goal : CGoal S} {g g' : Gen Map} {o : Nat} (hd : g.drop = false)
    (hg : GoalIn g.re goal) (hp : rp < g.re) (hq : rq < g.re) (h : n5Pre rp rq goal g = some (o, g')) :
    Keeps g g' := by
  have kk : ∀ x, x < g.re → x < g.re := fun _ e => e
  cases goal with
  | pick z o =>
    exact (keeps_emit hd (blobIn_fin (f := Termin.eqq rp rq z o) ⟨hp, hq, hg.1, hg.2⟩) h).1
  | done =>
    simp only [n5Pre] at h
    obtain ⟨⟨o0, o1⟩, g4, h4, h3⟩ := bind_some h
    have k4 := keeps_doneBlocks hd h4
    have l4 := k4.le
    exact k4.trans (keeps_emit (k4.dropF hd) (blobIn_fin (f := Termin.eqq rp rq (jmp0 o0) (jmp0 o1))
      ⟨show rp < g4.re by omega, show rq < g4.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1
  | next laz th =>
    simp only [n5Pre] at h
    obtain ⟨a, g4, h4, h3⟩ := bind_some h
    obtain ⟨k4, r4⟩ := keeps_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h4
    have l4 := k4.le
    cases a with
    | none =>
      simp only at h3
      by_cases ht : th.args = []
      · rw [if_pos ht] at h3
        exact k4.trans (keeps_emit (k4.dropF hd) (blobIn_one (p := Pole.equ rp rq) (f := Termin.hop (jmp0 th.there))
          (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
          (jmpIn_jmp0 _ _)) h3).1
      · rw [if_neg ht] at h3; cases h3
    | some x =>
      obtain ⟨r, o⟩ := x
      simp only at h3
      obtain ⟨⟨z, o'⟩, g5, h5, h3⟩ := bind_some h3
      have k5 := keeps_forl (k4.dropF hd) (r4 r o rfl) h5
      have l5 := k5.le
      exact k4.trans (k5.trans (keeps_emit ((k4.trans k5).dropF hd) (blobIn_fin (f := Termin.eqq rp rq (jmp0 z) (jmp0 o'))
        ⟨show rp < g5.re by omega, show rq < g5.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1)

theorem keepX_five {p q : Nomm} (ihp : KeepX S Map p) (ihq : KeepX S Map q) (hpp : p.pure = true) :
    KeepX S Map (Nomm.n5 p q) := by
  intro goal region g0 g1 nex hd hg hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  show KeepR g0 g1 nex (sixCount p + sixCount q)
  rw [runL_n5_toL] at h
  obtain ⟨rp, ga, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨rq, gb, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  obtain ⟨o, gc, h3, h⟩ := bind_some h
  have k3 := keeps_n5Pre ((k1.trans k2).dropF hd) (hg.mono (by omega)) (by omega) (by omega) h3
  have c3 := (kc_n5Pre _ _ _).keep _ _ _ h3
  obtain ⟨nexq, gd, h4, h⟩ := bind_some h
  obtain ⟨nexq', gd', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, ge, h5, h⟩ := bind_some h
  have l3 := k3.le
  exact (keepX_binary (nq := lazyReg rq) (np := lazyReg rp) ihp ihq ((k1.trans (k2.trans k3)).dropF hd) hc'
    (nb_this (by omega)) (nb_this (by omega)) (jmpIn_jmp0 _ _) h4 h5 h).pre (k1.trans (k2.trans k3))
    (by rw [c3, (KC.re').keep _ _ _ h2, (KC.re').keep _ _ _ h1]) (Nat.le_refl _)

theorem keepX_ten {a : Nat} {v q : Nomm} (ihv : KeepX S Map v) (ihq : KeepX S Map q) (hvp : v.pure = true)
    (hqp : q.pure = true) : KeepX S Map (Nomm.n10 a v q) := by
  intro goal region g0 g1 nex hd hg hc h
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  show KeepR g0 g1 nex (sixCount v + sixCount q)
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨n, gs'⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := keeps_simpleNext hd hg hs'
  have c1 := (kc_simpleNext _).keep _ _ _ hs'
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [show (Next.toL n : NextL S) = ⟨ofSure n.laz, n.th⟩ from rfl, intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nd, nr⟩ := keeps_into (k1.dropF hd) n1 hs2
  have c2 := (kc_into _ _).keep _ _ _ hs2
  obtain ⟨nexR, g2', hpr, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hvp, pure_apply] at hpr
  simp only [Option.some.injEq, Prod.mk.injEq] at hpr
  obtain ⟨rfl, rfl⟩ := hpr
  obtain ⟨nexDon, g3, h3, h⟩ := bind_some h
  obtain ⟨nexDon', g3', hpd, h⟩ := bind_some h
  rw [pastL_pure _ _ hqp, pure_apply] at hpd
  simp only [Option.some.injEq, Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  obtain ⟨nexRec, g4, h4, hcp⟩ := bind_some h
  have R := keepX_binary ihq ihv ((k1.trans k2).dropF hd) hc' nd nr (jmpIn_jmp0 _ _) h3 h4 hcp
  exact R.pre (k1.trans k2) (by rw [c2, c1]) (by omega)

/-! ## `%6` -/

theorem keeps_emitted {g : Gen Map} {b : Blob} (hd : g.drop = false) (hb : BlobIn (· < g.re) b) :
    Keeps g (g.emitted b) :=
  ⟨fun _ hl => belowIn_emitted hl hd hb, Nat.le_refl _, rfl, Nat.le_succ _⟩

theorem keeps_tagged (g : Gen Map) (o : Nat) (region : List Nat) : Keeps g (g.tagged o region) := by
  refine ⟨fun lo hl => ?_, by simp, by simp, by simp⟩
  intro o' b l u hb
  rw [tagged_blocks] at hb
  rw [tagged_bo] at u
  rw [tagged_re]
  exact hl o' b l u hb

theorem keeps_sixGenL {g2 : Gen Map} {t0 t1 : Jmp} {region : List Nat} (hd : g2.drop = false)
    (h0 : JmpIn (· < g2.re) t0) (h1 : JmpIn (· < g2.re) t1) :
    Keeps g2 (sixGenL g2 t0 t1 region) ∧ (sixGenL g2 t0 t1 region).cond = g2.cond :=
  ⟨(keeps_emitted hd (blobIn_fin (f := Termin.hop t0) h0)).trans
    ((keeps_emitted (g := g2.emitted ⟨[], [], Termin.hop t0⟩) (b := ⟨[], [], Termin.hop t1⟩) hd (blobIn_fin (f := Termin.hop t1) h1)).trans
      ((keeps_tagged _ _ _).trans (keeps_tagged _ _ _))),
    by simp [sixGenL, tagged_cond, emitted_cond]⟩

/-- The end of `%6`: the copy of the fork of the branches' needs at the two
lazy blocks `y` and `n` into the need of the test. -/
theorem keepX_sixEnd {g0 g1 g2 g3 g4 g5 : Gen Map} {xc x0 x1 nex : NextL S} {y n : Nat} {sc sa sb : Nat}
    (hd : g0.drop = false) (Rb : KeepR g0 g1 x1 sb) (Ra : KeepR g1 g2 x0 sa) (kG : Keeps g2 g3) (cG : g3.cond = g2.cond)
    (Rc : KeepR g3 g4 xc sc) (hy : g2.bo ≤ y) (hn : y + 1 = n) (hn3 : n + 1 = g3.bo)
    (h : copyL xc (mk (Sure.bunt : Sure S) [((y, x0.laz), (n, x1.laz))] []) g4 = some (nex, g5)) :
    KeepR g0 g5 nex (sc + sa + sb + 1) := by
  have l3 : g2.re ≤ g4.re := Nat.le_trans kG.le Rc.keeps.le
  have l1 : g1.re ≤ g4.re := Nat.le_trans Ra.keeps.le l3
  have b1 := Rb.keeps.bo; have b2 := Ra.keeps.bo; have b3 := kG.bo; have b4 := Rc.keeps.bo
  have hL : LazyIn g4.re (mk (Sure.bunt : Sure S) [((y, x0.laz), (n, x1.laz))] []) := by
    refine ⟨nb_none _, fun e he => ?_⟩
    rw [entries_six] at he
    rcases List.mem_append.mp he with he | he <;> rcases List.mem_cons.mp he with e' | he
    · rw [e']; exact Ra.out.1.1.mono l3
    · exact (Ra.out.1.2 e he).mono l3
    · rw [e']; exact Rb.out.1.1.mono l1
    · exact (Rb.out.1.2 e he).mono l1
  obtain ⟨k, o, c, sz, lb⟩ := keep_copyL (lo := g0.bo) (mid := g3.bo) (Rc.keeps.dropF (kG.dropF
    (Ra.keeps.dropF (Rb.keeps.dropF hd)))) Rc.out hL (by omega) b4 (fun e he => Rc.labs e he) (fun e he => by
      rw [entries_six] at he
      rcases List.mem_append.mp he with he | he <;> rcases List.mem_cons.mp he with e' | he
      · rw [e']; exact ⟨by omega, by omega⟩
      · have := Ra.labs e he; exact ⟨by omega, by omega⟩
      · rw [e']; exact ⟨by omega, by omega⟩
      · have := Rb.labs e he; exact ⟨by omega, by omega⟩) h
  refine ⟨Rb.keeps.trans (Ra.keeps.trans (kG.trans (Rc.keeps.trans k))), o,
    c.trans (Rc.cnd.trans (cG.trans (Ra.cnd.trans Rb.cnd))), ?_, lb⟩
  rw [sz, entries_six]
  simp only [List.length_append, List.length_cons]
  have := Rc.size; have := Ra.size; have := Rb.size; omega

theorem keeps_same {g g' : Gen Map} (h : SameBlocks g g') : Keeps g g' := by
  obtain ⟨hre, hbo, _, hdr, _, _, hbl⟩ := h
  refine ⟨fun lo hl o b l u hb => ?_, Nat.le_of_eq hre.symm, hdr, Nat.le_of_eq hbo.symm⟩
  rw [hbl] at hb; rw [hbo] at u; rw [hre]
  exact hl o b l u hb

theorem jmpIn_flatten {P : Nat → Prop} {ned : Need} {o : Nat} (h : ∀ x, NMem ned x → P x) :
    JmpIn P ⟨(flattenNeed ned).map some, o⟩ := fun x hx => by
  obtain ⟨y, hy, e⟩ := List.mem_map.mp hx
  have e' : y = x := Option.some.inj e
  rw [← e']
  exact h y ((mem_flatten ned y).mp hy)

/-- **`%6` for `%done` or `%pick`.** -/
theorem keepX_sixP {c a b : Nomm} (hcp : c.pure = true) (ihc : KeepX S Map c) (iha : KeepX S Map a)
    (ihb : KeepX S Map b) {goal : CGoal S} (hg' : NotNext goal) {region : List Nat} {g0 g4 : Gen Map}
    {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re goal)
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g4)) :
    KeepR g0 g4 nex (sixCount c + sixCount a + sixCount b + 1) := by
  rw [runL_n6_body _ _ _ hg'] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  have Rb := ihb hd hg (by omega) h1
  have d1 := Rb.keeps.dropF hd
  have Ra := iha d1 (hg.mono Rb.keeps.le) (by omega) h2
  have d2 := Ra.keeps.dropF d1
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have Rc := ihc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2)
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ (by omega) h3
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  exact keepX_sixEnd hd Rb Ra kG cG Rc (Nat.le_refl _) rfl (by simp) (hrest hbig)

/-- **`%6` for a fork-free `%next`**: `+fork-sure`, the branches in a new
region, `+sect` (which changes no block, as the branches keep `cond`), the
test for `%pick`. -/
theorem keepX_sixN {c a b : Nomm} (hcp : c.pure = true) (ihc : KeepX S Map c) (iha : KeepX S Map a)
    (ihb : KeepX S Map b) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th))
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g9)) :
    KeepR g0 g9 nex (sixCount c + sixCount a + sixCount b + 1) := by
  simp only [CGoal.toL] at h
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
  obtain ⟨_, _, _, _, _, _, _, hreg, hle, hbo, hdrop, hcond, _, hb0, hb1, hb2, hold⟩ := forkSure_spec hF hd
  have kF : Keeps g0 gF := by
    refine ⟨fun lo hl o b' l u hb' => ?_, hle, hdrop, by omega⟩
    by_cases h0 : o < g0.bo
    · rw [hold o h0] at hb'
      exact (hl o b' l h0 hb').mono fun _ e => Nat.lt_of_lt_of_le e hle
    by_cases e0 : o = g0.bo
    · rw [e0, hb0] at hb'; cases hb'
      exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => (hreg x (Or.inl hx)).2)
    by_cases e1 : o = g0.bo + 1
    · rw [e1, hb1] at hb'; cases hb'
      exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => (hreg x (Or.inr hx)).2)
    by_cases e2 : o = g0.bo + 2
    · rw [e2, hb2] at hb'; cases hb'
      exact ⟨fun x hx => Nat.lt_of_lt_of_le (hg.1 x ((mem_flatten _ x).mp hx)) hle, RegsIn.nil _, jmpIn_jmp0 _ _⟩
    · omega
  have kI : Keeps gF { gF with id := gF.id + 1 } := ⟨fun _ hl => hl, Nat.le_refl _, rfl, Nat.le_refl _⟩
  have dF := kF.dropF hd
  have Rb0 := ihb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩ (by omega) hR
  have Rb := Rb0.pre (kF.trans kI) hcond (Nat.le_refl _)
  have d1 := Rb.keeps.dropF hd
  have lR : gF.re ≤ gR.re := Rb0.keeps.le
  have Ra := iha (goal := CGoal.next s0 (jmp0 g0.bo)) d1
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩ (by omega) hQ
  have d2 := Ra.keeps.dropF d1
  have cR : gR.cond = gF.cond := Rb0.cnd
  rw [cR] at hS
  obtain ⟨ey, en, _, _, el, hsb⟩ := sect_spec d2 (Ra.cnd.trans cR) hS
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := gF.id :: region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have kS := kG.trans (keeps_same hsb)
  have cS : gS.cond = gQ.cond := hsb.2.2.2.2.2.1.trans cG
  have bS : gS.bo = gQ.bo + 2 := by rw [hsb.2.1]; simp
  have Rc := ihc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    (by omega) hC
  subst el
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  subst ey en
  exact keepX_sixEnd hd Rb Ra kS cS Rc (by omega) (by omega) (by omega) (hrest hbig)

/-! ## The induction -/

/-- **On `FragX` every run for a fork-free goal whose registers are below
`re`, from a state that does not drop, keeps (i5)** (with the bounds of
`KeepR`), when the nomm has at most 255 `%6`. -/
theorem runX_keeps {nm : Nomm} (hf : FragX (S := S) nm) : KeepX S Map nm := by
  induction hf with
  | frag hf => exact keepX_frag hf
  | @six c a b hc' _ _ ihc iha ihb =>
    have hcp := fragX_pure hc'
    intro goal region g0 g1 nex hd hg hc h
    show KeepR g0 g1 nex (sixCount c + sixCount a + sixCount b + 1)
    have hc'' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hc
    cases goal with
    | next sur th => exact keepX_sixN hcp ihc iha ihb hd hg hc'' h
    | done => exact keepX_sixP (goal := CGoal.done) hcp ihc iha ihb trivial hd hg hc'' h
    | pick z o => exact keepX_sixP (goal := CGoal.pick z o) hcp ihc iha ihb trivial hd hg hc'' h
  | four _ ih => exact keepX_four ih
  | three _ ih => exact keepX_three ih
  | seven hq _ ih => exact keepX_seven hq ih
  | cons hp hq ihp ihq => exact keepX_cons ihp ihq (fragX_pure hp) (fragX_pure hq)
  | five hp _ ihp ihq => exact keepX_five ihp ihq (fragX_pure hp)
  | ten hv hq ihv ihq => exact keepX_ten ihv ihq (fragX_pure hv) (fragX_pure hq)
  | sevenFrom ha _ ihq => exact keepX_sevenFrom ha ihq

/-- **Fact (i5) on `FragX`**: every run of a nomm of `FragX` with at most 255
`%6` for a fork-free goal whose registers are below `re`, from a state that
does not drop, meets `BelowIn g0.bo g1`. -/
theorem runX_below {nm : Nomm} (hf : FragX (S := S) nm) {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re goal) (hc : sixCount nm ≤ 255)
    (h : runL nm (CGoal.toL goal) region g0 = some (nex, g1)) : BelowIn g0.bo g1 :=
  (runX_keeps hf hd hg hc h).keeps.bel _ (belowIn_start g0)

/-- **The run of the top for `%done` from `gen0` on `FragX` meets `RunOKU`
and fact (i5)**, so `RunOKU.semW` and `RunOKU.semF` apply to it. -/
theorem runX_okU (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) (hcount : sixCount nm ≤ 255) {region : List Nat}
    {g1 : Gen Map} {nex : NextL S} (h : runL nm (CGoal.toL (CGoal.done : CGoal S)) region (gen0 : Gen Map) = some (nex, g1)) :
    RunOKU lib nm CGoal.done gen0 g1 nex ∧ BelowIn (gen0 : Gen Map).bo g1 :=
  ⟨((runX_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h).toU gen0_cond_none,
    runX_below (goal := CGoal.done) hf rfl trivial hcount h⟩

end Comp
end SkaModel
end Formalization
