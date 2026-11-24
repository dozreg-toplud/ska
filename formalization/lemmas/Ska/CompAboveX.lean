import lemmas.Ska.CompAboveRun
import lemmas.Ska.CompCollapseThree

/-!
# The lower bound over `FragX`, and `AboveX` of every nomm of `FragX`

The induction over `FragX` of `CompBelowX.lean` with the bound of
`CompAboveRun.lean` (README Gaps 12.2).  `KeepXA nm`: every run of `runL nm`
for a fork-free goal whose registers are below `re` and at least `m`, with
`m ≤ re`, from a state that does not drop, when `nm` has at most 255 `%6`,
keeps every `AboveIn m lo` and returns a `next` whose registers (its sure
need, the needs of its lazy entries, its jump's arguments) are at least `m`
(`KeepRA`).  The structural facts the cases need (the labels of the
entries, which make the copy of two lazy needs that of their sure needs, the
number of entries, `cond` kept) come from `runX_keeps`, so the case lemmas
take `KeepX` of the parts beside `KeepXA`.

* The cases `keepXA_frag`, `keepXA_seven`, `keepXA_sevenFrom`,
  `keepXA_four`, `keepXA_three`, `keepXA_cons`, `keepXA_five`, `keepXA_ten`
  (through `keepXA_binary` and `keepA_copyL`), `keepXA_sixP` and
  `keepXA_sixN` (`%6` under `%done`, `%pick` and a fork-free `%next`);
  `runX_keepsA`, the induction; `runX_above`.
* `aboveX_of_fragX`: every nomm of `FragX` meets `AboveX`, so the top
  theorems for `[7 [4 p] q]` and `[7 [3 p] q]` need no `AboveX`
  (`finishLF_bellContract74X`, `finishLF_bellContract73X`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The registers of a lazy need (its sure need and the needs of its
entries) are at least `m`. -/
def LazyA (m : Nat) (l : Lazy S) : Prop := NA m l.sure.ned ∧ ∀ e ∈ entries l, NA m e.2.sure.ned

/-- The registers of a `next` over lazy needs are at least `m`. -/
def NextAL (m : Nat) (nex : NextL S) : Prop := LazyA m nex.laz ∧ JmpIn (m ≤ ·) nex.th

/-- What the induction proves of one run. -/
structure KeepRA (m : Nat) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  keeps : KeepsA m g0 g1
  out : NextAL m nex

/-- **Every run of `nm` for a fork-free goal keeps the lower bound `m`.** -/
abbrev KeepXA (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {m : Nat} {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    g0.drop = false → GoalIn g0.re goal → GoalA m goal → m ≤ g0.re → sixCount nm ≤ 255 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → KeepRA m g0 g1 nex

theorem KeepRA.pre {m : Nat} {g0 g g1 : Gen Map} {nex : NextL S} (k : KeepsA m g0 g) (R : KeepRA m g g1 nex) :
    KeepRA m g0 g1 nex :=
  ⟨k.trans R.keeps, R.out⟩

theorem keepRA_toL {m : Nat} {g0 g1 : Gen Map} {n : Next S} (k : KeepsA m g0 g1) (o : NextA m n) :
    KeepRA m g0 g1 (Next.toL n) :=
  ⟨k, ⟨⟨o.1, fun e he => by simp [Next.toL, entries_ofSure] at he⟩, o.2⟩⟩

/-! ## The cases -/

theorem keepXA_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : KeepXA S Map nm := by
  intro m goal region g0 g1 nex hd _ hg hm _ h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k, o⟩ := run_keepsA m nm goal g0 g n hd hg hm hr
  exact keepRA_toL k o

theorem keepXA_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : KeepXA S Map p) :
    KeepXA S Map (Nomm.n7 p q) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag (hq goal)] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨_, n1⟩ := run_keeps q goal g0 g' n hd hgi hr
  obtain ⟨a1, m1⟩ := run_keepsA m q goal g0 g' n hd hg hm hr
  have R := ihp (goal := CGoal.next n.laz n.th) (a1.dropF hd) n1 m1 (Nat.le_trans hm a1.le)
    (by simp only [sixCount] at hc; omega) h2
  exact R.pre a1

theorem keepXA_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : KeepXA S Map q) :
    KeepXA S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha h
  have R := ihq hd hgi hg hm (by simp only [sixCount] at hc; omega) h1
  have E := fromL_ent axe _ _ hl
  refine ⟨R.keeps, ⟨⟨na_fromSure (fromL_sure hl) R.out.1.1, fun e he => ?_⟩, R.out.2⟩⟩
  obtain ⟨l, hl', he'⟩ := E.mem_right he
  exact na_fromSure (fromL_sure hl') (R.out.1.2 _ he')

/-- The tail of `%3` and `%4`: a block whose terminator reads the fresh
register `arg`, then the run of the operand for it. -/
theorem keepXA_tail {m : Nat} {p : Nomm} (ih : KeepXA S Map p) {b : Blob} {arg : Nat} {region : List Nat}
    {g g1 g2 : Gen Map} {o : Nat} {nex : NextL S} (hd : g.drop = false) (hb : BlobIn (m ≤ ·) b) (ha : arg < g.re)
    (haA : m ≤ arg) (hm : m ≤ g.re) (hc : sixCount p ≤ 255) (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region g1 = some (nex, g2)) :
    KeepRA m g g2 nex := by
  obtain ⟨k1, q1⟩ := keepsA_emit hd hb h1
  exact (ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) (k1.dropF hd) ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩
    ⟨na_this haA, jmpIn_jmp0 _ _⟩ (by omega) hc h).pre k1

theorem keepXA_four {p : Nomm} (ih : KeepXA S Map p) : KeepXA S Map (Nomm.n4 p) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
    obtain ⟨o, gc, h3, h⟩ := bind_some h
    exact (keepXA_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      (show m ≤ pro by omega)) (by omega) (by omega) (by omega) hcp h3 h).pre (k1.trans k2)
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
    obtain ⟨o', gc, h3, h⟩ := bind_some h
    exact (keepXA_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      ⟨show m ≤ pro by omega, hg.1, hg.2⟩) (by omega) (by omega) (by omega) hcp h3 h).pre (k1.trans k2)
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keepsA_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 hm h1
    obtain ⟨⟨pro, th'⟩, gb, h2, h⟩ := bind_some h
    have hp : KeepsA m ga gb ∧ m ≤ pro := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨KeepsA.refl _ _, r1 _ _ rfl⟩
      | none =>
        simp only at h2
        obtain ⟨r, g3, h3, h2⟩ := bind_some h2
        obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
        by_cases ht : th.args = []
        · rw [if_pos ht] at h2
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨k3, by have := k1.le; omega⟩
        · rw [if_neg ht] at h2; cases h2
    obtain ⟨k2, p2⟩ := hp
    obtain ⟨arg, gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
    obtain ⟨o, gd, h4, h⟩ := bind_some h
    have l12 := (k1.trans k2).le
    exact (keepXA_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
        (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (jmpIn_jmp0 _ _)) (by omega) (by omega) (by omega) hcp h4 h).pre (k1.trans (k2.trans k3))

theorem keepXA_three {p : Nomm} (ih : KeepXA S Map p) : KeepXA S Map (Nomm.n3 p) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨⟨o0, o1⟩, ga, h1, h⟩ := bind_some h
    have k1 := keepsA_doneBlocks (m := m) hd hm h1
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    have l1 := k1.le
    exact (keepXA_tail ih ((k1.trans k2).dropF hd)
      (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show m ≤ r by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) (by omega) (by omega) hcp h3 h).pre (k1.trans k2)
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    exact (keepXA_tail ih (k2.dropF hd)
      (blobIn_fin (f := Termin.clq r z o) ⟨show m ≤ r by omega, hg.1, hg.2⟩) (by omega) (by omega) (by omega)
      hcp h3 h).pre k2
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    dsimp only at h
    revert h; split
    · exact fun h => ih (goal := CGoal.next sur th) hd hgi hg hm hcp h
    intro h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keepsA_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 hm h1
    rcases a with _ | ⟨r, o⟩
    · cases h
    simp only at h
    obtain ⟨⟨z, o'⟩, gb, h2, h⟩ := bind_some h
    have k2 := keepsA_forl (k1.dropF hd) (r1 r o rfl) (Nat.le_trans hm k1.le) h2
    obtain ⟨r', gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
    obtain ⟨oc, gd, h4, h⟩ := bind_some h
    have l12 := (k1.trans k2).le
    exact (keepXA_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show m ≤ r' by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) (by omega) (by omega) hcp h4 h).pre (k1.trans (k2.trans k3))

/-! ## `+copy` of two lazy needs, and the binary cases -/

/-- **`+copy` of a lazy need into the result of a later run**, whose
entries lie apart (`copyL_apart_some`). -/
theorem keepA_copyL {m : Nat} {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S} {lo mid : Nat}
    (hd : g.drop = false) (h1 : NextAL m first) (h2 : LazyA m second) (hm : m ≤ g.re)
    (l1 : ∀ e ∈ entries first.laz, mid ≤ e.1 ∧ e.1 < g.bo) (l2 : ∀ e ∈ entries second, lo ≤ e.1 ∧ e.1 < mid)
    (h : copyL first second g = some (nex, g')) : KeepsA m g g' ∧ NextAL m nex := by
  obtain ⟨n, hc, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := (l1 _ (fork_in_entries he)).1
      have b := (l2 _ (fork_in_entries he')).2
      omega)
    (fun e he e' he' => by
      have a := (l1 _ (bond_in_entries he)).1
      have b := (l2 _ (bond_in_entries he')).2
      omega) h
  obtain ⟨k, o⟩ := keepsA_copy hd ⟨h1.1.1, h1.2⟩ h2.1 hm hc
  have P := entries_side_perm n.laz first.laz second
  refine ⟨k, ⟨⟨o.1, fun e he => ?_⟩, o.2⟩⟩
  rcases List.mem_append.mp (P.mem_iff.mp he) with a | a
  · exact h1.1.2 e a
  · exact h2.2 e a

/-- The two runs and the copy of cons, `%5` and `%10`. -/
theorem keepXA_binary {m : Nat} {p q : Nomm} (ihp : KeepXA S Map p) (ihq : KeepXA S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) {region : List Nat} {g0 g1 g2 g3 : Gen Map} {nq np : Sure S} {th : Jmp}
    {nex2 nex1 nex : NextL S} (hd : g0.drop = false) (hc : sixCount p + sixCount q ≤ 255)
    (hnq : NB g0.re nq.ned) (hnp : NB g0.re np.ned) (hj : JmpIn (· < g0.re) th)
    (hnqA : NA m nq.ned) (hnpA : NA m np.ned) (hjA : JmpIn (m ≤ ·) th) (hm : m ≤ g0.re)
    (h2 : runL q (CGoalL.next (ofSure nq) th) region g0 = some (nex2, g1))
    (h3 : runL p (CGoalL.next (ofSure np) nex2.th) region g1 = some (nex1, g2))
    (h4 : copyL nex1 nex2.laz g2 = some (nex, g3)) : KeepRA m g0 g3 nex := by
  have Rq := kq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have Aq := ihq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ ⟨hnqA, hjA⟩ hm (by omega) h2
  have d1 := Rq.keeps.dropF hd
  have Rp := kp (goal := CGoal.next np nex2.th) d1 ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩ (by omega) h3
  have Ap := ihp (goal := CGoal.next np nex2.th) d1 ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩ ⟨hnpA, Aq.out.2⟩
    (Nat.le_trans hm Rq.keeps.le) (by omega) h3
  have d2 := Rp.keeps.dropF d1
  obtain ⟨k, o⟩ := keepA_copyL (lo := g0.bo) (mid := g1.bo) d2 Ap.out Aq.out.1
    (Nat.le_trans hm (Nat.le_trans Rq.keeps.le Rp.keeps.le)) (fun e he => Rp.labs e he) (fun e he => Rq.labs e he) h4
  exact ⟨Aq.keeps.trans (Ap.keeps.trans k), o⟩

theorem keepXA_consBody {m : Nat} {p q : Nomm} (ihp : KeepXA S Map p) (ihq : KeepXA S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hd : g0.drop = false) (hgi : GoalIn g0.re (CGoal.next sur th))
    (hg : GoalA m (CGoal.next sur th)) (hm : m ≤ g0.re) (hc : sixCount p + sixCount q ≤ 255)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : KeepRA m g0 g1 nex := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hgi.1 hgi.2 hs2
  obtain ⟨a2, nhA, ntA⟩ := keepsA_split hd hg.1 hg.2 hm hs2
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
  exact (keepXA_binary ihp ihq kp kq (k2.dropF hd) hc nt nh (jmpIn_jmp0 _ _) ntA nhA (jmpIn_jmp0 _ _)
    (Nat.le_trans hm a2.le) h3 h4 hcp).pre a2

theorem keepXA_cons {p q : Nomm} (ihp : KeepXA S Map p) (ihq : KeepXA S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true) : KeepXA S Map (Nomm.cons p q) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at h
    rw [runL_cons_next] at h
    exact keepXA_consBody ihp ihq kp kq hpp hqp hd hgi hg hm hc' h
  | done =>
    simp only [CGoal.toL] at h
    rw [runL_cons_done] at h
    obtain ⟨r, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨o, gb, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keepsA_emit (m := m) (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show m ≤ r by omega)) h2
    rw [runL_cons_next] at h
    exact (keepXA_consBody (sur := lazyReg r) ihp ihq kp kq hpp hqp ((k1.trans k2).dropF hd)
      ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ ⟨na_this (by omega), jmpIn_jmp0 _ _⟩ (by omega) hc' h).pre (k1.trans k2)
  | pick z o =>
    simp only [CGoal.toL] at h
    rw [runL_cons_pick] at h
    obtain ⟨o', ga, h1, h⟩ := bind_some h
    obtain ⟨k1, _⟩ := keepsA_emit (m := m) hd (blobIn_fin (f := Termin.bom Option.none) trivial) h1
    obtain ⟨nex2, gb, h3, h⟩ := bind_some h
    obtain ⟨nex2', gb', hp2, h⟩ := bind_some h
    rw [pastL_pure _ _ hpp, pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nex1, gc, h4, h⟩ := bind_some h
    exact (keepXA_binary (nq := Sure.bunt) (np := Sure.bunt) ihp ihq kp kq (k1.dropF hd) hc' (nb_none _) (nb_none _)
      (jmpIn_jmp0 _ _) (na_none _) (na_none _) (jmpIn_jmp0 _ _) (Nat.le_trans hm k1.le) h3 h4 h).pre k1

theorem keepsA_n5Pre {m rp rq : Nat} {goal : CGoal S} {g g' : Gen Map} {o : Nat} (hd : g.drop = false)
    (hg : GoalA m goal) (hp : m ≤ rp) (hq : m ≤ rq) (hm : m ≤ g.re) (h : n5Pre rp rq goal g = some (o, g')) :
    KeepsA m g g' := by
  cases goal with
  | pick z o =>
    exact (keepsA_emit hd (blobIn_fin (f := Termin.eqq rp rq z o) ⟨hp, hq, hg.1, hg.2⟩) h).1
  | done =>
    simp only [n5Pre] at h
    obtain ⟨⟨o0, o1⟩, g4, h4, h3⟩ := bind_some h
    have k4 := keepsA_doneBlocks (m := m) hd hm h4
    exact k4.trans (keepsA_emit (k4.dropF hd) (blobIn_fin (f := Termin.eqq rp rq (jmp0 o0) (jmp0 o1))
      ⟨hp, hq, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1
  | next laz th =>
    simp only [n5Pre] at h
    obtain ⟨a, g4, h4, h3⟩ := bind_some h
    obtain ⟨k4, r4⟩ := keepsA_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 hm h4
    cases a with
    | none =>
      simp only at h3
      by_cases ht : th.args = []
      · rw [if_pos ht] at h3
        exact k4.trans (keepsA_emit (k4.dropF hd) (blobIn_one (p := Pole.equ rp rq) (f := Termin.hop (jmp0 th.there))
          (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
          (jmpIn_jmp0 _ _)) h3).1
      · rw [if_neg ht] at h3; cases h3
    | some x =>
      obtain ⟨r, o⟩ := x
      simp only at h3
      obtain ⟨⟨z, o'⟩, g5, h5, h3⟩ := bind_some h3
      have k5 := keepsA_forl (k4.dropF hd) (r4 r o rfl) (Nat.le_trans hm k4.le) h5
      exact k4.trans (k5.trans (keepsA_emit ((k4.trans k5).dropF hd)
        (blobIn_fin (f := Termin.eqq rp rq (jmp0 z) (jmp0 o')) ⟨hp, hq, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1)

theorem keepXA_five {p q : Nomm} (ihp : KeepXA S Map p) (ihq : KeepXA S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) : KeepXA S Map (Nomm.n5 p q) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  rw [runL_n5_toL] at h
  obtain ⟨rp, ga, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
  obtain ⟨rq, gb, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
  obtain ⟨o, gc, h3, h⟩ := bind_some h
  have k3 := keepsA_n5Pre ((k1.trans k2).dropF hd) hg (show m ≤ rp by omega) (show m ≤ rq by omega)
    (show m ≤ gb.re by omega) h3
  obtain ⟨nexq, gd, h4, h⟩ := bind_some h
  obtain ⟨nexq', gd', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, ge, h5, h⟩ := bind_some h
  have l3 := k3.le
  exact (keepXA_binary (nq := lazyReg rq) (np := lazyReg rp) ihp ihq kp kq ((k1.trans (k2.trans k3)).dropF hd) hc'
    (nb_this (by omega)) (nb_this (by omega)) (jmpIn_jmp0 _ _) (na_this (by omega)) (na_this (by omega))
    (jmpIn_jmp0 _ _) (by omega) h4 h5 h).pre (k1.trans (k2.trans k3))

theorem keepXA_ten {a : Nat} {v q : Nomm} (ihv : KeepXA S Map v) (ihq : KeepXA S Map q) (kv : KeepX S Map v)
    (kq : KeepX S Map q) (hvp : v.pure = true) (hqp : q.pure = true) : KeepXA S Map (Nomm.n10 a v q) := by
  intro m goal region g0 g1 nex hd hgi hg hm hc h
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨n, gs'⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := keeps_simpleNext hd hgi hs'
  obtain ⟨a1, m1⟩ := keepsA_simpleNext hd hg hm hs'
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [show (Next.toL n : NextL S) = ⟨ofSure n.laz, n.th⟩ from rfl, intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nd, nr⟩ := keeps_into (k1.dropF hd) n1 hs2
  obtain ⟨a2, ndA, nrA⟩ := keepsA_into (k1.dropF hd) m1 (Nat.le_trans hm a1.le) hs2
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
  exact (keepXA_binary ihq ihv kq kv ((k1.trans k2).dropF hd) hc' nd nr (jmpIn_jmp0 _ _) ndA nrA (jmpIn_jmp0 _ _)
    (Nat.le_trans hm (a1.trans a2).le) h3 h4 hcp).pre (a1.trans a2)

/-! ## `%6` -/

theorem keepsA_emitted {m : Nat} {g : Gen Map} {b : Blob} (hd : g.drop = false) (hb : BlobIn (m ≤ ·) b) :
    KeepsA m g (g.emitted b) :=
  ⟨fun _ hl => aboveIn_emitted hl hd hb, Nat.le_refl _, rfl, Nat.le_succ _⟩

theorem keepsA_tagged (m : Nat) (g : Gen Map) (o : Nat) (region : List Nat) : KeepsA m g (g.tagged o region) := by
  refine ⟨fun lo hl => ?_, by simp, by simp, by simp⟩
  intro o' b l u hb
  rw [tagged_blocks] at hb
  rw [tagged_bo] at u
  exact hl o' b l u hb

theorem keepsA_sixGenL {m : Nat} {g2 : Gen Map} {t0 t1 : Jmp} {region : List Nat} (hd : g2.drop = false)
    (h0 : JmpIn (m ≤ ·) t0) (h1 : JmpIn (m ≤ ·) t1) : KeepsA m g2 (sixGenL g2 t0 t1 region) :=
  (keepsA_emitted hd (blobIn_fin (f := Termin.hop t0) h0)).trans
    ((keepsA_emitted (g := g2.emitted ⟨[], [], Termin.hop t0⟩) (b := ⟨[], [], Termin.hop t1⟩) hd
      (blobIn_fin (f := Termin.hop t1) h1)).trans ((keepsA_tagged _ _ _ _).trans (keepsA_tagged _ _ _ _)))

/-- The end of `%6`: the copy of the fork of the branches' needs at the two
lazy blocks `y` and `n` into the need of the test. -/
theorem keepXA_sixEnd {m : Nat} {g0 g1 g2 g3 g4 g5 : Gen Map} {xc x0 x1 nex : NextL S} {y n : Nat} {sc sa sb : Nat}
    (hd : g0.drop = false) (Rb : KeepR g0 g1 x1 sb) (Ra : KeepR g1 g2 x0 sa) (kG : Keeps g2 g3)
    (Rc : KeepR g3 g4 xc sc) (Ab : KeepRA m g0 g1 x1) (Aa : KeepRA m g1 g2 x0) (aG : KeepsA m g2 g3)
    (Ac : KeepRA m g3 g4 xc) (hm : m ≤ g0.re) (hy : g2.bo ≤ y) (hn : y + 1 = n) (hn3 : n + 1 = g3.bo)
    (h : copyL xc (mk (Sure.bunt : Sure S) [((y, x0.laz), (n, x1.laz))] []) g4 = some (nex, g5)) :
    KeepRA m g0 g5 nex := by
  have b1 := Rb.keeps.bo; have b2 := Ra.keeps.bo; have b3 := kG.bo; have b4 := Rc.keeps.bo
  have hL : LazyA m (mk (Sure.bunt : Sure S) [((y, x0.laz), (n, x1.laz))] []) := by
    refine ⟨na_none _, fun e he => ?_⟩
    rw [entries_six] at he
    rcases List.mem_append.mp he with he | he <;> rcases List.mem_cons.mp he with e' | he
    · rw [e']; exact Aa.out.1.1
    · exact Aa.out.1.2 e he
    · rw [e']; exact Ab.out.1.1
    · exact Ab.out.1.2 e he
  have hm4 : m ≤ g4.re :=
    Nat.le_trans hm (Nat.le_trans Ab.keeps.le (Nat.le_trans Aa.keeps.le (Nat.le_trans aG.le Ac.keeps.le)))
  obtain ⟨k, o⟩ := keepA_copyL (lo := g0.bo) (mid := g3.bo) (Ac.keeps.dropF (aG.dropF
    (Aa.keeps.dropF (Ab.keeps.dropF hd)))) Ac.out hL hm4 (fun e he => Rc.labs e he) (fun e he => by
      rw [entries_six] at he
      rcases List.mem_append.mp he with he | he <;> rcases List.mem_cons.mp he with e' | he
      · rw [e']; exact ⟨by omega, by omega⟩
      · have := Ra.labs e he; exact ⟨by omega, by omega⟩
      · rw [e']; exact ⟨by omega, by omega⟩
      · have := Rb.labs e he; exact ⟨by omega, by omega⟩) h
  exact ⟨Ab.keeps.trans (Aa.keeps.trans (aG.trans (Ac.keeps.trans k))), o⟩

theorem keepsA_same {m : Nat} {g g' : Gen Map} (h : SameBlocks g g') : KeepsA m g g' := by
  obtain ⟨hre, hbo, _, hdr, _, _, hbl⟩ := h
  refine ⟨fun lo hl o b l u hb => ?_, Nat.le_of_eq hre.symm, hdr, Nat.le_of_eq hbo.symm⟩
  rw [hbl] at hb; rw [hbo] at u
  exact hl o b l u hb

/-- **`%6` for `%done` or `%pick`.** -/
theorem keepXA_sixP {c a b : Nomm} (hcp : c.pure = true) (ihc : KeepXA S Map c) (iha : KeepXA S Map a)
    (ihb : KeepXA S Map b) (kc : KeepX S Map c) (ka : KeepX S Map a) (kb : KeepX S Map b) {m : Nat}
    {goal : CGoal S} (hg' : NotNext goal) {region : List Nat} {g0 g4 : Gen Map}
    {nex : NextL S} (hd : g0.drop = false) (hgi : GoalIn g0.re goal) (hg : GoalA m goal) (hm : m ≤ g0.re)
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g4)) : KeepRA m g0 g4 nex := by
  rw [runL_n6_body _ _ _ hg'] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  have Rb := kb hd hgi (by omega) h1
  have Ab := ihb hd hgi hg hm (by omega) h1
  have d1 := Rb.keeps.dropF hd
  have Ra := ka d1 (hgi.mono Rb.keeps.le) (by omega) h2
  have Aa := iha d1 (hgi.mono Rb.keeps.le) hg (Nat.le_trans hm Rb.keeps.le) (by omega) h2
  have d2 := Ra.keeps.dropF d1
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have aG := keepsA_sixGenL (m := m) (region := region) d2 Aa.out.2 Ab.out.2
  have Rc := kc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2)
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ (by omega) h3
  have Ac := ihc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2)
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    (Nat.le_trans hm (Nat.le_trans Rb.keeps.le (Nat.le_trans Ra.keeps.le kG.le))) (by omega) h3
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  exact keepXA_sixEnd hd Rb Ra kG Rc Ab Aa aG Ac hm (Nat.le_refl _) rfl (by simp) (hrest hbig)

/-- **`%6` for a fork-free `%next`**: the blocks of `+fork-sure` mention the
copies `s0`, `s1` (fresh) and the goal's need. -/
theorem keepXA_sixN {c a b : Nomm} (hcp : c.pure = true) (ihc : KeepXA S Map c) (iha : KeepXA S Map a)
    (ihb : KeepXA S Map b) (kc : KeepX S Map c) (ka : KeepX S Map a) (kb : KeepX S Map b) {m : Nat}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hgi : GoalIn g0.re (CGoal.next sur th)) (hg : GoalA m (CGoal.next sur th))
    (hm : m ≤ g0.re) (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g9)) :
    KeepRA m g0 g9 nex := by
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
      exact ⟨fun x hx => Nat.lt_of_lt_of_le (hgi.1 x ((mem_flatten _ x).mp hx)) hle, RegsIn.nil _, jmpIn_jmp0 _ _⟩
    · omega
  have aF : KeepsA m g0 gF := by
    refine ⟨fun lo hl o b' l u hb' => ?_, hle, hdrop, by omega⟩
    by_cases h0 : o < g0.bo
    · rw [hold o h0] at hb'
      exact hl o b' l h0 hb'
    by_cases e0 : o = g0.bo
    · rw [e0, hb0] at hb'; cases hb'
      exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => Nat.le_trans hm (hreg x (Or.inl hx)).1)
    by_cases e1 : o = g0.bo + 1
    · rw [e1, hb1] at hb'; cases hb'
      exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => Nat.le_trans hm (hreg x (Or.inr hx)).1)
    by_cases e2 : o = g0.bo + 2
    · rw [e2, hb2] at hb'; cases hb'
      exact ⟨fun x hx => hg.1 x ((mem_flatten _ x).mp hx), RegsIn.nil _, jmpIn_jmp0 _ _⟩
    · omega
  have kI : Keeps gF { gF with id := gF.id + 1 } := ⟨fun _ hl => hl, Nat.le_refl _, rfl, Nat.le_refl _⟩
  have aI : KeepsA m gF { gF with id := gF.id + 1 } := ⟨fun _ hl => hl, Nat.le_refl _, rfl, Nat.le_refl _⟩
  have dF := kF.dropF hd
  have Rb0 := kb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩ (by omega) hR
  have Ab0 := ihb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩
    ⟨fun x hx => Nat.le_trans hm (hreg x (Or.inr hx)).1, jmpIn_jmp0 _ _⟩ (Nat.le_trans hm hle) (by omega) hR
  have Rb := Rb0.pre (kF.trans kI) hcond (Nat.le_refl _)
  have Ab := Ab0.pre (aF.trans aI)
  have d1 := Rb.keeps.dropF hd
  have lR : gF.re ≤ gR.re := Rb0.keeps.le
  have Ra := iha (m := m) (goal := CGoal.next s0 (jmp0 g0.bo)) d1
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩
    ⟨fun x hx => Nat.le_trans hm (hreg x (Or.inl hx)).1, jmpIn_jmp0 _ _⟩ (Nat.le_trans hm (Nat.le_trans hle lR))
    (by omega) hQ
  have Ka := ka (goal := CGoal.next s0 (jmp0 g0.bo)) d1
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩ (by omega) hQ
  have d2 := Ka.keeps.dropF d1
  have cR : gR.cond = gF.cond := Rb0.cnd
  rw [cR] at hS
  obtain ⟨ey, en, _, _, el, hsb⟩ := sect_spec d2 (Ka.cnd.trans cR) hS
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := gF.id :: region) d2 Ka.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ka.keeps.le)
  have aG := keepsA_sixGenL (m := m) (region := gF.id :: region) d2 Ra.out.2 Ab.out.2
  have kS := kG.trans (keeps_same hsb)
  have aS := aG.trans (keepsA_same (m := m) hsb)
  have Rc := kc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    (by omega) hC
  have Ac := ihc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ (Nat.le_trans hm (Nat.le_trans Rb.keeps.le (Nat.le_trans Ka.keeps.le kS.le)))
    (by omega) hC
  subst el
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ka.size; have := Rb.size; simp only [lazyMax]; omega
  subst ey en
  have bS : gS.bo = gQ.bo + 2 := by rw [hsb.2.1]; simp
  exact keepXA_sixEnd hd Rb Ka kS Rc Ab Ra aS Ac hm (by omega) (by omega) (by omega) (hrest hbig)

/-! ## The induction -/

/-- **On `FragX` every run for a fork-free goal whose registers are below
`re` and at least `m`, with `m ≤ re`, from a state that does not drop, keeps
the lower bound `m`**, when the nomm has at most 255 `%6`. -/
theorem runX_keepsA {nm : Nomm} (hf : FragX (S := S) nm) : KeepXA S Map nm := by
  induction hf with
  | frag hf => exact keepXA_frag hf
  | @six c a b hc' ha' hb' ihc iha ihb =>
    have hcp := fragX_pure hc'
    intro m goal region g0 g1 nex hd hgi hg hm hc h
    have hc'' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hc
    cases goal with
    | next sur th =>
      exact keepXA_sixN hcp ihc iha ihb (runX_keeps hc') (runX_keeps ha') (runX_keeps hb') hd hgi hg hm hc'' h
    | done =>
      exact keepXA_sixP (goal := CGoal.done) hcp ihc iha ihb (runX_keeps hc') (runX_keeps ha') (runX_keeps hb')
        trivial hd hgi hg hm hc'' h
    | pick z o =>
      exact keepXA_sixP (goal := CGoal.pick z o) hcp ihc iha ihb (runX_keeps hc') (runX_keeps ha') (runX_keeps hb')
        trivial hd hgi hg hm hc'' h
  | four _ ih => exact keepXA_four ih
  | three _ ih => exact keepXA_three ih
  | seven hq _ ih => exact keepXA_seven hq ih
  | cons hp hq ihp ihq => exact keepXA_cons ihp ihq (runX_keeps hp) (runX_keeps hq) (fragX_pure hp) (fragX_pure hq)
  | five hp hq ihp ihq => exact keepXA_five ihp ihq (runX_keeps hp) (runX_keeps hq) (fragX_pure hp)
  | ten hv hq ihv ihq => exact keepXA_ten ihv ihq (runX_keeps hv) (runX_keeps hq) (fragX_pure hv) (fragX_pure hq)
  | sevenFrom ha _ ihq => exact keepXA_sevenFrom ha ihq

/-- **The blocks a run of a nomm of `FragX` emits mention only registers
from `m` on**, for a fork-free goal whose registers are below `re` and at
least `m`, with `m ≤ re`. -/
theorem runX_above {nm : Nomm} (hf : FragX (S := S) nm) {m : Nat} {goal : CGoal S} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hd : g0.drop = false) (hgi : GoalIn g0.re goal) (hg : GoalA m goal)
    (hm : m ≤ g0.re) (hc : sixCount nm ≤ 255) (h : runL nm (CGoal.toL goal) region g0 = some (nex, g1)) :
    AboveIn m g0.bo g1 :=
  (runX_keepsA hf hd hgi hg hm hc h).keeps.ab _ (aboveIn_start m g0)

/-- **Every nomm of `FragX` meets `AboveX`.** -/
theorem aboveX_of_fragX {p : Nomm} (hf : FragX (S := S) p) : AboveX S Map p := by
  intro a th region g g' nex h ha ea _ _ d0 _ _ _ hcount o b l u hb
  have hj : ∀ (P : Nat → Prop), JmpIn P th := fun _ x hx => by rw [ea] at hx; exact absurd hx List.not_mem_nil
  exact runX_above hf (goal := CGoal.next (lazyReg a : Sure S) th) d0 ⟨nb_this ha, hj _⟩
    ⟨na_this (Nat.le_refl a), hj _⟩ (Nat.le_of_lt ha) hcount h o b l u hb

/-- **The final pass meets the contract on `[7 [4 p] q]`** with `p` and `q`
in `FragX`, at most 255 `%6`, when nothing is baked and the bell's cape has
no `[| |]`: `finishLF_bellContract74U` with `AboveX p` from `FragX p`. -/
theorem finishLF_bellContract74X {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {p q : Nomm} (hp : (Nomm.n7 (Nomm.n4 p) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n4 p) q))
    (hfp : FragX (S := S) p) (hfq : FragX (S := S) q)
    (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n4 p) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' :=
  finishLF_bellContract74U hok hp hA hfp (aboveX_of_fragX hfp) hfq hcount hbl hn hbake h N

/-- **The final pass meets the contract on `[7 [3 p] q]`** with `p` and `q`
in `FragX`, given `hq3`: `finishLF_bellContract73U` with `AboveX p` from
`FragX p`. -/
theorem finishLF_bellContract73X {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {p q : Nomm} (hp : (Nomm.n7 (Nomm.n3 p) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n3 p) q))
    (hfp : FragX (S := S) p) (hfq : FragX (S := S) q)
    (hq3 : ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nx, g1) →
      noneEquivalentL nx.laz = false)
    (hcount : sixCount (Nomm.n7 (Nomm.n3 p) q) ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n3 p) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' :=
  finishLF_bellContract73U hok hp hA hfp (aboveX_of_fragX hfp) hfq hq3 hcount hbl hn hbake h N

/-- `[7 [4 [5 [0 2] [0 3]]] [0 1]]`, not covered before (`AboveX` of `%5`),
meets every hypothesis of `finishLF_bellContract74X` on the formula. -/
example : FragX (S := S) (Nomm.n5 (Nomm.n0 2) (Nomm.n0 3)) ∧ FragX (S := S) (Nomm.n0 1) ∧
    sixCount (Nomm.n7 (Nomm.n4 (Nomm.n5 (Nomm.n0 2) (Nomm.n0 3))) (Nomm.n0 1)) ≤ 255 :=
  ⟨FragX.five (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial), FragX.frag fun _ => trivial, by decide⟩

end Comp
end SkaModel
end Formalization
