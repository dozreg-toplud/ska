import lemmas.Ska.RawInvFinishX
import lemmas.Ska.CompFootX

/-!
# Raw `+comp` output on `FragX`: the lazy entries lie apart

README Gaps 14, track D.  `optIn_finishLFX_of` asks `LazOK` of the top
run's result: the sure needs of the root and of the entries of its lazy
tree are pairwise disjoint, and no block of the run defines one of their
registers.  Track C's footprint (`FootR` of `runX_foot`) gives all of it
but one part: it says that the run writes no register of those needs
(`wr`) and that the root's need is apart from each entry's (`apart`), not
that two entries' needs are apart.

* `EApX nm`: every run of `runL nm` (under the hypotheses of `FootX`)
  returns a lazy tree whose entries have pairwise disjoint sure needs.
  The cases follow `runX_foot`: the result is the operand's (`%3`, `%4`,
  `%7`), the same entries moved under an axis (`+from`, `FromEnt`), the
  entries of two sub-runs side by side (`eapX_binary`: those of `q` lie
  below the start of `p`'s run or in `q`'s goal, those of `p` above it or
  in `p`'s goal, and the two goals are apart), or for `%6` the entries of
  the test and the two branches with their roots (`needsApart_six`: the
  test's registers are above the branches', the `a` branch's above the
  `b` branch's or in the fork's `s0`, the `b` branch's in its range or in
  `s1`, and `s0`, `s1` are apart).
* **`runX_eap`**: `EApX` for every nomm of `FragX`.
* **`lazOK_run`**: `LazOK` of the top run, from `runX_eap`, `FootR.apart`
  and `FootR.wr` (`defd_of_wroteIn`; `gen0` has no blocks).
* **`optIn_finishLFX`**, **`optimize_keeps_finishLFX`**: `OptIn` and
  `Opt.Keeps` of `finishLF` for every nomm of `FragX` with at most 255
  `%6` and nothing baked, with no hypothesis on the run.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Lists of entries apart -/

theorem needsApart_perm {a b : List (Nat × Comp.Lazy S)} (p : a.Perm b) (h : NeedsApart a) : NeedsApart b :=
  h.perm p (fun h' r a b => h' r b a)

theorem needsApart_append {a b : List (Nat × Comp.Lazy S)} {P Q : Nat → Prop} (ha : NeedsApart a)
    (hb : NeedsApart b) (hP : ∀ e ∈ a, ∀ r, NMem e.2.sure.ned r → P r)
    (hQ : ∀ e ∈ b, ∀ r, NMem e.2.sure.ned r → Q r) (hPQ : ∀ r, P r → ¬ Q r) : NeedsApart (a ++ b) :=
  List.pairwise_append.mpr ⟨ha, hb, fun e he e' he' r h1 h2 => hPQ r (hP e he r h1) (hQ e' he' r h2)⟩

theorem needsApart_root {o : Nat} {l : Comp.Lazy S} (h : NeedsApart (entries l))
    (ap : ∀ e ∈ entries l, ∀ r, NMem l.sure.ned r → ¬ NMem e.2.sure.ned r) : NeedsApart ((o, l) :: entries l) :=
  List.pairwise_cons.mpr ⟨fun e he r h1 h2 => ap e he r h1 h2, h⟩

theorem needsApart_fromEnt {axe : Nat} {a b : List (Nat × Comp.Lazy S)} (h : FromEnt axe a b)
    (ha : NeedsApart a) : NeedsApart b := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons hl hab ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp ha
    refine List.pairwise_cons.mpr ⟨fun e he r hr hr' => ?_, ih h2⟩
    obtain ⟨l, fl, ml⟩ := hab.mem_right he
    exact h1 _ ml r (nmem_fromSure (fromL_sure hl) hr) (nmem_fromSure (fromL_sure fl) hr')

/-- **The entries of `%6`**: those of the test, then each branch's root and
entries, apart when the three kinds lie in disjoint sets of registers. -/
theorem needsApart_six {s : Sure S} {lc l0 l1 : Comp.Lazy S} {y n : Nat} {Pc P0 P1 : Nat → Prop}
    (Nc : NeedsApart (entries lc)) (N0 : NeedsApart (entries l0)) (N1 : NeedsApart (entries l1))
    (A0 : ∀ e ∈ entries l0, ∀ r, NMem l0.sure.ned r → ¬ NMem e.2.sure.ned r)
    (A1 : ∀ e ∈ entries l1, ∀ r, NMem l1.sure.ned r → ¬ NMem e.2.sure.ned r)
    (rc : ∀ e ∈ entries lc, ∀ r, NMem e.2.sure.ned r → Pc r)
    (r0 : ∀ r, NMem l0.sure.ned r → P0 r) (re0 : ∀ e ∈ entries l0, ∀ r, NMem e.2.sure.ned r → P0 r)
    (r1 : ∀ r, NMem l1.sure.ned r → P1 r) (re1 : ∀ e ∈ entries l1, ∀ r, NMem e.2.sure.ned r → P1 r)
    (c0 : ∀ r, Pc r → ¬ P0 r) (c1 : ∀ r, Pc r → ¬ P1 r) (d01 : ∀ r, P0 r → ¬ P1 r) :
    NeedsApart (entries (mk s (lc.fork ++ [((y, l0), (n, l1))]) (lc.bond ++ []))) := by
  have p := entries_side_perm s lc (mk (Sure.bunt : Sure S) [((y, l0), (n, l1))] [])
  simp only [fork_mk, bond_mk] at p
  rw [entries_six] at p
  have m0 : ∀ e ∈ (y, l0) :: entries l0, ∀ r, NMem e.2.sure.ned r → P0 r := fun e he r hr => by
    rcases List.mem_cons.mp he with rfl | he
    · exact r0 r hr
    · exact re0 e he r hr
  have m1 : ∀ e ∈ (n, l1) :: entries l1, ∀ r, NMem e.2.sure.ned r → P1 r := fun e he r hr => by
    rcases List.mem_cons.mp he with rfl | he
    · exact r1 r hr
    · exact re1 e he r hr
  refine needsApart_perm p.symm (needsApart_append (P := Pc) (Q := fun r => P0 r ∨ P1 r) Nc
    (needsApart_append (needsApart_root N0 A0) (needsApart_root N1 A1) m0 m1 d01) rc
    (fun e he r hr => ?_) (fun r hc h => ?_))
  · rcases List.mem_append.mp he with he | he
    · exact Or.inl (m0 e he r hr)
    · exact Or.inr (m1 e he r hr)
  · rcases h with h | h
    · exact c0 r hc h
    · exact c1 r hc h

/-! ## The induction -/

/-- **What the induction proves of one nomm of `FragX`**: the sure needs of
the entries of the result's lazy tree are pairwise apart. -/
abbrev EApX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {goal : CGoal S} {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S},
    g0.drop = false → GoalIn g0.re goal → GDist goal → sixCount nm ≤ 255 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → NeedsApart (entries nex.laz)

theorem eapX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : EApX S Map nm := by
  intro goal region g0 g1 nex hd hg hD _ h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only [Next.toL, entries_ofSure, NeedsApart, List.Pairwise.nil]

theorem eapX_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : EApX S Map p) :
    EApX S Map (Nomm.n7 p q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag (hq goal)] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := run_keeps q goal g0 g' n hd hg hr
  have Fq := run_foot q goal g0 g' n hd hg hD hr
  exact ihp (goal := CGoal.next n.laz n.th) (k1.dropF hd) n1 Fq.dist (by simp only [sixCount] at hc; omega) h2

theorem eapX_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : EApX S Map q) :
    EApX S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha h
  exact needsApart_fromEnt (fromL_ent axe _ _ hl) (ihq hd hg hD (by simp only [sixCount] at hc; omega) h1)

/-! ## `%4` and `%3` -/

theorem eapX_tail {p : Nomm} (ih : EApX S Map p) {b : Blob} {arg : Nat} {region : List Nat}
    {g g1 g2 : Comp.Gen Map} {o : Nat} {nex : NextL S} (hd : g.drop = false) (hb : BlobIn (· < g.re) b)
    (ha : arg < g.re) (hc : sixCount p ≤ 255) (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region g1 = some (nex, g2)) :
    NeedsApart (entries nex.laz) := by
  obtain ⟨k1, q1⟩ := keeps_emit hd hb h1
  exact ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) (k1.dropF hd) ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩
    trivial hc h

theorem eapX_four {p : Nomm} (ih : EApX S Map p) : EApX S Map (Nomm.n4 p) := by
  intro goal region g0 g1 nex hd hg hD hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o, gc, h3, h⟩ := bind_some h
    exact eapX_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
      (fun x hx => by simp only [Comp.poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      (show pro < gb.re by omega)) (by omega) hcp h3 h
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o', gc, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g0.re → x < gb.re := fun x hx => by omega
    exact eapX_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
      (fun x hx => by simp only [Comp.poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      ⟨show pro < gb.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) hcp h3 h
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 h1
    obtain ⟨⟨pro, th'⟩, gb, h2, h⟩ := bind_some h
    have hp : Keeps ga gb ∧ pro < gb.re := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨Keeps.refl _, r1 _ _ rfl⟩
      | none =>
        simp only at h2
        obtain ⟨r, g3, h3, h2⟩ := bind_some h2
        obtain ⟨e3, q3, k3⟩ := keeps_re h3
        by_cases ht : th.args = []
        · rw [if_pos ht] at h2
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨k3, by omega⟩
        · rw [if_neg ht] at h2; cases h2
    obtain ⟨k2, p2⟩ := hp
    obtain ⟨arg, gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨o, gd, h4, h⟩ := bind_some h
    exact eapX_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
        (fun x hx => by simp only [Comp.poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (jmpIn_jmp0 _ _)) (by omega) hcp h4 h

theorem eapX_three {p : Nomm} (ih : EApX S Map p) : EApX S Map (Nomm.n3 p) := by
  intro goal region g0 g1 nex hd hg hD hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨⟨o0, o1⟩, ga, h1, h⟩ := bind_some h
    have k1 := keeps_doneBlocks hd h1
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    exact eapX_tail ih ((k1.trans k2).dropF hd)
      (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show r < gb.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) hcp h3 h
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g0.re → x < gb.re := fun x hx => by omega
    exact eapX_tail ih (k2.dropF hd)
      (blobIn_fin (f := Termin.clq r z o) ⟨show r < gb.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) hcp h3 h
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    dsimp only at h
    revert h; split
    · exact fun h => ih (goal := CGoal.next sur th) hd hg hD hcp h
    intro h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 h1
    rcases a with _ | ⟨r, o⟩
    · cases h
    simp only at h
    obtain ⟨⟨z, o'⟩, gb, h2, h⟩ := bind_some h
    have k2 := keeps_forl (k1.dropF hd) (r1 r o rfl) h2
    obtain ⟨r', gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨oc, gd, h4, h⟩ := bind_some h
    exact eapX_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show r' < gc.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) hcp h4 h

/-! ## The binary cases -/

/-- **Two runs and the `+copy`**: the entries of the two results side by
side. -/
theorem eapX_binary {p q : Nomm} (ihp : EApX S Map p) (ihq : EApX S Map q) (fp : FootX S Map p)
    (fq : FootX S Map q) (kp : KeepX S Map p) (kq : KeepX S Map q) {region : List Nat} {g0 g1 g2 g3 : Comp.Gen Map}
    {nq np : Sure S} {th : Jmp} {nex2 nex1 nex : NextL S} (hd : g0.drop = false) (hc : sixCount p + sixCount q ≤ 255)
    (hnq : NB g0.re nq.ned) (hnp : NB g0.re np.ned) (dq : Distinct nq.ned) (dp : Distinct np.ned)
    (ap : ∀ x, NMem np.ned x → ¬ NMem nq.ned x) (hj : JmpIn (· < g0.re) th)
    (h2 : runL q (CGoalL.next (ofSure nq) th) region g0 = some (nex2, g1))
    (h3 : runL p (CGoalL.next (ofSure np) nex2.th) region g1 = some (nex1, g2))
    (h4 : copyL nex1 nex2.laz g2 = some (nex, g3)) : NeedsApart (entries nex.laz) := by
  have Rq := kq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have Fq := fq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ dq (by omega) h2
  have Nq := ihq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ dq (by omega) h2
  have d1 := Rq.keeps.dropF hd
  have gp : GoalIn g1.re (CGoal.next np nex2.th) := ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩
  have Rp := kp (goal := CGoal.next np nex2.th) d1 gp (by omega) h3
  have Fp := fp (goal := CGoal.next np nex2.th) d1 gp dp (by omega) h3
  have Np := ihp (goal := CGoal.next np nex2.th) d1 gp dp (by omega) h3
  have l1 := Rq.keeps.le
  obtain ⟨n, -, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := (Rp.labs _ (fork_in_entries he)).1
      have b := (Rq.labs _ (fork_in_entries he')).2
      omega)
    (fun e he e' he' => by
      have a := (Rp.labs _ (bond_in_entries he)).1
      have b := (Rq.labs _ (bond_in_entries he')).2
      omega) h4
  refine needsApart_perm (entries_side_perm _ _ _).symm (needsApart_append
    (P := fun y => g1.re ≤ y ∨ NMem np.ned y) (Q := fun y => y < g1.re ∧ (g0.re ≤ y ∨ NMem nq.ned y)) Np Nq
    (fun e he y hy => Fp.esure e he y hy) (fun e he y hy => ⟨Rq.out.1.2 e he y hy, Fq.esure e he y hy⟩)
    fun y hp hq => ?_)
  obtain ⟨hq1, hq2⟩ := hq
  rcases hp with e | e
  · omega
  · rcases hq2 with e' | e'
    · have := hnp y e; omega
    · exact ap y e e'

theorem eapX_consBody {p q : Nomm} (ihp : EApX S Map p) (ihq : EApX S Map q) (fp : FootX S Map p)
    (fq : FootX S Map q) (kp : KeepX S Map p) (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hd : g0.drop = false)
    (hg : GoalIn g0.re (CGoal.next sur th)) (hD : Distinct sur.ned) (hc : sixCount p + sixCount q ≤ 255)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : NeedsApart (entries nex.laz) := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hg.1 hg.2 hs2
  obtain ⟨W2, dh, dt, ap, mh, mt⟩ := split_foot hd hD hg.1 hg.2 hs2
  simp only at W2 dh dt ap mh mt nh nt
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
  exact eapX_binary ihp ihq fp fq kp kq (k2.dropF hd) hc nt nh dt dh ap (jmpIn_jmp0 _ _) h3 h4 hcp

theorem eapX_cons {p q : Nomm} (ihp : EApX S Map p) (ihq : EApX S Map q) (fp : FootX S Map p)
    (fq : FootX S Map q) (kp : KeepX S Map p) (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true) :
    EApX S Map (Nomm.cons p q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at h
    rw [runL_cons_next] at h
    exact eapX_consBody ihp ihq fp fq kp kq hpp hqp hd hg hD hc' h
  | done =>
    simp only [CGoal.toL] at h
    rw [runL_cons_done] at h
    obtain ⟨r, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o, gb, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keeps_emit (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show r < ga.re by omega)) h2
    rw [runL_cons_next] at h
    exact eapX_consBody (sur := lazyReg r) ihp ihq fp fq kp kq hpp hqp ((k1.trans k2).dropF hd)
      ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ trivial hc' h
  | pick z o =>
    simp only [CGoal.toL] at h
    rw [runL_cons_pick] at h
    obtain ⟨o', ga, h1, h⟩ := bind_some h
    obtain ⟨k1, q1⟩ := keeps_emit hd (blobIn_fin (f := Termin.bom Option.none) trivial) h1
    obtain ⟨nex2, gb, h3, h⟩ := bind_some h
    obtain ⟨nex2', gb', hp2, h⟩ := bind_some h
    rw [pastL_pure _ _ hpp, pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nex1, gc, h4, h⟩ := bind_some h
    exact eapX_binary (nq := Sure.bunt) (np := Sure.bunt) ihp ihq fp fq kp kq (k1.dropF hd) hc' (nb_none _)
      (nb_none _) trivial trivial (fun _ e => e.elim) (jmpIn_jmp0 _ _) h3 h4 h

theorem eapX_five {p q : Nomm} (ihp : EApX S Map p) (ihq : EApX S Map q) (fp : FootX S Map p)
    (fq : FootX S Map q) (kp : KeepX S Map p) (kq : KeepX S Map q) (hpp : p.pure = true) :
    EApX S Map (Nomm.n5 p q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  rw [runL_n5_toL] at h
  obtain ⟨rp, ga, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨rq, gb, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  obtain ⟨o, gc, h3, h⟩ := bind_some h
  have k3 := keeps_n5Pre ((k1.trans k2).dropF hd) (hg.mono (by omega)) (by omega) (by omega) h3
  obtain ⟨nexq, gd, h4, h⟩ := bind_some h
  obtain ⟨nexq', gd', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, ge, h5, h⟩ := bind_some h
  have l3 := k3.le
  exact eapX_binary (nq := lazyReg rq) (np := lazyReg rp) ihp ihq fp fq kp kq ((k1.trans (k2.trans k3)).dropF hd)
    hc' (nb_this (by omega)) (nb_this (by omega)) trivial trivial
    (fun x e e' => by simp only [lazyReg, NMem] at e e'; omega) (jmpIn_jmp0 _ _) h4 h5 h

theorem eapX_ten {a : Nat} {v q : Nomm} (ihv : EApX S Map v) (ihq : EApX S Map q) (fv : FootX S Map v)
    (fq : FootX S Map q) (kv : KeepX S Map v) (kq : KeepX S Map q) (hvp : v.pure = true) (hqp : q.pure = true) :
    EApX S Map (Nomm.n10 a v q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨n, gs'⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := keeps_simpleNext hd hg hs'
  have F0 : Distinct n.laz.ned := by
    cases goal with
    | next laz th =>
      simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact hD
    | done =>
      simp only [simpleNext] at hs'
      obtain ⟨r, g5, h5, hs'⟩ := bind_some hs'
      obtain ⟨o, g6, h6, hs'⟩ := bind_some hs'
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      trivial
    | pick z o =>
      simp only [simpleNext] at hs'
      obtain ⟨r, g5, h5, hs'⟩ := bind_some hs'
      obtain ⟨o', g6, h6, hs'⟩ := bind_some hs'
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      trivial
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [show (Next.toL n : NextL S) = ⟨ofSure n.laz, n.th⟩ from rfl, intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nd, nr⟩ := keeps_into (k1.dropF hd) n1 hs2
  obtain ⟨_, _, _, _, md, mr, _, Sm⟩ := into_ok hs2
  obtain ⟨Dd, Dr, Ddr, _, _⟩ := Sm F0 n1.1
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
  exact eapX_binary ihq ihv fq fv kq kv ((k1.trans k2).dropF hd) hc' nd nr Dd Dr (fun x e e' => Ddr x e' e)
    (jmpIn_jmp0 _ _) h3 h4 hcp

/-! ## `%6` -/

theorem eapX_sixP {c a b : Nomm} (hcp : c.pure = true) (ihc : EApX S Map c) (iha : EApX S Map a)
    (ihb : EApX S Map b) (fc : FootX S Map c) (fa : FootX S Map a) (fb : FootX S Map b) (kc : KeepX S Map c)
    (ka : KeepX S Map a) (kb : KeepX S Map b) {goal : CGoal S} (hg' : NotNext goal) {region : List Nat}
    {g0 g4 : Comp.Gen Map} {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re goal) (hD : GDist goal)
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g4)) : NeedsApart (entries nex.laz) := by
  have ng : ∀ x, ¬ GMem goal x := fun x hx => by
    cases goal with
    | next => exact hg'
    | done => exact hx
    | pick => exact hx
  rw [runL_n6_body _ _ _ hg'] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  have Rb := kb hd hg (by omega) h1
  have Fb := fb hd hg hD (by omega) h1
  have Nb := ihb hd hg hD (by omega) h1
  have d1 := Rb.keeps.dropF hd
  have Ra := ka d1 (hg.mono Rb.keeps.le) (by omega) h2
  have Fa := fa d1 (hg.mono Rb.keeps.le) hD (by omega) h2
  have Na := iha d1 (hg.mono Rb.keeps.le) hD (by omega) h2
  have d2 := Ra.keeps.dropF d1
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have gc : GoalIn (sixGenL g2 x0.th x1.th region).re (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) :=
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
  have Rc := kc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2) gc (by omega) h3
  have Fc := fc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2) gc trivial (by omega) h3
  have Nc := ihc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2) gc trivial (by omega) h3
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  have h4 := hrest hbig
  have l1 := Rb.keeps.le
  have l2 := Ra.keeps.le
  obtain ⟨n, -, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have := (Rc.labs _ (fork_in_entries he)).1
      simp only [sixGenL_bo] at this
      rw [fork_mk, List.mem_singleton] at he'
      subst he'
      simp only
      omega)
    (fun e he e' he' => by rw [bond_mk] at he'; cases he') h4
  have rce : ∀ e ∈ entries xc.laz, ∀ y, NMem e.2.sure.ned y → g2.re ≤ y := fun e he y hy => by
    have e' := Fc.esure e he y hy
    simp only [sixGenL_re] at e'
    exact e'.resolve_right (fun e => e)
  exact needsApart_six (Pc := fun y => g2.re ≤ y) (P0 := fun y => g1.re ≤ y ∧ y < g2.re) (P1 := fun y => y < g1.re)
    Nc Na Nb Fa.apart Fb.apart rce
    (fun y hy => ⟨(Fa.sure y hy).resolve_right (ng y), Ra.out.1.1 y hy⟩)
    (fun e he y hy => ⟨(Fa.esure e he y hy).resolve_right (ng y), Ra.out.1.2 e he y hy⟩)
    (fun y hy => Rb.out.1.1 y hy) (fun e he y hy => Rb.out.1.2 e he y hy)
    (fun y a b => by omega) (fun y a b => by omega)
    (fun y a b => by omega)

theorem eapX_sixN {c a b : Nomm} (hcp : c.pure = true) (ihc : EApX S Map c) (iha : EApX S Map a)
    (ihb : EApX S Map b) (fc : FootX S Map c) (fa : FootX S Map a) (fb : FootX S Map b) (kc : KeepX S Map c)
    (ka : KeepX S Map a) (kb : KeepX S Map b) {sur : Sure S} {th : Jmp} {region : List Nat}
    {g0 g9 : Comp.Gen Map} {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th))
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g9)) :
    NeedsApart (entries nex.laz) := by
  simp only [CGoal.toL] at h
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
  obtain ⟨_, _, _, _, d0, d1, j01, hreg, hle, hbo, hdrop, hcond, _, hb0, hb1, hb2, hold⟩ := forkSure_spec hF hd
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
  have dF := kF.dropF hd
  have gb : GoalIn ({ gF with id := gF.id + 1 } : Comp.Gen Map).re (CGoal.next s1 (jmp0 (g0.bo + 1))) :=
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩
  have Rb := kb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF gb
    (by omega) hR
  have Fb := fb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF gb d1
    (by omega) hR
  have Nb := ihb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF gb d1
    (by omega) hR
  have d1' := Rb.keeps.dropF dF
  have lR : gF.re ≤ gR.re := Rb.keeps.le
  have ga : GoalIn gR.re (CGoal.next s0 (jmp0 g0.bo)) :=
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩
  have Ra := ka (goal := CGoal.next s0 (jmp0 g0.bo)) d1' ga (by omega) hQ
  have Fa := fa (goal := CGoal.next s0 (jmp0 g0.bo)) d1' ga d0 (by omega) hQ
  have Na := iha (goal := CGoal.next s0 (jmp0 g0.bo)) d1' ga d0 (by omega) hQ
  have d2 := Ra.keeps.dropF d1'
  have cR : gR.cond = gF.cond := Rb.cnd
  rw [cR] at hS
  obtain ⟨ey, en, _, _, el, hsb⟩ := sect_spec d2 (Ra.cnd.trans cR) hS
  obtain ⟨kG, _⟩ := keeps_sixGenL (region := gF.id :: region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have kS := kG.trans (keeps_same hsb)
  have bS : gS.bo = gQ.bo + 2 := by rw [hsb.2.1]; simp
  have reS : gS.re = gQ.re := by rw [hsb.1]; simp
  have gc : GoalIn gS.re (CGoal.pick (jmp0 yes) (jmp0 nuh) : CGoal S) := ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
  have Rc := kc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) gc (by omega) hC
  have Fc := fc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) gc trivial (by omega) hC
  have Nc := ihc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) gc trivial (by omega) hC
  subst el
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  subst ey en
  have h4 := hrest hbig
  have lQ := Ra.keeps.le
  have lC := Rc.keeps.le
  obtain ⟨n, -, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have := (Rc.labs _ (fork_in_entries he)).1
      rw [fork_mk, List.mem_singleton] at he'
      subst he'
      simp only
      omega)
    (fun e he e' he' => by rw [bond_mk] at he'; cases he') h4
  exact needsApart_six (Pc := fun y => gS.re ≤ y) (P0 := fun y => (gR.re ≤ y ∨ NMem s0.ned y) ∧ y < gQ.re)
    (P1 := fun y => (gF.re ≤ y ∨ NMem s1.ned y) ∧ y < gR.re) Nc Na Nb Fa.apart Fb.apart
    (fun e he y hy => (Fc.esure e he y hy).resolve_right (fun e => e))
    (fun y hy => ⟨Fa.sure y hy, Ra.out.1.1 y hy⟩) (fun e he y hy => ⟨Fa.esure e he y hy, Ra.out.1.2 e he y hy⟩)
    (fun y hy => ⟨Fb.sure y hy, Rb.out.1.1 y hy⟩) (fun e he y hy => ⟨Fb.esure e he y hy, Rb.out.1.2 e he y hy⟩)
    (fun y a b => by omega) (fun y a b => by omega)
    (fun y a b => by
      obtain ⟨a1 | a1, a2⟩ := a <;> obtain ⟨b1 | b1, b2⟩ := b
      · omega
      · omega
      · have := (hreg y (Or.inl a1)).2; omega
      · exact j01 y a1 b1)

/-- **The entries of every run on `FragX` lie apart.** -/
theorem runX_eap {nm : Nomm} (hf : FragX (S := S) nm) : EApX S Map nm := by
  induction hf with
  | frag hf => exact eapX_frag hf
  | @six c a b hc ha hb ihc iha ihb =>
    intro goal region g0 g1 nex hd hg hD hcount h
    have hc'' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hcount
    have fc : FootX S Map c := runX_foot hc
    have fa : FootX S Map a := runX_foot ha
    have fb : FootX S Map b := runX_foot hb
    cases goal with
    | next sur th =>
      exact eapX_sixN (fragX_pure hc) ihc iha ihb fc fa fb (runX_keeps hc) (runX_keeps ha)
        (runX_keeps hb) hd hg hc'' h
    | done =>
      exact eapX_sixP (goal := CGoal.done) (fragX_pure hc) ihc iha ihb fc fa fb (runX_keeps hc)
        (runX_keeps ha) (runX_keeps hb) trivial hd hg hD hc'' h
    | pick z o =>
      exact eapX_sixP (goal := CGoal.pick z o) (fragX_pure hc) ihc iha ihb fc fa fb (runX_keeps hc)
        (runX_keeps ha) (runX_keeps hb) trivial hd hg hD hc'' h
  | four hp ih => exact eapX_four ih
  | three hp ih => exact eapX_three ih
  | seven hq hp ih => exact eapX_seven hq ih
  | cons hp hq ihp ihq =>
    exact eapX_cons ihp ihq (runX_foot hp) (runX_foot hq) (runX_keeps hp) (runX_keeps hq)
      (fragX_pure hp) (fragX_pure hq)
  | five hp hq ihp ihq =>
    exact eapX_five ihp ihq (runX_foot hp) (runX_foot hq) (runX_keeps hp) (runX_keeps hq)
      (fragX_pure hp)
  | ten hv hq ihv ihq =>
    exact eapX_ten ihv ihq (runX_foot hv) (runX_foot hq) (runX_keeps hv) (runX_keeps hq)
      (fragX_pure hv) (fragX_pure hq)
  | sevenFrom ha _ ihq => exact eapX_sevenFrom ha ihq

/-! ## `LazOK` of the top run, and the final pass with no hypothesis -/

/-- **`LazOK` of the top run** on `FragX`. -/
theorem lazOK_run {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) {nex : NextL S}
    {g1 : Comp.Gen Map} (h : runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1)) :
    LazOK g1.blocks nex.th.there nex.laz := by
  have F := runX_foot hf (goal := CGoal.done) (by simp [gen0]) trivial trivial hc h
  have N := runX_eap hf (goal := CGoal.done) (by simp [gen0]) trivial trivial hc h
  refine ⟨needsApart_root N F.apart, fun e he r hr d => ?_⟩
  rcases defd_of_wroteIn F.wr d with d | ⟨-, -, h1, h2⟩
  · obtain ⟨o, b, hb, -⟩ := defd_iff.mp d
    simp [gen0, HoonMap.get_empty] at hb
  · rcases List.mem_cons.mp he with rfl | he
    · exact h1 hr
    · exact h2 e he hr

variable [MapKeys Map]

/-- **`OptIn` of the n-ary final pass on `FragX`**: the raw blocks of
`finishLF` for every nomm of `FragX` with at most 255 `%6`, nothing baked. -/
theorem optIn_finishLFX {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) {ord : NeedOrd}
    {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : OptIn c'.blocks :=
  optIn_finishLFX_of hf hc (fun _ _ h1 => lazOK_run hf hc h1) hbake h

/-- **`+optimize` keeps the n-ary code of `FragX`.** -/
theorem optimize_keeps_finishLFX (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' s' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') :
    Opt.Keeps c' s' :=
  optimize_keeps_optIn M (optIn_finishLFX hf hc hbake h) ho

/-! ## Two instances -/

/-- `[[6 [0 2] [0 3] [0 1]] [0 1]]`, a `%6` under a cons, is in `FragX`. -/
theorem fragX_consSix : FragX (S := S) (Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1)) :=
  FragX.cons (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial))
    (FragX.frag fun _ => trivial)

/-- `[6 [0 2] [6 [0 6] [0 3] [0 1]] [1 0]]`, a `%6` in a branch of a `%6`,
is in `FragX`. -/
theorem fragX_sixSix : FragX (S := S) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
    (Nomm.n1 (A 0))) :=
  FragX.six (FragX.frag fun _ => trivial)
    (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial))
    (FragX.frag fun _ => trivial)

/-- **A `%6` under a cons**: the raw n-ary code of
`[[6 [0 2] [0 3] [0 1]] [0 1]]` meets `OptIn`, and `+optimize` keeps it. -/
theorem optIn_finishLFX_consSix {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Map := Map) (Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1))
      ord less bake = some c') : OptIn c'.blocks :=
  optIn_finishLFX fragX_consSix (by decide) hbake h

theorem optimize_keeps_consSix (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat} {ord : NeedOrd}
    {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' s' : Straight Map}
    (h : finishLF (S := S) (Map := Map) (Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1))
      ord less bake = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') :
    Opt.Keeps c' s' :=
  optimize_keeps_finishLFX M fragX_consSix (by decide) hbake h ho

/-- **Nested `%6`s**: the raw n-ary code of
`[6 [0 2] [6 [0 6] [0 3] [0 1]] [1 0]]` meets `OptIn`, and `+optimize`
keeps it. -/
theorem optIn_finishLFX_sixSix {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Map := Map) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n1 (A 0))) ord less bake = some c') : OptIn c'.blocks :=
  optIn_finishLFX fragX_sixSix (by decide) hbake h

theorem optimize_keeps_sixSix (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat} {ord : NeedOrd}
    {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' s' : Straight Map}
    (h : finishLF (S := S) (Map := Map) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n1 (A 0))) ord less bake = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') :
    Opt.Keeps c' s' :=
  optimize_keeps_finishLFX M fragX_sixSix (by decide) hbake h ho

end Raw
end SkaModel
end Formalization
