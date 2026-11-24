import lemmas.Ska.CompTagKeep
import lemmas.Ska.CompBelowX

/-!
# The tags of a run of `FragX`

README Gaps 12.2 (ninth session), the tag invariant behind the threading of
`+sect`.  `+proxy` records in `cond` the tag of the lazy block it reads in,
and `+sect` skips a key whose tag names the branches' region id.  A run of
`FragX` for a fork-free goal makes no proxy, but its result's lazy blocks are
those a later `[4 p]` makes its proxies in, so their tags matter.

* `Sfx R t`: the tag `t` has the region `R` as a suffix, as every region
  inside a run with region `R` has (`rid :: R` for the branches of a `%6`
  under `%next`).
* `TagStep R g0 g1`: every entry of `tags` that changed from `g0` to `g1`
  has `R` as a suffix.
* `TagR R g0 g1 nex`: `TagStep`, and every lazy block of the result has a
  tag with `R` as a suffix.
* `runX_tags`: every run of `FragX` with region `R` for a fork-free goal
  meets `TagR R` (the hypotheses of `KeepX`), by the induction of
  `runX_keeps`.  The tags are set by `%6` only: the lazy blocks of `%done`
  and `%pick` get the region (`sixGenL`), those of `%next` the region of the
  branches (`+sect`), and every other arm keeps `tags` (`CompTagKeep.lean`).

Tested on the real compiler by `tools/hoon/tagkeep.py`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Tags with a region as a suffix -/

/-- The tag `t` has the region `R` as a suffix. -/
def Sfx (R t : List Nat) : Prop := ∃ pre, t = pre ++ R

theorem sfx_refl (R : List Nat) : Sfx R R := ⟨[], rfl⟩

theorem Sfx.tail {x : Nat} {R t : List Nat} (h : Sfx (x :: R) t) : Sfx R t := by
  obtain ⟨pre, rfl⟩ := h
  exact ⟨pre ++ [x], by simp⟩

theorem Sfx.mem {x : Nat} {R t : List Nat} (h : Sfx (x :: R) t) : x ∈ t := by
  obtain ⟨pre, rfl⟩ := h
  simp

/-- Every entry of `tags` that changed has `R` as a suffix. -/
def TagStep (R : List Nat) (g0 g1 : Gen Map) : Prop :=
  ∀ o t, HoonMap.get g1.tags o = some t → HoonMap.get g0.tags o = some t ∨ Sfx R t

theorem TagStep.of_eq {R : List Nat} {g0 g1 : Gen Map} (h : g1.tags = g0.tags) : TagStep R g0 g1 :=
  fun o t e => Or.inl (by rw [← h]; exact e)

theorem TagStep.trans {R : List Nat} {g0 g1 g2 : Gen Map} (a : TagStep R g0 g1) (b : TagStep R g1 g2) :
    TagStep R g0 g2 :=
  fun o t e => (b o t e).elim (fun e1 => a o t e1) Or.inr

theorem TagStep.mono {R R' : List Nat} (hR : ∀ t, Sfx R' t → Sfx R t) {g0 g1 : Gen Map}
    (h : TagStep R' g0 g1) : TagStep R g0 g1 :=
  fun o t e => (h o t e).imp id (hR t)

/-- A label whose tag has `R` as a suffix keeps such a tag. -/
theorem TagStep.keep {R : List Nat} {g0 g1 : Gen Map} (a : TagStep R g0 g1) {o : Nat}
    (h : ∀ t, HoonMap.get g0.tags o = some t → Sfx R t) : ∀ t, HoonMap.get g1.tags o = some t → Sfx R t :=
  fun t e => (a o t e).elim (h t) id

/-- **What the induction proves of one run.** -/
structure TagR (R : List Nat) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  step : TagStep R g0 g1
  ent : ∀ e ∈ entries nex.laz, ∀ t, HoonMap.get g1.tags e.1 = some t → Sfx R t

/-- `KeepR.pre` for tags (`k` is not used: it keeps the call sites of
`CompBelowX.lean`). -/
theorem TagR.pre {R : List Nat} {g0 g g1 : Gen Map} {nex : NextL S} (_k : Keeps g0 g) (c : g.tags = g0.tags)
    (T : TagR R g g1 nex) : TagR R g0 g1 nex :=
  ⟨(TagStep.of_eq c).trans T.step, T.ent⟩

/-- **Every run of `nm` for a fork-free goal sets tags with its region as a
suffix**, and its result's lazy blocks have such tags. -/
abbrev TagX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    g0.drop = false → GoalIn g0.re goal → sixCount nm ≤ 255 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → TagR region g0 g1 nex

/-! ## The cases -/

theorem tagX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : TagX S Map nm := by
  intro goal region g0 g1 nex hd hg _ h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨TagStep.of_eq ((kt_run nm goal).keep g0 n g hr), fun e he => by simp [Next.toL, entries_ofSure] at he⟩

theorem tagX_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : TagX S Map p) :
    TagX S Map (Nomm.n7 p q) := by
  intro goal region g0 g1 nex hd hg hc h
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag (hq goal)] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := run_keeps q goal g0 g' n hd hg hr
  exact (ihp (goal := CGoal.next n.laz n.th) (k1.dropF hd) n1 (by simp only [sixCount] at hc; omega) h2).pre
    k1 ((kt_run q goal).keep g0 n g' hr)

theorem tagX_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : TagX S Map q) :
    TagX S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region g0 g1 nex hd hg hc h
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha h
  have R := ihq hd hg (by simp only [sixCount] at hc; omega) h1
  refine ⟨R.step, fun e he => ?_⟩
  obtain ⟨l, _, he'⟩ := (fromL_ent axe _ _ hl).mem_right he
  exact R.ent (e.1, l) he'

theorem tagX_tail {p : Nomm} (ih : TagX S Map p) {b : Blob} {arg : Nat} {region : List Nat} {g g1 g2 : Gen Map}
    {o : Nat} {nex : NextL S} (hd : g.drop = false) (hb : BlobIn (· < g.re) b) (ha : arg < g.re)
    (hc : sixCount p ≤ 255) (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region g1 = some (nex, g2)) :
    TagR region g g2 nex := by
  obtain ⟨k1, q1⟩ := keeps_emit hd hb h1
  exact (ih (goal := CGoal.next (lazyReg arg) (jmp0 o)) (k1.dropF hd) ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ hc h).pre
    k1 ((KT.emit' _).keep _ _ _ h1)

theorem tagX_four {p : Nomm} (ih : TagX S Map p) : TagX S Map (Nomm.n4 p) := by
  intro goal region g0 g1 nex hd hg hc h
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
    have R := tagX_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      (show pro < gb.re by omega)) (by omega) hcp h3 h
    exact R.pre (k1.trans k2) (by rw [(KT.re').keep _ _ _ h2, (KT.re').keep _ _ _ h1])
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o', gc, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g0.re → x < gb.re := fun x hx => by omega
    have R := tagX_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      ⟨show pro < gb.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) hcp h3 h
    exact R.pre (k1.trans k2) (by rw [(KT.re').keep _ _ _ h2, (KT.re').keep _ _ _ h1])
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨a, ga, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 h1
    have c1 := (kt_collapseLazyAtom _).keep _ _ _ h1
    obtain ⟨⟨pro, th'⟩, gb, h2, h⟩ := bind_some h
    have hp : Keeps ga gb ∧ pro < gb.re ∧ gb.tags = ga.tags := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨Keeps.refl _, r1 _ _ rfl, rfl⟩
      | none =>
        simp only at h2
        obtain ⟨r, g3, h3, h2⟩ := bind_some h2
        obtain ⟨e3, q3, k3⟩ := keeps_re h3
        have c3 := (KT.re').keep _ _ _ h3
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
    have R := tagX_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
        (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (jmpIn_jmp0 _ _)) (by omega) hcp h4 h
    exact R.pre (k1.trans (k2.trans k3)) (by rw [(KT.re').keep _ _ _ h3, c2, c1])

theorem tagX_three {p : Nomm} (ih : TagX S Map p) : TagX S Map (Nomm.n3 p) := by
  intro goal region g0 g1 nex hd hg hc h
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
    have R := tagX_tail ih ((k1.trans k2).dropF hd)
      (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show r < gb.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) hcp h3 h
    exact R.pre (k1.trans k2) (by rw [(KT.re').keep _ _ _ h2, kt_doneBlocks.keep _ _ _ h1])
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨r, gb, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, gc, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g0.re → x < gb.re := fun x hx => by omega
    have R := tagX_tail ih (k2.dropF hd)
      (blobIn_fin (f := Termin.clq r z o) ⟨show r < gb.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) hcp h3 h
    exact R.pre k2 ((KT.re').keep _ _ _ h2)
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
    have c1 := (kt_collapseLazyAtom _).keep _ _ _ h1
    rcases a with _ | ⟨r, o⟩
    · cases h
    simp only at h
    obtain ⟨⟨z, o'⟩, gb, h2, h⟩ := bind_some h
    have k2 := keeps_forl (k1.dropF hd) (r1 r o rfl) h2
    have c2 := (kt_forl _ _).keep _ _ _ h2
    obtain ⟨r', gc, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨oc, gd, h4, h⟩ := bind_some h
    have R := tagX_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show r' < gc.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) hcp h4 h
    exact R.pre (k1.trans (k2.trans k3)) (by rw [(KT.re').keep _ _ _ h3, c2, c1])

/-! ## `+copy` and the binary cases -/

/-- **`+copy` of a lazy need into the result of a later run** whose lazy
blocks lie apart: the lazy blocks of the copy are those of the two. -/
theorem tag_copyL {R : List Nat} {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S} {mid : Nat}
    (l1 : ∀ e ∈ entries first.laz, mid ≤ e.1) (l2 : ∀ e ∈ entries second, e.1 < mid)
    (t1 : ∀ e ∈ entries first.laz, ∀ t, HoonMap.get g.tags e.1 = some t → Sfx R t)
    (t2 : ∀ e ∈ entries second, ∀ t, HoonMap.get g.tags e.1 = some t → Sfx R t)
    (h : copyL first second g = some (nex, g')) : TagR R g g' nex := by
  have c := (kt_copyL _ _).keep _ _ _ h
  obtain ⟨n, _, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := l1 _ (fork_in_entries he)
      have b := l2 _ (fork_in_entries he')
      omega)
    (fun e he e' he' => by
      have a := l1 _ (bond_in_entries he)
      have b := l2 _ (bond_in_entries he')
      omega) h
  refine ⟨TagStep.of_eq c, fun e he t et => ?_⟩
  rw [c] at et
  rcases List.mem_append.mp ((entries_side_perm _ _ _).mem_iff.mp he) with a | a
  · exact t1 e a t et
  · exact t2 e a t et

theorem tagX_binary {p q : Nomm} (ihp : TagX S Map p) (ihq : TagX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) {region : List Nat}
    {g0 g1 g2 g3 : Gen Map} {nq np : Sure S} {th : Jmp} {nex2 nex1 nex : NextL S}
    (hd : g0.drop = false) (hc : sixCount p + sixCount q ≤ 255) (hnq : NB g0.re nq.ned) (hnp : NB g0.re np.ned)
    (hj : JmpIn (· < g0.re) th)
    (h2 : runL q (CGoalL.next (ofSure nq) th) region g0 = some (nex2, g1))
    (h3 : runL p (CGoalL.next (ofSure np) nex2.th) region g1 = some (nex1, g2))
    (h4 : copyL nex1 nex2.laz g2 = some (nex, g3)) : TagR region g0 g3 nex := by
  have Rq := kq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have Tq := ihq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have d1 := Rq.keeps.dropF hd
  have Rp := kp (goal := CGoal.next np nex2.th) d1 ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩ (by omega) h3
  have Tp := ihp (goal := CGoal.next np nex2.th) d1 ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩ (by omega) h3
  have Tc := tag_copyL (mid := g1.bo) (fun e he => (Rp.labs e he).1) (fun e he => (Rq.labs e he).2)
    Tp.ent (fun e he => Tp.step.keep (Tq.ent e he)) h4
  exact ⟨Tq.step.trans (Tp.step.trans Tc.step), Tc.ent⟩

theorem tagX_consBody {p q : Nomm} (ihp : TagX S Map p) (ihq : TagX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true)
    (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th)) (hc : sixCount p + sixCount q ≤ 255)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : TagR region g0 g1 nex := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hg.1 hg.2 hs2
  have c2 := (kt_split _).keep _ _ _ hs2
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
  exact (tagX_binary ihp ihq kp kq (k2.dropF hd) hc nt (nh.mono (Nat.le_refl _)) (jmpIn_jmp0 _ _) h3 h4 hcp).pre
    k2 c2

theorem tagX_cons {p q : Nomm} (ihp : TagX S Map p) (ihq : TagX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true)
    (hqp : q.pure = true) : TagX S Map (Nomm.cons p q) := by
  intro goal region g0 g1 nex hd hg hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at h
    rw [runL_cons_next] at h
    exact tagX_consBody ihp ihq kp kq hpp hqp hd hg hc' h
  | done =>
    simp only [CGoal.toL] at h
    rw [runL_cons_done] at h
    obtain ⟨r, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o, gb, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keeps_emit (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show r < ga.re by omega)) h2
    rw [runL_cons_next] at h
    exact (tagX_consBody (sur := lazyReg r) ihp ihq kp kq hpp hqp ((k1.trans k2).dropF hd)
      ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ hc' h).pre (k1.trans k2)
      (by rw [(KT.emit' _).keep _ _ _ h2, (KT.re').keep _ _ _ h1])
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
    exact (tagX_binary (nq := Sure.bunt) (np := Sure.bunt) ihp ihq kp kq (k1.dropF hd) hc' (nb_none _) (nb_none _)
      (jmpIn_jmp0 _ _) h3 h4 h).pre k1 ((KT.emit' _).keep _ _ _ h1)

theorem kt_n5Pre (rp rq : Nat) (goal : CGoal S) : KT (n5Pre rp rq goal : CM Map Nat) := by
  cases goal with
  | pick z o => exact KT.emit' _
  | done => exact KT.bind' kt_doneBlocks fun _ => KT.emit' _
  | next laz th =>
    refine KT.bind' (kt_collapseLazyAtom _) fun a => ?_
    split
    · exact KT.ite' _ (KT.emit' _) KT.fail
    · exact KT.bind' (kt_forl _ _) fun _ => KT.emit' _

theorem tagX_five {p q : Nomm} (ihp : TagX S Map p) (ihq : TagX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) : TagX S Map (Nomm.n5 p q) := by
  intro goal region g0 g1 nex hd hg hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  rw [runL_n5_toL] at h
  obtain ⟨rp, ga, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨rq, gb, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  obtain ⟨o, gc, h3, h⟩ := bind_some h
  have k3 := keeps_n5Pre ((k1.trans k2).dropF hd) (hg.mono (by omega)) (by omega) (by omega) h3
  have c3 := (kt_n5Pre _ _ _).keep _ _ _ h3
  obtain ⟨nexq, gd, h4, h⟩ := bind_some h
  obtain ⟨nexq', gd', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, ge, h5, h⟩ := bind_some h
  have l3 := k3.le
  exact (tagX_binary (nq := lazyReg rq) (np := lazyReg rp) ihp ihq kp kq ((k1.trans (k2.trans k3)).dropF hd) hc'
    (nb_this (by omega)) (nb_this (by omega)) (jmpIn_jmp0 _ _) h4 h5 h).pre (k1.trans (k2.trans k3))
    (by rw [c3, (KT.re').keep _ _ _ h2, (KT.re').keep _ _ _ h1])

theorem tagX_ten {a : Nat} {v q : Nomm} (ihv : TagX S Map v) (ihq : TagX S Map q) (kv : KeepX S Map v)
    (kq : KeepX S Map q) (hvp : v.pure = true) (hqp : q.pure = true) : TagX S Map (Nomm.n10 a v q) := by
  intro goal region g0 g1 nex hd hg hc h
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨n, gs'⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := keeps_simpleNext hd hg hs'
  have c1 := (kt_simpleNext _).keep _ _ _ hs'
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [show (Next.toL n : NextL S) = ⟨ofSure n.laz, n.th⟩ from rfl, intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nd, nr⟩ := keeps_into (k1.dropF hd) n1 hs2
  have c2 := (kt_into _ _).keep _ _ _ hs2
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
  have R := tagX_binary ihq ihv kq kv ((k1.trans k2).dropF hd) hc' nd nr (jmpIn_jmp0 _ _) h3 h4 hcp
  exact R.pre (k1.trans k2) (by rw [c2, c1])

/-! ## `%6` -/

/-- The two lazy blocks of `%6` get the region `R'`, and nothing else
changes `tags`. -/
theorem tags_tagged (g : Gen Map) (o : Nat) (R : List Nat) (k : Nat) :
    HoonMap.get (g.tagged o R).tags k =
      if g.drop then HoonMap.get g.tags k else if k = o then some R else HoonMap.get g.tags k := by
  unfold Gen.tagged
  by_cases hd : g.drop = true
  · simp only [hd, if_true]
  · simp only [hd, Bool.false_eq_true, if_false, HoonMap.get_put]

theorem tags_sixGenL (g2 : Gen Map) (t0 t1 : Jmp) (R' : List Nat) (o : Nat) :
    HoonMap.get (sixGenL g2 t0 t1 R').tags o = HoonMap.get g2.tags o ∨
      HoonMap.get (sixGenL g2 t0 t1 R').tags o = some R' := by
  unfold sixGenL
  rw [tags_tagged, tags_tagged, tagged_drop]
  have e : ((g2.emitted ⟨[], [], Termin.hop t0⟩).emitted ⟨[], [], Termin.hop t1⟩).tags = g2.tags := rfl
  have d : ((g2.emitted ⟨[], [], Termin.hop t0⟩).emitted ⟨[], [], Termin.hop t1⟩).drop = g2.drop := rfl
  rw [e, d]
  by_cases hd : g2.drop = true
  · left; simp [hd]
  · simp only [hd, Bool.false_eq_true, if_false]
    split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl

theorem tagStep_sixGenL {R R' : List Nat} (hR : Sfx R R') (g2 : Gen Map) (t0 t1 : Jmp) :
    TagStep R g2 (sixGenL g2 t0 t1 R') := fun o t e => by
  rcases tags_sixGenL g2 t0 t1 R' o with h | h
  · rw [h] at e; exact Or.inl e
  · rw [h] at e; cases e; exact Or.inr hR

theorem tags_sixGenL_y {g2 : Gen Map} (t0 t1 : Jmp) (R' : List Nat) (hd : g2.drop = false) :
    HoonMap.get (sixGenL g2 t0 t1 R').tags g2.bo = some R' ∧
      HoonMap.get (sixGenL g2 t0 t1 R').tags (g2.bo + 1) = some R' := by
  unfold sixGenL
  rw [tags_tagged, tags_tagged, tagged_drop, tags_tagged, tags_tagged, tagged_drop]
  have d : ((g2.emitted ⟨[], [], Termin.hop t0⟩).emitted ⟨[], [], Termin.hop t1⟩).drop = g2.drop := rfl
  rw [d, hd]
  simp

/-- The end of `%6`: the copy of the fork of the branches' needs at the two
lazy blocks `y` and `n` into the need of the test. -/
theorem tagX_sixEnd {R R' : List Nat} (hR : ∀ t, Sfx R' t → Sfx R t) {g0 g1 g2 g3 g4 g5 : Gen Map}
    {xc x0 x1 nex : NextL S} {y n : Nat} {sc sa sb : Nat}
    (Rb : KeepR g0 g1 x1 sb) (Ra : KeepR g1 g2 x0 sa) (kG : Keeps g2 g3) (Rc : KeepR g3 g4 xc sc)
    (Tb : TagR R' g0 g1 x1) (Ta : TagR R' g1 g2 x0) (tG : TagStep R g2 g3) (Tc : TagR R g3 g4 xc)
    (ty : HoonMap.get g3.tags y = some R') (tn : HoonMap.get g3.tags n = some R')
    (hy : g2.bo ≤ y) (hn : y + 1 = n) (hn3 : n + 1 = g3.bo)
    (h : copyL xc (mk (Sure.bunt : Sure S) [((y, x0.laz), (n, x1.laz))] []) g4 = some (nex, g5)) :
    TagR R g0 g5 nex := by
  have b1 := Rb.keeps.bo; have b2 := Ra.keeps.bo; have b3 := kG.bo; have b4 := Rc.keeps.bo
  have s23 : TagStep R g2 g4 := tG.trans Tc.step
  have Tc' := tag_copyL (mid := g3.bo) (fun e he => (Rc.labs e he).1)
    (fun e he => by
      rw [entries_six] at he
      rcases List.mem_append.mp he with he | he <;> rcases List.mem_cons.mp he with e' | he
      · rw [e']; omega
      · have := Ra.labs e he; omega
      · rw [e']; omega
      · have := Rb.labs e he; omega)
    Tc.ent
    (fun e he => by
      rw [entries_six] at he
      rcases List.mem_append.mp he with he | he <;> rcases List.mem_cons.mp he with e' | he
      · rw [e']
        exact Tc.step.keep (fun t et => by rw [ty] at et; cases et; exact hR _ (sfx_refl _))
      · exact s23.keep (fun t et => hR t (Ta.ent e he t et))
      · rw [e']
        exact Tc.step.keep (fun t et => by rw [tn] at et; cases et; exact hR _ (sfx_refl _))
      · exact s23.keep ((Ta.step.mono hR).keep (fun t et => hR t (Tb.ent e he t et)))) h
  exact ⟨(Tb.step.mono hR).trans ((Ta.step.mono hR).trans (s23.trans Tc'.step)), Tc'.ent⟩

/-- **`%6` for `%done` or `%pick`.** -/
theorem tagX_sixP {c a b : Nomm} (hcp : c.pure = true) (ihc : TagX S Map c) (iha : TagX S Map a)
    (ihb : TagX S Map b) (kc : KeepX S Map c) (ka : KeepX S Map a) (kb : KeepX S Map b)
    {goal : CGoal S} (hg' : NotNext goal) {region : List Nat} {g0 g4 : Gen Map}
    {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re goal)
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g4)) :
    TagR region g0 g4 nex := by
  rw [runL_n6_body _ _ _ hg'] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  have Rb := kb hd hg (by omega) h1
  have Tb := ihb hd hg (by omega) h1
  have d1 := Rb.keeps.dropF hd
  have Ra := ka d1 (hg.mono Rb.keeps.le) (by omega) h2
  have Ta := iha d1 (hg.mono Rb.keeps.le) (by omega) h2
  have d2 := Ra.keeps.dropF d1
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have Rc := kc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2)
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ (by omega) h3
  have Tc := ihc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2)
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ (by omega) h3
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  have ty := tags_sixGenL_y (g2 := g2) x0.th x1.th region d2
  exact tagX_sixEnd (fun t ht => ht) Rb Ra kG Rc Tb Ta (tagStep_sixGenL (sfx_refl _) _ _ _) Tc ty.1 ty.2
    (Nat.le_refl _) rfl (by simp) (hrest hbig)

/-- **`%6` for a fork-free `%next`**: the branches run with the region
`rid :: region`, and `+sect` tags its two lazy blocks with it. -/
theorem tagX_sixN {c a b : Nomm} (hcp : c.pure = true) (ihc : TagX S Map c) (iha : TagX S Map a)
    (ihb : TagX S Map b) (kc : KeepX S Map c) (ka : KeepX S Map a) (kb : KeepX S Map b)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th))
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g9)) :
    TagR region g0 g9 nex := by
  simp only [CGoal.toL] at h
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
  obtain ⟨_, _, _, _, _, _, _, hreg, hle, hbo, hdrop, hcond, _, hb0, hb1, hb2, hold⟩ := forkSure_spec hF hd
  have tF : gF.tags = g0.tags := by have := (kt_forkSure _ _ _ _).keep _ _ _ hF; exact this
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
  have hgb : GoalIn ({ gF with id := gF.id + 1 } : Gen Map).re (CGoal.next s1 (jmp0 (g0.bo + 1))) :=
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩
  have Rb0 := kb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF hgb (by omega) hR
  have Tb0 := ihb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF hgb (by omega) hR
  have Rb := Rb0.pre (kF.trans kI) hcond (Nat.le_refl _)
  have Tb : TagR (gF.id :: region) g0 gR x1 := Tb0.pre (kF.trans kI) tF
  have d1 := Rb.keeps.dropF hd
  have lR : gF.re ≤ gR.re := Rb0.keeps.le
  have hga : GoalIn gR.re (CGoal.next s0 (jmp0 g0.bo)) :=
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩
  have Ra := ka (goal := CGoal.next s0 (jmp0 g0.bo)) d1 hga (by omega) hQ
  have Ta := iha (goal := CGoal.next s0 (jmp0 g0.bo)) d1 hga (by omega) hQ
  have d2 := Ra.keeps.dropF d1
  have cR : gR.cond = gF.cond := Rb0.cnd
  rw [cR] at hS
  obtain ⟨ey, en, _, _, el, hsb⟩ := sect_spec d2 (Ra.cnd.trans cR) hS
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := gF.id :: region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have kS := kG.trans (keeps_same hsb)
  have tS : gS.tags = (sixGenL gQ x0.th x1.th (gF.id :: region)).tags := hsb.2.2.2.2.1
  have cS : gS.cond = gQ.cond := hsb.2.2.2.2.2.1.trans cG
  have bS : gS.bo = gQ.bo + 2 := by rw [hsb.2.1]; simp
  have Rc := kc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    (by omega) hC
  have Tc := ihc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    (by omega) hC
  subst el
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  subst ey en
  have ty := tags_sixGenL_y (g2 := gQ) x0.th x1.th (gF.id :: region) d2
  have tG : TagStep region gQ gS := fun o t e => by
    rw [tS] at e; exact tagStep_sixGenL ⟨[gF.id], rfl⟩ gQ x0.th x1.th o t e
  exact tagX_sixEnd (fun t ht => ht.tail) Rb Ra kS Rc Tb Ta tG Tc (by rw [tS]; exact ty.1) (by rw [tS]; exact ty.2)
    (by omega) (by omega) (by omega) (hrest hbig)

/-! ## The induction -/

/-- **On `FragX` every run for a fork-free goal with region `R` sets only
tags with `R` as a suffix, and its result's lazy blocks have such tags**
(with the hypotheses of `KeepX`). -/
theorem runX_tags {nm : Nomm} (hf : FragX (S := S) nm) : TagX S Map nm := by
  induction hf with
  | frag hf => exact tagX_frag hf
  | @six c a b hc' ha' hb' ihc iha ihb =>
    have hcp := fragX_pure hc'
    intro goal region g0 g1 nex hd hg hc h
    have hc'' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hc
    cases goal with
    | next sur th =>
      exact tagX_sixN hcp ihc iha ihb (runX_keeps hc') (runX_keeps ha') (runX_keeps hb') hd hg hc'' h
    | done =>
      exact tagX_sixP (goal := CGoal.done) hcp ihc iha ihb (runX_keeps hc') (runX_keeps ha')
        (runX_keeps hb') trivial hd hg hc'' h
    | pick z o =>
      exact tagX_sixP (goal := CGoal.pick z o) hcp ihc iha ihb (runX_keeps hc') (runX_keeps ha')
        (runX_keeps hb') trivial hd hg hc'' h
  | four _ ih => exact tagX_four ih
  | three _ ih => exact tagX_three ih
  | seven hq _ ih => exact tagX_seven hq ih
  | cons hp hq ihp ihq => exact tagX_cons ihp ihq (runX_keeps hp) (runX_keeps hq) (fragX_pure hp) (fragX_pure hq)
  | five hp hq ihp ihq => exact tagX_five ihp ihq (runX_keeps hp) (runX_keeps hq) (fragX_pure hp)
  | ten hv hq ihv ihq => exact tagX_ten ihv ihq (runX_keeps hv) (runX_keeps hq) (fragX_pure hv) (fragX_pure hq)
  | sevenFrom ha _ ihq => exact tagX_sevenFrom ha ihq

end Comp
end SkaModel
end Formalization
