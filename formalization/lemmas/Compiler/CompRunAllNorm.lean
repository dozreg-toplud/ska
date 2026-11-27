import lemmas.Compiler.CompRunAllNormArms

/-!
# `NormRun` holds on the class with `%6`

`ClnFor env n`: every run of `runLC env msup` of `n`, from a goal whose lazy
need has only `Clean` sure needs (`GCl`), returns a lazy need with only
`Clean` sure needs.  A new invariant beside `res_all6`, by its own
induction over the class (`cln_all6`), with the arms of
`CompRunAllNormArms.lean`; it asks nothing of the state, so `GInv` is not
needed.  `%6`: the three arms of a goal `%next` (`+leap` and `+copy` of
what it took, `+kerf`, `+fork` and `+sect`, the fork-free fork of the sure
need), and the arm of `%done` and `%pick`.

**`normRun_six`**: `NormRun env nm` for every `nm` with `SixOk`, every
`env`.  So `+shape-collapse`'s convergence (`fixRet_bound`) holds on every
final pass of the class, with no hypothesis.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The goal's lazy need has only `Clean` sure needs. -/
def GCl : CGoalL CSet → Prop
  | CGoalL.next laz _ => LAll CleanS laz
  | _ => True

/-- **What a run of `n` keeps**: clean goals give clean lazy needs. -/
def ClnFor (env : CallEnv) (n : Nomm) : Prop :=
  ∀ (msup : Option Nomm) (goal : CGoalL CSet) (region : List Nat) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet),
    runLC env msup n goal region g = some (nex, g') → GCl goal → LAll CleanS nex.laz

theorem gcl_next {goal : CGoalL CSet} (hg : GCl goal) : ∀ laz th, goal = CGoalL.next laz th → LAll CleanS laz :=
  fun laz th e => by subst e; exact hg

theorem cln_n0 (env : CallEnv) (ax : Nat) : ClnFor env (Nomm.n0 ax) := by
  intro msup goal region g g' nex h hg
  simp only [runLC] at h
  split at h
  · exact lc_bombL h
  · obtain ⟨nex0, g1, e1, h⟩ := bind_some h
    have S := lc_simpleNext (gcl_next hg) e1
    split at h
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact S
    · cases hf : Lazy.fromL ax nex0.laz with
      | none => simp [hf] at h
      | some laz' =>
        simp only [hf, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact lc_from ax _ _ S hf

theorem cln_n1 (env : CallEnv) (k : Noun) : ClnFor env (Nomm.n1 k) := by
  intro msup goal region g g' nex h hg
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨r, g1, e1, h⟩ := bind_some h
    obtain ⟨o, g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact lc_bunt 0
  | pick z o =>
    simp only [runLC] at h
    split at h
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact lc_bunt 0
    · split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact lc_bunt 0
      · exact lc_bombL h
  | next laz th =>
    simp only [runLC] at h
    obtain ⟨o, g1, e1, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact lc_bunt 0

theorem cln_n3 {env : CallEnv} {p : Nomm} (ih : ClnFor env p) : ClnFor env (Nomm.n3 p) := by
  intro msup goal region g g' nex h hg
  cases goal with
  | next laz th =>
    simp only [runLC] at h
    split at h
    · exact ih _ _ _ _ _ _ h hg
    · obtain ⟨a, g1, e1, h⟩ := bind_some h
      rcases a with _ | ⟨r, o⟩
      · cases h
      · obtain ⟨⟨z, o'⟩, g2, e2, h⟩ := bind_some h
        obtain ⟨r', g3, e3, h⟩ := bind_some h
        obtain ⟨oc, g4, e4, h⟩ := bind_some h
        exact ih _ _ _ _ _ _ h (lc_reg _ 0)
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨r, g1, e1, h⟩ := bind_some h
    obtain ⟨oc, g2, e2, h⟩ := bind_some h
    exact ih _ _ _ _ _ _ h (lc_reg _ 0)
  | done =>
    simp only [runLC] at h
    obtain ⟨⟨o0, o1⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨r, g2, e2, h⟩ := bind_some h
    obtain ⟨oc, g3, e3, h⟩ := bind_some h
    exact ih _ _ _ _ _ _ h (lc_reg _ 0)

theorem cln_n4 {env : CallEnv} {p : Nomm} (ih : ClnFor env p) : ClnFor env (Nomm.n4 p) := by
  intro msup goal region g g' nex h hg
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨pro, g1, e1, h⟩ := bind_some h
    obtain ⟨arg, g2, e2, h⟩ := bind_some h
    obtain ⟨o, g3, e3, h⟩ := bind_some h
    exact ih _ _ _ _ _ _ h (lc_reg _ 0)
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨pro, g1, e1, h⟩ := bind_some h
    obtain ⟨arg, g2, e2, h⟩ := bind_some h
    obtain ⟨o', g3, e3, h⟩ := bind_some h
    exact ih _ _ _ _ _ _ h (lc_reg _ 0)
  | next laz th =>
    simp only [runLC] at h
    obtain ⟨a, g1, e1, h⟩ := bind_some h
    obtain ⟨⟨pro, th'⟩, g2, e2, h⟩ := bind_some h
    obtain ⟨arg, g3, e3, h⟩ := bind_some h
    obtain ⟨o, g4, e4, h⟩ := bind_some h
    exact ih _ _ _ _ _ _ h (lc_reg _ 0)

theorem cln_n5 {env : CallEnv} {p q : Nomm} (ihp : ClnFor env p) (ihq : ClnFor env q) :
    ClnFor env (Nomm.n5 p q) := by
  intro msup goal region g g' nex h hg
  simp only [runLC] at h
  obtain ⟨rp, g1, e1, h⟩ := bind_some h
  obtain ⟨rq, g2, e2, h⟩ := bind_some h
  obtain ⟨o, g3, e3, h⟩ := bind_some h
  obtain ⟨n2, g4, e4, h⟩ := bind_some h
  obtain ⟨n2', g5, e5, h⟩ := bind_some h
  obtain ⟨n1, g6, e6, e7⟩ := bind_some h
  exact lc_copyL (ihp _ _ _ _ _ _ e6 (lc_reg _ 0)) (lc_past (ihq _ _ _ _ _ _ e4 (lc_reg _ 0)) e5) e7

theorem cln_n2 {env : CallEnv} {p q : Nomm} (ihp : ClnFor env p) (ihq : ClnFor env q) :
    ClnFor env (Nomm.n2 p q Option.none) := by
  intro msup goal region g g' nex h hg
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  exact lc_copyL (ihp _ _ _ _ _ _ h6 (lc_reg _ 0)) (lc_past (ihq _ _ _ _ _ _ h4 (lc_reg _ 0)) h5) h7

theorem cln_n7 {env : CallEnv} {p q : Nomm} (ihp : ClnFor env p) (ihq : ClnFor env q) :
    ClnFor env (Nomm.n7 p q) := by
  intro msup goal region g g' nex h hg
  simp only [runLC] at h
  obtain ⟨nex1, g1, e1, h⟩ := bind_some h
  exact ihp _ _ _ _ _ _ h (ihq _ _ _ _ _ _ e1 hg)

theorem cln_n10 {env : CallEnv} {a : Nat} {v q : Nomm} (ihv : ClnFor env v) (ihq : ClnFor env q) :
    ClnFor env (Nomm.n10 a v q) := by
  intro msup goal region g g' nex h hg
  simp only [runLC] at h
  obtain ⟨nx, g1, e1, h⟩ := bind_some h
  have S := lc_simpleNext (gcl_next hg) e1
  obtain ⟨⟨don, rec, o⟩, g2, e2, h⟩ := bind_some h
  obtain ⟨cd, cr⟩ := lc_intoL S e2
  obtain ⟨nexR, g3, e3, h⟩ := bind_some h
  have cR := lc_past (nex := ⟨rec, jmp0 o⟩) cr e3
  obtain ⟨n2, g4, e4, h⟩ := bind_some h
  obtain ⟨n2', g5, e5, h⟩ := bind_some h
  obtain ⟨n1, g6, e6, e7⟩ := bind_some h
  exact lc_copyL (ihq _ _ _ _ _ _ e6 cR) (lc_past (ihv _ _ _ _ _ _ e4 cd) e5) e7

theorem cln_cons {env : CallEnv} {p q : Nomm} (ihp : ClnFor env p) (ihq : ClnFor env q) :
    ClnFor env (Nomm.cons p q) := by
  intro msup goal region g g' nex h hg
  simp only [runLC] at h
  obtain ⟨goal', g1, e1, h⟩ := bind_some h
  have G : GCl goal' := by
    cases goal with
    | done =>
      simp only at e1
      obtain ⟨r, g5, h5, e1⟩ := bind_some e1
      obtain ⟨o, g6, h6, e1⟩ := bind_some e1
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact lc_reg _ 0
    | pick z o =>
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1; trivial
    | next laz th =>
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1; exact hg
  cases goal' with
  | pick z o =>
    obtain ⟨o', g2, e2, h⟩ := bind_some h
    obtain ⟨n2, g3, e3, h⟩ := bind_some h
    obtain ⟨n2', g4, e4, h⟩ := bind_some h
    obtain ⟨n1, g5, e5, e6⟩ := bind_some h
    exact lc_copyL (ihp _ _ _ _ _ _ e5 (lc_bunt 0)) (lc_past (ihq _ _ _ _ _ _ e3 (lc_bunt 0)) e4) e6
  | done => cases h
  | next laz th =>
    obtain ⟨⟨hed, tel, o⟩, g2, e2, h⟩ := bind_some h
    obtain ⟨ch, ct⟩ := lc_splitL (nex := ⟨laz, th⟩) G e2
    obtain ⟨nexh, g3, e3, h⟩ := bind_some h
    have cH := lc_past (nex := ⟨hed, jmp0 o⟩) ch e3
    obtain ⟨n2, g4, e4, h⟩ := bind_some h
    obtain ⟨n2', g5, e5, h⟩ := bind_some h
    obtain ⟨n1, g6, e6, e7⟩ := bind_some h
    exact lc_copyL (ihp _ _ _ _ _ _ e6 cH) (lc_past (ihq _ _ _ _ _ _ e4 ct) e5) e7

/-! ## `%6` -/

theorem lc_liftPastFork {cod : Bell → Option Bool} {lz lz2 : Lazy CSet} {nom : Nomm} {g g' : Gen (TreapMap mugF)}
    (hc : LAll CleanS lz) (h : (liftO (Lazy.pastFork cod lz nom) : CM (TreapMap mugF) (Lazy CSet)) g = some (lz2, g')) :
    LAll CleanS lz2 := by
  simp only [liftO] at h
  obtain ⟨lz', e1, e2⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact lc_pastFork hc e1

section six
variable {env : CallEnv} {msup : Option Nomm} {p q r : Nomm}
  (ihp : ClnFor env p) (ihq : ClnFor env q) (ihr : ClnFor env r)
include ihp ihq ihr

theorem cln_sixFork {laz : Lazy CSet} {th : Jmp} {region : List Nat} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (hc : LAll CleanS laz)
    (h : sixNextForkC env.cod (runLC env msup p) (runLC env msup q) (runLC env msup r) p laz th region g
      = some (nex, g')) : LAll CleanS nex.laz := by
  simp only [sixNextForkC] at h
  obtain ⟨rc, g1, e1, h⟩ := bind_some h
  obtain ⟨⟨n0, n1⟩, g2, e2, h⟩ := bind_some h
  obtain ⟨c0, c1⟩ := lc_forkL (nex := ⟨laz, th⟩) hc e2
  obtain ⟨rid, g3, e3, h⟩ := bind_some h
  obtain ⟨cb, g4, e4, h⟩ := bind_some h
  obtain ⟨x1, g5, e5, h⟩ := bind_some h
  have d1 := ihr _ _ _ _ _ _ e5 c1
  obtain ⟨cw, g6, e6, h⟩ := bind_some h
  obtain ⟨x0, g7, e7, h⟩ := bind_some h
  have d0 := ihq _ _ _ _ _ _ e7 c0
  obtain ⟨⟨lz, yes, nuh⟩, g8, e8, h⟩ := bind_some h
  have cl := lc_sect d0 d1 e8
  obtain ⟨lz2, g9, e9, h⟩ := bind_some h
  have cl2 := lc_liftPastFork cl e9
  obtain ⟨o, g10, e10, h⟩ := bind_some h
  obtain ⟨lz3, g11, e11, h⟩ := bind_some h
  obtain ⟨nc, g12, e12, h⟩ := bind_some h
  exact lc_copyL (ihp _ _ _ _ _ _ e12 (lc_reg _ 0)) (lc_lazyShut cl2 e11) h

theorem cln_sixSimple {laz : Lazy CSet} {th : Jmp} {region : List Nat} {g g' : Gen (TreapMap mugF)}
    {nex : NextL CSet} (hc : LAll CleanS laz)
    (h : sixNextSimpleC env.cod (runLC env msup p) (runLC env msup q) (runLC env msup r) p laz th region g
      = some (nex, g')) : LAll CleanS nex.laz := by
  have hs : CleanS laz.sure := by obtain ⟨s, f, b⟩ := laz; exact hc.1
  simp only [sixNextSimpleC] at h
  obtain ⟨o0, g1, e1, h⟩ := bind_some h
  obtain ⟨o1, g2, e2, h⟩ := bind_some h
  obtain ⟨⟨s0, s1⟩, g3, e3, h⟩ := bind_some h
  obtain ⟨c0, c1⟩ := cs_forkSure' hs e3
  obtain ⟨rid, g4, e4, h⟩ := bind_some h
  obtain ⟨cb, g5, e5, h⟩ := bind_some h
  obtain ⟨x1, g6, e6, h⟩ := bind_some h
  have d1 := ihr _ _ _ _ _ _ e6 c1
  obtain ⟨cw, g7, e7, h⟩ := bind_some h
  obtain ⟨x0, g8, e8, h⟩ := bind_some h
  have d0 := ihq _ _ _ _ _ _ e8 c0
  obtain ⟨⟨lz, yes, nuh⟩, g9, e9, h⟩ := bind_some h
  have cl := lc_sect d0 d1 e9
  obtain ⟨lz2, g10, e10, h⟩ := bind_some h
  have cl2 := lc_liftPastFork cl e10
  obtain ⟨nc, g11, e11, h⟩ := bind_some h
  have cC := ihp _ _ _ _ _ _ e11 trivial
  split at h
  · exact lc_copyL cC cl2 h
  · obtain ⟨o, g12, e12, h⟩ := bind_some h
    obtain ⟨lz3, g13, e13, h⟩ := bind_some h
    exact lc_copyL (first := ⟨nc.laz, jmp0 o⟩) cC (lc_lazyShut cl2 e13) h

theorem cln_sixNext : ∀ (fuel : Nat) (laz : Lazy CSet) (th : Jmp) (region : List Nat) (g g' : Gen (TreapMap mugF))
    (nex : NextL CSet),
    sixNextLC env.cod (runLC env msup p) (runLC env msup q) (runLC env msup r) p q r fuel laz th region g
      = some (nex, g') → LAll CleanS laz → LAll CleanS nex.laz
  | 0, laz, th, region, g, g', nex, h, _ => by simp [sixNextLC] at h
  | fuel + 1, laz, th, region, g, g', nex, h, hc => by
    cases hl : leap laz q r with
    | none => simp only [sixNextLC, hl] at h; cases h
    | some x =>
      cases x with
      | some y =>
        obtain ⟨rest, bys⟩ := y
        simp only [sixNextLC, hl] at h
        obtain ⟨n1, g1, e1, h⟩ := bind_some h
        obtain ⟨cr, cb⟩ := lc_leap hc hl
        exact lc_copyAll bys n1 g1 g' nex (cln_sixNext fuel rest th region g g1 n1 e1 cr) cb h
      | none =>
        simp only [sixNextLC, hl] at h
        split at h
        · split at h
          · obtain ⟨⟨out, pro⟩, g1, e1, h⟩ := bind_some h
            exact cln_sixNext fuel _ _ region g1 g' nex h (lc_reg _ 0)
          · exact cln_sixFork ihp ihq ihr hc h
        · exact cln_sixSimple ihp ihq ihr hc h

end six

theorem cln_n6 {env : CallEnv} {p q r : Nomm} (ihp : ClnFor env p) (ihq : ClnFor env q) (ihr : ClnFor env r) :
    ClnFor env (Nomm.n6 p q r) := by
  intro msup goal region g g' nex h hg
  cases goal with
  | next laz th =>
    simp only [runLC] at h
    exact cln_sixNext ihp ihq ihr 3 laz th region g g' nex h hg
  | done =>
    simp only [runLC] at h
    obtain ⟨nex1, g1, e1, h⟩ := bind_some h
    have c1 := ihr _ _ _ _ _ _ e1 hg
    obtain ⟨nex0, g2, e2, h⟩ := bind_some h
    have c0 := ihq _ _ _ _ _ _ e2 hg
    obtain ⟨yes, g3, e3, h⟩ := bind_some h
    obtain ⟨nuh, g4, e4, h⟩ := bind_some h
    obtain ⟨_, g5, e5, h⟩ := bind_some h
    obtain ⟨_, g6, e6, h⟩ := bind_some h
    split at h
    · cases h
    split at h
    · cases h
    obtain ⟨lazy, g7, e7, h⟩ := bind_some h
    have cl := lc_liftPastFork (lz := Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [])
      ⟨trivial, ⟨walkP_of_lall _ c0, walkP_of_lall _ c1, trivial⟩, trivial⟩ e7
    obtain ⟨nexC, g8, e8, h⟩ := bind_some h
    have cC := ihp _ _ _ _ _ _ e8 trivial
    split at h
    · exact lc_copyL cC cl h
    · obtain ⟨o, g9, e9, h⟩ := bind_some h
      obtain ⟨lz, g10, e10, h⟩ := bind_some h
      exact lc_copyL (first := ⟨nexC.laz, jmp0 o⟩) cC (lc_lazyShut cl e10) h
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨nex1, g1, e1, h⟩ := bind_some h
    have c1 := ihr _ _ _ _ _ _ e1 hg
    obtain ⟨nex0, g2, e2, h⟩ := bind_some h
    have c0 := ihq _ _ _ _ _ _ e2 hg
    obtain ⟨yes, g3, e3, h⟩ := bind_some h
    obtain ⟨nuh, g4, e4, h⟩ := bind_some h
    obtain ⟨_, g5, e5, h⟩ := bind_some h
    obtain ⟨_, g6, e6, h⟩ := bind_some h
    split at h
    · cases h
    split at h
    · cases h
    obtain ⟨lazy, g7, e7, h⟩ := bind_some h
    have cl := lc_liftPastFork (lz := Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [])
      ⟨trivial, ⟨walkP_of_lall _ c0, walkP_of_lall _ c1, trivial⟩, trivial⟩ e7
    obtain ⟨nexC, g8, e8, h⟩ := bind_some h
    have cC := ihp _ _ _ _ _ _ e8 trivial
    split at h
    · exact lc_copyL cC cl h
    · obtain ⟨o', g9, e9, h⟩ := bind_some h
      obtain ⟨lz, g10, e10, h⟩ := bind_some h
      exact lc_copyL (first := ⟨nexC.laz, jmp0 o'⟩) cC (lc_lazyShut cl e10) h

/-- **Every run of the class with `%6` keeps the sure needs clean.** -/
theorem cln_all6 (env : CallEnv) : ∀ (n : Nomm), SixOk n = true → ClnFor env n
  | Nomm.cons p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact cln_cons (cln_all6 env p h.1) (cln_all6 env q h.2)
  | Nomm.n0 ax, _ => cln_n0 env ax
  | Nomm.n1 k, _ => cln_n1 env k
  | Nomm.n2 p q Option.none, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact cln_n2 (cln_all6 env p h.1) (cln_all6 env q h.2)
  | Nomm.n3 p, h => by
    simp only [SixOk] at h
    exact cln_n3 (cln_all6 env p h)
  | Nomm.n4 p, h => by
    simp only [SixOk] at h
    exact cln_n4 (cln_all6 env p h)
  | Nomm.n5 p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact cln_n5 (cln_all6 env p h.1) (cln_all6 env q h.2)
  | Nomm.n6 p q r, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact cln_n6 (cln_all6 env p h.1.1) (cln_all6 env q h.1.2) (cln_all6 env r h.2)
  | Nomm.n7 p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact cln_n7 (cln_all6 env p h.1) (cln_all6 env q h.2)
  | Nomm.n10 a v q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact cln_n10 (cln_all6 env v h.1.2) (cln_all6 env q h.2)
  | Nomm.n2 _ _ (some _), h => by simp [SixOk] at h
  | Nomm.n11s _ _ _, h => by simp [SixOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [SixOk] at h
  | Nomm.n12 _ _, h => by simp [SixOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [SixOk] at h

/-- **`NormRun` holds on the class with `%6`**, for every `env`: the final
pass's lazy need has no `[%pair [%none ~] [%none ~]]` in any sure need. -/
theorem normRun_six (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) : NormRun env nm := by
  intro nex g1 hr
  exact walkP_mono (fun _ s hs => ordNormal_of_clean s.ned hs) 0 nex.laz (cln_all6 env nm hn _ _ _ _ _ _ hr trivial)

end Compiler
end Formalization
