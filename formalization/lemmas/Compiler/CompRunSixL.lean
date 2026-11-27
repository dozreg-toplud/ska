import lemmas.Compiler.CompSixKerf
import lemmas.Compiler.CompRunSixLInv
import lemmas.Ska.CompSixFuel

/-!
# Phase L of the case `%6`: `+leap` returned a rest

Under a `%next` goal, the case `%6` of `+run` pushes

    =/  lep=(unit [gol=next bys=(list need-lazy)])
      ?.  ?=(%next -.goal)  ~
      =/  l  (leap laz.goal q.nomm r.nomm)
      ?~  l  ~
      `[[%next rest.u.l then.goal] bys.u.l]

(`cr6Lep`) and on `?^  lep` runs phase L (`cr6L0`):

    =^  nex  gen  $(goal gol.u.lep)
    =/  bys=(list need-lazy)  bys.u.lep
    |-  ^-  [next _gen]
    ?~  bys  [nex gen]
    =^  nex-new  gen  (copy nex i.bys)
    $(bys t.bys, nex nex-new)

The parts, with the cells of the Nock (`CompRunSixN.lean`):

* `cr6Lep` (475 characters): `+leap` (door arm `441179`, `lp6Bat`, linked by
  `lp6_leap`), then `[0 [[%next rest then.goal] bys]]`; `cr6l_head` takes the
  head of the case to `cr6L0` with that `lep` pushed.
* `cr6L0`: `$` on the subject of the case with the goal (axis `118`) edited
  to `gol.u.lep`, the state put back (axis `254`), `bys` pushed (`cr6L1`),
  the trap (`cr6L2`, `cr6L3`, its battery `cr6LB`).  `cr6l_eq`.
* The trap `cr6LB`: on `~` the pair `[nex gen]`, else `+copy` (door arm
  `220590`, `comp_copy_all`) of `nex` and `i.bys`, the state put back
  (axis `2046`), `bys` and `nex` edited, the trap again.  `cr6l_loop`: it is
  `copyAll`, given the side conditions of each `+copy` (`CopyChain`).

The model (`sixNextLC` at fuel `3`) is `sixNextLC` at fuel `2` on the rest,
then `copyAll`; under `LeapTwice` the fuel `2` is the fuel `3`
(`sixNextLC_leap_none`), so the model is `runLC` of `%6` on the goal
`[%next rest then]` then `copyAll` (`runLC_n6_l`).  No departure: the Hoon
runs `$` on `gol.u.lep` in the same region with the same state, then copies
the `bys` in list order, as `copyAll` does.

The side conditions of the copies (`copyAll_chain`, `chain_l`): the `bys`
and the rest meet `LInv` and have no register in common (`leapInv` of
`CompRunSixLInv.lean`), the registers of the run's result are fresh or the
rest's (`GRes`), and `+copy` keeps that (`copyL_inv`).  **`comp_run_n6_l`**
takes the link of the case on `[%next rest then]` (`hRe`, any phase) and its
result (`hReR`); `comp_run_n6_l_nf` and `comp_run_n6_l_k` give them by phase
S on a fork-free rest and phase K; phase F plugs in the same way.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The battery of the trap of phase L (the formula that `cr6LA2` quotes). -/
def cr6LB : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 0) (A 14)) (C (A 0) (A 1022))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 2))) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3)))))))))))))))))))

theorem cr6la2_eq : cr6LA2 = C (A 1) cr6LB := rfl

/-! ## The loop of `+copy` over `bys` -/

/-- The side conditions of the `+copy` of each `by` in turn: `CopyH` at the
state of that `+copy`. -/
def CopyChain : Gen (TreapMap mugF) → NextL CSet → List (Lazy CSet) → Prop
  | _, _, [] => True
  | g, nex, b :: rest => CopyH g.re nex.laz b ∧
      ∀ nex' g', copyL nex b g = some (nex', g') → CopyChain g' nex' rest

theorem listN_lazy_nil : listN (([] : List (Lazy CSet)).map Lazy.toNoun) = A 0 := rfl

/-- **The trap of phase L is `copyAll`**, given the side conditions of each
`+copy` (`CopyChain`). -/
theorem cr6l_loop (h7 : slot? 7 ctx = some compK) (x : GenRest) (mono nomm goal region sup LEP : Noun) :
    ∀ (bys : List (Lazy CSet)) (nex : NextL CSet) (g : Gen (TreapMap mugF)), CopyChain g nex bys →
    nock (C cr6LB (C (listN (bys.map Lazy.toNoun)) (C nex.goal.toNoun (C LEP
      (crSubj mono nomm goal region sup (compCore g x ctx)))))) cr6LB
      = (copyAll nex bys g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hD := comp_cp_at
  intro bys
  induction bys with
  | nil =>
    intro nex g _
    rw [listN_lazy_nil]
    simp only [crSubj, compCore]
    nock_open cr6LB
    simp [nock_exec, copyAll, pure, StateT.pure]
  | cons b bs ih =>
    intro nex g hc
    obtain ⟨hH, hk⟩ := hc
    have hcp := comp_copy_all h7 x g nex b hH
    rw [listN_lazy_cons]
    simp only [copyAll]
    rw [bind_apply]
    cases ec : copyL nex b g with
    | none =>
      rw [ec] at hcp
      simp only [crSubj, compCore] at hcp ⊢
      generalize comp.door = Dr at hD hcp ⊢
      nock_open cr6LB
      simp [nock_exec, hD, cr_cp_arm, hcp]
    | some v =>
      obtain ⟨nex', g'⟩ := v
      rw [ec] at hcp
      have ih1 := ih nex' g' (hk nex' g' ec)
      simp only [Option.map_some, Option.bind_some] at hcp ⊢
      simp only [crSubj, compCore] at hcp ih1 ⊢
      generalize comp.door = Dr at hD hcp ih1 ⊢
      nock_open cr6LB
      simp [nock_exec, hD, cr_cp_arm, hcp, ih1]

/-! ## The head: `lep` is `[~ [%next rest then] bys]` -/

/-- **The head of `%6` on the way to phase L**: `+leap` gives `[~ rest bys]`
(given the Nock of `+leap`), so `lep` is `[~ [%next rest then.goal] bys]` and
`?^  lep` holds: `cr6L0` runs with `lep` pushed. -/
theorem cr6l_head (p q r : Nomm) (laz rest : Lazy CSet) (th : Jmp) (bys : List (Lazy CSet))
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (hLp : nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat
      = some (leapN (some (rest, bys)))) :
    nock (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crDol
      = nock (C (C (A 0) (C (CGoalL.next rest th).toNoun (listN (bys.map Lazy.toNoun))))
          (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
            (compCore g x ctx))) cr6L0 := by
  have hD := lp6_at
  simp only [leapN, unitNoun] at hLp
  rw [Nomm.toNoun, cr_disp_n6, cr6_eq]
  simp only [crSubj, compCore, CGoalL.toNoun, Nomm.toNoun] at hLp ⊢
  generalize comp.door = Dr at hD hLp ⊢
  generalize laz.toNoun = LN at hLp ⊢
  generalize rest.toNoun = RN at hLp ⊢
  generalize listN (bys.map Lazy.toNoun) = BN at hLp ⊢
  unfold cr6Head cr6Lep
  simp [nock_exec, hD, lp6_arm, hLp]

/-! ## Phase L: `$` on the rest, then the loop -/

/-- **Phase L** (`cr6L0` ... `cr6L3`): `$` on the subject with the goal
`gol.u.lep` (given its link `hRe`, a model `R` of the run on the rest), the
state put back, then the loop of `+copy` over `bys` (`cr6l_loop`), given the
side conditions of the copies after every result of `R`. -/
theorem cr6l_eq (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (mono nomm goal region sup GR : Noun) (bys : List (Lazy CSet)) (R : CM (TreapMap mugF) (NextL CSet))
    (hRe : nock (crSubj mono nomm GR region sup (compCore g x ctx)) crDol
      = (R g).map fun p => C p.1.goal.toNoun (genNoun p.2 x))
    (hC : ∀ nex g', R g = some (nex, g') → CopyChain g' nex bys) :
    nock (C (C (A 0) (C GR (listN (bys.map Lazy.toNoun)))) (crSubj mono nomm goal region sup (compCore g x ctx)))
      cr6L0
      = ((do let nex ← R; copyAll nex bys : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  rw [bind_apply]
  cases eR : R g with
  | none =>
    rw [eR] at hRe
    simp only [crSubj, compCore] at hRe ⊢
    generalize comp.door = Dr at hRe ⊢
    unfold cr6L0
    simp [nock_exec, cr_bat_dol, hRe]
  | some v =>
    obtain ⟨nex, g'⟩ := v
    rw [eR] at hRe
    have hl := cr6l_loop h7 x mono nomm goal region sup (C (A 0) (C GR (listN (bys.map Lazy.toNoun)))) bys nex g'
      (hC nex g' eR)
    simp only [Option.map_some, Option.bind_some] at hRe ⊢
    simp only [crSubj, compCore] at hRe hl ⊢
    generalize comp.door = Dr at hRe hl ⊢
    generalize listN (bys.map Lazy.toNoun) = BN at hl ⊢
    unfold cr6L0 cr6L1 cr6L2 cr6L3
    rw [cr6la2_eq]
    simp [nock_exec, cr_bat_dol, hRe, hl]

/-! ## The model -/

/-- **The model of phase L**: where `+leap` gives `[~ rest bys]` and, on the
rest, `~` (`LeapTwice`), the case is the case on `[%next rest then]`, then
`copyAll` of `bys`. -/
theorem runLC_n6_l (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (laz rest : Lazy CSet) (th : Jmp)
    (bys : List (Lazy CSet)) (region : List Nat) (hlp : leap laz q r = some (some (rest, bys)))
    (h2 : leap rest q r = some Option.none) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = (do
          let nex ← runLC env msup (Nomm.n6 p q r) (CGoalL.next rest th) region
          copyAll nex bys) := by
  have e : ∀ L J, (runLC env msup (Nomm.n6 p q r) (CGoalL.next L J) region : CM (TreapMap mugF) (NextL CSet))
      = sixNextLC env.cod (runLC env msup p) (runLC env msup q) (runLC env msup r) p q r 3 L J region :=
    fun _ _ => rfl
  rw [e, e, sixNextLC.eq_2]
  simp only [hlp]
  rw [sixNextLC_leap_none env.cod _ _ _ p q r 0 1 rest th region h2]

/-! ## The side conditions of the copies -/

/-- **The copies of the loop meet `CopyChain`**, and what `copyAll` returns:
from a result with `GInv`, `by`s with `LInv` whose registers are apart from
each other and from the result's. -/
theorem copyAll_chain : ∀ (bys : List (Lazy CSet)) (nex : NextL CSet) (g : Gen (TreapMap mugF)),
    GInv g nex.goal → (∀ b ∈ bys, LInv g.re g.bo b) → (bys.flatMap lregs).Nodup →
    (∀ y ∈ lregs nex.laz, y ∉ bys.flatMap lregs) →
    CopyChain g nex bys ∧ ∀ nf g', copyAll nex bys g = some (nf, g') →
      g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ GInv g' nf.goal ∧
        ∀ y ∈ lregs nf.laz, y ∈ lregs nex.laz ∨ y ∈ bys.flatMap lregs ∨ g.re ≤ y
  | [], nex, g, hi, _, _, _ => by
    refine ⟨trivial, fun nf g' h => ?_⟩
    simp only [copyAll, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _, hi, fun y hy => Or.inl hy⟩
  | b :: bs, nex, g, hi, hb, hnd, hap => by
    have hi' : LInv g.re g.bo nex.laz ∧ g.drop = false ∧ JmpIn (· < g.re) nex.th := hi
    obtain ⟨hn, hd, -⟩ := hi'
    have hb0 := hb b List.mem_cons_self
    rw [List.flatMap_cons] at hnd hap
    have hnd' := List.nodup_append.1 hnd
    have hH : CopyH g.re nex.laz b :=
      copyH_of_regs (lnb_regs hn.1) (lnb_regs hb0.1) (fun y hy hy' => hap y hy (List.mem_append_left _ hy'))
    have ap : (lregs nex.laz ++ lregs b).Nodup :=
      List.nodup_append.2 ⟨hn.2.1, hb0.2.1, fun a ha c hc e => hap a ha (List.mem_append_left _ (e ▸ hc))⟩
    have step : ∀ nex' g1, copyL nex b g = some (nex', g1) →
        g.re ≤ g1.re ∧ g.bo ≤ g1.bo ∧ (CopyChain g1 nex' bs ∧ ∀ nf g', copyAll nex' bs g1 = some (nf, g') →
          g1.re ≤ g'.re ∧ g1.bo ≤ g'.bo ∧ GInv g' nf.goal ∧
            ∀ y ∈ lregs nf.laz, y ∈ lregs nex'.laz ∨ y ∈ bs.flatMap lregs ∨ g1.re ≤ y) ∧
          ∀ y ∈ lregs nex'.laz, y ∈ lregs nex.laz ++ lregs b ∨ g.re ≤ y := by
      intro nex' g1 h
      obtain ⟨le, bo, gi, rg⟩ := copyL_inv hn hb0 ap hd h
      refine ⟨le, bo, copyAll_chain bs nex' g1 gi
        (fun b' hb' => linv_mono (hb b' (List.mem_cons_of_mem _ hb')) le bo) hnd'.2.1 (fun y hy hy' => ?_), rg⟩
      rcases rg y hy with e | e
      · rcases List.mem_append.1 e with e | e
        · exact hap y e (List.mem_append_right _ hy')
        · exact hnd'.2.2 y e y hy' rfl
      · obtain ⟨b', hb', hyb⟩ := List.mem_flatMap.1 hy'
        have := lnb_regs (hb b' (List.mem_cons_of_mem _ hb')).1 y hyb
        omega
    refine ⟨⟨hH, fun nex' g1 h => (step nex' g1 h).2.2.1.1⟩, fun nf g' h => ?_⟩
    simp only [copyAll] at h
    obtain ⟨nex', g1, e1, e2⟩ := bind_some h
    obtain ⟨le, bo, ⟨-, hr⟩, rg⟩ := step nex' g1 e1
    obtain ⟨le2, bo2, gi2, rg2⟩ := hr nf g' e2
    refine ⟨Nat.le_trans le le2, Nat.le_trans bo bo2, gi2, fun y hy => ?_⟩
    rcases rg2 y hy with e | e | e
    · rcases rg y e with e' | e'
      · rcases List.mem_append.1 e' with e' | e'
        · exact Or.inl e'
        · exact Or.inr (Or.inl (List.mem_append_left _ e'))
      · exact Or.inr (Or.inr e')
    · exact Or.inr (Or.inl (List.mem_append_right _ e))
    · exact Or.inr (Or.inr (Nat.le_trans le e))

/-- The goal of the run on the rest meets `GInv`. -/
theorem ginv_rest {g : Gen (TreapMap mugF)} {laz rest : Lazy CSet} {th : Jmp} {q r : Nomm}
    {bys : List (Lazy CSet)} (hinv : GInv g (CGoalL.next laz th)) (hli : LeapInv g.re g.bo laz q r)
    (hlp : leap laz q r = some (some (rest, bys))) : GInv g (CGoalL.next rest th) :=
  ⟨(hli rest bys hlp).1, hinv.2.1, hinv.2.2⟩

/-- The copies of phase L after the run on the rest: `CopyChain`, and what
the loop returns, from what the run returns (`GRes`). -/
theorem chain_l {g g1 : Gen (TreapMap mugF)} {laz rest : Lazy CSet} {th : Jmp} {q r : Nomm}
    {bys : List (Lazy CSet)} {nex : NextL CSet} (hli : LeapInv g.re g.bo laz q r)
    (hlp : leap laz q r = some (some (rest, bys))) (hR : GRes g (CGoalL.next rest th) g1 nex) :
    CopyChain g1 nex bys ∧ ∀ nf g', copyAll nex bys g1 = some (nf, g') → GRes g (CGoalL.next laz th) g' nf := by
  obtain ⟨_, hb, hnd, hin⟩ := hli rest bys hlp
  obtain ⟨l1, b1, gi1, rg1⟩ := hR
  have hnd' := List.nodup_append.1 hnd
  have hbr : ∀ y ∈ bys.flatMap lregs, y < g.re := fun y hy => by
    obtain ⟨b', hb', hyb⟩ := List.mem_flatMap.1 hy
    exact lnb_regs (hb b' hb').1 y hyb
  obtain ⟨hc, hres⟩ := copyAll_chain bys nex g1 gi1 (fun b' hb' => linv_mono (hb b' hb') l1 b1) hnd'.2.1
    (fun y hy hy' => by
      rcases rg1 y hy with e | e
      · have := hbr y hy'; omega
      · exact hnd'.2.2 y e y hy' rfl)
  refine ⟨hc, fun nf g' h => ?_⟩
  obtain ⟨l2, b2, gi2, rg2⟩ := hres nf g' h
  refine ⟨Nat.le_trans l1 l2, Nat.le_trans b1 b2, gi2, fun y hy => ?_⟩
  rcases rg2 y hy with e | e | e
  · rcases rg1 y e with e' | e'
    · exact Or.inl e'
    · exact Or.inr (hin y (List.mem_append_left _ e'))
  · exact Or.inr (hin y (List.mem_append_right _ e))
  · exact Or.inl (Nat.le_trans l1 e)

/-! ## The case `%6` in phase L -/

/-- **The case `%6` of `+run` in phase L**: under a `%next` goal with `GInv`
whose `+leap` gives `[~ rest bys]` (`hlp`; the Nock is `lp6_leap`, which needs
`Bake.NoAx0` of the branches), with `LeapTwice`, given the link of the case on the goal `[%next rest then]` in
the same state (`hRe`, whatever phase it takes: `comp_run_n6_nf`,
`comp_run_n6_k`, phase F) and what that run returns (`hReR`): the run on the
rest, then `+copy` of each `by` (`copyAll`). -/
theorem comp_run_n6_l (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p q r : Nomm)
    (region : List Nat) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (htw : LeapTwice laz q r)
    (hRe : CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next rest th) region g)
    (hReR : ∀ nex g', runLC env msup (Nomm.n6 p q r) (CGoalL.next rest th) region g = some (nex, g') →
      GRes g (CGoalL.next rest th) g' nex) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  intro x mono sup hx
  have hli := leapInv hinv.1 hq hr
  have hl : LAll CrLok laz := lall_mono (fun _ h => h.1) hinv.1.1
  have hLp := lp6_leap h7 laz q r hl hq hr g x
  rw [hlp, Option.map_some] at hLp
  rw [cr6l_head p q r laz rest th bys region x g mono sup hLp,
    runLC_n6_l env msup p q r laz rest th bys region hlp (htw rest bys hlp)]
  exact cr6l_eq h7 x g mono _ _ _ sup _ bys _ (hRe x mono sup hx)
    (fun nex g' e => (chain_l hli hlp (hReR nex g' e)).1)

/-- **What `%6` returns in phase L**: `GRes`, given what the run on the rest
returns. -/
theorem res_n6_l {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (laz : Lazy CSet) (th : Jmp) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet)
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (htw : LeapTwice laz q r) (hi : GInv g (CGoalL.next laz th)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (hReR : ∀ nex g', runLC env msup (Nomm.n6 p q r) (CGoalL.next rest th) region g = some (nex, g') →
      GRes g (CGoalL.next rest th) g' nex)
    (h : runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  rw [runLC_n6_l env msup p q r laz rest th bys region hlp (htw rest bys hlp)] at h
  obtain ⟨n1, g1, e1, e2⟩ := bind_some h
  exact (chain_l (leapInv hi.1 hq hr) hlp (hReR n1 g1 e1)).2 nex g' e2

/-! ## The re-entry: phase S on a fork-free rest, phase K -/

/-- **Phase L, then phase S** on a rest with no fork and no bond
(`comp_run_n6_nf`). -/
theorem comp_run_n6_l_nf (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (s : Sure CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (Lazy.mk s [] [], bys)))
    (htw : LeapTwice laz q r) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g :=
  have hli := leapInv hinv.1 hq hr
  comp_run_n6_l h7 env msup p q r region hq hr laz th g hinv _ bys hlp htw
    (comp_run_n6_nf h7 hcode env msup p q r region P Q R s th g (ginv_rest hinv hli hlp))
    (fun nex g' e => res_n6_nf P.res (fun rid => (Q rid).res) (fun rid => (R rid).res) s th g g' nex
      (ginv_rest hinv hli hlp) e)

/-- **Phase L, then phase K** on the rest (`comp_run_n6_k`): its `+leap` is
`~` by `LeapTwice`, in the Nock by `lp6_leap_none`. -/
theorem comp_run_n6_l_k (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (htw : LeapTwice laz q r)
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt rest.fork rest.bond) = false)
    (hkt : kerfTest q r rest = true) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  have hli := leapInv hinv.1 hq hr
  have hi := ginv_rest hinv hli hlp
  have hl : LAll CrLok rest := lall_mono (fun _ h => h.1) hi.1.1
  have h2 := htw rest bys hlp
  exact comp_run_n6_l h7 env msup p q r region hq hr laz th g hinv rest bys hlp htw
    (comp_run_n6_k h7 hcode env msup p q r region P Q R rest th g hi h2 (lp6_leap_none h7 hl hq hr g h2) hne hkt)
    (fun nex g' e => res_n6_k P.res (fun rid => (Q rid).res) (fun rid => (R rid).res) rest th g g' nex hi h2 hne
      hkt e)

end Compiler
end Formalization
