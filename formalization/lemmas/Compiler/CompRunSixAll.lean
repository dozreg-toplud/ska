import lemmas.Ska.CompLeapTwiceRun
import lemmas.Compiler.CompRunSixF

/-!
# The case `%6` on every goal with the invariant

The phases of `%6` under a `%next` goal are linked one by one (S on a
fork-free goal, K, F, L).  Here they are put together.

* **Phase S on a goal whose forks and bonds ask nothing** (`+leap` gives `~`
  and `(none-equivalent laz.goal(sure *sure))` is `&`).  The Hoon then takes
  phase S: `+fork-sure` of `sure.laz.goal` drops the forks and bonds, as the
  model's `sixNextSimpleC` does with `forkSure laz.sure` (lines 4161 to 4180
  of the Hoon; no departure).  `cr6s_head_ne` (the head, with `+leap` in
  full), `cr6s_s01_g` (`cr6s_s01` on any lazy need), `runLC_n6_ne` (the
  model), **`comp_run_n6_ne`**, `res_n6_ne` (its `GRes`, through
  `res_n6_nf`: the model is the one of the goal `[%next [sure ~ ~] then]`).
* **`comp_run_n6_nl`**, `res_n6_nl`: `+leap` gives `~`; the case split on
  `noneEquivalentL` and `kerfTest`, phases S, K, F.
* `comp_run_n6_l_f`, `comp_run_n6_l_ne`: phase L re-entering phase F and
  phase S on a none-equivalent rest (without `LeapTwice`:
  `leapTwice_noAx0`).
* **`comp_run_n6_next`**, `res_n6_next`: every `%next` goal with `GInv`:
  `+leap` crashes (both crash, `cr6_head_crash`), gives `~`
  (`comp_run_n6_nl`) or a rest (phase L, then `comp_run_n6_nl` on the rest,
  whose `+leap` is `~` by `leapTwice_noAx0`).
* **`comp_run_n6_all`**, `res_n6_all`: every goal with `GInv` (`%done` and
  `%pick` by `comp_run_n6_dp`).  Hypotheses: `SixParts` of the three
  operands (the branches in the case's region and in every `rid :: region`)
  and `Bake.NoAx0` of the branches.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## Phase S on a goal whose forks and bonds ask nothing -/

/-- The noun of a `%next` goal, its lazy need spelled out. -/
theorem next_mkg_noun (s : Sure CSet) (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet))
    (args : List (Option Nat)) (there : Nat) :
    (CGoalL.next (Lazy.mk s fk bd) ⟨args, there⟩ : CGoalL CSet).toNoun
      = C (A 0x7478656e) (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))))
          (C (listNoun (unitNoun A) args) (A there))) := by
  rw [cgl_next_noun, lazy_toNoun_mk]; rfl

/-- **The head of `%6` on the way to phase S** under a goal whose need with
the bunt sure is `+none-equivalent`: `lep` is `~` (given the Nock of
`+leap`), `?^  lep` fails, and so does the `?&`: `cr6S0` runs with `lep`
pushed. -/
theorem cr6s_head_ne (h7 : slot? 7 ctx = some compK) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (hLp : nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat = some (A 0))
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = true) :
    nock (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crDol
      = nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
          (compCore g x ctx))) cr6S0 := by
  have hD := lp6_at
  obtain ⟨s, fk, bd⟩ := laz
  have hn := ne_all (Lazy.mk Sure.bunt fk bd)
  simp only [Lazy.fork, Lazy.bond] at hne
  rw [hne] at hn
  simp only [CGoalL.toNoun, lazy_toNoun_mk] at hn hLp ⊢
  simp only [Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none, HoonSet.toNoun_empty] at hn
  rw [Nomm.toNoun, cr_disp_n6, cr6_eq]
  simp only [crSubj, compCore, Nomm.toNoun] at hLp ⊢
  generalize comp.door = Dr at hD hLp ⊢
  generalize s.toNoun = SN at hLp ⊢
  unfold cr6Head cr6NoLep cr6Lep cr6T2
  simp [nock_exec, hD, lp6_arm, hLp, h7, compK_ne, ne_arm, hn, loob]

/-- **The head of `%6` when `+leap` crashes**: the case crashes. -/
theorem cr6_head_crash (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (hLp : nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat = Option.none) :
    nock (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crDol = Option.none := by
  have hD := lp6_at
  obtain ⟨s, fk, bd⟩ := laz
  simp only [CGoalL.toNoun, lazy_toNoun_mk] at hLp ⊢
  rw [Nomm.toNoun, cr_disp_n6, cr6_eq]
  simp only [crSubj, compCore, Nomm.toNoun] at hLp ⊢
  generalize comp.door = Dr at hD hLp ⊢
  generalize s.toNoun = SN at hLp ⊢
  unfold cr6Head cr6Lep
  simp [nock_exec, hD, lp6_arm, hLp]

/-- **`cr6s_s01` on any lazy need**: `+oo` twice, `+fork-sure` of the goal's
sure need (the forks and bonds are dropped), the goals, `+id`, the region,
then a continuation `K` from `cr6S2` on. -/
theorem cr6s_s01_g (hc : CompIn ctx) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp) (region : List Nat)
    (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (K : Sure CSet → Sure CSet → Nat → Nat → Nat → CM (TreapMap mugF) (NextL CSet))
    (hK : ∀ s0 s1 g3, forkSure laz.sure th.there g.bo (g.bo + 1) (ooG (ooG g)) = some ((s0, s1), g3) →
      nock (C (listNoun A (g3.id :: region)) (C (C (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo)).toNoun
          (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))).toNoun) (C (A 0)
          (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
            (compCore (idG g3) x ctx))))) cr6S2
        = (K s0 s1 g.bo (g.bo + 1) g3.id (idG g3)).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun
        (listNoun A region) sup (compCore g x ctx))) cr6S0
      = ((do
          let o0 ← oo
          let o1 ← oo
          let (s0, s1) ← forkSure laz.sure th.there o0 o1
          let rid ← idM
          K s0 s1 o0 o1 rid : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨s, fk, bd⟩ := laz
  obtain ⟨args, there⟩ := th
  have hfs := comp_fork_sure hc x (ooG (ooG g)) s there g.bo (g.bo + 1)
  have hD1 := comp_oo_at
  have hD2 := fks_at
  have hD3 := comp_id_at
  have ho1 := comp_oo' (ctx := ctx) x g
  have ho2 := comp_oo' (ctx := ctx) x (ooG g)
  rw [ooG_bo] at ho2
  simp only [bind_apply, oo_ap, Option.bind_some, ooG_bo]
  rw [next_mkg_noun] at hK ⊢
  simp only [Lazy.sure] at hK ⊢
  generalize listN (fk.map forkE) = FK at hK ⊢
  generalize listN (bd.map bondE) = BD at hK ⊢
  cases ef : forkSure s there g.bo (g.bo + 1) (ooG (ooG g)) with
  | none =>
    rw [ef] at hfs
    simp only [Option.bind_none, Option.map_none]
    simp only [crSubj, compCore] at hfs ⊢
    generalize comp.door = Dr at hD1 hD2 hD3 hfs ho1 ho2 ⊢
    unfold cr6S0 cr6SA0
    simp [nock_exec, hD1, ho1, ho2, hD2, fks_arm, hfs]
  | some v =>
    obtain ⟨⟨s0, s1⟩, g3⟩ := v
    rw [ef] at hfs
    have hk := hK s0 s1 g3 ef
    have hi := comp_id' (ctx := ctx) x g3
    simp only [Option.bind_some, Option.map_some, idM_ap] at hfs ⊢
    rw [next_jmp0_noun, next_jmp0_noun, Lazy.toNoun_ofSure, Lazy.toNoun_ofSure] at hk
    simp only [listNoun, lazyNoun, crSubj, compCore] at hk hfs ⊢
    generalize comp.door = Dr at hD1 hD2 hD3 hfs hk ho1 ho2 hi ⊢
    unfold cr6S0 cr6SA0 cr6S1 cr6SA1
    simp [nock_exec, hD1, ho1, ho2, hD2, fks_arm, hfs, hD3, hi, hk]

/-- **The model of `%6` under a goal whose `+leap` is `~` and whose need
with the bunt sure is `+none-equivalent`**: phase S (`sixNextSimpleC`), the
forks and bonds dropped by `forkSure laz.sure`. -/
theorem runLC_n6_ne (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (hlp : leap laz q r = some Option.none)
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = true) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = (do
          let o0 ← oo
          let o1 ← oo
          let (s0, s1) ← forkSure laz.sure th.there o0 o1
          let rid ← idM
          sixNfK env msup p q r region s0 s1 o0 o1 rid) := by
  show sixNextLC env.cod _ _ _ p q r 3 laz th region = _
  rw [sixNextLC.eq_2]
  simp only [hlp, hne, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

/-- The model on such a goal is the one on `[%next [sure ~ ~] then]`. -/
theorem runLC_n6_ne_eq (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (hlp : leap laz q r = some Option.none)
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = true) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = runLC env msup (Nomm.n6 p q r) (CGoalL.next (Lazy.mk laz.sure [] []) th) region := by
  rw [runLC_n6_ne env msup p q r laz th region hlp hne, runLC_n6_nf]

/-- `GInv` of a goal gives `GInv` of the goal with its sure need only. -/
theorem ginv_sureOnly {g : Gen (TreapMap mugF)} {laz : Lazy CSet} {th : Jmp} (h : GInv g (CGoalL.next laz th)) :
    GInv g (CGoalL.next (Lazy.mk laz.sure [] []) th) := by
  obtain ⟨s, fk, bd⟩ := laz
  obtain ⟨⟨hl, hn, -, -⟩, hd, hj⟩ := h
  refine ⟨⟨⟨hl.1, trivial, trivial⟩, ?_, ⟨List.nodup_nil, List.nodup_nil, trivial, trivial⟩, ?_⟩, hd, hj⟩
  · simp only [lregs, fregs, bregs, List.append_nil] at hn ⊢
    exact (List.nodup_append.1 hn).1
  · simp [llabs, flabs, blabs]

/-- **The case `%6` of `+run` in phase S on a goal whose forks and bonds ask
nothing**: under a `%next` goal with `GInv` whose `+leap` is `~` (`hlp`; the
Nock by `lp6_leap_none`, with `Bake.NoAx0` of the branches) and whose need
with the bunt sure is `+none-equivalent` (`hne`), given the parts
(`SixParts`, the branches in the regions `rid :: region`). -/
theorem comp_run_n6_ne (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region))
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (hlp : leap laz q r = some Option.none) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = true) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  intro x mono sup hx
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hd : g.drop = false := ginv_drop hinv
  have hl : LAll CrLok laz := lall_mono (fun _ h => h.1) hinv.1.1
  have hl0 : CrLok laz.sure := (ginv_sureOnly hinv).1.1.1.1
  rw [cr6s_head_ne h7 p q r laz th region x g mono sup (lp6_leap_none h7 hl hq hr g hlp x hx) hne,
    runLC_n6_ne env msup p q r laz th region hlp hne]
  refine cr6s_s01_g hc p q r laz th region x g mono sup (sixNfK env msup p q r region) (fun s0 s1 g3 ef => ?_)
  obtain ⟨-, -, d3, lk0, lk1, D0, D1, -, fr⟩ := forkSure_inv ef
  have dI : (idG g3).drop = false := d3.trans hd
  have gi1 : GInv (idG g3) (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))) :=
    ginv_ofSure (fun y hy => hl0 y (lk1 ▸ hy)) (fun y hy => (fr y (Or.inr hy)).2) D1 dI
  have gi0 : GInv (idG g3) (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo)) :=
    ginv_ofSure (fun y hy => hl0 y (lk0 ▸ hy)) (fun y hy => (fr y (Or.inl hy)).2) D0 dI
  exact cr6s_mid (ctx := ctx) env msup p q r (g3.id :: region) (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo))
    (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))) x hx (idG g3) mono
    (CGoalL.next laz th).toNoun (listNoun A region) sup (A 0)
    (fun cb cbw nex0 nex1 => sixLynN env msup p region (g3.id :: region) g.bo (g.bo + 1) cb cbw nex0 nex1)
    ((R g3.id).link _ _ gi1)
    (fun nex1 g1 e1 => (Q g3.id).link _ g1 (by
      obtain ⟨l1, b1, gi1', -⟩ := (R g3.id).res _ _ g1 nex1 gi1 e1
      exact ginv_mono gi0 l1 b1 ((ginv_drop gi1').trans dI.symm)))
    (fun nex1 g1 nex0 g2 e1 e2 => by
      obtain ⟨l1, b1, gi1', -⟩ := (R g3.id).res _ _ g1 nex1 gi1 e1
      have hi0 := ginv_mono gi0 l1 b1 ((ginv_drop gi1').trans dI.symm)
      obtain ⟨l2, -, gi2, -⟩ := (Q g3.id).res _ g1 g2 nex0 hi0 e2
      exact cr6s_lyn_n h7 hcode env msup p q r region (g3.id :: region) P.cod P.hin
        (fun yes nuh g' hd' => P.link _ g' ⟨hd', jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) P.res x hx g2 (ginv_drop gi2)
        nex0 nex1 gi2.1.1 (lnb_mono l2 0 gi1'.1.1) (Lazy.ofSure s0) (Lazy.ofSure s1) g.bo (g.bo + 1)
        (idG g3).cond g1.cond mono (C laz.toNoun th.toNoun) sup (A 0))

/-- **What `%6` returns in phase S on such a goal**: `GRes` (by `res_n6_nf`
on the goal with its sure need only). -/
theorem res_n6_ne {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ∀ rid, ResFor env msup q (rid :: region))
    (ihr : ∀ rid, ResFor env msup r (rid :: region))
    (laz : Lazy CSet) (th : Jmp) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet)
    (hi : GInv g (CGoalL.next laz th)) (hlp : leap laz q r = some Option.none)
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = true)
    (h : runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  rw [runLC_n6_ne_eq env msup p q r laz th region hlp hne] at h
  obtain ⟨l, b, gi, fr⟩ := res_n6_nf ihp ihq ihr laz.sure th g g' nex (ginv_sureOnly hi) h
  refine ⟨l, b, gi, fun y hy => ?_⟩
  rcases fr y hy with e | e
  · exact Or.inl e
  · obtain ⟨s, fk, bd⟩ := laz
    simp only [gregs, lregs, fregs, bregs, List.append_nil] at e ⊢
    exact Or.inr (List.mem_append_left _ e)

/-! ## `+leap` gives `~`: phases S, K, F -/

/-- **The case `%6` under a `%next` goal whose `+leap` is `~`**: phase S
when the need with the bunt sure is `+none-equivalent`, else phase K when
the `+kerf` test holds, else phase F. -/
theorem comp_run_n6_nl (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (hlp : leap laz q r = some Option.none) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  cases hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) with
  | true => exact comp_run_n6_ne h7 hcode env msup p q r region P Q R laz th g hinv hlp hq hr hne
  | false =>
    cases hkt : kerfTest q r laz with
    | true => exact comp_run_n6_k h7 hcode env msup p q r region P Q R laz th g hinv hlp hq hr hne hkt
    | false => exact comp_run_n6_f h7 hcode env msup p q r region P Q R laz th g hinv hlp hq hr hne hkt

/-- **What `%6` returns under a `%next` goal whose `+leap` is `~`.** -/
theorem res_n6_nl {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ∀ rid, ResFor env msup q (rid :: region))
    (ihr : ∀ rid, ResFor env msup r (rid :: region))
    (laz : Lazy CSet) (th : Jmp) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet)
    (hi : GInv g (CGoalL.next laz th)) (hlp : leap laz q r = some Option.none)
    (h : runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  cases hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) with
  | true => exact res_n6_ne ihp ihq ihr laz th g g' nex hi hlp hne h
  | false =>
    cases hkt : kerfTest q r laz with
    | true => exact res_n6_k ihp ihq ihr laz th g g' nex hi hlp hne hkt h
    | false => exact res_n6_f ihp ihq ihr laz th g g' nex hi hlp hne hkt h

/-! ## Phase L re-entering phases F and S -/

/-- **Phase L, then phase F** on the rest (`comp_run_n6_f`; its `+leap` is
`~` by `leapTwice_noAx0`). -/
theorem comp_run_n6_l_f (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt rest.fork rest.bond) = false)
    (hkt : kerfTest q r rest = false) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  have hi := ginv_rest hinv (leapInv hinv.1 hq hr) hlp
  have h2 := leapTwice_noAx0 (laz := laz) hq hr rest bys hlp
  exact comp_run_n6_l_tw h7 env msup p q r region hq hr laz th g hinv rest bys hlp
    (comp_run_n6_f h7 hcode env msup p q r region P Q R rest th g hi h2 hq hr hne hkt)
    (fun nex g' e => res_n6_f P.res (fun rid => (Q rid).res) (fun rid => (R rid).res) rest th g g' nex hi h2 hne
      hkt e)

/-- **Phase L, then phase S** on a rest whose forks and bonds ask nothing
(`comp_run_n6_ne`). -/
theorem comp_run_n6_l_ne (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th))
    (rest : Lazy CSet) (bys : List (Lazy CSet)) (hlp : leap laz q r = some (some (rest, bys)))
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt rest.fork rest.bond) = true) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  have hi := ginv_rest hinv (leapInv hinv.1 hq hr) hlp
  have h2 := leapTwice_noAx0 (laz := laz) hq hr rest bys hlp
  exact comp_run_n6_l_tw h7 env msup p q r region hq hr laz th g hinv rest bys hlp
    (comp_run_n6_ne h7 hcode env msup p q r region P Q R rest th g hi h2 hq hr hne)
    (fun nex g' e => res_n6_ne P.res (fun rid => (Q rid).res) (fun rid => (R rid).res) rest th g g' nex hi h2 hne e)

/-! ## Every `%next` goal -/

/-- The model of `%6` when `+leap` crashes. -/
theorem runLC_n6_crash (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (hlp : leap laz q r = Option.none) (g : Gen (TreapMap mugF)) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region g : Option (NextL CSet × Gen (TreapMap mugF)))
      = Option.none := by
  show sixNextLC env.cod _ _ _ p q r 3 laz th region g = _
  rw [sixNextLC.eq_2]
  simp only [hlp]

/-- **The case `%6` of `+run` under every `%next` goal with `GInv`**, given
the parts (`SixParts`) and `Bake.NoAx0` of the branches: `+leap` crashes
(so do the Hoon and the model), gives `~` (`comp_run_n6_nl`: phases S, K,
F), or gives a rest (phase L, `comp_run_n6_l_tw`, re-entering
`comp_run_n6_nl` on the rest, whose `+leap` is `~` by
`leapTwice_noAx0`). -/
theorem comp_run_n6_next (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next laz th)) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next laz th) region g := by
  cases hlp : leap laz q r with
  | none =>
    intro x mono sup hx
    have hl : LAll CrLok laz := lall_mono (fun _ h => h.1) hinv.1.1
    have hLp := lp6_leap h7 laz q r hl hq hr g x
    rw [hlp, Option.map_none] at hLp
    rw [cr6_head_crash p q r laz th region x g mono sup hLp, runLC_n6_crash env msup p q r laz th region hlp g]
    rfl
  | some l =>
    cases l with
    | none => exact comp_run_n6_nl h7 hcode env msup p q r region P Q R hq hr laz th g hinv hlp
    | some v =>
      obtain ⟨rest, bys⟩ := v
      have hi := ginv_rest hinv (leapInv hinv.1 hq hr) hlp
      have h2 := leapTwice_noAx0 (laz := laz) hq hr rest bys hlp
      exact comp_run_n6_l_tw h7 env msup p q r region hq hr laz th g hinv rest bys hlp
        (comp_run_n6_nl h7 hcode env msup p q r region P Q R hq hr rest th g hi h2)
        (fun nex g' e => res_n6_nl P.res (fun rid => (Q rid).res) (fun rid => (R rid).res) rest th g g' nex hi h2 e)

/-- **What `%6` returns under every `%next` goal with `GInv`.** -/
theorem res_n6_next {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ∀ rid, ResFor env msup q (rid :: region))
    (ihr : ∀ rid, ResFor env msup r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (laz : Lazy CSet) (th : Jmp) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet)
    (hi : GInv g (CGoalL.next laz th))
    (h : runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  cases hlp : leap laz q r with
  | none => rw [runLC_n6_crash env msup p q r laz th region hlp g] at h; cases h
  | some l =>
    cases l with
    | none => exact res_n6_nl ihp ihq ihr laz th g g' nex hi hlp h
    | some v =>
      obtain ⟨rest, bys⟩ := v
      have hi' := ginv_rest hi (leapInv hi.1 hq hr) hlp
      have h2 := leapTwice_noAx0 (laz := laz) hq hr rest bys hlp
      exact res_n6_l_tw laz th g g' nex rest bys hlp hi hq hr
        (fun nex' g'' e => res_n6_nl ihp ihq ihr rest th g g'' nex' hi' h2 e) h

/-! ## Every goal -/

/-- **The case `%6` of `+run` on every goal with `GInv`**: `%done` and
`%pick` by `comp_run_n6_dp` (the branches in the case's region), `%next` by
`comp_run_n6_next` (the branches in the regions `rid :: region`). -/
theorem comp_run_n6_all (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q0 : SixParts env msup ctx q region)
    (R0 : SixParts env msup ctx r region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region)) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) goal region g := by
  cases goal with
  | next laz th => exact comp_run_n6_next h7 hcode env msup p q r region P Q R hq hr laz th g hinv
  | done => exact comp_run_n6_dp h7 hcode env msup p q r region P Q0 R0 _ (fun _ _ h => by cases h) g hinv
  | pick z o => exact comp_run_n6_dp h7 hcode env msup p q r region P Q0 R0 _ (fun _ _ h => by cases h) g hinv

/-- **What `%6` returns on every goal with `GInv`.** -/
theorem res_n6_all {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq0 : ResFor env msup q region) (ihr0 : ResFor env msup r region)
    (ihq : ∀ rid, ResFor env msup q (rid :: region)) (ihr : ∀ rid, ResFor env msup r (rid :: region))
    (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) : ResFor env msup (Nomm.n6 p q r) region := by
  intro goal g g' nex hi h
  cases goal with
  | next laz th => exact res_n6_next ihp ihq ihr hq hr laz th g g' nex hi h
  | done => exact res_n6_dp ihp ihq0 ihr0 _ (fun _ _ h => by cases h) g g' nex hi h
  | pick z o => exact res_n6_dp ihp ihq0 ihr0 _ (fun _ _ h => by cases h) g g' nex hi h

end Compiler
end Formalization
