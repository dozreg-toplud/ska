import lemmas.Compiler.CompSect
import lemmas.Compiler.CompSixFork
import lemmas.Ska.CompSixFuel

/-!
# The case `%6` of `+run` under a fork-free `%next` goal: phase S

On a goal `[%next [sur ~ ~] then]` (no fork, no bond) the case `%6` runs
phase S (`sixNextLC_fork_free`, the model's `sixNextSimpleC`):

* the head: `+leap` gives `~` at its first test (`lp6_nil`; the battery of
  `+leap`, door arm `441179`, is cut into that test `lp6Test` and the rest
  `lp6Rest`), so `?^  lep` fails; `+none-equivalent` of the goal's need with
  the bunt sure is `&` (`ne_all`), so the `+kerf`/`+fork` test fails
  (`cr6s_head_nf`);
* `cr6S0` and `cr6S1` under `%next`: `+oo` twice, `+fork-sure` of the sure
  need, the goals `[%next [sur-i ~ ~] ~ o-i]`, `+id` and the branches'
  region (`cr6s_s01`);
* `cr6s_mid`: the two runs;
* the `%next` branch of `cr6S6`: the two asserts that the goals are `%next`
  and the call of `+sect` (`comp_sect`), then `cr6s_p` from `+past-fork` on
  (`cr6s_lyn_n`);
* `km_sect`: `+sect` keeps the counters growing, the mode and the tags.
* `wh_gate`: `+whole` (arm `1372` of `ana`), the first part of the test of
  `+kerf`, is the model's `whole` on every nomm.

**`comp_run_n6_nf`**: the case `%6` under a fork-free `%next` goal with
`GInv`, given the parts (`SixParts`; the branches in the regions
`rid :: region`).  The branch goals meet `GInv` by `forkSure_inv`
(`ginv_ofSure`).  **`res_n6_nf`**: what it returns meets `GRes`, every
register of the result fresh (`sect_labels`: the labels `+sect` returns are
below the label counter).

Compared with the Hoon part by part: no departure.  The Hoon asserts
`?=(%next -.goal-0)` and `?=(%next -.goal-1)` before `+sect`; the model has
no such asserts, since its goals are `%next` by construction.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## The first test of `+leap` -/

/-- The test `&(?=(~ fork.laz) ?=(~ bond.laz))` of `+leap`. -/
def lp6Test : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 51)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The rest of `+leap`, after its first test. -/
def lp6Rest : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 59)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 0) (A 114)) (C (A 0) (A 115)))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 504)) (C (C (A 0) (A 58)) (C (A 0) (A 59)))) (C (A 0) (A 6))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xabffe) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (C (A 0) (A 249)) (C (A 0) (A 30))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 125))) (C (A 0) (A 3)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 125))) (C (A 10) (C (C (A 14) (C (A 0) (A 5))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4)) (C (A 0) (A 14)))) (C (A 0) (A 3))))))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))

/-- The battery of `+leap` (door arm `441179`). -/
def lp6Bat : Noun := C (A 6) (C lp6Test (C (C (A 1) (A 0)) lp6Rest))

def lp6Bunt : Noun :=
  (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 0))))

def lp6Arm : Noun := C (A 8) (C (C (A 1) lp6Bunt) (C (C (A 1) lp6Bat) (C (A 0) (A 1))))

theorem lp6_at : slot? 441179 comp.door = some lp6Arm := by kernel_rfl

theorem lp6_arm (d : Noun) : nock d lp6Arm = some (C lp6Bat (C lp6Bunt d)) := by
  unfold lp6Arm; simp only [nock_exec]

/-- **`+leap` on a need with no fork and no bond** is `~` (the model's
`leap` gives `some none` there). -/
theorem lp6_nil (sN qn rn D : Noun) :
    nock (C lp6Bat (C (C (C sN (C (A 0) (A 0))) (C qn rn)) D)) lp6Bat = some (A 0) := by
  conv => lhs; arg 2; unfold lp6Bat
  unfold lp6Test
  simp [nock_exec]

/-! ## `+sect` keeps the counters, the mode and the tags -/

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem km_sectStep (rid : Nat) (yes : Bool) (made : Map (Nat × List Nat)) (acc : SectAcc Map) (k : Nat) :
    KM (sectStep rid yes made acc k) :=
  KM.of_gen fun g y g' h => by
    unfold sectStep at h
    split at h
    · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
    · split at h
      · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
      · split at h
        · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
        · cases h; exact ⟨Nat.le_succ _, Nat.le_refl _, rfl, rfl⟩

theorem km_foldlM_sectStep (rid : Nat) (yes : Bool) (made : Map (Nat × List Nat)) :
    ∀ (ks : List Nat) (acc : SectAcc Map), KM (ks.foldlM (sectStep rid yes made) acc : CM Map (SectAcc Map))
  | [], acc => KM.pure' acc
  | k :: ks, acc => by
    rw [List.foldlM_cons]
    exact KM.bind' (km_sectStep rid yes made acc k) fun a => km_foldlM_sectStep rid yes made ks a

theorem km_jabBlock (o : Nat) (f : Blob → Option Blob) : KM (jabBlock o f : CM Map Unit) :=
  KM.of_gen fun g y g' h => by
    unfold jabBlock at h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', -, e⟩ := Option.map_eq_some_iff.mp h
    cases e; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

theorem km_sectThread (rid o0end o1end : Nat) (cb cw : Map (Nat × List Nat)) :
    KM (sectThread rid o0end o1end cb cw : CM Map Unit) := by
  have key : ∀ g y g', sectThread rid o0end o1end cb cw g = some (y, g') →
      ∃ m : CM Map Unit, KM m ∧ m g = some (y, g') := by
    intro g y g' h
    unfold sectThread at h
    obtain ⟨b0, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b1, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · split at h
      · cases h
      · obtain ⟨bt, -, h⟩ := Option.bind_eq_some_iff.mp h
        refine ⟨_, ?_, h⟩
        exact KM.bind' (km_foldlM_sectStep _ _ _ _ _) fun _ => KM.bind' (km_foldlM_sectStep _ _ _ _ _) fun _ =>
          KM.bind' (km_jabBlock _ _) fun _ => KM.bind' (km_jabBlock _ _) fun _ => km_jabBlock _ _
    · cases h
  exact ⟨fun g y g' h => by obtain ⟨m, hm, e⟩ := key g y g' h; exact hm.keep g y g' e,
    fun g y g' h => by obtain ⟨m, hm, e⟩ := key g y g' h; exact hm.tags g y g' e⟩

/-- **`+sect` keeps the counters growing, the mode and the tags.** -/
theorem km_sect (nex0 nex1 : NextL S) (o0end o1end : Nat) (rb : List Nat) (cb cw : Map (Nat × List Nat)) :
    KM (sect nex0 nex1 o0end o1end rb cb cw : CM Map (Lazy S × Nat × Nat)) := by
  unfold sect
  split
  · exact KM.fail
  · refine KM.bind' (KM.emit' _) fun _ => KM.bind' (KM.emit' _) fun _ => KM.bind' (KM.setTag' _ _) fun _ =>
      KM.bind' (KM.setTag' _ _) fun _ => KM.bind' KM.get' fun _ => ?_
    dsimp only
    refine KM.ite' _ ?_ (KM.bind' (km_sectThread _ _ _ _ _) fun _ => ?_) <;>
      exact KM.ite' _ KM.fail (KM.ite' _ KM.fail (KM.pure' _))

end

/-! ## The `%next` branch of `cr6S6`: the asserts and `+sect` -/

theorem sect_arm (d : Noun) : nock d sectArm = some (C scBat (C scBunt d)) := by
  unfold sectArm; simp only [nock_exec]

/-- The noun of a goal `[%next laz ~ o]`. -/
theorem next_jmp0_noun (l : Lazy CSet) (o : Nat) :
    (CGoalL.next l (jmp0 o) : CGoalL CSet).toNoun = C (A 0x7478656e) (C l.toNoun (C (A 0) (A o))) := rfl

/-- Phase S under `%next` from the two runs on: `+sect`, then the rest from
`+past-fork` on. -/
noncomputable def sixLynN (env : CallEnv) (msup : Option Nomm) (p : Nomm) (region rb : List Nat) (o0 o1 : Nat)
    (cb cbw : TreapMap mugF (Nat × List Nat)) (nex0 nex1 : NextL CSet) : CM (TreapMap mugF) (NextL CSet) := do
  let (lazy, yes, nuh) ← sect nex0 nex1 o0 o1 rb cb cbw
  sixPM env msup p region lazy yes nuh

/-- **The `%next` branch of `cr6S6`, then `cr6S7`**: the asserts that both
branch goals are `%next`, the call of `+sect` on `[nex-0 nex-1 there.then.goal-0
there.then.goal-1 region-branch cond-before cond-between]`, and the rest
from `+past-fork` on (`cr6s_p`), given the links of `p` and that the needs of
the branches' results are below the counter. -/
theorem cr6s_lyn_n (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region rb : List Nat)
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none)
    (hP : ∀ (yes nuh : Nat) (g' : Gen (TreapMap mugF)), g'.drop = false →
      CompRunAtR (runLC env msup) ctx p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region g')
    (hR : ResFor env msup p region)
    (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF)) (hd : g.drop = false)
    (nex0 nex1 : NextL CSet) (h0 : LAll (LNB g.re) nex0.laz) (h1 : LAll (LNB g.re) nex1.laz)
    (l0 l1 : Lazy CSet) (o0 o1 : Nat) (cb cbw : TreapMap mugF (Nat × List Nat))
    (mono grest sup LEP : Noun) :
    nock (C nex0.goal.toNoun (C (HoonMap.toNoun condValNoun cbw) (C nex1.goal.toNoun
      (C (HoonMap.toNoun condValNoun cb) (C (listNoun A rb)
      (C (C (CGoalL.next l0 (jmp0 o0)).toNoun (CGoalL.next l1 (jmp0 o1)).toNoun) (C LEP
      (crSubj mono (Nomm.n6 p q r).toNoun (C (A 0x7478656e) grest) (listNoun A region) sup
        (compCore g x ctx))))))))) cr6S6
      = (sixLynN env msup p region rb o0 o1 cb cbw nex0 nex1 g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hs := comp_sect (x := x) hc nex0 nex1 o0 o1 rb cb cbw g
  have hD := sect_at
  simp only [scSmp] at hs
  unfold sixLynN
  rw [bind_apply]
  cases e : sect nex0 nex1 o0 o1 rb cb cbw g with
  | none =>
    rw [e] at hs
    simp only [Option.map_none, Option.bind_none]
    rw [next_jmp0_noun, next_jmp0_noun]
    simp only [crSubj, compCore] at hs ⊢
    generalize nex0.goal.toNoun = N0 at hs ⊢
    generalize nex1.goal.toNoun = N1 at hs ⊢
    generalize comp.door = Dr at hs hD ⊢
    unfold cr6S6 cr6SA6
    simp [nock_exec, hD, sect_arm, hs]
  | some v =>
    obtain ⟨⟨lazy, yes, nuh⟩, g'⟩ := v
    rw [e] at hs
    simp only [Option.map_some, Option.bind_some] at hs ⊢
    have hl := sect_lazy e
    obtain ⟨kr, -, kd⟩ := (km_sect nex0 nex1 o0 o1 rb cb cbw).keep _ _ _ e
    subst hl
    have hlz : ∀ y ∈ lregs (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] : Lazy CSet), y < g'.re := by
      intro y hy
      simp only [lregs, fregs, bregs, flattenNeed, Sure.bunt, List.nil_append, List.append_nil,
        List.mem_append] at hy
      rcases hy with hy | hy
      · exact Nat.lt_of_lt_of_le (lnb_regs h0 y hy) kr
      · exact Nat.lt_of_lt_of_le (lnb_regs h1 y hy) kr
    have hlok : LAll CrLok (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] : Lazy CSet) :=
      ⟨fun y hy => by simp [Sure.bunt] at hy; exact absurd hy (HoonSet.mem_empty y),
        ⟨by rw [walkP_irrel]; exact lall_mono (fun _ h => h.1) h0,
         by rw [walkP_irrel]; exact lall_mono (fun _ h => h.1) h1, trivial⟩, trivial⟩
    have hpm := cr6s_p h7 hcode env msup p q r region hpc hpn yes nuh (hP yes nuh) hR x hx g' (kd.trans hd)
      _ hlz hlok mono (C (A 0x7478656e) grest) sup nex0.goal.toNoun (HoonMap.toNoun condValNoun cbw)
      nex1.goal.toNoun (HoonMap.toNoun condValNoun cb) (listNoun A rb)
      (C (CGoalL.next l0 (jmp0 o0)).toNoun (CGoalL.next l1 (jmp0 o1)).toNoun) LEP
    rw [next_jmp0_noun, next_jmp0_noun] at hpm ⊢
    simp only [crSubj, compCore] at hs hpm ⊢
    generalize nex0.goal.toNoun = N0 at hs hpm ⊢
    generalize nex1.goal.toNoun = N1 at hs hpm ⊢
    generalize (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] : Lazy CSet).toNoun = LZ at hs hpm ⊢
    generalize comp.door = Dr at hs hD hpm ⊢
    unfold cr6S6 cr6SA6
    simp [nock_exec, hD, sect_arm, hs, hpm]

/-! ## The head: `+leap` gives `~`, and the `+kerf`/`+fork` test fails -/

/-- The noun of a fork-free goal `%next`. -/
theorem next_mk_noun (s : Sure CSet) (args : List (Option Nat)) (there : Nat) :
    (CGoalL.next (Lazy.mk s [] []) ⟨args, there⟩ : CGoalL CSet).toNoun
      = C (A 0x7478656e) (C (C s.toNoun (C (A 0) (A 0))) (C (listNoun (unitNoun A) args) (A there))) := rfl

/-- **The head of `%6` under a fork-free `%next` goal**: `lep` is `~` (the
first test of `+leap`), `?^  lep` fails, and so does `?&  ?=(%next -.goal)
!(none-equivalent laz.goal(sure *sure))`: phase S (`cr6S0`) runs with `lep`
pushed. -/
theorem cr6s_head_nf (h7 : slot? 7 ctx = some compK) (p q r : Nomm) (s : Sure CSet) (th : Jmp)
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun) :
    nock (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next (Lazy.mk s [] []) th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crDol
      = nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next (Lazy.mk s [] []) th).toNoun
          (listNoun A region) sup (compCore g x ctx))) cr6S0 := by
  have hD := lp6_at
  have hne := ne_all (Lazy.mk Sure.bunt [] [])
  rw [noneEquivalentL_bunt] at hne
  simp only [Lazy.toNoun, Lazy.forksNoun, Lazy.bondsNoun, Sure.toNoun, Sure.bunt, Need.toNoun,
    HoonSet.toNoun_empty, Tag.none] at hne
  rw [Nomm.toNoun, cr_disp_n6, cr6_eq]
  obtain ⟨args, there⟩ := th
  rw [next_mk_noun]
  simp only [crSubj, compCore]
  generalize comp.door = Dr at hD ⊢
  generalize s.toNoun = SN
  generalize listNoun (unitNoun A) args = AN
  unfold cr6Head cr6NoLep cr6Lep cr6T2
  simp [nock_exec, hD, lp6_arm, lp6_nil, h7, compK_ne, ne_arm, hne, loob]

/-! ## The goals of the branches: `cr6S0` and `cr6S1` under `%next` -/

/-- The state after `+oo`. -/
def ooG (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) := { g with bo := g.bo + 1 }

/-- The state after `+id`. -/
def idG (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) := { g with id := g.id + 1 }

theorem ooG_bo (g : Gen (TreapMap mugF)) : (ooG g).bo = g.bo + 1 := rfl

theorem oo_ap (g : Gen (TreapMap mugF)) : (oo : CM (TreapMap mugF) Nat) g = some (g.bo, ooG g) := rfl

theorem idM_ap (g : Gen (TreapMap mugF)) : (idM : CM (TreapMap mugF) Nat) g = some (g.id, idG g) := rfl

theorem comp_oo' (x : GenRest) (g : Gen (TreapMap mugF)) :
    nock (C comp.door (C (genNoun g x) ctx)) comp.oo.arm = some (C (A g.bo) (genNoun (ooG g) x)) :=
  comp_oo ctx x g

theorem comp_id' (x : GenRest) (g : Gen (TreapMap mugF)) :
    nock (C comp.door (C (genNoun g x) ctx)) comp.id.arm = some (C (A g.id) (genNoun (idG g) x)) :=
  comp_id ctx x g

/-- **The goals of the branches under `%next`** (`cr6S0` and `cr6S1`, their
`%next` branches): `+oo` twice, `+fork-sure` of the goal's sure need at
`there.then.goal`, the goals `[%next [sur-i ~ ~] ~ o-i]`, `+id` and the
region `[region-id region]`, then a continuation `K` from `cr6S2` on. -/
theorem cr6s_s01 (hc : CompIn ctx) (p q r : Nomm) (s : Sure CSet) (th : Jmp) (region : List Nat)
    (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (K : Sure CSet → Sure CSet → Nat → Nat → Nat → CM (TreapMap mugF) (NextL CSet))
    (hK : ∀ s0 s1 g3, forkSure s th.there g.bo (g.bo + 1) (ooG (ooG g)) = some ((s0, s1), g3) →
      nock (C (listNoun A (g3.id :: region)) (C (C (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo)).toNoun
          (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))).toNoun) (C (A 0)
          (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next (Lazy.mk s [] []) th).toNoun (listNoun A region) sup
            (compCore (idG g3) x ctx))))) cr6S2
        = (K s0 s1 g.bo (g.bo + 1) g3.id (idG g3)).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next (Lazy.mk s [] []) th).toNoun
        (listNoun A region) sup (compCore g x ctx))) cr6S0
      = ((do
          let o0 ← oo
          let o1 ← oo
          let (s0, s1) ← forkSure s th.there o0 o1
          let rid ← idM
          K s0 s1 o0 o1 rid : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨args, there⟩ := th
  have hfs := comp_fork_sure hc x (ooG (ooG g)) s there g.bo (g.bo + 1)
  have hD1 := comp_oo_at
  have hD2 := fks_at
  have hD3 := comp_id_at
  have ho1 := comp_oo' (ctx := ctx) x g
  have ho2 := comp_oo' (ctx := ctx) x (ooG g)
  rw [ooG_bo] at ho2
  simp only [bind_apply, oo_ap, Option.bind_some, ooG_bo]
  rw [next_mk_noun] at hK ⊢
  simp only at hK ⊢
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

/-! ## The case under a fork-free `%next` goal -/

/-- A goal `[%next [sur ~ ~] ~ o]` meets `GInv` when the looks of `sur` are
not at `0` and its need has no register twice, all below the counter. -/
theorem ginv_ofSure {s : Sure CSet} {o : Nat} {g : Gen (TreapMap mugF)} (hl : CrLok s)
    (hn : ∀ y, NMem s.ned y → y < g.re) (hd : Distinct s.ned) (hdr : g.drop = false) :
    GInv g (CGoalL.next (Lazy.ofSure s) (jmp0 o)) :=
  ⟨⟨⟨⟨hl, hn⟩, trivial, trivial⟩, by rw [lregs_ofSure]; exact (distinct_iff_nodup _).1 hd,
    lkeys_ofSure _, by simp [llabs_ofSure]⟩, hdr, jmpIn_jmp0 _ _⟩

/-- Phase S under `%next` after `+id`: the reads of `cond`, the two runs in
the region `rid :: region`, `+sect` and the rest. -/
noncomputable def sixNfK (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (s0 s1 : Sure CSet) (o0 o1 rid : Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let cb ← getCond
  let nex1 ← runLC env msup r (CGoalL.next (Lazy.ofSure s1) (jmp0 o1)) (rid :: region)
  let cbw ← getCond
  let nex0 ← runLC env msup q (CGoalL.next (Lazy.ofSure s0) (jmp0 o0)) (rid :: region)
  sixLynN env msup p region (rid :: region) o0 o1 cb cbw nex0 nex1

/-- **The model of `%6` under a fork-free `%next` goal** is phase S
(`sixNextLC_fork_free`). -/
theorem runLC_n6_nf (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (s : Sure CSet) (th : Jmp)
    (region : List Nat) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next (Lazy.mk s [] []) th) region : CM (TreapMap mugF) (NextL CSet))
      = (do
          let o0 ← oo
          let o1 ← oo
          let (s0, s1) ← forkSure s th.there o0 o1
          let rid ← idM
          sixNfK env msup p q r region s0 s1 o0 o1 rid) := by
  show sixNextLC env.cod _ _ _ p q r 3 (Lazy.mk s [] []) th region = _
  rw [sixNextLC_fork_free]
  rfl

/-- **The case `%6` of `+run` under a fork-free `%next` goal** (no fork, no
bond: phase S), on every state with the invariant, given the links and
results of the parts (`SixParts`): the test `p` in the case's region, the
branches `q` and `r` in every region `rid :: region` (they run in the
region of the fork). -/
theorem comp_run_n6_nf (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (P : SixParts env msup ctx p region) (Q : ∀ rid, SixParts env msup ctx q (rid :: region))
    (R : ∀ rid, SixParts env msup ctx r (rid :: region))
    (s : Sure CSet) (th : Jmp) (g : Gen (TreapMap mugF)) (hinv : GInv g (CGoalL.next (Lazy.mk s [] []) th)) :
    CompRunAtR (runLC env msup) ctx (Nomm.n6 p q r) (CGoalL.next (Lazy.mk s [] []) th) region g := by
  intro x mono sup hx
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hd : g.drop = false := ginv_drop hinv
  have hl0 : CrLok s := hinv.1.1.1.1
  rw [cr6s_head_nf h7, runLC_n6_nf]
  refine cr6s_s01 hc p q r s th region x g mono sup (sixNfK env msup p q r region) (fun s0 s1 g3 ef => ?_)
  obtain ⟨-, -, d3, lk0, lk1, D0, D1, -, fr⟩ := forkSure_inv ef
  have dI : (idG g3).drop = false := d3.trans hd
  have gi1 : GInv (idG g3) (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))) :=
    ginv_ofSure (fun y hy => hl0 y (lk1 ▸ hy)) (fun y hy => (fr y (Or.inr hy)).2) D1 dI
  have gi0 : GInv (idG g3) (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo)) :=
    ginv_ofSure (fun y hy => hl0 y (lk0 ▸ hy)) (fun y hy => (fr y (Or.inl hy)).2) D0 dI
  exact cr6s_mid (ctx := ctx) env msup p q r (g3.id :: region) (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo))
    (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))) x hx (idG g3) mono
    (CGoalL.next (Lazy.mk s [] []) th).toNoun (listNoun A region) sup (A 0)
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
        (idG g3).cond g1.cond mono (C (Lazy.mk s [] []).toNoun th.toNoun) sup (A 0))

/-! ## What the case returns -/

/-- **The labels `+sect` returns** are below the label counter after it. -/
theorem sect_labels {nex0 nex1 : NextL CSet} {o0 o1 : Nat} {rb : List Nat}
    {cb cw : TreapMap mugF (Nat × List Nat)} {g g' : Gen (TreapMap mugF)} {lz : Lazy CSet} {yes nuh : Nat}
    (h : sect nex0 nex1 o0 o1 rb cb cw g = some ((lz, yes, nuh), g')) : yes < g'.bo ∧ nuh < g'.bo := by
  unfold sect at h
  split at h
  · cases h
  · obtain ⟨o0b, g1, h1, h⟩ := bind_some h
    rw [emit_apply] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨o1b, g2, h2, h⟩ := bind_some h
    rw [emit_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    obtain ⟨_, g4, h4, h⟩ := bind_some h
    obtain ⟨g5, g5', h5, h⟩ := bind_some h
    simp only [get, Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    have b3 := ((KM.setTag' (Map := TreapMap mugF) _ _).keep _ _ _ h3).2.1
    have b4 := ((KM.setTag' (Map := TreapMap mugF) _ _).keep _ _ _ h4).2.1
    simp only [emitted_bo] at b3
    dsimp only at h
    by_cases hd : g4.drop = true
    · rw [if_pos hd] at h
      obtain ⟨e, rfl⟩ := sect_tail h
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      simp only [emitted_bo]
      omega
    · rw [if_neg hd] at h
      obtain ⟨u, g6, h6, h⟩ := bind_some h
      obtain ⟨e, rfl⟩ := sect_tail h
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      have b6 := ((km_sectThread (Map := TreapMap mugF) _ _ _ _ _).keep _ _ _ h6).2.1
      simp only [emitted_bo]
      omega

/-- **What `%6` returns under a fork-free `%next` goal**: `GRes`, given what
the runs of the parts return; every register of the result is fresh (the
branch goals' registers come from `+fork-sure`, the branches' needs are
apart, the fork of `+sect` meets `LInv`). -/
theorem res_n6_nf {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ∀ rid, ResFor env msup q (rid :: region))
    (ihr : ∀ rid, ResFor env msup r (rid :: region))
    (s : Sure CSet) (th : Jmp) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet)
    (hi : GInv g (CGoalL.next (Lazy.mk s [] []) th))
    (h : runLC env msup (Nomm.n6 p q r) (CGoalL.next (Lazy.mk s [] []) th) region g = some (nex, g')) :
    GRes g (CGoalL.next (Lazy.mk s [] []) th) g' nex := by
  have hd := ginv_drop hi
  have hl0 : CrLok s := hi.1.1.1.1
  rw [runLC_n6_nf] at h
  obtain ⟨o0, gA, eA, h⟩ := bind_some h
  rw [oo_ap] at eA
  simp only [Option.some.injEq, Prod.mk.injEq] at eA
  obtain ⟨rfl, rfl⟩ := eA
  obtain ⟨o1, gB, eB, h⟩ := bind_some h
  rw [oo_ap, ooG_bo] at eB
  simp only [Option.some.injEq, Prod.mk.injEq] at eB
  obtain ⟨rfl, rfl⟩ := eB
  obtain ⟨⟨s0, s1⟩, g3, ef, h⟩ := bind_some h
  obtain ⟨r3, b3, d3, lk0, lk1, D0, D1, aps, fr⟩ := forkSure_inv ef
  obtain ⟨rid, gI, eI, h⟩ := bind_some h
  rw [idM_ap] at eI
  simp only [Option.some.injEq, Prod.mk.injEq] at eI
  obtain ⟨rfl, rfl⟩ := eI
  have dI : (idG g3).drop = false := d3.trans hd
  have gi1 : GInv (idG g3) (CGoalL.next (Lazy.ofSure s1) (jmp0 (g.bo + 1))) :=
    ginv_ofSure (fun y hy => hl0 y (lk1 ▸ hy)) (fun y hy => (fr y (Or.inr hy)).2) D1 dI
  have gi0 : GInv (idG g3) (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo)) :=
    ginv_ofSure (fun y hy => hl0 y (lk0 ▸ hy)) (fun y hy => (fr y (Or.inl hy)).2) D0 dI
  unfold sixNfK at h
  obtain ⟨c0, g0, e0, h⟩ := bind_some h
  simp only [getCond, Option.some.injEq, Prod.mk.injEq] at e0
  obtain ⟨-, rfl⟩ := e0
  obtain ⟨nex1, g1, e1, h⟩ := bind_some h
  obtain ⟨c1, g1', e1', h⟩ := bind_some h
  simp only [getCond, Option.some.injEq, Prod.mk.injEq] at e1'
  obtain ⟨-, rfl⟩ := e1'
  obtain ⟨nex0, g2, e2, h⟩ := bind_some h
  obtain ⟨l1, b1, gj1, s1r⟩ := ihr g3.id _ _ g1 nex1 gi1 e1
  have hi0 : GInv g1 (CGoalL.next (Lazy.ofSure s0) (jmp0 g.bo)) :=
    ginv_mono gi0 l1 b1 ((ginv_drop gj1).trans dI.symm)
  obtain ⟨l2, b2, gj2, s2r⟩ := ihq g3.id _ g1 g2 nex0 hi0 e2
  have d2 : g2.drop = false := ginv_drop gj2
  unfold sixLynN at h
  obtain ⟨⟨lz, yes, nuh⟩, g4, e3, h⟩ := bind_some h
  have hlz := sect_lazy e3
  obtain ⟨k4r, k4b, k4d⟩ := (km_sect nex0 nex1 g.bo (g.bo + 1) (g3.id :: region) c0 c1).keep _ _ _ e3
  obtain ⟨hy, hn⟩ := sect_labels e3
  subst hlz
  have d4 : g4.drop = false := k4d.trans d2
  unfold sixPM at h
  obtain ⟨lazy, g7, e7, h⟩ := bind_some h
  simp only [liftO] at e7
  cases epf : Lazy.pastFork env.cod (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p with
  | none => rw [epf] at e7; cases e7
  | some lz' =>
  rw [epf] at e7
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e7
  obtain ⟨rfl, rfl⟩ := e7
  obtain ⟨nexC, g8, e8, h⟩ := bind_some h
  obtain ⟨l8, b8, gi8, s8⟩ := ihp _ g4 g8 nexC
    (show GInv g4 (CGoalL.pick (jmp0 yes) (jmp0 nuh)) from ⟨d4, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) e8
  -- the registers of the branches' needs: fresh, or of the goals of `+fork-sure`
  have rI : (idG g3).re = g3.re := rfl
  have rO : (ooG (ooG g)).re = g.re := rfl
  have bI : (idG g3).bo = g3.bo := rfl
  have f0 : ∀ y ∈ lregs nex0.laz, g1.re ≤ y ∨ NMem s0.ned y := fun y hy => by
    rcases s2r y hy with e | e
    · exact Or.inl e
    · simp only [gregs, lregs_ofSure] at e
      exact Or.inr ((mem_flatten _ _).1 e)
  have f1 : ∀ y ∈ lregs nex1.laz, g3.re ≤ y ∨ NMem s1.ned y := fun y hy => by
    rcases s1r y hy with e | e
    · exact Or.inl e
    · simp only [gregs, lregs_ofSure] at e
      exact Or.inr ((mem_flatten _ _).1 e)
  have lv0 : LInv g4.re g4.bo nex0.laz := linv_mono gj2.1 k4r k4b
  have lv1 : LInv g4.re g4.bo nex1.laz := linv_mono gj1.1 (by omega) (by omega)
  have ap01 : ∀ y ∈ lregs nex0.laz, y ∉ lregs nex1.laz := fun y hy hy' => by
    have hb1 := lnb_regs gj1.1.1 y hy'
    rcases f0 y hy with e | e
    · omega
    · have := (fr y (Or.inl e)).2
      rcases f1 y hy' with e' | e'
      · omega
      · exact aps y e e'
  have lvF := lyn_linv lv0 lv1 ap01 hy hn
  have lvP : LInv g4.re g4.bo lz' := linv_pastFork epf lvF
  have hC : LInv g8.re g8.bo nexC.laz := gi8.1
  have hP8 : LInv g8.re g8.bo lz' := linv_mono lvP l8 b8
  have ap8 : (lregs nexC.laz ++ lregs lz').Nodup := by
    refine List.nodup_append.2 ⟨gi8.1.2.1, lvP.2.1, fun a ha b hb e => ?_⟩
    subst e
    have := lnb_regs lvP.1 a hb
    rcases s8 a ha with e | e
    · omega
    · simp [gregs] at e
  obtain ⟨l9, b9, gi9, s9⟩ := six_tail_res hC hP8 ap8 (ginv_drop gi8) h
  have rg3 : g.re ≤ g3.re := rO ▸ r3
  refine ⟨by omega, by simp only [ooG_bo] at b3; omega, gi9, fun y hy => Or.inl ?_⟩
  rcases s9 y hy with e | e
  · rcases List.mem_append.1 e with e | e
    · rcases s8 y e with e' | e'
      · omega
      · simp [gregs] at e'
    · rw [lregs_pastFork epf] at e
      simp only [lregs, fregs, bregs, flattenNeed, Sure.bunt, List.nil_append, List.append_nil,
        List.mem_append] at e
      rcases e with e | e
      · rcases f0 y e with e' | e'
        · omega
        · have := (fr y (Or.inl e')).1; omega
      · rcases f1 y e with e' | e'
        · omega
        · have := (fr y (Or.inr e')).1; omega
  · omega

/-! ## `+whole`, the first part of the test of `+kerf` -/

/-- The battery of `+whole` (arm `1372` of `ana`). -/
def whBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 4)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 12)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 1) (A 1))))))))))))))))))))))))))))))))))))

def whBunt : Noun :=
  (C (A 0) (A 0))

def whArm : Noun := C (A 8) (C (C (A 1) whBunt) (C (C (A 1) whBat) (C (A 0) (A 1))))

theorem wh_at : slot? 1372 ana = some whArm := by kernel_rfl

theorem wh_arm (d : Noun) : nock d whArm = some (C whBat (C whBunt d)) := by
  unfold whArm; simp only [nock_exec]

/-- **`+whole` on every nomm** is the model's `whole` (the product is in one
register): `&` on `%1` of an atom, `%2`, `%3`, `%4`, `%5`, `%12`; both
branches of `%6`; `q` of `%7`, `%11` and `%mean`; `|` otherwise. -/
theorem wh_gate (K : Noun) : ∀ n : Nomm, nock (C whBat (C n.toNoun K)) whBat = some (loob (whole n))
  | Nomm.cons p q => by
    obtain ⟨a, b, hab⟩ := crc_nomm_cell p
    nock_open whBat
    simp [nock_exec, Nomm.toNoun, hab, whole]
  | Nomm.n0 ax => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.n1 k => by cases k <;> (nock_open whBat; simp [nock_exec, Nomm.toNoun, whole])
  | Nomm.n2 p q info => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.n3 p => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.n4 p => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.n5 p q => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.n6 p q r => by
    have hq := wh_gate K q
    have hr := wh_gate K r
    nock_open whBat
    cases eq : whole q <;> cases er : whole r <;> simp [nock_exec, Nomm.toNoun, whole, hq, hr, eq, er]
  | Nomm.n7 p q => by
    have hq := wh_gate K q
    nock_open whBat; simp [nock_exec, Nomm.toNoun, whole, hq]
  | Nomm.n10 a v q => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.n11s tag q body => by
    have hq := wh_gate K q
    nock_open whBat; simp [nock_exec, Nomm.toNoun, whole, hq]
  | Nomm.n11d tag h q body => by
    have hq := wh_gate K q
    nock_open whBat; simp [nock_exec, Nomm.toNoun, whole, hq]
  | Nomm.n12 p q => by nock_open whBat; simp [nock_exec, Nomm.toNoun, whole]
  | Nomm.mean p b q body k => by
    have hq := wh_gate K q
    nock_open whBat; simp [nock_exec, Nomm.toNoun, whole, hq, Tag.mean]
end Compiler
end Formalization
