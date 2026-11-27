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

**`comp_run_n6_nf`**: the case `%6` under a fork-free `%next` goal with
`GInv`, given the parts (`SixParts`; the branches in the regions
`rid :: region`).  The branch goals meet `GInv` by `forkSure_inv`
(`ginv_ofSure`).
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
end Compiler
end Formalization
