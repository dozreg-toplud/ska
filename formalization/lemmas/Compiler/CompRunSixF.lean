import lemmas.Compiler.CompForkLoop
import lemmas.Compiler.CompSixKerf
import lemmas.Compiler.CompForkKeep

/-!
# Phase F of `%6`: its head

Phase F (the branch of `%6` under a `%next` goal whose `+leap` is `~`, whose
need with the bunt sure is not `+none-equivalent`, and whose `+kerf` test
says no) is the chain `cr6F0` ... of `CompRunSixN.lean`:

    =^  r-cond  gen  re                        :: cr6F0
    =^  [nex-0 nex-1]  gen  (fork nex r-cond)  :: cr6F1
    =^  region-id  gen  id                     :: cr6F2
    =/  region-branch  [region-id region]      :: cr6F3
    ... the reads of `cond`, the runs of `r` and `q`, `+sect`, `+past-fork`,
    the `%brn` block, `+lazy-shut`, the run of `p`, `+copy`

The model is `sixNextForkC` of `Ska/CompRunLC.lean`, in the same order
(`re`, `forkL`, `idM`, `rid :: region`, `getCond`, the run of `r`, `getCond`,
the run of `q`, `sect`, `pastFork`, `emit` of the `%brn` block, `lazyShut`,
the run of `p` on `[%next [[%this r-cond] ~] ~ ~] ~ o]`, `copyL`).  No
departure.

`cr6f_s03`: the first four pushes (`+re`, `+fork` by `comp_fork_all`, `+id`,
the region), then a continuation from `cr6F4` on.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The state after `+re`. -/
def reG (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) := { g with re := g.re + 1 }

theorem re_ap (g : Gen (TreapMap mugF)) : (re : CM (TreapMap mugF) Nat) g = some (g.re, reG g) := rfl

/-- **The head of phase F** (`cr6F0` ... `cr6F3`): `+re` (the register of
the test), `+fork` of the goal on it (`comp_fork_all`), `+id` and the region
`[region-id region]` of the branches, then a continuation `K` from `cr6F4`
on, given its link on every result of `+fork`. -/
theorem cr6f_s03 (h7 : slot? 7 ctx = some compK) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (x : GenRest) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (K : NextL CSet → NextL CSet → Nat → Nat → CM (TreapMap mugF) (NextL CSet))
    (hK : ∀ n0 n1 g3, forkL ⟨laz, th⟩ g.re (reG g) = some ((n0, n1), g3) →
      nock (C (listNoun A (g3.id :: region)) (C (A g3.id) (C (C n0.goal.toNoun n1.goal.toNoun)
          (C (A g.re) (C (A 0)
            (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
              (compCore (idG g3) x ctx))))))) cr6F4
        = (K n0 n1 g.re g3.id (idG g3)).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun
        (listNoun A region) sup (compCore g x ctx))) cr6F0
      = ((do
          let rc ← re
          let (n0, n1) ← forkL ⟨laz, th⟩ rc
          let rid ← idM
          K n0 n1 rc rid : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hfk := comp_fork_all h7 x (reG g) laz th g.re
  have hD1 := comp_re_at
  have hD2 := fk_at
  have hD3 := comp_id_at
  have hr := comp_re' ctx x g
  simp only [bind_apply, re_ap, Option.bind_some]
  cases ef : forkL ⟨laz, th⟩ g.re (reG g) with
  | none =>
    rw [ef] at hfk
    simp only [Option.bind_none, Option.map_none]
    simp only [crSubj, compCore, reG] at hfk hr ⊢
    generalize comp.door = Dr at hD1 hD2 hD3 hfk hr ⊢
    unfold cr6F0 cr6F1
    simp [nock_exec, hD1, hr, hD2, fk_arm, hfk]
  | some v =>
    obtain ⟨⟨n0, n1⟩, g3⟩ := v
    rw [ef] at hfk
    have hk := hK n0 n1 g3 ef
    have hi := comp_id' (ctx := ctx) x g3
    simp only [Option.bind_some, Option.map_some, idM_ap] at hfk ⊢
    simp only [listNoun, crSubj, compCore, reG] at hk hfk hr ⊢
    generalize comp.door = Dr at hD1 hD2 hD3 hfk hk hr hi ⊢
    unfold cr6F0 cr6F1 cr6F2 cr6F3
    simp [nock_exec, hD1, hr, hD2, fk_arm, hfk, hD3, hi, hk]

/-! ## From `+past-fork` on: `cr6F9` ... `cr6F14` -/

/-- **`+lazy-shut` keeps `LInv`**; its registers are the old ones or fresh. -/
theorem lazyShut_inv {o : Nat} {laz laz' : Lazy CSet} {g g' : Gen (TreapMap mugF)}
    (hl : LInv g.re g.bo laz) (h : lazyShut o laz g = some (laz', g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = g.drop ∧ LInv g'.re g'.bo laz' ∧
      ∀ y ∈ lregs laz', y ∈ lregs laz ∨ g.re ≤ y := by
  unfold lazyShut at h
  split at h
  · rw [pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, hl, fun y hy => Or.inl hy⟩
  · obtain ⟨r, g1, e1, h⟩ := bind_some h
    rw [pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨er, lr⟩ := kern_reg e1
    obtain ⟨kr, kb, kd⟩ := (km_kern (S := CSet) (Map := TreapMap mugF) _ _).keep _ _ _ e1
    refine ⟨kr, kb, kd, linv_reg (r := r) (by omega), fun y hy => Or.inr ?_⟩
    change y ∈ lregs (Lazy.ofSure (lazyReg r : Sure CSet)) at hy
    rw [lregs_reg, List.mem_singleton] at hy
    omega

/-- Phase F from `+past-fork` on, in the model. -/
noncomputable def sixPF (env : CallEnv) (msup : Option Nomm) (p : Nomm) (region : List Nat) (rc : Nat)
    (lazy : Lazy CSet) (yes nuh : Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let lazy ← liftO (Lazy.pastFork env.cod lazy p)
  let o ← emit ⟨[], [], Termin.brn rc (jmp0 yes) (jmp0 nuh)⟩
  let lazy ← lazyShut o lazy
  let nexCond ← runLC env msup p (CGoalL.next (Lazy.ofSure ⟨Need.this rc, HoonSet.empty⟩) (jmp0 o)) region
  copyL nexCond lazy

/-- The goal of the test in phase F meets `GInv`. -/
theorem ginv_rc {rc o : Nat} {g : Gen (TreapMap mugF)} (h : rc < g.re) (hd : g.drop = false) :
    GInv g (CGoalL.next (Lazy.ofSure (⟨Need.this rc, HoonSet.empty⟩ : Sure CSet)) (jmp0 o)) :=
  ginv_ofSure (fun y hy => absurd hy (HoonSet.mem_empty y)) (fun y hy => by simp only [NMem] at hy; omega) trivial hd

/-- **Phase F from `+past-fork` on** (`cr6F9` ... `cr6F14`): `+past-fork`
over `p`, the `%brn` block on `r-cond` by `+emit`, `+lazy-shut` at it, the
run of `p` on `[%next (lazy-from-need this+r-cond) ~ o]`, and `+copy`, given
the link of `p` on that goal and what its runs return, `LInv` of `lazy`,
`r-cond` below the counter and not in `lazy`. -/
theorem cr6f_p (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region : List Nat)
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none) (rc yes nuh : Nat)
    (hP : ∀ (o : Nat) (g' : Gen (TreapMap mugF)),
      GInv g' (CGoalL.next (Lazy.ofSure ⟨Need.this rc, HoonSet.empty⟩) (jmp0 o)) →
      CompRunAtR (runLC env msup) ctx p (CGoalL.next (Lazy.ofSure ⟨Need.this rc, HoonSet.empty⟩) (jmp0 o)) region g')
    (hR : ResFor env msup p region)
    (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF)) (hd : g.drop = false) (hrc : rc < g.re)
    (lazy : Lazy CSet) (hl : LInv g.re g.bo lazy) (hap : rc ∉ lregs lazy)
    (mono goalN sup V8 V7 V6 V5 V4 V3 V2 V1 : Noun) :
    nock (C (C lazy.toNoun (C (A yes) (A nuh))) (C V8 (C V7 (C V6 (C V5 (C V4 (C V3 (C V2 (C (A rc) (C V1
      (crSubj mono (Nomm.n6 p q r).toNoun goalN (listNoun A region) sup (compCore g x ctx)))))))))))) cr6F9
      = (sixPF env msup p region rc lazy yes nuh g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  have hpf := comp_past_fork h7 hcode (genNoun g x) lazy p hpn
  have hD1 := pf_at
  have hD2 := comp_cp_at
  have hD3 := comp_emit_at
  have hD4 := lsh_at
  unfold sixPF
  rw [pastFork_cod hpc]
  simp only [compCore] at hpf ⊢
  cases e1 : Lazy.pastFork noCode lazy p with
  | none =>
    rw [e1] at hpf
    generalize comp.door = Dr at hpf hD1 hD2 hD3 hD4 ⊢
    unfold cr6F9
    simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind]
  | some lazy' =>
  rw [e1] at hpf
  simp only [Option.map_some] at hpf
  have hl' : LInv g.re g.bo lazy' := linv_pastFork e1 hl
  have hap' : rc ∉ lregs lazy' := by rw [lregs_pastFork e1]; exact hap
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.brn rc (jmp0 yes) (jmp0 nuh)⟩
  have hre := cf_emitG_re ⟨[], [], Termin.brn rc (jmp0 yes) (jmp0 nuh)⟩ g
  have hbo := cf_emitG_bo ⟨[], [], Termin.brn rc (jmp0 yes) (jmp0 nuh)⟩ g
  have hdr : (cfEmitG ⟨[], [], Termin.brn rc (jmp0 yes) (jmp0 nuh)⟩ g).drop = false := by
    rw [cf_emitG_drop]; exact hd
  generalize hg1 : cfEmitG ⟨[], [], Termin.brn rc (jmp0 yes) (jmp0 nuh)⟩ g = g1 at he hre hbo hdr
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.brn, cr_jmp0] at he
  have hsh := comp_lazy_shut h7 x hx g1 g.bo lazy' (walk_mdP hx _ (lall_mono (fun _ h => h.1) hl'.1))
  simp only [compCore] at hsh
  cases e3 : lazyShut g.bo lazy' g1 with
  | none =>
    rw [e3] at hsh
    generalize comp.door = Dr at hpf hD1 hD2 hD3 hD4 he hsh ⊢
    unfold cr6F9 cr6F10 cr6F11
    simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind, hD3, comp_emit_arm, he,
      cf_emit_g, hg1, hD4, lsh_arm, hsh, e3, Blob.toNoun, listNoun, Termin.toNoun, Tag.brn, cr_jmp0]
  | some v3 =>
  obtain ⟨lazy'', g2⟩ := v3
  rw [e3] at hsh
  simp only [Option.map_some] at hsh
  obtain ⟨k2r, k2b, k2d, hl2, f2⟩ := lazyShut_inv (linv_mono hl' (by omega) (by omega)) e3
  have hd2 : g2.drop = false := k2d.trans hdr
  have hq1 := hP g.bo g2 (ginv_rc (by omega) hd2) x mono sup hx
  rw [goalK_noun] at hq1
  simp only [crSubj, compCore] at hq1
  cases e4 : runLC (S := CSet) (Map := TreapMap mugF) env msup p
      (CGoalL.next (Lazy.ofSure ⟨Need.this rc, HoonSet.empty⟩) (jmp0 g.bo)) region g2 with
  | none =>
    rw [e4] at hq1
    generalize comp.door = Dr at hpf hD1 hD2 hD3 hD4 he hsh hq1 ⊢
    unfold cr6F9 cr6F10 cr6F11 cr6F12
    simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind, hD3, comp_emit_arm, he,
      cf_emit_g, hg1, hD4, lsh_arm, hsh, e3, hq1, e4, cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate,
      Blob.toNoun, listNoun, Termin.toNoun, Tag.brn, cr_jmp0]
  | some v4 =>
  obtain ⟨nexCond, g3⟩ := v4
  rw [e4] at hq1
  simp only [Option.map_some] at hq1
  obtain ⟨l3, -, gi3, fr3⟩ := hR _ g2 g3 nexCond (ginv_rc (by omega) hd2) e4
  have hf : ∀ y ∈ lregs nexCond.laz, y < g3.re := lnb_regs gi3.1.1
  have hs : ∀ y ∈ lregs lazy'', y < g3.re := fun y hy => by have := lnb_regs hl2.1 y hy; omega
  have ap : ∀ y ∈ lregs nexCond.laz, y ∉ lregs lazy'' := fun y hy hy' => by
    have := lnb_regs hl2.1 y hy'
    rcases fr3 y hy with e | e
    · omega
    · change y ∈ lregs (Lazy.ofSure (lazyReg rc : Sure CSet)) at e
      rw [lregs_reg, List.mem_singleton] at e
      subst e
      rcases f2 _ hy' with e' | e'
      · exact hap' e'
      · omega
  have hcp := comp_copy_all h7 x g3 nexCond lazy'' (copyH_of_regs hf hs ap)
  simp only [compCore] at hcp
  generalize comp.door = Dr at hpf hD1 hD2 hD3 hD4 he hsh hq1 hcp ⊢
  unfold cr6F9 cr6F10 cr6F11 cr6F12 cr6F13 cr6F14
  simp [nock_exec, crSubj, Nomm.toNoun, hD1, pf_arm, hpf, liftO, bind, StateT.bind, hD3, comp_emit_arm, he,
    cf_emit_g, hg1, hD4, lsh_arm, hsh, e3, hq1, e4, cr_bat_dol, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hD2,
    cr_cp_arm, hcp, Blob.toNoun, listNoun, Termin.toNoun, Tag.brn, cr_jmp0]

/-! ## `+sect`: `cr6F8` -/

/-- Phase F from the two runs on: `+sect`, then the rest from `+past-fork` on. -/
noncomputable def sixLynF (env : CallEnv) (msup : Option Nomm) (p : Nomm) (region rb : List Nat) (rc o0 o1 : Nat)
    (cb cbw : TreapMap mugF (Nat × List Nat)) (nex0 nex1 : NextL CSet) : CM (TreapMap mugF) (NextL CSet) := do
  let (lazy, yes, nuh) ← sect nex0 nex1 o0 o1 rb cb cbw
  sixPF env msup p region rc lazy yes nuh

/-- **`+sect` in phase F** (`cr6F8`, no asserts before it), then the rest
from `+past-fork` on (`cr6f_p`), given the links of `p`, `LInv` of the two
branch needs, apart, and `r-cond` below the counter and in neither. -/
theorem cr6f_lyn (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (region rb : List Nat)
    (hpc : hinted env.cod p = hinted noCode p) (hpn : hinted noCode p ≠ Option.none) (rc : Nat)
    (hP : ∀ (o : Nat) (g' : Gen (TreapMap mugF)),
      GInv g' (CGoalL.next (Lazy.ofSure ⟨Need.this rc, HoonSet.empty⟩) (jmp0 o)) →
      CompRunAtR (runLC env msup) ctx p (CGoalL.next (Lazy.ofSure ⟨Need.this rc, HoonSet.empty⟩) (jmp0 o)) region g')
    (hR : ResFor env msup p region)
    (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF)) (hd : g.drop = false) (hrc : rc < g.re)
    (nex0 nex1 : NextL CSet) (h0 : LInv g.re g.bo nex0.laz) (h1 : LInv g.re g.bo nex1.laz)
    (ap01 : ∀ y ∈ lregs nex0.laz, y ∉ lregs nex1.laz) (a0 : rc ∉ lregs nex0.laz) (a1 : rc ∉ lregs nex1.laz)
    (l0 l1 : Lazy CSet) (o0 o1 rid : Nat) (cb cbw : TreapMap mugF (Nat × List Nat)) (mono goalN sup : Noun) :
    nock (C nex0.goal.toNoun (C (HoonMap.toNoun condValNoun cbw) (C nex1.goal.toNoun
      (C (HoonMap.toNoun condValNoun cb) (C (listNoun A rb) (C (A rid)
      (C (C (CGoalL.next l0 (jmp0 o0)).toNoun (CGoalL.next l1 (jmp0 o1)).toNoun) (C (A rc) (C (A 0)
      (crSubj mono (Nomm.n6 p q r).toNoun goalN (listNoun A region) sup (compCore g x ctx))))))))))) cr6F8
      = (sixLynF env msup p region rb rc o0 o1 cb cbw nex0 nex1 g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hs := comp_sect (x := x) hc nex0 nex1 o0 o1 rb cb cbw g
  have hD := sect_at
  simp only [scSmp] at hs
  unfold sixLynF
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
    unfold cr6F8
    simp [nock_exec, hD, sect_arm, hs]
  | some v =>
    obtain ⟨⟨lazy, yes, nuh⟩, g'⟩ := v
    rw [e] at hs
    simp only [Option.map_some, Option.bind_some] at hs ⊢
    have hl := sect_lazy e
    obtain ⟨kr, kb, kd⟩ := (km_sect nex0 nex1 o0 o1 rb cb cbw).keep _ _ _ e
    obtain ⟨hy, hn⟩ := sect_labels e
    subst hl
    have lvF := lyn_linv (linv_mono h0 kr kb) (linv_mono h1 kr kb) ap01 hy hn
    have hap : rc ∉ lregs (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] : Lazy CSet) := by
      simp only [lregs, fregs, bregs, flattenNeed, Sure.bunt, List.nil_append, List.append_nil,
        List.mem_append, not_or]
      exact ⟨a0, a1⟩
    have hpm := cr6f_p h7 hcode env msup p q r region hpc hpn rc yes nuh hP hR x hx g' (kd.trans hd)
      (by omega) _ lvF hap mono goalN sup nex0.goal.toNoun (HoonMap.toNoun condValNoun cbw)
      nex1.goal.toNoun (HoonMap.toNoun condValNoun cb) (listNoun A rb) (A rid)
      (C (CGoalL.next l0 (jmp0 o0)).toNoun (CGoalL.next l1 (jmp0 o1)).toNoun) (A 0)
    rw [next_jmp0_noun, next_jmp0_noun] at hpm ⊢
    simp only [crSubj, compCore] at hs hpm ⊢
    generalize nex0.goal.toNoun = N0 at hs hpm ⊢
    generalize nex1.goal.toNoun = N1 at hs hpm ⊢
    generalize (Lazy.mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] [] : Lazy CSet).toNoun = LZ at hs hpm ⊢
    generalize comp.door = Dr at hs hD hpm ⊢
    unfold cr6F8
    simp [nock_exec, hD, sect_arm, hs, hpm]

/-! ## The two runs: `cr6F4` ... `cr6F7` -/

/-- **The two runs of the branches in phase F** (`cr6F4` to `cr6F7`):
`cond-before`, the run of `r` for `goal-1` in `region-branch`,
`cond-between`, the run of `q` for `goal-0`, then a continuation `K` from
`cr6F8` on, given the links of the two runs (as `cr6s_mid`, on the subject
of phase F, which holds `region-id` and `r-cond` too). -/
theorem cr6f_mid (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (rb : List Nat)
    (goal0 goal1 : CGoalL CSet) (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF))
    (mono goalN regionN sup LEP : Noun) (rid rc : Nat)
    (K : TreapMap mugF (Nat × List Nat) → TreapMap mugF (Nat × List Nat) → NextL CSet → NextL CSet →
      CM (TreapMap mugF) (NextL CSet))
    (hr : CompRunAtR (runLC env msup) ctx r goal1 rb g)
    (hq : ∀ nex1 g1, runLC env msup r goal1 rb g = some (nex1, g1) → CompRunAtR (runLC env msup) ctx q goal0 rb g1)
    (hK : ∀ nex1 g1 nex0 g2, runLC env msup r goal1 rb g = some (nex1, g1) →
      runLC env msup q goal0 rb g1 = some (nex0, g2) →
      nock (C nex0.goal.toNoun (C (condN g1) (C nex1.goal.toNoun (C (condN g) (C (listNoun A rb) (C (A rid)
        (C (C goal0.toNoun goal1.toNoun) (C (A rc) (C LEP
          (crSubj mono (Nomm.n6 p q r).toNoun goalN regionN sup (compCore g2 x ctx))))))))))) cr6F8
        = (K g.cond g1.cond nex0 nex1 g2).map fun p => C p.1.goal.toNoun (genNoun p.2 x)) :
    nock (C (listNoun A rb) (C (A rid) (C (C goal0.toNoun goal1.toNoun) (C (A rc) (C LEP
      (crSubj mono (Nomm.n6 p q r).toNoun goalN regionN sup (compCore g x ctx))))))) cr6F4
      = ((do
          let cb ← getCond
          let nex1 ← runLC env msup r goal1 rb
          let cbw ← getCond
          let nex0 ← runLC env msup q goal0 rb
          K cb cbw nex0 nex1 : CM (TreapMap mugF) (NextL CSet)) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hr1 := hr x mono sup hx
  simp only [crSubj, compCore, genNoun] at hr1
  simp only [bind_apply, getCond, Option.bind_some]
  cases e1 : runLC (S := CSet) (Map := TreapMap mugF) env msup r goal1 rb g with
  | none =>
    rw [e1] at hr1
    unfold cr6F4 cr6F5
    simp [nock_exec, crSubj, compCore, Nomm.toNoun, cr_bat_dol, hr1, genNoun]
  | some rr =>
    obtain ⟨nex1, g1⟩ := rr
    rw [e1] at hr1
    simp only [Option.map_some] at hr1
    have hq1 := hq nex1 g1 e1 x mono sup hx
    simp only [crSubj, compCore, genNoun] at hq1
    cases e2 : runLC (S := CSet) (Map := TreapMap mugF) env msup q goal0 rb g1 with
    | none =>
      rw [e2] at hq1
      unfold cr6F4 cr6F5 cr6F6 cr6F7
      simp [nock_exec, crSubj, compCore, Nomm.toNoun, cr_bat_dol, hr1, hq1, genNoun, e2]
    | some rr =>
      obtain ⟨nex0, g2⟩ := rr
      rw [e2] at hq1
      simp only [Option.map_some] at hq1
      have hk := hK nex1 g1 nex0 g2 e1 e2
      simp only [crSubj, compCore, condN, genNoun, Nomm.toNoun] at hk
      unfold cr6F4 cr6F5 cr6F6 cr6F7
      simp [nock_exec, crSubj, compCore, Nomm.toNoun, cr_bat_dol, hr1, hq1, hk, genNoun, e2]

/-! ## The head on the way to phase F, and the model -/

/-- **The head of `%6` on the way to phase F**: `lep` is `~` (given the
Nock of `+leap`), `?^  lep` fails, `+none-equivalent` of the need with the
bunt sure is `|`, and the test of `+kerf` fails (`cr6tk_eq`): `cr6F0` runs
with `lep` pushed. -/
theorem cr6f_head (h7 : slot? 7 ctx = some compK) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF)) (mono sup : Noun)
    (hLp : nock (C lp6Bat (C (C laz.toNoun (C q.toNoun r.toNoun)) (compCore g x ctx))) lp6Bat = some (A 0))
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = false) (hkt : kerfTest q r laz = false) :
    nock (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crDol
      = nock (C (A 0) (crSubj mono (Nomm.n6 p q r).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
          (compCore g x ctx))) cr6F0 := by
  have hD := lp6_at
  have htk := cr6tk_eq h7 p q r laz th region x hx g mono sup (A 0)
  rw [hkt] at htk
  obtain ⟨s, fk, bd⟩ := laz
  have hn := ne_all (Lazy.mk Sure.bunt fk bd)
  simp only [Lazy.fork, Lazy.bond] at hne
  rw [hne] at hn
  simp only [CGoalL.toNoun, lazy_toNoun_mk] at hn hLp htk ⊢
  simp only [Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none, HoonSet.toNoun_empty] at hn
  rw [Nomm.toNoun, cr_disp_n6, cr6_eq]
  simp only [crSubj, compCore, Nomm.toNoun] at hLp htk ⊢
  generalize comp.door = Dr at hD hLp htk ⊢
  generalize s.toNoun = SN at hLp htk ⊢
  unfold cr6Head cr6NoLep cr6Lep cr6T2 cr6KF
  simp [nock_exec, hD, lp6_arm, hLp, h7, compK_ne, ne_arm, hn, htk, loob]

/-- The model of `%6` under a `%next` goal whose `+leap` is `~`, whose need
with the bunt sure is not `+none-equivalent` and whose `+kerf` test fails:
phase F (`sixNextForkC`). -/
theorem runLC_n6_f (env : CallEnv) (msup : Option Nomm) (p q r : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (hlp : leap laz q r = some Option.none)
    (hne : Lazy.noneEquivalentL (Lazy.mk Sure.bunt laz.fork laz.bond) = false) (hkt : kerfTest q r laz = false) :
    (runLC env msup (Nomm.n6 p q r) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = sixNextForkC env.cod (runLC env msup p) (runLC env msup q) (runLC env msup r) p laz th region := by
  show sixNextLC env.cod _ _ _ p q r 3 laz th region = _
  unfold kerfTest at hkt
  rw [sixNextLC.eq_2]
  simp only [hlp, hne, Bool.not_false, if_true, hkt, Bool.false_eq_true, if_false]

end Compiler
end Formalization
