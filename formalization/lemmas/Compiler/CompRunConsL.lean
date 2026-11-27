import lemmas.Compiler.CompRunLeafL
import lemmas.Ska.CompNC

/-!
# The cons case of `+run` on lazy goals, with lazy results

The cons `[p q]` on every goal with `GInv`, for `p` and `q` that may call
(no direct call: `+hinted` reads no code table, `hinted_plain`).  The Nock
is the old one (`crcHead`, `crcPick`, `crcNTail`, `crc_eq`); what changes is
the class of goals and results:

* `+split` of any lazy need (`comp_split_all`, the looks of `GInv`);
* `+past` with its bond branch (`comp_past`): the head's goal is
  `+past` of the first half over `q`, and `q`'s result goes through
  `+past` over `p`, either of which parks a need in a bond when the nomm
  calls;
* the runs of `q` and `p` on lazy goals with lazy results, taken as
  hypotheses on every goal with `GInv`;
* `+copy` of two lazy needs (`comp_copy_all`), its side condition `CopyH`
  from the runs' results (`tail_copyH`, `RunResL`).

`crc_ntailL` is the tail on a `%next` goal from `+past` on; `crc_nextL` adds
`+split`; `crc_pickL` the branch `%pick`; `comp_run_consL` the whole case.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## No direct call -/

theorem plainOk_noDirect : ∀ (n : Nomm), PlainOk n = true → NoDirect n
  | Nomm.cons p q, h => by
    simp only [PlainOk, Bool.and_eq_true] at h; exact ⟨plainOk_noDirect p h.1, plainOk_noDirect q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q Option.none, h => by
    simp only [PlainOk, Bool.and_eq_true] at h; exact ⟨plainOk_noDirect p h.1, plainOk_noDirect q h.2⟩
  | Nomm.n3 p, h => by simp only [PlainOk] at h; exact plainOk_noDirect p h
  | Nomm.n4 p, h => by simp only [PlainOk] at h; exact plainOk_noDirect p h
  | Nomm.n5 p q, h => by
    simp only [PlainOk, Bool.and_eq_true] at h; exact ⟨plainOk_noDirect p h.1, plainOk_noDirect q h.2⟩
  | Nomm.n7 p q, h => by
    simp only [PlainOk, Bool.and_eq_true] at h; exact ⟨plainOk_noDirect p h.1, plainOk_noDirect q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [PlainOk, Bool.and_eq_true] at h; exact ⟨plainOk_noDirect v h.1.2, plainOk_noDirect q h.2⟩
  | Nomm.n2 _ _ (some _), h => by simp [PlainOk] at h
  | Nomm.n6 _ _ _, h => by simp [PlainOk] at h
  | Nomm.n11s _ _ _, h => by simp [PlainOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [PlainOk] at h
  | Nomm.n12 _ _, h => by simp [PlainOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [PlainOk] at h

/-- **`+hinted` of a nomm of the plain class** reads no code table and does
not crash. -/
theorem hinted_plain (cod : Bell → Option Bool) {n : Nomm} (h : PlainOk n = true) :
    hinted cod n = hinted noCode n ∧ hinted noCode n ≠ Option.none := by
  have hn := plainOk_noDirect n h
  rw [hinted_noDirect cod n hn, hinted_noDirect noCode n hn]
  exact ⟨rfl, by simp⟩

/-- **`+hinted` of a nomm with no direct call** reads no code table and does
not crash. -/
theorem hinted_nd (cod : Bell → Option Bool) {n : Nomm} (hn : NoDirect n) :
    hinted cod n = hinted noCode n ∧ hinted noCode n ≠ Option.none := by
  rw [hinted_noDirect cod n hn, hinted_noDirect noCode n hn]
  exact ⟨rfl, by simp⟩

theorem pastL_plain {cod : Bell → Option Bool} {n : Nomm} (h : PlainOk n = true) (nex : NextL CSet)
    (region : List Nat) : (pastL cod nex n region : CM (TreapMap mugF) (NextL CSet)) = pastL noCode nex n region :=
  pastL_cod (hinted_plain cod h).1 nex region

theorem cr_next_nounL (n : NextL CSet) : n.goal.toNoun = C (A 0x7478656e) (C n.laz.toNoun n.th.toNoun) := rfl

theorem cgl_next_noun (laz : Lazy CSet) (th : Jmp) :
    (CGoalL.next laz th).toNoun = C (A 0x7478656e) (C laz.toNoun th.toNoun) := rfl

/-! ## The tail of the `%next` branch -/

/-- **The tail of the cons case for a `%next` goal**, from `+split` on:
`+past` of `[%next hed ~ o]` over `q`, `q` into `tel`, `+past` over `p`,
`p` into the first `+past`'s need, `+copy`; every need lazy. -/
theorem crc_ntailL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (hqn : hinted noCode q ≠ Option.none) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun)
    (hed tel : Lazy CSet) (o : Nat) (g1 : Gen (TreapMap mugF))
    (hq : ∀ nexh g2, pastL noCode ⟨hed, jmp0 o⟩ q region g1 = some (nexh, g2) →
      CompRunAtR (runLC env msup) ctx q (CGoalL.next tel nexh.th) region g2)
    (hp : ∀ nexh g2 n2 g3 n2' g4, pastL noCode ⟨hed, jmp0 o⟩ q region g1 = some (nexh, g2) →
      runLC env msup q (CGoalL.next tel nexh.th) region g2 = some (n2, g3) →
      pastL noCode n2 p region g3 = some (n2', g4) →
      CompRunAtR (runLC env msup) ctx p (CGoalL.next nexh.laz n2'.th) region g4)
    (hcp : ∀ nexh g2 n2 g3 n2' g4 n1 g5, pastL noCode ⟨hed, jmp0 o⟩ q region g1 = some (nexh, g2) →
      runLC env msup q (CGoalL.next tel nexh.th) region g2 = some (n2, g3) →
      pastL noCode n2 p region g3 = some (n2', g4) →
      runLC env msup p (CGoalL.next nexh.laz n2'.th) region g4 = some (n1, g5) → CopyH g5.re n1.laz n2'.laz) :
    nock (C (C hed.toNoun (C tel.toNoun (A o))) (crSubj mono (Nomm.cons p q).toNoun goalN
      (listNoun A region) sup (compCore g1 x ctx))) crcNTail
      = ((do
          let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLC env msup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL noCode nex2 p region
          let nex1 ← runLC env msup p (CGoalL.next nexh.laz nex2.th) region
          copyL nex1 nex2.laz : CM (TreapMap mugF) (NextL CSet)) g1).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hpa1 := comp_past h7 hcode x g1 ⟨hed, jmp0 o⟩ q region hqn
  simp only [cr_next_nounL, cr_jmp0, compCore] at hpa1
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases e1 : pastL (S := CSet) (Map := TreapMap mugF) noCode ⟨hed, jmp0 o⟩ q region g1 with
  | none =>
    rw [e1] at hpa1
    generalize comp.door = Dr at hpa1 hD1 hD2 ⊢
    nock_open crcNTail
    simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa1, e1]
  | some r1 =>
    obtain ⟨nexh, g2⟩ := r1
    rw [e1] at hpa1
    simp only [Option.map_some, cr_next_nounL] at hpa1
    have hq1 := hq nexh g2 e1 x mono sup hx
    simp only [crSubj, compCore, cgl_next_noun] at hq1
    cases e2 : runLC (S := CSet) (Map := TreapMap mugF) env msup q (CGoalL.next tel nexh.th) region g2 with
    | none =>
      rw [e2] at hq1
      generalize comp.door = Dr at hpa1 hD1 hD2 hq1 ⊢
      nock_open crcNTail
      simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa1, e1,
        hq1, e2, cgl_next_noun]
    | some r2 =>
      obtain ⟨n2, g3⟩ := r2
      rw [e2] at hq1
      simp only [Option.map_some, cr_next_nounL] at hq1
      have hpa2 := comp_past h7 hcode x g3 n2 p region hpn
      simp only [cr_next_nounL, compCore] at hpa2
      cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode n2 p region g3 with
      | none =>
        rw [e3] at hpa2
        generalize comp.door = Dr at hpa1 hD1 hD2 hq1 hpa2 ⊢
        nock_open crcNTail
        simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa1,
          e1, hq1, e2, hpa2, e3, cgl_next_noun]
      | some r3 =>
        obtain ⟨n2', g4⟩ := r3
        rw [e3] at hpa2
        simp only [Option.map_some, cr_next_nounL] at hpa2
        have hp1 := hp nexh g2 n2 g3 n2' g4 e1 e2 e3 x mono sup hx
        simp only [crSubj, compCore, cgl_next_noun] at hp1
        cases e4 : runLC (S := CSet) (Map := TreapMap mugF) env msup p (CGoalL.next nexh.laz n2'.th) region g4 with
        | none =>
          rw [e4] at hp1
          generalize comp.door = Dr at hpa1 hD1 hD2 hq1 hpa2 hp1 ⊢
          nock_open crcNTail
          simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa1,
            e1, hq1, e2, hpa2, e3, hp1, e4, cgl_next_noun]
        | some r4 =>
          obtain ⟨n1, g5⟩ := r4
          rw [e4] at hp1
          simp only [Option.map_some, cr_next_nounL] at hp1
          have hcpy := comp_copy_all h7 x g5 n1 n2'.laz (hcp nexh g2 n2 g3 n2' g4 n1 g5 e1 e2 e3 e4)
          simp only [compCore, cr_next_nounL] at hcpy
          generalize comp.door = Dr at hpa1 hD1 hD2 hq1 hpa2 hp1 hcpy ⊢
          nock_open crcNTail
          simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa1,
            e1, hq1, e2, hpa2, e3, hp1, e4, hD2, cr_cp_arm, hcpy, cgl_next_noun, cr_next_nounL]

/-! ## The `%next` branch, `%pick`, and the whole case -/

theorem runLC_cons_next (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) :
    (runLC env msup (Nomm.cons p q) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet)) = (do
      let (hed, tel, o) ← splitL ⟨laz, th⟩
      let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
      let nex2 ← runLC env msup q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLC env msup p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz) := by
  conv => lhs; unfold runLC
  rfl

theorem runLC_cons_pick (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (z o : Jmp) (region : List Nat) :
    (runLC env msup (Nomm.cons p q) (CGoalL.pick z o) region : CM (TreapMap mugF) (NextL CSet)) = (do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      let nex2 ← runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLC env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nex2.th) region
      copyL nex1 nex2.laz) := by
  conv => lhs; unfold runLC
  rfl

/-- What the cases take of a part: the link and the result on every goal
with the invariant. -/
structure PartL (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (n : Nomm) (region : List Nat) : Prop where
  link : ∀ (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal → CompRunAtR (runLC env msup) ctx n goal region g
  res : ResFor env msup n region
  nd : NoDirect n

/-- **The `%next` branch of the cons case on a lazy goal**: `+split`
(`comp_split_all`), then `crc_ntailL`. -/
theorem crc_nextL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region)
    (x : GenRest) (hx : x.NoSoft) (mono sup : Noun) (laz : Lazy CSet) (th : Jmp) (g : Gen (TreapMap mugF))
    (hinv : GInv g (CGoalL.next laz th)) :
    nock (crSubj mono (Nomm.cons p q).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup
      (compCore g x ctx)) crKc
      = (runLC env msup (Nomm.cons p q) (CGoalL.next laz th) region g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hpc, hpn⟩ := hinted_nd env.cod P.nd
  obtain ⟨hqc, hqn⟩ := hinted_nd env.cod Q.nd
  have hsp := comp_split_all h7 x g ⟨laz, th⟩ (crInvL_lok (crInvL_of_gInv hinv) 0)
  simp only [cr_next_nounL, compCore] at hsp
  have hDs := cr_split_at
  rw [runLC_cons_next, crc_eq, cgl_next_noun]
  simp only [pastL_cod hpc, pastL_cod hqc]
  cases es : splitL (Map := TreapMap mugF) ⟨laz, th⟩ g with
  | none =>
    rw [es] at hsp
    simp only [crSubj, compCore, Option.map_none] at hsp ⊢
    generalize comp.door = Dr at hDs hsp ⊢
    nock_open crcHead
    simp [nock_exec, hDs, crc_split_arm, hsp, bind, StateT.bind, es]
  | some r =>
    obtain ⟨⟨hed, tel, o⟩, g1⟩ := r
    rw [es] at hsp
    obtain ⟨l1, b1, d1, ih, it, nd, -⟩ := splitL_inv hinv es
    have ht := crc_ntailL h7 hcode env msup p q hpn hqn region x hx mono
      (C (A 0x7478656e) (C laz.toNoun th.toNoun)) sup hed tel o g1
      (fun nexh g2 e1 => by
        obtain ⟨r2, b2, d2, i2, j2, rg2⟩ := pastL_inv ih (jmpIn_jmp0 _ _) e1
        exact Q.link _ _ ⟨linv_mono it (by omega) b2, d2.trans d1, j2⟩)
      (fun nexh g2 n2 g3 n2' g4 e1 e2 e3 => by
        obtain ⟨r2, b2, d2, i2, j2, rg2⟩ := pastL_inv ih (jmpIn_jmp0 _ _) e1
        have hq : GInv g2 (CGoalL.next tel nexh.th) := ⟨linv_mono it (by omega) b2, d2.trans d1, j2⟩
        exact P.link _ _ (tail_pgoal hq i2 (Q.res _ _ _ _ hq e2) e3).1)
      (fun nexh g2 n2 g3 n2' g4 n1 g5 e1 e2 e3 e4 => by
        obtain ⟨r2, b2, d2, i2, j2, rg2⟩ := pastL_inv ih (jmpIn_jmp0 _ _) e1
        have hq : GInv g2 (CGoalL.next tel nexh.th) := ⟨linv_mono it (by omega) b2, d2.trans d1, j2⟩
        have R2 := Q.res _ _ _ _ hq e2
        have R1 := P.res _ _ _ _ (tail_pgoal hq i2 R2 e3).1 e4
        exact (tail_copyH hq i2 (by rw [rg2]; exact nd) R2 e3 R1).1)
    simp only [crSubj, compCore, Option.map_some] at hsp ht ⊢
    generalize (Nomm.cons p q).toNoun = NN at ht ⊢
    generalize comp.door = Dr at hDs hsp ht ⊢
    nock_open crcHead
    simp [nock_exec, hDs, crc_split_arm, hsp, ht, bind, StateT.bind, es]

/-- **The branch `%pick` of the cons case**, with lazy results: the
`[%bom ~]` block `o`, `q` for `[%next *need-lazy ~ o]`, `+past` over `p`,
`p` for `[%next *need-lazy then]`, `+copy`. -/
theorem crc_pickL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region)
    (x : GenRest) (hx : x.NoSoft) (mono goalN sup : Noun) (g : Gen (TreapMap mugF)) (hd : g.drop = false) :
    nock (crSubj mono (Nomm.cons p q).toNoun goalN (listNoun A region) sup (compCore g x ctx)) crcPick
      = ((do
          let nex2 ← runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 g.bo)) region
          let nex2 ← pastL noCode nex2 p region
          let nex1 ← runLC env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz : CM (TreapMap mugF) (NextL CSet)) (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g)).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨hpc, hpn⟩ := hinted_nd env.cod P.nd
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.bom Option.none⟩
  rw [crc_blob_bom] at he
  have hq0 : GInv (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g) (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 g.bo)) :=
    ginv_bunt_j (by rw [cf_emitG_drop]; exact hd) (jmpIn_jmp0 _ _)
  have hv1 := Q.link _ _ hq0 x mono sup hx
  rw [cgl_next_noun, Lazy.toNoun_ofSure, cr_bunt_lazy, cr_jmp0] at hv1
  simp only [crSubj, compCore] at hv1
  have hD0 := comp_emit_at
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  simp only [compCore]
  cases eq : runLC (S := CSet) (Map := TreapMap mugF) env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 g.bo))
      region (cfEmitG ⟨[], [], Termin.bom Option.none⟩ g) with
  | none =>
    rw [eq] at hv1
    generalize comp.door = Dr at hv1 hD0 hD1 hD2 he ⊢
    nock_open crcPick
    simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nex2, g2⟩ := r
    rw [eq] at hv1
    simp only [Option.map_some, cr_next_nounL] at hv1
    have hpa2 := comp_past h7 hcode x g2 nex2 p region hpn
    simp only [cr_next_nounL, compCore] at hpa2
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode nex2 p region g2 with
    | none =>
      rw [e3] at hpa2
      generalize comp.door = Dr at hv1 hD0 hD1 hD2 he hpa2 ⊢
      nock_open crcPick
      simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq,
        h7, hcode, hD1, cr_past_arm, hpa2, e3]
    | some r3 =>
      obtain ⟨n2', g3⟩ := r3
      rw [e3] at hpa2
      simp only [Option.map_some, cr_next_nounL] at hpa2
      have R2 := Q.res _ _ _ _ hq0 eq
      have pg := tail_pgoal hq0 (linv_bunt _ _) R2 e3
      have hq1 := P.link _ _ pg.1 x mono sup hx
      rw [cgl_next_noun, Lazy.toNoun_ofSure, cr_bunt_lazy] at hq1
      simp only [crSubj, compCore] at hq1
      cases eq2 : runLC (S := CSet) (Map := TreapMap mugF) env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) n2'.th)
          region g3 with
      | none =>
        rw [eq2] at hq1
        generalize comp.door = Dr at hv1 hD0 hD1 hD2 he hpa2 hq1 ⊢
        nock_open crcPick
        simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq,
          h7, hcode, hD1, cr_past_arm, hpa2, e3, hq1, eq2]
      | some r' =>
        obtain ⟨nex1, g4⟩ := r'
        rw [eq2] at hq1
        simp only [Option.map_some, cr_next_nounL] at hq1
        have R1 := P.res _ _ _ _ pg.1 eq2
        have hcpy := comp_copy_all h7 x g4 nex1 n2'.laz
          (tail_copyH hq0 (linv_bunt _ _) (by simp [lregs_bunt]) R2 e3 R1).1
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hv1 hD0 hD1 hD2 he hpa2 hq1 hcpy ⊢
        nock_open crcPick
        simp [nock_exec, crSubj, Nomm.toNoun, hD0, comp_emit_arm, he, cr_bat_dol, hv1, bind, StateT.bind, eq,
          h7, hcode, hD1, cr_past_arm, hpa2, e3, hq1, eq2, hD2, cr_cp_arm, hcpy, cr_next_nounL]

/-- **The cons case of `+run` on every goal with the invariant**, for `p`
and `q` of the plain class, given their links and results on every goal
with the invariant (`PartL`). -/
theorem comp_run_consL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtR (runLC env msup) ctx (Nomm.cons p q) goal region g := by
  intro x mono sup hx
  obtain ⟨a, b, hab⟩ := crc_nomm_cell p
  have hnn : (Nomm.cons p q).toNoun = C (C a b) q.toNoun := by
    rw [show (Nomm.cons p q).toNoun = C p.toNoun q.toNoun from rfl, hab]
  rw [hnn, cr_disp_cons, ← hnn]
  cases goal with
  | next laz th => exact crc_nextL h7 hcode env msup p q P Q x hx mono sup laz th g hinv
  | done =>
    have e : (CGoalL.done : CGoalL CSet).toNoun = (CGoal.toL CGoal.done).toNoun := rfl
    rw [e, crc_eq, crc_done_step h7, ← crc_eq, runLC_cons_done]
    simp only [bind_apply, re_apply, Option.bind_some, cf_emit_g]
    exact crc_nextL h7 hcode env msup p q P Q x hx mono sup _ _ _
      (ginv_reg _ (by rw [cf_emitG_re]; simp) (by rw [cf_emitG_drop]; exact hinv))
  | pick z o =>
    obtain ⟨hpc, -⟩ := hinted_nd env.cod P.nd
    have hpk := crc_pickL h7 hcode env msup p q P Q x hx mono (CGoalL.pick (S := CSet) z o).toNoun sup g hinv.1
    rw [runLC_cons_pick, crc_eq]
    simp only [pastL_cod hpc]
    simp only [crSubj, compCore, CGoalL.toNoun] at hpk ⊢
    generalize (Nomm.cons p q).toNoun = NN at hpk ⊢
    generalize comp.door = Dr at hpk ⊢
    nock_open crcHead
    simp [nock_exec, CGoalL.toNoun, hpk, bind, StateT.bind, cf_emit_g]

end Compiler
end Formalization
