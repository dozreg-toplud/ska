import lemmas.Compiler.CompRunHintMean

/-!
# The case `%mean` of `+run`: the branch `NO` at `mono` `&` (README Gaps 25)

At `mono` `&` the branch `NO` of `crKmean` runs only on a constant
(`konst` `[~ n]`, `cmTest` takes `YES` otherwise).  Then `b-ned` is
`[%none ~]`, `+need-ord-alloc-regs` allocates no register, the ops are
`[%hcp n body]`/`[%hce n body]`, and the soft calls (`+soft-new`,
`+soft-bond`) run only when `+sound p [%none ~]` is `|`, where the model
`runLCH` is `none`: with `snd p [%none ~]` (which `+sound-far` always
gives, `CompRunHintMeanCheck.lean`, `konstOK`) they are never reached and
need no link.  The parts, from the last (nouns `cmN11` to `cmNo`,
`tools/gen/runhintm.py`), each against any model `R` of `p` and `q`:

* `cm_n11`: `$` of `p` under `[%next (lazy-from-need sub-ned) ~ prol]`,
  then `+copy` with the bound need;
* `cm_n10`: the push of `nex-arg`: `+lazy-from-need`, `+sound p b-ned`
  (`SoundAt`), then `cm_n11`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 8000

variable {ctx : Noun}

/-- The goal of the trap: `[%next (lazy-from-need sub-ned) ~ prol]`. -/
noncomputable abbrev cmGoal (ned : Need) (prol : Nat) : CGoalL CSet :=
  CGoalL.next (Lazy.ofSure ⟨ned, HoonSet.empty⟩) (jmp0 prol)

theorem cm_goal_noun (ned : Need) (prol : Nat) : (cmGoal ned prol).toNoun
    = C (A 0x7478656e) (C (C (C ned.toNoun (A 0)) (C (A 0) (A 0))) (C (A 0) (A prol))) := by
  simp [CGoalL.toNoun, Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun, HoonSet.toNoun_empty, Jmp.toNoun, jmp0, listNoun]

/-- The model from the run of `p` on. -/
noncomputable def cmTail11 (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p : Nomm)
    (ned : Need) (laz : Lazy CSet) (prol : Nat) (region : List Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let nexTrap ← R p (cmGoal ned prol) region
  copyL nexTrap laz

/-- The bottom of the stack of `crKmean`'s pushes: `sub-ned`, `b-ned`,
`konst`, then the subject of `$`. -/
abbrev cmSubj (subnedN bnedN KV mono nommN goalN regionN sup : Noun) (g : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  C subnedN (C bnedN (C KV (crSubj mono nommN goalN regionN sup (compCore g x ctx))))

/-- **From the run of `p` on**: `p` under `[%next (lazy-from-need sub-ned) ~
prol]`, then `+copy` with the bound need. -/
theorem cm_n11 (h7 : slot? 7 ctx = some compK) {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} (p q : Nomm) (b : Bell) (body : Noun) (k : Option Noun) (region : List Nat)
    (x : GenRest) (hx : x.NoSoft) (mono goalN sup KV nF1N epilN n5N n4N opsN subvN bnedN : Noun) (ned : Need)
    (nF2 : NextL CSet) (prol : Nat) (g : Gen (TreapMap mugF))
    (hp : CompRunAtX R ctx X p (cmGoal ned prol) region g)
    (hcp : ∀ n g', R p (cmGoal ned prol) region g = some (n, g') → CopyH g'.re n.laz nF2.laz)
    (hX : X x mono sup) :
    nock (C (cmGoal ned prol).toNoun (C (A prol) (C nF2.goal.toNoun (C nF1N (C epilN (C n5N (C n4N (C opsN
      (C subvN (cmSubj ned.toNoun bnedN KV mono (Nomm.mean p b q body k).toNoun goalN (listNoun A region) sup
        g x ctx)))))))))) cmN11
      = (cmTail11 R p ned nF2.laz prol region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hp1 := hp x mono sup hx hX
  simp only [crSubj, compCore] at hp1
  have hD2 := comp_cp_at
  simp only [cmSubj, crSubj, compCore, cr_next_nounL]
  cases e1 : R p (cmGoal ned prol) region g with
  | none =>
    rw [e1] at hp1
    generalize comp.door = Dr at hp1 hD2 ⊢
    unfold cmN11
    simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, hp1, cmTail11, bind, StateT.bind, e1]
  | some r1 =>
    obtain ⟨n1, g8⟩ := r1
    have hcpy := comp_copy_all h7 x g8 n1 nF2.laz (hcp n1 g8 e1)
    simp only [compCore, cr_next_nounL] at hcpy
    rw [e1] at hp1
    simp only [Option.map_some, cr_next_nounL] at hp1
    generalize comp.door = Dr at hp1 hD2 hcpy ⊢
    unfold cmN11
    simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, hp1, cmTail11, bind, StateT.bind, e1, hD2, cr_cp_arm, hcpy]

/-- **From the push of `nex-arg` on**: `+lazy-from-need` of `sub-ned`,
`+sound p [%none ~]` (`&` by `hsp`), then `cm_n11`. -/
theorem cm_n10 (h7 : slot? 7 ctx = some compK) {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {snd : Nomm → NeedOrd → Bool} (p q : Nomm) (b : Bell) (body : Noun)
    (k : Option Noun) (region : List Nat) (x : GenRest) (hx : x.NoSoft)
    (mono goalN sup KV nF1N epilN n5N n4N opsN subvN : Noun) (ned : Need) (nF2 : NextL CSet) (prol : Nat)
    (g : Gen (TreapMap mugF)) (hs : SoundAt ctx snd p) (hsp : snd p NeedOrd.none = true)
    (hp : CompRunAtX R ctx X p (cmGoal ned prol) region g)
    (hcp : ∀ n g', R p (cmGoal ned prol) region g = some (n, g') → CopyH g'.re n.laz nF2.laz)
    (hX : X x mono sup) :
    nock (C (A prol) (C nF2.goal.toNoun (C nF1N (C epilN (C n5N (C n4N (C opsN
      (C subvN (cmSubj ned.toNoun NeedOrd.none.toNoun KV mono (Nomm.mean p b q body k).toNoun goalN
        (listNoun A region) sup g x ctx))))))))) cmN10
      = (cmTail11 R p ned nF2.laz prol region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h15 := cr_ctx15 h7
  have ht := cm_n11 h7 p q b body k region x hx mono goalN sup KV nF1N epilN n5N n4N opsN subvN
    NeedOrd.none.toNoun ned nF2 prol g hp hcp hX
  have hsn := hs g x NeedOrd.none
  rw [hsp] at hsn
  rw [cm_goal_noun] at ht
  have hS := comp_sound_at
  simp only [crSubj, compCore, cmSubj, Nomm.toNoun] at ht hsn ⊢
  generalize comp.door = Dr at ht hsn hS ⊢
  nock_open cmN10
  simp [nock_exec, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, hS, snd_arm, hsn, loob, ht]

/-! ## From the run of `q` -/

/-- The blobs of the epilogue and the prologue of a constant. -/
abbrev cmEpil (n body : Noun) (th : Jmp) : Blob := ⟨[], [Pole.hce n body], Termin.hop th⟩
abbrev cmProl (n body : Noun) (th : Jmp) : Blob := ⟨[], [Pole.hcp n body], Termin.hop th⟩

/-- `[prol-op epil-op]` of a constant. -/
abbrev cmOps (n body : Noun) : Noun := C (Pole.hcp n body).toNoun (Pole.hce n body).toNoun

/-- The model from the run of `q` on. -/
noncomputable def cmTail7 (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm)
    (n body : Noun) (ned : Need) (laz : Lazy CSet) (epil : Nat) (region : List Nat) :
    CM (TreapMap mugF) (NextL CSet) := do
  let nexFol1 ← R q (CGoalL.next laz (jmp0 epil)) region
  let nexFol2 ← lazyBound nexFol1 region
  let prol ← emit (cmProl n body nexFol2.th)
  cmTail11 R p ned nexFol2.laz prol region

/-- **What the part from the run of `q` takes**: the link of `q` at its goal,
the link of `p` at its goal after `+lazy-bound` and the prologue, the
`CopyH` of the `+copy`. -/
def CmRest (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (ctx : Noun)
    (X : GenRest → Noun → Noun → Prop) (p q : Nomm) (n body : Noun) (region : List Nat) (ned : Need)
    (laz : Lazy CSet) (epil : Nat) (g4 : Gen (TreapMap mugF)) : Prop :=
  CompRunAtX R ctx X q (CGoalL.next laz (jmp0 epil)) region g4 ∧
  (∀ n1 g5 n2 g6, R q (CGoalL.next laz (jmp0 epil)) region g4 = some (n1, g5) →
    lazyBound n1 region g5 = some (n2, g6) →
    CompRunAtX R ctx X p (cmGoal ned g6.bo) region (cfEmitG (cmProl n body n2.th) g6)) ∧
  (∀ n1 g5 n2 g6 n3 g8, R q (CGoalL.next laz (jmp0 epil)) region g4 = some (n1, g5) →
    lazyBound n1 region g5 = some (n2, g6) →
    R p (cmGoal ned g6.bo) region (cfEmitG (cmProl n body n2.th) g6) = some (n3, g8) →
    CopyH g8.re n3.laz n2.laz)

/-- **From the run of `q` on**: `q`, `+lazy-bound`, the prologue, `cm_n10`. -/
theorem cm_n7 (h7 : slot? 7 ctx = some compK) {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {snd : Nomm → NeedOrd → Bool} (p q : Nomm) (b : Bell) (body : Noun)
    (k : Option Noun) (n : Noun) (region : List Nat) (x : GenRest) (hx : x.NoSoft)
    (mono goalN sup KV n4N subvN : Noun) (ned : Need) (nex5 : NextL CSet) (epil : Nat)
    (g4 : Gen (TreapMap mugF)) (hs : SoundAt ctx snd p) (hsp : snd p NeedOrd.none = true)
    (hR : CmRest R ctx X p q n body region ned nex5.laz epil g4) (hX : X x mono sup) :
    nock (C (A epil) (C nex5.goal.toNoun (C n4N (C (cmOps n body) (C subvN (cmSubj ned.toNoun NeedOrd.none.toNoun KV mono
      (Nomm.mean p b q body k).toNoun goalN (listNoun A region) sup g4 x ctx)))))) cmN7
      = (cmTail7 R p q n body ned nex5.laz epil region g4).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨hq, hp, hcp⟩ := hR
  have hq1 := hq x mono sup hx hX
  simp only [crSubj, compCore, cgl_next_noun, cr_jmp0] at hq1
  have hD1 := comp_lb_at
  have hD2 := comp_emit_at
  simp only [cmSubj, crSubj, compCore, cr_next_nounL, cmOps, Pole.toNoun, Tag.hcp, Tag.hce]
  cases e1 : R q (CGoalL.next nex5.laz (jmp0 epil)) region g4 with
  | none =>
    rw [e1] at hq1
    generalize comp.door = Dr at hq1 hD1 hD2 ⊢
    nock_open cmN7
    simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, hq1, cmTail7, bind, StateT.bind, e1]
  | some r1 =>
    obtain ⟨n1, g5⟩ := r1
    rw [e1] at hq1
    simp only [Option.map_some, cr_next_nounL] at hq1
    have hlb := comp_lazy_bound hc x g5 n1 region
    simp only [compCore, cr_next_nounL] at hlb
    cases e2 : lazyBound (S := CSet) (Map := TreapMap mugF) n1 region g5 with
    | none =>
      rw [e2] at hlb
      generalize comp.door = Dr at hq1 hD1 hD2 hlb ⊢
      nock_open cmN7
      simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, hq1, cmTail7, bind, StateT.bind, e1, hD1, lb_arm, hlb, e2]
    | some r2 =>
      obtain ⟨n2, g6⟩ := r2
      rw [e2] at hlb
      simp only [Option.map_some, cr_next_nounL] at hlb
      have he := cf_emit (x := x) hc g6 (cmProl n body n2.th)
      simp only [cmProl, Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.hcp] at he
      have ht := cm_n10 h7 p q b body k region x hx mono goalN sup KV n1.goal.toNoun (A epil) nex5.goal.toNoun n4N
        (cmOps n body) subvN ned n2 g6.bo _ hs hsp (hp n1 g5 n2 g6 e1 e2) (fun n' g' e => hcp n1 g5 n2 g6 n' g' e1 e2 e) hX
      simp only [cmSubj, crSubj, compCore, cr_next_nounL, Nomm.toNoun, cmOps, Pole.toNoun, Tag.hcp, Tag.hce] at ht
      generalize comp.door = Dr at hq1 hD1 hD2 hlb he ht ⊢
      nock_open cmN7
      simp [nock_exec, crSubj, Nomm.toNoun, cr_bat_dol, hq1, cmTail7, bind, StateT.bind, e1, hD1, lb_arm, hlb, e2,
        hD2, comp_emit_arm, he, cf_emit_g, ht]

/-! ## From `+past-if` -/

/-- The model from `+past-if` on. -/
noncomputable def cmFrom (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (snd : Nomm → NeedOrd → Bool) (p q : Nomm) (n body : Noun) (ned : Need) (region : List Nat) (nex : NextL CSet) :
    CM (TreapMap mugF) (NextL CSet) := do
  let nex ← pastIfL snd nex q region
  let epil ← emit (cmEpil n body nex.th)
  cmTail7 R p q n body ned nex.laz epil region

/-- **From `+past-if` on**: `+past-if`, the epilogue, `cm_n7`. -/
theorem cm_n5 (h7 : slot? 7 ctx = some compK) {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {snd : Nomm → NeedOrd → Bool} (p q : Nomm) (b : Bell) (body : Noun)
    (k : Option Noun) (n : Noun) (region : List Nat) (x : GenRest) (hx : x.NoSoft)
    (mono goalN sup KV subvN : Noun) (ned : Need) (nex4 : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hsq : SoundAt ctx snd q) (hs : SoundAt ctx snd p) (hsp : snd p NeedOrd.none = true)
    (hR : ∀ nex5 g2, pastIfL snd nex4 q region g1 = some (nex5, g2) →
      CmRest R ctx X p q n body region ned nex5.laz g2.bo (cfEmitG (cmEpil n body nex5.th) g2))
    (hX : X x mono sup) :
    nock (C nex4.goal.toNoun (C (cmOps n body) (C subvN (cmSubj ned.toNoun NeedOrd.none.toNoun KV mono
      (Nomm.mean p b q body k).toNoun goalN (listNoun A region) sup g1 x ctx)))) cmN5
      = (cmFrom R snd p q n body ned region nex4 g1).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hpi := comp_past_if h7 x g1 nex4 q region hsq
  simp only [cmSubj, crSubj, compCore, cr_next_nounL, cmOps, Pole.toNoun, Tag.hcp, Tag.hce] at hpi ⊢
  have hD1 := comp_past_if_at
  have hD2 := comp_emit_at
  cases e1 : pastIfL snd nex4 q region g1 with
  | none =>
    rw [e1] at hpi
    generalize comp.door = Dr at hpi hD1 hD2 ⊢
    nock_open cmN5
    simp [nock_exec, crSubj, Nomm.toNoun, hD1, pi_arm, hpi, cmFrom, bind, StateT.bind, e1]
  | some r =>
    obtain ⟨nex5, g2⟩ := r
    rw [e1] at hpi
    simp only [Option.map_some, cr_next_nounL] at hpi
    have he := cf_emit (x := x) hc g2 (cmEpil n body nex5.th)
    simp only [cmEpil, Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.hce] at he
    have ht := cm_n7 h7 p q b body k n region x hx mono goalN sup KV nex4.goal.toNoun subvN ned nex5 g2.bo _
      hs hsp (hR nex5 g2 e1) hX
    simp only [cmSubj, crSubj, compCore, cr_next_nounL, Nomm.toNoun, cmOps, Pole.toNoun, Tag.hcp, Tag.hce] at ht
    generalize comp.door = Dr at hpi hD1 hD2 he ht ⊢
    nock_open cmN5
    simp [nock_exec, crSubj, Nomm.toNoun, hD1, pi_arm, hpi, hD2, comp_emit_arm, he, ht, cmFrom, bind,
      StateT.bind, e1, cf_emit_g]

/-! ## The branch from its start -/

/-- **The branch `NO` on a constant `n`**: `b-ned` `[%none ~]`,
`+need-ord-alloc-regs` (no register), `+flatten-need`, the ops `[%hcp n
body]`/`[%hce n body]`, `+simple-next`, `cm_n5`. -/
theorem cm_no (h7 : slot? 7 ctx = some compK) {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {snd : Nomm → NeedOrd → Bool} (p q : Nomm) (b : Bell) (body : Noun)
    (k : Option Noun) (n : Noun) (goal : CGoalL CSet) (region : List Nat) (x : GenRest) (hx : x.NoSoft)
    (mono sup : Noun) (g : Gen (TreapMap mugF))
    (hsq : SoundAt ctx snd q) (hs : SoundAt ctx snd p) (hsp : snd p NeedOrd.none = true)
    (hR : ∀ nex4 g1 nex5 g2, simpleNextL goal g = some (nex4, g1) → pastIfL snd nex4 q region g1 = some (nex5, g2) →
      CmRest R ctx X p q n body region Need.none nex5.laz g2.bo (cfEmitG (cmEpil n body nex5.th) g2))
    (hX : X x mono sup) :
    nock (C (C (A 0) n) (crSubj mono (Nomm.mean p b q body k).toNoun goal.toNoun (listNoun A region) sup
      (compCore g x ctx))) cmNo
      = ((simpleNextL goal >>= cmFrom R snd p q n body Need.none region) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hsn := comp_simple_next hc x g goal mono (Nomm.mean p b q body k).toNoun (listNoun A region) sup
  have hnoar := noar_gate ctx x NeedOrd.none g
  have hD2 := noar_at
  have hD3 := comp_fn_at
  have hfn := comp_flatten_need hc (genNoun g x) Need.none
  rw [bind_apply]
  cases e : simpleNextL (S := CSet) (Map := TreapMap mugF) goal g with
  | none =>
    rw [e] at hsn
    simp only [Option.map_none] at hsn
    simp only [crSubj, compCore, needOrdAllocRegs, pure, StateT.pure, Option.map_some, NeedOrd.toNoun, Need.toNoun,
      Tag.none, Nomm.toNoun] at hsn hnoar hfn ⊢
    generalize comp.door = Dr at hsn hnoar hD2 hD3 hfn ⊢
    nock_open cmNo
    simp [nock_exec, crSubj, Nomm.toNoun, hsn, cr_bat_sn, hD2, noarHint, h7, hnoar, hD3, comp_fn_arm, hfn,
      NeedOrd.toNoun, Need.toNoun, Tag.none, cmN4]
  | some r =>
    obtain ⟨nex4, g1⟩ := r
    rw [e] at hsn
    simp only [Option.map_some] at hsn
    have hk := cm_n5 h7 p q b body k n region x hx mono goal.toNoun sup (C (A 0) n)
      (listNoun A (flattenNeed Need.none)) Need.none nex4 g1 hsq hs hsp (fun nex5 g2 e1 => hR nex4 g1 nex5 g2 e e1) hX
    simp only [cmSubj, crSubj, compCore, Nomm.toNoun, cmOps, Pole.toNoun, Tag.hcp, Tag.hce] at hsn hk
    simp only [crSubj, compCore, needOrdAllocRegs, pure, StateT.pure, Option.map_some, NeedOrd.toNoun, Need.toNoun,
      Tag.none] at hnoar hfn hk ⊢
    generalize comp.door = Dr at hsn hk hnoar hD2 hD3 hfn ⊢
    nock_open cmNo
    simp [nock_exec, crSubj, Nomm.toNoun, hsn, cr_bat_sn, hD2, noarHint, h7, hnoar, hD3, comp_fn_arm, hfn,
      NeedOrd.toNoun, Need.toNoun, Tag.none, hk, Tag.hcp, Tag.hce, cmN4]

end Compiler
end Formalization
