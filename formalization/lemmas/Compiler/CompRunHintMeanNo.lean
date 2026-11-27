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

end Compiler
end Formalization
