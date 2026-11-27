import lemmas.Compiler.CompRunDirectKN
import lemmas.Compiler.CompRunDirect

/-!
# The direct call of the case `%2` of `+run`: the call that emits a block

README Gaps 19.  The parts of `crDCall` (cut in `CompRunDirectKN.lean`),
each against the model `callL` of `Ska/CompCall.lean` with `info = some (b,
~)`, `mono` `|`, no ring and `sof` false:

* `RunAt`: one instance of the run link (fixed `x`, `mono`, `sup`);
  `CompRunAtR` is `RunAt` for every `x` with `NoSoft`, `mono` and `sup`
  (`cra_runAt`).  `CompRunAtM`: the link at `mono` `|` (`A 1`) and the `sup`
  of the model (`unitNoun Nomm.toNoun msup`), for every `x` with `NoSoft`
  and the environment `E x`; `CompRunAtR` gives it (`cram_of_r`).
* `crd_cnf`, `crd_ctail`: the tail of the call (steps `10` to `14`): the run
  of `q` under `+safe-fol-fol` for `[%next *need-lazy then.nex-arg]`,
  `+past`, the run of `p` for `[%next laz.nex-arg then.nex-fol]`, `+copy`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## The statement -/

/-- **One instance of the run link**: the `$` arm of `+run` on the noun of a
nomm and a goal, with the rest `x` of the state, `mono` and `sup` fixed, is
`runLC env msup`. -/
def RunAt (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (x : GenRest) (mono sup : Noun) (n : Nomm)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
    = (runLC env msup n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

theorem cra_runAt {env : CallEnv} {msup : Option Nomm} {n : Nomm} {goal : CGoalL CSet} {region : List Nat}
    {g : Gen (TreapMap mugF)} :
    CompRunAtR (runLC env msup) ctx n goal region g
      ↔ ∀ (x : GenRest) (mono sup : Noun), x.NoSoft → RunAt env msup ctx x mono sup n goal region g :=
  Iff.rfl

/-- **The run link at `mono` `|`** (`A 1`, the n-ary versions of
`+compile-scc-in`) with the Hoon's `sup` the noun of the model's `msup`, for
every rest `x` of the state with an empty `soft` that meets `E` (what the
direct call reads of `cache` and of the context: `CallNoun`). -/
def CompRunAtM (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (E : GenRest → Prop) (n : Nomm)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  ∀ x : GenRest, x.NoSoft → E x → RunAt env msup ctx x (A 1) (unitNoun Nomm.toNoun msup) n goal region g

/-- `CompRunAtR` (every `mono`, `sup` and `x`) gives `CompRunAtM`. -/
theorem cram_of_r {env : CallEnv} {msup : Option Nomm} (E : GenRest → Prop) {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)} (h : CompRunAtR (runLC env msup) ctx n goal region g) :
    CompRunAtM env msup ctx E n goal region g :=
  fun x hx _ => h x _ _ hx

/-! ## The tail: steps `10` to `14` -/

/-- The subject of step `10`: `nex-arg` on the eight values pushed after
`callee-pure` (`rin`, `b-ned`, `sub-ned`, `sub-v`, `b-sur`, `sof`,
`call-blocks`, `[sub-ned call-block]`). -/
abbrev crdS9 (NA V8 V7 V6 V5 V4 V3 V2 V1 PV S : Noun) : Noun :=
  C NA (C V8 (C V7 (C V6 (C V5 (C V4 (C V3 (C V2 (C V1 (C PV S)))))))))

/-- The first push of the run of `q` (`+safe-fol-fol`, else the run). -/
noncomputable def crdFq (env : CallEnv) (msup : Option Nomm) (q : Nomm) (th : Jmp) (region : List Nat) :
    CM (TreapMap mugF) (NextL CSet) :=
  if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
  else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region

/-- The model of the tail of the call. -/
noncomputable def crdTailM (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (nexA : NextL CSet)
    (region : List Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let nexFol ← crdFq env msup q nexA.th region
  let nexFol ← pastL noCode nexFol p region
  let nexSub ← runLC env msup p (CGoalL.next nexA.laz nexFol.th) region
  copyL nexSub nexFol.laz

/-- **Step `10`**: `+safe-fol-fol` of `q`, else the run of `q` for
`[%next *need-lazy then.nex-arg]`. -/
theorem crd_cnf (h7 : slot? 7 ctx = some compK) (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (region : List Nat) (x : GenRest) (mono I sup goalN : Noun) (nexA : NextL CSet)
    (V8 V7 V6 V5 V4 V3 V2 V1 PV : Noun) (g : Gen (TreapMap mugF))
    (hq : RunAt env msup ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) nexA.th) region g) :
    nock (crdS9 nexA.goal.toNoun V8 V7 V6 V5 V4 V3 V2 V1 PV
      (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) goalN (listNoun A region) sup (compCore g x ctx))) crDKc10
      = (crdFq env msup q nexA.th region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  have hq1 := hq
  unfold RunAt at hq1
  rw [cgl_next_noun, cr_bunt_noun] at hq1
  rw [cr_next_nounL]
  unfold crDKc10 crdFq
  simp only [crSubj, compCore] at hq1 ⊢
  generalize comp.door = Dr at hq1 ⊢
  cases hs : safeFolFol q with
  | true =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, cr_next_nounL, cr_bunt_noun]
  | false =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, cr_bat_dol, hq1]

/-- **The tail of the call** (steps `10` to `14`): `crd_cnf`, `+past` over
`p` (`comp_past`), the run of `p` for `[%next laz.nex-arg then.nex-fol]`,
`+copy` (`comp_copy_all`). -/
theorem crd_ctail (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (region : List Nat) (x : GenRest) (mono I sup goalN : Noun) (nexA : NextL CSet)
    (V8 V7 V6 V5 V4 V3 V2 V1 PV : Noun) (g : Gen (TreapMap mugF))
    (hq : RunAt env msup ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) nexA.th) region g)
    (hp : ∀ nexF g2 nexF' g3, crdFq env msup q nexA.th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      RunAt env msup ctx x mono sup p (CGoalL.next nexA.laz nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFq env msup q nexA.th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      runLC env msup p (CGoalL.next nexA.laz nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (crdS9 nexA.goal.toNoun V8 V7 V6 V5 V4 V3 V2 V1 PV
      (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) goalN (listNoun A region) sup (compCore g x ctx))) crDKr10
      = (crdTailM env msup p q nexA region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hnf := crd_cnf h7 env msup p q region x mono I sup goalN nexA V8 V7 V6 V5 V4 V3 V2 V1 PV g hq
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  unfold crdTailM
  generalize hF : crdFq env msup q nexA.th region = F at hnf hp hcp
  simp only [crSubj, compCore, crdS9, cr_next_nounL] at hnf ⊢
  cases eq : F g with
  | none =>
    rw [eq] at hnf
    generalize comp.door = Dr at hnf hD1 hD2 ⊢
    unfold crDKr10
    simp [nock_exec, hnf, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hnf
    simp only [Option.map_some, cr_next_nounL] at hnf
    have hpa := comp_past h7 hcode x g2 nexF p region hpn
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode nexF p region g2 with
    | none =>
      rw [e3] at hpa
      generalize comp.door = Dr at hnf hD1 hD2 hpa ⊢
      unfold crDKr10 crDKr11 crDKc11
      simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      have hp1 := hp nexF g2 nexF' g3 eq e3
      unfold RunAt at hp1
      rw [cgl_next_noun] at hp1
      simp only [crSubj, compCore] at hp1
      cases eq2 : runLC (S := CSet) (Map := TreapMap mugF) env msup p
          (CGoalL.next nexA.laz nexF'.th) region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 ⊢
        unfold crDKr10 crDKr11 crDKc11 crDKr12 crDKc12
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 hcpy ⊢
        unfold crDKr10 crDKr11 crDKc11 crDKr12 crDKc12 crDKr13 crDKc13 crDKr14
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2, hD2, cr_cp_arm, hcpy, cr_next_nounL, Function.comp_def]

end Compiler
end Formalization
