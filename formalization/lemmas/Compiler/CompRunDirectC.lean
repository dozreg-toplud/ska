import lemmas.Compiler.CompRunDirectKN
import lemmas.Compiler.CompRunDirect
import lemmas.Compiler.CompSccIn

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

/-! ## Step `7`: the call blocks, `mono` `|`, no key, no ring, `sof` `|` -/

/-- The subject of step `7`: `sof` (`|`), `b-sur`, `sub-v`, `sub-ned`,
`b-ned`, `rin` (`~`), `callee-pure` on the subject of `$`. -/
abbrev crdS6 (V5 SV SN V2 PV S : Noun) : Noun :=
  C (A 1) (C V5 (C SV (C SN (C V2 (C (A 0) (C PV S))))))

/-- The noun of a direct call with no memo key. -/
abbrev crdN (p q : Nomm) (b : Bell) : Noun := C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (A 0)))))

/-- The tail of the noun of a goal. -/
noncomputable def crdGoalT : CGoalL CSet → Noun
  | CGoalL.pick z o => C z.toNoun o.toNoun
  | CGoalL.done => A 0
  | CGoalL.next laz th => C laz.toNoun th.toNoun

/-- The model of step `7` (`callL`): under `%done` one block `[~ ~ %jmp b
sub-v]`; otherwise `+simple-next`, `+kerf` and `[~ [%cal b sub-v pro]~ %hop
~ out]`. -/
noncomputable def crdBlockM (b : Bell) (subV : List Nat) : CGoalL CSet → CM (TreapMap mugF) Nat
  | CGoalL.done => emit ⟨[], [], Termin.jmp b subV⟩
  | g => do
      let nex ← simpleNextL g
      let (out, pro) ← kerf nex
      emit ⟨[], [Pole.cal b subV pro], Termin.hop (jmp0 out)⟩

/-- **Step `7` under `%done`**: the test of `%done` with no key, `mono` `|`,
one `+emit` of `[~ ~ (jump-op ~)]` (`[%jmp b sub-v]`, no ring), the `=?` of
`sof` (`|`, the state kept). -/
theorem crd_blk_done (hc : CompIn ctx) (x : GenRest) (V5 V2 PV : Noun) (subNed : Need) (p q : Nomm) (b : Bell)
    (region : List Nat) (sup : Noun) (g : Gen (TreapMap mugF)) :
    nock (crdS6 V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) sup (compCore g x ctx)))
      crDKc7
      = (crdBlockM b (flattenNeed subNed) CGoalL.done g).map fun p => C (A p.1) (genNoun p.2 x) := by
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.jmp] at he
  have hD := comp_emit_at
  simp only [crdBlockM, cf_emit_g, Option.map_some]
  simp only [crSubj, compCore] at he ⊢
  generalize comp.door = Dr at he hD ⊢
  unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7D crD7Ur0 crD7Uc0 crD7Ur1
  simp [nock_exec, CGoalL.toNoun, hD, comp_emit_arm, he]

theorem crd_blob_cal (b : Bell) (v : List Nat) (d t : Nat) :
    Blob.toNoun ⟨[], [Pole.cal b v d], Termin.hop (jmp0 t)⟩
      = C (A 0) (C (C (C (A 0x6c6163) (C b.toNoun (C (listNoun A v) (A d)))) (A 0)) (C (A 0x706f68) (C (A 0) (A t)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.cal, Jmp.toNoun, jmp0]

/-- **Step `7` on a `%next` or `%pick` goal**: the test of `%done` fails,
`+simple-next` (`comp_simple_next`), `+kerf` (`comp_kerf_all`), `mono` `|`,
one `+emit` of `[~ [(call-op ~ pro)]~ %hop ~ out]` (`[%cal b sub-v pro]`, no
ring), the `=?` of `sof` (`|`). -/
theorem crd_blk_next (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (V5 V2 PV : Noun)
    (subNed : Need) (p q : Nomm) (b : Bell) (region : List Nat) (sup : Noun) (goal : CGoalL CSet)
    (hgd : goal ≠ CGoalL.done) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    nock (crdS6 V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockM b (flattenNeed subNed) goal g).map fun p => C (A p.1) (genNoun p.2 x) := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  have hmod : crdBlockM b (flattenNeed subNed) goal = (do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      emit ⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : CM (TreapMap mugF) Nat) := by
    cases goal with
    | done => exact absurd rfl hgd
    | _ => rfl
  have htd : ∃ k, goal.toNoun = C (A k) (crdGoalT goal) ∧ k ≠ 0x656e6f64 := by
    cases goal with
    | done => exact absurd rfl hgd
    | next laz th => exact ⟨_, rfl, by decide⟩
    | pick z o => exact ⟨_, rfl, by decide⟩
  obtain ⟨k, hk, hkd⟩ := htd
  have hkd' : (0x656e6f64 : Nat) ≠ k := fun h => hkd h.symm
  have hsn := comp_simple_next hc x g goal (A 1) (crdN p q b) (listNoun A region) sup
  rw [hmod, bind_apply]
  simp only [crSubj, compCore] at hsn ⊢
  cases e : simpleNextL (S := CSet) (Map := TreapMap mugF) goal g with
  | none =>
    rw [e] at hsn
    simp only [Option.map_none] at hsn
    rw [hk] at hsn ⊢
    generalize comp.door = Dr at hsn ⊢
    unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0
    simp [nock_exec, crdS6, hsn, cr_bat_sn, hkd, hkd']
  | some r =>
    obtain ⟨nex0, g1⟩ := r
    rw [e] at hsn
    simp only [Option.map_some] at hsn
    obtain ⟨-, -, ⟨⟨lnb, -⟩, d1, -⟩, -⟩ := simpleNextL_res hinv e
    have hkf := comp_kerf_all hc hl hm x g1 nex0 (walk_mdP hx g1.bo (lall_mono (fun _ hs => hs.1) lnb))
    have hD1 := comp_kerf_at
    have hD3 := comp_emit_at
    rw [cr_next_nounL] at hsn
    simp only [compCore] at hkf
    cases ek : kerf nex0 g1 with
    | none =>
      rw [ek] at hkf
      rw [hk] at hsn ⊢
      generalize comp.door = Dr at hsn hkf hD1 hD3 ⊢
      unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0 crD7Nr1 crD7Nc1
      simp [nock_exec, crdS6, hsn, cr_bat_sn, hkd, hkd', hD1, comp_kerf_arm, hkf, bind, StateT.bind, ek]
    | some r2 =>
      obtain ⟨⟨out, pro⟩, g2⟩ := r2
      rw [ek] at hkf
      simp only [Option.map_some] at hkf
      have he := cf_emit (x := x) hc g2 ⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩
      rw [crd_blob_cal] at he
      rw [hk] at hsn ⊢
      generalize comp.door = Dr at hsn hkf hD1 hD3 he ⊢
      unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0 crD7Nr1 crD7Nc1 crD7Ne crD7Vr0 crD7Vc0 crD7Vr1
      simp [nock_exec, crdS6, hsn, cr_bat_sn, hkd, hkd', hD1, comp_kerf_arm, hkf, bind, StateT.bind, ek, hD3, comp_emit_arm,
        he, cf_emit_g]

/-! ## Steps `7` to `14` -/

/-- The `next` of the argument: `[%next (lazy-from-need sub-ned) ~ call-block]`. -/
noncomputable def crdArg (subNed : Need) (cb : Nat) : NextL CSet := ⟨Lazy.ofSure ⟨subNed, HoonSet.empty⟩, jmp0 cb⟩

/-- The model of the call from step `7` on. -/
noncomputable def crdCallM (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (subNed : Need)
    (goal : CGoalL CSet) (region : List Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let cb ← crdBlockM b (flattenNeed subNed) goal
  crdTailM env msup p q (crdArg subNed cb) region

theorem crd_arg_noun (subNed : Need) (cb : Nat) :
    (crdArg subNed cb).goal.toNoun
      = C (A 0x7478656e) (C (C (C subNed.toNoun (A 0)) (C (A 0) (A 0))) (C (A 0) (A cb))) := by
  simp [crdArg, cr_next_nounL, Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun, HoonSet.toNoun_empty, Jmp.toNoun,
    jmp0, listNoun]

/-- **Steps `7` to `14`**: the call blocks (given, `hblk`), `?@` of an atom
(step `8`), `nex-arg` with `(~(has by soft.gen) call-block)` `|` under
`NoSoft` (step `9`), and the tail (`crd_ctail`). -/
theorem crd_from7 (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (region : List Nat) (x : GenRest) (hx : x.NoSoft) (V5 V2 PV sup : Noun) (subNed : Need) (b : Bell)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF))
    (hblk : nock (crdS6 V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockM b (flattenNeed subNed) goal g).map fun p => C (A p.1) (genNoun p.2 x))
    (hq : ∀ cb g1, crdBlockM b (flattenNeed subNed) goal g = some (cb, g1) →
      RunAt env msup ctx x (A 1) sup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g1)
    (hp : ∀ cb g1 nexF g2 nexF' g3, crdBlockM b (flattenNeed subNed) goal g = some (cb, g1) →
      crdFq env msup q (jmp0 cb) region g1 = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      RunAt env msup ctx x (A 1) sup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g3)
    (hcp : ∀ cb g1 nexF g2 nexF' g3 nexS g4, crdBlockM b (flattenNeed subNed) goal g = some (cb, g1) →
      crdFq env msup q (jmp0 cb) region g1 = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      runLC env msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (crdS6 V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKr7
      = (crdCallM env msup p q b subNed goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h15 := cr_ctx15 h7
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  unfold crdCallM
  rw [bind_apply]
  simp only [crSubj, compCore, crdS6] at hblk ⊢
  cases eb : crdBlockM b (flattenNeed subNed) goal g with
  | none =>
    rw [eb] at hblk
    generalize comp.door = Dr at hblk ⊢
    unfold crDKr7
    simp [nock_exec, hblk]
  | some r =>
    obtain ⟨cb, g1⟩ := r
    rw [eb] at hblk
    simp only [Option.map_some] at hblk
    have ht := crd_ctail h7 hcode env msup p q hpn region x (A 1) (C (A 0) (C b.toNoun (A 0))) sup goal.toNoun
      (crdArg subNed cb) (C subNed.toNoun (A cb)) (A cb) (A 1) V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2
      (A 0) PV g1 (hq cb g1 eb) (fun nexF g2 nexF' g3 e e3 => hp cb g1 nexF g2 nexF' g3 eb e e3)
      (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => hcp cb g1 nexF g2 nexF' g3 nexS g4 eb e e3 e4)
    rw [crd_arg_noun] at ht
    have hs := crn_has x cb (hx cb)
    simp only [crSubj, compCore, crdS9] at ht
    generalize comp.door = Dr at hblk ht ⊢
    unfold crDKr7 crDKr8 crDKc8 crDKr9 crDKc9
    simp [nock_exec, hblk, h15, hc, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, by_arm, by.arm_at, by.has.arm_at, has_arm, hs,
      ht]

/-! ## Steps `1` to `6`, under the hypotheses on the rest of the compiler -/

/-- The battery of the gate `+callee-need` (door arm `221180`). -/
noncomputable def cneBat : Noun := (slot? 29 ((slot? 221180 comp.door).getD (A 0))).getD (A 0)

theorem cne_at : slot? 221180 comp.door
    = some (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) cneBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The battery of the gate `+callee-sure` (door arm `4060`). -/
noncomputable def csuBat : Noun := (slot? 29 ((slot? 4060 comp.door).getD (A 0))).getD (A 0)

theorem csu_at : slot? 4060 comp.door
    = some (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) csuBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- **What the call reads of the rest of the compiler, as nouns** (README
Gaps 19), for the callee `b` with no key, `nb` its need in the model
(`env.need b = some nb`), `sur` what `+callee-sure` returns:
* `cole`: `call.cole.jets.long-ska` (axis `6846` of the context) has no
  entry for `b` (the model's `env.ring b = none`);
* `hot`: `jets-hot` (axis `54`) is there (`biff` builds its `get` gate);
* `need`: `+callee-need` returns `nb` and leaves the state as it is, on
  every state with this rest `x` (it reads `cache`, which `x` holds);
* `sure`: `+callee-sure` (`gut:by` of `sure.cache`) returns `sur`;
* `sof`: the push of `sof` is `|` (the model's `env.sof … = false`), on
  every state, `sub-ned`, `sub-v`, `callee-pure`, goal and region: it reads
  none of them. -/
structure CallNoun (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd) (sur : Noun)
    (x : GenRest) : Prop where
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  hot : ∃ jh, slot? 54 ctx = some jh
  need : ∀ g : Gen (TreapMap mugF),
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x))
  sure : ∀ g : Gen (TreapMap mugF), nock (C csuBat (C b.toNoun (compCore g x ctx))) csuBat = some sur
  sof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C sur (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj (A 1) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some (A 1)

/-- **Steps `0` to `6`**: `rin` (`get:by`, `~`), `b-ned` (no key:
`+callee-need`), `sub-ned` (`noar_gate`), `sub-v` (`comp_flatten_need`),
`b-sur` (`biff` of `~`, then `+callee-sure`), `sof` (`|`), then step `7` on. -/
theorem crd_head6 (h7 : slot? 7 ctx = some compK) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (sur : Noun) (x : GenRest) (hn : CallNoun msup ctx p q b nb sur x) (PV goalN : Noun) (region : List Nat)
    (g : Gen (TreapMap mugF)) :
    nock (C PV (crSubj (A 1) (crdN p q b) goalN (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g x ctx)))
      crDCall
      = (needOrdAllocRegs nb g).bind fun r => nock (crdS6 sur (listNoun A (flattenNeed r.1)) r.1.toNoun nb.toNoun PV
          (crSubj (A 1) (crdN p q b) goalN (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore r.2 x ctx)))
          crDKr7 := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨cole, hcole, hgc⟩ := hn.cole
  obtain ⟨jh, hjh⟩ := hn.hot
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole (A 0) hgc
  have hne := hn.need g
  have hnoar := noar_gate ctx x nb g
  have hD1 := cne_at
  have hD2 := noar_at
  have hD3 := comp_fn_at
  have hD4 := csu_at
  rw [crdk_eq]
  simp only [crSubj, compCore, crdS6] at hne hnoar ⊢
  cases e : needOrdAllocRegs nb g with
  | none =>
    rw [e] at hnoar
    generalize comp.door = Dr at hne hnoar hD1 hD2 hD3 hD4 ⊢
    unfold crDKr0 crDKr1 crDKc1 crDKr2 crDKc2 crDKr3 crDKc3
    simp [nock_exec, crdN, hc, hcole, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hD1, hne, hD2, noarHint, h7, hnoar, e]
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    rw [e] at hnoar
    simp only [Option.map_some] at hnoar
    have hfn := comp_flatten_need hc (genNoun g1 x) subNed
    have hsu := hn.sure g1
    have hsof := hn.sof g1 (listNoun A (flattenNeed subNed)) subNed.toNoun PV goalN (listNoun A region)
    simp only [crSubj, compCore] at hsu hsof
    generalize comp.door = Dr at hne hnoar hD1 hD2 hD3 hD4 hfn hsu hsof ⊢
    unfold crDKr0 crDKr1 crDKc1 crDKr2 crDKc2 crDKr3 crDKc3 crDKr4 crDKc4 crDKr5 crDKc5 crDKr6
    simp [nock_exec, crdN, hc, hcole, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hD1, hne, hD2, noarHint, h7, hnoar, hD3,
      comp_fn_arm, hfn, hjh, biff_arm, biff.arm_at, biff_gate_nil, hD4, hsu, hsof]

/-! ## The drop test where it fails, the model, the call -/

/-- Whether the call is dropped (`callL`): a pure callee on a `%next` goal
whose need asks nothing. -/
noncomputable def crdDrop (pu : Bool) : CGoalL CSet → Bool
  | CGoalL.next laz _ => pu && Lazy.noneEquivalentL laz
  | _ => false

/-- **The test of the drop on every goal**: `&(callee-pure ?=(%next -.goal)
(none-equivalent laz.goal))` is `crdDrop`; on `%done` and `%pick` it fails at
`?=(%next -.goal)`, on an impure callee at `callee-pure`. -/
theorem crd_test_all (h7 : slot? 7 ctx = some compK) (N mono region sup : Noun) (pu : Bool) (goal : CGoalL CSet)
    (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C (loob pu) (crSubj mono N goal.toNoun region sup (compCore g x ctx))) crDTest
      = some (loob (crdDrop pu goal)) := by
  cases pu with
  | true =>
    cases goal with
    | next laz th => exact crd_test h7 N mono region sup laz th g x
    | done => unfold crDTest; simp [nock_exec, crSubj, CGoalL.toNoun, crdDrop, loob]
    | pick z o => unfold crDTest; simp [nock_exec, crSubj, CGoalL.toNoun, crdDrop, loob]
  | false =>
    unfold crDTest
    cases goal <;> simp [nock_exec, crSubj, CGoalL.toNoun, crdDrop, loob]

/-- **The model of the call** (`callL` with a known callee, no key, no ring,
`sof` false, not dropped): `+need-ord-alloc-regs`, then `crdCallM`. -/
theorem crd_model_call (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (goal : CGoalL CSet) (region : List Nat) (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    (hpc : hinted env.cod p = hinted noCode p) :
    (runLC env msup (Nomm.n2 p q (some (b, Option.none))) goal region : CM (TreapMap mugF) (NextL CSet))
      = needOrdAllocRegs nb >>= fun subNed => crdCallM env msup p q b subNed goal region := by
  cases goal with
  | next laz th =>
    simp only [crdDrop] at hdr
    simp only [runLC, callL, hdr, hri, hnb, hsof, Bool.false_eq_true, if_false, pastL_cod hpc]
    unfold crdCallM crdTailM crdFq crdArg crdBlockM
    rfl
  | done =>
    simp only [runLC, callL, hri, hnb, hsof, Bool.false_eq_true, if_false, pastL_cod hpc]
    unfold crdCallM crdTailM crdFq crdArg crdBlockM
    rfl
  | pick z o =>
    simp only [runLC, callL, hri, hnb, hsof, Bool.false_eq_true, if_false, pastL_cod hpc]
    unfold crdCallM crdTailM crdFq crdArg crdBlockM
    rfl

/-- **The call after the drop test** (steps `0` to `14`): `crd_head6`, then
step `7` by the goal (`crd_blk_done`, `crd_blk_next`) and `crd_from7`. -/
theorem crd_call_body (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none) (b : Bell)
    (nb : NeedOrd) (sur : Noun) (x : GenRest) (hx : x.NoSoft) (hn : CallNoun msup ctx p q b nb sur x) (PV : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : GInv g goal)
    (hpq : ∀ subNed g1, needOrdAllocRegs nb g = some (subNed, g1) →
      (∀ cb g2, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        RunAt env msup ctx x (A 1) (unitNoun Nomm.toNoun msup) q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb))
          region g2) ∧
      (∀ cb g2 nexF g3 nexF' g4, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        crdFq env msup q (jmp0 cb) region g2 = some (nexF, g3) → pastL noCode nexF p region g3 = some (nexF', g4) →
        RunAt env msup ctx x (A 1) (unitNoun Nomm.toNoun msup) p
          (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4) ∧
      (∀ cb g2 nexF g3 nexF' g4 nexS g5, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        crdFq env msup q (jmp0 cb) region g2 = some (nexF, g3) → pastL noCode nexF p region g3 = some (nexF', g4) →
        runLC env msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4 = some (nexS, g5) →
        CopyH g5.re nexS.laz nexF'.laz)) :
    nock (C PV (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup)
      (compCore g x ctx))) crDCall
      = ((needOrdAllocRegs nb >>= fun subNed => crdCallM env msup p q b subNed goal region :
          CM (TreapMap mugF) (NextL CSet)) g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  rw [crd_head6 h7 msup p q b nb sur x hn PV goal.toNoun region g, bind_apply]
  cases e : needOrdAllocRegs nb g with
  | none => rfl
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    obtain ⟨⟨k, hk⟩, hre, -, -⟩ := needOrdAllocRegs_spec nb g g1 subNed e
    have hinv1 : GInv g1 goal := ginv_mono hinv hre (by rw [hk]; exact Nat.le_refl _) (by rw [hk])
    obtain ⟨hq, hp, hcp⟩ := hpq subNed g1 e
    have hblk : nock (crdS6 sur (listNoun A (flattenNeed subNed)) subNed.toNoun nb.toNoun PV
        (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g1 x ctx)))
        crDKc7 = (crdBlockM b (flattenNeed subNed) goal g1).map fun p => C (A p.1) (genNoun p.2 x) := by
      by_cases hgd : goal = CGoalL.done
      · subst hgd; exact crd_blk_done hc x sur nb.toNoun PV subNed p q b region _ g1
      · exact crd_blk_next h7 x hx sur nb.toNoun PV subNed p q b region _ goal hgd g1 hinv1
    simp only [Option.bind_some]
    exact crd_from7 h7 hcode env msup p q hpn region x hx sur nb.toNoun PV _ subNed b goal g1 hblk hq hp hcp

/-- **The case `%2` on a direct call that emits a block** (README Gaps 19),
one instance (`RunAt`) at `mono` `|` and `sup` the noun of `msup`: a callee
`b` with no memo key whose code entry has `pure` `env.pure b` (`CodePure`),
the call not dropped (`crdDrop`), no ring, `env.need b = some nb`, `sof`
false, the rest `x` of the state with `NoSoft` and `CallNoun`, every goal with
`GInv`; the runs of `q` and `p` for the goals of the call (`hpq`). -/
theorem comp_run_n2_call (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hpl : PlainOk p = true) (b : Bell) (hcd : CodePure cod env b)
    (nb : NeedOrd) (sur : Noun) (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF))
    (hinv : GInv g goal) (hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = Option.none)
    (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    (x : GenRest) (hx : x.NoSoft) (hn : CallNoun msup ctx p q b nb sur x)
    (hpq : ∀ subNed g1, needOrdAllocRegs nb g = some (subNed, g1) →
      (∀ cb g2, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        RunAt env msup ctx x (A 1) (unitNoun Nomm.toNoun msup) q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb))
          region g2) ∧
      (∀ cb g2 nexF g3 nexF' g4, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        crdFq env msup q (jmp0 cb) region g2 = some (nexF, g3) → pastL noCode nexF p region g3 = some (nexF', g4) →
        RunAt env msup ctx x (A 1) (unitNoun Nomm.toNoun msup) p
          (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4) ∧
      (∀ cb g2 nexF g3 nexF' g4 nexS g5, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        crdFq env msup q (jmp0 cb) region g2 = some (nexF, g3) → pastL noCode nexF p region g3 = some (nexF', g4) →
        runLC env msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4 = some (nexS, g5) →
        CopyH g5.re nexS.laz nexF'.laz)) :
    RunAt env msup ctx x (A 1) (unitNoun Nomm.toNoun msup) (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨hpc, hpn⟩ := hinted_plain env.cod hpl
  obtain ⟨V, hgot, hv⟩ := hcd
  unfold RunAt
  rw [crd_model_call env msup p q b nb goal region hdr hri hnb hsof hpc, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id Option.none) V _ (A 1)
    goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) g x hgot hv
  have ht := crd_test_all h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id Option.none))))))
    (A 1) (listNoun A region) (unitNoun Nomm.toNoun msup) (env.pure b) goal g x
  rw [hdr] at ht
  have hcall := crd_call_body h7 hcode env msup p q hpn b nb sur x hx hn (loob (env.pure b)) goal region g hinv hpq
  simp only [crdN] at hcall
  have hu : unitNoun (id : Noun → Noun) Option.none = A 0 := rfl
  rw [hu] at hpure ht ⊢
  have hl : loob false = A 1 := rfl
  rw [hl] at ht
  unfold crDHead
  simp [nock_exec, hpure, ht, hcall]

end Compiler
end Formalization
