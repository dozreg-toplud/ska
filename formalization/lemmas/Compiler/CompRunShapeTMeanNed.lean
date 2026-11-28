import lemmas.Compiler.CompRunShapeTMeanPre

/-!
# `%mean`, the pushes after `l-fol`: the need, `l-arg`, the end (track A, 2026-11-28)

Each on an abstract subject `rsmS5 ..`:
* **`rsm_ned`**: `rsmNed` (`+mean-konst`, then `[%none ~]` on a konst, else `+callee-need`, which moves
  the rest from `y` to `y'`).
* **`rsm_r5`**: the `=^` of the need, then `rsmArg` and `rsmEnd` at the rest `y'`.
* **`rsm_arg`**: `rsmArg` is `rsmArgM` (`+sound` of `p`, else `+id` and `+put:in` of `sofs`).
* **`rsm_end`**: the `=^` of `l-arg`, the run of `p` (from `y` to `y'`), `+laze-copy` with `l-fol`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **The need push of `%mean`**: `+mean-konst` (`rmk_gate`); on a konst `[%none ~]` at the same rest,
else `+callee-need`, from `y` to `y'`. -/
theorem rsm_ned (hc : CompIn ctx) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) (b : Bell)
    (k : Option Noun) (hmp : MeanPure cod env b k) (LFOL I LF GOL SIM P Q BODY GN SN : Noun) (st : RSt CSet)
    (y y' : RsRest) (kon : Bool) (ek : meanKonstS env b k = some kon) (ned : NeedOrd)
    (hk : kon = false → nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C ned.toNoun (rsGenNoun st y')))
    (ht : kon = true → ned = NeedOrd.none ∧ y' = y) :
    nock (rsmS5 LFOL I LF GOL SIM (meanN P b Q BODY k) GN SN (rsDoor st y ctx)) rsmNed
      = some (C ned.toNoun (rsGenNoun st y')) := by
  have hmk := rmk_gate hc hcode env b k hmp (rsGenNoun st y)
  rw [ek] at hmk
  simp only [Option.map_some] at hmk
  unfold rsmNed rsmS5
  cases kon with
  | false =>
    have h := hk rfl
    simp only [rsDoor] at h
    simp only [Bool.false_eq_true, if_false] at hmk
    simp [nock_exec, rsS, rsCoreG, rsDoor, meanN, rmk_at', rmkArm, hmk, rsd_cne_at', h]
  | true =>
    obtain ⟨rfl, rfl⟩ := ht rfl
    rcases k with _ | kk
    · simp [meanKonstS] at ek
    · simp only [if_true, unitNoun, id] at hmk
      simp [nock_exec, rsS, rsCoreG, rsDoor, meanN, rmk_at', rmkArm, hmk, unitNoun, NeedOrd.toNoun, Tag.none]

/-- **The `=^` of the need**, then `rsmArg` and `rsmEnd` on the subject at the rest `y'` the need
push returns. -/
theorem rsm_r5 (LFOL I LF GOL SIM NOM GN SN : Noun) (st : RSt CSet) (y y' : RsRest) (NED : Noun)
    (hned : nock (rsmS5 LFOL I LF GOL SIM NOM GN SN (rsDoor st y ctx)) rsmNed = some (C NED (rsGenNoun st y'))) :
    nock (rsmS5 LFOL I LF GOL SIM NOM GN SN (rsDoor st y ctx)) rsmR5
      = (nock (C NED (rsmS5 LFOL I LF GOL SIM NOM GN SN (rsDoor st y' ctx))) rsmArg).bind fun X =>
          nock (C X (C NED (rsmS5 LFOL I LF GOL SIM NOM GN SN (rsDoor st y' ctx)))) rsmEnd := by
  unfold rsmR5 rsmTis
  simp only [rsmS5, rsS, rsCoreG, rsDoor] at hned ⊢
  generalize rsmNed = N at hned
  generalize rsmArg = AR
  generalize rsmEnd = EN
  generalize rsGenNoun st y' = G' at hned ⊢
  simp [nock_exec, hned]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod)
include hc h7 hcode hcn

/-- **`l-arg`**: `[[ned ~] ~ ~]` when `(sound p ned)`, else a bond with a new identifier put in
`sofs` (the rest is kept). -/
theorem rsm_arg (p : Nomm) (b : Bell) (Q BODY : Noun) (k : Option Noun) (ned : NeedOrd) (s : Bool)
    (hs : soundS env p ned = some s) (LFOL I LF GOL SIM GN SN : Noun) (st : RSt CSet) (y : RsRest) :
    nock (C ned.toNoun (rsmS5 LFOL I LF GOL SIM (meanN p.toNoun b Q BODY k) GN SN (rsDoor st y ctx))) rsmArg
      = (rsmArgM env p ned st).map fun r => C r.1.toNoun (rsGenNoun r.2 y) := by
  have hsn := rsd_snd h7 hcode (rsGenNoun st y) p.toNoun ned.toNoun
  have hsf := sf_gate env.cod cod hcn 3 p ned s hs
  have hs' : soundS env p ned = some s := hs
  unfold rsmArg rsmS5
  cases s with
  | true =>
    simp [nock_exec, rsS, rsCoreG, rsDoor, meanN, rsd_snd_at', snd_arm, hsn, hsf, loob, rsmArgM, shLiftS, hs',
      bind, StateT.bind, pure, StateT.pure, nedL, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun,
      HoonSet.toNoun_empty]
  | false =>
    have hpu := cs_put_in st.sofs st.idg
    have hid := rs_id (ctx := ctx) st y
    simp only [rsGenNoun] at hid hsn
    have hc' : slot? 262143 ctx = some layer2 := hc
    simp [nock_exec, rsS, rsCoreG, rsDoor, rsGenNoun, meanN, rsd_snd_at', snd_arm, hsn, hsf, loob, rsmArgM,
      shLiftS, hs', bind, StateT.bind, pure, StateT.pure, nedL, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun,
      SureO.toNoun, SureO.bunt, NeedOrd.toNoun, Tag.none, HoonSet.toNoun_empty, idS, putSofs, lzp_id_at',
      comp_id_at, hid, hc', in.arm_at, in_arm, in.put.arm_at, put_in_arm, hpu]

end

/-- **The end of `%mean`**: the `=^` of `l-arg` (the rest `y` it returns), the run of `p` on it
from `y` to `y'`, `+laze-copy` of its `laze` with `l-fol` (`LF0`). -/
theorem rsm_end (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (env : ShapeEnv) (p : Nomm) (sup : Option Nomm)
    (b : Bell) (Q BODY : Noun) (k : Option Noun) (la LF0 : Laze CSet) (st : RSt CSet) (y y' : RsRest)
    (NED X1 X2 GOL SIM GN : Noun) (st0 : RSt CSet) (y0 : RsRest)
    (hp' : nock (rsCoreG p.toNoun (GoalS.next la).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = (runShape env sup p (GoalS.next la) st).map fun r => C r.1.toNoun (rsGenNoun r.2 y')) :
    nock (C (C la.toNoun (rsGenNoun st y)) (C NED (rsmS5 LF0.toNoun X1 X2 GOL SIM (meanN p.toNoun b Q BODY k) GN
      (supNoun sup) (rsDoor st0 y0 ctx)))) rsmEnd
      = ((runShape env sup p (GoalS.next la) st).bind fun r =>
          (lazeCopy r.1 LF0).map fun l => (l, r.2)).map fun r => C r.1.toNoun (rsGenNoun r.2 y') := by
  simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
  unfold rsmEnd rsmS5
  cases e : runShape env sup p (GoalS.next la) st with
  | none =>
    rw [e] at hp'
    simp [nock_exec, rsS, rsCoreG, rsDoor, meanN, hp']
  | some r =>
    obtain ⟨lt, st1⟩ := r
    rw [e] at hp'
    have hlc := lc_all hc h7 (rsGenNoun st1 y') lt LF0
    cases e4 : lazeCopy lt LF0 with
    | none =>
      rw [e4] at hlc
      simp [nock_exec, rsS, rsCoreG, rsDoor, meanN, hp', lc_at', lc_arm, hlc, e4]
    | some l =>
      rw [e4] at hlc
      simp [nock_exec, rsS, rsCoreG, rsDoor, meanN, hp', lc_at', lc_arm, hlc, e4]

end Compiler
end Formalization
