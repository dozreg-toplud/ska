import lemmas.Compiler.CompRunRClass
import lemmas.Compiler.CompStraightMapSix
import lemmas.Ska.CompDirectMEq

/-!
# The gate of `+compile-unary` on code with direct calls (README Gaps 19)

`+compile-unary` (K arm `2810`, line 3396) runs `(~(run comp gen) & nomm
[%done ~] ~ ~)` after `+compile-scc-in` and `+comp scc long-ska jets-hot
n-ary-map ~ func`: the run at `mono` `&` with `msup = ~` from `genEntry`,
then `+kerf` and `+to-straight`.  On a nomm of `DirOk` whose direct calls
meet `CallOk` (`DirCalls`) in the context `cuCtx` that `+comp` builds and at
the one rest `cuRest CA` (the cache `+compile-scc-in` returned), the run is
`runLCM env true` (`comp_run_dirMM`), so the gate is `finishLUCM env n`.

* `cu_trap_dir`: the trap, as `cu_trap_six` with `comp_run_dirMM` for the
  run, `res_dir` for what it returns (`LAll CrLok` for `+kerf`),
  `comp_kerf_all`, `ts_at_all`.
* **`cu_gate_dir`**: the gate of `+compile-unary` on `DirOk` is `finishLUCM
  env n`, given `DirCalls`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

/-- **The trap of `+compile-unary` on `DirOk`**: if `+compile-scc-in` returns
`[NM CA]`, `code` holds the nomm `n` at `func` and every direct call of `n`
meets `CallOk` at the rest `cuRest CA`, the trap returns `[[straight NM] CA]`
with `straight` the noun of `finishLUCM env n`, and crashes when that is
`none`. -/
theorem cu_trap_dir (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (hd : DirCalls env CODE (cuCtx FUNC SCC CODE LSR JH NM) (· = cuRest CA) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have hcode : slot? 52 (cuCtx FUNC SCC CODE LSR JH NM) = some CODE := by simp [cuCtx, nock_exec]
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill _ h7
  have hrun := comp_run_dirMM h7 hcode env (· = cuRest CA) n hn Option.none [] hd (CGoal.toL CGoal.done) genEntry
    (show genEntry.drop = false from rfl) (cuRest CA) (cu_entry_nosoft CA) rfl
  simp only [RunAtR, unitNoun] at hrun
  have hres := res_dir h7 hcode env (· = cuRest CA) n hn Option.none [] hd
  rw [cu_trap_entry FUNC SCC CODE LSR JH CACHE NM CA hcsi,
    cu_trap_run FUNC SCC CODE LSR JH CACHE NM CA V n hgot hv, hrun]
  have hf : finishLUCM (S := CSet) (Map := TreapMap mugF) env n
      = ((runLCM env true Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind
          fun p => kerf p.1 p.2).bind
          fun q => toStraightF q.2.cond q.2.blocks (Need.this q.1.2) q.1.1 := by
    rw [Option.bind_assoc]; rfl
  rw [hf]
  cases e : runLCM (S := CSet) (Map := TreapMap mugF) env true Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) []
      genEntry with
  | none => simp
  | some p =>
    obtain ⟨nex, g1⟩ := p
    obtain ⟨-, -, hG, -⟩ := hres CGoalL.done genEntry g1 nex rfl e
    simp only [NextL.goal, GInv] at hG
    have hlok : LAll CrLok nex.laz := lall_mono (fun s h => h.1) hG.1.1
    have hk := comp_kerf_all hc hl hm (cuRest CA) g1 nex (walk_mdP (cu_entry_nosoft CA) g1.bo hlok)
    simp only [compCore] at hk
    simp only [Option.bind_some, Option.map_some, NextL.goal, CGoalL.toNoun]
    rw [cu_trap_kerf, hk]
    cases e2 : kerf nex g1 with
    | none => simp
    | some q =>
      obtain ⟨⟨o, sub⟩, g2⟩ := q
      have h : nock (C tsBat (C (tsSampleN (A o) (C (A 0x73696874) (A sub)))
            (C comp.door (C (genNoun g2 (cuRest CA)) (cuCtx FUNC SCC CODE LSR JH NM))))) tsBat
          = (toStraightF g2.cond g2.blocks (Need.this sub) o).map Straight.toNoun :=
        ts_at_all h7 g2 (cuRest CA) o (Need.this sub) (by simp [flattenNeed, isRun])
      simp only [Option.map_some, Option.bind_some]
      unfold cuS4
      rw [cu_trap_end, tsSample_eq, h, cu_gen_cache]
      cases toStraightF g2.cond g2.blocks (Need.this sub) o <;> rfl

/-- **The gate of `+compile-unary` on `DirOk`** (plan item 0 of README Gaps
19): `finishLUCM env n`, the whole-subject code with the direct calls
through `+mono-try-call`, given `DirCalls` at the rest `cuRest CA`. -/
theorem cu_gate_dir (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (hd : DirCalls env CODE (cuCtx FUNC SCC CODE LSR JH NM) (· = cuRest CA) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  rw [cu_gate_rp, ← cu_trap_dir FUNC SCC CODE LSR JH CACHE NM CA V env n hn hd hcsi hgot hv]
  apply Option.ext
  intro y
  rw [cu_rp_iff]
  have hk : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) rpK
      = nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap := by
    unfold cuTC
    simp [rpK, nock_exec]
  rw [hk]

/-! ## The environment from the samples (plan items (a), (b), (c)) -/

/-- A loobean read back. -/
def unLoob : Noun → Option Bool
  | Noun.atom 0 => some true
  | Noun.atom 1 => some false
  | _ => Option.none

theorem unLoob_eq {w : Noun} {c : Bool} (h : unLoob w = some c) : w = loob c := by
  match w, h with
  | Noun.atom 0, h => simp [unLoob] at h; subst h; rfl
  | Noun.atom 1, h => simp [unLoob] at h; subst h; rfl
  | Noun.atom (_ + 2), h => simp [unLoob] at h
  | Noun.cell _ _, h => simp [unLoob] at h

/-- **`pure` of the code entry of `b`** in the noun `CODE` of `code.long-ska`
(ctx axis `52`): `none` when `b` is not a key or the field is not a loobean. -/
noncomputable def codeOf (CODE : Noun) (b : Bell) : Option Bool :=
  match getF mugF b.toNoun CODE with
  | some (Noun.cell (Noun.atom 0) V) => (slot? 6 V).bind unLoob
  | _ => Option.none

/-- **The ring of `b`** in the noun `COLE` of `call.cole.jets.long-ska` (ctx
axis `6846`, axis `190` of the rest `[jets calls]` of `long-ska`). -/
noncomputable def ringOf (COLE : Noun) (b : Bell) : Option Noun :=
  match getF mugF b.toNoun COLE with
  | some (Noun.cell (Noun.atom 0) r) => some r
  | _ => Option.none

/-- **The environment of the calls is the one of the samples**: `cod` and
`pure` from `code.long-ska`, `ring` from `call.cole` (`need`, `sure`, `sof`
are free). -/
structure EnvFrom (env : CallEnv) (CODE COLE : Noun) : Prop where
  cod : ∀ b, env.cod b = codeOf CODE b
  pure : ∀ b c, codeOf CODE b = some c → env.pure b = c
  ring : ∀ b, getF mugF b.toNoun COLE = some (A 0) → env.ring b = Option.none

/-- The environment of the samples with `need`, `sure`, `sof` given. -/
noncomputable def envOf (CODE COLE : Noun) (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
    (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool) : CallEnv :=
  ⟨need, sure, fun b => (codeOf CODE b).getD false, ringOf COLE, codeOf CODE, sof⟩

theorem envOf_from (CODE COLE : Noun) (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
    (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool) : EnvFrom (envOf CODE COLE need sure sof) CODE COLE :=
  ⟨fun _ => rfl, fun b c h => by simp [envOf, h], fun b h => by simp [envOf, ringOf, h]⟩

/-- (a) **`CodePure` and `env.cod b` from the code entry.** -/
theorem codePure_of {env : CallEnv} {CODE COLE : Noun} (he : EnvFrom env CODE COLE) {b : Bell} {c : Bool}
    (h : codeOf CODE b = some c) : CodePure CODE env b ∧ env.cod b = some (env.pure b) := by
  have hp := he.pure b c h
  refine ⟨?_, by rw [he.cod b, h, hp]⟩
  unfold codeOf at h
  split at h
  · rename_i V hg
    cases hs : slot? 6 V with
    | none => rw [hs] at h; simp at h
    | some w =>
      rw [hs] at h
      exact ⟨V, hg, by rw [hp, hs, unLoob_eq h]⟩
  · simp at h

/-- The context that `+comp` builds: `call.cole` at axis `6846`. -/
theorem cuCtx_cole {FUNC SCC CODE LSR JH NM COLE : Noun} (h : slot? 190 LSR = some COLE) :
    slot? 6846 (cuCtx FUNC SCC CODE LSR JH NM) = some COLE := by
  have : slot? 6846 (cuCtx FUNC SCC CODE LSR JH NM) = slot? 190 LSR := by simp [cuCtx, nock_exec]
  rw [this, h]

/-- (c) `jets-hot` at axis `54`. -/
theorem cuCtx_hot (FUNC SCC CODE LSR JH NM : Noun) : slot? 54 (cuCtx FUNC SCC CODE LSR JH NM) = some JH := by
  simp [cuCtx, nock_exec]

/-- (f) **The push of `sof` returns** (the field `sof` of `CallNounMR`). -/
def SofRet (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (x : GenRest) : Prop :=
  ∃ SOF, ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj (A 0) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some SOF

/-- **What one direct call still takes**, at the rest `x`: the callee has a
code entry in `code.long-ska` (`codeOf`, a fact of the analysis), no ring in
`call.cole`, and its need `nb` (`env.need b`), read by `+callee-need` in a
read-only case (`NeedRead`), `sure.cache` (`SureNoun`), the push of `sof`
returns (`SofRet`). -/
def CallS (env : CallEnv) (CODE COLE ctx : Noun) (x : GenRest) (msup : Option Nomm) (p q : Nomm) (b : Bell) :
    Prop :=
  (∃ c, codeOf CODE b = some c) ∧ getF mugF b.toNoun COLE = some (A 0) ∧
    ∃ nb, env.need b = some nb ∧ NeedRead ctx x b nb ∧ SureNoun env b x ∧ SofRet env msup ctx p q b nb x

/-- **`CallOk` from `CallS`** in a context with `call.cole` the noun `COLE`
and `jets-hot` present, for an environment of the samples. -/
theorem callOk_of_s {ctx : Noun} (h7 : slot? 7 ctx = some compK) {env : CallEnv} {CODE COLE : Noun}
    (he : EnvFrom env CODE COLE) (hcl : slot? 6846 ctx = some COLE) (hhot : ∃ jh, slot? 54 ctx = some jh)
    {x0 : GenRest} {msup : Option Nomm} {p q : Nomm} {b : Bell} (h : CallS env CODE COLE ctx x0 msup p q b) :
    CallOk env CODE ctx (· = x0) msup p q b := by
  obtain ⟨⟨c, hc⟩, hri, nb, hnb, hnr, hsu, SOF, hsof⟩ := h
  obtain ⟨hcd, hcod⟩ := codePure_of he hc
  exact callOk_of_r h7 hcd hcod (he.ring b hri) hnb fun x hx => by
    subst hx
    exact ⟨SOF, ⟨⟨COLE, hcl, hri⟩, hhot, hnr, hsu, hsof⟩⟩

/-- **`CallS` of every direct call**, each at the `msup` its run gets. -/
def DirCallsS (env : CallEnv) (CODE COLE ctx : Noun) (x : GenRest) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => DirCallsS env CODE COLE ctx x ms p ∧ DirCallsS env CODE COLE ctx x ms q
  | ms, Nomm.n2 p q Option.none => DirCallsS env CODE COLE ctx x ms p ∧ DirCallsS env CODE COLE ctx x ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      CallS env CODE COLE ctx x ms p q b ∧ DirCallsS env CODE COLE ctx x ms p ∧ DirCallsS env CODE COLE ctx x ms q
  | ms, Nomm.n3 p => DirCallsS env CODE COLE ctx x ms p
  | ms, Nomm.n4 p => DirCallsS env CODE COLE ctx x ms p
  | ms, Nomm.n5 p q => DirCallsS env CODE COLE ctx x ms p ∧ DirCallsS env CODE COLE ctx x ms q
  | ms, Nomm.n6 p q r =>
      DirCallsS env CODE COLE ctx x ms p ∧ DirCallsS env CODE COLE ctx x ms q ∧ DirCallsS env CODE COLE ctx x ms r
  | ms, Nomm.n7 p q => DirCallsS env CODE COLE ctx x ms p ∧ DirCallsS env CODE COLE ctx x (some p) q
  | ms, Nomm.n10 _ v q => DirCallsS env CODE COLE ctx x ms v ∧ DirCallsS env CODE COLE ctx x ms q
  | _, _ => True

theorem dirCalls_of_s {ctx : Noun} (h7 : slot? 7 ctx = some compK) {env : CallEnv} {CODE COLE : Noun}
    (he : EnvFrom env CODE COLE) (hcl : slot? 6846 ctx = some COLE) (hhot : ∃ jh, slot? 54 ctx = some jh)
    {x0 : GenRest} : ∀ (ms : Option Nomm) (n : Nomm), DirCallsS env CODE COLE ctx x0 ms n →
      DirCalls env CODE ctx (· = x0) ms n
  | ms, Nomm.cons p q, h => ⟨dirCalls_of_s h7 he hcl hhot ms p h.1, dirCalls_of_s h7 he hcl hhot ms q h.2⟩
  | _, Nomm.n0 _, _ => trivial
  | _, Nomm.n1 _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h => ⟨dirCalls_of_s h7 he hcl hhot ms p h.1, dirCalls_of_s h7 he hcl hhot ms q h.2⟩
  | ms, Nomm.n2 p q (some (b, _)), h =>
    ⟨callOk_of_s h7 he hcl hhot h.1, dirCalls_of_s h7 he hcl hhot ms p h.2.1, dirCalls_of_s h7 he hcl hhot ms q h.2.2⟩
  | ms, Nomm.n3 p, h => dirCalls_of_s h7 he hcl hhot ms p h
  | ms, Nomm.n4 p, h => dirCalls_of_s h7 he hcl hhot ms p h
  | ms, Nomm.n5 p q, h => ⟨dirCalls_of_s h7 he hcl hhot ms p h.1, dirCalls_of_s h7 he hcl hhot ms q h.2⟩
  | ms, Nomm.n6 p q r, h =>
    ⟨dirCalls_of_s h7 he hcl hhot ms p h.1, dirCalls_of_s h7 he hcl hhot ms q h.2.1,
      dirCalls_of_s h7 he hcl hhot ms r h.2.2⟩
  | ms, Nomm.n7 p q, h => ⟨dirCalls_of_s h7 he hcl hhot ms p h.1, dirCalls_of_s h7 he hcl hhot (some p) q h.2⟩
  | ms, Nomm.n10 _ v q, h => ⟨dirCalls_of_s h7 he hcl hhot ms v h.1, dirCalls_of_s h7 he hcl hhot ms q h.2⟩
  | _, Nomm.n11s _ _ _, _ => trivial
  | _, Nomm.n11d _ _ _ _, _ => trivial
  | _, Nomm.n12 _ _, _ => trivial
  | _, Nomm.mean _ _ _ _ _, _ => trivial

/-- **The gate of `+compile-unary` on `DirOk`, with the environment of the
samples** (plan items 0, (a), (b), (c) of README Gaps 19): `env` has `cod`,
`pure` of `code.long-ska` and `ring` of `call.cole` (`EnvFrom`; `envOf`), and
every direct call has `CallS` at the rest `cuRest CA`: a code entry, no ring,
`NeedRead`, `SureNoun`, `SofRet`. -/
theorem cu_gate_dir_s (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hn : DirOk n = true) (he : EnvFrom env CODE COLE) (hcl : slot? 190 LSR = some COLE)
    (hd : DirCallsS env CODE COLE (cuCtx FUNC SCC CODE LSR JH NM) (cuRest CA) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA :=
  cu_gate_dir FUNC SCC CODE LSR JH CACHE NM CA V env n hn
    (dirCalls_of_s rfl he (cuCtx_cole hcl) ⟨JH, cuCtx_hot FUNC SCC CODE LSR JH NM⟩ Option.none n hd) hcsi hgot hv

end Compiler
end Formalization
