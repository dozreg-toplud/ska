import lemmas.Compiler.CompLift

/-!
# The trap of `+compile-unary`

```hoon
  =/  args  +<
  %-  road-pure  |.
  =^  n-ary-map=(map bell straight)  cache  (compile-scc-in +.args)
  =/  comp  (comp scc long-ska jets-hot n-ary-map ~ func)
  =|  gen=line-short
  =.  cache.gen  cache
  =^  nex=next  gen
    (~(run comp gen) & nomm:(~(got by code.long-ska) func) [%done ~] ~ ~)
  =^  [o=@uwoo sub=@uvre]  gen  (~(kerf comp gen) nex)
  :_  cache.gen
  :-  (~(to-straight comp gen) [%next [[this+sub ~] ~ ~] ~ o])
  n-ary-map
```

The gate of `+compile-unary` (battery `cuGB`, at axis `179885` of `K`)
pushes `args` and `road-pure` and slams `road-pure` on the trap core
`[cuTrap [args [cuGB [sam K]]]]` (`cuTC`).  The trap (`cuTrap`, axis
`1473626077` of `K`, `cu_trap_at`) is cut into its calls: `cuCsi` (the call
of `+compile-scc-in`, arm `2732` of `K`, on `+.args`), the edit of the
gate's `cache` (axis `1007`), `cuCompCall` (the gate `+comp`, arm `5590` of
`K`, whose battery `cgBat` builds the door `[comp.door [cuBunt ctx]]`), the
`=|` and `=.` of `cu_entry_step`, `cuRunCall` (`~(run comp gen)` on `&`,
the nomm of `(~(got by code) func)`, `[%done ~]`, `~`, `~`),
`cuAfterRun` (the `=^` of the run, `cuKerfCall`, the `=^` of `+kerf`),
and `cuEnd` (`cuTsCall`, the pair with `n-ary-map`, `cache.gen` at `3838`).

Every face the trap reads (`func`, `scc`, `long-ska`, `jets-hot`, `cache`)
is the gate's sample, not the copy `args`, so the edit of `cache` reaches
the door and the state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The call `(compile-scc-in +.args)`. -/
def cuCsi : Noun :=
  C (A 8) (C (C (A 9) (C (A 2732) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))

/-- The call `(comp scc long-ska jets-hot n-ary-map ~ func)`. -/
def cuCompCall : Noun :=
  C (A 8) (C (C (A 9) (C (A 5590) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 506)) (C (C (A 0) (A 1014)) (C (C (A 0) (A 2030)) (C (C (A 0) (A 6)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 252)))))))) (C (A 0) (A 2)))))))

/-- `nomm:(~(got by code.long-ska) func)`. -/
def cuGot : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 8172))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1020))) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))

/-- The sample of the run: `&`, the nomm, `[%done ~]`, `~`, `~`. -/
def cuRunSam : Noun :=
  C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) cuGot))
    (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f64) (A 0)))))
      (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))))

/-- `(~(run comp gen) ..)`. -/
def cuRunCall : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 3071) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) cuRunSam) (C (A 0) (A 2)))))))

/-- `(~(kerf comp gen) nex)`. -/
def cuKerfCall : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 0xabb4) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))

/-- The sample `[%next [[this+sub ~] ~ ~] ~ o]` of `+to-straight`. -/
def cuTsSam : Noun :=
  C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x7478656e)) (C (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 5)))
    (C (A 1) (A 0))) (C (A 1) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 4))))))

/-- `(~(to-straight comp gen) ..)`. -/
def cuTsCall : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 0) (A 30)) (C (A 9) (C (A 0x2aec) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2))))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) cuTsSam) (C (A 0) (A 2)))))))

/-- The `=^` of `+kerf` and the product `[[straight n-ary-map] cache.gen]`. -/
def cuEnd : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 14) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
    (C (C cuTsCall (C (A 0) (A 62))) (C (A 0) (A 3838))))))

/-- The `=^` of the run, then the call of `+kerf`. -/
def cuAfterRun : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 6) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
    (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) cuKerfCall)) cuEnd)))))))

/-- After `=.  cache.gen  cache`: the run and the rest. -/
def cuEntry : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) cuRunCall)) cuAfterRun)))

/-- The `=|` and the `=.` of `cache.gen`, then the run. -/
def cuR3 : Noun :=
  C (A 8) (C (C (A 1) cuBunt) (C (A 7) (C (C (A 10) (C (C (A 766) (C (A 0) (A 4079))) (C (A 0) (A 1)))) cuEntry)))

/-- **The trap of `+compile-unary`.** -/
def cuTrap : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) cuCsi))
    (C (A 7) (C (C (A 10) (C (C (A 1007) (C (A 0) (A 5))) (C (A 0) (A 1))))
      (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
        (C (A 8) (C cuCompCall cuR3)))))))))

/-- The trap in the pill, a kernel fact. -/
theorem cu_trap_at : slot? 1473626077 compK = some cuTrap := by kernel_rfl

/-- The battery of the gate of `+compile-unary`. -/
def cuGB : Noun :=
  C (A 8) (C (C (A 0) (A 6)) (C (A 8) (C (C (A 0) (A 4094)) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) cuTrap) (C (A 0) (A 1)))))) (C (A 0) (A 2)))))))))

theorem cu_gb_at : slot? 179885 compK = some cuGB := by kernel_rfl

/-- The sample bunt of `+comp`, read from the pill. -/
noncomputable def cuCgBunt : Noun := (slot? 44725 compK).getD (A 0)

/-- The battery of the gate `+comp`: the door with the bunt of `line-short`. -/
def cgBat : Noun := C (A 8) (C (C (A 1) cuBunt) (C (C (A 1) comp.door) (C (A 0) (A 1))))

/-- **The arm `+comp`** of `K`, a kernel fact. -/
theorem cu_comp_at : slot? 5590 compK
    = some (C (A 8) (C (C (A 1) cuCgBunt) (C (C (A 1) cgBat) (C (A 0) (A 1))))) := by kernel_rfl

/-- The slam of `+comp`: the door `[comp.door [cuBunt ctx]]`. -/
theorem cu_cg_slam (X : Noun) :
    nock (C cgBat X) cgBat = some (C comp.door (C cuBunt (C cgBat X))) := by
  conv => { lhs; arg 2; unfold cgBat }
  simp only [nock_exec]

/-! ## The subjects -/

/-- The gate's sample `[func scc long-ska jets-hot cache]`, with
`long-ska` as `[code rest]`. -/
def cuSam (FUNC SCC CODE LSR JH CACHE : Noun) : Noun := C FUNC (C SCC (C (C CODE LSR) (C JH CACHE)))

/-- The trap core: the trap on `[args gate]`. -/
def cuTC (SAM : Noun) : Noun := C cuTrap (C SAM (C cuGB (C SAM compK)))

/-- The context of the door: the gate `+comp` with its sample. -/
def cuCtx (FUNC SCC CODE LSR JH NM : Noun) : Noun :=
  C cgBat (C (C SCC (C (C CODE LSR) (C JH (C NM (C (A 0) FUNC))))) compK)

/-- The subject after `+compile-scc-in` returned `[NM CA]`: the gate's
`cache` is `CA`. -/
def cuS4 (FUNC SCC CODE LSR JH CACHE NM CA : Noun) : Noun :=
  C NM (C cuTrap (C (cuSam FUNC SCC CODE LSR JH CACHE) (C cuGB (C (cuSam FUNC SCC CODE LSR JH CA) compK))))

/-- **From the trap core to the entry of the run**: `+compile-scc-in`, the
edit of `cache`, `+comp`, the `=|` and the `=.`. -/
theorem cu_trap_entry (FUNC SCC CODE LSR JH CACHE NM CA : Noun)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA)) :
    nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = nock (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA))
          (C (C comp.door (C cuBunt (cuCtx FUNC SCC CODE LSR JH NM)))
            (cuS4 FUNC SCC CODE LSR JH CACHE NM CA))) cuEntry := by
  have he := cu_entry_step (C (C comp.door (C cuBunt (cuCtx FUNC SCC CODE LSR JH NM)))
    (cuS4 FUNC SCC CODE LSR JH CACHE NM CA)) cuEntry CA (by simp [cuS4, cuSam, nock_exec])
  rw [← he]
  conv => { lhs; arg 2; unfold cuTrap }
  unfold cuTC at hcsi ⊢
  simp only [cuSam] at hcsi
  simp [nock_exec, hcsi, cuSam, cuS4, cuCtx, cuCompCall, cu_comp_at, cu_cg_slam, cuR3]

/-- The noun of the goal `[%done ~]`. -/
theorem cu_done_noun : (CGoal.toL (CGoal.done : CGoal CSet)).toNoun = C (A 0x656e6f64) (A 0) := by
  rfl

/-- **The run of the trap**: the door with `gen`, the nomm of `+got:by`
of `code` at `func`, the gate `+run` on `[& nomm [%done ~] ~ ~]`. -/
theorem cu_trap_run (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA))
        (C (C comp.door (C cuBunt (cuCtx FUNC SCC CODE LSR JH NM)))
          (cuS4 FUNC SCC CODE LSR JH CACHE NM CA))) cuEntry
      = (nock (crSubj (A 0) n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) (A 0)
          (compCore genEntry (cuRest CA) (cuCtx FUNC SCC CODE LSR JH NM))) crDol).bind fun R =>
        nock (C R (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA))
          (C (C comp.door (C cuBunt (cuCtx FUNC SCC CODE LSR JH NM)))
            (cuS4 FUNC SCC CODE LSR JH CACHE NM CA)))) cuAfterRun := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := got_gate layer2 hgc FUNC CODE V hgot
  have hL := compK_layer2
  have hr := comp_run_at
  rw [cu_done_noun]
  simp only [compCore]
  conv => { lhs; arg 2; unfold cuEntry }
  generalize genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA) = GN
  unfold cuS4 cuSam
  generalize cuCtx FUNC SCC CODE LSR JH NM = CTX
  generalize comp.door = Dr at hr ⊢
  simp [nock_exec, cuRunCall, cuRunSam, cuGot, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, hv, hr,
    crArm, crB, crBat, crSubj, listNoun]

/-- **The `=^` of the run and the call of `+kerf`.** -/
theorem cu_trap_kerf (NEXN G1N GN S4 CTX : Noun) :
    nock (C (C NEXN G1N) (C GN (C (C comp.door (C cuBunt CTX)) S4))) cuAfterRun
      = (nock (C kerfBat (C NEXN (C comp.door (C G1N CTX)))) kerfBat).bind fun K =>
          nock (C K (C NEXN (C G1N (C (C comp.door (C cuBunt CTX)) S4)))) cuEnd := by
  have hk := comp_kerf_at
  conv => { lhs; arg 2; unfold cuAfterRun }
  generalize comp.door = Dr at hk ⊢
  simp [nock_exec, cuKerfCall, hk, comp_kerf_arm]

/-- **The call of `+to-straight` and the product** `[[straight n-ary-map]
cache.gen]`. -/
theorem cu_trap_end (o sub : Nat) (G2N NEXN G1N NM S4R CTX : Noun) :
    nock (C (C (C (A o) (A sub)) G2N) (C NEXN (C G1N (C (C comp.door (C cuBunt CTX)) (C NM S4R))))) cuEnd
      = (nock (C tsBat (C (tsSample (A o) (A sub)) (C comp.door (C G2N CTX)))) tsBat).bind fun ST =>
          (slot? 510 G2N).bind fun CA2 => some (C (C ST NM) CA2) := by
  have hts := comp_ts_at
  conv => { lhs; arg 2; unfold cuEnd }
  generalize comp.door = Dr at hts ⊢
  simp [nock_exec, cuTsCall, cuTsSam, hts, comp_ts_arm, tsSample, Option.bind_assoc]

/-- `cache` of the state is axis `510` of its noun. -/
theorem cu_gen_cache (g : Gen (TreapMap mugF)) (x : GenRest) : slot? 510 (genNoun g x) = some x.cache := by
  simp only [genNoun, nock_exec]

/-- **The trap of `+compile-unary`** on a pure nomm with no `%6` and no
`%10` at axis `0`: if `+compile-scc-in` returns `[NM CA]` and `code` holds
`V` at `func` with the nomm `n` at its head, the trap returns
`[[straight NM] CA]` with `straight` the noun of `finishLU n`, and crashes
when `finishLU n` is `none`.  The cache it returns is `CA`, the one that
`+compile-scc-in` returned: `+run`, `+kerf` and `+to-straight` keep it. -/
theorem cu_trap (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (n : Nomm)
    (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map fun st => C (C st.toNoun NM) CA := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have hcode : slot? 52 (cuCtx FUNC SCC CODE LSR JH NM) = some CODE := by simp [cuCtx, nock_exec]
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill _ h7
  have hts : TsAt (cuCtx FUNC SCC CODE LSR JH NM) :=
    ts_at_of_step hc h7 (ts_step_at hc (lf_ts_rj hc))
  rw [cu_trap_entry FUNC SCC CODE LSR JH CACHE NM CA hcsi,
    cu_trap_run FUNC SCC CODE LSR JH CACHE NM CA V n hgot hv,
    cu_entry_run h7 hcode n hpu h6 ht CA (A 0) (A 0)]
  have hf : finishLU (S := CSet) (Map := TreapMap mugF) n
      = ((runL n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind fun p => kerf p.1 p.2).bind
          fun q => toStraightF q.2.cond q.2.blocks (Need.this q.1.2) q.1.1 := by
    rw [Option.bind_assoc]; rfl
  rw [hf]
  have hce := cu_cond_empty n hpu h6
  rw [runL_toL n hpu h6] at hce ⊢
  cases e : run (S := CSet) (Map := TreapMap mugF) n CGoal.done genEntry with
  | none => simp [e, Functor.map, StateT.map]
  | some p =>
    obtain ⟨nex, g1⟩ := p
    have hk := comp_kerf hc hl hm (cuRest CA) g1 nex (cu_entry_nosoft CA g1.bo)
      (cra_run_lok n hpu h6 CGoal.done genEntry g1 nex e trivial)
    simp only [compCore] at hk
    simp only [e, Functor.map, StateT.map, bind, pure, Option.bind_some, Option.map_some,
      cr_next_noun] at hce ⊢
    rw [cu_trap_kerf, hk]
    cases e2 : kerf (Next.toL nex) g1 with
    | none => simp
    | some q =>
      obtain ⟨⟨o, sub⟩, g2⟩ := q
      have h := hts g2 (cuRest CA) sub o (hce o sub g2 e2)
      simp only [compCore] at h
      simp only [Option.map_some, Option.bind_some]
      unfold cuS4
      rw [cu_trap_end, h, cu_gen_cache]
      cases toStraightF g2.cond g2.blocks (Need.this sub) o <;> rfl

/-- `road-pure` in `K` (axis `254` of `compTypes`), a kernel fact. -/
theorem cu_rp_in_K : slot? 510 compK = some (C rpBat (C rpSam rpCtx)) := by kernel_rfl

/-- The gate of `+compile-unary` pushes `args` and `road-pure` and slams
`road-pure` on the trap core. -/
theorem cu_gate_rp (SAM : Noun) :
    nock (C cuGB (C SAM compK)) cuGB = nock (C rpBat (C (cuTC SAM) rpCtx)) rpBat := by
  have hrp := cu_rp_in_K
  conv => { lhs; arg 2; unfold cuGB }
  unfold cuTC
  generalize compK = Kc at hrp ⊢
  simp [nock_exec, hrp]

/-- **The gate of `+compile-unary`** on its sample `[func scc long-ska
jets-hot cache]`, with `long-ska` as `[code rest]`: the trap's product
(`cu_trap`) through `road-pure` (`cu_rp_iff`), with the same hypotheses. -/
theorem cu_gate (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (n : Nomm)
    (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map fun st => C (C st.toNoun NM) CA := by
  rw [cu_gate_rp, ← cu_trap FUNC SCC CODE LSR JH CACHE NM CA V n hpu h6 ht hcsi hgot hv]
  apply Option.ext
  intro y
  rw [cu_rp_iff]
  have hk : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) rpK
      = nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap := by
    unfold cuTC
    simp [rpK, nock_exec]
  rw [hk]

end Compiler
end Formalization
