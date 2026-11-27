import lemmas.Compiler.CompCalleeCompOne
import lemmas.Compiler.PokeLinkSccHit
import lemmas.Compiler.CompSccSixBake

/-!
# `CalleeCompiled` for a one-bell callee (README Gaps 19 (g))

The miss of `+callee-compiled` calls `+scc-of` on the callee.  In the
whole-subject run of `+compile-unary` that call takes the CACHE HIT path of
`+scc-of` (`[u.s sccs]`, no `sub` loop, no `+tarjan`): the poke's own
`+scc-of` on `func` put the SCC of every bell `func` reaches into
`sccs.cache` (measured, `tools/hoon/sccofhit.py`: 107 of 107 misses in
`nary.cache` over the 37 `%full` pokes of `calleecomp.py` found the callee in
`sccs.cache`, SCC sizes 1 (91), 2 (8), 3 (7), 4 (1)).

* `sccBat_hitN`: the battery of `+scc-of` (track P's `sccBat`,
  `Compiler/PokeLinkSccHit.lean`) on any `sccs` noun with an entry for `b`
  returns it and `sccs` unchanged; `sccCore_compK`: its core is `K`;
* **`ccc_scc_hit`**: the push of `+scc-of` in the miss branch of
  `+callee-compiled` (`cccSccF`) on a cache whose `sccs` has the entry;
* `RInl SC0 inl`: the predicate on rests that every one-bell compile keeps:
  `sccs.cache` is `SC0`, `inl.cache` is a map whose entry for a key `k` with
  `inl k = some nm` is absent or `nm`;
* `CompOne`: what the caller's `env` must say of the callee `b`: the need
  of the model's straight and its sure need (the agreement facts; an `env`
  read from the FINAL cache gives them, `compOne_of_final`);
* **`calleeCompiled_one`**: `CalleeCompiled env (RInl SC0 inl) ctx b nb` for a
  callee `b` with no self call, `SixOk` code, `sccs` entry `[b ~ ~]`, from
  track A's one-bell chain with the real bake (`csi_gate_scc_one_f_six_B`:
  `FixRet`, `BakeRunO`), `cccMiss_one`, `ext_one`, `putF_spec`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The cache hit of `+scc-of` on any `sccs` noun -/

/-- **The battery of `+scc-of` on a `sccs` noun with an entry for `B`**:
`[S sccs]`. -/
theorem sccBat_hitN {B CA SC S : Noun} (hg : getF mugF B SC = some (C (A 0) S)) :
    nock (C sccBat (C (C B (C CA SC)) sccCore)) sccBat = some (C S SC) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg' := get_gate layer2 hgc B SC _ hg
  rw [sccBat_run]
  have h1 : nock (C sccBat (C (C B (C CA SC)) sccCore)) sccGetF = some (C (A 0) S) := by
    simp [sccGetF, sccCore_hoon, by.arm_at, by_arm, by.get.arm_at, get_arm, nock_exec, hg']
  rw [h1]
  simp [sccTestF, sccHitF, nock_exec]

/-- The core of `+scc-of` is `K`, the core of `+comp`. -/
theorem sccCore_compK : sccCore = compK := by kernel_rfl

/-- **The push of `+scc-of` in the miss branch of `+callee-compiled` on a
cache hit**: `sccs` (axis `14` of `cache`) has the entry `S` for `b`; the
product is `[S sccs]`.  The context gives `K` at axis `7` and `calls` at
axis `107`. -/
theorem ccc_scc_hit {ctx CL : Noun} (h7 : slot? 7 ctx = some compK) (h107 : slot? 107 ctx = some CL)
    (b : Bell) {NR MO SC RS SO SS S : Noun} (hg : getF mugF b.toNoun SC = some (C (A 0) S))
    (g : Gen (TreapMap mugF)) :
    nock (cccS0 b g (ccRest NR MO SC RS SO SS) ctx) cccSccF = some (C S SC) := by
  have ha := sccCore_arm
  have hh := sccBat_hitN (CA := CL) hg
  rw [sccCore_compK] at ha hh
  unfold cccS0 cccSccF
  simp only [compCore, genNoun, ccRest]
  generalize compK = KC at ha hh h7 ⊢
  simp [nock_exec, ha, h7, h107, sccHint, hh]

/-- **`CccMiss` of a one-bell callee on the cache hit of `+scc-of`**:
`cccMiss_one` with the `+scc-of` gate discharged by `ccc_scc_hit` (the
`sccs` entry of `b` is `[b ~ ~]`, `sccs` unchanged). -/
theorem cccMiss_hit_one {ctx LONG JH CL : Noun} (h7 : slot? 7 ctx = some compK) (hl : slot? 26 ctx = some LONG)
    (hj : slot? 54 ctx = some JH) (h107 : slot? 107 ctx = some CL) (b : Bell) (nb : NeedOrd)
    {NR MO SC RS SO SS st CA' : Noun} (hg : getF mugF b.toNoun SC = some (C (A 0) (setOne b.toNoun)))
    (hcsi1 : nock (C csiBody (C (csiSam (setOne b.toNoun) LONG JH (C NR (C MO (C SC RS)))) compK)) csiBody
      = some (C (C (C b.toNoun st) (C (A 0) (A 0))) CA'))
    (hst : slot? 2 st = some nb.toNoun) :
    CccMiss ctx b nb NR MO SC RS SO SS CA' :=
  cccMiss_one h7 hl hj b nb (fun g => ccc_scc_hit h7 h107 b hg g) hcsi1 hst

/-! ## The predicate the one-bell compiles keep -/

/-- **`sccs` fixed and `inl` entries known**: `sccs.cache` is `SC0`;
`inl.cache` is a map, and for every key `k` with `inl k = some nm` its
entry is absent or `nm` (what `+inlined` stores for a callee with no direct
call: the nomm of its code). -/
def RInl (SC0 : Noun) (inl : Noun → Option Nomm) (x : GenRest) : Prop :=
  ∃ NR MO INL SU, x.cache = cacheN NR MO SC0 INL SU ∧ IsMap mugF INL ∧
    ∀ k nm, inl k = some nm → getF mugF k INL = some (A 0) ∨ getF mugF k INL = some (C (A 0) nm.toNoun)

/-- After `+put:by`, the key holds the new value. -/
theorem getF_put_self {M M' k v : Noun} (hm : IsMap mugF M) (hp : putF mugF k v M = some M') :
    IsMap mugF M' ∧ getF mugF k M' = some (C (A 0) v) := by
  obtain ⟨out, hput, hmo, hget⟩ := putF_spec mugF M k v hm
  rw [hp] at hput
  cases hput
  exact ⟨hmo, getF_some hmo ((hget k v).2 (Or.inl ⟨rfl, rfl⟩))⟩

/-- After `+put:by`, another key reads as before. -/
theorem getF_put_other {M M' k v k' : Noun} (hm : IsMap mugF M) (hp : putF mugF k v M = some M') (hne : k' ≠ k) :
    getF mugF k' M' = getF mugF k' M := by
  obtain ⟨out, hput, hmo, hget⟩ := putF_spec mugF M k v hm
  rw [hp] at hput
  cases hput
  by_cases hx : ∃ u, Get M k' u
  · obtain ⟨u, hu⟩ := hx
    rw [getF_some hm hu, getF_some hmo ((hget k' u).2 (Or.inr ⟨hne, hu⟩))]
  · have hn : ∀ u, ¬ Get M k' u := fun u h => hx ⟨u, h⟩
    rw [getF_none hm hn, getF_none hmo fun u h => ?_]
    rcases (hget k' u).1 h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne h1
    · exact hn u h2

/-- A lookup after `+put:by`: the new key, or an old entry. -/
theorem getF_put_cases {M M' k v k' u : Noun} (hm : IsMap mugF M) (hp : putF mugF k v M = some M')
    (h : getF mugF k' M' = some (C (A 0) u)) :
    (k' = k ∧ u = v) ∨ (k' ≠ k ∧ getF mugF k' M = some (C (A 0) u)) := by
  by_cases e : k' = k
  · subst e
    rw [(getF_put_self hm hp).2] at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  · rw [getF_put_other hm hp e] at h
    exact Or.inr ⟨e, h⟩

/-! ## What the caller's `env` says of the callee -/

/-- **The agreement facts of a one-bell callee** `b = [[cape DATA] FOL]`:
the model's compile of its nomm `nm` (on the callee's own `envb`, the
run, `+shape-collapse` with `fuel`, the final pass with `+bake-need` of
`less.b`) returns `p` and the straight `st`, and the caller's `env` reads
`st`'s need and the sure need `sccSur p.1 cape` for `b`. -/
def CompOne (env envb : CallEnv) (cape : Cape) (DATA : Noun) (nm : Nomm) (fuel : Nat)
    (p : NextL CSet × Gen (TreapMap mugF)) (st : Straight (TreapMap mugF)) (b : Bell) : Prop :=
  runLC envb Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some p ∧
  finishLFC (S := CSet) (Map := TreapMap mugF) envb nm (scOrd fuel p.1 cape) cape
    (fun n => bakeNeed n (Sock.mk cape DATA)) = some st ∧
  env.need b = some st.need ∧ env.sure b = sccSur p.1 cape

/-- **The agreement facts from the final cache**: an entry of `nary.cache`
and of `sure.cache` at a rest `y` persists along `Ext` to the final rest
`z`, where `AgreeE env` makes it `env`'s.  So an `env` that agrees with the
final cache agrees with the entries every miss put. -/
theorem compOne_of_final {env : CallEnv} {y z : GenRest} (he : Ext y z) (hA : AgreeE env z) {b : Bell}
    {NR SU st sur : Noun} (hNR : slot? 2 y.cache = some NR) (hSU : slot? 31 y.cache = some SU)
    (hn : getF mugF b.toNoun NR = some (C (A 0) st)) (hs : getF mugF b.toNoun SU = some (C (A 0) sur)) :
    (∃ nb, env.need b = some nb ∧ slot? 2 st = some nb.toNoun) ∧ sur = (env.sure b).toNoun := by
  obtain ⟨-, -, h2, h31⟩ := he
  obtain ⟨N', hN', hsN⟩ := h2 NR hNR
  obtain ⟨S', hS', hsS⟩ := h31 SU hSU
  obtain ⟨-, NRz, MOz, SCz, INLz, SUz, hc, -, -, hag, hsa⟩ := hA
  have e2 : N' = NRz := by rw [hc] at hN'; simpa [cacheN, nock_exec] using hN'.symm
  have e31 : S' = SUz := by rw [hc] at hS'; simpa [cacheN, nock_exec] using hS'.symm
  subst e2 e31
  exact ⟨(hag b st (hsN _ _ hn)).1, (hsa b sur (hsS _ _ hs)).1⟩

/-! ## `CalleeCompiled` on one bell -/

/-- **`CalleeCompiled` for a one-bell callee** `b = [[cape DATA] FOL]` with no
self call, whose code entry holds the nomm `nm` in `SixOk` (no direct call),
at every rest with `AgreeE` and `RInl SC0 inl` where `sccs` holds `[b ~ ~]`
for `b` and `inl` gives `nm`.  Track A's hypotheses of the callee's run:
`NoAx0`, `FixRet` (the loop of `+inter2-collapse` stops within `fuel`) and
`BakeRunO` (the residual of `+bake-need` is a run); the agreement facts
`CompOne`.  The context: `K` at `7`, `long-ska` `[CODE JETS CALLS]` at `26`
(so `calls` at `107`), `jets-hot` at `54`. -/
theorem calleeCompiled_one {ctx CODE JETS CALLS JH SC0 : Noun} (h7 : slot? 7 ctx = some compK)
    (hl : slot? 26 ctx = some (C CODE (C JETS CALLS))) (hj : slot? 54 ctx = some JH)
    (h107 : slot? 107 ctx = some CALLS) (env envb : CallEnv) (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat)
    (p : NextL CSet × Gen (TreapMap mugF)) (st : Straight (TreapMap mugF)) (inl : Noun → Option Nomm)
    (hsc : getF mugF (C (C cape.toNoun DATA) FOL) SC0 = some (C (A 0) (setOne (C (C cape.toNoun DATA) FOL))))
    (hinl : inl (C (C cape.toNoun DATA) FOL) = some nm)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (hcode : ∃ V, getF mugF (C (C cape.toNoun DATA) FOL) CODE = some (C (A 0) V) ∧ slot? 2 V = some nm.toNoun)
    (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfix : FixRet envb nm cape fuel)
    (hbake : BakeRunO envb nm (fun nex => scOrd fuel nex cape) cape DATA)
    (hone : CompOne env envb cape DATA nm fuel p st ⟨Sock.mk cape DATA, FOL⟩) :
    CalleeCompiled env (RInl SC0 inl) ctx ⟨Sock.mk cape DATA, FOL⟩ st.need := by
  intro x NR MO SC RS hA hR hcx h0
  obtain ⟨xc, xs, xf⟩ := x
  simp only at hcx h0 ⊢
  subst hcx
  obtain ⟨hns, NR1, MO1, SC1, INL, SU, hc1, hnr, hsu, hag, hsa⟩ := hA
  obtain ⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩ := hR
  simp only [cacheN, Noun.cell.injEq] at hc1
  obtain ⟨e1, e2, e3, e4⟩ := hc1
  subst NR1 MO1 SC1 RS
  simp only [cacheN, Noun.cell.injEq] at hc2
  obtain ⟨e5, e6, e7, e8, e9⟩ := hc2
  subst NR2 MO2 INL2 SU2 SC
  have hBb : (⟨Sock.mk cape DATA, FOL⟩ : Bell).toNoun = (C (C cape.toNoun DATA) FOL) := rfl
  -- `b` is absent from `sure.cache` too
  have hsu0 : getF mugF (C (C cape.toNoun DATA) FOL) SU = some (A 0) := by
    rcases getF_cases (k := (C (C cape.toNoun DATA) FOL)) hsu with h | ⟨v, hv⟩
    · exact h
    · obtain ⟨-, u, hu⟩ := hsa ⟨Sock.mk cape DATA, FOL⟩ v hv
      exact absurd (hu.symm.trans h0) (by simp)
  -- `+inlined`
  obtain ⟨INL', hiok, hil', hin'⟩ : ∃ INL', InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL' ∧ IsMap mugF INL' ∧
      ∀ k nm', inl k = some nm' → getF mugF k INL' = some (A 0) ∨ getF mugF k INL' = some (C (A 0) nm'.toNoun) := by
    rcases hin (C (C cape.toNoun DATA) FOL) nm hinl with hi0 | hi1
    · obtain ⟨INL', hp, hmo, -⟩ := putF_spec mugF INL (C (C cape.toNoun DATA) FOL) nm.toNoun hil
      refine ⟨INL', Or.inr ⟨hi0, hcode, hp⟩, hmo, fun k nm' hk => ?_⟩
      by_cases e : k = (C (C cape.toNoun DATA) FOL)
      · subst e
        rw [hinl] at hk
        cases hk
        exact Or.inr (getF_put_self hil hp).2
      · rw [getF_put_other hil hp e]
        exact hin k nm' hk
    · exact ⟨INL, Or.inl ⟨hi1, rfl⟩, hil, hin⟩
  -- track A's chain
  obtain ⟨hrun, hfin, hneed, hsure⟩ := hone
  have hcsi := csi_gate_scc_one_f_six_B (fun _ => True) tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NR MO SC0 INL SU
    h0 hnr hsu hcalls nm INL' hiok envb hn hax (fun nex => scOrd fuel nex cape)
    (scAt_of_scRet envb nm cape fuel (scRet_of_fixRet envb hn hax cape fuel hfix)) (fun _ _ _ => trivial) hbake
  obtain ⟨NRU, hpn, hmn, -⟩ := putF_spec mugF NR (C (C cape.toNoun DATA) FOL) st.toNoun hnr
  obtain ⟨SUU, hps, hms, -⟩ := putF_spec mugF SU (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun hsu
  rw [hrun] at hcsi
  simp only [Option.bind_some, hfin, hpn, hps, Option.map_some] at hcsi
  have hst : slot? 2 st.toNoun = some st.need.toNoun := by simp [Straight.toNoun, nock_exec]
  have hmiss := cccMiss_hit_one h7 hl hj h107 ⟨Sock.mk cape DATA, FOL⟩ st.need (RS := C INL SU) (SO := xs) (SS := xf)
    hsc hcsi hst
  refine ⟨cacheN NRU MO SC0 INL' SUU, hmiss, ext_one hnr hsu h0 hsu0 hpn hps, ?_, ?_, ?_⟩
  · -- `AgreeE` at the new cache
    refine ⟨fun o => hns o, NRU, MO, SC0, INL', SUU, rfl, hmn, hms, fun b' u hu => ?_, fun b' v hv => ?_⟩
    · rcases getF_put_cases hnr hpn hu with ⟨e, rfl⟩ | ⟨-, hu'⟩
      · have eb : b' = ⟨Sock.mk cape DATA, FOL⟩ := by
          obtain ⟨l, f⟩ := b'
          cases l <;> simp [Bell.toNoun, Sock.toNoun] at e
          · obtain ⟨⟨h1, h2⟩, h3⟩ := e
            subst h2 h3
            have := congrArg Cape.ofNoun? h1
            simp [Cape.ofNoun?_toNoun] at this
            subst this
            rfl
        subst eb
        exact ⟨⟨st.need, hneed, hst⟩, _, (getF_put_self hsu hps).2⟩
      · obtain ⟨h1, v, hv⟩ := hag b' u hu'
        exact ⟨h1, v, mapSub_put hsu hsu0 hps _ _ hv⟩
    · rcases getF_put_cases hsu hps hv with ⟨e, rfl⟩ | ⟨-, hv'⟩
      · have eb : b' = ⟨Sock.mk cape DATA, FOL⟩ := by
          obtain ⟨l, f⟩ := b'
          cases l <;> simp [Bell.toNoun, Sock.toNoun] at e
          · obtain ⟨⟨h1, h2⟩, h3⟩ := e
            subst h2 h3
            have := congrArg Cape.ofNoun? h1
            simp [Cape.ofNoun?_toNoun] at this
            subst this
            rfl
        subst eb
        exact ⟨by rw [hsure], _, (getF_put_self hnr hpn).2⟩
      · obtain ⟨h1, u, hu⟩ := hsa b' v hv'
        exact ⟨h1, u, mapSub_put hnr h0 hpn _ _ hu⟩
  · exact ⟨NRU, MO, INL', SUU, rfl, hil', hin'⟩
  · refine ⟨NRU, st.toNoun, ?_, ?_⟩
    · show slot? 2 (cacheN NRU MO SC0 INL' SUU) = some NRU
      simp [cacheN, nock_exec]
    · exact (getF_put_self hnr hpn).2

end Compiler
end Formalization
