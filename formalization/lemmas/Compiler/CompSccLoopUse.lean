import lemmas.Compiler.CompSccLoopInd
import lemmas.Compiler.CompUnaryDir

/-! # `csi_gate_loop` for the gate of `+compile-unary` (track K's hypotheses, README Gaps 21.11)

* `hcsi_of_loop`: track K's `hcsi` (the call of `+compile-scc-in` in the trap of
  `+compile-unary` returns `[NM CA]`) from `csi_gate_loop`, with `NM` the map of the final pass
  and `CA` the last member run's cache with `nary` united.
* `csiNeeds_of_loop`, `csiSures_of_loop`: track K's `CsiNeeds` and `CsiSures` for callees inside
  the SCC, for `R` that holds `MlNeeds` (each entry of the model's `ml` is the need, at axis 2,
  of the straight at that bell of `map-local`) and `SureHolds` (each entry of the model's
  `sure` is the entry of `sure.cache`), with `env.need`, `env.sure` read off the model's final
  state. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

/-- `map-local` holds the model's needs: at a bell with an entry `n`, a straight whose head is
`n`. -/
def MlNeeds (ml : Noun → Option NeedOrd) (ML : Noun) : Prop :=
  ∀ b n, ml b = some n → ∃ u, getF mugF b ML = some (C (A 0) u) ∧ slot? 2 u = some n.toNoun

/-- `sure.cache` (axis 31 of the cache) holds the model's `sure` at the bells of `bs`, and has
no entry where the model has none (then the read is `[%none ~]`). -/
def SureHolds (bs : List Noun) (sure : Noun → Option NeedOrd) (CA : Noun) : Prop :=
  ∃ S, slot? 31 CA = some S ∧ ∀ b ∈ bs,
    (∃ v, sure b = some v ∧ getF mugF b S = some (C (A 0) v.toNoun)) ∨
      (sure b = none ∧ getF mugF b S = some (A 0))

/-- **`hcsi` from the loop**: under the hypotheses of `csi_gate_loop` (on the sample
`[SCC [CODE LSR] JH CA0]`) and that the final pass's cache is a cell on which `+uni:by` returns
(`hfin`), the call of `+compile-scc-in` in the trap of `+compile-unary` returns `[M CA]` with
`R` of the model's result `s` on `M` and the last member run's cache. -/
theorem hcsi_of_loop {N : Type} [DecidableEq N] (c : Cfg Noun N)
    (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (FUNC SCC CODE LSR JH CA0 KIDS ORD : Noun)
    (hlevy : nock (C csiBody (C (csiSam SCC (C CODE LSR) JH CA0) compK)) csiLevy = some (A 1))
    (hkidsP : nock (C (A 0) (C csiBody (C (csiSam SCC (C CODE LSR) JH CA0) compK))) csiKids
      = some KIDS)
    (hdn : nock (C KIDS (C (A 0) (C csiBody (C (csiSam SCC (C CODE LSR) JH CA0) compK)))) csiDone
      = some (A 1))
    (p : LoopP) (hp : p = ⟨A 1, KIDS, SCC, C CODE LSR, JH, CA0, A 0, A 0, ORD⟩)
    (hR0 : ∀ ml sure ML CA, R ml sure ML CA → R (fun _ => none) sure (A 0) CA)
    (hmay : MemGate c R p.ctx (fun _ => c.none) (A 0) Mode.may (A 0x79616d))
    (hdone : MemGate c R p.ctx (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64))
    (st0 : St Noun N)
    (hmust : ∀ MAY CA1, R (maySweep c st0).ml (maySweep c st0).sure MAY CA1 →
      ∃ TOP, nock (C MAY (C ORD (p.subj (A 0) CA1))) csfTop = some TOP ∧
        MemGate c R p.ctx (topOf c (maySweep c st0)) TOP Mode.must (A 0x7473756d))
    (hkids : KidsN c KIDS) (hscc : SccN c SCC)
    (hord : ORD = listN c.order) (hsub : ∀ b ∈ c.order, b ∈ c.scc)
    (hdfs : nock (p.subj (A 0) CA0) csfOrder = some ORD)
    (hpr : ∀ TOP MAY, PrintId { p with TOP := TOP, MAY := MAY })
    (hR : R st0.ml st0.sure (A 0) CA0) (fuel : Nat) (s : St Noun N)
    (hs : compileSccIn c false fuel st0 = some s)
    (hfin : ∀ M CA', R s.ml s.sure M CA' → ∃ NARY REST NARYU, CA' = C NARY REST ∧
      nock (C by.uni.battery (C M (C by.battery (C NARY layer2)))) by.uni.battery = some NARYU) :
    ∃ M NARY REST NARYU, R s.ml s.sure M (C NARY REST) ∧
      nock (cuTC (cuSam FUNC SCC CODE LSR JH CA0)) cuCsi = some (C M (C NARYU REST)) := by
  obtain ⟨M, CA', hR', hgo⟩ := csi_gate_loop c R SCC (C CODE LSR) JH CA0 KIDS ORD hlevy hkidsP hdn
    p hp hR0 hmay hdone st0 hmust hkids hscc hord hsub hdfs hpr hR fuel s hs
  obtain ⟨NARY, REST, NARYU, rfl, hu⟩ := hfin M CA' hR'
  exact ⟨M, NARY, REST, NARYU, hR', by rw [cu_csi_eq]; exact hgo NARY REST NARYU rfl hu⟩

/-- **`CsiNeeds` from the loop, for callees inside the SCC**: when `map-local` `M` holds the
model's final `ml` (`MlNeeds`, a clause of `R`), every callee of `n` is a member, and `env.need`
is the model's final entry. -/
theorem csiNeeds_of_loop (env : CallEnv) (n : Nomm) (SCC M CA : Noun)
    (ml : Noun → Option NeedOrd) (hml : MlNeeds ml M)
    (hin : ∀ b ∈ dirBells n, hasInF mugF b.toNoun SCC = some true)
    (henv : ∀ b ∈ dirBells n, ∃ nb, env.need b = some nb ∧ ml b.toNoun = some nb) :
    CsiNeeds env SCC M CA n := by
  intro b hb
  obtain ⟨nb, he, hm⟩ := henv b hb
  obtain ⟨u, hg, hu⟩ := hml _ _ hm
  exact ⟨nb, he, Or.inl ⟨hin b hb, u, hg, hu⟩⟩

/-- **`CsiSures` from the loop**: when `sure.cache` of the returned cache holds the model's final
`sure` at the callees (`SureHolds`, a clause of `R` carried through the `+uni:by` at `nary`,
which does not touch axis 31), and `env.sure` is that `sure` (`[%none ~]` where it has none). -/
theorem csiSures_of_loop (env : CallEnv) (n : Nomm) (CA : Noun)
    (sure : Noun → Option NeedOrd) (hs : SureHolds ((dirBells n).map Bell.toNoun) sure CA)
    (henv : ∀ b ∈ dirBells n, env.sure b = (sure b.toNoun).getD NeedOrd.none) :
    CsiSures env CA n := by
  intro b hb
  obtain ⟨S, hS, hall⟩ := hs
  refine ⟨S, by simpa [cuRest] using hS, ?_⟩
  rcases hall b.toNoun (List.mem_map_of_mem hb) with ⟨v, hv, hg⟩ | ⟨hv, hg⟩
  · left; rw [henv b hb, hv]; simpa using hg
  · right; exact ⟨hg, by rw [henv b hb, hv]; rfl⟩

/-- `+uni:by` at `nary` (the head of the cache) leaves `sure.cache` (axis 31): `SureHolds` of the
last member run's cache `[NARY REST]` is `SureHolds` of `[NARYU REST]`. -/
theorem sureHolds_uni (bs : List Noun) (sure : Noun → Option NeedOrd) (NARY NARYU REST : Noun)
    (h : SureHolds bs sure (C NARY REST)) : SureHolds bs sure (C NARYU REST) := by
  obtain ⟨S, hS, hall⟩ := h
  exact ⟨S, by simpa [nock_exec] using hS, hall⟩

end Compiler
end Formalization
