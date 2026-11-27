import lemmas.Compiler.CompUnaryDirT
import lemmas.Compiler.CompSofCode

/-!
# The per-call facts discharged from the cache (README Gaps 19 (g))

The invariant on rests is chosen once: `AgreeE env x` (no soft; `cache` is
`[nary mono sccs inl sure]` with `nary.cache` and `sure.cache` maps; every
entry of `nary.cache` has the need `env.need b` and an entry in `sure.cache`;
every entry of `sure.cache` is `env.sure b`), and `EnvE env x0 x` is
`AgreeE env x` with `Ext x0 x` from the rest `x0` the run starts at.

* `agreeE_ext`: `AgreeE` at the new rest is all an `Ext` step must show to be an
  `ExtE (EnvE env x0)` step.
* `sureNoun_ext`: `SureNoun` at `x0` (an entry, or none with `env.sure b` the
  `%none` need) holds at every later rest with `AgreeE`.
* `CalleeCompiled env ctx b nb`: what the compile of a miss must give (the
  gates of `+scc-of` and `+compile-scc-in`, `CccMiss`, a cache `CA'` that
  extends the old one, keeps `AgreeE`, and holds the entry of `b`).
* `CallAt`: a callee readable at `x0` (`NeedRead` and `SureNoun` there: what
  `CsiNeeds`, `CsiSures` give), or outside the SCC with `CalleeCompiled`.
* **`callOkT_of_E`**: `CallOkT` of one call from `CallAt`, the code entry, no
  ring, and the push of `sof` at every rest (on a hit `x' = x`; on a miss the
  rest `CalleeCompiled` gives).
* `dirCallsT_of_E`, **`cu_gate_dirE`**: the gate of `+compile-unary` with
  the per-call facts down to `AgreeE` at the start, `CallAt` per callee, and
  the facts of the code table.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- **The invariant on rests** (README Gaps 19 (g)): no soft; `cache` is
`[nary mono sccs inl sure]` with `nary.cache` and `sure.cache` maps, every
entry of `nary.cache` has the need `env.need b` (axis `2` of the `straight`)
and an entry in `sure.cache`, every entry of `sure.cache` is `env.sure b`. -/
def AgreeE (env : CallEnv) (x : GenRest) : Prop :=
  x.NoSoft ∧ ∃ NR MO SC INL SU, x.cache = cacheN NR MO SC INL SU ∧ IsMap mugF NR ∧ IsMap mugF SU ∧
    (∀ (b : Bell) u, getF mugF b.toNoun NR = some (C (A 0) u) →
      (∃ nb, env.need b = some nb ∧ slot? 2 u = some nb.toNoun) ∧ ∃ v, getF mugF b.toNoun SU = some (C (A 0) v)) ∧
    (∀ (b : Bell) v, getF mugF b.toNoun SU = some (C (A 0) v) → v = (env.sure b).toNoun)

/-- `AgreeE` and `Ext` from the rest `x0` the run starts at. -/
def EnvE (env : CallEnv) (x0 x : GenRest) : Prop := AgreeE env x ∧ Ext x0 x

/-- **An `Ext` step whose new rest has `AgreeE` keeps `EnvE`**. -/
theorem agreeE_ext {env : CallEnv} {x0 x y : GenRest} (he : Ext x y) (hA : AgreeE env y) :
    ExtE (EnvE env x0) x y :=
  ⟨he, fun h => ⟨hA, ext_trans h.2 he⟩⟩

/-- A map lookup is a hit or a miss. -/
theorem getF_cases {M k : Noun} (hm : IsMap mugF M) :
    getF mugF k M = some (A 0) ∨ ∃ u, getF mugF k M = some (C (A 0) u) := by
  by_cases h : ∃ v, Get M k v
  · obtain ⟨v, hg⟩ := h
    exact Or.inr ⟨v, getF_some hm hg⟩
  · exact Or.inl (getF_none hm fun v hg => h ⟨v, hg⟩)

/-- **`SureNoun` is kept along `Ext` under `AgreeE`**: an entry stays, and a
callee with no entry and the `%none` need either still has none or gets an
entry that agrees, so `%none`. -/
theorem sureNoun_ext {env : CallEnv} {b : Bell} {x0 x : GenRest} (h : SureNoun env b x0) (he : Ext x0 x)
    (hA : AgreeE env x) : SureNoun env b x := by
  obtain ⟨S, hS, hg⟩ := h
  rcases hg with hg | ⟨-, hn⟩
  · exact sureNoun_of_hit (sureHit_ext ⟨S, hS, hg⟩ he)
  · obtain ⟨-, NR, MO, SC, INL, SU, hc, -, hsu, -, hag⟩ := hA
    have h31 : slot? 31 x.cache = some SU := by rw [hc]; simp [cacheN, nock_exec]
    refine ⟨SU, h31, ?_⟩
    rcases getF_cases (k := b.toNoun) hsu with h0 | ⟨v, hv⟩
    · exact Or.inr ⟨h0, hn⟩
    · exact Or.inl (by rw [hv, hag b v hv])

/-- **A hit in `nary.cache` under `AgreeE`**: `NeedRead` (the case `nary`)
and `SureNoun` (the entry in `sure.cache`). -/
theorem hit_of_agree {ctx : Noun} {env : CallEnv} {b : Bell} {nb : NeedOrd} {x : GenRest} {S : Noun}
    (hS : slot? 12 ctx = some S) (hin : hasInF mugF b.toNoun S = some false) (hnb : env.need b = some nb)
    (hA : AgreeE env x) {NR u : Noun} (hNR : slot? 2 x.cache = some NR)
    (hu : getF mugF b.toNoun NR = some (C (A 0) u)) : NeedRead ctx x b nb ∧ SureNoun env b x := by
  obtain ⟨-, NR', MO, SC, INL, SU, hc, -, -, hag, hsa⟩ := hA
  have h2 : NR' = NR := by rw [hc] at hNR; simpa [cacheN, nock_exec] using hNR
  subst h2
  obtain ⟨⟨nb', hnb', hu'⟩, v, hv⟩ := hag b u hu
  rw [hnb] at hnb'
  cases hnb'
  refine ⟨NeedRead.nary hS hin hNR hu hu', SU, by rw [hc]; simp [cacheN, nock_exec], Or.inl ?_⟩
  rw [hv, hsa b v hv]

/-- **What the compile of a miss must give** (the named hypothesis per
callee outside the SCC): at a rest with `AgreeE` whose cache is
`[NR MO SC RS]` with no entry for `b` in `NR`, the gates of `+scc-of` and
`+compile-scc-in` on the subjects of the miss (`CccMiss`) with a cache
`CA'` that extends the old one (`Ext`), keeps `AgreeE`, and has the entry
of `b` in `nary.cache`. -/
def CalleeCompiled (env : CallEnv) (ctx : Noun) (b : Bell) (nb : NeedOrd) : Prop :=
  ∀ (x : GenRest) (NR MO SC RS : Noun), AgreeE env x → x.cache = C NR (C MO (C SC RS)) →
    getF mugF b.toNoun NR = some (A 0) →
    ∃ CA', CccMiss ctx b nb NR MO SC RS x.soft x.sofs CA' ∧ Ext x ⟨CA', x.soft, x.sofs⟩ ∧
      AgreeE env ⟨CA', x.soft, x.sofs⟩ ∧ ∃ N' u, slot? 2 CA' = some N' ∧ getF mugF b.toNoun N' = some (C (A 0) u)

/-- **What one callee takes**: readable at the start `x0` (`NeedRead` and
`SureNoun` there), or outside the SCC with `CalleeCompiled`. -/
def CallAt (env : CallEnv) (ctx : Noun) (x0 : GenRest) (b : Bell) (nb : NeedOrd) : Prop :=
  (NeedRead ctx x0 b nb ∧ SureNoun env b x0) ∨
    (∃ S, slot? 12 ctx = some S ∧ hasInF mugF b.toNoun S = some false ∧ CalleeCompiled env ctx b nb)

/-- **`CallOkT` of one call, discharged** at `E = EnvE env x0` and
`Y = ExtE E`: the code entry, no ring, the need `nb`, `CallAt`, and the push
of `sof` at every rest. -/
theorem callOkT_of_E {ctx : Noun} (h7 : slot? 7 ctx = some compK) {env : CallEnv} {cod : Noun} {x0 : GenRest}
    {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd}
    (hcd : CodePure cod env b) (hc : env.cod b = some (env.pure b)) (hri : env.ring b = Option.none)
    (hnb : env.need b = some nb)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hsof : ∀ x, SofRet env msup ctx p q b nb x)
    (hca : CallAt env ctx x0 b nb) :
    CallOkT env cod ctx (EnvE env x0) (ExtE (EnvE env x0)) msup p q b := by
  refine ⟨hcd, hc, hri, nb, hnb, fun x _ hE => ?_⟩
  have hit : NeedRead ctx x b nb → SureNoun env b x → ∃ x' sur SOF, ExtE (EnvE env x0) x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 0) SOF ∧ CallNounM msup ctx p q b nb sur x' (A 0) SOF := by
    intro hr hs
    obtain ⟨SOF, hso⟩ := hsof x
    have hm := callNounM_of_r h7 (⟨hcole, hhot, hr, hs, hso⟩ : CallNounMR env msup ctx p q b nb x SOF)
    exact ⟨x, _, SOF, ⟨ext_refl x, id⟩, callNounMT_of_m hm, hm⟩
  rcases hca with ⟨hr, hs⟩ | ⟨S, hS, hin, hcc⟩
  · exact hit (needRead_ext hr hE.2) (sureNoun_ext hs hE.2 hE.1)
  · obtain ⟨_, NR, MO, SC, INL, SU, hcx, hnm, -⟩ := hE.1
    have hNR : slot? 2 x.cache = some NR := by rw [hcx]; simp [cacheN, nock_exec]
    rcases getF_cases (k := b.toNoun) hnm with h0 | ⟨u, hu⟩
    · obtain ⟨CA', hmiss, hext, hA', N', u', hN', hu'⟩ := hcc x NR MO SC (C INL SU) hE.1 hcx h0
      obtain ⟨hr', hs'⟩ := hit_of_agree hS hin hnb hA' hN' hu'
      obtain ⟨SOF, hso⟩ := hsof ⟨CA', x.soft, x.sofs⟩
      have hm := callNounM_of_r h7 (⟨hcole, hhot, hr', hs', hso⟩ : CallNounMR env msup ctx p q b nb _ SOF)
      exact ⟨_, _, SOF, agreeE_ext hext hA',
        callNounMT_of h7 hcole hhot (NeedStep.miss hS hin hcx h0 hmiss) hs' hso, hm⟩
    · obtain ⟨hr, hs⟩ := hit_of_agree hS hin hnb hE.1 hNR hu
      exact hit hr hs

/-- What a callee of `n` takes in the gate: a code entry, no ring in
`call.cole`, its need, and `CallAt` at the start. -/
def BellE (env : CallEnv) (CODE COLE ctx : Noun) (x0 : GenRest) (b : Bell) : Prop :=
  (∃ c, codeOf CODE b = some c) ∧ getF mugF b.toNoun COLE = some (A 0) ∧
    ∃ nb, env.need b = some nb ∧ CallAt env ctx x0 b nb

/-- **`DirCallsT` at `EnvE` from the callees' facts** and the push of `sof`
at every rest. -/
theorem dirCallsT_of_E {ctx : Noun} (h7 : slot? 7 ctx = some compK) {env : CallEnv} {CODE COLE : Noun}
    (he : EnvFrom env CODE COLE) (hcl : slot? 6846 ctx = some COLE) (hhot : ∃ jh, slot? 54 ctx = some jh)
    {x0 : GenRest} : ∀ (ms : Option Nomm) (n : Nomm), (∀ b ∈ dirBells n, BellE env CODE COLE ctx x0 b) →
      (∀ x, SofAll env ctx x ms n) → DirCallsT env CODE ctx (EnvE env x0) (ExtE (EnvE env x0)) ms n
  | ms, Nomm.cons p q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAll] at hs
    exact ⟨dirCallsT_of_E h7 he hcl hhot ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsT_of_E h7 he hcl hhot ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | _, Nomm.n0 _, _, _ => trivial
  | _, Nomm.n1 _, _, _ => trivial
  | ms, Nomm.n2 p q Option.none, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAll] at hs
    exact ⟨dirCallsT_of_E h7 he hcl hhot ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsT_of_E h7 he hcl hhot ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | ms, Nomm.n2 p q (some (b0, k)), hb, hs => by
    simp only [dirBells, List.mem_cons, List.mem_append] at hb; simp only [SofAll] at hs
    obtain ⟨⟨c, hc⟩, hr, nb, hnb, hca⟩ := hb b0 (Or.inl rfl)
    obtain ⟨hcd, hcod⟩ := codePure_of he hc
    exact ⟨callOkT_of_E h7 hcd hcod (he.ring b0 hr) hnb ⟨COLE, hcl, hr⟩ hhot (fun x => (hs x).1 nb hnb) hca,
      dirCallsT_of_E h7 he hcl hhot ms p (fun b h => hb b (Or.inr (Or.inl h))) fun x => (hs x).2.1,
      dirCallsT_of_E h7 he hcl hhot ms q (fun b h => hb b (Or.inr (Or.inr h))) fun x => (hs x).2.2⟩
  | ms, Nomm.n3 p, hb, hs => dirCallsT_of_E h7 he hcl hhot ms p hb hs
  | ms, Nomm.n4 p, hb, hs => dirCallsT_of_E h7 he hcl hhot ms p hb hs
  | ms, Nomm.n5 p q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAll] at hs
    exact ⟨dirCallsT_of_E h7 he hcl hhot ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsT_of_E h7 he hcl hhot ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | ms, Nomm.n6 p q r, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAll] at hs
    exact ⟨dirCallsT_of_E h7 he hcl hhot ms p (fun b h => hb b (Or.inl (Or.inl h))) fun x => (hs x).1,
      dirCallsT_of_E h7 he hcl hhot ms q (fun b h => hb b (Or.inl (Or.inr h))) fun x => (hs x).2.1,
      dirCallsT_of_E h7 he hcl hhot ms r (fun b h => hb b (Or.inr h)) fun x => (hs x).2.2⟩
  | ms, Nomm.n7 p q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAll] at hs
    exact ⟨dirCallsT_of_E h7 he hcl hhot ms p (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsT_of_E h7 he hcl hhot (some p) q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | ms, Nomm.n10 _ v q, hb, hs => by
    simp only [dirBells, List.mem_append] at hb; simp only [SofAll] at hs
    exact ⟨dirCallsT_of_E h7 he hcl hhot ms v (fun b h => hb b (Or.inl h)) fun x => (hs x).1,
      dirCallsT_of_E h7 he hcl hhot ms q (fun b h => hb b (Or.inr h)) fun x => (hs x).2⟩
  | _, Nomm.n11s _ _ _, _, _ => trivial
  | _, Nomm.n11d _ _ _ _, _, _ => trivial
  | _, Nomm.n12 _ _, _, _ => trivial
  | _, Nomm.mean _ _ _ _ _, _, _ => trivial

/-- **A callee readable at the start from `+compile-scc-in`'s product**:
`SccNeed` (what `CsiNeeds` gives) and `SureNoun` at `cuRest CA` (what
`CsiSures` gives) are the first case of `CallAt`. -/
theorem callAt_of_scc {FUNC SCC CODE LSR JH NM CA : Noun} {env : CallEnv} {b : Bell} {nb : NeedOrd}
    (h : SccNeed SCC NM CA b nb) (hs : SureNoun env b (cuRest CA)) :
    CallAt env (cuCtx FUNC SCC CODE LSR JH NM) (cuRest CA) b nb :=
  Or.inl ⟨needRead_of_scc h, hs⟩

/-- **The gate of `+compile-unary` on `DirOk` with the per-call facts
discharged from the cache** (README Gaps 19 (g)).  Hypotheses, in three
groups.  State nouns: the code entry of `func` (`hgot`, `hv`), `call.cole`
(`hcl`), `+compile-scc-in`'s product `[NM CA]` (`hcsi`), and the invariant
at its cache (`hE0 : AgreeE env (cuRest CA)`).  The class: `DirOk n`.  Facts
of the code table: `EnvFrom`, `CodeNoRing`, `CodeAna`.  Per callee of `n`:
its need and `CallAt` (readable at the start, from `CsiNeeds` and `CsiSures`,
or outside the SCC with `CalleeCompiled`).  The product carries a cache `CA'`
that extends `CA` and has `AgreeE`. -/
theorem cu_gate_dirE (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA))
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hcall : ∀ b ∈ dirBells n, ∃ nb, env.need b = some nb ∧
      CallAt env (cuCtx FUNC SCC CODE LSR JH NM) (cuRest CA) b nb) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have harm : SofArms env CODE Option.none n :=
    sofArms_code (sfTable_code hana) Option.none n hn (fun b mem => by
      obtain ⟨c, hc⟩ := (hcr b mem).1
      obtain ⟨V', hg⟩ := entry_of_codeOf hc
      exact sofBell_code hana hg) (fun _ e => by cases e)
  have hsof : ∀ x, SofAll env (cuCtx FUNC SCC CODE LSR JH NM) x Option.none n := fun x =>
    sofAll_of_arms rfl (by simp [cuCtx, nock_exec]) he x Option.none n hn (fun b m => (hcr b m).1) harm
  have hd := dirCallsT_of_E h7 he (cuCtx_cole hcl) ⟨JH, cuCtx_hot FUNC SCC CODE LSR JH NM⟩ Option.none n
    (fun b hb => by
      obtain ⟨hc, hr⟩ := hcr b hb
      obtain ⟨nb, hnb, hca⟩ := hcall b hb
      exact ⟨hc, hr, nb, hnb, hca⟩) hsof
  obtain ⟨CA', hx, hE, h⟩ := cu_gate_dirExt FUNC SCC CODE LSR JH CACHE NM CA V env n hn (EnvE env (cuRest CA))
    ⟨hE0, ext_refl _⟩ hd hcsi hgot hv
  exact ⟨CA', hx, hE.1, h⟩

/-- **The old hypotheses as the case with no miss**: with `CsiNeeds` and
`CsiSures` every callee is readable at the start. -/
theorem cu_gate_dirE_csi (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hneed : CsiNeeds env SCC NM CA n) (hsure : CsiSures env CA n) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' :=
  cu_gate_dirE FUNC SCC CODE LSR JH CACHE NM CA V COLE env n hgot hv hcl hcsi hE0 hn he hcr hana fun b hb => by
    obtain ⟨nb, hnb, hs⟩ := hneed b hb
    exact ⟨nb, hnb, callAt_of_scc hs (hsure b hb)⟩

end Compiler
end Formalization
