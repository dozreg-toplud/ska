import lemmas.Compiler.CompSccOfOneAny

/-!
# Nested misses closed by induction on height (README Gaps 19 (g))

A member run of the loop on an SCC `S` may miss an outside callee `b'`; that miss compiles the SCC
of `b'` inside the run, at the bells in progress `(PeS P S st, PfS Pf S)`.  Here:

* `CtxK`: the four slots of the context `calleeCompiled_sccA` reads (`ctxK_memD`: a member
  context has them).
* `HtScc SC0 ht`: the heights `ht` are constant on every SCC of `sccs.cache`.
* `Above ht h P Pf`: `P ⊆ Pf` and every bell in progress is higher than `h` (the invariant of the
  nesting: the SCCs in progress are the callers' SCCs, all higher); `above_memS`: a member run
  of an SCC of height `h` keeps it for every callee of smaller height.
* `CCBelow ... D h`: every callee in the domain `D` of height below `h` is `CalleeCompiledP` at
  every `(P, Pf)` above it, at every context with `CtxK` (the induction hypothesis).
* `CalleeH`: the table's data of one callee: a one-bell callee (`OneCalleeA`, no `BakeRunO`:
  `calleeCompiled_oneKA`) or an SCC with
  the data of `SccCalleeR` at every `(P, Pf)` above it, where each `%done` call's
  `MemDoneRest` may use `CCBelow` at the callee's height.
* **`calleeCompiled_stepH`** (one step) and **`calleeCompiled_heights`**: every callee of `D`
  is `CalleeCompiledP env (RKP SC0 inl Pf) P` at every `(P, Pf)` above it.
* `calleeCompiled_heights0`: at `(∅, ∅)`, `CalleeCompiled` with `RK` (what the gate takes).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The slots of a context that `calleeCompiled_sccA` and `calleeCompiled_oneKP` read. -/
def CtxK (CODE JETS CALLS JH ctx : Noun) : Prop :=
  slot? 7 ctx = some compK ∧ slot? 26 ctx = some (C CODE (C JETS CALLS)) ∧ slot? 54 ctx = some JH ∧
    slot? 107 ctx = some CALLS

theorem ctxK_memD (CODE JETS CALLS JH SCC ML TOP B : Noun) :
    CtxK CODE JETS CALLS JH (memDCtx SCC (C CODE (C JETS CALLS)) JH ML TOP B) :=
  ⟨rfl, by simp [memDCtx, nock_exec], by simp [memDCtx, nock_exec], by simp [memDCtx, nock_exec]⟩

theorem ctxK_cu (FUNC SCC CODE JETS CALLS JH NM : Noun) :
    CtxK CODE JETS CALLS JH (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) :=
  ⟨rfl, by simp [cuCtx, nock_exec], cuCtx_hot _ _ _ _ _ _, by simp [cuCtx, nock_exec]⟩

/-- **The heights are constant on the SCCs of `sccs.cache`.** -/
def HtScc (SC0 : Noun) (ht : Noun → Nat) : Prop :=
  ∀ k S, getF mugF k SC0 = some (C (A 0) S) → ∀ k' ∈ tapList S, ht k' = ht k

/-- **The bells in progress are above the height `h`** (and `P ⊆ Pf`). -/
def Above (ht : Noun → Nat) (h : Nat) (P Pf : Noun → Prop) : Prop :=
  (∀ k, P k → Pf k) ∧ ∀ k, Pf k → h < ht k

theorem above_empty (ht : Noun → Nat) (h : Nat) : Above ht h (fun _ => False) (fun _ => False) :=
  ⟨fun _ h => h, fun _ h => h.elim⟩

/-- **A member run keeps `Above` for the callees of smaller height**: the bells in progress
of a member run of `S` (of height `h`, `HtScc`) are those of the loop and the members of `S`. -/
theorem above_memS {ht : Noun → Nat} {h h' : Nat} {P Pf : Noun → Prop} {S : Noun}
    {st : St Noun NeedOrd} (hab : Above ht h P Pf) (hS : ∀ k ∈ tapList S, ht k = h) (hlt : h' < h) :
    Above ht h' (PeS P S st) (PfS Pf S) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rcases hk with hk | ⟨hk, -⟩
    · exact Or.inl (hab.1 k hk)
    · exact Or.inr hk
  · rcases hk with hk | hk
    · exact Nat.lt_trans hlt (hab.2 k hk)
    · rw [hS k hk]; exact hlt

/-- **The induction hypothesis below the height `h`**: every callee of the domain `D` of
height below `h` is `CalleeCompiledP` at every `(P', Pf')` above it, at every context with
`CtxK`, at its need. -/
def CCBelow (env : CallEnv) (SC0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) (h : Nat) : Prop :=
  ∀ (b' : Bell) (P' Pf' : Noun → Prop) (ctx' : Noun) (nb' : NeedOrd), D b' → ht b'.toNoun < h →
    Above ht (ht b'.toNoun) P' Pf' → CtxK CODE JETS CALLS JH ctx' → env.need b' = some nb' →
    CalleeCompiledP env (RKP SC0 inl Pf') P' ctx' b' nb'

theorem cCBelow_mono {env : CallEnv} {SC0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} {h h' : Nat} (hle : h' ≤ h)
    (H : CCBelow env SC0 CODE JETS CALLS JH inl ht D h) : CCBelow env SC0 CODE JETS CALLS JH inl ht D h' :=
  fun b' P' Pf' ctx' nb' hD hlt => H b' P' Pf' ctx' nb' hD (Nat.lt_of_lt_of_le hlt hle)

/-- **The loop data of an SCC callee at the bells in progress `(P, Pf)`** (`SccCalleeR` at any
`(P, Pf)`, with each `%done` call's `MemDoneRest` under the hypothesis `IH`): at every rest
where the loop runs, a real configuration that is the pill's, ranked, the `%may` and `%must`
gates, `env` the model's at the members, and per `%done` call `MemDoneRest`. -/
def SccLoopData (env : CallEnv) (SC0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S : Noun) (IH : Prop) : Prop :=
  ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR →
    ∃ (r : RealCfg) (order : List Noun) (kids : Noun → List Noun) (rk : Ranked (cfgReal r order kids))
      (nout : Noun → NeedOrd),
      CfgOf (cfgReal r order kids) S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) ∧
      MemGate (cfgReal r order kids)
        (LoopR (cfgReal r order kids).scc (fun _ => []) nout (QK env (RKP SC0 inl Pf) P S x))
        (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
        (fun _ => (cfgReal r order kids).none) (A 0) Mode.may (A 0x79616d) ∧
      (∀ TOP, TopN (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd)).ml TOP →
        MemGate (cfgReal r order kids)
          (LoopR (cfgReal r order kids).scc (fun _ => []) nout (QK env (RKP SC0 inl Pf) P S x))
          (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
          (topOf (cfgReal r order kids) (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd))) TOP Mode.must
          (A 0x7473756d)) ∧
      (∀ (s : St Noun NeedOrd), compileSccIn (cfgReal r order kids) false (fuelR (cfgReal r order kids) rk) St.empty
        = some s → ∀ b' : Bell, b'.toNoun ∈ (cfgReal r order kids).scc →
          env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v) ∧
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopR r.scc (fun _ => []) nout (QK env (RKP SC0 inl Pf) P S x) st.ml st.sure ML CACHE → IH →
        MemDoneRest r order kids env SC0 inl P Pf S x st keep (A 1)
          (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE

/-- **The table's data of one callee `b`** (heights `ht`, domain `D`): a one-bell callee, or an
SCC `S` (its `sccs` entry, `hnd`) with `SccLoopData` at every `(P, Pf)` above `b`, whose
`%done` calls may use `CCBelow` at `b`'s height (the outside callees of the members, lower). -/
def CalleeH (env : CallEnv) (SC0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) (b : Bell) : Prop :=
  OneCalleeA env SC0 CODE CALLS inl b ∨
    ∃ S, getF mugF b.toNoun SC0 = some (C (A 0) S) ∧
      ((∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
      ∀ P Pf, Above ht (ht b.toNoun) P Pf →
        SccLoopData env SC0 CODE JETS CALLS JH inl P Pf S (CCBelow env SC0 CODE JETS CALLS JH inl ht D (ht b.toNoun))

/-- **One step of the induction on height**: a callee with `CalleeH` whose lower callees are
`CCBelow` is `CalleeCompiledP` at every `(P, Pf)` above it (`calleeCompiled_oneKA`, or
`calleeCompiled_sccA` with `sccLoopAtA_real`). -/
theorem calleeCompiled_stepH {env : CallEnv} {SC0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0)
    (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v) (hht : HtScc SC0 ht)
    {b : Bell} (hT : CalleeH env SC0 CODE JETS CALLS JH inl ht D b)
    (hIH : CCBelow env SC0 CODE JETS CALLS JH inl ht D (ht b.toNoun))
    {P Pf : Noun → Prop} (hab : Above ht (ht b.toNoun) P Pf) {ctx : Noun} (hctx : CtxK CODE JETS CALLS JH ctx)
    {nb : NeedOrd} (hnb : env.need b = some nb) :
    CalleeCompiledP env (RKP SC0 inl Pf) P ctx b nb := by
  obtain ⟨h7, hl, hj, h107⟩ := hctx
  have hnPf : ∀ k, Pf k → ht k ≠ ht b.toNoun := fun k hk e => Nat.lt_irrefl _ (e ▸ hab.2 k hk)
  rcases hT with hone | ⟨S, hsc, hnd, hdat⟩
  · obtain ⟨cape, DATA, FOL, nm, fuel, envb, p, st, rfl, hsc, hinl, hcalls, hcode, hn, hax, hfix, hone⟩ := hone
    have e : nb = st.need := Option.some.inj (hnb.symm.trans hone.2.2.1)
    subst e
    exact calleeCompiled_oneKA h7 hl hj h107 env envb cape DATA FOL nm fuel p st inl hsc hinl hcalls hcode hn hax
      hfix hone P Pf (fun h => hnPf _ (hab.1 _ h) rfl) (fun h => hnPf _ h rfl)
  · have hS : ∀ k ∈ tapList S, ht k = ht b.toNoun := hht _ _ hsc
    have hPfS : ∀ k ∈ tapList S, ¬ Pf k := fun k hk h => hnPf k h (hS k hk)
    have hPS : ∀ k ∈ tapList S, ¬ P k := fun k hk h => hPfS k hk (hab.1 k h)
    have hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k := fun k hk => ((hsg _ _ hsc).2.2 k hk).2
    refine calleeCompiled_sccA h7 hl hj h107 env inl P Pf b nb S hsg hcj hsc hnd hPS hPfS hnb fun x NR CR hx => ?_
    obtain ⟨r, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩ := hdat P Pf hab x NR CR hx
    exact sccLoopAtA_real env SC0 inl P Pf S CODE JETS CALLS JH x NR CR hx hPS hbell r order kids rk nout
      hcfg hmay hmust henv fun st keep b0 ML CACHE hb hL => hcall st keep b0 ML CACHE hb hL hIH

/-- **Every callee is compiled, by induction on height** (README Gaps 19 (g)): for a table
whose SCCs have heights (`HtScc`) and whose callees of the domain `D` have `CalleeH`, every
callee of `D` is `CalleeCompiledP env (RKP SC0 inl Pf) P` at every `(P, Pf)` above it, at every
context with `CtxK`. -/
theorem calleeCompiled_heights {env : CallEnv} {SC0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0)
    (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v) (hht : HtScc SC0 ht)
    (hT : ∀ b, D b → CalleeH env SC0 CODE JETS CALLS JH inl ht D b) :
    ∀ (b : Bell) (P Pf : Noun → Prop) (ctx : Noun) (nb : NeedOrd), D b → Above ht (ht b.toNoun) P Pf →
      CtxK CODE JETS CALLS JH ctx → env.need b = some nb → CalleeCompiledP env (RKP SC0 inl Pf) P ctx b nb := by
  have H : ∀ m, CCBelow env SC0 CODE JETS CALLS JH inl ht D m := by
    intro m
    induction m with
    | zero => intro b' P' Pf' ctx' nb' _ hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ m ih =>
      intro b' P' Pf' ctx' nb' hD hlt hab hctx hnb
      exact calleeCompiled_stepH hsg hcj hht (hT b' hD) (cCBelow_mono (Nat.le_of_lt_succ hlt) ih) hab hctx hnb
  exact fun b P Pf ctx nb hD hab hctx hnb => H (ht b.toNoun + 1) b P Pf ctx nb hD (Nat.lt_succ_self _) hab hctx hnb

/-- **At the gate** (`P = Pf = ∅`): `CalleeCompiled` with `RK`. -/
theorem calleeCompiled_heights0 {env : CallEnv} {SC0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0)
    (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v) (hht : HtScc SC0 ht)
    (hT : ∀ b, D b → CalleeH env SC0 CODE JETS CALLS JH inl ht D b) {b : Bell} {ctx : Noun} {nb : NeedOrd}
    (hD : D b) (hctx : CtxK CODE JETS CALLS JH ctx) (hnb : env.need b = some nb) :
    CalleeCompiled env (RK SC0 inl) ctx b nb := by
  intro x NR MO SC RS hA hR hc h0
  obtain ⟨CA', h1, h2, h3, h4, h5⟩ := calleeCompiled_heights hsg hcj hht hT b _ _ ctx nb hD (above_empty ht _) hctx hnb
    x NR MO SC RS (agreeIP_of_E _ hA) (rKP_empty.2 hR) hc h0
  exact ⟨CA', h1, h2, agreeE_of_IP h3, rKP_empty.1 h4, h5⟩

end Compiler
end Formalization
