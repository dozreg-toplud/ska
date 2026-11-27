import lemmas.Compiler.CompSccOfHeight

/-!
# The calls of a member run from static facts, and the gate with the nesting discharged
(README Gaps 19 (g))

* `DirCallsP Ok`: `DirCallsTN`'s recursion with any per-call predicate `Ok`; **`dirCallsTN_of`**:
  `DirCallsTN` from `Ok → CallOkTN` (the shape of `dirCallsT_of_E`).
* `MemCallOk`: the static facts of one call of a member run (on `envDone`): code entry, no ring,
  `call.cole`, its need, `sof` `|` with `SofRetN`, and member of the SCC, or outside it, in the
  domain `D`, of smaller height.  **`callOkTN_memOk`**: `CallOkTN` at `EM` (by `callOkTN_member`,
  or `callOkTN_out` with `CalleeCompiledP` from `CCBelow` at `above_memS`).
* `MemDoneRestS`: `MemDoneRest` with `DirCallsP MemCallOk` for the calls; `memDoneRest_of_S`.
* `SccLoopDataS`, `CalleeHS`: the table's data with static calls and `r.env = env`;
  `sccLoopData_of_S`, `calleeH_of_S`.
* **`cu_gate_dir_sccH`**: the gate of `+compile-unary` on `DirOk` with every outside callee in
  `D` and the nested misses closed by `calleeCompiled_heights0`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **`DirCallsTN`'s recursion with a per-call predicate `Ok`** (each direct call at the `msup`
its run gets). -/
def DirCallsP (Ok : Option Nomm → Nomm → Nomm → Bell → Prop) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => DirCallsP Ok ms p ∧ DirCallsP Ok ms q
  | ms, Nomm.n2 p q Option.none => DirCallsP Ok ms p ∧ DirCallsP Ok ms q
  | ms, Nomm.n2 p q (some (b, _)) => Ok ms p q b ∧ DirCallsP Ok ms p ∧ DirCallsP Ok ms q
  | ms, Nomm.n3 p => DirCallsP Ok ms p
  | ms, Nomm.n4 p => DirCallsP Ok ms p
  | ms, Nomm.n5 p q => DirCallsP Ok ms p ∧ DirCallsP Ok ms q
  | ms, Nomm.n6 p q r => DirCallsP Ok ms p ∧ DirCallsP Ok ms q ∧ DirCallsP Ok ms r
  | ms, Nomm.n7 p q => DirCallsP Ok ms p ∧ DirCallsP Ok (some p) q
  | ms, Nomm.n10 _ v q => DirCallsP Ok ms v ∧ DirCallsP Ok ms q
  | _, _ => True

/-- **`DirCallsTN` from per-call facts.** -/
theorem dirCallsTN_of {env : CallEnv} {cod ctx : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop}
    {Ok : Option Nomm → Nomm → Nomm → Bell → Prop}
    (hok : ∀ ms p q b, Ok ms p q b → CallOkTN env cod ctx E Y ms p q b) :
    ∀ (ms : Option Nomm) (n : Nomm), DirCallsP Ok ms n → DirCallsTN env cod ctx E Y ms n
  | ms, Nomm.cons p q, h => ⟨dirCallsTN_of hok ms p h.1, dirCallsTN_of hok ms q h.2⟩
  | _, Nomm.n0 _, _ => trivial
  | _, Nomm.n1 _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h => ⟨dirCallsTN_of hok ms p h.1, dirCallsTN_of hok ms q h.2⟩
  | ms, Nomm.n2 p q (some (b0, k)), h =>
    ⟨hok ms p q b0 h.1, dirCallsTN_of hok ms p h.2.1, dirCallsTN_of hok ms q h.2.2⟩
  | ms, Nomm.n3 p, h => dirCallsTN_of hok ms p h
  | ms, Nomm.n4 p, h => dirCallsTN_of hok ms p h
  | ms, Nomm.n5 p q, h => ⟨dirCallsTN_of hok ms p h.1, dirCallsTN_of hok ms q h.2⟩
  | ms, Nomm.n6 p q r, h =>
    ⟨dirCallsTN_of hok ms p h.1, dirCallsTN_of hok ms q h.2.1, dirCallsTN_of hok ms r h.2.2⟩
  | ms, Nomm.n7 p q, h => ⟨dirCallsTN_of hok ms p h.1, dirCallsTN_of hok (some p) q h.2⟩
  | ms, Nomm.n10 _ v q, h => ⟨dirCallsTN_of hok ms v h.1, dirCallsTN_of hok ms q h.2⟩
  | _, Nomm.n11s _ _ _, _ => trivial
  | _, Nomm.n11d _ _ _ _, _ => trivial
  | _, Nomm.n12 _ _, _ => trivial
  | _, Nomm.mean _ _ _ _ _, _ => trivial

/-- **The static facts of one call `b` of a member run** (on `envDone r order kids st`, in the
context `ctx` whose `scc` is `SCC`): `CodePure`, the code entry, no ring, no entry in `call.cole`,
the need `nb` with `sof` `|` and `SofRetN`, and either `b` a member, or `b` outside, in the domain
`D` of the table, of height below `h` (the height of the SCC in progress). -/
def MemCallOk (r : RealCfg) (order : List Noun) (kids : Noun → List Noun) (st : St Noun NeedOrd)
    (CODE ctx SCC : Noun) (ht : Noun → Nat) (D : Bell → Prop) (h : Nat) (ms : Option Nomm) (p q : Nomm)
    (b : Bell) : Prop :=
  CodePure CODE (envDone r order kids st) b ∧
    (envDone r order kids st).cod b = some ((envDone r order kids st).pure b) ∧
    (envDone r order kids st).ring b = Option.none ∧
    (∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)) ∧
    ∃ nb, (envDone r order kids st).need b = some nb ∧ (envDone r order kids st).sof (made p ms) p q b nb = false ∧
      (∀ x, SofRetN (envDone r order kids st) ms ctx p q b nb x) ∧
      ((hasInF mugF b.toNoun SCC = some true ∧ b.toNoun ∈ r.scc) ∨
        (hasInF mugF b.toNoun SCC = some false ∧ b.toNoun ∉ r.scc ∧ D b ∧ ht b.toNoun < h))

/-- **`CallOkTN` at `EM` from the static facts** (a member by `callOkTN_member`; an outside
callee by `callOkTN_out`, its nested compile `CalleeCompiledP` from the induction hypothesis
`CCBelow` at the bells in progress of the member run, `above_memS`). -/
theorem callOkTN_memOk {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd}
    {env : CallEnv} {SC0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun} {xs : GenRest}
    {CODE JETS CALLS JH ML B SCC : Noun} {ht : Noun → Nat} {D : Bell → Prop} {h : Nat}
    (hre : r.env = env) (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    (hab : Above ht h P Pf) (hS : ∀ k ∈ tapList S, ht k = h) (hml : MlExact st.ml ML)
    (hIH : CCBelow env SC0 CODE JETS CALLS JH inl ht D h) {ms : Option Nomm} {p q : Nomm} {b : Bell}
    (hok : MemCallOk r order kids st CODE (memDCtx SCC (C CODE (C JETS CALLS)) JH ML (A 0) B) SCC ht D h ms p q b) :
    CallOkTN (envDone r order kids st) CODE (memDCtx SCC (C CODE (C JETS CALLS)) JH ML (A 0) B)
      (EM env SC0 inl P Pf S st xs) (ExtE (EM env SC0 inl P Pf S st xs)) ms p q b := by
  obtain ⟨hcd, hc, hri, hcole, nb, hnb, hsf, hsof, hin⟩ := hok
  rcases hin with ⟨hin, hb⟩ | ⟨hin, hb, hD, hlt⟩
  · rw [need_done hb] at hnb
    obtain rfl := Option.some.inj hnb
    exact callOkTN_member hcd hc hri hsf hcole hsof hml hin hb fun x hx => by rw [hrs]; exact hx.2.2.2
  · have hnb' : env.need b = some nb := by rw [← hre, ← (need_done_out hb).1]; exact hnb
    exact callOkTN_out hre hrs hab.1 hPS hbell hcd hc hri hnb hsf hcole hsof hin
      (hIH b _ _ _ nb hD hlt (above_memS hab hS hlt) (ctxK_memD _ _ _ _ _ _ _ _) hnb')

def MemDoneRestS (r : RealCfg) (order : List Noun) (kids : Noun → List Noun) (env : CallEnv) (SC0 : Noun)
    (inl : Noun → Option Nomm) (P Pf : Noun → Prop) (S : Noun) (xs : GenRest) (st : St Noun NeedOrd) (keep : Bool)
    (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun) (ht : Noun → Nat) (D : Bell → Prop) (h : Nat) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    InlKeep inl CACHE CA1 ∧ DirOk nm = true ∧
    DirCallsP (MemCallOk r order kids st CODE (memDCtx SCC (C CODE LSR) JH ML (A 0) b) SCC ht D h) Option.none nm ∧
    ∃ (nex : NextL CSet) (g1 : Gen (TreapMap mugF)),
      runLC (envDone r order kids st) Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
        = some (nex, g1) ∧
    ∃ ord, shapeCol fuel nex.laz cape = some ord ∧ nex.th.args = [] ∧
    ∃ (nedF : Need) (g2 : Gen (TreapMap mugF)), needOrdAllocRegs ord g1 = some (nedF, g2) ∧
      isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
        ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true ∧
    ∃ sur, sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur ∧
      (∃ s, finishLFC (S := CSet) (Map := TreapMap mugF) (envDone r order kids st) nm ord cape
        (fun n => bakeNeed n (Sock.mk cape DATA)) = some s) ∧
      ∀ (x1 : GenRest) (C1 C2 C3 C4 SURE' : Noun) (prev : NeedOrd), st.ml b = some prev →
        msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape ≠ needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1 →
        ∃ t, nock (C finBody (C (C (A 0) (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun)
              (memFCR keep (wasN (st.sure b)) sur.toNoun
                (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
                (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
                nex.th.there (genNoun g2 x1) nm.toNoun
                (memDCtx SCC (C CODE LSR) JH ML (A 0) b) b ML
                (A 0) (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)))) finBody
          = some (C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t)

theorem memDoneRest_of_S {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {env : CallEnv} {SC0 : Noun}
    {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun} {xs : GenRest} {st : St Noun NeedOrd} {keep : Bool}
    {DN KIDS ML0 CB SCC CODE JETS CALLS JH CACHE0 b ML CACHE : Noun} {ht : Noun → Nat} {D : Bell → Prop} {h : Nat}
    (hre : r.env = env) (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    (hab : Above ht h P Pf) (hS : ∀ k ∈ tapList S, ht k = h) (hml : MlExact st.ml ML)
    (hIH : CCBelow env SC0 CODE JETS CALLS JH inl ht D h)
    (H : MemDoneRestS r order kids env SC0 inl P Pf S xs st keep DN KIDS ML0 CB SCC CODE (C JETS CALLS) JH CACHE0 b
      ML CACHE ht D h) :
    MemDoneRest r order kids env SC0 inl P Pf S xs st keep DN KIDS ML0 CB SCC CODE (C JETS CALLS) JH CACHE0 b
      ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, hn, hd, rest⟩ := H
  exact ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, hn,
    dirCallsTN_of (fun ms p q b' hok => callOkTN_memOk hre hrs hPS hbell hab hS hml hIH hok) _ _ hd, rest⟩

/-- **`SccLoopData` with static calls** (`MemDoneRestS`, no induction hypothesis) and the
real configuration's `env` the table's (`r.env = env`). -/
def SccLoopDataS (env : CallEnv) (SC0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S : Noun) (ht : Noun → Nat) (D : Bell → Prop) (h : Nat) : Prop :=
  ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR →
    ∃ (r : RealCfg) (order : List Noun) (kids : Noun → List Noun) (rk : Ranked (cfgReal r order kids))
      (nout : Noun → NeedOrd),
      r.env = env ∧ CfgOf (cfgReal r order kids) S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) ∧
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
        LoopR r.scc (fun _ => []) nout (QK env (RKP SC0 inl Pf) P S x) st.ml st.sure ML CACHE →
        MemDoneRestS r order kids env SC0 inl P Pf S x st keep (A 1)
          (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE ht D h


theorem sccLoopData_of_S {env : CallEnv} {SC0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {P Pf : Noun → Prop} {S : Noun} {ht : Noun → Nat} {D : Bell → Prop} {h : Nat}
    (hPS : ∀ k ∈ tapList S, ¬ P k) (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    (hab : Above ht h P Pf) (hS : ∀ k ∈ tapList S, ht k = h)
    (H : SccLoopDataS env SC0 CODE JETS CALLS JH inl P Pf S ht D h) :
    SccLoopData env SC0 CODE JETS CALLS JH inl P Pf S (CCBelow env SC0 CODE JETS CALLS JH inl ht D h) := by
  intro x NR CR hx
  obtain ⟨r, order, kids, rk, nout, hre, hcfg, hmay, hmust, henv, hcall⟩ := H x NR CR hx
  exact ⟨r, order, kids, rk, nout, hcfg, hmay, hmust, henv, fun st keep b ML CACHE hb hL hIH =>
    memDoneRest_of_S hre hcfg.scc hPS hbell hab hS hL.1 hIH (hcall st keep b ML CACHE hb hL)⟩

/-- **The table's data of one callee with static calls**: `CalleeH` with `SccLoopDataS`. -/
def CalleeHS (env : CallEnv) (SC0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) (b : Bell) : Prop :=
  OneCallee env SC0 CODE CALLS inl b ∨
    ∃ S, getF mugF b.toNoun SC0 = some (C (A 0) S) ∧
      ((∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
      ∀ P Pf, Above ht (ht b.toNoun) P Pf → SccLoopDataS env SC0 CODE JETS CALLS JH inl P Pf S ht D (ht b.toNoun)

theorem calleeH_of_S {env : CallEnv} {SC0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0) (hht : HtScc SC0 ht) {b : Bell}
    (H : CalleeHS env SC0 CODE JETS CALLS JH inl ht D b) : CalleeH env SC0 CODE JETS CALLS JH inl ht D b := by
  rcases H with hone | ⟨S, hsc, hnd, hdat⟩
  · exact Or.inl hone
  · refine Or.inr ⟨S, hsc, hnd, fun P Pf hab => ?_⟩
    have hS : ∀ k ∈ tapList S, ht k = ht b.toNoun := hht _ _ hsc
    have hPS : ∀ k ∈ tapList S, ¬ P k := fun k hk hp =>
      Nat.lt_irrefl _ ((hS k hk) ▸ hab.2 k (hab.1 k hp))
    exact sccLoopData_of_S hPS (fun k hk => ((hsg _ _ hsc).2.2 k hk).2) hab hS (hdat P Pf hab)

/-- **What one callee of the caller takes, with the table**: readable at the start, or outside the
caller's SCC, in the domain `D` of the table, with a need. -/
def AnyCalleeH (env : CallEnv) (SCC : Noun) (D : Bell → Prop) (ctx : Noun) (x0 : GenRest) (b : Bell) : Prop :=
  (∃ nb, env.need b = some nb ∧ NeedRead ctx x0 b nb ∧ SureNoun env b x0) ∨
    (hasInF mugF b.toNoun SCC = some false ∧ D b ∧ ∃ nb, env.need b = some nb)

/-- **The gate of `+compile-unary` on `DirOk` with the nested misses discharged** (README Gaps
19 (g)): `cu_gate_dir_scc`'s state nouns, invariants, code table, `SccsGood` and jug, plus the
heights `HtScc`, the table's `CalleeHS` for every bell of `D`, and per callee `AnyCalleeH`. -/
theorem cu_gate_dir_sccH (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RK SC0 inl (cuRest CA))
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hht : HtScc SC0 ht) (hT : ∀ b, D b → CalleeHS env SC0 CODE JETS CALLS JH inl ht D b)
    (hcal : ∀ b ∈ dirBells n, AnyCalleeH env SCC D (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) (cuRest CA) b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RK SC0 inl (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  refine cu_gate_dirE FUNC SCC CODE (C JETS CALLS) JH CACHE NM CA V COLE env (RK SC0 inl) n hgot hv hcl hcsi hE0 hR0
    hn he hcr hana fun b hb => ?_
  rcases hcal b hb with ⟨nb, hnb, hr, hs⟩ | ⟨hout, hD, nb, hnb⟩
  · exact ⟨nb, hnb, Or.inl ⟨hr, hs⟩⟩
  · exact ⟨nb, hnb, Or.inr ⟨SCC, by simp [cuCtx, nock_exec], hout,
      calleeCompiled_heights0 hsg hcj hht (fun b' hD' => calleeH_of_S hsg hht (hT b' hD')) hD
        (ctxK_cu _ _ _ _ _ _ _) hnb⟩⟩

end Compiler
end Formalization
