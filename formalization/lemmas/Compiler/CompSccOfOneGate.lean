import lemmas.Compiler.CompSccOfOne

/-!
# The gate of `+compile-unary` with one-bell callees (README Gaps 19 (g))

**`cu_gate_dir_one`**: the gate of `+compile-unary` on a caller `n` in
`DirOk` all of whose direct callees are one-bell SCCs with no self call,
outside the caller's SCC, with code in `SixOk` (the shape of a callee that
`+inlined` replaced in the n-ary code, so the whole-subject run is the first
to reach it).  No hypothesis names the callee's compile: a miss is
`calleeCompiled_one` (the cache hit of `+scc-of`, track A's one-bell chain
with the real bake), a hit is `hit_of_agree`.

* `OneCallee`: the facts of one such callee (its `sccs` entry `[b ~ ~]`, its
  `inl` entry, no self call, its code entry `nm`, track A's run hypotheses
  `NoAx0`, `FixRet`, `BakeRunO`, and `CompOne`: `env`'s need and sure need of
  `b` are the model's);
* **`cu_gate_dir_one`**; `cu_gate_dir_one_call`: the same for `[2 p q]` with
  one callee `b` and `p`, `q` free of direct calls (the shape of `%dt`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The facts of a one-bell callee** `b = [[cape DATA] FOL]` (README Gaps
19 (g)): `sccs` holds `[b ~ ~]` for it, `inl` gives the nomm `nm` of its code
entry, it does not call itself, `nm` is `SixOk` with `NoAx0`, track A's
`FixRet` and `BakeRunO` hold of its run on `envb`, and `CompOne`: the
caller's `env` reads the model's need and sure need for `b`. -/
def OneCallee (env : CallEnv) (SC0 CODE CALLS : Noun) (inl : Noun → Option Nomm) (b : Bell) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat) (envb : CallEnv)
    (p : NextL CSet × Gen (TreapMap mugF)) (st : Straight (TreapMap mugF)),
    b = ⟨Sock.mk cape DATA, FOL⟩ ∧
    getF mugF (C (C cape.toNoun DATA) FOL) SC0 = some (C (A 0) (setOne (C (C cape.toNoun DATA) FOL))) ∧
    inl (C (C cape.toNoun DATA) FOL) = some nm ∧ NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS ∧
    (∃ V, getF mugF (C (C cape.toNoun DATA) FOL) CODE = some (C (A 0) V) ∧ slot? 2 V = some nm.toNoun) ∧
    SixOk nm = true ∧ Bake.NoAx0 nm ∧ FixRet envb nm cape fuel ∧
    BakeRunO envb nm (fun nex => scOrd fuel nex cape) cape DATA ∧ CompOne env envb cape DATA nm fuel p st b

/-- **`CallAt` of a one-bell callee outside the SCC**: case (b), with
`CalleeCompiled` from `calleeCompiled_one`. -/
theorem callAt_one {FUNC SCC CODE JETS CALLS JH NM SC0 : Noun} {env : CallEnv} {inl : Noun → Option Nomm}
    {x0 : GenRest} {b : Bell} (hout : hasInF mugF b.toNoun SCC = some false)
    (h : OneCallee env SC0 CODE CALLS inl b) :
    ∃ nb, env.need b = some nb ∧
      CallAt env (RInl SC0 inl) (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) x0 b nb := by
  obtain ⟨cape, DATA, FOL, nm, fuel, envb, p, st, rfl, hsc, hinl, hcalls, hcode, hn, hax, hfix, hbake, hone⟩ := h
  refine ⟨st.need, hone.2.2.1, Or.inr ⟨SCC, by simp [cuCtx, nock_exec], hout, ?_⟩⟩
  exact calleeCompiled_one (CODE := CODE) (JETS := JETS) (CALLS := CALLS) (JH := JH) rfl (by simp [cuCtx, nock_exec]) (cuCtx_hot _ _ _ _ _ _) (by simp [cuCtx, nock_exec])
    env envb cape DATA FOL nm fuel p st inl hsc hinl hcalls hcode hn hax hfix hbake hone

/-- **The gate of `+compile-unary` on `DirOk` with one-bell callees**
(README Gaps 19 (g)).  Hypotheses: the state nouns (the code entry of `func`
`hgot`, `hv`; `call.cole` `hcl`; `+compile-scc-in`'s product `hcsi`; the
invariants at its cache, `AgreeE` `hE0` and `RInl` `hR0`), the class `DirOk
n`, the code table (`EnvFrom`, `CodeNoRing`, `CodeAna`), and per callee: it
is outside the SCC (`hout`) and `OneCallee`.  The product carries a cache
`CA'` that extends `CA` and keeps both invariants. -/
theorem cu_gate_dir_one (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RInl SC0 inl (cuRest CA))
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hout : ∀ b ∈ dirBells n, hasInF mugF b.toNoun SCC = some false)
    (hone : ∀ b ∈ dirBells n, OneCallee env SC0 CODE CALLS inl b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RInl SC0 inl (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' :=
  cu_gate_dirE FUNC SCC CODE (C JETS CALLS) JH CACHE NM CA V COLE env (RInl SC0 inl) n hgot hv hcl hcsi hE0 hR0
    hn he hcr hana fun b hb => callAt_one (hout b hb) (hone b hb)

/-- **The shape of `%dt`**: a caller `[2 p q]` that calls the one-bell `b`
once, with `p` and `q` free of direct calls.  The per-callee hypotheses are
those of `b` alone. -/
theorem cu_gate_dir_one_call (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (p q : Nomm) (b : Bell)
    (hp : dirBells p = []) (hq : dirBells q = [])
    (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some (Nomm.n2 p q (some (b, Option.none))).toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RInl SC0 inl (cuRest CA))
    (hn : DirOk (Nomm.n2 p q (some (b, Option.none))) = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE (Nomm.n2 p q (some (b, Option.none))))
    (hana : CodeAna CODE)
    (hout : hasInF mugF b.toNoun SCC = some false) (hone : OneCallee env SC0 CODE CALLS inl b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RInl SC0 inl (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env (Nomm.n2 p q (some (b, Option.none)))).map
            fun st => C (C st.toNoun NM) CA' :=
  cu_gate_dir_one FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 env inl _ hgot hv hcl hcsi hE0 hR0 hn he hcr
    hana (fun b' hb' => by simp [dirBells, hp, hq] at hb'; subst hb'; exact hout)
    (fun b' hb' => by simp [dirBells, hp, hq] at hb'; subst hb'; exact hone)

/-- The class of `%dt`'s nomm: a call of `b` on `[0 1]` with a constant formula. -/
example (b : Bell) (FOL : Noun) : DirOk (Nomm.n2 (Nomm.n0 1) (Nomm.n1 FOL) (some (b, Option.none))) = true ∧
    dirBells (Nomm.n2 (Nomm.n0 1) (Nomm.n1 FOL) (some (b, Option.none))) = [b] := by
  simp [DirOk, dirBells]

end Compiler
end Formalization
