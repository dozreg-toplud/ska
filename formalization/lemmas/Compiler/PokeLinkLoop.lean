import lemmas.Compiler.PokeLinkFlags
import lemmas.Compiler.PokeLinkRest
import lemmas.Compiler.PokeLinkReach

/-!
# `LoopLinkAt` at `fl = flagsOf` from two pill leaves (track P, README Gaps 23, P1)

`LoopLinkAt` (pushes 8 and 9 of `spRest`: `+tarjan` under `%poke-tarjan`,
then the SCC loop under `%poke-scc-loop` with `+eval-finalized`) at the
flags `flagsOf`, from:

* `SccsLeafAt`: push 8 returns a list of SCC sets that is `TarjanSpecN` of
  the new code (the leaf on `+tarjan`, 188 cells);
* `LoopRunAt`: push 9 on the noun of a list of SCC sets writes the new table
  with the flags of the model's loop `sccLoop` started from `F` (243 cells,
  `+eval-finalized` against `evalFin`);
* the model's loop returns on a `TarjanSpec` list (`LoopTotal`);
* the old table closed, `vars` on keys, info bells among callees, and `F` a
  solution of the old table (so `flagsOf code` is `F`'s flags,
  `flagsOf_sol`).

`tabFlags G` is a flag table read as `Flags`.  **`loopLinkAt_flagsOf`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

/-- A flag table as `Flags` (the same for every table). -/
def tabFlags (G : FlagTab) : Flags := fun _ b =>
  match G b with
  | some p => flagNoun p
  | none => A 0

section Leaves

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- **The leaf on `+tarjan`** (push 8): the list it returns is `TarjanSpecN`
of the new code. -/
def SccsLeafAt (nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) : Prop :=
  ∃ q, nock (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr))) srSccs = some q ∧
    TarjanSpecN nc q

/-- **The leaf of the SCC loop** (push 9): on the noun of a list `Ls` of SCC
sets, when the model's loop from `F` over `Ls` returns `G`, the pill's loop
writes the new table with `G`'s flags. -/
def LoopRunAt (code nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) (F : FlagTab) : Prop :=
  ∀ (Ls : List (FinMap Bell Unit)) (G : FlagTab),
    sccLoop (nmOf (addCode code nc)) F (Ls.map fun S => (FinMap.rap S).map Prod.fst) = some G →
    nock (C (listNoun FinMap.setNoun Ls) (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
        (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r codeN vr)))) srLoop =
      some (C (listNoun FinMap.setNoun Ls) (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
        (srSp root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r
          (codeNoun (tabFlags G) (addCode code nc)) vr))))

end Leaves

/-- The model's loop returns on every `TarjanSpec` list of the new code. -/
def LoopTotal (code nc : FinMap Bell (VarEntry FinMap)) (F : FlagTab) : Prop :=
  ∀ L, TarjanSpec nc L → ∃ G, sccLoop (nmOf (addCode code nc)) F L = some G

/-- **`LoopLinkAt` at `flagsOf`** from the two leaves, on a closed old table
with a solution `F`. -/
theorem loopLinkAt_flagsOf (root : Ident) (r1 r2 r3 r4 jRest callsN varsN seekN hotN : Noun)
    (gr : Callgraph FinMap × Noun)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    {code : FinMap Bell (VarEntry FinMap)} {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)} {F : FlagTab} (vr : Noun)
    (hc : CodeClosed code) (hv : VarsKeys E.vars code) (hi : InfoCalls code) (hbg : bakeGraph E n = some bg)
    (hF : FlagSol code F)
    (hS : SccsLeafAt root r1 r2 r3 r4 jRest (codeNoun flagsOf code) callsN varsN seekN hotN gr r
      (newCode code bg.1) bg.1 vr)
    (hR : LoopRunAt root r1 r2 r3 r4 jRest (codeNoun flagsOf code) callsN varsN seekN hotN gr r
      code (newCode code bg.1) bg.1 vr F)
    (hT : LoopTotal code (newCode code bg.1) F) :
    LoopLinkAt root r1 r2 r3 r4 jRest (codeNoun flagsOf code) callsN varsN seekN hotN gr r
      flagsOf code (newCode code bg.1) bg.1 vr := by
  obtain ⟨q, hq, Ls, rfl, hspec⟩ := hS
  obtain ⟨G, hG⟩ := hT _ hspec
  refine ⟨_, hq, ?_⟩
  rw [hR Ls G hG]
  have hfl := (flagsOf_poke hc hv hi hbg hspec hF hG).1
  have e : codeNoun (tabFlags G) (addCode code (newCode code bg.1)) =
      codeNoun flagsOf (addCode code (newCode code bg.1)) :=
    codeNoun_congr fun b _ => (hfl b).symm
  rw [e]

/-- `flagsOf code` is `tabFlags F` on a closed table with the solution `F`:
the old code noun of the leaves is `codeNoun (tabFlags F) code`. -/
theorem codeNoun_flagsOf {code : FinMap Bell (VarEntry FinMap)} (hc : CodeClosed code) (hi : InfoCalls code)
    {F : FlagTab} (hF : FlagSol code F) : codeNoun flagsOf code = codeNoun (tabFlags F) code :=
  codeNoun_congr fun b _ => flagsOf_sol hc hi hF b

end Compiler
end Formalization
