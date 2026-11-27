import lemmas.Ska.CompGenConsK
import lemmas.Ska.CompGenSevenN

/-!
# The class of the one induction (interface)

README Gaps 12.39, item 12.  The class `NextGC` that the induction over
call-free, hint-free nomms carries: `RunOKGen` under every goal of the class
(`GoalG`, registers no keys of `cond`, `LabUniq`, `Clean` needs, the sure need
apart from the entries' needs, a jump without arguments), with `x = false`,
`GrowU` and no goal entry re-pointed, and of the result `ResG`: `LabUniq`,
`Clean` needs, `SureApart`, and the registers of each result entry those of a
goal entry AT ITS LABEL, the goal's sure ones or fresh (`EregsAt`).  Every
clause is checked at every sub-run of famA to famD (`CompGenClassCheck.lean`).

`GenFrag f nm`: the nomms built of `[0 a]` (`a ≥ 2`), `[1 k]`, `[3 p]`,
`[4 p]`, `[5 p q]`, the cons and `[7 p q]`, with their formulas.  `%6` is not
in it: under `%next` it re-points goal entries (phase F) and its runs are not
`GrowU` (`c:growU`, `c:frontA` of `CompGenCheck.lean` fail on 41,330 runs of
famB), so its class is `NextGC` widened to `GrowG`, `RepointG` and `x`.

The closure of each constructor is a `Prop` (`ClosedCons`, ...), and
`nextGC_all_of` is the induction from the closures.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The sure need is apart from every entry's need.** -/
def SureApart (L : Lazy S) : Prop :=
  ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → ¬ NMem L.sure.ned r

/-- **`FrameG.eregs` per label**: the registers of a result entry are those
of a goal entry at its label, the goal's sure ones, or fresh. -/
def EregsAt (L : Lazy S) (g0 g1 : Gen Map) (laz : Lazy S) : Prop :=
  ∀ e ∈ entries laz, ∀ r, NMem e.2.sure.ned r →
    (∃ e0 ∈ entries L, e0.1 = e.1 ∧ NMem e0.2.sure.ned r) ∨ NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re)

/-- **The result side of the class.** -/
structure ResG (L : Lazy S) (g0 g1 : Gen Map) (laz : Lazy S) : Prop where
  lu : Raw.LabUniq laz
  cl : Clean laz.sure.ned
  ecl : ∀ e ∈ entries laz, Clean e.2.sure.ned
  sa : SureApart laz
  eat : EregsAt L g0 g1 laz

/-- **The premises of the class at a goal** (and of the state). -/
structure PremG (L : Lazy S) (th : Jmp) (g0 : Gen Map) : Prop where
  goal : GoalG (Map := Map) L th g0
  nc : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none
  ec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none
  lu : Raw.LabUniq L
  cl : Clean L.sure.ned
  ecl : ∀ e ∈ entries L, Clean e.2.sure.ned
  sa : SureApart L
  ta : th.args = []
  bo : 1 ≤ g0.bo
  drop : g0.drop = false
  up : UpBelow g0
  clr : Clear g0
  cb : CondBelow g0

/-- **The class `NextGC`**: under every goal of the class, `RunOKGen` with
`x = false`, `GrowU`, no goal entry re-pointed, and `ResG` of the result. -/
abbrev NextGC (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    PremG (Map := Map) L th g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ Q : Wit, RunOKGen lib N P f L th Q false g0 g1 nex ∧ GrowU g0 g1 ∧
      (∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a) ∧ ResG (Map := Map) L g0 g1 nex.laz

/-- **The fragment of the induction**, with the formulas: `[0 a]` (`a ≥ 2`),
`[1 k]`, `[3 p]`, `[4 p]`, `[5 p q]`, the cons, `[7 p q]`. -/
inductive GenFrag : Noun → Nomm → Prop
  | n0 {a : Nat} : 2 ≤ a → GenFrag (slot a) (Nomm.n0 a)
  | n1 (k : Noun) : GenFrag (quote k) (Nomm.n1 k)
  | n3 {f : Noun} {p : Nomm} : GenFrag f p → GenFrag (C (A 3) f) (Nomm.n3 p)
  | n4 {f : Noun} {p : Nomm} : GenFrag f p → GenFrag (C (A 4) f) (Nomm.n4 p)
  | n5 {fp fq : Noun} {p q : Nomm} : GenFrag fp p → GenFrag fq q → GenFrag (n3 (A 5) fp fq) (Nomm.n5 p q)
  | cons {fp fq : Noun} {p q : Nomm} : GenFrag fp p → GenFrag fq q → GenFrag (C fp fq) (Nomm.cons p q)
  | n7 {fb fc : Noun} {p q : Nomm} : GenFrag fb p → GenFrag fc q → GenFrag (n3 (A 7) fb fc) (Nomm.n7 p q)

section Closed
variable (S Map)

/-- `[0 a]` is in the class at every `P`. -/
def ClosedN0 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {a : Nat}, 2 ≤ a → ∀ P, NextGC (S := S) (Map := Map) lib N env P (slot a) (Nomm.n0 a)

def ClosedN1 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ (k : Noun) P, NextGC (S := S) (Map := Map) lib N env P (quote k) (Nomm.n1 k)

/-- A unary part in the class at every `P` makes `[3 p]` one. -/
def ClosedN3 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {f : Noun} {p : Nomm}, GenFrag f p → (∀ P, NextGC (S := S) (Map := Map) lib N env P f p) →
    ∀ P, NextGC (S := S) (Map := Map) lib N env P (C (A 3) f) (Nomm.n3 p)

def ClosedN4 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {f : Noun} {p : Nomm}, GenFrag f p → (∀ P, NextGC (S := S) (Map := Map) lib N env P f p) →
    ∀ P, NextGC (S := S) (Map := Map) lib N env P (C (A 4) f) (Nomm.n4 p)

def ClosedN5 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, GenFrag fp p → GenFrag fq q →
    (∀ P, NextGC (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGC (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGC (S := S) (Map := Map) lib N env P (n3 (A 5) fp fq) (Nomm.n5 p q)

def ClosedCons (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, GenFrag fp p → GenFrag fq q →
    (∀ P, NextGC (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGC (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGC (S := S) (Map := Map) lib N env P (C fp fq) (Nomm.cons p q)

def ClosedN7 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fb fc : Noun} {p q : Nomm}, GenFrag fb p → GenFrag fc q →
    (∀ P, NextGC (S := S) (Map := Map) lib N env P fb p) → (∀ P, NextGC (S := S) (Map := Map) lib N env P fc q) →
    ∀ P, NextGC (S := S) (Map := Map) lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q)

end Closed

/-- **The one induction, from the closures.** -/
theorem nextGC_all_of {lib : Lib} {N : Needs} {env : CallEnv}
    (h0 : ClosedN0 S Map lib N env) (h1 : ClosedN1 S Map lib N env) (h3 : ClosedN3 S Map lib N env)
    (h4 : ClosedN4 S Map lib N env) (h5 : ClosedN5 S Map lib N env) (hc : ClosedCons S Map lib N env)
    (h7 : ClosedN7 S Map lib N env) {f : Noun} {nm : Nomm} (hf : GenFrag f nm) :
    ∀ P, NextGC (S := S) (Map := Map) lib N env P f nm := by
  induction hf with
  | n0 ha => exact h0 ha
  | n1 k => exact h1 k
  | n3 hp ih => exact h3 hp ih
  | n4 hp ih => exact h4 hp ih
  | n5 hp hq ihp ihq => exact h5 hp hq ihp ihq
  | cons hp hq ihp ihq => exact hc hp hq ihp ihq
  | n7 hp hq ihp ihq => exact h7 hp hq ihp ihq

end Comp
end SkaModel
end Formalization
