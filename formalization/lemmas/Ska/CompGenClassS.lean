import lemmas.Ska.CompGenClassQ

/-!
# The class at entry-free goals, `NextGC0`, and the fragment `Frag0` beyond `FragX`

README Gaps 12.39, item 12 (g).  Under a goal with no entry nothing is
re-pointed (`RepointG` is asked at the goal's entry labels only), the fronts
are vacuous and `x` is never needed (the `%3`/`%4`/`%5` failures of
`NextGCS` and the re-pointings of `%6` are all at goal entries).  So a run at
an entry-free goal is `NextGCS`'s clauses without `FrontsSG`: `NextGC0`.
`+comp`'s top goal `[don re]` has no entry, and so have the halves of a cons
under it (`ConsGAt.labH`, `labT`) and `q` of a `[7 p q]` under it; `p` runs
at `q`'s result, which may have entries (`%6`'s fork labels), so `p` needs
`NextGCS`.

`Frag0`: `[0 a]`, `[1 k]`, the cons, `[7 p q]` with `p` of `ConsFrag`,
`[6 c a b]` with the test of `GenFrag` (`%6`-free).  It is NOT in `FragX`:
`[[7 [1 0] [6 [1 0] [1 1] [1 2]]] [1 0]]` is in `Frag0`, and `FragX` has a
`%6` under the `q` of a `%7` only when `p` is `[0 axe]` (`FragX.sevenFrom`).
The closures of the cons, `%7` and `%6` are exact `Prop`s here
(`Closed0Cons`, `Closed0N7`, `Closed0N6`); `nextGC0_all_of`, the induction,
and `contract_frag0_of`, the contract at a cons or `[0 a]` root.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The class at entry-free goals**: `NextGCS`'s clauses, the fronts
vacuous. -/
abbrev NextGC0 (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    PremG (Map := Map) L th g0 → entries L = [] →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ Q : Wit, RunOKGen lib N P f L th Q false g0 g1 nex ∧ GrowU g0 g1 ∧ ResG (Map := Map) L g0 g1 nex.laz

theorem NextGCS.to0 {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : NextGCS (S := S) (Map := Map) lib N env P f nm) : NextGC0 (S := S) (Map := Map) lib N env P f nm :=
  fun H _ hr => let ⟨Q, R, g, _, r, _⟩ := h H hr; ⟨Q, R, g, r⟩

/-- **The fragment beyond `FragX`.** -/
inductive Frag0 : Noun → Nomm → Prop
  | n0 {a : Nat} : 2 ≤ a → Frag0 (slot a) (Nomm.n0 a)
  | n1 (k : Noun) : Frag0 (quote k) (Nomm.n1 k)
  | cons {fp fq : Noun} {p q : Nomm} : Frag0 fp p → Frag0 fq q → Frag0 (C fp fq) (Nomm.cons p q)
  | n7 {fb fc : Noun} {p q : Nomm} : ConsFrag fb p → Frag0 fc q → Frag0 (n3 (A 7) fb fc) (Nomm.n7 p q)
  | n6 {fc fa fb : Noun} {c a b : Nomm} : GenFrag fc c → Frag0 fa a → Frag0 fb b →
      Frag0 (n4 (A 6) fc fa fb) (Nomm.n6 c a b)

theorem Frag0.to6 {f : Noun} {nm : Nomm} (h : Frag0 f nm) : GenFrag6 f nm := by
  induction h with
  | n0 ha => exact GenFrag6.n0 ha
  | n1 k => exact GenFrag6.n1 k
  | cons _ _ ihp ihq => exact GenFrag6.cons ihp ihq
  | n7 hp _ ihq => exact GenFrag6.n7 hp.toGen.to6 ihq
  | n6 hc _ _ iha ihb => exact GenFrag6.n6 hc iha ihb

theorem ConsFrag.to0 {f : Noun} {nm : Nomm} (h : ConsFrag f nm) : Frag0 f nm := by
  induction h with
  | n0 ha => exact Frag0.n0 ha
  | n1 k => exact Frag0.n1 k
  | cons _ _ ihp ihq => exact Frag0.cons ihp ihq
  | n7 hp _ _ ihq => exact Frag0.n7 hp ihq

section Ifaces
variable (S Map)

def Closed0Cons (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, Frag0 fp p → Frag0 fq q →
    (∀ P, NextGC0 (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGC0 (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGC0 (S := S) (Map := Map) lib N env P (C fp fq) (Nomm.cons p q)

def Closed0N7 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fb fc : Noun} {p q : Nomm}, ConsFrag fb p → Frag0 fc q →
    (∀ P, NextGCS (S := S) (Map := Map) lib N env P fb p) → (∀ P, NextGC0 (S := S) (Map := Map) lib N env P fc q) →
    ∀ P, NextGC0 (S := S) (Map := Map) lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q)

/-- **`%6` under `%next` at an entry-free goal**: the test `%6`-free, the
branches in the class. -/
def Closed0N6 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fc fa fb : Noun} {c a b : Nomm}, GenFrag fc c → Frag0 fa a → Frag0 fb b →
    (∀ P, NextGC0 (S := S) (Map := Map) lib N env P fa a) → (∀ P, NextGC0 (S := S) (Map := Map) lib N env P fb b) →
    ∀ P, NextGC0 (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b)

end Ifaces

/-- **The one induction at entry-free goals, from the closures.** -/
theorem nextGC0_all_of {lib : Lib} {N : Needs} {env : CallEnv}
    (hc : Closed0Cons S Map lib N env) (h7 : Closed0N7 S Map lib N env) (h6 : Closed0N6 S Map lib N env)
    {f : Noun} {nm : Nomm} (hf : Frag0 f nm) :
    ∀ P, NextGC0 (S := S) (Map := Map) lib N env P f nm := by
  induction hf with
  | n0 ha => exact fun P => NextGCS.to0 (closedS_n0 lib N env ha P)
  | n1 k => exact fun P => NextGCS.to0 (closedS_n1 lib N env k P)
  | cons hp hq ihp ihq => exact hc hp hq ihp ihq
  | n7 hp hq ihq => exact h7 hp hq (nextGCS_consFrag lib N env hp) ihq
  | n6 hc' ha hb iha ihb => exact h6 hc' ha hb iha ihb

/-- **A cons or `[0 a]` under `%done`** from `NextGC0` at `[don re]`. -/
theorem doneGS_of_nextGC0 {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    (H : NextGC0 (S := S) (Map := Map) lib N env P f nm) : DoneGS S Map lib N env P f nm := by
  intro sup region g0 g2 nex b0 d0 hu hcl hcb hr
  rw [runLC_done_next env sup hs region g0] at hr
  obtain ⟨Q, R, gu, Res⟩ := H (cm2_premDon (S := S) b0 d0 hu hcl hcb) (entries_ofSure _) hr
  exact ⟨runOKGD_done_of_gen hu hcb d0 R gu, Res.lu, Res.cl, Res.ecl, Res.sa⟩

/-- **THE UNARY CONTRACT ON `Frag0` at a cons or `[0 a]` root, from the
closures.** -/
theorem contract_frag0_of (lib : Lib) (env : CallEnv) (N : Needs)
    (hc : Closed0Cons S Map lib N env) (h7 : Closed0N7 S Map lib N env) (h6 : Closed0N6 S Map lib N env)
    {f : Noun} {nm : Nomm} (hf : Frag0 f nm) (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ ax, 2 ≤ ax ∧ nm = Nomm.n0 ax))
    {c : Straight Map} (h : finishLUC (S := S) (Map := Map) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  have hs' : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨
      (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax) := by
    rcases hs with hs | ⟨ax, hax, e⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inr ⟨ax, by omega, e⟩)
  have H := finishLUC_contractGD (P := fun _ => True) lib N
    (fun hr => (doneGS_of_nextGC0 (S := S) (Map := Map) hs'
      (nextGC0_all_of hc h7 h6 hf (fun _ => True)) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) h
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
