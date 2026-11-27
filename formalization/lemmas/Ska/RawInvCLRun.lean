import lemmas.Ska.RawInvCLCollapse

/-!
# The run-level liveness with calls: the induction on `PlainN`

README Gaps 14 (b), track D.  `LR env sup nm` is `LiveRun IL JL` of
`runLC env sup nm`.

* `ArmsL env`: the statements of the arms not yet closed (`%3`, `%4`, `%5`,
  cons, `%10`, the call `%2`), each from `LR` of its parts.
* **`liveRun_plainOf`**: `LR env sup nm` on all of `PlainN` from `ArmsL`
  (`%0`, `%1`, `%7` by `liveRun_n0`, `liveRun_n1`, `liveRun_n7`).
* `il_gen0`: the precondition at the top (`gen0`, `%done`, no outer kills);
  **`liveRun_plain_topOf`**: the top run's `JL` and `LiveC` from `ArmsL`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `LiveRun IL JL` of one run of `runLC`. -/
abbrev LR (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (sup : Option Nomm) (nm : Nomm) : Prop :=
  LiveRun (Map := Map) IL JL (runLC (S := S) env sup nm)

/-- **The arms not closed yet**, each from `LR` of its parts. -/
structure ArmsL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv) :
    Prop where
  n3 : ∀ sup p, PlainN p → LR S Map env sup p → LR S Map env sup (Nomm.n3 p)
  n4 : ∀ sup p, PlainN p → LR S Map env sup p → LR S Map env sup (Nomm.n4 p)
  n5 : ∀ sup p q, PlainN p → PlainN q → LR S Map env sup p → LR S Map env sup q →
    LR S Map env sup (Nomm.n5 p q)
  cons : ∀ sup p q, PlainN p → PlainN q → LR S Map env sup p → LR S Map env sup q →
    LR S Map env sup (Nomm.cons p q)
  n10 : ∀ sup a v q, PlainN v → PlainN q → LR S Map env sup v → LR S Map env sup q →
    LR S Map env sup (Nomm.n10 a v q)
  n2 : ∀ sup p q, PlainN p → PlainN q → LR S Map env sup p → LR S Map env sup q →
    LR S Map env sup (Nomm.n2 p q Option.none)

/-- **The run-level liveness with calls on all of `PlainN`**, from the arms
not closed yet. -/
theorem liveRun_plainOf (env : CallEnv) (A : ArmsL S Map env) :
    ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), LR S Map env sup nm
  | Nomm.n0 ax, _, sup => liveRun_n0 env sup ax
  | Nomm.n1 k, _, sup => liveRun_n1 env sup k
  | Nomm.n3 p, h, sup => A.n3 sup p h (liveRun_plainOf env A p h sup)
  | Nomm.n4 p, h, sup => A.n4 sup p h (liveRun_plainOf env A p h sup)
  | Nomm.n5 p q, h, sup =>
    A.n5 sup p q h.1 h.2 (liveRun_plainOf env A p h.1 sup) (liveRun_plainOf env A q h.2 sup)
  | Nomm.cons p q, h, sup =>
    A.cons sup p q h.1 h.2 (liveRun_plainOf env A p h.1 sup) (liveRun_plainOf env A q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    liveRun_n7 env sup (liveRun_plainOf env A q h.2 (some p)) (liveRun_plainOf env A p h.1 sup)
  | Nomm.n10 a v q, h, sup =>
    A.n10 sup a v q h.1 h.2 (liveRun_plainOf env A v h.1 sup) (liveRun_plainOf env A q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup =>
    A.n2 sup p q h.1 h.2 (liveRun_plainOf env A p h.1 sup) (liveRun_plainOf env A q h.2 sup)
  | Nomm.n2 _ _ (some _), h, _ => h.elim
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim

/-- **The precondition at the top**: `gen0`, the goal `%done`, no outer kills. -/
theorem il_gen0 : IL (S := S) (fun _ _ => False) CGoalL.done (gen0 : Comp.Gen Map) := by
  refine ⟨ats_gen0, fun k b hb => ?_, fun k v hk => ?_, KVan.none _, trivial⟩
  · simp [gen0, HoonMap.get_empty] at hb
  · simp [gen0, HoonMap.get_empty] at hk

/-- **The top run** of a `PlainN` nomm from `gen0` under `%done`: the
result's `IL` and the liveness spec, from the arms not closed yet. -/
theorem liveRun_plain_topOf (env : CallEnv) (A : ArmsL S Map env) {nm : Nomm} (hp : PlainN nm)
    {nex : NextL S} {g1 : Comp.Gen Map}
    (h : runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1)) :
    JL (fun _ _ => False) nex g1 ∧ LiveC (fun _ _ => False) CGoalL.done gen0 g1 nex :=
  liveRun_plainOf env A nm hp Option.none _ _ _ _ _ _ il_gen0 h

end Raw
end SkaModel
end Formalization
