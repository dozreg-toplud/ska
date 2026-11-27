module

public import core.Nock
public import core.Cue
public import core.Pill

@[expose] public section

namespace Formalization
namespace Ska

open Nock

/-! ## Hoon's calling conventions, in Nock -/

/-- The arm at `axis` of the battery of `core`: `*[core 9 axis 0 1]`. -/
def Pull (core : Noun) (axis : Nat) (arm : Noun) : Prop :=
  Nock core (T3 9 (A axis) (T2 0 (A 1))) arm

/-- The gate called on a sample: `*[gate(+6 sam) 9 2 0 1]`. -/
def Slam (gate sam out : Noun) : Prop :=
  ∃ battery bunt context,
    gate = C battery (C bunt context) ∧
    Nock (C battery (C sam context)) (T3 9 (A 2) (T2 0 (A 1))) out

/-! ## Constants of the pill

The tags are cords: their letters as bytes, the first letter lowest.

Each axis is read off the formula that Hoon compiles a name to against the
library, given beside it.  They change when arms are added or renamed.
-/

def steel : Nat := 0x6c65657473   -- %steel
def full : Nat := 0x6c6c7566      -- %full
def jets : Nat := 0x7374656a      -- %jets

def axPoke : Nat := 23            -- poke        [9 23 0 1]
def axInner : Nat := 7            -- ..^poke     [0 7]
def axEval : Nat := 3             -- the core of the +eval- arms
def axTop : Nat := 22             -- eval-top    [9 22 0 3]
def axMook : Nat := 191           -- eval-mook   [9 191 0 3]
def axHoon : Nat := 2097151       -- the core of hoon.hoon with +mock
def axMock : Nat := 1406          -- mock        [9 1.406 0 2.097.151]

/-! ## The core and its arms -/

/-- `core` is what the pill builds. -/
def FromPill (core : Noun) : Prop :=
  ∃ nok trap,
    cue pill = some (T4 steel nok trap (A 0)) ∧
    Nock (C trap (A 0)) nok core

/-- `(poke ovo)` on `core` returns `[prod core']`. -/
def Poke (core ovo prod core' : Noun) : Prop :=
  ∃ gate, Pull core axPoke gate ∧ Slam gate ovo (C prod core')

/-- `(eval-top [s f] gul)` in `core` returns the tone `ton` and leaves
`core'`: the arm returns the inner core, which goes back in at `axInner`. -/
def Top (core s f gul ton core' : Noun) : Prop :=
  ∃ eval gate inner,
    Fas (A axEval) core eval ∧
    Pull eval axTop gate ∧
    Slam gate (C (C s f) gul) (C ton inner) ∧
    Hax (A axInner) inner core core'

/-- `(eval-mook ton)` in `core` returns the toon `toon` and leaves `core'`. -/
def Mook (core ton toon core' : Noun) : Prop :=
  ∃ eval gate inner,
    Fas (A axEval) core eval ∧
    Pull eval axMook gate ∧
    Slam gate ton (C toon inner) ∧
    Hax (A axInner) inner core core'

/-- The interpreter, rendered: `+eval-top`, then `+eval-mook` of its tone. -/
def Run (core s f gul toon core'' : Noun) : Prop :=
  ∃ ton core', Top core s f gul ton core' ∧ Mook core' ton toon core''

/-- `(mock [s f] gul)` returns `toon`, by the hoon.hoon inside `core`. -/
def Mock (core s f gul toon : Noun) : Prop :=
  ∃ hoon gate,
    Fas (A axHoon) core hoon ∧
    Pull hoon axMock gate ∧
    Slam gate (C (C s f) gul) toon

/-! ## The history of a core -/

/-- A `%jets` poke that names at least one jet.  The interpreter runs a
jetted function by its own code, which is the same thing only while no call
site was compiled against a jet's arguments. -/
def Hot (ovo : Noun) : Prop :=
  ∃ head tail, ovo = C (A jets) (C head tail)

/-- `Reach core₀ core`: `core₀` can become `core`. -/
inductive Reach (core₀ : Noun) : Noun → Prop where
  | pill : Reach core₀ core₀
  | poke {core ovo prod core'} :
      Reach core₀ core → Poke core ovo prod core' → ¬ Hot ovo →
      Reach core₀ core'
  | top {core s f gul ton core'} :
      Reach core₀ core → Top core s f gul ton core' →
      Reach core₀ core'
  | mook {core ton toon core'} :
      Reach core₀ core → Mook core ton toon core' →
      Reach core₀ core'

/-! ## The statements

In all of them `gul`, the scry gate, is any noun; `~` is no namespace.
-/

/-- The pill holds a core. -/
def Loads : Prop :=
  ∃ core, FromPill core

/-- SKA interpreter computes a result without a crash iff Nock does the same.
The scry gate is `~`: with a namespace, opcode 12 computes nouns that Nock
has no rule for. -/
def NockEquivalence : Prop :=
  ∀ core₀ core s f p,
    FromPill core₀ → Reach core₀ core →
    (Nock s f p ↔
     ∃ core', Top core s f (A 0) (C (A 0) p) core')

/-- Interpreting with SKA is equivalent to interpreting with +mock -/
def MockEquivalence : Prop :=
  ∀ core₀ core s f gul toon,
    FromPill core₀ → Reach core₀ core →
    (Mock core₀ s f gul toon ↔
     ∃ core', Run core s f gul toon core')

/-- Analysis and compilation of the entry point halt: `[%full s f]` is
answered for every subject and every formula that is a cell. -/
def Halts : Prop :=
  ∀ core₀ core s f₁ f₂,
    FromPill core₀ → Reach core₀ core →
    ∃ prod core', Poke core (T3 full s (C f₁ f₂)) prod core'

def Full : Prop :=
  Loads ∧ NockEquivalence ∧ MockEquivalence ∧ Halts

end Ska
end Formalization
