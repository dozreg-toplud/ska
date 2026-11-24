module

public import core.Nock
public import core.Cue
public import core.Pill

/-!
# The statements

Everything here is about one noun, the pill, and is said with `cue` and
`Eval` alone.  No Lean model of the compiler or of the interpreter appears:
the compiler and the interpreter are the Nock inside the pill.

The arms of the pill are run with `EvalA` (`Pull`, `Slam`), so the statements
say nothing about a scry gate or library code that would run a hint with a
cell for a tag.

The pill decodes to `[%steel nok trap ~]`, and `nok` on `[trap ~]` computes
the SKA core.  That core is three cores deep:

    [battery  [battery  [battery ...]]]
     outer     +eval-*   inner: +poke and the state
     +poke     +3        +7

* `Poke` is the outer `+poke`.
* `Top` is `+eval-top`: analysis, compilation and the IR interpreter.
* `Mook` is `+eval-mook`: the renderer of the interpreter's trace.
* `Mock` is `+mock` of the hoon.hoon that the core is built on.

`Reach` is every core that the pill's core can become: by any pokes, except
a `%jets` poke that names a jet, and by any runs of the two `+eval-` arms.

The statements:

* `Loads`     the pill does hold a core (without it the rest says nothing)
* `Meek`      if Nock computes `p`, the interpreter returns `[%0 p]`
              (Nock with atom hint tags, `EvalA`)
* `Weak`      what `+mock` returns, the interpreter returns, rendered
* `Converse`  what the interpreter returns, rendered, `+mock` returns
* `Halts`     the `%full` poke returns on every subject and formula
* `Full`      all of them

Nothing is proved here.
-/

@[expose] public section

namespace Formalization
namespace Ska

open Nock

/-! ## Hoon's calling conventions, in Nock -/

/-- The arm at `axis` of the battery of `core`: `*[core 9 axis 0 1]`. -/
def Pull (core : Noun) (axis : Nat) (arm : Noun) : Prop :=
  EvalA core (n3 (A 9) (A axis) (slot 1)) arm

/-- The gate called on a sample: `*[gate(+6 sam) 9 2 0 1]`. -/
def Slam (gate sam out : Noun) : Prop :=
  ∃ battery bunt context,
    gate = C battery (C bunt context) ∧
    EvalA (C battery (C sam context)) (n3 (A 9) (A 2) (slot 1)) out

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
def IsCore (core : Noun) : Prop :=
  ∃ nok trap,
    cue pill = some (n4 (A steel) nok trap (A 0)) ∧
    Eval (C trap (A 0)) nok core

/-- `(poke ovo)` on `core` returns `[prod core']`. -/
def Poke (core ovo prod core' : Noun) : Prop :=
  ∃ gate, Pull core axPoke gate ∧ Slam gate ovo (C prod core')

/-- `(eval-top [s f] gul)` in `core` returns the tone `ton` and leaves
`core'`: the arm returns the inner core, which goes back in at `axInner`. -/
def Top (core s f gul ton core' : Noun) : Prop :=
  ∃ eval gate inner,
    Slot axEval core eval ∧
    Pull eval axTop gate ∧
    Slam gate (C (C s f) gul) (C ton inner) ∧
    Edit axInner inner core core'

/-- `(eval-mook ton)` in `core` returns the toon `toon` and leaves `core'`. -/
def Mook (core ton toon core' : Noun) : Prop :=
  ∃ eval gate inner,
    Slot axEval core eval ∧
    Pull eval axMook gate ∧
    Slam gate ton (C toon inner) ∧
    Edit axInner inner core core'

/-- The interpreter, rendered: `+eval-top`, then `+eval-mook` of its tone. -/
def Run (core s f gul toon core'' : Noun) : Prop :=
  ∃ ton core', Top core s f gul ton core' ∧ Mook core' ton toon core''

/-- `(mock [s f] gul)` returns `toon`, by the hoon.hoon inside `core`. -/
def Mock (core s f gul toon : Noun) : Prop :=
  ∃ hoon gate,
    Slot axHoon core hoon ∧
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
  ∃ core, IsCore core

/-- If Nock computes `p` from `s` and `f`, so does the interpreter, on any
core the pill's core can become, whatever the scry gate.  Nock here is
`EvalA`: no hint with a cell for a tag is run. -/
def Meek : Prop :=
  ∀ core₀ core s f p gul,
    IsCore core₀ → Reach core₀ core →
    EvalA s f p →
    ∃ core', Top core s f gul (C (A 0) p) core'

/-- What `+mock` returns, the interpreter returns: a product, a block, or a
crash with the same rendered trace. -/
def Weak : Prop :=
  ∀ core₀ core s f gul toon,
    IsCore core₀ → Reach core₀ core →
    Mock core₀ s f gul toon →
    ∃ core', Run core s f gul toon core'

/-- What the interpreter returns, `+mock` returns.  So the interpreter does
not halt where `+mock` does not. -/
def Converse : Prop :=
  ∀ core₀ core s f gul toon core',
    IsCore core₀ → Reach core₀ core →
    Run core s f gul toon core' →
    Mock core₀ s f gul toon

/-- Analysis and compilation of the entry point halt: `[%full s f]` is
answered for every subject and every formula that is a cell. -/
def Halts : Prop :=
  ∀ core₀ core s f₁ f₂,
    IsCore core₀ → Reach core₀ core →
    ∃ prod core', Poke core (n3 (A full) s (C f₁ f₂)) prod core'

def Full : Prop :=
  Loads ∧ Meek ∧ Weak ∧ Converse ∧ Halts

end Ska
end Formalization
