import lemmas.Compiler.FolLoopLink

/-!
`+soft-spot` of the analysis core `ana` against the Lean model `softSpotF`,
on every noun.  This discharges `SoftSpotIs` of `Compiler/FolLoopLink.lean`
for every `Env` whose `softSpot` is `softSpotF` (`softSpotIs_of`).

```hoon
++  soft-spot
  |=  n=*
  ^-  (unit spot)
  ?@  n  ~
  =/  tel  +.n
  =/  hed  -.n
  ?.  ?=(pint tel)  ~
  =;  pax=(unit path)
    ?~  pax  ~
    `[u.pax tel]
  ::
  |-  ^-  (unit path)
  ?~  hed  `~
  ?.  ?=([@ta *] hed)  ~
  =/  rest=(unit path)  $(hed +.hed)
  ?~  rest  ~
  `[-.hed u.rest]
```

The gate never crashes and never reads its context.  The loop rebuilds
`hed` when it is a list of atoms, so the spot it returns is `n` itself.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- A list of atoms ending in `~`, as `?~` and `?=([@ta *] hed)` test it. -/
def atomList : Noun → Bool
  | Noun.atom 0 => true
  | Noun.cell (Noun.atom _) t => atomList t
  | _ => false

/-- `?=(pint tel)`: `[[@ @] [@ @]]`. -/
def pintShape : Noun → Bool
  | Noun.cell (Noun.cell (Noun.atom _) (Noun.atom _)) (Noun.cell (Noun.atom _) (Noun.atom _)) => true
  | _ => false

/-- The model of `+soft-spot`: the noun itself when it is `[path pint]`. -/
def softSpotF : Noun → Option Noun
  | Noun.cell h t => if pintShape t && atomList h then some (C h t) else none
  | Noun.atom _ => none

/-- The loop of `+soft-spot` over `hed`: `[~ hed]` on a list of atoms, else `~`. -/
theorem soft_spot_loop (x : Noun) : ∀ h : Noun,
    nock (C soft_spot.loop (C h x)) soft_spot.loop = some (if atomList h then C (A 0) h else A 0)
  | Noun.atom 0 => by nock_open soft_spot.loop; simp [nock_exec, atomList]
  | Noun.atom (k + 1) => by nock_open soft_spot.loop; simp [nock_exec, atomList]
  | Noun.cell (Noun.cell a b) t => by nock_open soft_spot.loop; simp [nock_exec, atomList]
  | Noun.cell (Noun.atom k) t => by
    have ih := soft_spot_loop x t
    nock_open soft_spot.loop
    cases e : atomList t with
    | false => rw [e] at ih; simp [nock_exec, atomList, ih, e]
    | true => rw [e] at ih; simp [nock_exec, atomList, ih, e]

/-- Slamming `+soft-spot` on any noun, in any context. -/
theorem soft_spot_gate (ctx n : Noun) :
    nock (C soft_spot.battery (C n ctx)) soft_spot.battery = some (unitNoun id (softSpotF n)) := by
  nock_open soft_spot.battery
  rcases n with k | ⟨h, t⟩
  · simp [nock_exec, softSpotF, unitNoun]
  · have hl := soft_spot_loop (C t (C soft_spot.battery (C (C h t) ctx))) h
    rcases t with k | ⟨k1 | ⟨p1 | ⟨_, _⟩, q1 | ⟨_, _⟩⟩, k2 | ⟨p2 | ⟨_, _⟩, q2 | ⟨_, _⟩⟩⟩
    all_goals try (simp [nock_exec, softSpotF, unitNoun, pintShape]; done)
    cases e : atomList h with
    | false => rw [e] at hl; simp [nock_exec, softSpotF, unitNoun, pintShape, hl, e]
    | true => rw [e] at hl; simp [nock_exec, softSpotF, unitNoun, pintShape, hl, e]

/-- `SoftSpotIs` holds of every `Env` whose `softSpot` is `softSpotF`. -/
theorem softSpotIs_of {R : Type} (env : SkaModel.Ana.Env R) (h : env.softSpot = softSpotF) :
    SoftSpotIs env := fun n => by rw [h]; exact soft_spot_gate ana n

end Compiler
end Formalization
