import lemmas.Ska.CompDirectM

/-!
# The direct call through a ring: `callLR`, `callDMR`, `callLMR` (track K, README Gaps 19 (h))

`callL` (`CompCall.lean`) and `callDM` (`CompDirectM.lean`) model the direct call `[2 p q [~ b
key]]` of `+run` only when the callee has no ring (`| _, _, _ => fun _ => Option.none` on
`env.ring b = some r`).  A callee whose bell has an entry in `call.cole` (a core registered by
`%fast`, `+ska-cole-update` / `+ska-cole-settle`) is called through its ring: the Hoon
(`desk/lib/nock-compilation.hoon`, lines 3950 to 4031) computes `rin`, then

```
=/  call-op
  |=  [pes=(unit @uvre) pro=@uvre]
  ?^  key  ...                                  :: %cam / %csm (memo keys, not here)
  ?~  rin
    ?~  pes  [%cal b-callee sub-v pro]
    [%csl b-callee u.pes pro]
  ?~  pes  [%caf b-callee sub-v pro u.rin]
  [%csf b-callee u.pes pro u.rin]
=/  jump-op
  |=  pes=(unit @uvre)
  ?~  rin
    ?~  pes  [%jmp b-callee sub-v]
    [%jsp b-callee u.pes]
  ?~  pes  [%jmf b-callee sub-v u.rin]
  [%jsf b-callee u.pes u.rin]
```

and uses `(jump-op ~)` for the tail call with `mono` `|`, `(call-op ~ pro)` for the call under
another goal with `mono` `|`, `(jump-op ~)` / `(jump-op `sub-pes)` for the optimistic and the
pessimistic tail blocks with `mono` `&`, `(call-op ~ pro-opt)` / `(call-op `sub-pes pro-pes)` for
the two call blocks with `mono` `&`.  Nothing else of the case reads `rin` but `b-sur` and
`+callee-need` (lines 3971, 4608), and both read it only through `(biff rin ~(get by
jets-hot))`: with no hot driver for the ring they are what they are without a ring.  So the ring
changes the ops and nothing else: the registers, the labels, the blocks' order, the needs.

* `ringOfNoun`: the `Ring` of the noun `u.rin` (the ops of the model hold a `Ring`); on a noun
  that is a ring (`RingNoun`) its `toNoun` is the noun back.
* `callOpR`, `jumpOpR`: the gates `call-op` (no memo key) and `jump-op`.
* `callLR`: `callL` with `jumpOpR` / `callOpR` of `env.ring b` in place of `%jmp` / `%cal`, the
  match on `key, env.need b` only.  `monoBlocksR`, `callDMR`: the same for `monoBlocks`,
  `callDM`.  `callLMR`: `callLM` over them.
* `env.need` and `env.sure` are the model's `+callee-need` and `+callee-sure`; with a hot
  driver the Hoon gives the driver's need and `[%none ~]` (out of scope: the top statement admits
  no `%jets` poke that names a jet, `core/Statement.lean` `Hot`); with none they are read as
  without a ring, so an environment built from the state needs no change there
  (`CompRingRun.lean`, `EnvNoHot`).
* The agreement: where `env.ring b = none`, `callLR`, `callDMR`, `callLMR` are `callL`,
  `callDM`, `callLM` (`callLR_eq`, `callDMR_eq`, `callLMR_eq`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## The ring of a noun -/

/-- The atoms of a list noun (a cell head that is not an atom reads `0`). -/
def ringAtoms : Noun → List Nat
  | Noun.cell (Noun.atom a) t => a :: ringAtoms t
  | Noun.cell (Noun.cell _ _) t => 0 :: ringAtoms t
  | Noun.atom _ => []

/-- **The `Ring` of the noun `u.rin`**: `[path axe]`. -/
def ringOfNoun : Noun → Ring
  | Noun.cell p (Noun.atom a) => ⟨ringAtoms p, a⟩
  | Noun.cell p (Noun.cell _ _) => ⟨ringAtoms p, 0⟩
  | Noun.atom _ => ⟨[], 0⟩

/-- **The noun is a ring**: `ringOfNoun` reads it back.  What the pill link needs of every value of
`call.cole` (a `(map bell ring)`: P, from `+cole-put`). -/
def RingNoun (u : Noun) : Prop := (ringOfNoun u).toNoun = u

theorem ringAtoms_listNoun : ∀ l : List Nat, ringAtoms (listNoun A l) = l
  | [] => rfl
  | a :: l => by simp [listNoun, ringAtoms, ringAtoms_listNoun l]

theorem ringOfNoun_toNoun (r : Ring) : ringOfNoun r.toNoun = r := by
  simp [Ring.toNoun, ringOfNoun, ringAtoms_listNoun]

/-- The noun of a `Ring` is a ring. -/
theorem ringNoun_toNoun (r : Ring) : RingNoun r.toNoun := by
  simp [RingNoun, ringOfNoun_toNoun]

/-! ## The gates `call-op` and `jump-op` (no memo key) -/

/-- **`call-op`** of `[pes pro]` for no memo key: `%cal` / `%csl` without a ring, `%caf` /
`%csf` with one. -/
def callOpR (b : Bell) (rin : Option Noun) (pes : Option Nat) (subV : List Nat) (pro : Nat) : Pole :=
  match rin, pes with
  | Option.none, Option.none => Pole.cal b subV pro
  | Option.none, some s => Pole.csl b s pro
  | some u, Option.none => Pole.caf b subV pro (ringOfNoun u)
  | some u, some s => Pole.csf b s pro (ringOfNoun u)

/-- **`jump-op`** of `pes`: `%jmp` / `%jsp` without a ring, `%jmf` / `%jsf` with one. -/
def jumpOpR (b : Bell) (rin : Option Noun) (pes : Option Nat) (subV : List Nat) : Termin :=
  match rin, pes with
  | Option.none, Option.none => Termin.jmp b subV
  | Option.none, some s => Termin.jsp b s
  | some u, Option.none => Termin.jmf b subV (ringOfNoun u)
  | some u, some s => Termin.jsf b s (ringOfNoun u)

/-! ## The case `%2` with `mono` `|` -/

/-- **The case `%2` of `run` for `mono` `|`, rings included**: `callL` whose direct call (no memo
key, `sof` false) emits `jumpOpR b (env.ring b) ~ sub-v` under `%done` and `callOpR b (env.ring
b) ~ sub-v pro` otherwise. -/
def callLR (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CM Map (NextL S) :=
  match info with
  | Option.none => do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let rSub ← re
      let rFol ← re
      let o ← emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩
      let nexFol ← rq (CGoalL.next (ofSure (lazyReg rFol)) (jmp0 o)) region
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next (ofSure (lazyReg rSub)) nexFol.th) region
      copyL nexSub nexFol.laz
  | some (b, key) =>
      let drop : Option Jmp := match goal with
        | CGoalL.next laz th => if env.pure b && noneEquivalentL laz then some th else Option.none
        | _ => Option.none
      match drop with
      | some th => do
          let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
            else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
          let nexFol ← pastL env.cod nexFol p region
          let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
          copyL nexSub nexFol.laz
      | Option.none =>
          match key, env.need b with
          | Option.none, some bNed =>
            if env.sof (made p sup) p q b bNed then fun _ => Option.none else do
            let subNed ← needOrdAllocRegs bNed
            let subV := flattenNeed subNed
            let callBlock ← (match goal with
              | CGoalL.done => emit ⟨[], [], jumpOpR b (env.ring b) Option.none subV⟩
              | g => do
                  let nex ← simpleNextL g
                  let (out, pro) ← kerf nex
                  emit ⟨[], [callOpR b (env.ring b) Option.none subV pro], Termin.hop (jmp0 out)⟩ : CM Map Nat)
            let nexArg : NextL S := ⟨ofSure ⟨subNed, HoonSet.empty⟩, jmp0 callBlock⟩
            let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
              else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
            let nexFol ← pastL env.cod nexFol p region
            let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
            copyL nexSub nexFol.laz
          | _, _ => fun _ => Option.none

/-! ## The case `%2` with `mono` `&` -/

/-- **The call blocks with `mono` `&`, rings included**: `monoBlocks` with `jumpOpR` /
`callOpR` of `rin`. -/
def monoBlocksR (b : Bell) (rin : Option Noun) (subNed : Need) (goal : CGoalL S) : CM Map (Nat × Nat) :=
  let subV := flattenNeed subNed
  match goal with
  | CGoalL.done => do
      let subPes ← re
      let opt ← emit ⟨[], [], jumpOpR b rin Option.none subV⟩
      let pes ← emit ⟨[], [], jumpOpR b rin (some subPes) subV⟩
      let o ← monoTryCall subNed opt subPes pes
      pure (subPes, o)
  | g => do
      let nex ← simpleNextL g
      let (out, pro) ← kerf nex
      let merged ← re
      let subPes ← re
      let merge ← emit ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩
      let proOpt ← re
      let proPes ← re
      let opt ← emit ⟨[], [callOpR b rin Option.none subV proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
      let pes ← emit ⟨[], [callOpR b rin (some subPes) subV proPes], Termin.hop ⟨[some proPes], merge⟩⟩
      let o ← monoTryCall subNed opt subPes pes
      pure (subPes, o)

/-- **The direct call with `mono` `&`, rings included**: `callDM` with `monoBlocksR b (env.ring
b)`, the match on `key, env.need b` only. -/
def callDMR (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (b : Bell) (key : Option Noun) (goal : CGoalL S) (region : List Nat) : CM Map (NextL S) :=
  let drop : Option Jmp := match goal with
    | CGoalL.next laz th => if env.pure b && noneEquivalentL laz then some th else Option.none
    | _ => Option.none
  match drop with
  | some th => do
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
      copyL nexSub nexFol.laz
  | Option.none =>
      match key, env.need b with
      | Option.none, some bNed => do
        let subNed ← needOrdAllocRegs bNed
        let (subPes, callBlock) ← monoBlocksR b (env.ring b) subNed goal
        let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
        copyL nexSub nexFol.laz
      | _, _ => fun _ => Option.none

/-- **The case `%2` of `run` with `mono`, rings included.** -/
def callLMR (env : CallEnv) (mono : Bool) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CM Map (NextL S) :=
  match mono, info with
  | true, some (b, key) => callDMR env rp rq p q b key goal region
  | _, _ => callLR env rp rq p q info sup goal region

/-! ## Agreement where the callee has no ring -/

/-- The callee of `info`, if any, has no ring. -/
def InfoNoRing (env : CallEnv) (info : Option (Bell × Option Noun)) : Prop :=
  ∀ b k, info = some (b, k) → env.ring b = Option.none

/-- **Without a ring, `callLR` is `callL`.** -/
theorem callLR_eq (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    {info : Option (Bell × Option Noun)} (h : InfoNoRing env info) (sup : Option Nomm) (goal : CGoalL S)
    (region : List Nat) :
    (callLR env rp rq p q info sup goal region : CM Map (NextL S)) = callL env rp rq p q info sup goal region := by
  rcases info with _ | ⟨b, key⟩
  · rfl
  · have hr : env.ring b = Option.none := h b key rfl
    simp only [callLR, callL, hr, jumpOpR, callOpR]
    rcases key with _ | k <;> cases env.need b <;> rfl

/-- **Without a ring, `monoBlocksR` is `monoBlocks`.** -/
theorem monoBlocksR_none (b : Bell) (subNed : Need) (goal : CGoalL S) :
    (monoBlocksR b Option.none subNed goal : CM Map (Nat × Nat)) = monoBlocks b subNed goal := by
  cases goal <;> rfl

/-- **Without a ring, `callDMR` is `callDM`.** -/
theorem callDMR_eq (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm) (b : Bell)
    (key : Option Noun) (hr : env.ring b = Option.none) (goal : CGoalL S) (region : List Nat) :
    (callDMR env rp rq p q b key goal region : CM Map (NextL S)) = callDM env rp rq p q b key goal region := by
  simp only [callDMR, callDM, hr, monoBlocksR_none]
  rcases key with _ | k <;> cases env.need b <;> rfl

/-- **Without a ring, `callLMR` is `callLM`.** -/
theorem callLMR_eq (env : CallEnv) (mono : Bool) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    {info : Option (Bell × Option Noun)} (h : InfoNoRing env info) (sup : Option Nomm) (goal : CGoalL S)
    (region : List Nat) :
    (callLMR env mono rp rq p q info sup goal region : CM Map (NextL S)) =
      callLM env mono rp rq p q info sup goal region := by
  rcases mono with _ | _ <;> rcases info with _ | ⟨b, key⟩
  · rfl
  · exact callLR_eq env rp rq p q h sup goal region
  · rfl
  · exact callDMR_eq env rp rq p q b key (h b key rfl) goal region

end Comp
end SkaModel
end Formalization
