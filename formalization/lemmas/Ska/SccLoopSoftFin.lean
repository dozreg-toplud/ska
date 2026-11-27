import lemmas.Ska.SccLoopSoft
import lemmas.Ska.CompLazyFinal

/-! # `finish` with soft calls (README Gaps 21.16)

`finish` (line 3560) runs `+coerce-lazy`, then `+soft-done`, `+add-ops` of the baked registers
and `+to-straight`.  With soft calls two of these read `soft.gen`:

* `+coerce-lazy` (line 6805): at a `%this` of the input need in a soft block (the bond block
  `o'` of `+soft-bond`) it calls `+soft-ask`, which records `[src ned]` in `req` instead of
  emitting the ops of `+kern-need`.  On the corpus this is what fills `req`: after the run
  `req` is empty in all 6 soft compiles, after `+coerce-lazy` it has 3 entries in each.
* `+soft-done` (line 5292) folds `+soft-emit` over `~(tap by soft.gen)` (`?: dropping gen`).

`+soft-emit` (line 5317) returns `gen` on an empty `req`.  Otherwise it cuts each requirement
`[src ned]` (`+soft-cut`, under the places `+soft-axes` gives the registers of the callee's
need): a part of the callee's subject is handed on (`tops`), a fetch that is the function's own
or that the callee reads first thing is emitted with a crash (`ops`); the parts under a `tops`
entry whose need is a cell or `%both` are tried at run time (`tries`).

**What the code of a soft call does at run time.**  The fetches of the subject formula's own
parts, and of the parts the callee reads first thing (`+sure-at`), are emitted in the head
block of the bond with `%cel`/`%hed`/`%tal` and crash on an atom, as the callee itself would.
The other parts are tried: if one is not a cell where the callee takes it apart, the callee's
subject is rebuilt from what there is (`+soft-cons`) and its subject version is called
(`%jsp`/`%csl`), else the call goes on to the n-ary version.  A part the callee takes whole
(need `%this`) is only moved into the callee's register, so neither crashes nor is tried.

**The model here covers `+soft-emit` without tries** (`softEmitT`): every requirement has a
need `%none` or `%this` (no `+soft-cut` of a cell, so no `+sure-at`, no `+soft-try`, no
`+soft-cons`, no `+soft-free`); then the code is `(emir head.s ~ ops fin.hed)`: the head block
of the bond gets the moves.  Any other requirement gives `none` (not modelled).  This is the
case of all 6 soft compiles of the corpus (`SccLoopSoftFinCheck.lean`). -/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## `+coerce-lazy` with soft calls -/

/-- The loop `sure-loop` of `+coerce-lazy` with `+soft-ask` at a `%this` in a soft block. -/
def sureLoopS (o : Nat) : Need → Need → CMS Map Unit
  | Need.none, tgt => if tgt = Need.none then pure () else liftS crashM
  | Need.this r, tgt => withSoft fun sf => if sf o then softAsk o r tgt else
      liftS (do let ops ← kernNeed r tgt; addOps o ops)
  | Need.pair p q, tgt =>
      match tgt with
      | Need.none => pure ()
      | Need.pair tp tq => do sureLoopS o p tp; sureLoopS o q tq
      | _ => liftS crashM
  | Need.both r h t, tgt =>
      match tgt with
      | Need.none => pure ()
      | Need.this d => if r = d then liftS crashM else liftS (addOps o [Pole.mov r d])
      | Need.pair tp tq => do sureLoopS o h tp; sureLoopS o t tq
      | Need.both d th tt =>
          if r = d then liftS crashM else do
            liftS (addOps o [Pole.mov r d])
            sureLoopS o h th
            sureLoopS o t tt

/-- `+coerce-lazy` on one node, soft calls read. -/
def coerceLazyS (ned : Need) (o : Nat) (laz : Sure S) (less : Cape) : CMS Map Unit := do
  let lok ← liftS (fun g => (coerceLok laz.lok less ned).map fun l => (l, g) : CM Map S)
  let tgt ← liftS (sureRequireLook ⟨laz.ned, lok⟩)
  sureLoopS o ned tgt

mutual
/-- **`+coerce-lazy`** (line 6805) with soft calls: the node, then the bonds, then the forks. -/
def coerceLazyLS (ned : Need) (less : Cape) : Nat → Lazy S → CMS Map Unit
  | o, mk s f b => do
    coerceLazyS ned o s less
    if f.isEmpty && b.isEmpty then pure () else do
    coerceBondsS ned less b
    coerceForksS ned less f

def coerceBondsS (ned : Need) (less : Cape) : List (Nat × Lazy S) → CMS Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    coerceLazyLS ned less o l
    coerceBondsS ned less rest

def coerceForksS (ned : Need) (less : Cape) : List (ForkE S) → CMS Map Unit
  | [] => pure ()
  | ((oy, y), (on, n)) :: rest => do
    coerceLazyLS ned less oy y
    coerceLazyLS ned less on n
    coerceForksS ned less rest
end

/-! ## `+soft-emit` without tries, `+soft-done` -/

/-- **`+soft-axes`** (line 5533): the place of each register of the callee's need in its
subject, as an association list whose first match is the last `+put:by`. -/
def softAxes : Need → Nat → List (Nat × Nat) → List (Nat × Nat)
  | Need.none, _, m => m
  | Need.this r, axe, m => (r, axe) :: m
  | Need.pair h t, axe, m => softAxes t (Hoon.pegF axe 3) (softAxes h (Hoon.pegF axe 2) m)
  | Need.both r h t, axe, m =>
      softAxes t (Hoon.pegF axe 3) (softAxes h (Hoon.pegF axe 2) ((r, axe) :: m))

/-- **`+soft-cut`** (line 5604) on a need `%none` or `%this` (`+soft-axis` of `%this r` is the
place of `r`, `%none` is `%any`): `[ops tops]`.  A cell or `%both` is not modelled (`none`);
`?<  =(src r.ned)` crashes. -/
def softCutT (src : Nat) (ned : Need) (axs : List (Nat × Nat)) :
    Option (List Pole × List (Nat × Nat × Need)) :=
  match ned with
  | Need.none => some ([], [])
  | Need.this r =>
    match axs.lookup r with
    | some q => some ([], [(q, src, ned)])
    | none => if src = r then none else some ([Pole.mov src r], [])
  | _ => none

/-- The loop of `+soft-emit` over `req.s`: each cut's lists in front of the accumulator. -/
def softCuts (axs : List (Nat × Nat)) :
    List (Nat × Need) → List Pole × List (Nat × Nat × Need) → Option (List Pole × List (Nat × Nat × Need))
  | [], acc => some acc
  | (src, ned) :: rest, acc => (softCutT src ned axs).bind fun (o, t) =>
      softCuts axs rest (o ++ acc.1, t ++ acc.2)

/-- The moves of the parts the callee takes whole (line 5338). -/
def softMoves (tops : List (Nat × Nat × Need)) : List Pole :=
  tops.filterMap fun (_, r, ned) =>
    match ned with
    | Need.this d => if r = d then none else some (Pole.mov r d)
    | Need.both d _ _ => if r = d then none else some (Pole.mov r d)
    | _ => none

/-- `tries` of `+soft-emit` (line 5350): the entries of `tops` whose need is not `%none`,
`%this`. -/
def softTries (tops : List (Nat × Nat × Need)) : List (Nat × Nat × Need) :=
  tops.filter fun (_, _, ned) => match ned with
    | Need.none => false
    | Need.this _ => false
    | _ => true

/-- **`+soft-emit` without tries** (line 5317): `gen` on an empty `req`, else the head block of
the bond (`[~ ~ %hop ~ *]`, asserted) gets the ops; `none` where tries would be made. -/
def softEmitT (s : SoftCall) : CM Map Unit := fun g =>
  if s.req = [] then some ((), g) else
  (softCuts (softAxes s.ned 1 []) s.req ([], [])).bind fun (opsC, topsC) =>
  if softTries topsC ≠ [] then none else
  (HoonMap.get g.blocks s.head).bind fun hed =>
  if hed.par = [] ∧ hed.body = [] then
    match hed.fin with
    | Termin.hop t => if t.args = [] then emir s.head ⟨[], opsC ++ softMoves topsC, hed.fin⟩ g else none
    | _ => none
  else none

/-- **`+soft-done`** (line 5292) on the list `~(tap by soft.gen)`. -/
def softDoneL : List (Nat × SoftCall) → CM Map Unit
  | [] => pure ()
  | (_, s) :: rest => do softEmitT s; softDoneL rest

/-- `+soft-done` on a state: nothing when dropping. -/
def softDone (tapS : Map SoftCall → List (Nat × SoftCall)) (st : GenSf Map) : Option (Gen Map) :=
  if st.g.drop then some st.g else (softDoneL (tapS st.soft) st.g).map (·.2)

/-! ## `finish` -/

/-- **The final pass of `+compile-scc-in` with soft calls**: `finishLFC` with `runLCS env snd ~`,
`+coerce-lazy` reading `soft.gen` and `+soft-done` over `tapS` (the order of `+tap:by`). -/
def finishLFCS [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (tapS : Map SoftCall → List (Nat × SoftCall)) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runLCS env snd Option.none nm (CGoalL.done : CGoalL S) [] (GenSf.ofGen gen0)).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1.g).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyLS nedFinal less nex.th.there nex.laz ⟨g2, g1.soft⟩).bind fun (_, g3) =>
        (softDone tapS g3).bind fun g3' =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3').bind fun (_, g4) =>
          toStraightF g4.cond g4.blocks bak.1 nex.th.there

end Comp
end SkaModel
end Formalization
