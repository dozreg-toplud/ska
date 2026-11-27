import lemmas.Ska.SccLoopReal
import lemmas.Ska.CompRunLC

/-! # Soft calls in the member compile: `runLCS` (README Gaps 21.15)

**What a soft call is** (`desk/lib/nock-compilation.hoon`), in five sentences.
1. A direct call `[%2 p q]` with no memo key is soft (`sof`, lines 3968 to 3975) when the
   subject formula does not make the callee's need `b-ned` by conses (`!(sound (made p sup)
   b-ned)`, `+sound-far`) and either the callee may read a part that is not sure to be a cell
   (`+need-soft b-ned b-sur less`) or `p` or `q` is hinted (`+hinted`).
2. At `mono` `|`, `+soft-new` (lines 4007 and 4019, arm at line 5196) puts in `soft.gen`, at
   the block `o` of the call, the entry `[kin b rin sub-ned b-sur o o o pro out aux ~]`
   (`kin` `%tail` under `%done`, else `%call`), and right after `+soft-bond` (line 4047) emits
   three hops `h → o' → l → o`, moves the entry to `o'` (with `head h`, `last l`) and hands the
   subject formula the lazy need `[*sure ~ [o' [sub-ned ~] ~ ~]~]` from `h` instead of
   `[sub-ned ~]` from `o`.
3. `soft.gen` is read again inside `+run`: `+kern` (under `+kerf` and `+lazy-shut`) records in a
   soft block what it would take apart there (`+soft-ask`, the field `req`) instead of emitting
   the ops, `+soft-less` leaves the soft bonds out of the size `+lazy-big` reads (`%6`,
   `+lazy-shut`), and `+soft-fork` makes `%6` on `%next` kerf its goal when a soft bond's need is
   not sound in both branches.
4. After the run `soft.gen` is read once more, by `finish` on `%done` (`+soft-done`, line 3569,
   after `+coerce-lazy`), which emits the blocks of each entry (`+soft-emit`): neither
   `+collapse-shape` nor `+bake-need` nor `+sure-of` reads it, so the `need-new` and `sur` of a
   member see a soft call only through the `laz` of the run.
5. A soft requirement does not fail the compile: a part the callee reads first thing (`sur`) is
   fetched with a crash, as the callee would crash on it, every other part is tried at run time
   and a noun that is not a cell sends the call to the callee's subject version, whole, and
   `+soft-emit` itself crashes only when `+soft-free` fails (line 5458).

**The model.**  `GenS` is `Gen` with `soft.gen`, `CMS` its state monad, `liftS` a step of `CM`
on the `Gen` part.  `runLCS env snd` is `runLC env` (`Ska/CompRunLC.lean`, not changed) with the
direct call of `callL` taken when `env.sof` holds (`callLS`: `softNew`, `softBond`), `+kern` with
`softAsk` (`kernS`), and `+soft-less`, `+soft-fork` reading the state (`withSoft`); `snd` is
`+sound` (`code.long-ska`), read by `+soft-fork` only.  `memDoneMS` is `memDoneM` with `runLCS`
from an empty `soft.gen`.  With an empty `soft.gen` and no soft call, `runLCS` is `runLC`
(`runLCS_eq`, `Ska/SccLoopSoftEq.lean`). -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The state of `+run` with `soft.gen`.** -/
structure GenS (Map : Type → Type) where
  g : Gen Map
  soft : Map SoftCall

/-- The arms of `+comp` that read or write `soft.gen` thread `GenS`. -/
abbrev CMS (Map : Type → Type) := StateT (GenS Map) Option

/-- A step of `CM` on the `Gen` part, `soft.gen` kept. -/
def liftS {α : Type} (m : CM Map α) : CMS Map α := fun s =>
  (m s.g).map fun p => (p.1, ⟨p.2, s.soft⟩)

/-- `(~(has by soft.gen) o)`. -/
def GenS.isSoft (s : GenS Map) (o : Nat) : Bool := (HoonMap.get s.soft o).isSome

/-- A step that reads the test `~(has by soft.gen)` of the current state. -/
def withSoft {α : Type} (k : (Nat → Bool) → CMS Map α) : CMS Map α := fun s => k s.isSoft s

/-- `+soft-new` (line 5196): the entry `[kin b rin ned sur o o o pro out ~ ~]` at `o`. -/
def softNew (o kin : Nat) (b : Bell) (rin : Option Noun) (ned : Need) (sur : NeedOrd) (pro out : Nat) :
    CMS Map Unit := fun s =>
  some ((), ⟨s.g, HoonMap.put s.soft o ⟨kin, b, rin, ned, sur, o, o, o, pro, out, []⟩⟩)

/-- `+soft-bond` (line 5212): three hops before the call, the entry moved to the middle one
(`+got:by` crashes on a missing entry). -/
def softBond (nex : NextL S) (region : List Nat) : CMS Map (NextL S) := do
  let call := nex.th.there
  let l ← liftS (emit ⟨[], [], Termin.hop nex.th⟩)
  let o ← liftS (emit ⟨[], [], Termin.hop (jmp0 l)⟩)
  let h ← liftS (emit ⟨[], [], Termin.hop (jmp0 o)⟩)
  liftS (setTag o region)
  fun s => (HoonMap.get s.soft call).map fun c =>
    (⟨mk Sure.bunt [] [(o, ofSure nex.laz.sure)], jmp0 h⟩,
     ⟨s.g, HoonMap.put (HoonMap.del s.soft call) o { c with head := h, last := l }⟩)

/-- `+soft-ask` (line 5227): `[src ned]` in front of `req` of the entry at `o`, unless dropping
(`+jab:by` crashes on a missing entry). -/
def softAsk (o src : Nat) (ned : Need) : CMS Map Unit := fun s =>
  if s.g.drop then some ((), s) else
  (HoonMap.get s.soft o).map fun c => ((), ⟨s.g, HoonMap.put s.soft o { c with req := (src, ned) :: c.req }⟩)

mutual
/-- `+walk-lazy` in `CMS`. -/
def walkLazyS (f : Nat → Sure S → CMS Map Unit) : Nat → Lazy S → CMS Map Unit
  | o, mk s fk bd => do
    f o s
    if fk.isEmpty && bd.isEmpty then pure () else do
    walkForksS f fk
    walkBondsS f bd

def walkForksS (f : Nat → Sure S → CMS Map Unit) : List ((Nat × Lazy S) × (Nat × Lazy S)) → CMS Map Unit
  | [] => pure ()
  | ((oy, y), (on, n)) :: rest => do
    walkLazyS f oy y
    walkLazyS f on n
    walkForksS f rest

def walkBondsS (f : Nat → Sure S → CMS Map Unit) : List (Nat × Lazy S) → CMS Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    walkLazyS f o l
    walkBondsS f rest
end

/-- **`+kern`** (line 5070), with `+soft-ask` in a soft block. -/
def kernS (o : Nat) (laz : Lazy S) : CMS Map Nat := do
  let r ← liftS re
  let s ← get
  if s.g.drop then pure r else do
    walkLazyS (fun oLaz sur => do
      let ned ← liftS (sureRequireLook sur)
      if ned = Need.none then pure () else do
      let src ← (if oLaz = o then pure r else liftS (proxy r oLaz) : CMS Map Nat)
      withSoft fun sf => if sf oLaz then softAsk oLaz src ned else do
      let ops ← liftS (kernNeed src ned)
      liftS (addOps oLaz ops)) o laz
    pure r

/-- `+lazy-shut` (line 5037), `+soft-less` reading the state. -/
def lazyShutS (o : Nat) (laz : Lazy S) : CMS Map (Lazy S) :=
  withSoft fun sf => if !(lazyBig (softLess sf laz)) then pure laz else do
    let r ← kernS o laz
    pure (ofSure ⟨Need.this r, HoonSet.empty⟩)

/-- `+kerf` (line 5044). -/
def kerfS (nex : NextL S) : CMS Map (Nat × Nat) := do
  let o ← liftS (emit ⟨[], [], Termin.hop nex.th⟩)
  let r ← kernS o nex.laz
  pure (o, r)

/-- `!&((sound q ned) (sound r ned))` of `+soft-fork`, on the ordered need. -/
def unsoundQR (snd : Nomm → NeedOrd → Bool) (q r : Nomm) (n : Need) : Bool :=
  !(snd q (needToOrd n) && snd r (needToOrd n))

def sixNextForkCS [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CMS Map (NextL S)) (p : Nomm)
    (laz : Lazy S) (th : Jmp) (region : List Nat) : CMS Map (NextL S) := do
  let rCond ← liftS re
  let (g0, g1) ← liftS (forkL ⟨laz, th⟩ rCond)
  let rid ← liftS idM
  let rb := rid :: region
  let condBefore ← liftS getCond
  let nex1 ← rr (CGoalL.next g1.laz g1.th) rb
  let condBetween ← liftS getCond
  let nex0 ← rq (CGoalL.next g0.laz g0.th) rb
  let (lazy, yes, nuh) ← liftS (sect nex0 nex1 g0.th.there g1.th.there rb condBefore condBetween)
  let lazy ← liftS (liftO (pastFork cod lazy p))
  let o ← liftS (emit ⟨[], [], Termin.brn rCond (jmp0 yes) (jmp0 nuh)⟩)
  let lazy ← lazyShutS o lazy
  let nexCond ← rp (CGoalL.next (ofSure ⟨Need.this rCond, HoonSet.empty⟩) (jmp0 o)) region
  liftS (copyL nexCond lazy)

def sixNextSimpleCS [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CMS Map (NextL S)) (p : Nomm)
    (laz : Lazy S) (th : Jmp) (region : List Nat) : CMS Map (NextL S) := do
  let o0 ← liftS oo
  let o1 ← liftS oo
  let (s0, s1) ← liftS (forkSure laz.sure th.there o0 o1)
  let rid ← liftS idM
  let rb := rid :: region
  let condBefore ← liftS getCond
  let nex1 ← rr (CGoalL.next (ofSure s1) (jmp0 o1)) rb
  let condBetween ← liftS getCond
  let nex0 ← rq (CGoalL.next (ofSure s0) (jmp0 o0)) rb
  let (lazy, yes, nuh) ← liftS (sect nex0 nex1 o0 o1 rb condBefore condBetween)
  let lazy ← liftS (liftO (pastFork cod lazy p))
  let nexCond ← rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
  withSoft fun sf => if !(lazyBig (softLess sf lazy)) then liftS (copyL nexCond lazy) else do
    let o ← liftS (emit ⟨[], [], Termin.hop nexCond.th⟩)
    let lazy ← lazyShutS o lazy
    liftS (copyL ⟨nexCond.laz, jmp0 o⟩ lazy)

def sixNextLCS [HoonMapKeys Map] (cod : Bell → Option Bool) (snd : Nomm → NeedOrd → Bool)
    (rp rq rr : CGoalL S → List Nat → CMS Map (NextL S)) (p q r : Nomm) :
    Nat → Lazy S → Jmp → List Nat → CMS Map (NextL S)
  | 0, _, _, _ => fun _ => Option.none
  | fuel + 1, laz, th, region =>
    match leap laz q r with
    | Option.none => fun _ => Option.none
    | some (some (rest, bys)) => do
      let nex ← sixNextLCS cod snd rp rq rr p q r fuel rest th region
      liftS (copyAll nex bys)
    | some Option.none =>
      if !(noneEquivalentL (mk Sure.bunt laz.fork laz.bond)) then
        withSoft fun sf =>
        if (whole q && whole r) || thisOnly laz || lazyBig (softLess sf laz) ||
            softFork sf (unsoundQR snd q r) laz then do
          let (out, pro) ← kerfS ⟨laz, th⟩
          sixNextLCS cod snd rp rq rr p q r fuel (ofSure ⟨Need.this pro, HoonSet.empty⟩) (jmp0 out) region
        else sixNextForkCS cod rp rq rr p laz th region
      else sixNextSimpleCS cod rp rq rr p laz th region

/-- **The case `%2` with soft calls** (`callL` of `Ska/CompCall.lean` plus the direct call with
`sof`): `+soft-new` at the block of the call, then `+soft-bond` when the block is soft. -/
def callLS (env : CallEnv) (rp rq : CGoalL S → List Nat → CMS Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CMS Map (NextL S) :=
  match info with
  | Option.none => do
      let nex ← liftS (simpleNextL goal)
      let (out, pro) ← kerfS nex
      let rSub ← liftS re
      let rFol ← liftS re
      let o ← liftS (emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩)
      let nexFol ← rq (CGoalL.next (ofSure (lazyReg rFol)) (jmp0 o)) region
      let nexFol ← liftS (pastL env.cod nexFol p region)
      let nexSub ← rp (CGoalL.next (ofSure (lazyReg rSub)) nexFol.th) region
      liftS (copyL nexSub nexFol.laz)
  | some (b, key) =>
      let drop : Option Jmp := match goal with
        | CGoalL.next laz th => if env.pure b && noneEquivalentL laz then some th else Option.none
        | _ => Option.none
      match drop with
      | some th => do
          let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
            else rq (CGoalL.next (ofSure Sure.bunt) th) region : CMS Map (NextL S))
          let nexFol ← liftS (pastL env.cod nexFol p region)
          let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
          liftS (copyL nexSub nexFol.laz)
      | Option.none =>
          match key, env.ring b, env.need b with
          | Option.none, Option.none, some bNed => do
            let sof := env.sof (made p sup) p q b bNed
            let subNed ← liftS (needOrdAllocRegs bNed)
            let subV := flattenNeed subNed
            let callBlock ← (match goal with
              | CGoalL.done => do
                  let o ← liftS (emit ⟨[], [], Termin.jmp b subV⟩)
                  if sof then softNew o 1 b Option.none subNed (env.sure b) 0 0
                  pure o
              | g => do
                  let nex ← liftS (simpleNextL g)
                  let (out, pro) ← kerfS nex
                  let o ← liftS (emit ⟨[], [Pole.cal b subV pro], Termin.hop (jmp0 out)⟩)
                  if sof then softNew o 0 b Option.none subNed (env.sure b) pro out
                  pure o : CMS Map Nat)
            let nexArg0 : NextL S := ⟨ofSure ⟨subNed, HoonSet.empty⟩, jmp0 callBlock⟩
            let nexArg ← withSoft fun sf => if sf callBlock then softBond nexArg0 region else pure nexArg0
            let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
              else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CMS Map (NextL S))
            let nexFol ← liftS (pastL env.cod nexFol p region)
            let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
            liftS (copyL nexSub nexFol.laz)
          | _, _, _ => fun _ => Option.none

/-- **`+run` at `mono` `|` with soft calls**: `runLC` with `callLS`, `kernS`, `lazyShutS` and
`+soft-less` / `+soft-fork` reading `soft.gen`. -/
def runLCS [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool) :
    Option Nomm → Nomm → CGoalL S → List Nat → CMS Map (NextL S)
  | sup, Nomm.cons p q, goal, region => do
      let goal ← (match goal with
        | CGoalL.done => do
            let r ← liftS re
            let o ← liftS (emit ⟨[], [], Termin.don r⟩)
            pure (CGoalL.next (ofSure (lazyReg r)) (jmp0 o))
        | g => pure g : CMS Map (CGoalL S))
      match goal with
      | CGoalL.pick _ _ => do
          let o ← liftS (emit ⟨[], [], Termin.bom Option.none⟩)
          let nex2 ← runLCS env snd sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← liftS (pastL env.cod nex2 p region)
          let nex1 ← runLCS env snd sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          liftS (copyL nex1 nex2.laz)
      | CGoalL.next laz th => do
          let (hed, tel, o) ← liftS (splitL ⟨laz, th⟩)
          let nexh ← liftS (pastL env.cod ⟨hed, jmp0 o⟩ q region)
          let nex2 ← runLCS env snd sup q (CGoalL.next tel nexh.th) region
          let nex2 ← liftS (pastL env.cod nex2 p region)
          let nex1 ← runLCS env snd sup p (CGoalL.next nexh.laz nex2.th) region
          liftS (copyL nex1 nex2.laz)
      | CGoalL.done => fun _ => Option.none
  | sup, Nomm.n0 ax, goal, region => liftS (runLC env sup (Nomm.n0 ax) goal region)
  | sup, Nomm.n1 k, goal, region => liftS (runLC env sup (Nomm.n1 k) goal region)
  | sup, Nomm.n3 p, goal, region =>
      match goal with
      | CGoalL.next laz th =>
          if noneEquivalentL laz then runLCS env snd sup p (CGoalL.next laz th) region else do
            let a ← liftS (collapseLazyAtomL ⟨laz, th⟩)
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← liftS (forl r o)
                let r' ← liftS re
                let oc ← liftS (emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩)
                runLCS env snd sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← liftS re
          let oc ← liftS (emit ⟨[], [], Termin.clq r z o⟩)
          runLCS env snd sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← liftS doneBlocks
          let r ← liftS re
          let oc ← liftS (emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩)
          runLCS env snd sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← liftS re
          let arg ← liftS re
          let o ← liftS (emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩)
          runLCS env snd sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← liftS re
          let arg ← liftS re
          let o' ← liftS (emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩)
          runLCS env snd sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← liftS (collapseLazyAtomL ⟨laz, th⟩)
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← liftS re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CMS Map (Nat × Nat))
          let arg ← liftS re
          let o ← liftS (emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩)
          runLCS env snd sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
  | sup, Nomm.n5 p q, goal, region => do
      let rp ← liftS re
      let rq ← liftS re
      let o ← (match goal with
        | CGoalL.pick z o => liftS (emit ⟨[], [], Termin.eqq rp rq z o⟩)
        | CGoalL.done => do
            let (o0, o1) ← liftS doneBlocks
            liftS (emit ⟨[], [], Termin.eqq rp rq (jmp0 o0) (jmp0 o1)⟩)
        | CGoalL.next laz th => do
            let a ← liftS (collapseLazyAtomL ⟨laz, th⟩)
            match a with
            | Option.none =>
                if th.args = [] then liftS (emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩)
                else fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← liftS (forl r o)
                liftS (emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩) : CMS Map Nat)
      let nexq ← runLCS env snd sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← liftS (pastL env.cod nexq p region)
      let nexp ← runLCS env snd sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      liftS (copyL nexp nexq.laz)
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLCS env.cod snd (runLCS env snd sup p) (runLCS env snd sup q)
          (runLCS env snd sup r) p q r 3 laz th region
      | _ => do
          let nex1 ← runLCS env snd sup r goal region
          let nex0 ← runLCS env snd sup q goal region
          let yes ← liftS (emit ⟨[], [], Termin.hop nex0.th⟩)
          let nuh ← liftS (emit ⟨[], [], Termin.hop nex1.th⟩)
          liftS (setTag yes region)
          liftS (setTag nuh region)
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftS (liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p))
          let nexCond ← runLCS env snd sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          withSoft fun sf => if !(lazyBig (softLess sf lazy)) then liftS (copyL nexCond lazy) else do
            let o ← liftS (emit ⟨[], [], Termin.hop nexCond.th⟩)
            let lazy ← lazyShutS o lazy
            liftS (copyL ⟨nexCond.laz, jmp0 o⟩ lazy)
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCS env snd (some p) q goal region
      runLCS env snd sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← liftS (simpleNextL goal)
      let (don, rec, o) ← liftS (intoL next a)
      let nexR ← liftS (pastL env.cod ⟨rec, jmp0 o⟩ v region)
      let nexDon ← runLCS env snd sup v (CGoalL.next don nexR.th) region
      let nexDon ← liftS (pastL env.cod nexDon q region)
      let nexRec ← runLCS env snd sup q (CGoalL.next nexR.laz nexDon.th) region
      liftS (copyL nexRec nexDon.laz)
  | sup, Nomm.n2 p q info, goal, region =>
      callLS env (runLCS env snd sup p) (runLCS env snd sup q) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

/-- An empty `soft.gen` on a state. -/
def GenS.ofGen (g : Gen Map) : GenS Map := ⟨g, HoonMap.empty⟩

end Comp
end SkaModel

namespace SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- **The `%done` compile of a member with soft calls**: `memDoneM` with `runLCS env snd ~`
from an empty `soft.gen`; the chain after the run does not read `soft.gen` (sentence 4). -/
noncomputable def memDoneMS (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (m : MemInfo) :
    Option (Out NeedOrd) :=
  (runLCS (S := CSet) (Map := TreapMap mugF) env snd Option.none m.nm CGoalL.done [] (GenS.ofGen gen0)).bind
    fun (nex, g1) =>
      if nex.th.args ≠ [] then Option.none else
      (shapeCol m.fuel nex.laz m.cape).bind fun ord =>
        (needOrdAllocRegs ord g1.g).bind fun (nedF, _) =>
          (sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok m.cape).map fun sur =>
            ⟨needToOrd (bakeNeed nedF (Sock.mk m.cape m.data)).1, sur⟩

end SkaModel.SccLoop
end Formalization
