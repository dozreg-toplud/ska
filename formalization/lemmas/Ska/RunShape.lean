import lemmas.Ska.SofModel
import lemmas.Ska.CompCall
import lemmas.Ska.BakeNeed

/-!
# A model of `+run-shape` (track A, 2026-11-27)

`++  run-shape` of `+comp` (`desk/lib/nock-compilation.hoon`, line 4399): "the
traversal of +run reduced to what decides the lazy need of the subject.  No
code, no registers, no blocks".  The sweeps of `+compile-scc-in` (modes `%must`
and `%may` of `member`) run it, then `+laze-collapse` or `+laze-may`, then
`+bake-need-ord`.

## The types

* `$sure-ordered` `[ned=need-ordered lok=(set @)]`: `SureO S`.
* `$laze` `[sure=sure-ordered fork=(list [y=[o=@uxid laz=$] n=[o=@uxid laz=$]])
  bond=(list [o=@uxid laz=$])]`: `Laze S`.  It is not `Lazy S` of
  `CompLazy.lean`: the sure need of a `laze` is a `need-ordered` (no
  registers, `NeedOrd`), that of a `need-lazy` a `need` with registers.  The
  shape is the same, and so are the arms (`laze-split` is `+split` without
  registers and blocks), so each arm below follows its `Lazy` model.
* `$goal-shape` `$%([%pick ~] [%done ~] [%next laz=laze])`: `GoalS S`.
* The state: `+run-shape` reads and changes only `id-gen` (`+id`) and `sofs`
  of `gen` (`RSt S`), and reads `cache.gen` through `+callee-need` and
  `+callee-sure`, which the model takes from the environment `ShapeEnv` (as
  `CallEnv` does for `+run`): `need b` is `+callee-need` (a hot jet's need,
  `map-local` or `top` in the SCC, the n-ary cache, or a compile of the
  callee's SCC: the model does not see the compile, only its need), `sure b`
  is `+callee-sure`, `jet b` whether `(biff rin ~(get by jets-hot))` is a
  `^`, `pure b` the flag `pure` of `(~(got by code.long-ska) b)` (`none`
  where `got` crashes), `cod b` its `nomm` (for `+sound-far`).
* The monad `SM S = StateT (RSt S) Option`: `none` is a crash.

## Totality

Every function is structural on the nomm or on the `laze`, but for two:
* the case `%6` under `%next` runs the whole case again on the same nomm
  with another goal (`$(goal [%next rest.u.lep])` after `+laze-leaps`,
  `$(goal [%next this])` where `+run` would `+kerf`): `sixShape` has fuel
  (`sixFuel = 4`; one leap, one kerf and the final run take 3);
* the walks down an axis (`+laze-into`'s trap, `+laze-from`'s, `+need-ord-cut`)
  recurse on `mas axe`, well-founded on the axis.

The case `[^ *]` under `%done` runs again with `[%next this]`: the model
takes that goal at once (`consNext`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

/-- `$sure-ordered`. -/
structure SureO (S : Type) where
  ned : NeedOrd
  lok : S

/-- `$laze`. -/
inductive Laze (S : Type) where
  | mk (sure : SureO S) (fork : List ((Nat × Laze S) × (Nat × Laze S))) (bond : List (Nat × Laze S))

/-- `$goal-shape`. -/
inductive GoalS (S : Type) where
  | pick
  | done
  | next (laz : Laze S)

/-- The part of `gen` that `+run-shape` changes: `id-gen` and `sofs`. -/
structure RSt (S : Type) where
  idg : Nat
  sofs : S

/-- What `+run-shape` reads of the door and of `cache.gen`. -/
structure ShapeEnv where
  need : Bell → Option NeedOrd
  sure : Bell → NeedOrd
  jet : Bell → Bool
  pure : Bell → Option Bool
  cod : Bell → Option Nomm

/-- The monad: the state, `none` for a crash. -/
abbrev SM (S : Type) := StateT (RSt S) Option

variable {S : Type} [HoonSet S]

namespace SureO
/-- `*sure-ordered`. -/
def bunt : SureO S := ⟨NeedOrd.none, HoonSet.empty⟩
def toNoun (s : SureO S) : Noun := C s.ned.toNoun (HoonSet.toNoun s.lok)
end SureO

namespace Laze
def sure : Laze S → SureO S | mk s _ _ => s
def fork : Laze S → List ((Nat × Laze S) × (Nat × Laze S)) | mk _ f _ => f
def bond : Laze S → List (Nat × Laze S) | mk _ _ b => b

mutual
/-- The noun of a `laze`. -/
def toNoun : Laze S → Noun
  | mk s f b => C s.toNoun (C (forksNoun f) (bondsNoun b))
def forksNoun : List ((Nat × Laze S) × (Nat × Laze S)) → Noun
  | [] => A 0
  | ((oy, ly), (on, ln)) :: rest => C (C (C (A oy) (toNoun ly)) (C (A on) (toNoun ln))) (forksNoun rest)
def bondsNoun : List (Nat × Laze S) → Noun
  | [] => A 0
  | (o, l) :: rest => C (C (A o) (toNoun l)) (bondsNoun rest)
end
end Laze

open Laze

/-- `none` of `+run-shape`: `*laze`. -/
def noneL : Laze S := mk SureO.bunt [] []

/-- `this` of `+run-shape`: `[[this+~ ~] ~ ~]`. -/
def thisL : Laze S := mk ⟨NeedOrd.this, HoonSet.empty⟩ [] []

/-- `[[ned ~] ~ ~]`. -/
def nedL (ned : NeedOrd) : Laze S := mk ⟨ned, HoonSet.empty⟩ [] []

/-- `+id`. -/
def idS : SM S Nat := fun st => some (st.idg, { st with idg := st.idg + 1 })

/-- A crash or a value, in the monad. -/
def liftS {α : Type} (o : Option α) : SM S α := fun st => o.map (·, st)

/-- `(~(put in sofs.gen) i)`. -/
def putSofs (i : Nat) : SM S Unit := fun st => some ((), { st with sofs := HoonSet.put st.sofs i })

/-- `(~(has in sofs.gen) o)`. -/
def sofsHas (s : S) (o : Nat) : Bool := (HoonSet.toList s).contains o

/-- `+sound`: `(sound-far nom ned code.long-ska 3)`. -/
def soundS (env : ShapeEnv) (nom : Nomm) (ned : NeedOrd) : Option Bool := soundFar env.cod 3 nom ned

/-! ## The small arms -/

/-- `+laze-empty`. -/
def lazeEmpty (l : Laze S) : Bool :=
  decide (l.sure.ned = NeedOrd.none) && HoonSet.small l.sure.lok && l.fork.isEmpty && l.bond.isEmpty

/-- `+laze-prune`. -/
def lazePrune : Laze S → Laze S
  | mk s f b => mk s (f.filter fun e => !(lazeEmpty e.1.2 && lazeEmpty e.2.2)) (b.filter fun e => !lazeEmpty e.2)

mutual
/-- `+laze-none-equivalent`. -/
def noneEq : Laze S → Bool
  | mk s f b => decide (s.ned = NeedOrd.none) && HoonSet.small s.lok && noneEqF f && noneEqB b
def noneEqF : List ((Nat × Laze S) × (Nat × Laze S)) → Bool
  | [] => true
  | ((_, a), (_, b)) :: rest => (noneEq a && noneEq b) && noneEqF rest
def noneEqB : List (Nat × Laze S) → Bool
  | [] => true
  | (_, n) :: rest => noneEq n && noneEqB rest
end

mutual
/-- `+laze-this-only`. -/
def thisOnlyS : Laze S → Bool
  | mk s f b => (match s.ned with | NeedOrd.this => true | NeedOrd.none => true | _ => false) &&
      HoonSet.small s.lok && thisOnlyF f && thisOnlyB b
def thisOnlyF : List ((Nat × Laze S) × (Nat × Laze S)) → Bool
  | [] => true
  | ((_, a), (_, b)) :: rest => (thisOnlyS a && thisOnlyS b) && thisOnlyF rest
def thisOnlyB : List (Nat × Laze S) → Bool
  | [] => true
  | (_, n) :: rest => thisOnlyS n && thisOnlyB rest
end

mutual
/-- The count of `+laze-big` from `c`; a bond whose block is in `sofs`
(`soft o`) is not counted. -/
def cntGo (soft : Nat → Bool) (c : Nat) : Laze S → Nat
  | mk _ f b => if c > Lazy.lazyMax then c else cntB soft (cntF soft (c + 1) f) b
def cntF (soft : Nat → Bool) (c : Nat) : List ((Nat × Laze S) × (Nat × Laze S)) → Nat
  | [] => c
  | ((_, y), (_, n)) :: rest => cntF soft (cntGo soft (cntGo soft c y) n) rest
def cntB (soft : Nat → Bool) (c : Nat) : List (Nat × Laze S) → Nat
  | [] => c
  | (o, l) :: rest => if soft o then cntB soft c rest else cntB soft (cntGo soft c l) rest
end

/-- `+laze-big`. -/
def lazeBig (soft : Nat → Bool) (l : Laze S) : Bool := decide (cntGo soft 0 l > Lazy.lazyMax)

mutual
/-- `+laze-soft-fork`, with `uns ned` for `!&((sound q ned) (sound r ned))`. -/
def softForkS (soft : Nat → Bool) (uns : NeedOrd → Option Bool) : Laze S → Option Bool
  | mk _ f b => orB (softForkSB soft uns b) (softForkSF soft uns f)
def softForkSB (soft : Nat → Bool) (uns : NeedOrd → Option Bool) : List (Nat × Laze S) → Option Bool
  | [] => some false
  | (o, l) :: rest => orB (orB (if soft o then uns l.sure.ned else some false) (softForkS soft uns l))
      (softForkSB soft uns rest)
def softForkSF (soft : Nat → Bool) (uns : NeedOrd → Option Bool) :
    List ((Nat × Laze S) × (Nat × Laze S)) → Option Bool
  | [] => some false
  | ((_, a), (_, b)) :: rest => orB (orB (softForkS soft uns a) (softForkS soft uns b)) (softForkSF soft uns rest)
end

/-- `!&((sound q ned) (sound r ned))`. -/
def unsS (env : ShapeEnv) (q r : Nomm) (ned : NeedOrd) : Option Bool :=
  (andO (soundS env q ned) (soundS env r ned)).map (! ·)

/-! ## `+laze-split` -/

/-- `+laze-must`. -/
def lazeMust : NeedOrd → NeedOrd
  | NeedOrd.both h t => NeedOrd.both h t
  | NeedOrd.this => NeedOrd.this
  | NeedOrd.pair p q => NeedOrd.both p q
  | NeedOrd.none => NeedOrd.this

/-- The `rep` of `+laze-split` over the looks. -/
def splitLokS (lok : S) : Option (S × S) :=
  (HoonSet.toList lok).foldl (fun acc axe => acc.bind fun (h, t) =>
    if axe = 0 then Option.none else
    if axe = 1 ∨ axe = 2 ∨ axe = 3 then some (h, t) else
    if cap axe = 2 then some (HoonSet.put h (mas axe), t) else some (h, HoonSet.put t (mas axe)))
    (some (HoonSet.empty, HoonSet.empty))

/-- The halves of the sure need in `+laze-split`. -/
def splitNed : NeedOrd → NeedOrd × NeedOrd
  | NeedOrd.pair p q => (p, q)
  | NeedOrd.none => (NeedOrd.none, NeedOrd.none)
  | NeedOrd.this => (NeedOrd.this, NeedOrd.this)
  | NeedOrd.both h t => (lazeMust h, lazeMust t)

mutual
/-- **`+laze-split`**. -/
def lazeSplit : Laze S → Option (Laze S × Laze S)
  | mk s f b => (splitLokS s.lok).bind fun (lh, lt) =>
    if f.isEmpty && b.isEmpty then
      some (mk ⟨(splitNed s.ned).1, lh⟩ [] [], mk ⟨(splitNed s.ned).2, lt⟩ [] [])
    else (splitF f).bind fun fs => (splitB b).map fun bs =>
      (lazePrune (mk ⟨(splitNed s.ned).1, lh⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
       lazePrune (mk ⟨(splitNed s.ned).2, lt⟩ (fs.map Prod.snd) (bs.map Prod.snd)))
def splitF : List ((Nat × Laze S) × (Nat × Laze S)) →
    Option (List (((Nat × Laze S) × (Nat × Laze S)) × ((Nat × Laze S) × (Nat × Laze S))))
  | [] => some []
  | ((oy, y), (on, n)) :: rest => (lazeSplit y).bind fun (yh, yt) => (lazeSplit n).bind fun (nh, nt) =>
      (splitF rest).map fun r => (((oy, yh), (on, nh)), ((oy, yt), (on, nt))) :: r
def splitB : List (Nat × Laze S) → Option (List ((Nat × Laze S) × (Nat × Laze S)))
  | [] => some []
  | (o, l) :: rest => (lazeSplit l).bind fun (h, t) => (splitB rest).map fun r => ((o, h), (o, t)) :: r
end

/-! ## `+laze-into` -/

/-- The `rep` of `+laze-into` over the looks, then `axe` put into the
recipient's looks unless it is `1`. -/
def intoLokS (axe : Nat) (lok : S) : Option (S × S) :=
  ((HoonSet.toList lok).foldl (fun acc a => acc.bind fun (d, r) =>
    (gep axe a).map fun rest => match rest with
      | Option.none => (d, HoonSet.put r a)
      | some u => if u = 1 then (d, r) else (HoonSet.put d u, r))
    (some (HoonSet.empty, HoonSet.empty))).map fun (d, r) => (d, if axe = 1 then r else HoonSet.put r axe)

/-- The trap of `+laze-into` down the axis, with the stack `tack`. -/
def intoGo (axe : Nat) (ned : NeedOrd) (tack : List (Bool × NeedOrd)) : Option (NeedOrd × NeedOrd) :=
  if axe = 1 then
    some (ned, tack.foldl (fun acc (e : Bool × NeedOrd) => if e.1 then consOrd acc e.2 else consOrd e.2 acc)
      NeedOrd.none)
  else if axe = 0 then Option.none
  else
    let h := decide (cap axe = 2)
    match ned with
    | NeedOrd.none => intoGo (mas axe) ned ((h, ned) :: tack)
    | NeedOrd.this => intoGo (mas axe) ned ((h, ned) :: tack)
    | NeedOrd.pair p q =>
      if h then intoGo (mas axe) p ((h, q) :: tack) else intoGo (mas axe) q ((h, p) :: tack)
    | NeedOrd.both l r =>
      if h then intoGo (mas axe) (lazeMust l) ((h, lazeMust r) :: tack)
      else intoGo (mas axe) (lazeMust r) ((h, lazeMust l) :: tack)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- The needs of the donor and the recipient in `+laze-into`. -/
def intoNed (axe : Nat) (ned : NeedOrd) : Option (NeedOrd × NeedOrd) :=
  if axe = 1 then some (ned, NeedOrd.none) else intoGo axe ned []

mutual
/-- **`+laze-into`**. -/
def lazeInto (axe : Nat) : Laze S → Option (Laze S × Laze S)
  | mk s f b => if axe = 0 then Option.none else
    (intoLokS axe s.lok).bind fun (ld, lr) => (intoNed axe s.ned).bind fun (nd, nr) =>
    if f.isEmpty && b.isEmpty then some (mk ⟨nd, ld⟩ [] [], mk ⟨nr, lr⟩ [] [])
    else (intoF axe f).bind fun fs => (intoB axe b).map fun bs =>
      (lazePrune (mk ⟨nd, ld⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
       lazePrune (mk ⟨nr, lr⟩ (fs.map Prod.snd) (bs.map Prod.snd)))
def intoF (axe : Nat) : List ((Nat × Laze S) × (Nat × Laze S)) →
    Option (List (((Nat × Laze S) × (Nat × Laze S)) × ((Nat × Laze S) × (Nat × Laze S))))
  | [] => some []
  | ((oy, y), (on, n)) :: rest => (lazeInto axe y).bind fun (yd, yr) => (lazeInto axe n).bind fun (nd, nr) =>
      (intoF axe rest).map fun r => (((oy, yd), (on, nd)), ((oy, yr), (on, nr))) :: r
def intoB (axe : Nat) : List (Nat × Laze S) → Option (List ((Nat × Laze S) × (Nat × Laze S)))
  | [] => some []
  | (o, l) :: rest => (lazeInto axe l).bind fun (d, r) => (intoB axe rest).map fun rs => ((o, d), (o, r)) :: rs
end

/-! ## `+laze-from`, `+need-ord-cut`, `+need-ord-from` -/

/-- The trap of `+laze-from` (and of `+need-ord-from`) down the axis. -/
def fromOrd (axe : Nat) (ned : NeedOrd) : Option NeedOrd :=
  if axe = 1 then some ned else if axe = 0 then Option.none else
  if cap axe = 2 then (fromOrd (mas axe) ned).map fun x => NeedOrd.pair x NeedOrd.none
  else (fromOrd (mas axe) ned).map fun x => NeedOrd.pair NeedOrd.none x
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- The sure need of `+laze-from`. -/
def fromSureS (axe : Nat) (s : SureO S) : Option (SureO S) :=
  if s.ned = NeedOrd.none then
    if axe = 1 then Option.none else
    some ⟨NeedOrd.none, if HoonSet.isEmpty s.lok then setOne axe else setRun (Hoon.pegF axe) s.lok⟩
  else (fromOrd axe s.ned).map fun n => ⟨n, setRun (Hoon.pegF axe) s.lok⟩

mutual
/-- **`+laze-from`**. -/
def lazeFrom (axe : Nat) : Laze S → Option (Laze S)
  | mk s f b => if axe = 0 then Option.none else
    (fromSureS axe s).bind fun sur =>
    if f.isEmpty && b.isEmpty then some (mk sur [] [])
    else (fromF axe f).bind fun fs => (fromB axe b).map fun bs => mk sur fs bs
def fromF (axe : Nat) : List ((Nat × Laze S) × (Nat × Laze S)) → Option (List ((Nat × Laze S) × (Nat × Laze S)))
  | [] => some []
  | ((oy, y), (on, n)) :: rest => (lazeFrom axe y).bind fun y' => (lazeFrom axe n).bind fun n' =>
      (fromF axe rest).map fun r => ((oy, y'), (on, n')) :: r
def fromB (axe : Nat) : List (Nat × Laze S) → Option (List (Nat × Laze S))
  | [] => some []
  | (o, l) :: rest => (lazeFrom axe l).bind fun l' => (fromB axe rest).map fun r => (o, l') :: r
end

/-- **`+need-ord-cut`**: `none` is a crash, `some none` is `~`. -/
def needOrdCut (axe : Nat) (ned : NeedOrd) : Option (Option (NeedOrd × NeedOrd)) :=
  if axe = 1 then some (some (ned, NeedOrd.none)) else
  match ned with
  | NeedOrd.none => some (some (ned, ned))
  | NeedOrd.this => some Option.none
  | NeedOrd.both _ _ => some Option.none
  | NeedOrd.pair p q =>
    if axe = 0 then Option.none else
    if cap axe = 2 then (needOrdCut (mas axe) p).map fun k => k.map fun e => (e.1, consOrd e.2 q)
    else (needOrdCut (mas axe) q).map fun k => k.map fun e => (e.1, consOrd p e.2)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- **`+need-ord-from`**. -/
def needOrdFrom (axe : Nat) (ned : NeedOrd) : Option NeedOrd :=
  if ned = NeedOrd.none then some ned else fromOrd axe ned

/-! ## `+laze-leap`, `+laze-leaps` -/

mutual
/-- **`+laze-leap`**. -/
def lazeLeap (p s : Nat) : Laze S → Option (Laze S × Laze S)
  | mk sur fk bd => do
    let cut ← needOrdCut p sur.ned
    let (sb, sr) ← (match cut with
      | Option.none => some ((SureO.bunt : SureO S), sur)
      | some (don, rec) => do
          let (lb, lr) ← leapLok p s sur.lok
          let nf ← needOrdFrom s don
          pure ((⟨nf, lb⟩ : SureO S), (⟨rec, lr⟩ : SureO S)) : Option (SureO S × SureO S))
    let fs ← leapSF p s fk
    let bs ← leapSB p s bd
    pure (lazePrune (mk sb (fs.map Prod.fst) (bs.map Prod.fst)), lazePrune (mk sr (fs.map Prod.snd) (bs.map Prod.snd)))
def leapSF (p s : Nat) : List ((Nat × Laze S) × (Nat × Laze S)) →
    Option (List (((Nat × Laze S) × (Nat × Laze S)) × ((Nat × Laze S) × (Nat × Laze S))))
  | [] => some []
  | ((oy, y), (on, n)) :: rest =>
    (lazeLeap p s y).bind fun (yb, yr) => (lazeLeap p s n).bind fun (nb, nr) =>
      (leapSF p s rest).map fun r => (((oy, yb), (on, nb)), ((oy, yr), (on, nr))) :: r
def leapSB (p s : Nat) : List (Nat × Laze S) → Option (List ((Nat × Laze S) × (Nat × Laze S)))
  | [] => some []
  | (o, l) :: rest => (lazeLeap p s l).bind fun (b, r) => (leapSB p s rest).map fun rs => ((o, b), (o, r)) :: rs
end

/-- The loop of `+laze-leaps` over the parts. -/
def leapsLoop (sur : SureO S) : List (Nat × Nat) → Laze S → List (Laze S) →
    Option (Option (Laze S × List (Laze S)))
  | [], lab, bys => if bys.isEmpty then some Option.none else some (some (mk sur lab.fork lab.bond, bys))
  | (p, s) :: rest, lab, bys => (lazeLeap p s lab).bind fun (b, r) =>
      if lazeEmpty b then leapsLoop sur rest lab bys else leapsLoop sur rest r (b :: bys)

/-- **`+laze-leaps`**. -/
def lazeLeaps (laz : Laze S) (q r : Nomm) : Option (Option (Laze S × List (Laze S))) :=
  if laz.fork.isEmpty && laz.bond.isEmpty then some Option.none else
  (passBoth q r).bind fun pas => leapsLoop laz.sure pas (mk SureO.bunt laz.fork laz.bond) []

/-! ## `+laze-copy` -/

/-- `(~(get by index) o)` of `+laze-copy`'s `malt`: the last entry with
the key. -/
def lastF (sec : List ((Nat × Laze S) × (Nat × Laze S))) (o : Nat) : Option ((Nat × Laze S) × (Nat × Laze S)) :=
  (sec.filter fun e => e.1.1 == o).getLast?

def lastB (sec : List (Nat × Laze S)) (o : Nat) : Option (Nat × Laze S) :=
  (sec.filter fun e => e.1 == o).getLast?

mutual
/-- **`+laze-copy`**. -/
def lazeCopy : Laze S → Laze S → Option (Laze S)
  | mk s f b, mk s2 f2 b2 =>
    let sur : SureO S := ⟨uniOrd s.ned s2.ned, HoonSet.uni s.lok s2.lok⟩
    ((if f2.isEmpty then some f else if f.isEmpty then some f2 else
      (copyF f f2).map fun m => m ++ f2.filter fun e => !(f.any fun x => x.1.1 == e.1.1)) : Option _).bind fun fk =>
    ((if b2.isEmpty then some b else if b.isEmpty then some b2 else
      (copyB b b2).map fun m => m ++ b2.filter fun e => !(b.any fun x => x.1 == e.1)) : Option _).map fun bd =>
    mk sur fk bd
def copyF : List ((Nat × Laze S) × (Nat × Laze S)) → List ((Nat × Laze S) × (Nat × Laze S)) →
    Option (List ((Nat × Laze S) × (Nat × Laze S)))
  | [], _ => some []
  | ((oy, ly), (on, ln)) :: rest, sec =>
    match lastF sec oy with
    | Option.none => (copyF rest sec).map fun r => ((oy, ly), (on, ln)) :: r
    | some ((_, my), (mon, mn)) =>
      if on ≠ mon then Option.none else
      (lazeCopy ly my).bind fun y => (lazeCopy ln mn).bind fun n =>
        (copyF rest sec).map fun r => ((oy, y), (on, n)) :: r
def copyB : List (Nat × Laze S) → List (Nat × Laze S) → Option (List (Nat × Laze S))
  | [], _ => some []
  | (o, l) :: rest, sec =>
    match lastB sec o with
    | Option.none => (copyB rest sec).map fun r => (o, l) :: r
    | some (_, m) => (lazeCopy l m).bind fun c => (copyB rest sec).map fun r => (o, c) :: r
end

/-! ## The arms that take identifiers -/

mutual
/-- **`+laze-branch`**. -/
def lazeBranch : Laze S → SM S (Laze S × Laze S)
  | mk s f b => do
    let fs ← branchF f
    let bs ← branchB b
    pure (mk s (fs.map Prod.fst) (bs.map Prod.fst), mk s (fs.map Prod.snd) (bs.map Prod.snd))
def branchF : List ((Nat × Laze S) × (Nat × Laze S)) →
    SM S (List (((Nat × Laze S) × (Nat × Laze S)) × ((Nat × Laze S) × (Nat × Laze S))))
  | [] => pure []
  | ((_, y), (_, n)) :: rest => do
    let o0y ← idS
    let o1y ← idS
    let o0n ← idS
    let o1n ← idS
    let (y0, y1) ← lazeBranch y
    let (n0, n1) ← lazeBranch n
    let r ← branchF rest
    pure ((((o0y, y0), (o0n, n0)), ((o1y, y1), (o1n, n1))) :: r)
def branchB : List (Nat × Laze S) → SM S (List ((Nat × Laze S) × (Nat × Laze S)))
  | [] => pure []
  | (_, l) :: rest => do
    let o0 ← idS
    let o1 ← idS
    let (l0, l1) ← lazeBranch l
    let r ← branchB rest
    pure (((o0, l0), (o1, l1)) :: r)
end

/-- **`+laze-sect`**. -/
def lazeSect (l0 l1 : Laze S) : SM S (Laze S) := do
  let o0 ← idS
  let o1 ← idS
  pure (mk SureO.bunt [((o0, l0), (o1, l1))] [])

/-- **`+laze-past`**. -/
def lazePast (env : ShapeEnv) (laz : Laze S) (nom : Nomm) : SM S (Laze S) :=
  if decide (laz.sure.ned = NeedOrd.none) && HoonSet.small laz.sure.lok && laz.fork.isEmpty then pure laz else do
  let h ← liftS (hinted env.pure nom)
  if !h then pure laz else do
  let i ← idS
  pure (mk SureO.bunt [] ((i, mk laz.sure laz.fork []) :: laz.bond))

/-- **`+laze-past-if`**. -/
def lazePastIf (env : ShapeEnv) (laz : Laze S) (nom : Nomm) : SM S (Laze S) := do
  let keep ← (if HoonSet.small laz.sure.lok then liftS (soundS env nom laz.sure.ned) else pure false : SM S Bool)
  if keep then pure laz else do
  let i ← idS
  pure (mk SureO.bunt laz.fork ((i, mk laz.sure [] []) :: laz.bond))

/-- **`+laze-past-fork`**. -/
def lazePastFork (env : ShapeEnv) (laz : Laze S) (nom : Nomm) : Option (Laze S) :=
  (hinted env.pure nom).map fun h => if !h then laz else
    mk laz.sure (laz.fork.map fun e => ((e.1.1, mk SureO.bunt [] [(e.1.1, e.1.2)]),
      (e.2.1, mk SureO.bunt [] [(e.2.1, e.2.2)]))) laz.bond

/-- The test of the soft branch of a direct call (lines 4466 to 4472). -/
def softTest (env : ShapeEnv) (p q : Nomm) (b : Bell) (k : Option Noun) (ned sur : NeedOrd)
    (sup : Option Nomm) : Option Bool :=
  match k with
  | some _ => some false
  | Option.none => (soundS env (made p sup) ned).bind fun s => if s then some false else
      orB (needSoft ned sur b.less) (orB (hinted env.pure p) (hinted env.pure q))

/-- `?^ (mean-konst b k)`. -/
def meanKonstS (env : ShapeEnv) (b : Bell) (k : Option Noun) : Option Bool :=
  match k with
  | Option.none => some false
  | some _ => env.pure b

/-! ## `+run-shape` -/

/-- The goal `simple` (what `+simple-next` does to the goal). -/
def simpleS : GoalS S → Laze S
  | GoalS.next l => l
  | _ => thisL

/-- The case `[^ *]` under `[%next laz]`. -/
def consNext (env : ShapeEnv) (rp rq : GoalS S → SM S (Laze S)) (p q : Nomm) (laz : Laze S) :
    SM S (Laze S) := do
  let (hed, tel) ← liftS (lazeSplit laz)
  let hed ← lazePast env hed q
  let l2 ← rq (GoalS.next tel)
  let l2 ← lazePast env l2 p
  let l1 ← rp (GoalS.next hed)
  liftS (lazeCopy l1 l2)

/-- The end of the case `%6`: the branches under `gb`, the test under
`%pick`. -/
def sixBranch (env : ShapeEnv) (rp rq rr : GoalS S → SM S (Laze S)) (p : Nomm) (gb : GoalS S) :
    SM S (Laze S) := do
  let l1 ← rr gb
  let l0 ← rq gb
  let lazy ← lazeSect l0 l1
  let lazy ← liftS (lazePastFork env lazy p)
  let st ← get
  let lazy := if lazeBig (sofsHas st.sofs) lazy then thisL else lazy
  let lc ← rp GoalS.pick
  liftS (lazeCopy lc lazy)

/-- The middle of the case `%6`: the branches under the halves of
`+laze-branch`, the test under `[%next this]`. -/
def sixFork (env : ShapeEnv) (rp rq rr : GoalS S → SM S (Laze S)) (p : Nomm) (laz : Laze S) :
    SM S (Laze S) := do
  let (g0, g1) ← lazeBranch laz
  let l1 ← rr (GoalS.next g1)
  let l0 ← rq (GoalS.next g0)
  let lazy ← lazeSect l0 l1
  let lazy ← liftS (lazePastFork env lazy p)
  let st ← get
  let lazy := if lazeBig (sofsHas st.sofs) lazy then thisL else lazy
  let lc ← rp (GoalS.next thisL)
  liftS (lazeCopy lc lazy)

/-- The case `%6` under `[%next laz]`, with fuel for its runs on the same
nomm. -/
def sixShape (env : ShapeEnv) (rp rq rr : GoalS S → SM S (Laze S)) (p q r : Nomm) :
    Nat → Laze S → SM S (Laze S)
  | 0, _ => fun _ => Option.none
  | fuel + 1, laz => do
    let lep ← liftS (lazeLeaps laz q r)
    match lep with
    | some (rest, bys) => do
      let l ← sixShape env rp rq rr p q r fuel rest
      liftS (bys.foldlM (fun acc by_ => lazeCopy acc by_) l)
    | Option.none =>
      if !(noneEq (mk SureO.bunt laz.fork laz.bond)) then do
        let st ← get
        let soft := sofsHas st.sofs
        let kerf ← (if (whole q && whole r) || thisOnlyS laz || lazeBig soft laz then pure true
          else liftS (softForkS soft (unsS env q r) laz) : SM S Bool)
        if kerf then sixShape env rp rq rr p q r fuel thisL
        else sixFork env rp rq rr p laz
      else sixBranch env rp rq rr p (GoalS.next (mk laz.sure [] []))

/-- The fuel of `sixShape`. -/
def sixFuel : Nat := 4

/-- **`+run-shape`** with `sup`. -/
def runShape (env : ShapeEnv) : Option Nomm → Nomm → GoalS S → SM S (Laze S)
  | sup, Nomm.cons p q, goal =>
    match goal with
    | GoalS.pick => do
      let l2 ← runShape env sup q (GoalS.next noneL)
      let l2 ← lazePast env l2 p
      let l1 ← runShape env sup p (GoalS.next noneL)
      liftS (lazeCopy l1 l2)
    | GoalS.done => consNext env (runShape env sup p) (runShape env sup q) p q thisL
    | GoalS.next laz => consNext env (runShape env sup p) (runShape env sup q) p q laz
  | _, Nomm.n0 ax, goal =>
    if ax = 0 then pure noneL else if ax = 1 then pure (simpleS goal) else liftS (lazeFrom ax (simpleS goal))
  | _, Nomm.n1 _, _ => pure noneL
  | sup, Nomm.n2 p q info, goal =>
    match info with
    | Option.none => do
      let lf ← runShape env sup q (GoalS.next thisL)
      let lf ← lazePast env lf p
      let ls ← runShape env sup p (GoalS.next thisL)
      liftS (lazeCopy ls lf)
    | some (b, k) => do
      let pu ← liftS (env.pure b)
      let drop := pu && (match goal with | GoalS.next l => noneEq l | _ => false)
      let lf ← (if safeFolFol q then pure noneL else runShape env sup q (GoalS.next noneL) : SM S (Laze S))
      let lf ← lazePast env lf p
      let ls ← (if drop then runShape env sup p (GoalS.next noneL) else do
        let ned ← (match k with
          | some (Noun.cell _ _) => pure NeedOrd.this
          | _ => liftS (env.need b) : SM S NeedOrd)
        let sur := if env.jet b then NeedOrd.none else env.sure b
        let soft ← liftS (softTest env p q b k ned sur sup)
        if !soft then runShape env sup p (GoalS.next (nedL ned)) else do
          let i ← idS
          putSofs i
          runShape env sup p (GoalS.next (mk SureO.bunt [] [(i, nedL ned)])) : SM S (Laze S))
      liftS (lazeCopy ls lf)
  | sup, Nomm.n3 p, goal =>
    match goal with
    | GoalS.next l => if noneEq l then runShape env sup p goal else runShape env sup p (GoalS.next thisL)
    | _ => runShape env sup p (GoalS.next thisL)
  | sup, Nomm.n4 p, _ => runShape env sup p (GoalS.next thisL)
  | sup, Nomm.n5 p q, _ => do
    let lq ← runShape env sup q (GoalS.next thisL)
    let lq ← lazePast env lq p
    let lp ← runShape env sup p (GoalS.next thisL)
    liftS (lazeCopy lp lq)
  | sup, Nomm.n6 p q r, goal =>
    match goal with
    | GoalS.next laz =>
      sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r sixFuel laz
    | g => sixBranch env (runShape env sup p) (runShape env sup q) (runShape env sup r) p g
  | sup, Nomm.n7 p q, goal => do
    let l ← runShape env (some p) q goal
    runShape env sup p (GoalS.next l)
  | sup, Nomm.n10 a v q, goal => do
    let (don, rec) ← liftS (lazeInto a (simpleS goal))
    let rec ← lazePast env rec v
    let lDon ← runShape env sup v (GoalS.next don)
    let lDon ← lazePast env lDon q
    let lRec ← runShape env sup q (GoalS.next rec)
    liftS (lazeCopy lRec lDon)
  | sup, Nomm.n11s tag q _, goal =>
    if !hintStatic tag then runShape env sup q goal else do
    let gol ← lazePastIf env (simpleS goal) q
    let lf ← runShape env sup q (GoalS.next gol)
    let i ← idS
    pure (mk SureO.bunt [] [(i, lf)])
  | sup, Nomm.n11d tag h q _, goal =>
    if !hintDynamic tag then do
      let lf ← runShape env sup q goal
      if safeNomm h then pure lf else do
      let lf ← lazePast env lf h
      let lt ← runShape env sup h (GoalS.next noneL)
      liftS (lazeCopy lt lf)
    else do
      let gol ← lazePastIf env (simpleS goal) q
      let lf ← runShape env sup q (GoalS.next gol)
      let i ← idS
      let lt ← runShape env sup h (GoalS.next thisL)
      liftS (lazeCopy lt (mk SureO.bunt [] [(i, lf)]))
  | sup, Nomm.mean p b q _ k, goal => do
    let gol ← lazePastIf env (simpleS goal) q
    let lf ← runShape env sup q (GoalS.next gol)
    let i ← idS
    let kon ← liftS (meanKonstS env b k)
    let ned ← (if kon then pure NeedOrd.none else liftS (env.need b) : SM S NeedOrd)
    let snd ← liftS (soundS env p ned)
    let la ← (if snd then pure (nedL ned) else do
      let j ← idS
      putSofs j
      pure (mk SureO.bunt [] [(j, nedL ned)]) : SM S (Laze S))
    let lt ← runShape env sup p (GoalS.next la)
    liftS (lazeCopy lt (mk SureO.bunt [] [(i, lf)]))
  | sup, Nomm.n12 p q, _ => do
    let lq ← runShape env sup q (GoalS.next thisL)
    let lq ← lazePast env lq p
    let lp ← runShape env sup p (GoalS.next thisL)
    liftS (lazeCopy lp lq)

/-! ## `+laze-to-inter1`, `+laze-collapse`, `+laze-may` -/

mutual
/-- **`+laze-to-inter1`**: `l2i` of `ShapeCol.lean` on a `laze` (the sure
need is ordered already). -/
def lazeToI1 : Laze S → I1 S
  | mk s f b => lazeToI1B b s.ned s.lok (lazeToI1F f)
def lazeToI1F : List ((Nat × Laze S) × (Nat × Laze S)) → List (I1 S × I1 S)
  | [] => []
  | ((_, y), (_, n)) :: r => (lazeToI1 y, lazeToI1 n) :: lazeToI1F r
def lazeToI1B : List (Nat × Laze S) → NeedOrd → S → List (I1 S × I1 S) → I1 S
  | [], ned, lok, fk => I1.mk ned lok fk
  | (_, i) :: r, ned, lok, fk =>
    lazeToI1B r (uniOrd (lazeToI1 i).ned ned) (HoonSet.uni lok (lazeToI1 i).lok) ((lazeToI1 i).fork ++ fk)
end

/-- **`+laze-collapse`** with fuel for the fixed point of
`+inter2-collapse`. -/
def lazeCollapse (fuel : Nat) (laz : Laze S) (less : Cape) : Option NeedOrd :=
  (i12 less (lazeToI1 laz)).bind fun intr => inter2Collapse fuel intr less

mutual
/-- The trap of `+laze-may`: the `+roll` over the forks from the sure need. -/
def mayGo : I2 → NeedOrd
  | I2.mk s f => mayF f s
def mayF : List (I2 × I2) → NeedOrd → NeedOrd
  | [], acc => acc
  | (y, n) :: r, acc => mayF r (uniOrd (uniOrd acc (mayGo y)) (mayGo n))
end

/-- **`+laze-may`**. -/
def lazeMay (laz : Laze S) (less : Cape) : Option NeedOrd :=
  (i12 less (lazeToI1 laz)).map mayGo

end Comp
end SkaModel
end Formalization
