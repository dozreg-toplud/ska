module

public import Lean
public import lemmas.CueRel
/-!
# The tactic `cue_dec`

The generated files of `lemmas/Pill/Cue/` prove statements
`Dec pill KV b n e i i'` (`lemmas/CueRel.lean`), one for each piece of the
pill, with the proof `by cue_dec`.  The tactic builds the derivation from the
bits of the pill and from the noun `n`, and leaves every check to the kernel:
the elaborator does not evaluate anything.

It reads the bits through the windows `Formalization.Pill.Cue.W<k>`, which
hold the bits `8192 * k` to `8192 * k + 16384` of the pill
(`Formalization.Pill.Cue.win<k>` says so), and it walks `n` along the tokens of
the jam:

* a name `Formalization.Pill.Cue.k<j>` is the entry `j` of the table `KV`: a
  reference to it, or its first encoding, after which the count moves past it;
* a name `Formalization.Pill.Cue.s<b>` is a noun of the pill that is not
  referred to back, given a name to keep the terms small;
* `C h t` and `A x` are a cell and an atom that are not referred to back.

When the tactic reaches, below the top, the bit `b` of a noun for which a
theorem `Formalization.Pill.Cue.d<b>` exists, it uses that theorem instead of
walking the noun.  The generator makes those theorems in an order where each
one comes after the ones it uses.
-/

public section

namespace Formalization
namespace Nock
namespace CueRel

open Lean Meta Elab Tactic

/-- The number a literal stands for. -/
meta def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg!.consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- The bits `i` to `i + n` of `w`. -/
meta def bitsM (w i n : Nat) : Nat := (w >>> i) % 2 ^ n

/-- The length-prefixed atom at bit `s` of `w`: its leading zeros, its
length in bits and its value. -/
meta def matM (w s : Nat) : Option (Nat × Nat × Nat) := Id.run do
  let mut z := 0
  while bitsM w (s + z) 1 == 0 do
    z := z + 1
    if z > 64 then return none
  if z == 0 then return some (0, 1, 0)
  let len := 2 ^ (z - 1) + bitsM w (s + z + 1) (z - 1)
  return some (z, 2 * z + len, bitsM w (s + 2 * z) len)

/-- What a jam holds at a bit. -/
inductive Tok where
  | atom (z p x : Nat)
  | cell
  | ref (z p q : Nat)

structure CueCtx where
  a : Expr
  kv : Expr
  top : Nat
  wins : IO.Ref (Std.HashMap Nat Nat)

abbrev CueM := ReaderT CueCtx MetaM

meta def cueNs : Name := `Formalization.Pill.Cue

meta def window (k : Nat) : CueM Nat := do
  let ctx ← read
  if let some w := (← ctx.wins.get)[k]? then return w
  let nm := cueNs ++ Name.mkSimple s!"W{k}"
  let some info := (← getEnv).find? nm | throwError "cue_dec: no window {nm}"
  let some v := info.value? (allowOpaque := true) | throwError "cue_dec: {nm} has no value"
  let some w := natLit? v | throwError "cue_dec: {nm} is not a literal"
  ctx.wins.modify (·.insert k w)
  return w

meta def token (b : Nat) : CueM Tok := do
  let k := b / 8192
  let w ← window k
  let d := b - 8192 * k
  if bitsM w d 1 == 0 then
    let some (z, p, x) := matM w (d + 1) | throwError "cue_dec: bad atom at {b}"
    return .atom z p x
  else if bitsM w (d + 1) 1 == 0 then return .cell
  else
    let some (z, p, q) := matM w (d + 2) | throwError "cue_dec: bad reference at {b}"
    return .ref z p q

/-- The name of a generated noun, as `(true, j)` for the entry `j` of the
table and `(false, b)` for a noun with a name only. -/
meta def cueName? (e : Expr) : Option (Bool × Nat) := do
  let .const nm _ := e.consumeMData | none
  let .str p s := nm | none
  guard (p == cueNs)
  if s.startsWith "k" then (s.drop 1).toNat?.map (true, ·)
  else if s.startsWith "s" then (s.drop 1).toNat?.map (false, ·)
  else none

meta def bodyOf (e : Expr) : MetaM Expr := do
  let .const nm _ := e.consumeMData | throwError "cue_dec: not a name {e}"
  let some info := (← getEnv).find? nm | throwError "cue_dec: unknown {nm}"
  let some v := info.value? (allowOpaque := true) | throwError "cue_dec: {nm} has no value"
  return v.consumeMData

meta def cellParts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Formalization.Nock.C 2 || e.isAppOfArity ``Formalization.Nock.Noun.cell 2 then
    some (e.appFn!.appArg!, e.appArg!)
  else none

meta def atomVal? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if e.isAppOfArity ``Formalization.Nock.A 1 || e.isAppOfArity ``Formalization.Nock.Noun.atom 1 then
    natLit? e.appArg!
  else none

meta def lit (n : Nat) : Expr := mkRawNatLit n

meta def trueRfl : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def pairRfl (q : Nat) (n : Expr) : Expr :=
  let nat := mkConst ``Nat
  let noun := mkConst ``Formalization.Nock.Noun
  let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) nat noun
  mkApp2 (mkConst ``Eq.refl [Level.one]) ty
    (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) nat noun (lit q) n)

meta def winOf (b : Nat) : Expr × Expr × Nat :=
  let k := b / 8192
  (mkConst (cueNs ++ Name.mkSimple s!"W{k}"), mkConst (cueNs ++ Name.mkSimple s!"win{k}"), 8192 * k)

meta def mkC (h t : Expr) : Expr := mkApp2 (mkConst ``Formalization.Nock.C) h t
meta def mkA (x : Nat) : Expr := mkApp (mkConst ``Formalization.Nock.A) (lit x)

/-- The derivation for the noun `exp` at bit `b` with count `i`: the proof,
the end bit and the count at the end. -/
meta partial def go (b i : Nat) (exp : Expr) : CueM (Expr × Nat × Nat) := do
  let ctx ← read
  -- a theorem for this bit
  if b != ctx.top then
    let dn := cueNs ++ Name.mkSimple s!"d{b}"
    if let some info := (← getEnv).find? dn then
      let ty := info.type
      let args := ty.getAppArgs
      unless ty.isAppOfArity ``Dec 7 do throwError "cue_dec: {dn} is not about Dec"
      let some b' := natLit? args[2]! | throwError "cue_dec: {dn}: start"
      let some e' := natLit? args[4]! | throwError "cue_dec: {dn}: end"
      let some i₀ := natLit? args[5]! | throwError "cue_dec: {dn}: count"
      let some i₁ := natLit? args[6]! | throwError "cue_dec: {dn}: count"
      unless b' == b && i₀ == i do
        throwError "cue_dec: {dn} starts at {b'} with count {i₀}, wanted {b} and {i}"
      return (mkConst dn, e', i₁)
  let (W, hW, o) := winOf b
  let tok ← token b
  let named := cueName? exp
  match tok, named with
  | .ref z p q, some (true, j) =>
    let e := b + 2 + p
    let pf := mkAppN (mkConst ``tokR) #[ctx.a, ctx.kv, W, lit o, lit b,
      lit z, lit p, lit q, lit e, lit j, lit i, exp, hW, trueRfl, pairRfl q exp]
    return (pf, e, i)
  | .ref _ _ _, _ => throwError "cue_dec: a reference at {b}, but the noun is {exp}"
  | .atom z p x, some (true, j) =>
    unless j == i do throwError "cue_dec: entry {j} at {b}, but the count is {i}"
    let e := b + 1 + p
    let pf := mkAppN (mkConst ``tokAK) #[ctx.a, ctx.kv, W, lit o, lit b, lit z, lit p, lit x,
      lit e, lit i, lit (i + 1), hW, trueRfl, pairRfl b (mkA x)]
    return (pf, e, i + 1)
  | .atom z p x, none =>
    match atomVal? exp with
    | some x' =>
      unless x' == x do throwError "cue_dec: atom {x} at {b}, but the noun is {x'}"
      let e := b + 1 + p
      let pf := mkAppN (mkConst ``tokA) #[ctx.a, ctx.kv, W, lit o, lit b, lit z, lit p, lit x,
        lit e, lit i, hW, trueRfl]
      return (pf, e, i)
    | none => throwError "cue_dec: atom at {b}, but the noun is {exp}"
  | .atom _ _ _, some (false, _) => throwError "cue_dec: atom at {b}, but the noun is {exp}"
  | .cell, _ =>
    let (keyed, body) ← match named with
      | some (true, j) => pure (some j, ← bodyOf exp)
      | some (false, _) => pure (none, ← bodyOf exp)
      | none => pure (none, exp)
    let some (h, t) := cellParts? body | throwError "cue_dec: cell at {b}, but the noun is {body}"
    let (p₁, e₁, i₁) ← go (b + 2) i h
    let (p₂, e₂, i₂) ← go e₁ i₁ t
    match keyed with
    | none =>
      let pf := mkAppN (mkConst ``tokC) #[ctx.a, ctx.kv, W, lit o, lit b, lit (b + 2), lit e₁,
        lit e₂, lit i, lit i₁, lit i₂, h, t, hW, trueRfl, p₁, p₂]
      return (pf, e₂, i₂)
    | some j =>
      unless j == i₂ do throwError "cue_dec: entry {j} ends at {e₂}, but the count is {i₂}"
      let pf := mkAppN (mkConst ``tokCK) #[ctx.a, ctx.kv, W, lit o, lit b, lit (b + 2), lit e₁,
        lit e₂, lit i, lit i₁, lit i₂, lit (i₂ + 1), h, t, hW, trueRfl, p₁, p₂,
        pairRfl b (mkC h t)]
      return (pf, e₂, i₂ + 1)

/-- Prove `Dec a KV b n e i i'` from the bits of the windows, leaving every
check to the kernel. -/
elab "cue_dec" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``Dec 7 do throwError "cue_dec: the goal is not about Dec"
  let args := ty.getAppArgs
  let some b := natLit? args[2]! | throwError "cue_dec: the start is not a literal"
  let some e := natLit? args[4]! | throwError "cue_dec: the end is not a literal"
  let some i := natLit? args[5]! | throwError "cue_dec: the count is not a literal"
  let some i' := natLit? args[6]! | throwError "cue_dec: the count is not a literal"
  let wins ← IO.mkRef {}
  let (pf, e₁, i₁) ← (go b i args[3]!).run { a := args[0]!, kv := args[1]!, top := b, wins }
  unless e₁ == e && i₁ == i' do
    throwError "cue_dec: the derivation ends at {e₁} with count {i₁}, not {e} and {i'}"
  goal.assign pf

/-- The list of chunks that `Formalization.pill` glues, as its definition
writes it. -/
elab "pill_list%" : term => do
  let some info := (← getEnv).find? ``Formalization.pill | throwError "pill_list%: no pill"
  let some v := info.value? (allowOpaque := true) | throwError "pill_list%: pill has no value"
  let v := v.consumeMData
  unless v.isAppOfArity ``Formalization.glue 1 do throwError "pill_list%: pill is not a glue"
  return v.appArg!

meta partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e := e.consumeMData.headBeta
  if let .letE _ _ v b _ := e then return ← listElems (b.instantiate1 v)
  if e.isAppOfArity ``List.cons 3 then
    return #[e.appFn!.appArg!] ++ (← listElems e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then return #[]
  else throwError "listElems: not a list literal"

/-- The window `k`: chunks `k` and `k + 1` of the pill, as one literal. -/
elab "win% " k:num : term => do
  let k := k.getNat
  let some info := (← getEnv).find? `Formalization.Pill.Cue.pillList | throwError "win%: no pillList"
  let some v := info.value? (allowOpaque := true) | throwError "win%: pillList has no value"
  let xs ← listElems v
  let get (i : Nat) : MetaM Nat := do
    if h : i < xs.size then
      match natLit? xs[i] with
      | some n => pure n
      | none => throwError "win%: chunk {i} is not a literal"
    else pure 0
  return mkRawNatLit ((← get k) + 2 ^ 8192 * (← get (k + 1)))

end CueRel
end Nock
end Formalization
