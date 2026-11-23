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

/-! ## Commands that define the generated nouns

The files `lemmas/Pill/Cue/Win.lean` and `J*.lean` are one command each, so
that the elaborator does not parse and elaborate millions of characters of
terms: the command reads the bits of the pill and builds the definitions
itself.  The kernel checks each definition as usual. -/

/-- Add a definition whose body importers see, and which is not compiled. -/
meta def addPublicDef (nm : Name) (type value : Expr) : CoreM Unit := do
  let value := ShareCommon.shareCommon' value
  let h := getMaxHeight (← getEnv) value + 1
  addDecl (.defnDecl (mkDefinitionValEx nm [] type value (.regular h) .safe [nm]))
    (forceExpose := true)
  modifyEnv (addNoncomputable · nm)

meta def cueName (s : String) : Name := cueNs ++ Name.mkSimple s

/-- `cue_windows n`: the windows `W<k>` and the theorems `win<k>` for
`k < n`. -/
elab "cue_windows " n:num : command => Command.liftTermElabM do
  let some info := (← getEnv).find? `Formalization.Pill.Cue.pillList
    | throwError "cue_windows: no pillList"
  let some v := info.value? (allowOpaque := true) | throwError "cue_windows: no value"
  let xs ← listElems v
  let mut cs : Array Nat := #[]
  for x in xs do
    let some c := natLit? x | throwError "cue_windows: a chunk is not a literal"
    cs := cs.push c
  let nat := mkConst ``Nat
  for k in [0:n.getNat] do
    let w := cs.getD k 0 + 2 ^ 8192 * cs.getD (k + 1) 0
    let W := cueName s!"W{k}"
    addPublicDef W nat (mkRawNatLit w)
    let ty := mkApp3 (mkConst ``WinOK) (mkConst ``Formalization.pill) (mkConst W)
      (mkRawNatLit (8192 * k))
    let pf := mkApp3 (mkConst `Formalization.Pill.Cue.winOK_pill) (mkRawNatLit k) (mkConst W)
      (mkApp2 (mkConst ``Eq.refl [Level.one]) nat (mkConst W))
    addDecl (.thmDecl { name := cueName s!"win{k}", levelParams := [], type := ty, value := pf })

/-- Fields of `bits` wide, packed into one number. -/
meta def unpack (n width count : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:count] do
    out := out.push ((n >>> (width * i)) % 2 ^ width)
  return out

meta def pack (xs : Array Nat) (width : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [0:xs.size] do
    n := n + xs[i]! * 2 ^ (width * i)
  return n

meta def litOf (nm : Name) : MetaM Nat := do
  let some info := (← getEnv).find? nm | throwError "cue_nouns: no {nm}"
  let some v := info.value? (allowOpaque := true) | throwError "cue_nouns: {nm} has no value"
  let some n := natLit? v | throwError "cue_nouns: {nm} is not a literal"
  return n

structure NounSt where
  wins : Std.HashMap Nat Nat := {}
  /-- the entry of the table that starts at a bit -/
  key : Std.HashMap Nat Nat := {}
  /-- the end of each named noun, by its start -/
  ends : Std.HashMap Nat Nat := {}
  /-- the nouns named only to keep terms small, by their start -/
  aux : Std.HashSet Nat := {}

abbrev NounM := StateT NounSt MetaM

meta def windowN (k : Nat) : NounM Nat := do
  if let some w := (← get).wins[k]? then return w
  let w ← litOf (cueName s!"W{k}")
  modify fun st => { st with wins := st.wins.insert k w }
  return w

meta def tokenN (b : Nat) : NounM Tok := do
  let k := b / 8192
  let w ← windowN k
  let d := b - 8192 * k
  if bitsM w d 1 == 0 then
    let some (z, p, x) := matM w (d + 1) | throwError "cue_nouns: bad atom at {b}"
    return .atom z p x
  else if bitsM w (d + 1) 1 == 0 then return .cell
  else
    let some (z, p, q) := matM w (d + 2) | throwError "cue_nouns: bad reference at {b}"
    return .ref z p q

meta def mkAR (x : Nat) : Expr := mkApp (mkConst ``Formalization.Nock.A) (mkRawNatLit x)

/-- The term of the noun at bit `b`, with the named nouns below it by name,
and its end. -/
meta partial def nounAt (b : Nat) (top : Bool) : NounM (Expr × Nat) := do
  let st ← get
  unless top do
    if let some e := st.ends[b]? then
      if let some j := st.key[b]? then return (mkConst (cueName s!"k{j}"), e)
      if st.aux.contains b then return (mkConst (cueName s!"s{b}"), e)
  match ← tokenN b with
  | .atom _ p x => return (mkAR x, b + 1 + p)
  | .ref _ p q =>
    let some j := st.key[q]? | throwError "cue_nouns: a reference at {b} to {q}, not an entry"
    return (mkConst (cueName s!"k{j}"), b + 2 + p)
  | .cell =>
    let (h, e₁) ← nounAt (b + 2) false
    let (t, e₂) ← nounAt e₁ false
    return (mkC h t, e₂)

/-- The part of the table for the entries `lo + a` to `lo + b - 1`, as a
definition named `nm`.  A range of more than 16 entries is split in two
definitions, so that the kernel, which instantiates the whole body of a
definition when it applies it, only ever instantiates a small one. -/
meta partial def kvDef (nm : Name) (lo : Nat) (items : Array (Nat × Name)) (a b : Nat) :
    CoreM Unit := do
  let nat := mkConst ``Nat
  let noun := mkConst ``Formalization.Nock.Noun
  let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) nat noun
  let leaf (i : Nat) : Expr :=
    let (q, k) := items[i]!
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) nat noun (mkRawNatLit q) (mkConst k)
  let pick (m : Nat) (r l : Expr) : Expr :=
    mkApp4 (mkConst ``cond [Level.one]) ty
      (mkApp2 (mkConst ``Nat.ble) (mkRawNatLit (lo + m)) (.bvar 0)) r l
  let rec inline (a b : Nat) (fuel : Nat) : Expr :=
    match fuel with
    | 0 => leaf a
    | fuel + 1 => if b - a ≤ 1 then leaf a else
        let m := (a + b) / 2
        pick m (inline m b fuel) (inline a m fuel)
  let body ← if b - a ≤ 16 then pure (inline a b 64) else do
    let m := (a + b) / 2
    let nl := nm.appendAfter "l"
    let nr := nm.appendAfter "r"
    kvDef nl lo items a m
    kvDef nr lo items m b
    pure (pick m (mkApp (mkConst nr) (.bvar 0)) (mkApp (mkConst nl) (.bvar 0)))
  addPublicDef nm (mkForall `j .default nat ty) (.lam `j nat body .default)

/-- `cue_nouns f lo "k80 s95 ..."`: the named nouns of the chain file `f`, in
the order of the list (`k` for an entry of the table, numbered from `lo` in
that order, `s` for a noun named only to keep terms small, each by the bit
where it starts); then `KV<f>`, the part of the table for these entries, and
`JI<f>`, `JK<f>`, `JN<f>`, which record the starts and ends of the nouns for
the next files. -/
elab "cue_nouns " f:num lo:num spec:str : command => Command.liftTermElabM do
  let f := f.getNat
  let lo := lo.getNat
  let mut st : NounSt := {}
  -- what the files before this one named
  for g in [0:f] do
    let n ← litOf (cueName s!"JN{g}")
    let info := unpack (← litOf (cueName s!"JI{g}")) 24 (3 * n)
    for i in [0:n] do
      let b := info[3 * i]!
      st := { st with ends := st.ends.insert b info[3 * i + 1]! }
      let j := info[3 * i + 2]!
      if j == 0 then st := { st with aux := st.aux.insert b }
      else st := { st with key := st.key.insert b (j - 1) }
  let noun := mkConst ``Formalization.Nock.Noun
  let mut j := lo
  let mut items : Array (Nat × Name) := #[]
  let mut infos : Array Nat := #[]
  for item in (spec.getString.replace "\n" " ").splitOn " " do
    if item.isEmpty then continue
    let keyed := item.startsWith "k"
    let some b := (item.drop 1).toNat? | throwError "cue_nouns: bad item {item}"
    let ((v, e), st') ← (nounAt b true).run st
    st := st'
    let nm := if keyed then cueName s!"k{j}" else cueName s!"s{b}"
    addPublicDef nm noun v
    st := { st with ends := st.ends.insert b e }
    if keyed then
      st := { st with key := st.key.insert b j }
      items := items.push (b, nm)
      infos := infos ++ #[b, e, j + 1]
      j := j + 1
    else
      st := { st with aux := st.aux.insert b }
      infos := infos ++ #[b, e, 0]
  let nat := mkConst ``Nat
  if !items.isEmpty then
    kvDef (cueName s!"KV{f}") lo items 0 items.size
  addPublicDef (cueName s!"JN{f}") nat (mkRawNatLit (infos.size / 3))
  addPublicDef (cueName s!"JI{f}") nat (mkRawNatLit (pack infos 24))

end CueRel
end Nock
end Formalization
