import lemmas.Compiler.CompSureOf

/-!
# A model of `+shape-collapse` on lazy needs with forks

```hoon
++  shape-collapse
  |=  [laz=need-lazy less=cape]
  ^-  need-ordered
  (inter2-collapse (inter1-to-inter2 (lazy-to-inter1 laz) less) less)
```

The `ord` of the final pass of `+compile-scc-in` (`+collapse-shape`,
`need-ord-alloc-regs (shape-collapse laz.nex less)`).  The Hoon, arm by arm,
and the function of the model that stands for it:

* `+uni-need-ord` (`uniOrd`), `+msg-need-ord` (`msgOrd`, with `msgNone` for
  its calls `(msg none+~ h-double ..)`), `+need-ord-regs` (`ordRegs`),
  `+msg-need-ord-fix-aware` (`msgFix`), `+hed-need-ord`, `+tel-need-ord`
  (`ordHed`, `ordTel`), `hed:ca`, `tel:ca` (`capeHed`, `capeTel`);
* `$need-inter1`, `$need-inter2`: `I1 S`, `I2`;
* `+lazy-to-inter1` (`l2i`, `l2iForks`, `l2iBonds`): the sure need made
  ordered, each fork's branches converted, then a `+roll` over the bonds
  that unites each bond's sure need into the sure need (`uniOrd` of the
  bond's first), its looks into the looks, and puts its forks before the
  forks so far.  The Hoon's first test (no fork and no bond: `[[ned lok] ~]`)
  gives what the roll gives on no bond, so the model has no such case;
* `+inter1-to-inter2` (`i12`): `+sure-of`'s fold at every node
  (`sureOfS`, the fold of `sureOfStep` over the looks in the order of the
  set's `toList`), its crash on a look at `0` as `none`;
* `+inter2-fix-round` (`fixRound`, `fixKids`, `rollMsg`): the parent's shape
  (`uniOrd` of the parent's and the node's sure) pushed down to the kids,
  then the `+roll` over the new kids of the `msgOrd` of their two sures,
  from that shape;
* the fixed point of `+inter2-collapse` (`fixLoop`): rounds from `intr`
  with the parent `[%none ~]` until a round gives its input back (the
  test `=(new fix)` on nouns, `I2.toNoun`); the model has fuel, `none`
  when it runs out;
* `+inter2-orig` (`orig`, `origLoop`): from `sure.intr`, for each fork and
  the fork of `fix` at the same place, `uniOrd` of the accumulator and
  `msgFix` of the two branches' results with the sure of `fix` at this
  node; the `?>  ?=(^ fixes)` is a `none`;
* the `!@  collapse-check` of `+inter2-collapse` takes `res`: the wing is
  commented out (the check against `+inter2-collapse-nested` does not run);
* `shapeCol fuel laz less`: the whole arm.

On a fork-free, bond-free lazy need it is `+sure-of` of the sure part
(`shapeCol_ofSure`), which is what the model used so far (`sccSur`).  The
`#guard`s at the end check it on the dumps of `tools/hoon/shapecoldump.hoon`.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

variable {S : Type} [HoonSet S]

/-! ## Shapes -/

/-- `+hed-need-ord`. -/
def ordHed : NeedOrd → NeedOrd
  | NeedOrd.both h _ => h
  | NeedOrd.pair p _ => p
  | _ => NeedOrd.none

/-- `+tel-need-ord`. -/
def ordTel : NeedOrd → NeedOrd
  | NeedOrd.both _ t => t
  | NeedOrd.pair _ q => q
  | _ => NeedOrd.none

/-- `hed:ca`. -/
def capeHed : Cape → Cape
  | Cape.cell h _ => h
  | c => c

/-- `tel:ca`. -/
def capeTel : Cape → Cape
  | Cape.cell _ t => t
  | c => c

/-- The end of the `%both` case of `+uni-need-ord`: `[%this ~]` when
`+cons-need` of the halves is `[%none ~]`, else a `%both` of them. -/
def uniBoth (x y : NeedOrd) : NeedOrd :=
  match consOrd x y with
  | NeedOrd.pair p q => NeedOrd.both p q
  | _ => NeedOrd.this

/-- **`+uni-need-ord`**. -/
def uniOrd (a b : NeedOrd) : NeedOrd :=
  if a = b then a else
  match a, b with
  | NeedOrd.none, b => b
  | a, NeedOrd.none => a
  | NeedOrd.this, NeedOrd.both h t => NeedOrd.both h t
  | NeedOrd.this, NeedOrd.pair p q => NeedOrd.both p q
  | NeedOrd.this, NeedOrd.this => NeedOrd.this
  | NeedOrd.both h t, NeedOrd.this => NeedOrd.both h t
  | NeedOrd.pair p q, NeedOrd.this => NeedOrd.both p q
  | NeedOrd.pair p q, NeedOrd.pair p' q' => consOrd (uniOrd p p') (uniOrd q q')
  | NeedOrd.pair p q, NeedOrd.both h t => uniBoth (uniOrd p h) (uniOrd q t)
  | NeedOrd.both h t, NeedOrd.pair p q => uniBoth (uniOrd h p) (uniOrd t q)
  | NeedOrd.both h t, NeedOrd.both h' t' => uniBoth (uniOrd h h') (uniOrd t t')

/-- **`+need-ord-regs`** from the accumulator `acc`: the registers of a
shape, counted until there are more than `max`. -/
def ordRegs (max : Nat) : NeedOrd → Nat → Nat
  | n, acc => if acc > max then acc else
    match n with
    | NeedOrd.none => acc
    | NeedOrd.this => acc + 1
    | NeedOrd.both h t => ordRegs max t (ordRegs max h (acc + 1))
    | NeedOrd.pair p q => ordRegs max q (ordRegs max p acc)

/-- `+split-max`. -/
def splitMax : Nat := 6

/-- The end of the case of `+msg-need-ord` where one side is `%this` or
`%none` and `less` is a cell: `[%this ~]` when the split has more than
`split-max` registers. -/
def msgCap (res : NeedOrd) : NeedOrd :=
  if ordRegs splitMax res 0 > splitMax then NeedOrd.this else res

/-- **`(msg-need-ord [%none ~] d less)`**. -/
def msgNone : NeedOrd → Cape → NeedOrd
  | NeedOrd.none, _ => NeedOrd.none
  | NeedOrd.this, _ => NeedOrd.this
  | NeedOrd.pair p q, Cape.cell lh lt => msgCap (consOrd (msgNone p lh) (msgNone q lt))
  | NeedOrd.both h t, Cape.cell lh lt => msgCap (NeedOrd.both (msgNone h lh) (msgNone t lt))
  | _, _ => NeedOrd.this

/-- The case of `+msg-need-ord` where `s` (`single`) is `%this` or `%none`
and `d` (`double`) is a cell or a `%both`. -/
def msgOne (s d : NeedOrd) (less : Cape) : NeedOrd :=
  match less with
  | Cape.cell lh lt =>
    let l := msgNone (ordHed d) lh
    let r := msgNone (ordTel d) lt
    let both := match d with | NeedOrd.both _ _ => true | _ => false
    msgCap (if s = NeedOrd.this || both then NeedOrd.both l r else consOrd l r)
  | _ => NeedOrd.this

/-- **`+msg-need-ord`**. -/
def msgOrd (a b : NeedOrd) (less : Cape) : NeedOrd :=
  if a = b then a else
  match a, b with
  | NeedOrd.this, NeedOrd.this => NeedOrd.this
  | NeedOrd.this, NeedOrd.none => NeedOrd.this
  | NeedOrd.none, NeedOrd.this => NeedOrd.this
  | NeedOrd.none, NeedOrd.none => NeedOrd.none
  | NeedOrd.this, d => msgOne NeedOrd.this d less
  | NeedOrd.none, d => msgOne NeedOrd.none d less
  | d, NeedOrd.this => msgOne NeedOrd.this d less
  | d, NeedOrd.none => msgOne NeedOrd.none d less
  | NeedOrd.both h t, NeedOrd.both h' t' =>
    NeedOrd.both (msgOrd h h' (capeHed less)) (msgOrd t t' (capeTel less))
  | NeedOrd.both h t, NeedOrd.pair p q =>
    NeedOrd.both (msgOrd h p (capeHed less)) (msgOrd t q (capeTel less))
  | NeedOrd.pair p q, NeedOrd.both h t =>
    NeedOrd.both (msgOrd p h (capeHed less)) (msgOrd q t (capeTel less))
  | NeedOrd.pair p q, NeedOrd.pair p' q' =>
    consOrd (msgOrd p p' (capeHed less)) (msgOrd q q' (capeTel less))

/-- Whether a shape is `%this` or `%both` (a part of `need-here`). -/
def ordWhole : NeedOrd → Bool
  | NeedOrd.this => true
  | NeedOrd.both _ _ => true
  | _ => false

/-- The end of `+msg-need-ord-fix-aware` given the `+cons-need` `x` of the
halves. -/
def fixEnd (here : Bool) (x : NeedOrd) : NeedOrd :=
  match x with
  | NeedOrd.pair p q => if here then NeedOrd.both p q else x
  | _ => if here then NeedOrd.this else NeedOrd.none

/-- **`+msg-need-ord-fix-aware`**: the MSG of `a` and `b` knowing that the
axes of `fix` exist. -/
def msgFix (a b fix : NeedOrd) (less : Cape) : NeedOrd :=
  if a = b then a else
  match fix with
  | NeedOrd.this => msgOrd a b less
  | NeedOrd.none => msgOrd a b less
  | NeedOrd.pair fh ft =>
    if a = NeedOrd.none ∧ b = NeedOrd.pair fh ft then b else
    if b = NeedOrd.none ∧ a = NeedOrd.pair fh ft then a else
    fixEnd (ordWhole a || ordWhole b)
      (consOrd (msgFix (ordHed a) (ordHed b) fh (capeHed less))
        (msgFix (ordTel a) (ordTel b) ft (capeTel less)))
  | NeedOrd.both fh ft =>
    if a = NeedOrd.none ∧ b = NeedOrd.both fh ft then b else
    if b = NeedOrd.none ∧ a = NeedOrd.both fh ft then a else
    fixEnd (ordWhole a || ordWhole b)
      (consOrd (msgFix (ordHed a) (ordHed b) fh (capeHed less))
        (msgFix (ordTel a) (ordTel b) ft (capeTel less)))

/-! ## The intermediate needs -/

/-- `$need-inter1`: a sure need with its looks, and forks. -/
inductive I1 (S : Type) where
  | mk (ned : NeedOrd) (lok : S) (fork : List (I1 S × I1 S))

/-- `$need-inter2`: a shape, and forks. -/
inductive I2 where
  | mk (sure : NeedOrd) (fork : List (I2 × I2))

namespace I1
def ned : I1 S → NeedOrd | mk n _ _ => n
def lok : I1 S → S | mk _ l _ => l
def fork : I1 S → List (I1 S × I1 S) | mk _ _ f => f
end I1

namespace I2
def sure : I2 → NeedOrd | mk s _ => s
def fork : I2 → List (I2 × I2) | mk _ f => f

mutual
/-- The noun of a `need-inter2`. -/
def toNoun : I2 → Noun
  | mk s f => C s.toNoun (forksNoun f)
/-- The noun of its forks. -/
def forksNoun : List (I2 × I2) → Noun
  | [] => A 0
  | (y, n) :: r => C (C (toNoun y) (toNoun n)) (forksNoun r)
end
end I2

/-! ## `+lazy-to-inter1` -/

mutual
/-- **`+lazy-to-inter1`**. -/
def l2i : Lazy S → I1 S
  | Lazy.mk s f b => l2iBonds b (needToOrd s.ned) s.lok (l2iForks f)
/-- Its `+turn` over the forks. -/
def l2iForks : List ((Nat × Lazy S) × (Nat × Lazy S)) → List (I1 S × I1 S)
  | [] => []
  | ((_, y), (_, n)) :: r => (l2i y, l2i n) :: l2iForks r
/-- Its `+roll` over the bonds. -/
def l2iBonds : List (Nat × Lazy S) → NeedOrd → S → List (I1 S × I1 S) → I1 S
  | [], ned, lok, fk => I1.mk ned lok fk
  | (_, i) :: r, ned, lok, fk =>
    l2iBonds r (uniOrd (l2i i).ned ned) (HoonSet.uni lok (l2i i).lok) ((l2i i).fork ++ fk)
end

/-! ## `+inter1-to-inter2` -/

/-- The gate of the `+rep:in` of `+inter1-to-inter2` (`sureOfStep`). -/
def sureStepS (less : Cape) (new : NeedOrd) (axe : Nat) : Option NeedOrd :=
  if axe = 1 then some new else
  (axeInLessCape axe less).map fun inLess => if inLess then new else sureLook axe new

/-- **`+sure-of`** over any set: the fold of `sureStepS` over the looks. -/
def sureOfS (ned : NeedOrd) (lok : S) (less : Cape) : Option NeedOrd :=
  (HoonSet.toList lok).foldlM (fun new axe => sureStepS less new axe) ned

mutual
/-- **`+inter1-to-inter2`**. -/
def i12 (less : Cape) : I1 S → Option I2
  | I1.mk ned lok fk => (sureOfS ned lok less).bind fun s => (i12Forks less fk).map fun f => I2.mk s f
/-- Its `+turn` over the forks. -/
def i12Forks (less : Cape) : List (I1 S × I1 S) → Option (List (I2 × I2))
  | [] => some []
  | (y, n) :: r =>
    (i12 less y).bind fun y' => (i12 less n).bind fun n' => (i12Forks less r).map fun r' => (y', n') :: r'
end

/-! ## `+inter2-collapse` -/

/-- The `+roll` of `+inter2-fix-round` over the new kids, from `p`. -/
def rollMsg (less : Cape) (kids : List (I2 × I2)) (p : NeedOrd) : NeedOrd :=
  kids.foldl (fun acc yn => uniOrd acc (msgOrd yn.1.sure yn.2.sure less)) p

mutual
/-- **`+inter2-fix-round`** at a node, the parent's shape coming in as
`parent`. -/
def fixRound (less : Cape) : I2 → NeedOrd → I2
  | I2.mk s fk, parent =>
    I2.mk (rollMsg less (fixKids less fk (uniOrd parent s)) (uniOrd parent s))
      (fixKids less fk (uniOrd parent s))
/-- Its `+turn` over the forks. -/
def fixKids (less : Cape) : List (I2 × I2) → NeedOrd → List (I2 × I2)
  | [], _ => []
  | (y, n) :: r, p => (fixRound less y p, fixRound less n p) :: fixKids less r p
end

/-- **The fixed point of `+inter2-collapse`** with fuel: rounds from the
parent `[%none ~]` until a round gives its input back. -/
def fixLoop (less : Cape) : Nat → I2 → Option I2
  | 0, _ => Option.none
  | k + 1, fix =>
    if (fixRound less fix NeedOrd.none).toNoun = fix.toNoun then some (fixRound less fix NeedOrd.none)
    else fixLoop less k (fixRound less fix NeedOrd.none)

mutual
/-- **`+inter2-orig`**. -/
def orig (less : Cape) : I2 → I2 → Option NeedOrd
  | I2.mk s fk, I2.mk fs ffk => origLoop less fs fk ffk s
/-- Its trap over the forks of `intr` and of `fix`. -/
def origLoop (less : Cape) (fs : NeedOrd) : List (I2 × I2) → List (I2 × I2) → NeedOrd → Option NeedOrd
  | [], _, acc => some acc
  | _ :: _, [], _ => Option.none
  | (y, n) :: r, (fy, fn) :: fr, acc =>
    (orig less y fy).bind fun oy => (orig less n fn).bind fun on =>
      origLoop less fs r fr (uniOrd acc (msgFix oy on fs less))
end

/-- **`+inter2-collapse`** with fuel. -/
def inter2Collapse (fuel : Nat) (intr : I2) (less : Cape) : Option NeedOrd :=
  (fixLoop less fuel intr).bind fun fix => orig less intr fix

/-- **`+shape-collapse`** with fuel for its fixed point. -/
def shapeCol (fuel : Nat) (laz : Lazy S) (less : Cape) : Option NeedOrd :=
  (i12 less (l2i laz)).bind fun intr => inter2Collapse fuel intr less

/-! ## On a fork-free need -/

theorem uniOrd_none_left (b : NeedOrd) : uniOrd NeedOrd.none b = b := by
  unfold uniOrd; by_cases h : NeedOrd.none = b <;> simp [h]

theorem sureStepS_eq (less : Cape) : sureStepS less = sureOfStep less := by
  funext new axe; rfl

/-- **On a lazy need with no fork and no bond, `+shape-collapse` is
`+sure-of` of its sure part.** -/
theorem shapeCol_ofSure (fuel : Nat) (s : Sure S) (less : Cape) :
    shapeCol (fuel + 1) (Lazy.ofSure s) less = sureOfS (needToOrd s.ned) s.lok less := by
  simp only [shapeCol, Lazy.ofSure, l2i, l2iForks, l2iBonds, i12, i12Forks]
  generalize sureOfS (needToOrd s.ned) s.lok less = x
  cases x with
  | none => rfl
  | some r =>
    simp only [Option.bind_some, Option.map_some, inter2Collapse, fixLoop, fixRound, fixKids, rollMsg,
      List.foldl_nil, uniOrd_none_left]
    simp [orig, origLoop]

end Comp
end SkaModel
end Formalization
