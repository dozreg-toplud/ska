import lemmas.Ska.CompFrag

/-!
# A model of the end of `+comp`: the subject's code and the renumbering

The arms that the final pass of `+compile-scc-in` (the gate `member` with
`done` set, its `finish` with no pessimized shape) runs after `run`, for a
fork-free lazy need and an empty `soft` map:

* `+collapse-shape`: `?>  =(~ args.then.nex)`, then `+need-ord-alloc-regs`
  of the shape that `+shape-collapse` gives.  `+shape-collapse` is not
  modelled: its product is the parameter `ord`, so that what is proved holds
  for every shape.
* `+bake-need` is not modelled.  The model of `finish` takes it as a
  parameter `bake`, and the theorems take the case where it bakes nothing
  (`bake ned = (ned, [])`) as an explicit hypothesis.
* `+coerce-lazy` with `+kern-need`, `+axe-in-less-cape`, `+axe-in-need`.
  With no fork and no bond its last two rolls do nothing; with `soft` empty
  the test `(~(has by soft.gen) o)` is false.  `+soft-done` folds over the
  empty `soft` and is the identity.
* `+to-straight` on its pure-renaming path (the input registers a run
  `[r0, r0+n)` and no proxies): the parameters and the body of each kept
  block through `+map-regs`, its terminator by `+chase-fin`.  `cond` is not
  modelled (it is empty on the fragment), so `proxies` is false.  On the
  other path (the inputs not such a run) the model returns `none`; the
  theorems prove that with nothing baked the inputs are always a run.

`~(rep by blocks)` folds in the treap's order; `HoonMapKeys` gives the keys
of a map in some order with membership as its only law, as `HoonSet` does
for sets, so the theorems hold for the real treap.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A crash in the monad. -/
def crashM {α : Type} : CM Map α := fun _ => Option.none

/-! ## `+need-ord-alloc-regs` -/

def needOrdAllocRegs : NeedOrd → CM Map Need
  | NeedOrd.none => pure Need.none
  | NeedOrd.this => do let r ← re; pure (Need.this r)
  | NeedOrd.pair p q => do
      let h ← needOrdAllocRegs p
      let t ← needOrdAllocRegs q
      if h = Need.none ∧ t = Need.none then crashM else pure (Need.pair h t)
  | NeedOrd.both p q => do
      let r ← re
      let h ← needOrdAllocRegs p
      let t ← needOrdAllocRegs q
      if h = Need.none ∧ t = Need.none then crashM else pure (Need.both r h t)

/-! ## `+axe-in-less-cape`, `+axe-in-need` -/

/-- The loop of `+axe-in-less-cape`. -/
def axeInCape (axe : Nat) (less : Cape) : Bool :=
  if _h : axe ≤ 1 then true else
  match less with
  | Cape.cell h t => if cap axe = 2 then axeInCape (mas axe) h else axeInCape (mas axe) t
  | _ => false
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- `+axe-in-less-cape`: `?<  =(0 axe)`. -/
def axeInLessCape (axe : Nat) (less : Cape) : Option Bool :=
  if axe = 0 then Option.none else some (axeInCape axe less)

/-- The loop of `+axe-in-need`. -/
def axeInNeedL (axe : Nat) (ned : Need) : Bool :=
  if _h : axe ≤ 1 then true else
  match ned with
  | Need.pair p q => if cap axe = 2 then axeInNeedL (mas axe) p else axeInNeedL (mas axe) q
  | Need.both _ h t => if cap axe = 2 then axeInNeedL (mas axe) h else axeInNeedL (mas axe) t
  | _ => false
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-! ## `+kern-need` -/

/-- The case `%both` of the loop of `+kern-need`, with the recursive calls
for the head and the tail as `kh` and `kt`: the ops for the tail from a
fresh register, behind a `%tal` if there are any, then the same for the
head behind a `%hed`, then the `%cel` check, then the `%mov` into the
need's register. -/
def kernBoth (r d : Nat) (kh kt : Nat → List Pole → CM Map (List Pole)) (ops : List Pole) :
    CM Map (List Pole) := do
  let rt ← re
  let ops1 ← kt rt ops
  let ops := if ops1 ≠ ops then Pole.tal d rt :: ops1 else ops1
  let rh ← re
  let ops1 ← kh rh ops
  let ops := if ops1 ≠ ops then Pole.hed d rh :: ops1 else ops1
  let ops := Pole.cel d :: ops
  if r = d then crashM else pure (Pole.mov r d :: ops)

/-- The loop of `+kern-need`, with its accumulator `ops`; a pair is a
`%both` on a fresh register. -/
def kernLoop : Nat → Need → List Pole → CM Map (List Pole)
  | _, Need.none, ops => pure ops
  | r, Need.this d, ops => if r = d then crashM else pure (Pole.mov r d :: ops)
  | r, Need.pair p q, ops => do
      let rn ← re
      kernBoth r rn (fun x a => kernLoop x p a) (fun x a => kernLoop x q a) ops
  | r, Need.both d h t, ops => kernBoth r d (fun x a => kernLoop x h a) (fun x a => kernLoop x t a) ops

/-- `+kern-need`: ops that fill the registers of `ned` from the noun in `r`,
checking each cell the need takes apart. -/
def kernNeed (r : Nat) (ned : Need) : CM Map (List Pole) := kernLoop r ned []

/-! ## `+coerce-lazy` -/

/-- The looks of `+coerce-lazy`: those not known to be there from the
bell's cape, nor from the input need. -/
def coerceLok (lok : S) (less : Cape) (ned : Need) : Option S :=
  (HoonSet.toList lok).foldl (fun acc axe => acc.bind fun s =>
    (axeInLessCape axe less).bind fun inLess =>
      if inLess then some s else
      if axe = 0 then Option.none else
      if axeInNeedL axe ned then some s else some (HoonSet.put s axe)) (some HoonSet.empty)

/-- The loop `sure-loop` of `+coerce-lazy`: the input need `ned` against the
need `tgt` the code wants, ops into block `o`. -/
def sureLoop (o : Nat) : Need → Need → CM Map Unit
  | Need.none, tgt => if tgt = Need.none then pure () else crashM
  | Need.this r, tgt => do let ops ← kernNeed r tgt; addOps o ops
  | Need.pair p q, tgt =>
      match tgt with
      | Need.none => pure ()
      | Need.pair tp tq => do sureLoop o p tp; sureLoop o q tq
      | _ => crashM
  | Need.both r h t, tgt =>
      match tgt with
      | Need.none => pure ()
      | Need.this d => if r = d then crashM else addOps o [Pole.mov r d]
      | Need.pair tp tq => do sureLoop o h tp; sureLoop o t tq
      | Need.both d th tt =>
          if r = d then crashM else do
            addOps o [Pole.mov r d]
            sureLoop o h th
            sureLoop o t tt

/-- `+coerce-lazy` on a fork-free lazy need, with `soft` empty. -/
def coerceLazy (ned : Need) (o : Nat) (laz : Sure S) (less : Cape) : CM Map Unit := do
  let lok ← (fun g => (coerceLok laz.lok less ned).map fun l => (l, g) : CM Map S)
  let tgt ← sureRequireLook ⟨laz.ned, lok⟩
  sureLoop o ned tgt

/-! ## `+to-straight` -/

/-- The keys of a map, in the order `~(rep by m)` visits them. -/
class HoonMapKeys (Map : Type → Type) [HoonMap Map] where
  keys : {ν : Type} → Map ν → List Nat
  mem_keys {ν : Type} (m : Map ν) (k : Nat) : k ∈ keys m ↔ (HoonMap.get m k).isSome

/-- `+bypassable`. -/
def bypassable (branch : Bool) (b : Blob) : Bool :=
  match b.par, b.body, b.fin with
  | [], [], Termin.hop t => !branch || t.args.isEmpty
  | _, _, _ => false

/-- `+chase`: a jump past the bypassable blocks. -/
def chase (bs : Map Blob) (branch : Bool) (j : Jmp) : Option Jmp :=
  (HoonMap.get bs j.there) >>= fun b =>
    match b.fin with
    | Termin.hop t =>
        if bypassable branch b then (if j.args = [] then chase bs branch t else Option.none)
        else some j
    | _ => some j
partial_fixpoint

/-- The renaming of `+to-straight` on a run `[r0, r0+n)` of inputs. -/
def renReg (r0 n r : Nat) : Nat := if r < r0 then r + n else if r < r0 + n then r - r0 else r

/-- `+map-regs` on one op. -/
def renPole (ren : Nat → Nat) : Pole → Pole
  | Pole.imm n d => Pole.imm n (ren d)
  | Pole.mov s d => Pole.mov (ren s) (ren d)
  | Pole.inc s d => Pole.inc (ren s) (ren d)
  | Pole.con h t d => Pole.con (ren h) (ren t) (ren d)
  | Pole.hed s d => Pole.hed (ren s) (ren d)
  | Pole.tal s d => Pole.tal (ren s) (ren d)
  | Pole.cel p => Pole.cel (ren p)
  | Pole.lob p => Pole.lob (ren p)
  | Pole.equ l r => Pole.equ (ren l) (ren r)
  | Pole.hsp n f => Pole.hsp n f
  | Pole.hse n f => Pole.hse n f
  | Pole.hdp n p f => Pole.hdp n (ren p) f
  | Pole.hde n p f => Pole.hde n (ren p) f
  | Pole.hmp a v f => Pole.hmp a (v.map ren) f
  | Pole.hme a v f => Pole.hme a (v.map ren) f
  | Pole.hcp n f => Pole.hcp n f
  | Pole.hce n f => Pole.hce n f
  | Pole.spy e p d => Pole.spy (ren e) (ren p) (ren d)
  | Pole.nok u f d => Pole.nok (ren u) (ren f) (ren d)
  | Pole.cal a v d => Pole.cal a (v.map ren) (ren d)
  | Pole.caf a v d n => Pole.caf a (v.map ren) (ren d) n
  | Pole.cam a v d k => Pole.cam a (v.map ren) (ren d) k
  | Pole.csl a s d => Pole.csl a (ren s) (ren d)
  | Pole.csf a s d n => Pole.csf a (ren s) (ren d) n
  | Pole.csm a s d k => Pole.csm a (ren s) (ren d) k

/-- The renaming of a jump's arguments. -/
def renJmp (ren : Nat → Nat) (j : Jmp) : Jmp := ⟨j.args.map (Option.map ren), j.there⟩

/-- `+chase-fin`.  A block of `+comp` has no `%lti` (that is `termin-out`). -/
def chaseFin (bs : Map Blob) (ren : Nat → Nat) : Termin → Option Termin
  | Termin.clq s z o => (chase bs true z).bind fun z' => (chase bs true o).bind fun o' =>
      some (Termin.clq (ren s) (renJmp ren z') (renJmp ren o'))
  | Termin.eqq l r z o => (chase bs true z).bind fun z' => (chase bs true o).bind fun o' =>
      some (Termin.eqq (ren l) (ren r) (renJmp ren z') (renJmp ren o'))
  | Termin.brn s z o => (chase bs true z).bind fun z' => (chase bs true o).bind fun o' =>
      some (Termin.brn (ren s) (renJmp ren z') (renJmp ren o'))
  | Termin.brz s z o => (chase bs true z).bind fun z' => (chase bs true o).bind fun o' =>
      some (Termin.brz (ren s) (renJmp ren z') (renJmp ren o'))
  | Termin.hop t => (chase bs false t).bind fun t' => some (Termin.hop (renJmp ren t'))
  | Termin.jmp a v => some (Termin.jmp a (v.map ren))
  | Termin.jmf a v n => some (Termin.jmf a (v.map ren) n)
  | Termin.jsp a s => some (Termin.jsp a (ren s))
  | Termin.jsf a s n => some (Termin.jsf a (ren s) n)
  | Termin.don s => some (Termin.don (ren s))
  | Termin.bom Option.none => some (Termin.bom Option.none)
  | Termin.bom (some x) => (chase bs true ⟨[], x⟩).bind fun j => some (Termin.bom (some j.there))
  | Termin.lti _ _ _ _ => Option.none

/-- `+rewrite-input` on the renaming path: the need without its registers. -/
def needToOrd : Need → NeedOrd
  | Need.none => NeedOrd.none
  | Need.this _ => NeedOrd.this
  | Need.pair p q => NeedOrd.pair (needToOrd p) (needToOrd q)
  | Need.both _ h t => NeedOrd.both (needToOrd h) (needToOrd t)

/-- `+count-args`. -/
def countArgs : NeedOrd → Nat
  | NeedOrd.none => 0
  | NeedOrd.this => 1
  | NeedOrd.pair p q => countArgs p + countArgs q
  | NeedOrd.both h t => countArgs h + countArgs t + 1

/-- Whether the registers are the run `r0, r0+1, ..` (the loop `run` of
`+to-straight`). -/
def isRun : List Nat → Nat → Nat → Bool
  | [], _, _ => true
  | r :: rs, r0, i => r == r0 + i && isRun rs r0 (i + 1)

/-- One kept block, renamed, with its terminator chased. -/
def keepBlock (bs : Map Blob) (ren : Nat → Nat) (k : Nat) (b : Blob) : Option (Option Blob) :=
  if k ≠ 0 ∧ bypassable true b then some Option.none else
  (chaseFin bs ren b.fin).map fun fin => some ⟨b.par.map ren, b.body.map (renPole ren), fin⟩

/-- The fold `~(rep by blocks)` of the renaming path. -/
def renameBlocks [HoonMapKeys Map] (bs : Map Blob) (ren : Nat → Nat) : Option (Map Blob) :=
  (HoonMapKeys.keys bs).foldl (fun acc k => acc.bind fun new =>
    (HoonMap.get bs k).bind fun b => (keepBlock bs ren k b).map fun kb =>
      match kb with
      | Option.none => new
      | some b1 => HoonMap.put new k b1) (some HoonMap.empty)

/-- `+to-straight` of `[%next [[ned ~] ~ ~] ~ o]`, on its pure-renaming path;
`none` on the other path. -/
def toStraight [HoonMapKeys Map] (blocks : Map Blob) (ned : Need) (o : Nat) : Option (Straight Map) :=
  let ins := flattenNeed ned
  let r0 := ins.headD 0
  let n := ins.length
  if isRun ins r0 0 = false then Option.none else
  (HoonMap.get blocks o).bind fun start =>
    let bs := HoonMap.put (HoonMap.del blocks o) 0 start
    (renameBlocks bs (renReg r0 n)).map fun new =>
      ⟨needToOrd ned, countArgs (needToOrd ned), new⟩

/-! ## The final pass -/

/-- The initial state of `+comp` in the final pass: `*line-short` with mode
`%run`. -/
def gen0 : Gen Map := ⟨0, 1, 0, false, HoonMap.empty⟩

/-- The final pass of `member` in `+compile-scc-in` for a function alone in
its SCC, on the nomm `nm`: `run` for `%done`, `+collapse-shape` with the
shape `ord`, `bake` (a parameter for `+bake-need`), `+coerce-lazy`,
`+soft-done` (the identity), the baked immediates into block `o`, and
`+to-straight`. -/
def finish [HoonMapKeys Map] (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (run nm (CGoal.done : CGoal S) gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazy nedFinal nex.th.there nex.laz less g2).bind fun (_, g3) =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
          toStraight g4.blocks bak.1 nex.th.there

end Comp
end SkaModel
end Formalization
