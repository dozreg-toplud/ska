import lemmas.Ska.Mink

/-!
# The interpreter of SKA's IR

The last core of `nock-compilation.hoon`, "Formal definition of the
interpreter": `+eval-top`, `+eval-blob`, `+eval-pole`, `+eval-pass`,
`+read`, `+store`, `+move`, `+eval-mook` and `+eval-rend`.

The interpreter pokes the compiler: `(poke %full s f)` for an entry point and
`(poke %dire a mono)` for a callee.  Here the compiler is a parameter,
`poke : σ → Ovum → Option (Prod Map × σ)`, with an opaque state `σ` (the
inner core); `none` is a poke that crashes or does not return.

## How the recursion is modelled

The Hoon arms call each other: `+eval-blob` runs a callee's blocks by calling
itself, and `+eval-pole` runs an indirect call by calling `+eval-top`.  The
model splits the recursion in two.

* Inside one function, `execBlob` follows the blocks and the ops.  What leaves
  the function, a call (`%cal` and the like, `%jmp` and the like) or an
  indirect call (`%nok`), is asked of an `Oracle`.  `execBlob` is defined by
  `partial_fixpoint`, since the blocks of an IR may loop.
* `interp k` is the oracle of the interpreter itself, with `k` levels of
  calls: a call pokes `%dire` and runs the callee with `interp (k - 1)`, and
  an indirect call is `+eval-top` with `interp (k - 1)`.

So `(interp k).nok` is `+eval-top` allowed `k` nested calls, and `+eval-top`
returns `r` when some `k` is enough (`EvalTop`).  Each Hoon arm is one Lean
function: `+eval-top` is `topBody`, `+eval-blob` is `execBlob`, `+eval-pole`
is `execPole`, `+eval-pass` is `evalPass`; the poke and the jump to the
callee's first block, which `+eval-blob` and `+eval-pole` write out at each
call, are `callBody`.  `%caf`, `%cam`, `%jmf`, `%csf`, `%csm` and `%jsf` are
plain calls, as in the Hoon.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- What leaves a function: a call of a bell (`mono` tells whether the
subject goes whole, in one register) on argument values with the caller's
trace, and an indirect call `.*(u f)`.  Both take the scry gate. -/
structure Oracle (σ : Type) where
  call : σ → Bell → Bool → List Noun → Trace → Noun → Option (Tone × σ)
  nok : σ → Noun → Noun → Noun → Option (Tone × σ)

section
variable {Map : Type → Type} [HoonMap Map]

/-! ## The registers

The Hoon keeps the registers as a `(map @uvre (unit *))`: `[~ v]` is the
value `v`, `~` is poison, the mark of a parameter that a hop passed `~`.  A
poisoned register is defined: `+move` copies it.  Only a real read, `+read`,
asks for a value.  Here the map is a `Map (Option Noun)`, whose noun is
`HoonMap.toNoun (unitNoun id) regs`. -/

/-- `+read`: `(~(got by regs) r)`, which must be a value: a crash if the
register is not there or is poisoned. -/
def read (r : Nat) (regs : Map (Option Noun)) : Option Noun :=
  match HoonMap.get regs r with
  | some (some v) => some v
  | _ => none

/-- `+store`: `(~(put by regs) r `v)`. -/
def store (r : Nat) (v : Noun) (regs : Map (Option Noun)) : Map (Option Noun) :=
  HoonMap.put regs r (some v)

/-- `+move`: `(~(put by regs) d (~(got by regs) s))`, which copies a value or
poison, and crashes if `s` is not there. -/
def move (s d : Nat) (regs : Map (Option Noun)) : Option (Map (Option Noun)) :=
  (HoonMap.get regs s).map fun u => HoonMap.put regs d u

/-- `(~(put by regs) p ~)`: the register `p` is poisoned. -/
def poison (p : Nat) (regs : Map (Option Noun)) : Map (Option Noun) := HoonMap.put regs p none

/-- The loop of `+eval-pass`: an argument `~` poisons its parameter, a
register is moved to it. -/
def evalPassLoop : List (Option Nat) → List Nat → Map (Option Noun) → Option (Map (Option Noun))
  | [], par, regs => if par = [] then some regs else none
  | _ :: _, [], _ => none
  | a :: args, p :: par, regs =>
      (match a with
       | none => some (poison p regs)
       | some r => move r p regs).bind (evalPassLoop args par)

/-- `+eval-pass`: the arguments of a jump to the parameters of a block.  It
checks that no argument is a parameter. -/
def evalPass (args : List (Option Nat)) (par : List Nat) (regs : Map (Option Noun)) :
    Option (Map (Option Noun)) :=
  if args.all (fun a => match a with | none => true | some r => !par.contains r) then
    evalPassLoop args par regs
  else none

/-! ### What the proofs use of the registers -/

theorem read_eq_some {r : Nat} {regs : Map (Option Noun)} {v : Noun} :
    read r regs = some v ↔ HoonMap.get regs r = some (some v) := by
  unfold read; split <;> simp_all

theorem read_store_self (r : Nat) (v : Noun) (regs : Map (Option Noun)) :
    read r (store r v regs) = some v := by
  simp [read, store, HoonMap.get_put]

theorem read_store_other {r r' : Nat} (h : r' ≠ r) (v : Noun) (regs : Map (Option Noun)) :
    read r' (store r v regs) = read r' regs := by
  simp [read, store, HoonMap.get_put, h]

theorem read_poison_self (p : Nat) (regs : Map (Option Noun)) : read p (poison p regs) = none := by
  simp [read, poison, HoonMap.get_put]

theorem read_poison_other {r p : Nat} (h : r ≠ p) (regs : Map (Option Noun)) :
    read r (poison p regs) = read r regs := by
  simp [read, poison, HoonMap.get_put, h]

/-- A move of a value is a store of it. -/
theorem move_of_read {s d : Nat} {regs : Map (Option Noun)} {v : Noun} (h : read s regs = some v) :
    move s d regs = some (store d v regs) := by
  rw [read_eq_some] at h; simp [move, store, h]

/-- After a move, `d` reads as `s` read before, the others as before. -/
theorem read_move {s d : Nat} {regs regs' : Map (Option Noun)} (h : move s d regs = some regs')
    (r : Nat) : read r regs' = if r = d then read s regs else read r regs := by
  unfold move at h
  cases e : HoonMap.get regs s with
  | none => simp [e] at h
  | some u =>
    simp only [e, Option.map_some, Option.some.injEq] at h
    subst h
    by_cases hr : r = d
    · subst hr; simp [read, HoonMap.get_put, e]
    · simp [read, HoonMap.get_put, hr]

/-- A move crashes only on a register that is not there. -/
theorem move_isSome {s d : Nat} {regs : Map (Option Noun)} :
    (move s d regs).isSome = (HoonMap.get regs s).isSome := by
  simp [move]

/-- `pop`: `+.trace`, a crash on an empty trace. -/
def popTrace : Trace → Option Trace
  | [] => none
  | _ :: t => some t

variable {σ : Type}

/-- After a call: `%0` stores the product, `%1` and `%2` end the block. -/
def afterCall (st : σ) (regs : Map (Option Noun)) (trace : Trace) (d : Nat) :
    Tone → Option (Tone × Map (Option Noun) × Trace × σ)
  | Tone.zero p => some (Tone.zero (A 0), store d p regs, trace, st)
  | Tone.one b => some (Tone.one b, regs, trace, st)
  | Tone.two tr => some (Tone.two tr, regs, trace, st)

/-- The ops of `+eval-pole` that do not leave the function: they change the
registers and the trace only.  `fine` is `[%0 ~]`, `boom` is `[%2 trace]`; a
crash of the Hoon (a register that is not there, the head of an atom, a pop
of an empty trace, a scry gate that crashes) is `none`.  The ops that leave
the function, `%nok` and the calls, are not local; `execPole` runs them. -/
def localPole (lib : Lib) (scry : Noun) (pole : Pole) (regs : Map (Option Noun)) (trace : Trace) :
    Option (Tone × Map (Option Noun) × Trace) :=
  let fine := fun (regs : Map (Option Noun)) (trace : Trace) => some (Tone.zero (A 0), regs, trace)
  let boom := some (Tone.two trace, regs, trace)
  match pole with
  | Pole.imm n d => fine (store d n regs) trace
  | Pole.mov s d => (move s d regs).bind fun r => fine r trace
  | Pole.inc s d => (read s regs).bind fun v =>
      match v with
      | Noun.cell _ _ => boom
      | Noun.atom a => fine (store d (A (a + 1)) regs) trace
  | Pole.con h t d => (read h regs).bind fun vh => (read t regs).bind fun vt =>
      fine (store d (C vh vt) regs) trace
  | Pole.hed s d => (read s regs).bind fun v =>
      match v with
      | Noun.cell x _ => fine (store d x regs) trace
      | Noun.atom _ => none
  | Pole.tal s d => (read s regs).bind fun v =>
      match v with
      | Noun.cell _ y => fine (store d y regs) trace
      | Noun.atom _ => none
  | Pole.cel p => (read p regs).bind fun v =>
      match v with
      | Noun.atom _ => boom
      | Noun.cell _ _ => fine regs trace
  | Pole.lob p => (read p regs).bind fun v =>
      if v = A 0 ∨ v = A 1 then fine regs trace else boom
  | Pole.equ l r => (read l regs).bind fun _ => (read r regs).bind fun _ => fine regs trace
  | Pole.hsp _ _ => fine regs trace
  | Pole.hse _ _ => fine regs trace
  | Pole.hdp n p _ =>
      if stopTag n then (read p regs).bind fun v => fine regs ((n, v) :: trace)
      else fine regs trace
  | Pole.hde n _ _ =>
      if stopTag n then (popTrace trace).bind fun t => fine regs t
      else fine regs trace
  | Pole.hmp a v _ => (v.mapM (read · regs)).bind fun vs =>
      fine regs ((Tag.meaf, C a.toNoun (listNoun id vs)) :: trace)
  | Pole.hme _ _ _ => (popTrace trace).bind fun t => fine regs t
  | Pole.hcp n _ => fine regs ((Tag.meac, n) :: trace)
  | Pole.hce _ _ => (popTrace trace).bind fun t => fine regs t
  | Pole.spy e p d =>
      if scry = A 0 then boom else
      (read e regs).bind fun ref => (read p regs).bind fun pax =>
        (lib.slam scry (C ref pax)).bind fun res => (scryDecode res).bind fun dr =>
          match dr with
          | ScryRes.block => some (Tone.one pax, regs, trace)
          | ScryRes.hunk =>
              some (Tone.two ((Tag.hunk, C ref pax) :: trace), regs, (Tag.hunk, C ref pax) :: trace)
          | ScryRes.val v => fine (store d v regs) trace
  | _ => none

/-- `+eval-pole`: one op.  `%nok` is `+eval-top` (the oracle's `nok`) with
an empty trace, whose trace on a crash goes on top of ours; the calls are the
oracle's `call`.  The other ops are `localPole`. -/
def execPole (lib : Lib) (O : Oracle σ) (scry : Noun) (st : σ) (pole : Pole)
    (regs : Map (Option Noun)) (trace : Trace) : Option (Tone × Map (Option Noun) × Trace × σ) :=
  match pole with
  | Pole.nok u f d => (read u regs).bind fun vu => (read f regs).bind fun vf =>
      (O.nok st vu vf scry).bind fun (ton, st') =>
        match ton with
        | Tone.zero p => some (Tone.zero (A 0), store d p regs, trace, st')
        | Tone.one b => some (Tone.one b, regs, trace, st')
        | Tone.two tr => some (Tone.two (tr ++ trace), regs, trace, st')
  | Pole.cal a v d => (v.mapM (read · regs)).bind fun vs =>
      (O.call st a false vs trace scry).bind fun (ton, st') => afterCall st' regs trace d ton
  | Pole.caf a v d _ => (v.mapM (read · regs)).bind fun vs =>
      (O.call st a false vs trace scry).bind fun (ton, st') => afterCall st' regs trace d ton
  | Pole.cam a v d _ => (v.mapM (read · regs)).bind fun vs =>
      (O.call st a false vs trace scry).bind fun (ton, st') => afterCall st' regs trace d ton
  | Pole.csl a s d => (read s regs).bind fun vs =>
      (O.call st a true [vs] trace scry).bind fun (ton, st') => afterCall st' regs trace d ton
  | Pole.csf a s d _ => (read s regs).bind fun vs =>
      (O.call st a true [vs] trace scry).bind fun (ton, st') => afterCall st' regs trace d ton
  | Pole.csm a s d _ => (read s regs).bind fun vs =>
      (O.call st a true [vs] trace scry).bind fun (ton, st') => afterCall st' regs trace d ton
  | _ => (localPole lib scry pole regs trace).map fun (ton, regs', trace') => (ton, regs', trace', st)

/-- `+eval-blob`: run the block `b` of the function `s`, after passing
`params` to its parameters, then its ops, then its end. -/
def execBlob (lib : Lib) (O : Oracle σ) (s : Straight Map) (scry : Noun)
    (st : σ) (regs : Map (Option Noun)) (trace : Trace) (b : Blob) (params : List (Option Nat)) :
    Option (Tone × σ) :=
  if params ≠ [] ∨ b.par ≠ [] then
    (evalPass params b.par regs) >>= fun regs' =>
      execBlob lib O s scry st regs' trace { b with par := [] } []
  else
  match b.body with
  | p :: rest =>
      (execPole lib O scry st p regs trace) >>= fun (ton, regs', trace', st') =>
        match ton with
        | Tone.zero _ => execBlob lib O s scry st' regs' trace' { b with body := rest } []
        | _ => some (ton, st')
  | [] =>
    match b.fin with
    | Termin.lti n r z o => (read r regs) >>= fun v =>
        let j := if (match v with | Noun.atom a => decide (a < n) | _ => false) then z else o
        (HoonMap.get s.blocks j.there) >>= fun b' => execBlob lib O s scry st regs trace b' j.args
    | Termin.clq r z o => (read r regs) >>= fun v =>
        let j := match v with | Noun.cell _ _ => z | Noun.atom _ => o
        (HoonMap.get s.blocks j.there) >>= fun b' => execBlob lib O s scry st regs trace b' j.args
    | Termin.eqq l r z o => (read l regs) >>= fun x => (read r regs) >>= fun y =>
        let j := if x = y then z else o
        (HoonMap.get s.blocks j.there) >>= fun b' => execBlob lib O s scry st regs trace b' j.args
    | Termin.brn r z o => (read r regs) >>= fun v =>
        if v = A 0 then
          (HoonMap.get s.blocks z.there) >>= fun b' => execBlob lib O s scry st regs trace b' z.args
        else if v = A 1 then
          (HoonMap.get s.blocks o.there) >>= fun b' => execBlob lib O s scry st regs trace b' o.args
        else some (Tone.two trace, st)
    | Termin.brz r z o => (read r regs) >>= fun v =>
        let j := if v = A 0 then z else o
        (HoonMap.get s.blocks j.there) >>= fun b' => execBlob lib O s scry st regs trace b' j.args
    | Termin.hop t =>
        (HoonMap.get s.blocks t.there) >>= fun b' => execBlob lib O s scry st regs trace b' t.args
    | Termin.jmp a v => (v.mapM (read · regs)) >>= fun vs => O.call st a false vs trace scry
    | Termin.jmf a v _ => (v.mapM (read · regs)) >>= fun vs => O.call st a false vs trace scry
    | Termin.jsp a r => (read r regs) >>= fun v => O.call st a true [v] trace scry
    | Termin.jsf a r _ => (read r regs) >>= fun v => O.call st a true [v] trace scry
    | Termin.don r => (read r regs) >>= fun v => some (Tone.zero v, st)
    | Termin.bom _ => some (Tone.two trace, st)
partial_fixpoint

/-- The registers of a callee: value `i` in register `i`, put in order, each
wrapped in a unit. -/
def regsFrom : Nat → List Noun → Map (Option Noun) → Map (Option Noun)
  | _, [], out => out
  | r, v :: vs, out => regsFrom (r + 1) vs (HoonMap.put out r (some v))

def regsOf (vals : List Noun) : Map (Option Noun) := regsFrom 0 vals HoonMap.empty

/-- Entering a function: its block 0, with the argument values in registers
`0 ..`, no parameters passed. -/
def execEntry (lib : Lib) (O : Oracle σ) (st : σ) (c : Straight Map) (vals : List Noun)
    (trace : Trace) (scry : Noun) : Option (Tone × σ) :=
  (HoonMap.get c.blocks 0).bind fun b => execBlob lib O c scry st (regsOf vals) trace b []

/-- A call, as `+eval-blob` and `+eval-pole` make it: poke `%dire`, take
the `%ir` apart, and run the callee from its block 0. -/
def callBody (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) (O : Oracle σ)
    (st : σ) (a : Bell) (mono : Bool) (vals : List Noun) (trace : Trace) (scry : Noun) :
    Option (Tone × σ) :=
  (poke st (Ovum.dire a mono)).bind fun (p, st') =>
    match p with
    | Prod.ir _ c _ => execEntry lib O st' c vals trace scry
    | _ => none

/-- `?=([%11 %bare *] f)`: a formula under a `%bare` hint. -/
def isBare : Noun → Bool
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom t) _) => t == Tag.bare
  | _ => false

/-- `+eval-top`.  A formula under `%bare` is run by `+mink`, here with `k`
levels of fuel; any other is compiled and run. -/
def topBody (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) (O : Oracle σ) (k : Nat)
    (st : σ) (s f scry : Noun) : Option (Tone × σ) :=
  match f with
  | Noun.atom _ => some (Tone.two [], st)
  | Noun.cell _ _ =>
    if isBare f then (minkF lib scry k [] s f).map fun r => (r, st) else
    (poke st (Ovum.full s f)).bind fun (p, st') =>
      match p with
      | Prod.ir _ c _ =>
        if c.nargs = 1 ∧ c.need = NeedOrd.this then
          (HoonMap.get c.blocks 0).bind fun b =>
            if b.par = [] then execBlob lib O c scry st' (regsOf [s]) [] b [] else none
        else none
      | _ => none

/-- The interpreter's own oracle, with `k` levels of calls. -/
def interp (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) : Nat → Oracle σ
  | 0 => ⟨fun _ _ _ _ _ _ => none, fun _ _ _ _ => none⟩
  | k + 1 => ⟨callBody lib poke (interp lib poke k), topBody lib poke (interp lib poke k) k⟩

/-- `(eval-top [s f] gul)` in the state `st` returns the tone `ton` and the
state `st'`. -/
def EvalTop (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) (st : σ) (s f gul : Noun)
    (ton : Tone) (st' : σ) : Prop :=
  ∃ k, (interp lib poke k).nok st s f gul = some (ton, st')

/-! ## Rendering the trace -/

/-- `+eval-rend`: a frame to a tank.  `%meac` is a constant `%mean`,
`%meaf` a deferred one, which runs the arm (a call with neither trace nor
scry gate); any other frame is rendered by `+mook`. -/
def evalRend (lib : Lib) (O : Oracle σ) (k : Nat) (st : σ) (fr : Frame) : Option (Noun × σ) :=
  if fr.1 = Tag.meac then some (rendProduct lib fr.2, st)
  else if fr.1 = Tag.meaf then
    match fr.2 with
    | Noun.atom _ => none
    | Noun.cell hd tl =>
      (nounList? tl).bind fun vs => (Bell.ofNoun? hd).bind fun a =>
        (O.call st a false vs [] (A 0)).bind fun (ton, st') =>
          match ton with
          | Tone.zero p => some (rendProduct lib p, st')
          | _ => some (leafHash, st')
  else (rendF lib k fr).map fun tank => (tank, st)

/-- The loop of `+eval-mook`: the frames from the last, each tank consed. -/
def evalMookLoop (lib : Lib) (O : Oracle σ) (k : Nat) : σ → List Frame → List Noun →
    Option (List Noun × σ)
  | st, [], out => some (out, st)
  | st, fr :: rest, out =>
      (evalRend lib O k st fr).bind fun (tank, st') => evalMookLoop lib O k st' rest (tank :: out)

/-- `+eval-mook`: the tone of `+eval-top` as a toon. -/
def evalMook (lib : Lib) (O : Oracle σ) (k : Nat) (st : σ) : Tone → Option (Toon × σ)
  | Tone.zero p => some (Toon.zero p, st)
  | Tone.one p => some (Toon.one p, st)
  | Tone.two tr =>
      (evalMookLoop lib O k st (skip lib (fun m => (Tag.lose, m)) tr).reverse []).map
        fun (out, st') => (Toon.two out, st')

/-- The interpreter, rendered: `+eval-top`, then `+eval-mook` of its tone,
both with `k` levels of calls. -/
def RunI (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) (st : σ) (s f gul : Noun)
    (toon : Toon) (st'' : σ) : Prop :=
  ∃ k ton st', (interp lib poke k).nok st s f gul = some (ton, st') ∧
    evalMook lib (interp lib poke k) k st' ton = some (toon, st'')

end

end SkaModel
end Formalization
