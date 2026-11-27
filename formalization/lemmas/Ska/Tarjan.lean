/-!
# `tarjanM`: the model of `++  tarjan` (`desk/lib/nock-compilation.hoon`)

The arm, step by step:

* the graph `g` is a `(jug v v)`; `~(rep by g)` visits its entries in the
  pre-order of the treap (node, left, right), and `~(rep in kids)` the kids
  of a vertex in that order.  The model takes the graph as that list
  (`Gr V`: each key with its kids, in `rep` order); `~(get ju g) kid` is
  `kidsOf G kid` (`~` off the keys, so a kid outside the key set is a vertex
  without kids);
* the state `gen` is `St`: `idx` the index counter, `vis` the indices of the
  visited vertices, `stk` the stack, `cur` the set of the stack's vertices,
  `fin` the components emitted, the last emitted first;
* `connect` (the trap `connect`): give `v` the next index, push it (`enter`),
  fold its kids (`kidsLoop`): a visited kid on the stack lowers `lowest` to
  its index, a visited kid off the stack does nothing, an unvisited kid is
  visited by `connect` and lowers `lowest` to what it returns; if `lowest`
  is still `v`'s index, pop the stack down to `v` (`popLoop`, a crash on the
  empty stack) and cons the popped set onto `fin`;
* `outer` (the `~(rep by g)`): every key not visited yet is a root;
* `tarjanM`: `fin` of the end state.  On the empty graph the arm crashes
  (the bunt of `vertex = _p.n.-.g` reads the root node of `g` when the gate
  of the `rep` is built), so the model is `none` there.

`connect` recurses on the fuel: the recursion is not structural (it goes to
an unvisited kid).  The measure is the number of unvisited vertices, which
each call lowers by one; `fuelOf G` (one more than the count of key and kid
occurrences of `G`) is above it.

`fin` has the components callers first (the first one emitted, a sink of the
condensation, is last); `+ska-poke` flops it to callees first.
-/

namespace Formalization
namespace Tarjan

/-- The graph in the order of `~(rep by g)`: each key with its kids in the
order of `~(rep in kids)`. -/
abbrev Gr (V : Type) := List (V × List V)

variable {V : Type} [DecidableEq V]

/-- `~(get ju g) v`: the kids of `v`, none off the keys. -/
def kidsOf (G : Gr V) (v : V) : List V :=
  match G.find? (fun p => decide (p.1 = v)) with
  | some p => p.2
  | none => []

/-- The state `gen` of the arm. -/
structure St (V : Type) where
  idx : Nat
  vis : V → Option Nat
  stk : List V
  cur : V → Bool
  fin : List (List V)

/-- The bunt of `gen`. -/
def St.init : St V := ⟨0, fun _ => none, [], fun _ => false, []⟩

/-- The pop loop: pop until `v` (`v` included), each popped vertex leaves
`cur` and joins `out`; a crash on the empty stack.  Returns `out`, the rest
of the stack and `cur`. -/
def popLoop (v : V) : List V → List V → (V → Bool) → Option (List V × List V × (V → Bool))
  | [], _, _ => none
  | p :: stk, out, cur =>
    let cur' := fun x => if x = p then false else cur x
    if v = p then some (p :: out, stk, cur') else popLoop v stk (p :: out) cur'

/-- The first step of `connect`: `v` gets the index `idx`, which grows by
one; `v` is pushed and joins `cur`. -/
def enter (v : V) (acc : St V) : St V :=
  { acc with idx := acc.idx + 1, vis := fun x => if x = v then some acc.idx else acc.vis x,
             stk := v :: acc.stk, cur := fun x => if x = v then true else acc.cur x }

/-- The fold `~(rep in kids)` of `connect`, with `connect` at the smaller
fuel as `rec`.  `lo` is `lowest`. -/
def kidsLoop (G : Gr V) (rec : V → List V → St V → Option (Nat × St V)) :
    List V → Nat → St V → Option (Nat × St V)
  | [], lo, acc => some (lo, acc)
  | k :: ks, lo, acc =>
    match acc.vis k with
    | some ki => kidsLoop G rec ks (if acc.cur k then min lo ki else lo) acc
    | none =>
      match rec k (kidsOf G k) acc with
      | none => none
      | some (lk, acc') => kidsLoop G rec ks (min lo lk) acc'

/-- The trap `connect` on `v` with kids `kids`: returns `lowest` and the
state. -/
def connect (G : Gr V) : Nat → V → List V → St V → Option (Nat × St V)
  | 0, _, _, _ => none
  | n + 1, v, kids, acc =>
    match kidsLoop G (connect G n) kids acc.idx (enter v acc) with
    | none => none
    | some (lo, acc') =>
      if acc.idx = lo then
        match popLoop v acc'.stk [] acc'.cur with
        | none => none
        | some (out, stk, cur) => some (lo, { acc' with stk := stk, cur := cur, fin := out :: acc'.fin })
      else some (lo, acc')

/-- The outer `~(rep by g)`: a key not visited yet is a root of `connect`. -/
def outer (G : Gr V) (n : Nat) : Gr V → St V → Option (St V)
  | [], acc => some acc
  | (v, kids) :: rest, acc =>
    match acc.vis v with
    | some _ => outer G n rest acc
    | none =>
      match connect G n v kids acc with
      | none => none
      | some (_, acc') => outer G n rest acc'

/-- The fuel: one more than the number of key and kid occurrences. -/
def fuelOf (G : Gr V) : Nat := G.length + (G.map fun p => p.2.length).sum + 1

/-- **The model of `+tarjan`**: the components, callers first; `none` on the
empty graph (the arm crashes there). -/
def tarjanM (G : Gr V) : Option (List (List V)) :=
  match G with
  | [] => none
  | _ :: _ => (outer G (fuelOf G) G St.init).map St.fin

end Tarjan
end Formalization
