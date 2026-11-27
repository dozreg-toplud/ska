import lemmas.Ska.TarjanData

/-!
# `tarjanM` against the real `+tarjan`, and the spec and the invariant on the dump

On the 222 graphs of `TarjanData.lean` (`tools/hoon/tarjandump.hoon`, written by
`tools/gen/tarjancheck.py`):

* (a) `tarjanM` of the dumped graph is the dumped product of the library's
  `+tarjan`: the same list of components in the same order, each component the
  same set; the empty graph crashes in both (`none`);
* (b) every dumped product, flopped (the order `+ska-poke` uses), meets the spec
  on its graph (vertices: the keys and their kids): each component nonempty
  and exactly the SCC of each of its members, the components cover the vertices
  once, callees first (no member of an earlier component calls a member of a
  later one); unflopped (callers first) the order clause fails on some graph;
* (c) on a copy of the model that records its states (`connectT`, after each
  `enter`, each kid, each return of `connect` before its pop, each pop), the
  invariant in the arm's terms holds on every state of every graph: the
  clauses `stkDec`, `curOK`, `partOK`, `idxOK`, `finOK`, `stkReach`, `lowOK`,
  `endOK` below.
-/

namespace Formalization
namespace Tarjan

def sortL (l : List Nat) : List Nat := l.mergeSort

/-! ## (a) the model against the dump -/

def agreeA (c : Nat × Gr Nat × Option (List (List Nat))) : Bool :=
  (tarjanM c.2.1).map (·.map sortL) == c.2.2.map (·.map sortL)

#guard (tjDump.filter fun c => !agreeA c).map (·.1) == []
#guard tjDump.length == 222

/-! ## (b) the spec on the dump -/

/-- The vertices: the keys and their kids. -/
def verts (G : Gr Nat) : List Nat := (G.map (·.1) ++ (G.map (·.2)).flatten).eraseDups

/-- The vertices reachable from `a` (breadth first). -/
def reachFrom (G : Gr Nat) (a : Nat) : List Nat :=
  go (2 * (verts G).length + 2) [a] [a]
where
  go : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, x :: fr, seen =>
    let new := ((kidsOf G x).filter fun w => !seen.contains w).eraseDups
    go n (fr ++ new) (seen ++ new)

/-- The reachability table of `G` (vertices below 100). -/
def reachTab (G : Gr Nat) : Array (Array Bool) :=
  (List.range 100).toArray.map fun a =>
    if (verts G).contains a then
      let r := reachFrom G a
      (List.range 100).toArray.map fun b => r.contains b
    else (List.range 100).toArray.map fun b => decide (a = b)

def rch (R : Array (Array Bool)) (a b : Nat) : Bool := (R.getD a #[]).getD b false

def sccOf (G : Gr Nat) (R : Array (Array Bool)) (a : Nat) : List Nat :=
  (verts G).filter fun b => rch R a b && rch R b a

def calleesFirst (G : Gr Nat) : List (List Nat) → Bool
  | [] => true
  | S :: rest =>
    S.all (fun b => rest.all fun T => T.all fun c => !(kidsOf G b).contains c) && calleesFirst G rest

/-- The spec, `L` callees first. -/
def specB (G : Gr Nat) (L : List (List Nat)) : Bool :=
  let R := reachTab G
  L.all (fun S => !S.isEmpty && S.all fun a => sortL (sccOf G R a) == sortL S) &&
    L.flatten.eraseDups.length == L.flatten.length &&
    sortL L.flatten == sortL (verts G) && calleesFirst G L

-- Flopped, every dumped product meets the spec.
#guard (tjDump.filter fun c => match c.2.2 with
  | none => false
  | some L => !specB c.2.1 L.reverse).map (·.1) == []

-- Unflopped (callers first) it does not, on some graph.
#guard tjDump.any fun c => match c.2.2 with
  | none => false
  | some L => !specB c.2.1 L

/-! ## (c) the invariant on the states of a traced copy of the model -/

/-- A state with the DFS call path (innermost first) and, at a return of
`connect` before its pop, `(v, lowest, index of v)`. -/
structure Snap where
  st : St Nat
  path : List Nat
  ret : Option (Nat × Nat × Nat)

def kidsLoopT (G : Gr Nat) (path : List Nat)
    (rec : Nat → List Nat → St Nat → List Snap → Option (Nat × St Nat × List Snap)) :
    List Nat → Nat → St Nat → List Snap → Option (Nat × St Nat × List Snap)
  | [], lo, acc, log => some (lo, acc, log)
  | k :: ks, lo, acc, log =>
    match acc.vis k with
    | some ki =>
      let lo' := if acc.cur k then min lo ki else lo
      kidsLoopT G path rec ks lo' acc (⟨acc, path, none⟩ :: log)
    | none =>
      match rec k (kidsOf G k) acc log with
      | none => none
      | some (lk, acc', log') => kidsLoopT G path rec ks (min lo lk) acc' (⟨acc', path, none⟩ :: log')

def connectT (G : Gr Nat) : Nat → List Nat → Nat → List Nat → St Nat → List Snap →
    Option (Nat × St Nat × List Snap)
  | 0, _, _, _, _, _ => none
  | n + 1, path, v, kids, acc, log =>
    let e := enter v acc
    match kidsLoopT G (v :: path) (connectT G n (v :: path)) kids acc.idx e (⟨e, v :: path, none⟩ :: log) with
    | none => none
    | some (lo, acc', log') =>
      let log'' := (⟨acc', v :: path, some (v, lo, acc.idx)⟩ : Snap) :: log'
      if acc.idx = lo then
        match popLoop v acc'.stk [] acc'.cur with
        | none => none
        | some (out, stk, cur) =>
          let s : St Nat := { acc' with stk := stk, cur := cur, fin := out :: acc'.fin }
          some (lo, s, ⟨s, path, none⟩ :: log'')
      else some (lo, acc', log'')

def outerT (G : Gr Nat) (n : Nat) : Gr Nat → St Nat → List Snap → Option (St Nat × List Snap)
  | [], acc, log => some (acc, log)
  | (v, kids) :: rest, acc, log =>
    match acc.vis v with
    | some _ => outerT G n rest acc (⟨acc, [], none⟩ :: log)
    | none =>
      match connectT G n [] v kids acc log with
      | none => none
      | some (_, acc', log') => outerT G n rest acc' (⟨acc', [], none⟩ :: log')

def tarjanT (G : Gr Nat) : Option (St Nat × List Snap) :=
  outerT G (fuelOf G) G St.init [⟨St.init, [], none⟩]

/-- The stack: distinct vertices, indices strictly decreasing from the head. -/
def decr : List (Option Nat) → Bool
  | [] => true
  | [a] => a.isSome
  | a :: b :: r => (match a, b with | some x, some y => y < x | _, _ => false) && decr (b :: r)

def stkDec (s : Snap) : Bool := decr (s.st.stk.map s.st.vis)

/-- `cur` is the set of the stack's vertices. -/
def curOK (vs : List Nat) (s : Snap) : Bool := vs.all fun x => s.st.cur x == s.st.stk.contains x

/-- A visited vertex is on the stack or in one emitted set, exactly once; an
unvisited one in neither. -/
def partOK (vs : List Nat) (s : Snap) : Bool :=
  vs.all fun x =>
    let c := (s.st.stk ++ s.st.fin.flatten).count x
    if (s.st.vis x).isSome then c == 1 else c == 0

/-- The indices are distinct, below `idx`, and `idx` is the number of visited
vertices. -/
def idxOK (vs : List Nat) (s : Snap) : Bool :=
  let ix := vs.filterMap s.st.vis
  ix.eraseDups.length == ix.length && ix.all (· < s.st.idx) && ix.length == s.st.idx

def posIn (fin : List (List Nat)) (w : Nat) : Option Nat := fin.findIdx? (·.contains w)

/-- Each emitted set is a full SCC, and every successor of an emitted vertex
is emitted, in the same set or an earlier-emitted one (later in `fin`). -/
def finOK (G : Gr Nat) (R : Array (Array Bool)) (s : Snap) : Bool :=
  let fin := s.st.fin
  (fin.all fun S => S.all fun a => sortL (sccOf G R a) == sortL S) &&
    (List.range fin.length).all fun i =>
      (fin.getD i []).all fun u => (kidsOf G u).all fun w =>
        match posIn fin w with
        | some j => decide (i ≤ j)
        | none => false

/-- Every vertex on the stack reaches a vertex on the stack at or below it
that is on the DFS call path. -/
def stkReach (R : Array (Array Bool)) (s : Snap) : Bool :=
  s.st.stk.all fun x => s.st.stk.any fun y =>
    decide ((s.st.vis y).getD 0 ≤ (s.st.vis x).getD 0) && s.path.contains y && rch R x y

/-- At a return of `connect` on `v` (before its pop): `lowest` is the least of
`v`'s index and the indices of the stack's vertices that a vertex of `v`'s
subtree (indices from `v`'s on) has an edge to. -/
def lowOK (G : Gr Nat) (vs : List Nat) (s : Snap) : Bool :=
  match s.ret with
  | none => true
  | some (_, lo, i0) =>
    let sub := vs.filter fun u => match s.st.vis u with | some i => decide (i0 ≤ i) | none => false
    let ws := sub.flatMap fun u => (kidsOf G u).filter fun w => s.st.stk.contains w
    lo == (ws.filterMap s.st.vis).foldl min i0

/-- The end state: empty stack, every vertex visited. -/
def endOK (vs : List Nat) (st : St Nat) : Bool :=
  st.stk.isEmpty && vs.all (fun x => (st.vis x).isSome) && st.idx == vs.length

def traceOK (clause : Gr Nat → List Nat → Array (Array Bool) → Snap → Bool)
    (c : Nat × Gr Nat × Option (List (List Nat))) : Bool :=
  match c.2.1 with
  | [] => true
  | G =>
    match tarjanT G with
    | none => false
    | some (_, log) =>
      let vs := verts G
      let R := reachTab G
      log.all (clause G vs R)

def failing (clause : Gr Nat → List Nat → Array (Array Bool) → Snap → Bool) : List Nat :=
  (tjDump.filter fun c => !traceOK clause c).map (·.1)

-- The traced copy is the model.
#guard (tjDump.filter fun c => match c.2.1 with
  | [] => false
  | G => (tarjanT G).map (·.1.fin) != tarjanM G).map (·.1) == []

#guard failing (fun _ _ _ s => stkDec s) == []
#guard failing (fun _ vs _ s => curOK vs s) == []
#guard failing (fun _ vs _ s => partOK vs s) == []
#guard failing (fun _ vs _ s => idxOK vs s) == []
#guard failing (fun G _ R s => finOK G R s) == []
#guard failing (fun _ _ R s => stkReach R s) == []
#guard failing (fun G vs _ s => lowOK G vs s) == []

#guard (tjDump.filter fun c => match c.2.1 with
  | [] => false
  | G => match tarjanT G with
    | none => true
    | some (st, _) => !endOK (verts G) st).map (·.1) == []

end Tarjan
end Formalization
