import lemmas.Ska.Know

/-!
# The flags of `code`: `+eval-finalized` and the SCC loop of `+ska-poke`

An entry of `code.lon` is `[nomm pure total]`.  The flags are written by the
SCC loop at the end of `+ska-poke` (README Gaps 23, P1): for each SCC of the
new bells, callees' SCCs first, every member is put with `[| |]`, then each
member in the order of `~(rep in scc)` gets `(eval-finalized b acc)`, which
reads the flags written so far (`+got:by` on `acc`, a crash on a bell that
is not there).

* `haveAx`: the arm `+have` of `+eval-finalized` (its assert `axe ≠ 0` is
  `haveO`);
* `efGo`: the trap `nomm-loop` on the sock `sub`, `[s pure total]`; the
  `?&` of the `%2` and `%5` cases stop at the first `|` (the later parts are
  not run, so their crashes do not count), the other conjunctions are of
  values already computed;
* `evalFin`: `+eval-finalized` on a nomm table and a flag table;
* `sccStep`, `sccLoop`: the SCC loop on a list of SCCs, each the list of
  its members in `~(rep in scc)` order;
* `flagNoun`: the noun `[pure total]` (`&` is `0`).

The models are computable over functions (`Bell → Option _`), so the
`#guard`s of `PokeFlagsCheck.lean` run them on the tables the real compiler
made.
-/

namespace Formalization
namespace SkaModel
namespace PokeF

open Nock Bake

/-- `+have` of `+eval-finalized` past its assert: whether the sock knows the
cells down to `axe`. -/
def haveAx (s : Sock) (axe : Nat) : Bool :=
  if axe ≤ 1 then true else
  match s with
  | Sock.mk Cape.no _ => false
  | _ => if cap axe = 2 then haveAx (So.hed s) (mas axe) else haveAx (So.tel s) (mas axe)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- `+have` with its assert `?<  =(0 axe)`. -/
def haveO (s : Sock) (axe : Nat) : Option Bool := if axe = 0 then none else some (haveAx s axe)

/-- The flags `[pure total]` of the entries of `acc`, by bell. -/
abbrev FlagTab := Bell → Option (Bool × Bool)

/-- `?&(a b)` when `b` runs only if `a` is `&`. -/
def andS (a b : Option Bool) : Option Bool :=
  match a with
  | some true => b
  | some false => some false
  | none => none

/-- The trap `nomm-loop` of `+eval-finalized` on the sock `sub`. -/
def efGo (ft : FlagTab) : Sock → Nomm → Option (Sock × Bool × Bool)
  | sub, Nomm.cons p q =>
    (efGo ft sub p).bind fun rp => (efGo ft sub q).map fun rq =>
      (So.knit rp.1 rq.1, rp.2.1 && rq.2.1, rp.2.2 && rq.2.2)
  | sub, Nomm.n0 p =>
    if p = 0 then some (Sock.dunno, false, false) else
    (So.pull sub p).bind fun s => (haveO sub p).map fun h => (s, h, h)
  | _, Nomm.n1 p => some (Sock.mk Cape.yes p, true, true)
  | sub, Nomm.n2 p q info =>
    let ip : Option Bool := match info with
      | none => some false
      | some i => (ft i.1).map (·.1)
    let it : Option Bool := match info with
      | none => some false
      | some i => (ft i.1).map (·.2)
    (andS ((efGo ft sub p).map (·.2.1)) (andS ((efGo ft sub q).map (·.2.1)) ip)).bind fun pu =>
    (andS ((efGo ft sub p).map (·.2.2)) (andS ((efGo ft sub q).map (·.2.2)) it)).map fun to =>
      (Sock.dunno, pu, to)
  | sub, Nomm.n3 p => (efGo ft sub p).map fun r => (Sock.dunno, r.2.1, r.2.2)
  | _, Nomm.n4 _ => some (Sock.dunno, false, false)
  | sub, Nomm.n5 p q =>
    (andS ((efGo ft sub p).map (·.2.1)) ((efGo ft sub q).map (·.2.1))).bind fun pu =>
    (andS ((efGo ft sub p).map (·.2.2)) ((efGo ft sub q).map (·.2.2))).map fun to =>
      (Sock.dunno, pu, to)
  | sub, Nomm.n6 _ q r =>
    (efGo ft sub q).bind fun y => (efGo ft sub r).map fun n => (So.purr y.1 n.1, false, false)
  | sub, Nomm.n7 p q =>
    (efGo ft sub p).bind fun rp => (efGo ft rp.1 q).map fun rq =>
      (rq.1, rp.2.1 && rq.2.1, rp.2.2 && rq.2.2)
  | sub, Nomm.n10 a v q =>
    (efGo ft sub v).bind fun don => (efGo ft sub q).bind fun rec => (haveO rec.1 a).bind fun got =>
    (So.darn rec.1 a don.1).map fun s =>
      (s, rec.2.1 && don.2.1 && got, rec.2.2 && don.2.2 && got)
  | sub, Nomm.n11s _ q _ => (efGo ft sub q).map fun r => (r.1, false, r.2.2)
  | sub, Nomm.n11d tag h q _ =>
    (efGo ft sub h).bind fun tok => (efGo ft sub q).map fun fol =>
      (fol.1, hintFree tag && tok.2.1 && fol.2.1, tok.2.2 && fol.2.2)
  | _, Nomm.n12 _ _ => some (Sock.dunno, false, false)
  | sub, Nomm.mean p _ q _ _ =>
    (efGo ft sub p).bind fun tok => (efGo ft sub q).map fun fol =>
      (fol.1, tok.2.1 && fol.2.1, tok.2.2 && fol.2.2)

/-- **`+eval-finalized`**: the flags of `b` from its nomm (`nm`, the nomms
of `acc`) and the flags written so far (`ft`, the flags of `acc`). -/
def evalFin (nm : Bell → Option Nomm) (ft : FlagTab) (b : Bell) : Option (Bool × Bool) :=
  (nm b).bind fun n => (efGo ft b.less n).map (·.2)

/-- One SCC of the loop: its members at `[| |]`, then each, in order, set
to `+eval-finalized` of the table so far. -/
def sccStep (nm : Bell → Option Nomm) (ft : FlagTab) (scc : List Bell) : Option FlagTab :=
  let ft1 : FlagTab := fun c => if c ∈ scc then some (false, false) else ft c
  scc.foldl (fun acc b => acc.bind fun f => (evalFin nm f b).map fun pt =>
    fun c => if c = b then some pt else f c) (some ft1)

/-- **The SCC loop** over a list of SCCs (callees first). -/
def sccLoop (nm : Bell → Option Nomm) (ft : FlagTab) : List (List Bell) → Option FlagTab
  | [] => some ft
  | s :: l => (sccStep nm ft s).bind fun ft' => sccLoop nm ft' l

/-- The noun `[pure total]` of a code entry's flags. -/
def flagNoun (p : Bool × Bool) : Noun := C (A (if p.1 then 0 else 1)) (A (if p.2 then 0 else 1))

end PokeF
end SkaModel
end Formalization
