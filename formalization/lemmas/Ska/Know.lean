import lemmas.Ska.CallGraph
import lemmas.Ska.Bake

/-!
# `+know`: a function's nomm evaluated as socks under its bake

`+know` walks a nomm with the sock its variant's bell knows of the subject,
folds reads of fully known parts to literals (`%0`), and `%3`, `%4`, `%5`,
cons, `%7`, `%10` and trace, `%fast` and `%memo` hints of literals to
literals, takes the branch of a `%6` whose condition is known `0` or `1`, and
sends each direct call (and the call of a `%mean` hint) to the variant that
`res` names for its code bell and the sock `k` it knows of the callee's
subject, listing these sites.  A call's product is the code bell's datum's
product, patched for `k` (`dat`).  A fold drops a computation only when it is
safe (`+safe-nomm`).

`knowGo` is the model, arm by arm; `none` is a crash of the Hoon (only `res`
and `+darn:so` can crash here).  The provenance is kept as the Hoon keeps it,
for `+double-int`.  Not proved yet: that the folded nomm agrees with the
original on every subject that fits both the bake and the code requirement,
and that each site's subject fits its `k` (what `Bake.bakeOf_fits` needs).
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Bake

/-- A site: the callee's code bell and what the caller knows of its subject. -/
abbrev Site := Bell × Sock

/-- `?(hint-safe %fast %memo)`: the hints a literal can drop. -/
def hintFree (tag : Nat) : Bool := hintSafe tag || tag == Tag.fast || tag == Tag.memo

/-- A fully known sock's data: `?=(^ sock)` and `(all:ca cape)`. -/
def known : Sock → Option Noun
  | Sock.mk c d => if Ca.all c = true then some d else none
  | Sock.void => none

/-- The literal of a folded nomm, `?=([%1 *] nomm)`. -/
def lit : Nomm → Option Noun
  | Nomm.n1 p => some p
  | _ => none

/-- The product of a literal, `[&+x ~]`. -/
def litAnno (x : Noun) : Anno := ⟨Sock.mk Cape.yes x, A 0⟩

/-- `+know` on a nomm, the subject's sock-anno `sub` and the sites so far:
the folded nomm, its product, and the sites (latest first).  `fold` is the
`bake-mode` flag. -/
def knowGo (fold : Bool) (dat : Bell → Option Datum) (res : Bell → Sock → Option Bell) :
    Nomm → Anno → List Site → Option ((Nomm × Anno) × List Site)
  | Nomm.cons p q, sub, st =>
    (knowGo fold dat res p sub st).bind fun l =>
    (knowGo fold dat res q sub l.2).bind fun r =>
    match fold, lit l.1.1, lit r.1.1 with
    | true, some x, some y => some ((Nomm.n1 (C x y), litAnno (C x y)), r.2)
    | _, _, _ => some ((Nomm.cons l.1.1 r.1.1, ⟨So.knit l.1.2.sock r.1.2.sock, Pi.cons l.1.2.src r.1.2.src⟩), r.2)
  | Nomm.n0 p, sub, st =>
    if p = 0 then some ((Nomm.n0 p, Anno.dunno), st) else
    (if p = 1 then some sub else (So.pull sub.sock p).map fun s => (⟨s, Pi.slot sub.src p⟩ : Anno)).map fun prod =>
    match fold, known prod.sock with
    | true, some d => ((Nomm.n1 d, ⟨prod.sock, A 0⟩), st)
    | _, _ => ((Nomm.n0 p, prod), st)
  | Nomm.n1 p, _, st => some ((Nomm.n1 p, litAnno p), st)
  | Nomm.n2 p q info, sub, st =>
    (knowGo fold dat res p sub st).bind fun s =>
    (knowGo fold dat res q sub s.2).bind fun f =>
    match info with
    | none => some ((Nomm.n2 s.1.1 f.1.1 none, Anno.dunno), f.2)
    | some (b, mk) =>
      let k := s.1.2.sock
      (res b k).map fun v =>
      let prod : Anno := match dat b with
        | none => Anno.dunno
        | some d => let pp := patchProd d.prod d.map k; ⟨pp.sock, Pi.compose pp.src s.1.2.src⟩
      ((Nomm.n2 s.1.1 f.1.1 (some (v, mk)), prod), (b, k) :: f.2)
  | Nomm.n3 p, sub, st =>
    (knowGo fold dat res p sub st).map fun r =>
    match fold, known r.1.2.sock, safeNomm r.1.1 with
    | true, some d, true =>
      let pro := if isCellN d then 0 else 1
      ((Nomm.n1 (A pro), litAnno (A pro)), r.2)
    | _, _, _ => ((Nomm.n3 r.1.1, Anno.dunno), r.2)
  | Nomm.n4 p, sub, st =>
    (knowGo fold dat res p sub st).map fun r =>
    match fold, known r.1.2.sock, safeNomm r.1.1 with
    | true, some (Noun.atom a), true => ((Nomm.n1 (A (a + 1)), litAnno (A (a + 1))), r.2)
    | _, _, _ => ((Nomm.n4 r.1.1, Anno.dunno), r.2)
  | Nomm.n5 p q, sub, st =>
    (knowGo fold dat res p sub st).bind fun pp =>
    (knowGo fold dat res q sub pp.2).map fun qq =>
    match fold, known pp.1.2.sock, safeNomm pp.1.1, known qq.1.2.sock, safeNomm qq.1.1 with
    | true, some dp, true, some dq, true =>
      let pro := if dp = dq then 0 else 1
      ((Nomm.n1 (A pro), litAnno (A pro)), qq.2)
    | _, _, _, _, _ => ((Nomm.n5 pp.1.1 qq.1.1, Anno.dunno), qq.2)
  | Nomm.n6 p q r, sub, st =>
    (knowGo fold dat res p sub st).bind fun pp =>
    match fold, known pp.1.2.sock, safeNomm pp.1.1 with
    | true, some (Noun.atom 0), true => knowGo fold dat res q sub pp.2
    | true, some (Noun.atom 1), true => knowGo fold dat res r sub pp.2
    | _, _, _ =>
      (knowGo fold dat res q sub pp.2).bind fun qq =>
      (knowGo fold dat res r sub qq.2).map fun rr =>
      ((Nomm.n6 pp.1.1 qq.1.1 rr.1.1, doubleInt qq.1.2 rr.1.2), rr.2)
  | Nomm.n7 p q, sub, st =>
    (knowGo fold dat res p sub st).bind fun pp =>
    (knowGo fold dat res q pp.1.2 pp.2).map fun qq =>
    match fold, lit qq.1.1, safeNomm pp.1.1 with
    | true, some x, true => ((qq.1.1, litAnno x), qq.2)
    | _, _, _ => ((Nomm.n7 pp.1.1 qq.1.1, qq.1.2), qq.2)
  | Nomm.n10 ax don rec, sub, st =>
    (knowGo fold dat res don sub st).bind fun dn =>
    (knowGo fold dat res rec sub dn.2).bind fun rc =>
    let l : Option Noun := match fold, lit dn.1.1, lit rc.1.1 with
      | true, some x, some y => edit? ax x y
      | _, _, _ => none
    match l with
    | some u => some ((Nomm.n1 u, litAnno u), rc.2)
    | none =>
      (So.darn rc.1.2.sock ax dn.1.2.sock).map fun s =>
      ((Nomm.n10 ax dn.1.1 rc.1.1, ⟨s, Pi.edit rc.1.2.src ax dn.1.2.src⟩), rc.2)
  | Nomm.n11s tag q body, sub, st =>
    (knowGo fold dat res q sub st).map fun qq =>
    match fold, hintFree tag, lit qq.1.1 with
    | true, true, some x => ((qq.1.1, litAnno x), qq.2)
    | _, _, _ => ((Nomm.n11s tag qq.1.1 body, qq.1.2), qq.2)
  | Nomm.n11d tag h q body, sub, st =>
    (knowGo fold dat res h sub st).bind fun hh =>
    (knowGo fold dat res q sub hh.2).map fun qq =>
    match fold, hintFree tag, safeNomm hh.1.1, lit qq.1.1 with
    | true, true, true, some x => ((qq.1.1, litAnno x), qq.2)
    | _, _, _, _ => ((Nomm.n11d tag hh.1.1 qq.1.1 body, qq.1.2), qq.2)
  | Nomm.n12 p q, sub, st =>
    (knowGo fold dat res p sub st).bind fun pp =>
    (knowGo fold dat res q sub pp.2).map fun qq =>
    ((Nomm.n12 pp.1.1 qq.1.1, Anno.dunno), qq.2)
  | Nomm.mean p b q body k, sub, st =>
    (knowGo fold dat res p sub st).bind fun pp =>
    let kk := pp.1.2.sock
    (res b kk).bind fun v =>
    (knowGo fold dat res q sub ((b, kk) :: pp.2)).map fun qq =>
    ((Nomm.mean pp.1.1 v qq.1.1 body k, qq.1.2), qq.2)

/-- `+know`: the folded nomm and the sites, from the subject sock `sub`
(provenance `1`, the whole subject). -/
def know (fold : Bool) (nomm : Nomm) (sub : Sock) (dat : Bell → Option Datum)
    (res : Bell → Sock → Option Bell) : Option (Nomm × List Site) :=
  (knowGo fold dat res nomm ⟨sub, A 1⟩ []).map fun r => (r.1.1, r.2)

end Bake

end SkaModel
end Formalization
