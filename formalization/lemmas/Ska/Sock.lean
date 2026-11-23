import lemmas.Ska.Contract

/-!
# Capes and socks: the `+ca` and `+so` cores

Lean models of the arms of `+ca` (operations on capes) and `+so` (operations
on socks) near the top of `nock-compilation.hoon`, arm by arm.  An arm that
can crash returns an `Option`; `none` is the crash.  The `~+` memoization and
the `=(a b)` short cuts do not change what an arm computes, but the short cuts
are kept, since they are part of the case structure.

`+cap` and `+mas` of `hoon.hoon` crash on `0` and `1`; every arm here calls
them only on an axis of at least `2`, and `cap`, `mas` below are their values
there.

What the operations mean is in `SockFacts.lean`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Axes -/

/-- `+cap`: `2` if the axis is in the head, `3` if in the tail (for `a ≥ 2`). -/
def cap : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | a + 4 => cap ((a + 4) / 2)
decreasing_by omega

/-- `+mas`: the axis within the head or the tail (for `a ≥ 2`). -/
def mas : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | a + 4 => (a + 4) % 2 + mas ((a + 4) / 2) * 2
decreasing_by omega

theorem mas_lt : ∀ a, 2 ≤ a → mas a < a
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by simp [mas]
  | 3, _ => by simp [mas]
  | a + 4, _ => by
    have ih := mas_lt ((a + 4) / 2) (by omega)
    rw [mas]
    omega
decreasing_by omega

theorem mas_pos : ∀ a, 2 ≤ a → 1 ≤ mas a
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by simp [mas]
  | 3, _ => by simp [mas]
  | a + 4, _ => by
    have ih := mas_pos ((a + 4) / 2) (by omega)
    rw [mas]
    omega
decreasing_by omega

/-- `+con:ca`: the cons of two capes, `[| |]` normalized to `|`. -/
def Ca.con (h t : Cape) : Cape := if h = Cape.no ∧ t = Cape.no then Cape.no else Cape.cell h t

/-- `?=([%| *] s)`: a sock whose cape is `|`. -/
def Sock.isNo : Sock → Bool
  | Sock.mk Cape.no _ => true
  | _ => false

/-- The unknown sock, `*sock`: `[| ~]`. -/
def Sock.dunno : Sock := Sock.mk Cape.no (A 0)

/-! ## `+so`, the parts that `+ca` uses -/

namespace So

/-- `+knit:so`: the cons of two socks. -/
def knit (one two : Sock) : Sock :=
  match one, two with
  | Sock.mk l d1, Sock.mk r d2 =>
    let c := Ca.con l r
    if c = Cape.no then Sock.dunno else Sock.mk c (C d1 d2)
  | _, _ => Sock.void

/-- `+hed:so`. -/
def hed : Sock → Sock
  | Sock.void => Sock.void
  | Sock.mk c d =>
    match c, d with
    | Cape.no, _ => Sock.dunno
    | _, Noun.atom _ => Sock.dunno
    | Cape.yes, Noun.cell h _ => Sock.mk Cape.yes h
    | Cape.cell ch _, Noun.cell h _ => Sock.mk ch h

/-- `+tel:so`. -/
def tel : Sock → Sock
  | Sock.void => Sock.void
  | Sock.mk c d =>
    match c, d with
    | Cape.no, _ => Sock.dunno
    | _, Noun.atom _ => Sock.dunno
    | Cape.yes, Noun.cell _ t => Sock.mk Cape.yes t
    | Cape.cell _ ct, Noun.cell _ t => Sock.mk ct t

end So

/-! ## `+ca` -/

namespace Ca

/-- `+all:ca`: all is known. -/
def all : Cape → Bool
  | Cape.yes => true
  | Cape.no => false
  | Cape.cell h t => all h && all t

/-- `+hed:ca`. -/
def hed : Cape → Cape
  | Cape.cell h _ => h
  | c => c

/-- `+tel:ca`. -/
def tel : Cape → Cape
  | Cape.cell _ t => t
  | c => c

/-- The loop of `+yea:ca`, at the axis `axe`. -/
def yeaAt : Cape → Nat → List Nat
  | Cape.no, _ => []
  | Cape.yes, axe => [axe]
  | Cape.cell h t, axe => yeaAt h (axe * 2) ++ yeaAt t (axe * 2 + 1)

/-- `+yea:ca`: the list of known axes. -/
def yea (c : Cape) : List Nat := yeaAt c 1

/-- `+int:ca`: intersection. -/
def int (a b : Cape) : Cape :=
  if a = b then a else
  match a, b with
  | Cape.no, _ => Cape.no
  | Cape.yes, _ => b
  | Cape.cell _ _, Cape.no => Cape.no
  | Cape.cell _ _, Cape.yes => a
  | Cape.cell ah aT, Cape.cell bh bT => con (int ah bh) (int aT bT)

/-- `+app:ca`: apply a mask to a sock. -/
def app (c : Cape) (s : Sock) : Sock :=
  match s with
  | Sock.void => Sock.void
  | Sock.mk cs _ =>
    if c = cs then s
    else if c = Cape.no ∨ cs = Cape.no then Sock.dunno
    else
    match c with
    | Cape.yes => s
    | Cape.cell ch ct => So.knit (app ch (So.hed s)) (app ct (So.tel s))
    | Cape.no => s

/-- `+uni:ca`: union. -/
def uni (a b : Cape) : Cape :=
  if a = b then a else
  match a, b with
  | Cape.yes, _ => Cape.yes
  | Cape.no, _ => b
  | Cape.cell _ _, Cape.yes => Cape.yes
  | Cape.cell _ _, Cape.no => a
  | Cape.cell ah aT, Cape.cell bh bT => con (uni ah bh) (uni aT bT)

/-- The loop of `+pat:ca`. -/
def patLoop (c : Cape) (a : Nat) : Cape :=
  if _h : a ≤ 1 then c else
  if cap a = 2 then Cape.cell (patLoop c (mas a)) Cape.no
  else Cape.cell Cape.no (patLoop c (mas a))
termination_by a
decreasing_by all_goals exact mas_lt a (by omega)

/-- `+pat:ca`: push a cape to an axis.  A crash on axis `0`. -/
def pat (c : Cape) (a : Nat) : Option Cape :=
  if a = 0 then none else if c = Cape.no then some Cape.no else some (patLoop c a)

/-- `+dif:ca`: subtract `b` from `a`.  A crash where `a` is `&` and `b` a
cell. -/
def dif (a b : Cape) : Option Cape :=
  if a = b then some Cape.no else
  match a, b with
  | _, Cape.yes => some Cape.no
  | _, Cape.no => some a
  | Cape.no, _ => some Cape.no
  | Cape.yes, _ => none
  | Cape.cell ah aT, Cape.cell bh bT => do
      let l ← dif ah bh
      let r ← dif aT bT
      pure (con l r)

/-- `+lack:ca`: the parts of `a` that `b` does not know. -/
def lack (a b : Cape) : Cape :=
  match a, b with
  | Cape.no, _ => Cape.no
  | _, Cape.yes => Cape.no
  | _, Cape.no => a
  | a, Cape.cell bh bT =>
    if a = Cape.cell bh bT then Cape.no else con (lack (hed a) bh) (lack (tel a) bT)

/-- `+lot:ca`: the cape at an axis.  A crash on axis `0`. -/
def lot (c : Cape) (axe : Nat) : Option Cape :=
  if axe = 0 then none else some (lotLoop c axe)
where
  lotLoop (c : Cape) (axe : Nat) : Cape :=
    if axe ≤ 1 then c else
    match c with
    | Cape.cell ch ct => if cap axe = 2 then lotLoop ch (mas axe) else lotLoop ct (mas axe)
    | c => c
  termination_by axe
  decreasing_by all_goals exact mas_lt axe (by omega)

end Ca

/-! ## `+so` -/

namespace So

/-- `+huge:so` once neither sock is `%void`: does `[c2 d2]` nest under
`[c1 d1]`, does it know all that `[c1 d1]` knows?  `none` is a crash
(`badone`, and the two assertions on a cell of data). -/
def hugeMk (c1 : Cape) (d1 : Noun) (c2 : Cape) (d2 : Noun) : Option Bool :=
  if (c1 = c2 ∧ d1 = d2) then some true else
  match d1 with
  | Noun.atom _ =>
    match c1 with
    | Cape.cell _ _ => none
    | Cape.no => some true
    | Cape.yes => some (decide (c2 = Cape.yes ∧ d1 = d2))
  | Noun.cell d1h d1t =>
    match d2 with
    | Noun.atom _ =>
      match c2 with
      | Cape.cell _ _ => none
      | _ => if c1 = Cape.no then none else some false
    | Noun.cell d2h d2t =>
      (hugeMk (Ca.hed c1) d1h (Ca.hed c2) d2h).bind fun l =>
        if l then hugeMk (Ca.tel c1) d1t (Ca.tel c2) d2t else some false

/-- `+huge:so`: does `two` nest under `one`? -/
def huge (one two : Sock) : Option Bool :=
  match one, two with
  | Sock.void, Sock.void => some true
  | _, Sock.void => some true
  | Sock.void, _ => some false
  | Sock.mk c1 d1, Sock.mk c2 d2 => hugeMk c1 d1 c2 d2

/-- `+jibe:so` once neither sock is `%void`. -/
def jibeMk (c1 : Cape) (d1 : Noun) (c2 : Cape) (d2 : Noun) : Bool :=
  if (c1 = c2 ∧ d1 = d2) then true else
  if c1 = Cape.no ∨ c2 = Cape.no then true else
  if c1 = Cape.yes ∧ c2 = Cape.yes then decide (d1 = d2) else
  match d1, d2 with
  | Noun.cell d1h d1t, Noun.cell d2h d2t =>
    jibeMk (Ca.hed c1) d1h (Ca.hed c2) d2h && jibeMk (Ca.tel c1) d1t (Ca.tel c2) d2t
  | _, _ => false

/-- `+jibe:so`: do two socks agree wherever both know? -/
def jibe (one two : Sock) : Bool :=
  match one, two with
  | Sock.mk c1 d1, Sock.mk c2 d2 => jibeMk c1 d1 c2 d2
  | _, _ => false

/-- The loop of `+pull:so`. -/
def pullLoop (c : Cape) (d : Noun) (axe : Nat) : Sock :=
  if axe ≤ 1 then Sock.mk c d else
  if c = Cape.no then Sock.dunno else
  match d with
  | Noun.atom _ => Sock.dunno
  | Noun.cell dh dt =>
    match c with
    | Cape.cell ch ct => if cap axe = 2 then pullLoop ch dh (mas axe) else pullLoop ct dt (mas axe)
    | _ => if cap axe = 2 then pullLoop c dh (mas axe) else pullLoop c dt (mas axe)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- `+pull:so`: the sock at an axis.  A crash on axis `0`. -/
def pull (s : Sock) (axe : Nat) : Option Sock :=
  if axe = 0 then none else
  match s with
  | Sock.void => some Sock.void
  | Sock.mk c d => some (pullLoop c d axe)

/-- The depth of the cape of a sock: the measure of `+purr`. -/
def capeDepth : Cape → Nat
  | Cape.cell h t => max (capeDepth h) (capeDepth t) + 1
  | _ => 0

def depth : Sock → Nat
  | Sock.void => 0
  | Sock.mk c _ => capeDepth c

theorem depth_hed_le (s : Sock) : depth (hed s) ≤ depth s := by
  cases s with
  | void => simp [hed, depth]
  | mk c d =>
    cases c <;> cases d <;> simp [hed, depth, capeDepth, Sock.dunno] <;> omega

theorem depth_tel_le (s : Sock) : depth (tel s) ≤ depth s := by
  cases s with
  | void => simp [tel, depth]
  | mk c d =>
    cases c <;> cases d <;> simp [tel, depth, capeDepth, Sock.dunno] <;> omega

theorem depth_hed_lt {ch ct : Cape} {d : Noun} :
    depth (hed (Sock.mk (Cape.cell ch ct) d)) < depth (Sock.mk (Cape.cell ch ct) d) := by
  cases d <;> simp [hed, depth, capeDepth, Sock.dunno] <;> omega

theorem depth_tel_lt {ch ct : Cape} {d : Noun} :
    depth (tel (Sock.mk (Cape.cell ch ct) d)) < depth (Sock.mk (Cape.cell ch ct) d) := by
  cases d <;> simp [tel, depth, capeDepth, Sock.dunno] <;> omega

/-- The inner loop of `+purr:so`, where both capes are `&`. -/
def purrData (d1 d2 : Noun) : Sock :=
  if d1 = d2 then Sock.mk Cape.yes d1 else
  match d1, d2 with
  | Noun.cell a b, Noun.cell c d => knit (purrData a c) (purrData b d)
  | _, _ => Sock.dunno

/-- `+purr:so`: the meet of two socks, what both know and agree on. -/
def purr (one two : Sock) : Sock :=
  if one = two then one else
  match one, two with
  | Sock.void, _ => two
  | _, Sock.void => one
  | Sock.mk c1 d1, Sock.mk c2 d2 =>
    if c1 = Cape.no ∨ c2 = Cape.no then Sock.dunno else
    match c1, c2 with
    | Cape.yes, Cape.yes => purrData d1 d2
    | Cape.cell ch ct, c2 =>
      knit (purr (hed (Sock.mk (Cape.cell ch ct) d1)) (hed (Sock.mk c2 d2)))
        (purr (tel (Sock.mk (Cape.cell ch ct) d1)) (tel (Sock.mk c2 d2)))
    | c1, Cape.cell ch ct =>
      knit (purr (hed (Sock.mk c1 d1)) (hed (Sock.mk (Cape.cell ch ct) d2)))
        (purr (tel (Sock.mk c1 d1)) (tel (Sock.mk (Cape.cell ch ct) d2)))
    | _, _ => Sock.dunno
termination_by depth one + depth two
decreasing_by
  all_goals simp_wf
  · exact Nat.add_lt_add_of_lt_of_le depth_hed_lt (depth_hed_le _)
  · exact Nat.add_lt_add_of_lt_of_le depth_tel_lt (depth_tel_le _)
  · exact Nat.add_lt_add_of_le_of_lt (depth_hed_le _) depth_hed_lt
  · exact Nat.add_lt_add_of_le_of_lt (depth_tel_le _) depth_tel_lt

/-- The upward loop of `+darn:so`: the edited part knit back with the
siblings left on the way down. -/
def darnUp (two : Sock) : List (Nat × Sock) → Sock
  | [] => two
  | (2, s) :: acc => darnUp (knit two s) acc
  | (_, s) :: acc => darnUp (knit s two) acc

/-- The downward loop of `+darn:so`: it stops at the axis, or where both
socks are unknown.  A crash at axis `0` (`+cap`). -/
def darnDown (one : Sock) (axe : Nat) (two : Sock) (acc : List (Nat × Sock)) : Option Sock :=
  if axe = 1 ∨ (one.isNo ∧ two.isNo) then
    some (darnUp two acc)
  else if axe = 0 then none
  else if cap axe = 2 then darnDown (hed one) (mas axe) two ((2, tel one) :: acc)
  else darnDown (tel one) (mas axe) two ((3, hed one) :: acc)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- `+darn:so`: edit the sock `one` at `axe` with `two`. -/
def darn (one : Sock) (axe : Nat) (two : Sock) : Option Sock :=
  if axe = 1 then some two
  else if one = Sock.void ∨ two = Sock.void then some Sock.void
  else if one.isNo ∧ two.isNo then some Sock.dunno
  else darnDown one axe two []

end So

end SkaModel
end Formalization
