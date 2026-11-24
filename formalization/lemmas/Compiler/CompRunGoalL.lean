import lemmas.Compiler.CompRunCall
import lemmas.Compiler.CompRunInvL
import lemmas.Compiler.CompCopyAll

/-!
# `+run` on lazy goals: the statement and the invariant

The cases of `+run` were linked on fork-free goals `CGoal.toL gl` only
(`CompRunCases.lean`, `CompRunCons.lean`, `CompRunCall.lean`), with results
that are fork-free (`CrRes`).  A cons, `%5`, `%10` or `%2` whose part that
runs first in Nock order calls makes `+past` park a need in a bond, so its
result has a bond, and the next run (`%7`, the head of a cons) runs for a
goal with a bond.  This file states the link on every lazy goal, with lazy
results.

## The statement

`CompRunAtC env ctx n goal region g` (`CompRunTwo.lean`) is already stated
for every `goal : CGoalL CSet`: the `$` arm of `+run` on the noun of `n` and
`goal`, from the state `g` and every rest `x` of the state with an empty
`soft`, is `runLC env msup n goal region g`, for every `msup`, `mono` and
Hoon `sup`.  The aim (`RunLinkL`): it holds for every nomm of the plain class
`PlainOk` (`%0`, `%1`, `%3`, `%4`, `%5`, `%7`, cons, `%10` with an axis not
`0`, and the indirect call `[2 p q ~]`, nested in any way, no `%6`) on every
goal and state with `GInv`, every region and every `env`.  What a run
returns meets `GRes` (`RunResL`), which gives `GInv` of the goal of the next
run (`%7`, the head of a cons) and the side condition of `+copy`.

## The invariant `GInv g goal`

* `%done`, `%pick z o`: the mode is `%run` (`g.drop = false`), the jumps'
  arguments below the counter.
* `%next laz th`: the same, and `LInv g.re g.bo laz`:
  - **looks**: no sure need of `laz` (forks and bonds to any depth) looks at
    axis `0` (`LAll (LNB ..)`, first half).  Read by `+from`, `+split`,
    `+into` (`WalkP lok0`) and, with an empty `soft`, by the walks of
    `+mede`, `+kern`, `+collapse-lazy-atom` (`WalkP mdP`, `walk_mdP`).
  - **registers below the counter**: every register of every sure need is
    below `g.re` (`LAll (LNB ..)`, second half).  Read by `+copy`
    (`CopyH`, first two parts).
  - **apartness**: no register occurs twice in `laz` (`(lregs laz).Nodup`,
    `lregs` lists the registers of every sure need in walk order).  It makes
    the two halves of `+split` and of `+into` apart (and so the goals of the
    two runs of a cons and of a `%10`), which is what `+copy` needs at the
    end (`CopyH`, third part, `LApart`): the result of a run is made of
    registers of its goal and fresh ones (`GRes`).
  - **keys**: at every level the forks' yes labels and the bonds' labels
    have no duplicate (`LKeys`).  `+copy-lazy` merges the entries of the
    second need into those of the first with the same label (`+malt`,
    `~(get by ..)`): with two entries of the first at one label the second
    need's entry would be copied twice, and the result would hold its
    registers twice.
  - **labels**: every label of `laz` is below `g.bo` (`llabs`), so the
    block that `+past` emits (`g.bo`) is a new key.
* **`soft`**: empty (`GenRest.NoSoft`, in `CompRunAtR` itself).  `+kern`,
  `+mede`, `+collapse-lazy-atom` read it through `mdP`.
* **`cond`**: no condition.  `+proxy` writes it and nothing in the cases of
  the plain class reads it.
* **tags of fork and bond blocks**: no condition for the link.  Only
  `+proxy` reads `tags`, with `~(got by tags)`, which crashes on a missing
  key exactly where the model's `proxy` is `none`, so the link holds with or
  without them.  They matter only for the model to succeed (the top
  theorem), not for the equation of the link.

## The result `GRes g goal g' nex`

The counters grow (`re`, `bo`), `GInv g' nex.goal` (so the mode stays, the
result's looks, registers, apartness, keys and labels hold at the new
counters), and every register of the result is fresh (`g.re ≤ r`) or one of
the goal's lazy need (`gregs`).

## Checks

The two runs of the session's brief, from `genAt 0 1` under `%done` with
the evaluable `FM` and `LS` of `Ska/CompCall.lean`: the cons
`[[2 [0 3] [0 2]] [0 1]]` (its result has one bond, at the block of `+past`)
and the Nock `[8 [9 2 [0 1]] [0 2]]`; `gresB` (the Boolean `GRes`) holds of
both results and `copyHB` (the Boolean `CopyH` at the counter) of the needs
each final `+copy` joins.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## Registers, keys, labels -/

section
variable {S : Type} [HoonSet S]

mutual
/-- The registers of every sure need of a lazy need, in walk order. -/
def lregs : Lazy S → List Nat
  | Lazy.mk s f b => flattenNeed s.ned ++ (fregs f ++ bregs b)

/-- The same over the forks. -/
def fregs : List (Lazy.ForkE S) → List Nat
  | [] => []
  | ((_, y), (_, n)) :: rest => lregs y ++ (lregs n ++ fregs rest)

/-- The same over the bonds. -/
def bregs : List (Nat × Lazy S) → List Nat
  | [] => []
  | (_, l) :: rest => lregs l ++ bregs rest
end

mutual
/-- The labels of every fork and bond of a lazy need, to any depth. -/
def llabs : Lazy S → List Nat
  | Lazy.mk _ f b => flabs f ++ blabs b

def flabs : List (Lazy.ForkE S) → List Nat
  | [] => []
  | ((oy, y), (on, n)) :: rest => oy :: on :: (llabs y ++ (llabs n ++ flabs rest))

def blabs : List (Nat × Lazy S) → List Nat
  | [] => []
  | (o, l) :: rest => o :: (llabs l ++ blabs rest)
end

mutual
/-- At every level, the yes labels of the forks and the labels of the bonds
have no duplicate. -/
def LKeys : Lazy S → Prop
  | Lazy.mk _ f b => (f.map fun e => e.1.1).Nodup ∧ (b.map fun e => e.1).Nodup ∧ FKeys f ∧ BKeys b

def FKeys : List (Lazy.ForkE S) → Prop
  | [] => True
  | ((_, y), (_, n)) :: rest => LKeys y ∧ LKeys n ∧ FKeys rest

def BKeys : List (Nat × Lazy S) → Prop
  | [] => True
  | (_, l) :: rest => LKeys l ∧ BKeys rest
end

/-- The registers of a goal's lazy need. -/
def gregs : CGoalL S → List Nat
  | CGoalL.next laz _ => lregs laz
  | _ => []

end

/-! ## The invariant and the result -/

/-- **The lazy part of the invariant**, at the register counter `kr` and the
label counter `kb`: looks and registers below `kr` (`LNB`), no register
twice, no key twice at a level, labels below `kb`. -/
def LInv (kr kb : Nat) (laz : Lazy CSet) : Prop :=
  LAll (LNB kr) laz ∧ (lregs laz).Nodup ∧ LKeys laz ∧ ∀ o ∈ llabs laz, o < kb

/-- **The invariant of a lazy goal and a state.** -/
def GInv (g : Gen (TreapMap mugF)) : CGoalL CSet → Prop
  | CGoalL.next laz th => LInv g.re g.bo laz ∧ g.drop = false ∧ JmpIn (· < g.re) th
  | CGoalL.pick z o => g.drop = false ∧ JmpIn (· < g.re) z ∧ JmpIn (· < g.re) o
  | CGoalL.done => g.drop = false

/-- **What a run returns from a goal with the invariant.** -/
def GRes (g : Gen (TreapMap mugF)) (goal : CGoalL CSet) (g' : Gen (TreapMap mugF)) (nex : NextL CSet) : Prop :=
  g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ GInv g' nex.goal ∧ ∀ r ∈ lregs nex.laz, g.re ≤ r ∨ r ∈ gregs goal

/-- **The plain class**: the pure constructors and the indirect call, nested
in any way, no `%6`, every `%10` axis not `0`. -/
def PlainOk : Nomm → Bool
  | Nomm.cons p q => PlainOk p && PlainOk q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q Option.none => PlainOk p && PlainOk q
  | Nomm.n3 p => PlainOk p
  | Nomm.n4 p => PlainOk p
  | Nomm.n5 p q => PlainOk p && PlainOk q
  | Nomm.n7 p q => PlainOk p && PlainOk q
  | Nomm.n10 a v q => a != 0 && PlainOk v && PlainOk q
  | _ => false

variable {ctx : Noun}

/-- **The aim: the run link on lazy goals.** -/
def RunLinkL (ctx : Noun) : Prop :=
  ∀ (env : CallEnv) (n : Nomm), PlainOk n = true → ∀ (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)), GInv g goal → CompRunAtC env ctx n goal region g

/-- **The aim: what the runs return.** -/
def RunResL : Prop :=
  ∀ (env : CallEnv) (n : Nomm), PlainOk n = true → ∀ (msup : Option Nomm) (goal : CGoalL CSet)
    (region : List Nat) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), GInv g goal →
    runLC env msup n goal region g = some (nex, g') → GRes g goal g' nex

/-! ## The registers of a lazy need against `LAll` -/

theorem mem_flat : ∀ (n : Need) (x : Nat), x ∈ flattenNeed n ↔ NMem n x
  | Need.none, x => by simp [flattenNeed, NMem]
  | Need.this r, x => by simp [flattenNeed, NMem]
  | Need.pair p q, x => by simp [flattenNeed, NMem, mem_flat p x, mem_flat q x]
  | Need.both r p q, x => by simp [flattenNeed, NMem, mem_flat p x, mem_flat q x]

theorem distinct_iff_nodup : ∀ n : Need, Distinct n ↔ (flattenNeed n).Nodup
  | Need.none => by simp [Distinct, flattenNeed]
  | Need.this r => by simp [Distinct, flattenNeed]
  | Need.pair p q => by
    simp only [Distinct, flattenNeed, List.nodup_append, distinct_iff_nodup p, distinct_iff_nodup q]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, b, fun x hx y hy e => c x ((mem_flat p x).1 hx) (e ▸ (mem_flat q y).1 hy)⟩
    · rintro ⟨a, b, c⟩; exact ⟨a, b, fun x hx hy => c x ((mem_flat p x).2 hx) x ((mem_flat q x).2 hy) rfl⟩
  | Need.both r p q => by
    simp only [Distinct, flattenNeed, List.nodup_cons, List.nodup_append, List.mem_append, distinct_iff_nodup p,
      distinct_iff_nodup q, not_or, mem_flat]
    constructor
    · rintro ⟨a, b, c, d, e⟩; exact ⟨⟨d, e⟩, a, b, fun x hx y hy h => c x hx (h ▸ hy)⟩
    · rintro ⟨⟨d, e⟩, a, b, c⟩; exact ⟨a, b, fun x hx hy => c x hx x hy rfl, d, e⟩

mutual
/-- `LAll` of a predicate on the registers is the predicate on `lregs`. -/
theorem lall_regs (Q : Nat → Prop) : ∀ laz : Lazy CSet,
    (∀ r ∈ lregs laz, Q r) → LAll (fun t => ∀ r, NMem t.ned r → Q r) laz
  | Lazy.mk s f b, h => by
    simp only [lregs, List.mem_append] at h
    exact ⟨fun r hr => h r (Or.inl ((mem_flat _ r).2 hr)),
      fregs_walk Q f fun r hr => h r (Or.inr (Or.inl hr)), bregs_walk Q b fun r hr => h r (Or.inr (Or.inr hr))⟩

theorem fregs_walk (Q : Nat → Prop) : ∀ f : List (Lazy.ForkE CSet),
    (∀ r ∈ fregs f, Q r) → WalkPF (fun _ t => ∀ r, NMem t.ned r → Q r) f
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, h => by
    simp only [fregs, List.mem_append] at h
    refine ⟨?_, ?_, fregs_walk Q rest fun r hr => h r (Or.inr (Or.inr hr))⟩
    · rw [walkP_irrel]; exact lall_regs Q y fun r hr => h r (Or.inl hr)
    · rw [walkP_irrel]; exact lall_regs Q n fun r hr => h r (Or.inr (Or.inl hr))

theorem bregs_walk (Q : Nat → Prop) : ∀ b : List (Nat × Lazy CSet),
    (∀ r ∈ bregs b, Q r) → WalkPB (fun _ t => ∀ r, NMem t.ned r → Q r) b
  | [], _ => trivial
  | (o, l) :: rest, h => by
    simp only [bregs, List.mem_append] at h
    refine ⟨?_, bregs_walk Q rest fun r hr => h r (Or.inr hr)⟩
    rw [walkP_irrel]; exact lall_regs Q l fun r hr => h r (Or.inl hr)
end

mutual
/-- The converse: a register of `lregs` meets every predicate that `LAll`
puts on the registers. -/
theorem regs_lall (Q : Nat → Prop) : ∀ laz : Lazy CSet,
    LAll (fun t => ∀ r, NMem t.ned r → Q r) laz → ∀ r ∈ lregs laz, Q r
  | Lazy.mk s f b, ⟨hs, hf, hb⟩, r, hr => by
    simp only [lregs, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · exact hs r ((mem_flat _ r).1 hr)
    · exact fregs_lall Q f hf r hr
    · exact bregs_lall Q b hb r hr

theorem fregs_lall (Q : Nat → Prop) : ∀ f : List (Lazy.ForkE CSet),
    WalkPF (fun _ t => ∀ r, NMem t.ned r → Q r) f → ∀ r ∈ fregs f, Q r
  | [], _, r, hr => by simp [fregs] at hr
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hrest⟩, r, hr => by
    simp only [fregs, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · rw [walkP_irrel] at hy; exact regs_lall Q y hy r hr
    · rw [walkP_irrel] at hn; exact regs_lall Q n hn r hr
    · exact fregs_lall Q rest hrest r hr

theorem bregs_lall (Q : Nat → Prop) : ∀ b : List (Nat × Lazy CSet),
    WalkPB (fun _ t => ∀ r, NMem t.ned r → Q r) b → ∀ r ∈ bregs b, Q r
  | [], _, r, hr => by simp [bregs] at hr
  | (o, l) :: rest, ⟨hl, hrest⟩, r, hr => by
    simp only [bregs, List.mem_append] at hr
    rcases hr with hr | hr
    · rw [walkP_irrel] at hl; exact regs_lall Q l hl r hr
    · exact bregs_lall Q rest hrest r hr
end

/-- The registers below the counter, from `LNB`. -/
theorem lnb_regs {k : Nat} {laz : Lazy CSet} (h : LAll (LNB k) laz) : ∀ r ∈ lregs laz, r < k :=
  regs_lall (· < k) laz (lall_mono (fun _ hs => hs.2) h)

/-- **`CopyH` from the registers**: both needs below the counter, no register
in both. -/
theorem copyH_of_regs {k : Nat} {f s : Lazy CSet} (hf : ∀ r ∈ lregs f, r < k) (hs : ∀ r ∈ lregs s, r < k)
    (ap : ∀ r ∈ lregs f, r ∉ lregs s) : CopyH k f s := by
  refine ⟨lall_mono (fun _ h => h) (lall_regs (· < k) f hf), lall_mono (fun _ h => h) (lall_regs (· < k) s hs),
    fun r => ?_⟩
  by_cases hr : r ∈ lregs f
  · exact Or.inr (lall_mono (fun t h e => h r e rfl) (lall_regs (fun x => x ≠ r) s fun x hx e => ap r hr (e ▸ hx)))
  · exact Or.inl (lall_mono (fun t h e => h r e rfl) (lall_regs (fun x => x ≠ r) f fun x hx e => hr (e ▸ hx)))

/-- The root need of a lazy need with no register twice has none twice. -/
theorem distinct_root {laz : Lazy CSet} (h : (lregs laz).Nodup) : Distinct laz.sure.ned := by
  obtain ⟨s, f, b⟩ := laz
  simp only [lregs, List.nodup_append] at h
  exact (distinct_iff_nodup _).2 h.1

/-- `GInv` on a `%next` goal gives `CrInvL` (the invariant of the links of
the helpers). -/
theorem crInvL_of_gInv {g : Gen (TreapMap mugF)} {laz : Lazy CSet} {th : Jmp}
    (h : GInv g (CGoalL.next laz th)) : CrInvL g (CGoalL.next laz th) :=
  ⟨h.1.1, h.2.1, h.2.2, distinct_root h.1.2.1⟩

/-! ## Checks on two runs

Boolean forms of `GRes` and `CopyH` over the evaluable `FM` and `LS` of
`Ska/CompCall.lean`, and the runs of the brief from `genAt 0 1` under
`%done` with an environment for indirect calls (`envI`: no callee, `+hinted`
reads nothing). -/

section
variable {S : Type} [HoonSet S]

mutual
def lallB (q : Sure S → Bool) : Lazy S → Bool
  | Lazy.mk s f b => q s && lallBF q f && lallBB q b

def lallBF (q : Sure S → Bool) : List (Lazy.ForkE S) → Bool
  | [] => true
  | ((_, y), (_, n)) :: rest => lallB q y && lallB q n && lallBF q rest

def lallBB (q : Sure S → Bool) : List (Nat × Lazy S) → Bool
  | [] => true
  | (_, l) :: rest => lallB q l && lallBB q rest
end

mutual
def lkeysB : Lazy S → Bool
  | Lazy.mk _ f b => (f.map fun e => e.1.1).Nodup && (b.map fun e => e.1).Nodup && fkeysB f && bkeysB b

def fkeysB : List (Lazy.ForkE S) → Bool
  | [] => true
  | ((_, y), (_, n)) :: rest => lkeysB y && lkeysB n && fkeysB rest

def bkeysB : List (Nat × Lazy S) → Bool
  | [] => true
  | (_, l) :: rest => lkeysB l && bkeysB rest
end

def jmpInB (k : Nat) (j : Jmp) : Bool := j.args.all fun a => match a with | some x => x < k | Option.none => true

/-- `LInv` as a test. -/
def linvB (kr kb : Nat) (laz : Lazy S) : Bool :=
  lallB (fun s => (HoonSet.toList s.lok).all (· != 0) && (flattenNeed s.ned).all (· < kr)) laz &&
    (lregs laz).Nodup && lkeysB laz && (llabs laz).all (· < kb)

/-- `GRes` as a test. -/
def gresB {Map : Type → Type} [HoonMap Map] (g : Gen Map) (goal : CGoalL S) (g' : Gen Map) (nex : NextL S) : Bool :=
  decide (g.re ≤ g'.re) && decide (g.bo ≤ g'.bo) && linvB g'.re g'.bo nex.laz && !g'.drop &&
    jmpInB g'.re nex.th && (lregs nex.laz).all fun r => decide (g.re ≤ r) || (gregs goal).contains r

/-- `CopyH` as a test. -/
def copyHB (k : Nat) (f s : Lazy S) : Bool :=
  (lregs f).all (· < k) && (lregs s).all (· < k) && (lregs f).all fun r => !(lregs s).contains r

end

/-- An environment for indirect calls: no callee. -/
def envI : CallEnv :=
  ⟨fun _ => Option.none, fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => Option.none,
   fun _ _ _ _ _ => false⟩

/-- The run of a nomm under `%done` from `genAt 0 1`: the result and the
state. -/
def runDone (n : Nomm) : Option (NextL LS × Gen FM) :=
  runLC (S := LS) (Map := FM) envI Option.none n CGoalL.done [] (genAt 0 1)

/-- The cons of the brief, `[[2 [0 3] [0 2]] [0 1]]`. -/
def consCall : Nomm := Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)

/-- The Nock `[8 [9 2 [0 1]] [0 2]]`: `[7 [[7 [0 1] [2 [0 1] [0 2]]] [0 1]] [0 2]]`. -/
def eightNine : Nomm :=
  Nomm.n7 (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) (Nomm.n0 1)) (Nomm.n0 2)

/-- The cons under `%done`, step by step: the `+split` of the fresh
register's goal, the run of the tail, its `+past` over the calling head (a
bond), the run of the head, and the two needs the `+copy` joins. -/
def consSteps (p q : Nomm) (laz : Lazy LS) (th : Jmp) (g : Gen FM) :
    Option ((Lazy LS × Lazy LS × Lazy LS × Lazy LS) × Gen FM) :=
  ((do
    let (hed, tel, o) ← splitL ⟨laz, th⟩
    let nexh ← pastL envI.cod ⟨hed, jmp0 o⟩ q []
    let nex2 ← runLC envI Option.none q (CGoalL.next tel nexh.th) []
    let nex2 ← pastL envI.cod nex2 p []
    let nex1 ← runLC envI Option.none p (CGoalL.next nexh.laz nex2.th) []
    pure (hed, tel, nex1.laz, nex2.laz) : CM FM _) g)

/-- `[7 [[2 [0 3] [0 2]] [0 1]] [[0 2] [0 3]]]`: the cons `[[0 2] [0 3]]` runs for
the goal that the calling cons returns, which has a bond. -/
def sevenCons : Nomm := Nomm.n7 consCall (Nomm.cons (Nomm.n0 2) (Nomm.n0 3))

/-- `[[[0 2] [0 3]] [2 [0 3] [0 2]]]`: the head runs for the goal that `+past`
makes over the calling tail, which has a bond. -/
def nestCons : Nomm := Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)

/-- The number of bonds of the result under `%done` and `GRes`. -/
def checkDone (n : Nomm) : Option (Nat × Bool) :=
  (runDone n).map fun r => (r.1.laz.bond.length, gresB (genAt 0 1) (CGoalL.done : CGoalL LS) r.2 r.1)

-- The cons of the brief: its result has one bond (the tail's need, parked by
-- `+past` over the calling head), and it meets `GRes`.
#guard checkDone consCall == some (1, true)

-- Its `+copy` joins two needs that meet `CopyH` at the counter, the second
-- with the bond.
#guard (consSteps (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1) (Lazy.ofSure (lazyReg 0)) (jmp0 1)
    { genAt 1 2 with blocks := HoonMap.put (genAt 1 2).blocks 1 ⟨[], [], Termin.don 0⟩ }).map
  (fun r => (r.1.2.2.2.bond.length, copyHB r.2.re r.1.2.2.1 r.1.2.2.2)) == some (1, true)

-- `[8 [9 2 [0 1]] [0 2]]`: its result meets `GRes`.  It has no bond: the
-- tail `[0 1]` of the inner cons runs for the tail of `[%pair [%this 0] ~]`,
-- which asks nothing, so `+past` keeps it.
#guard checkDone eightNine == some (0, true)

-- The inner cons of `[8 [9 2 [0 1]] [0 2]]`, for the goal that `[0 2]`
-- returns: its `+copy` meets `CopyH`.
#guard (consSteps (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) (Nomm.n0 1)
    (Lazy.ofSure ⟨Need.pair (Need.this 0) Need.none, HoonSet.empty⟩) (jmp0 1)
    { genAt 1 2 with blocks := HoonMap.put (genAt 1 2).blocks 1 ⟨[], [], Termin.don 0⟩ }).map
  (fun r => copyHB r.2.re r.1.2.2.1 r.1.2.2.2) == some true

-- Runs for goals with a bond meet `GRes`.
#guard checkDone sevenCons == some (1, true)
#guard checkDone nestCons == some (1, true)

end Compiler
end Formalization
