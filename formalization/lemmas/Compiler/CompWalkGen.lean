import lemmas.Compiler.CompMedeLink
import lemmas.Hoon.RollUni

/-!
# `+walk-lazy` on every lazy need

`+walk-lazy` (door axis `30`, `comp_wl_at`, battery `wlBat` of
`CompMedeLink.lean`) runs on the core

    [wlBat [[o [laz f]] [door [gen ctx]]]]

with `o` at `12`, `laz` at `26` (`sure` at `52`, `fork` at `106`, `bond` at
`107`), the gate `f` at `27` and the door's `gen` at `30`.  Its Nock, in
order:

1. `=.  gen  (f o sure.laz gen)`: the gate slammed on `[o sure gen]`, its
   product put at `30`;
2. `?:  &(?=(~ fork.laz) ?=(~ bond.laz))  gen`;
3. `=.  gen  (roll fork.laz ..)`: `+roll` of layer 2 over the forks, with the
   gate `wlFG` whose sample is `[[y n] gen]` and whose context is the walk
   core: it runs the walk core with `o.y`, `laz.y` and its `gen` put at `12`,
   `26`, `30`, then again with `o.n`, `laz.n` and the product;
4. `(roll bond.laz ..)`: the same with the gate `wlBG` over the bonds.

The bunts of the roll gates' samples run the mold `need-lazy` of the types
core (`CompMold ctx 191`); the roll replaces them before they are read.

The model is `walkLazy` of `Ska/CompLazyArms.lean`: `f o s`, then (unless
both lists are empty) `walkForks` (each fork's yes need, then its no need)
and `walkBonds`.  The order of the gate's calls, of the forks and bonds, and
of the state threading agree with the Hoon: no departure.

**The generic link** `comp_walk_lazy_all`: for any gate `[Fb [Fs Fc]]` that
is the model's `f` on the state noun at every visited pair of a block and a
sure need that meets a predicate `P` (`WalkP P o laz`: every pair the walk
visits meets `P`), the walk is `walkLazy f o laz` on every lazy need, with
forks and bonds to any depth.  The state's rest `x` (`cache`, `soft`,
`sofs`) is the one the gate keeps.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## The Nock -/

/-- The gate of the `+roll` over the forks: `walk(gen gen, laz laz.y, o
o.y)`, then the same on `n`. -/
def wlFG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 13) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 13))) (C (A 10) (C (C (A 26) (C (A 0) (A 49))) (C (A 10) (C (C (A 12) (C (A 0) (A 48))) (C (A 0) (A 7))))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 13))) (C (A 10) (C (C (A 26) (C (A 0) (A 51))) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 7))))))))))))

/-- The gate of the `+roll` over the bonds: `walk(gen gen, laz laz, o o)`. -/
def wlBG : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 13))) (C (A 10) (C (C (A 26) (C (A 0) (A 25))) (C (A 10) (C (C (A 12) (C (A 0) (A 24))) (C (A 0) (A 7))))))))))

/-- `wlBat` with its two roll gates named. -/
def wlBatS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 0) (A 27)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 0) (A 116)) (C (A 0) (A 62))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 106)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 107)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 30))) (C (C (A 1) wlFG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 30))) (C (C (A 1) wlBG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))))))

theorem wlBat_eq : wlBat = wlBatS := by kernel_rfl

/-- The walk core: the battery, the sample `[o [laz f]]`, the door, its
`gen`, the context. -/
def wlC (ctx : Noun) (o : Nat) (L F D G : Noun) : Noun :=
  C wlBat (C (C (A o) (C L F)) (C D (C G ctx)))

/-- The noun of a fork entry. -/
noncomputable def forkE (e : Lazy.ForkE CSet) : Noun := C (C (A e.1.1) e.1.2.toNoun) (C (A e.2.1) e.2.2.toNoun)

/-- The noun of a bond entry. -/
noncomputable def bondE (e : Nat × Lazy CSet) : Noun := C (A e.1) e.2.toNoun

theorem forksNoun_eq : ∀ fk : List (Lazy.ForkE CSet), Lazy.forksNoun fk = listN (fk.map forkE)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [Lazy.forksNoun, List.map_cons, listN, appendN_cons, forkE]
    rw [forksNoun_eq rest]; rfl

theorem bondsNoun_eq : ∀ bd : List (Nat × Lazy CSet), Lazy.bondsNoun bd = listN (bd.map bondE)
  | [] => rfl
  | (o, l) :: rest => by
    simp only [Lazy.bondsNoun, List.map_cons, listN, appendN_cons, bondE]
    rw [bondsNoun_eq rest]; rfl

/-- `+roll` of layer 2 with any gate: the fold of its slams. -/
theorem roll_gate_N (c bp e acc bc : Noun) (l : List Noun) :
    nock (C roll.battery (C (C (listN l) (C bp (C (C e acc) bc))) c)) roll.battery
      = l.foldlM (fun acc x => nock (C bp (C (C x acc) bc)) bp) acc :=
  roll_gate_M c bp e acc bc _ l (fun _ _ _ => rfl)

/-- The fork gate on a fork entry: the walk of the yes need, then of the no
need, whatever walk core it was made in. -/
theorem wl_fgate (F D G' L' : Noun) (o' oy on : Nat) (ly ln acc : Noun) :
    nock (C wlFG (C (C (C (C (A oy) ly) (C (A on) ln)) acc) (wlC ctx o' L' F D G'))) wlFG
      = (nock (wlC ctx oy ly F D acc) wlBat).bind fun a1 => nock (wlC ctx on ln F D a1) wlBat := by
  unfold wlFG wlC
  cases h : nock (C wlBat (C (C (A oy) (C ly F)) (C D (C acc ctx)))) wlBat with
  | none => simp [nock_exec, h]
  | some a1 => simp [nock_exec, h]

/-- The bond gate on a bond entry: the walk of its need. -/
theorem wl_bgate (F D G' L' : Noun) (o' ob : Nat) (lb acc : Noun) :
    nock (C wlBG (C (C (C (A ob) lb) acc) (wlC ctx o' L' F D G'))) wlBG
      = nock (wlC ctx ob lb F D acc) wlBat := by
  unfold wlBG wlC
  simp [nock_exec]

/-- `+roll` over `~` returns the first accumulator. -/
theorem roll_gate_nil' (c bp e acc bc : Noun) :
    nock (C roll.battery (C (C (A 0) (C bp (C (C e acc) bc))) c)) roll.battery = some acc :=
  roll_gate_N c bp e acc bc []

theorem wl_zero_ne (l : List Noun) (h : l ≠ []) : (A 0 = listN l) = False := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [listN]

theorem wl_eq_nil (l : List Noun) (h : l ≠ []) : eqCode (A 0) (listN l) = A 1 := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp [eqCode, listN]

/-- **One step of the walk**: the gate on `[o s gen]`, then, unless both
lists are empty, the roll of `wlFG` over the forks and of `wlBG` over the
bonds, each in the walk core with the `gen` it has reached. -/
theorem wl_step (hc : CompIn ctx) (hm : CompMold ctx 191) (o : Nat) (s : Sure CSet)
    (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) (Fb Fs Fc D G : Noun) :
    nock (wlC ctx o (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C Fb (C Fs Fc)) D G) wlBat
      = (nock (C Fb (C (C (A o) (C s.toNoun G)) Fc)) Fb).bind fun G1 =>
        if fk = [] ∧ bd = [] then some G1 else
        ((fk.map forkE).foldlM (fun acc y => nock (C wlFG (C (C y acc)
          (wlC ctx o (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C Fb (C Fs Fc)) D G1))) wlFG)
          G1).bind fun G2 =>
        (bd.map bondE).foldlM (fun acc y => nock (C wlBG (C (C y acc)
          (wlC ctx o (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C Fb (C Fs Fc)) D G2))) wlBG)
          G2 := by
  obtain ⟨Q, a, M, m, v, hQ, ha, hM, hmm, hv⟩ := hm
  unfold wlC
  conv => { lhs; arg 2; rw [wlBat_eq]; unfold wlBatS }
  cases h1 : nock (C Fb (C (C (A o) (C s.toNoun G)) Fc)) Fb with
  | none =>
    simp [nock_exec, h1]
  | some G1 =>
    by_cases hfk : fk = []
    · by_cases hbd : bd = []
      · subst hfk; subst hbd
        simp [nock_exec, h1, listN]
      · have hb : bd.map bondE ≠ [] := by simpa using hbd
        subst hfk
        simp [nock_exec, h1, hbd, wl_eq_nil _ hb, wl_zero_ne _ hb, hc, roll.arm_at, roll_arm, hQ, ha, hM, hmm, hv,
          roll_gate_N, roll_gate_nil', Option.bind_assoc]
    · have hf : fk.map forkE ≠ [] := by simpa using hfk
      simp [nock_exec, h1, hfk, wl_eq_nil _ hf, wl_zero_ne _ hf, hc, roll.arm_at, roll_arm, hQ, ha, hM, hmm, hv,
        roll_gate_N, roll_gate_nil', Option.bind_assoc]

/-! ## The walk -/

/-- The fold of the fork gate over the fork entries: each entry's yes need,
then its no need, walked in turn. -/
theorem wl_fold_forks (F D L G1 : Noun) (o : Nat) (fk : List (Lazy.ForkE CSet)) (a : Noun) :
    (fk.map forkE).foldlM (fun acc y => nock (C wlFG (C (C y acc) (wlC ctx o L F D G1))) wlFG) a
    = fk.foldlM (fun acc e => (nock (wlC ctx e.1.1 e.1.2.toNoun F D acc) wlBat).bind fun a1 =>
        nock (wlC ctx e.2.1 e.2.2.toNoun F D a1) wlBat) a := by
  rw [List.foldlM_map]
  congr 1
  funext acc e
  exact wl_fgate (ctx := ctx) F D G1 L o e.1.1 e.2.1 e.1.2.toNoun e.2.2.toNoun acc

/-- The fold of the bond gate over the bond entries. -/
theorem wl_fold_bonds (F D L G2 : Noun) (o : Nat) (bd : List (Nat × Lazy CSet)) (a : Noun) :
    (bd.map bondE).foldlM (fun acc y => nock (C wlBG (C (C y acc) (wlC ctx o L F D G2))) wlBG) a
    = bd.foldlM (fun acc e => nock (wlC ctx e.1 e.2.toNoun F D acc) wlBat) a := by
  rw [List.foldlM_map]
  congr 1
  funext acc e
  exact wl_bgate (ctx := ctx) F D G2 L o e.1 e.2.toNoun acc

mutual
/-- Every pair of a block and a sure need that `+walk-lazy` visits from `o`
on `laz` meets `P`. -/
def WalkP (P : Nat → Sure CSet → Prop) : Nat → Lazy CSet → Prop
  | o, Lazy.mk s fk bd => P o s ∧ WalkPF P fk ∧ WalkPB P bd

/-- The same over the forks. -/
def WalkPF (P : Nat → Sure CSet → Prop) : List (Lazy.ForkE CSet) → Prop
  | [] => True
  | ((oy, y), (on, n)) :: rest => WalkP P oy y ∧ WalkP P on n ∧ WalkPF P rest

/-- The same over the bonds. -/
def WalkPB (P : Nat → Sure CSet → Prop) : List (Nat × Lazy CSet) → Prop
  | [] => True
  | (ob, l) :: rest => WalkP P ob l ∧ WalkPB P rest
end

theorem lazy_toNoun_mk (s : Sure CSet) (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) :
    (Lazy.mk s fk bd).toNoun = C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))) := by
  simp only [Lazy.toNoun, forksNoun_eq, bondsNoun_eq]

section
variable (hc : CompIn ctx) (hm : CompMold ctx 191) (x : GenRest) (Fb Fs Fc D : Noun)
  (f : Nat → Sure CSet → CM (TreapMap mugF) Unit) (P : Nat → Sure CSet → Prop)
  (hf : ∀ o s g, P o s → nock (C Fb (C (C (A o) (C s.toNoun (genNoun g x))) Fc)) Fb
    = (f o s g).map fun p => genNoun p.2 x)
include hc hm hf

mutual
theorem wl_all : ∀ (laz : Lazy CSet) (o : Nat) (g : Gen (TreapMap mugF)), WalkP P o laz →
    nock (wlC ctx o laz.toNoun (C Fb (C Fs Fc)) D (genNoun g x)) wlBat
      = (Lazy.walkLazy f o laz g).map fun p => genNoun p.2 x
  | Lazy.mk s fk bd, o, g, ⟨hs, hfk, hbd⟩ => by
    rw [lazy_toNoun_mk, wl_step hc hm, hf o s g hs]
    simp only [wl_fold_forks, wl_fold_bonds]
    cases e1 : f o s g with
    | none => simp [Lazy.walkLazy, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, g1⟩ := p
      by_cases hfb : fk = [] ∧ bd = []
      · obtain ⟨rfl, rfl⟩ := hfb
        simp [Lazy.walkLazy, e1, bind, StateT.bind, pure, StateT.pure]
      · have hne : ¬ (fk.isEmpty = true ∧ bd.isEmpty = true) := by
          simpa [List.isEmpty_iff] using hfb
        simp only [Option.map_some, Option.bind_some, hfb, if_false]
        rw [wl_forks fk g1 hfk]
        cases e2 : Lazy.walkForks f fk g1 with
        | none => simp [Lazy.walkLazy, e1, e2, bind, StateT.bind, hfb]
        | some q =>
          obtain ⟨u2, g2⟩ := q
          simp only [Option.map_some, Option.bind_some]
          rw [wl_bonds bd g2 hbd]
          simp [Lazy.walkLazy, e1, e2, bind, StateT.bind, hfb]

theorem wl_forks : ∀ (fk : List (Lazy.ForkE CSet)) (g : Gen (TreapMap mugF)), WalkPF P fk →
    fk.foldlM (fun acc e => (nock (wlC ctx e.1.1 e.1.2.toNoun (C Fb (C Fs Fc)) D acc) wlBat).bind fun a1 =>
        nock (wlC ctx e.2.1 e.2.2.toNoun (C Fb (C Fs Fc)) D a1) wlBat) (genNoun g x)
      = (Lazy.walkForks f fk g).map fun p => genNoun p.2 x
  | [], g, _ => by simp [Lazy.walkForks, pure, StateT.pure]
  | ((oy, y), (on, n)) :: rest, g, ⟨hy, hn, hr⟩ => by
    simp only [List.foldlM_cons]
    rw [wl_all y oy g hy]
    cases e1 : Lazy.walkLazy f oy y g with
    | none => simp [Lazy.walkForks, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, g1⟩ := p
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
      rw [wl_all n on g1 hn]
      cases e2 : Lazy.walkLazy f on n g1 with
      | none => simp [Lazy.walkForks, e1, e2, bind, StateT.bind]
      | some q =>
        obtain ⟨u2, g2⟩ := q
        simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
        rw [wl_forks rest g2 hr]
        simp [Lazy.walkForks, e1, e2, bind, StateT.bind]

theorem wl_bonds : ∀ (bd : List (Nat × Lazy CSet)) (g : Gen (TreapMap mugF)), WalkPB P bd →
    bd.foldlM (fun acc e => nock (wlC ctx e.1 e.2.toNoun (C Fb (C Fs Fc)) D acc) wlBat) (genNoun g x)
      = (Lazy.walkBonds f bd g).map fun p => genNoun p.2 x
  | [], g, _ => by simp [Lazy.walkBonds, pure, StateT.pure]
  | (ob, l) :: rest, g, ⟨hl, hr⟩ => by
    simp only [List.foldlM_cons]
    rw [wl_all l ob g hl]
    cases e1 : Lazy.walkLazy f ob l g with
    | none => simp [Lazy.walkBonds, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, g1⟩ := p
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
      rw [wl_bonds rest g1 hr]
      simp [Lazy.walkBonds, e1, bind, StateT.bind]
end

/-- **`+walk-lazy` on every lazy need** (forks and bonds to any depth): for a
gate `[Fb [Fs Fc]]` that computes the model's `f` on the state noun at every
pair of a block and a sure need that meets `P`, the walk from `o` on `laz`,
when every pair it visits meets `P` (`WalkP`), is `walkLazy f o laz`, on
every door `D` and state `g` (the rest `x` of the state is the one the gate
keeps).  The walk reads of the context layer 2 (`+roll`, `CompIn`) and the
mold `need-lazy` (`CompMold ctx 191`, the bunts of the roll gates). -/
theorem comp_walk_lazy_all (laz : Lazy CSet) (o : Nat) (g : Gen (TreapMap mugF)) (hp : WalkP P o laz) :
    nock (C wlBat (C (C (A o) (C laz.toNoun (C Fb (C Fs Fc)))) (C D (C (genNoun g x) ctx)))) wlBat
      = (Lazy.walkLazy f o laz g).map fun p => genNoun p.2 x :=
  wl_all hc hm x Fb Fs Fc D f P hf laz o g hp

end

end Compiler
end Formalization
