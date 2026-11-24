import lemmas.Compiler.CompCopyLib
import lemmas.Compiler.CompRunInvL
import lemmas.Hoon.DifIn

/-!
# The merge branch of `+copy-lazy`

When both lazy needs have forks (or both have bonds), `+copy-lazy` merges
the entries that name the same block:

    =/  index  (malt (turn fork.second |=(e [o.y.e e])))
    =^  merged  gen
      %^  spin  fork.first  gen
      |=  [e gen-acc]
      =.  gen  gen-acc
      ?~  m=(~(get by index) o.y.e)  [e gen]
      ?>  =(o.n.e o.n.u.m)
      =^  laz-y  gen  copy-lazy(o o.y.e, first laz.y.e, second laz.y.u.m)
      =^  laz-n  gen  copy-lazy(o o.n.e, first laz.n.e, second laz.n.u.m)
      [[[o.y.e laz-y] [o.n.e laz-n]] gen]
    =/  seen  (silt (turn fork.first |=(e o.y.e)))
    [(weld merged (skip fork.second |=(e (~(has in seen) o.y.e)))) gen]

and the same over the bonds.  The model `copyLazyL` (with `mergeForks`,
`mergeBonds`) of `Ska/CompLazyArms.lean` does the same: the index is the
last entry of `second` under each key (`index`, a fold of `put`, as `+gas:by`
puts in order), the spin goes over `first` in order with the yes need copied
before the no need, the `?>` is the model's `none`, `seen` is membership in
the keys of `first`.  No departure.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

def clSGF : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 112))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 28)) (C (A 0) (A 1022))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 114)) (C (A 0) (A 22)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 112)) (C (C (A 0) (A 113)) (C (A 0) (A 21))))) (C (A 0) (A 63)))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 242)) (C (C (A 0) (A 243)) (C (A 0) (A 55))))) (C (A 0) (A 127)))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 496)) (C (A 0) (A 6))) (C (C (A 0) (A 498)) (C (A 0) (A 2)))) (C (A 0) (A 4094))))))))))))))))))) (C (A 0) (A 0))))))))))))

def clSGB : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 28)) (C (A 0) (A 2046))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 57)) (C (A 0) (A 11))))) (C (A 0) (A 127)))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 120)) (C (A 0) (A 2))) (C (A 0) (A 4094))))))))))))))))))

def clBatS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 5500) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 232)) (C (A 0) (A 236)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 13)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 238)))) (C (C (C (A 0) (A 234)) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 234)))) (C (C (C (A 0) (A 238)) (C (A 0) (A 62))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 494)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (C (A 0) (A 24)) (C (A 0) (A 6)))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5f7bffb) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1002)) (C (C (A 0) (A 254)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2989) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 126))) (C (C (A 1) clSGF) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2026)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (A 0) (A 24))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4078)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 510))))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 495)))) (C (C (C (A 0) (A 491)) (C (A 0) (A 126))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 491)))) (C (C (C (A 0) (A 495)) (C (A 0) (A 126))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1007)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (C (A 0) (A 12)) (C (A 0) (A 6)))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5f7bffb) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2027)) (C (C (A 0) (A 510)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2742) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 254))) (C (C (A 1) clSGB) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4075)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 0) (A 12))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8175)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 1022))))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 28)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 2025))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2029))) (C (A 0) (A 2))))))))) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 254)))))))))))))))))))))))))))))))

theorem cl_bat_eq : clBat = clBatS := by kernel_rfl

/-! ## The model -/

/-- The gate of the spin over the forks of `first`, in the model. -/
noncomputable def mgF (idx : TreapMap mugF (Lazy.ForkE CSet)) (e : Lazy.ForkE CSet) :
    CM (TreapMap mugF) (Lazy.ForkE CSet) :=
  match HoonMap.get idx e.1.1 with
  | Option.none => pure e
  | some ((_, my), (mon, mn)) =>
    if e.2.1 = mon then do
      let y' ← Lazy.copyLazyL e.1.1 e.1.2 my
      let n' ← Lazy.copyLazyL e.2.1 e.2.2 mn
      pure ((e.1.1, y'), (e.2.1, n'))
    else fun _ => Option.none

/-- The gate of the spin over the bonds of `first`, in the model. -/
noncomputable def mgB (idx : TreapMap mugF (Nat × Lazy CSet)) (e : Nat × Lazy CSet) :
    CM (TreapMap mugF) (Nat × Lazy CSet) :=
  match HoonMap.get idx e.1 with
  | Option.none => pure e
  | some (_, m) => do
    let l' ← Lazy.copyLazyL e.1 e.2 m
    pure (e.1, l')

theorem mergeForks_spinM (idx : TreapMap mugF (Lazy.ForkE CSet)) :
    ∀ (fk : List (Lazy.ForkE CSet)) (g : Gen (TreapMap mugF)),
    Lazy.mergeForks idx fk g = spinM (fun e g => mgF idx e g) fk g
  | [], g => rfl
  | ((oy, y), (on, n)) :: rest, g => by
    have ih : Lazy.mergeForks idx rest = spinM (fun e g => mgF idx e g) rest :=
      funext (mergeForks_spinM idx rest)
    simp only [Lazy.mergeForks, spinM, ih, bind, StateT.bind]
    generalize spinM (fun e g => mgF idx e g) rest = R
    unfold mgF
    cases e1 : (HoonMap.get idx oy : Option (Lazy.ForkE CSet)) with
    | none =>
      simp only [pure, StateT.pure, Option.bind_some]
      cases R g <;> rfl
    | some v =>
      obtain ⟨⟨_, my⟩, ⟨mon, mn⟩⟩ := v
      simp only
      split
      · cases e2 : Lazy.copyLazyL oy y my g with
        | none => simp [e2, bind, StateT.bind, Functor.map, StateT.map]
        | some p =>
          obtain ⟨y', g1⟩ := p
          cases e3 : Lazy.copyLazyL on n mn g1 with
          | none => simp [e2, e3, bind, StateT.bind, Functor.map, StateT.map]
          | some q =>
            obtain ⟨n', g2⟩ := q
            simp only [e2, e3, Option.bind_some, pure, StateT.pure, bind, StateT.bind, Functor.map, StateT.map]
            cases R g2 <;> rfl
      · rfl

theorem mergeBonds_spinM (idx : TreapMap mugF (Nat × Lazy CSet)) :
    ∀ (bd : List (Nat × Lazy CSet)) (g : Gen (TreapMap mugF)),
    Lazy.mergeBonds idx bd g = spinM (fun e g => mgB idx e g) bd g
  | [], g => rfl
  | (ob, l) :: rest, g => by
    have ih : Lazy.mergeBonds idx rest = spinM (fun e g => mgB idx e g) rest :=
      funext (mergeBonds_spinM idx rest)
    simp only [Lazy.mergeBonds, spinM, ih, bind, StateT.bind]
    generalize spinM (fun e g => mgB idx e g) rest = R
    unfold mgB
    cases e1 : (HoonMap.get idx ob : Option (Nat × Lazy CSet)) with
    | none =>
      simp only [pure, StateT.pure, Option.bind_some]
      cases R g <;> rfl
    | some v =>
      obtain ⟨_, m⟩ := v
      cases e2 : Lazy.copyLazyL ob l m g with
      | none => simp [e2, bind, StateT.bind, Functor.map, StateT.map]
      | some p =>
        obtain ⟨l', g1⟩ := p
        simp only [e2, Option.bind_some, pure, StateT.pure, bind, StateT.bind, Functor.map, StateT.map]
        cases R g1 <;> rfl

/-! ## The counter only grows -/

theorem addOps_re {o : Nat} {ops : List Pole} {g g' : Gen (TreapMap mugF)} {u : Unit}
    (h : addOps o ops g = some (u, g')) : g'.re = g.re := by
  simp only [addOps] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  · obtain ⟨b, -, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h; rw [← h.2]

mutual
theorem copyLazyL_le : ∀ (o : Nat) (f s : Lazy CSet) (g g' : Gen (TreapMap mugF)) (r : Lazy CSet),
    Lazy.copyLazyL o f s g = some (r, g') → g.re ≤ g'.re
  | o, Lazy.mk s1 f1 b1, second, g, g', r, h => by
    simp only [Lazy.copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨A0, -, c1⟩ := copyNeed_spec (Map := TreapMap mugF) _ _ _ _ _ _ e1
    obtain ⟨u, g2, e2, h⟩ := bind_some h
    have r2 := addOps_re e2
    obtain ⟨fk, g3, e3, h⟩ := bind_some h
    have l3 : g2.re ≤ g3.re := by
      split at e3
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3; obtain ⟨-, rfl⟩ := e3; exact Nat.le_refl _
      · split at e3
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3; obtain ⟨-, rfl⟩ := e3; exact Nat.le_refl _
        · obtain ⟨mg, g4, e4, e3⟩ := bind_some e3
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
          rw [← e3.2]; exact mergeForks_le _ f1 g2 g4 mg e4
    obtain ⟨bd, g5, e5, h⟩ := bind_some h
    have l5 : g3.re ≤ g5.re := by
      split at e5
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e5; obtain ⟨-, rfl⟩ := e5; exact Nat.le_refl _
      · split at e5
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e5; obtain ⟨-, rfl⟩ := e5; exact Nat.le_refl _
        · obtain ⟨mg, g6, e6, e5⟩ := bind_some e5
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e5
          rw [← e5.2]; exact mergeBonds_le _ b1 g3 g6 mg e6
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    have := c1.le
    omega

theorem mergeForks_le (idx : TreapMap mugF (Lazy.ForkE CSet)) : ∀ (fk : List (Lazy.ForkE CSet))
    (g g' : Gen (TreapMap mugF)) (r : List (Lazy.ForkE CSet)),
    Lazy.mergeForks idx fk g = some (r, g') → g.re ≤ g'.re
  | [], g, g', r, h => by
    simp only [Lazy.mergeForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
  | ((oy, y), (on, n)) :: rest, g, g', r, h => by
    simp only [Lazy.mergeForks] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    have l1 : g.re ≤ g1.re := by
      cases hg : (HoonMap.get idx oy : Option (Lazy.ForkE CSet)) with
      | none =>
        simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨-, rfl⟩ := e1; exact Nat.le_refl _
      | some v =>
        obtain ⟨⟨_, my⟩, ⟨mon, mn⟩⟩ := v
        simp only [hg] at e1
        split at e1
        · obtain ⟨y', g2, e2, e1⟩ := bind_some e1
          obtain ⟨n', g3, e3, e1⟩ := bind_some e1
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
          rw [← e1.2]
          exact Nat.le_trans (copyLazyL_le oy y _ g g2 y' e2) (copyLazyL_le on n _ g2 g3 n' e3)
        · cases e1
    obtain ⟨r', g4, e4, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact Nat.le_trans l1 (mergeForks_le idx rest g1 g4 r' e4)

theorem mergeBonds_le (idx : TreapMap mugF (Nat × Lazy CSet)) : ∀ (bd : List (Nat × Lazy CSet))
    (g g' : Gen (TreapMap mugF)) (r : List (Nat × Lazy CSet)),
    Lazy.mergeBonds idx bd g = some (r, g') → g.re ≤ g'.re
  | [], g, g', r, h => by
    simp only [Lazy.mergeBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
  | (ob, l) :: rest, g, g', r, h => by
    simp only [Lazy.mergeBonds] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    have l1 : g.re ≤ g1.re := by
      cases hg : (HoonMap.get idx ob : Option (Nat × Lazy CSet)) with
      | none =>
        simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨-, rfl⟩ := e1; exact Nat.le_refl _
      | some v =>
        obtain ⟨_, m⟩ := v
        simp only [hg] at e1
        obtain ⟨l', g2, e2, e1⟩ := bind_some e1
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        rw [← e1.2]
        exact copyLazyL_le ob l _ g g2 l' e2
    obtain ⟨r', g4, e4, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact Nat.le_trans l1 (mergeBonds_le idx rest g1 g4 r' e4)
end

/-! ## The hypotheses of the general copy -/

/-- No register is in both lazy needs. -/
def LApart (f s : Lazy CSet) : Prop :=
  ∀ r, LAll (fun t => ¬ NMem t.ned r) f ∨ LAll (fun t => ¬ NMem t.ned r) s

/-- **The hypotheses of the general `+copy-lazy`**: every register of both
lazy needs below `k`, and no register in both. -/
def CopyH (k : Nat) (f s : Lazy CSet) : Prop :=
  LAll (fun t => NB k t.ned) f ∧ LAll (fun t => NB k t.ned) s ∧ LApart f s

theorem copyH_mono {k k' : Nat} (hk : k ≤ k') {f s : Lazy CSet} (h : CopyH k f s) : CopyH k' f s :=
  ⟨lall_mono (fun _ hs => hs.mono hk) h.1, lall_mono (fun _ hs => hs.mono hk) h.2.1, h.2.2⟩

/-- The parts of the entries of a fork list. -/
theorem walkPF_mem {Q : Sure CSet → Prop} : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF (fun _ s => Q s) fk →
    ∀ e ∈ fk, LAll Q e.1.2 ∧ LAll Q e.2.2
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact ⟨Eq.mp (walkP_irrel Q oy 0 y) hy, Eq.mp (walkP_irrel Q on 0 n) hn⟩
    · exact walkPF_mem rest hr e he'

theorem walkPB_mem {Q : Sure CSet → Prop} : ∀ (bd : List (Nat × Lazy CSet)), WalkPB (fun _ s => Q s) bd →
    ∀ e ∈ bd, LAll Q e.2
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · exact Eq.mp (walkP_irrel Q ob 0 l) hl
    · exact walkPB_mem rest hr e he'

/-- The hypotheses hold of the parts of two entries. -/
theorem copyH_part {k : Nat} {f s y m : Lazy CSet}
    (hy : ∀ Q, LAll Q f → LAll Q y) (hm : ∀ Q, LAll Q s → LAll Q m) (h : CopyH k f s) : CopyH k y m :=
  ⟨hy _ h.1, hm _ h.2.1, fun r => (h.2.2 r).elim (fun a => Or.inl (hy _ a)) (fun a => Or.inr (hm _ a))⟩

/-- The side conditions of `+copy-need-make-ops` at the roots. -/
theorem copyH_root {k : Nat} {f s : Lazy CSet} (h : CopyH k f s) :
    cnLt k f.sure.ned ∧ cnLt k s.sure.ned ∧ cnMeet f.sure.ned s.sure.ned := by
  cases f with
  | mk sf ff bf =>
  cases s with
  | mk ss fs bs =>
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨cri_lt_of_nb _ h1.1, cri_lt_of_nb _ h2.1, cri_meet_apart _ _ fun r e1 e2 => ?_⟩
  rcases h3 r with a | a
  · exact a.1 e1
  · exact a.1 e2

/-! ## The gates of the spins -/

section
variable (hc : CompIn ctx) (x : GenRest)
include hc

/-- The noun of a result of `+copy-lazy`. -/
noncomputable def clEnc (x : GenRest) (p : Lazy CSet × Gen (TreapMap mugF)) : Noun :=
  C p.1.toNoun (genNoun p.2 x)

/-- **The gate of the spin over the forks**: `=.  gen  gen-acc`, the lookup in
the index, `e` itself when the index has no entry at `o.y.e`, the `?>` on
the no blocks, then `+copy-lazy` of the yes needs and of the no needs, in
the copy-lazy core whatever its sample and state. -/
theorem cl_fgate (idx : TreapMap mugF (Lazy.ForkE CSet)) (NO SAMPLE G' : Noun) (e : Lazy.ForkE CSet)
    (g : Gen (TreapMap mugF))
    (ihy : ∀ (m : Lazy CSet) (g' : Gen (TreapMap mugF)), g.re ≤ g'.re →
      (∃ v, HoonMap.get idx e.1.1 = some v ∧ m = v.1.2) →
      nock (C clBat (C (C (A e.1.1) (C e.1.2.toNoun m.toNoun)) (compCore g' x ctx))) clBat
        = (Lazy.copyLazyL e.1.1 e.1.2 m g').map (clEnc x))
    (ihn : ∀ (m : Lazy CSet) (g' : Gen (TreapMap mugF)), g.re ≤ g'.re →
      (∃ v, HoonMap.get idx e.1.1 = some v ∧ m = v.2.2) →
      nock (C clBat (C (C (A e.2.1) (C e.2.2.toNoun m.toNoun)) (compCore g' x ctx))) clBat
        = (Lazy.copyLazyL e.2.1 e.2.2 m g').map (clEnc x)) :
    nock (C clSGF (C (C (forkE e) (genNoun g x)) (C (HoonMap.toNoun forkE idx)
      (C NO (C clBat (C SAMPLE (C comp.door (C G' ctx)))))))) clSGF
      = (mgF idx e g).map fun r => C (forkE r.1) (genNoun r.2 x) := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  have hget := getF_hoonMap forkE idx oy
  have hgg := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A oy) _ _ hget
  unfold clSGF
  simp only at ihy ihn
  cases ev : (HoonMap.get idx oy : Option (Lazy.ForkE CSet)) with
  | none =>
    rw [ev] at hgg
    simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgF, ev, forkE,
      pure, StateT.pure]
  | some v =>
    obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := v
    rw [ev] at hgg
    by_cases hon : on = mon
    · subst hon
      have hy := ihy my g (Nat.le_refl _) ⟨_, ev, rfl⟩
      simp only [compCore] at hy
      cases e1 : Lazy.copyLazyL oy y my g with
      | none =>
        rw [e1] at hy
        simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgF, ev, forkE,
          hy, e1, bind, StateT.bind]
      | some p =>
        obtain ⟨y', g1⟩ := p
        rw [e1] at hy
        have hn := ihn mn g1 (copyLazyL_le _ _ _ _ _ _ e1) ⟨_, ev, rfl⟩
        simp only [compCore] at hn
        cases e2 : Lazy.copyLazyL on n mn g1 with
        | none =>
          rw [e2] at hn
          simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgF, ev, forkE,
            hy, e1, hn, e2, bind, StateT.bind, clEnc]
        | some q =>
          obtain ⟨n', g2⟩ := q
          rw [e2] at hn
          simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgF, ev, forkE,
            hy, e1, hn, e2, bind, StateT.bind, clEnc, pure, StateT.pure]
    · simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgF, ev, forkE, hon,
        eqCode_atom]

/-- **The gate of the spin over the bonds**: the lookup, `e` itself without an
entry, else `+copy-lazy` of the two needs of the block. -/
theorem cl_bgate (idx : TreapMap mugF (Nat × Lazy CSet)) (FK NO SAMPLE G' : Noun) (e : Nat × Lazy CSet)
    (g : Gen (TreapMap mugF))
    (ih : ∀ (m : Lazy CSet) (g' : Gen (TreapMap mugF)), g.re ≤ g'.re → (∃ v, HoonMap.get idx e.1 = some v ∧ m = v.2) →
      nock (C clBat (C (C (A e.1) (C e.2.toNoun m.toNoun)) (compCore g' x ctx))) clBat
        = (Lazy.copyLazyL e.1 e.2 m g').map (clEnc x)) :
    nock (C clSGB (C (C (bondE e) (genNoun g x)) (C (HoonMap.toNoun bondE idx)
      (C FK (C NO (C clBat (C SAMPLE (C comp.door (C G' ctx))))))))) clSGB
      = (mgB idx e g).map fun r => C (bondE r.1) (genNoun r.2 x) := by
  obtain ⟨ob, l⟩ := e
  have hget := getF_hoonMap bondE idx ob
  have hgg := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A ob) _ _ hget
  unfold clSGB
  simp only at ih
  cases ev : (HoonMap.get idx ob : Option (Nat × Lazy CSet)) with
  | none =>
    rw [ev] at hgg
    simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgB, ev, bondE,
      pure, StateT.pure]
  | some v =>
    obtain ⟨ob', m⟩ := v
    rw [ev] at hgg
    have hl := ih m g (Nat.le_refl _) ⟨_, ev, rfl⟩
    simp only [compCore] at hl
    cases e1 : Lazy.copyLazyL ob l m g with
    | none =>
      rw [e1] at hl
      simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgB, ev, bondE,
        hl, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨l', g1⟩ := p
      rw [e1] at hl
      simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgB, ev, bondE,
        hl, e1, bind, StateT.bind, clEnc, pure, StateT.pure]

end

/-! ## The fork and bond parts of the battery -/

def clFX : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 238)))) (C (C (C (A 0) (A 234)) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 234)))) (C (C (C (A 0) (A 238)) (C (A 0) (A 62))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 494)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (C (A 0) (A 24)) (C (A 0) (A 6)))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5f7bffb) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1002)) (C (C (A 0) (A 254)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2989) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 126))) (C (C (A 1) clSGF) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2026)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (A 0) (A 24))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4078)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 510)))))))))))))))))))))

def clBX : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 495)))) (C (C (C (A 0) (A 491)) (C (A 0) (A 126))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 491)))) (C (C (C (A 0) (A 495)) (C (A 0) (A 126))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1007)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (C (A 0) (A 12)) (C (A 0) (A 6)))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5f7bffb) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2027)) (C (C (A 0) (A 510)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2742) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 254))) (C (C (A 1) clSGB) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4075)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 0) (A 12))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8175)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 1022)))))))))))))))))))))

def clBatS2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 5500) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 232)) (C (A 0) (A 236)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 13)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) clFX)) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) clBX)) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 28)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 2025))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2029))) (C (A 0) (A 2))))))))) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 254)))))))))))))))))))))))))))))))

theorem cl_bat_eq2 : clBat = clBatS2 := by kernel_rfl

/-! ## The molds `lazy-fork` and `lazy-bond` -/

noncomputable def ctLfArm : Noun := (slot? 2989 compTypes).getD (A 0)
theorem ct_lf_at : slot? 2989 compTypes = some ctLfArm := by kernel_rfl
noncomputable def ctLfGate : Noun := (evalFuel 2000 compTypes ctLfArm).getD (A 0)
theorem ct_lf_gate : nock compTypes ctLfArm = some ctLfGate := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)
noncomputable def ctLfBat : Noun := (slot? 2 ctLfGate).getD (A 0)
theorem ct_lf_bat : slot? 2 ctLfGate = some ctLfBat := by kernel_rfl
noncomputable def ctLfBunt : Noun := (evalFuel 2000 ctLfGate ctLfBat).getD (A 0)
theorem ct_lf_bunt : nock ctLfGate ctLfBat = some ctLfBunt := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

noncomputable def ctLbArm : Noun := (slot? 2742 compTypes).getD (A 0)
theorem ct_lb_at : slot? 2742 compTypes = some ctLbArm := by kernel_rfl
noncomputable def ctLbGate : Noun := (evalFuel 2000 compTypes ctLbArm).getD (A 0)
theorem ct_lb_gate : nock compTypes ctLbArm = some ctLbGate := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)
noncomputable def ctLbBat : Noun := (slot? 2 ctLbGate).getD (A 0)
theorem ct_lb_bat : slot? 2 ctLbGate = some ctLbBat := by kernel_rfl
noncomputable def ctLbBunt : Noun := (evalFuel 2000 ctLbGate ctLbBat).getD (A 0)
theorem ct_lb_bunt : nock ctLbGate ctLbBat = some ctLbBunt := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-! ## `+silt` and `+has:in` of the seen set -/

@[nock_exec] theorem cm_silt_arm (d : Noun) : nock d silt.arm = some (C silt.battery (C (A 0) d)) := by
  nock_open silt.arm; simp only [nock_exec]

theorem cm_silt_gate (l : List Noun) (out : Noun) (h : gasInF mugF (A 0) l = some out) :
    nock (C silt.battery (C (listN l) layer2)) silt.battery = some out := by
  have hg : nock (C in.gas.battery (C (listN l) (C in.battery (C (A 0) layer2)))) in.gas.battery = some out := by
    nock_open in.gas.battery
    simp only [nock_exec, gas_in_loop layer2 gorIn_morIn_layer2 l (A 0) out h]
  nock_open silt.battery
  simp [nock_exec, in_arm, in.arm_at, in.gas.arm_at, gas_in_arm, hg]

/-- The seen set: the `+silt` of the keys, and `+has:in` on it is membership. -/
theorem seen_set (l : List Nat) : ∃ S0, gasInF mugF (A 0) (l.map A) = some S0 ∧
    ∀ k, nock (C in.has.battery (C (A k) (C in.battery (C S0 layer2)))) in.has.battery
      = some (loob (decide (k ∈ l))) := by
  obtain ⟨S0, h1, hs, hh⟩ := gasInF_spec (mug := mugF) (l.map A) (A 0) isSet_nil
  refine ⟨S0, h1, fun k => ?_⟩
  obtain ⟨t, ht, hti⟩ := hasInF_spec mugF S0 (A k) hs
  rw [has_in_gate layer2 gorIn_morIn_layer2.1 (A k) S0 t ht]
  congr 2
  have : (A k ∈ l.map A ∨ Has (A 0) (A k)) ↔ k ∈ l := by
    constructor
    · rintro (h | h)
      · obtain ⟨y, hy, e⟩ := List.mem_map.1 h
        cases e; exact hy
      · exact absurd h not_has_atom
    · intro h; exact Or.inl (List.mem_map_of_mem h)
  have key : t = true ↔ k ∈ l := by rw [hti, hh, this]
  cases t with
  | true => simp [key.1 rfl]
  | false =>
    have : ¬ k ∈ l := fun h => by simpa using key.2 h
    simp [this]

/-- The gates of the spins keep the counter from below. -/
theorem mgF_le {idx : TreapMap mugF (Lazy.ForkE CSet)} {e : Lazy.ForkE CSet} {g : Gen (TreapMap mugF)}
    {r : Lazy.ForkE CSet × Gen (TreapMap mugF)} (h : mgF idx e g = some r) : g.re ≤ r.2.re := by
  unfold mgF at h
  cases ev : (HoonMap.get idx e.1.1 : Option (Lazy.ForkE CSet)) with
  | none =>
    simp only [ev, pure, StateT.pure, Option.some.injEq] at h; rw [← h]; exact Nat.le_refl _
  | some v =>
    obtain ⟨⟨_, my⟩, ⟨mon, mn⟩⟩ := v
    simp only [ev] at h
    split at h
    · obtain ⟨y', g1, e1, h⟩ := bind_some h
      obtain ⟨n', g2, e2, h⟩ := bind_some h
      simp only [pure, StateT.pure, Option.some.injEq] at h
      rw [← h]
      exact Nat.le_trans (copyLazyL_le _ _ _ _ _ _ e1) (copyLazyL_le _ _ _ _ _ _ e2)
    · cases h

theorem mgB_le {idx : TreapMap mugF (Nat × Lazy CSet)} {e : Nat × Lazy CSet} {g : Gen (TreapMap mugF)}
    {r : (Nat × Lazy CSet) × Gen (TreapMap mugF)} (h : mgB idx e g = some r) : g.re ≤ r.2.re := by
  unfold mgB at h
  cases ev : (HoonMap.get idx e.1 : Option (Nat × Lazy CSet)) with
  | none =>
    simp only [ev, pure, StateT.pure, Option.some.injEq] at h; rw [← h]; exact Nat.le_refl _
  | some v =>
    obtain ⟨_, m⟩ := v
    simp only [ev] at h
    obtain ⟨l', g1, e1, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq] at h
    rw [← h]
    exact copyLazyL_le _ _ _ _ _ _ e1

/-! ## The fork part -/

/-- The forks of the result of `+copy-lazy`, in the model (the expression of
`copyLazyL`). -/
noncomputable def forkPart (ff fs : List (Lazy.ForkE CSet)) : CM (TreapMap mugF) (List (Lazy.ForkE CSet)) :=
  if fs.isEmpty then pure ff else if ff.isEmpty then pure fs else do
    let merged ← Lazy.mergeForks (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) ff
    pure (merged ++ fs.filter fun e => !(Lazy.seen (S := CSet) (fun e : Lazy.ForkE CSet => e.1.1) ff e.1.1))

/-- The pair `[key e]` of an entry's noun. -/
def pairOf : Noun → Noun
  | Noun.cell (Noun.cell a b) c => C a (C (C a b) c)
  | _ => A 0

/-- The key of an entry's noun. -/
def keyOf : Noun → Noun
  | Noun.cell (Noun.cell a _) _ => a
  | _ => A 0

theorem turn_pairs (bs bc : Noun) (fk : List (Lazy.ForkE CSet)) :
    nock (C turn.battery (C (C (listN (fk.map forkE)) (C (C (C (A 0) (A 24)) (C (A 0) (A 6))) (C bs bc))) layer2))
      turn.battery = some (listN ((fk.map fun e => (A e.1.1, forkE e)).map pairNoun)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc pairOf (fk.map forkE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, forkE, pairOf])]
  simp [List.map_map, Function.comp_def, forkE, pairOf, pairNoun]

theorem turn_keys (bs bc : Noun) (fk : List (Lazy.ForkE CSet)) :
    nock (C turn.battery (C (C (listN (fk.map forkE)) (C (C (A 0) (A 24)) (C bs bc))) layer2))
      turn.battery = some (listN ((fk.map fun e => e.1.1).map A)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc keyOf (fk.map forkE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, forkE, keyOf])]
  simp [List.map_map, Function.comp_def, forkE, keyOf]

/-- **The fork part of `+copy-lazy`** (`clFX`, on the subject `[[ned ops]
core]` after `+add-ops`): `forkPart`, given the spin gate at every fork of
`first` and every later state. -/
theorem cl_fpart (hc : CompIn ctx) (h15 : slot? 15 ctx = some compTypes) (x : GenRest) (NO : Noun) (o : Nat)
    (sf ss : Sure CSet) (ff fs : List (Lazy.ForkE CSet)) (bf bs : List (Nat × Lazy CSet))
    (g : Gen (TreapMap mugF))
    (hgate : ∀ e ∈ ff, ∀ g' : Gen (TreapMap mugF), g.re ≤ g'.re → ∀ (NO' SAMPLE G' : Noun),
      nock (C clSGF (C (C (forkE e) (genNoun g' x))
        (C (HoonMap.toNoun forkE (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs))
          (C NO' (C clBat (C SAMPLE (C comp.door (C G' ctx)))))))) clSGF
      = (mgF (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) e g').map
          fun r => C (forkE r.1) (genNoun r.2 x)) :
    nock (C NO (C clBat (C (C (A o) (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
      (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE)))))) (C comp.door (C (genNoun g x) ctx)))))
      clFX = (forkPart ff fs g).map fun r => C (listN (r.1.map forkE)) (genNoun r.2 x) := by
  have tF := lz_test forkE ff
  have tS := lz_test forkE fs
  have hL := comp_le_at
  generalize hSAM : C (A o) (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
      (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))) = SAM
  unfold clFX
  rcases tS with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
  · subst s1
    subst hSAM
    simp [nock_exec, s2, s3, forkPart, pure, StateT.pure]
  rcases tF with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  · subst f1
    subst hSAM
    simp [nock_exec, s2, s3, f2, f3, forkPart, pure, StateT.pure, s1]
  subst hSAM
  -- the merge
  have hT0 := turn_pairs (C (C (A 0) lzBunt) (C (A 0) lzBunt))
    (C NO (C clBat (C (C (A o) (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
      (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE)))))) (C comp.door (C (genNoun g x) ctx))))) fs
  have hIdx := malt_gate _ _ (malt_index forkE (fun e : Lazy.ForkE CSet => e.1.1) fs)
  unfold lzBunt at hT0
  simp only [forkPart, s1, f1, List.isEmpty_iff, if_false, bind, StateT.bind]
  generalize hidx : Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs = idx at hIdx hgate ⊢
  have hSpin := spin_gate_TI forkE forkE (fun g => genNoun g x) layer2 spinIn_layer2 clSGF
    (C ctLfBunt (genNoun g x))
    (C (HoonMap.toNoun forkE idx) (C NO (C clBat (C (C (A o) (C (C sf.toNoun (C (listN (ff.map forkE))
      (listN (bf.map bondE)))) (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))))
      (C comp.door (C (genNoun g x) ctx))))))
    (fun e g => mgF idx e g) (fun g' => g.re ≤ g'.re) ff g
    (fun e he g' hle => hgate e he g' hle _ _ _) (fun e he g' r hle hr => Nat.le_trans hle (mgF_le hr))
    (Nat.le_refl _)
  rw [← mergeForks_spinM] at hSpin
  have hsp := spin_arm_l2
  rw [spin_gate_eq] at hsp
  simp only [List.map_map] at hT0 hIdx
  have hm1 := malt_at
  have ht1 := turn.arm_at
  have hs1 := spin.arm_at
  have hc' : slot? 262143 ctx = some layer2 := hc
  cases eS : Lazy.mergeForks idx ff g with
  | none =>
    rw [eS] at hSpin
    generalize layer2 = L2 at hc' hm1 ht1 hs1 hT0 hIdx hSpin hsp ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hs1,
      hsp, hSpin, h15, ct_lf_at, ct_lf_gate, ct_lf_bat, ct_lf_bunt, eS, buntGate]
  | some r =>
    obtain ⟨merged, g2⟩ := r
    rw [eS] at hSpin
    have hTk := turn_keys (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C (listN (merged.map forkE)) (C (HoonMap.toNoun forkE idx) (C NO (C clBat (C (C (A o)
        (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
          (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))))
        (C comp.door (C (genNoun g2 x) ctx))))))) ff
    unfold lzBunt at hTk
    simp only [List.map_map] at hTk
    obtain ⟨S0, hS0, hhas⟩ := seen_set (ff.map fun e => e.1.1)
    have hSilt := cm_silt_gate _ S0 hS0
    simp only [List.map_map] at hSilt
    have hSkip := skip_gate_map forkE layer2 clG2 (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C S0 (C (listN (merged.map forkE)) (C (HoonMap.toNoun forkE idx) (C NO (C clBat (C (C (A o)
        (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
          (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))))
        (C comp.door (C (genNoun g2 x) ctx))))))))
      (fun e => decide (e.1.1 ∈ ff.map fun e => e.1.1)) fs (fun e _ => by
        have := hhas e.1.1
        unfold clG2
        simp [nock_exec, hc, in_arm, in.arm_at, in.has.arm_at, has_in_arm, this, forkE])
    unfold lzBunt clG2 at hSkip
    have hW := weld_gate_list layer2 (merged.map forkE)
      ((fs.filter fun a => !decide (a.1.1 ∈ ff.map fun e => e.1.1)).map forkE)
    have hsl := silt.arm_at
    have hsk := skip.arm_at
    have hwl := weld.arm_at
    generalize layer2 = L2 at hc' hm1 ht1 hs1 hT0 hIdx hSpin hsp hTk hSilt hSkip hW hsl hsk hwl ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hs1,
      hsp, hSpin, h15, ct_lf_at, ct_lf_gate, ct_lf_bat, ct_lf_bunt, eS, buntGate, hTk, hsl, cm_silt_arm, hSilt,
      hsk, lp_skip_arm, hSkip, hwl, weld_arm, hW, seen_iff, pure, StateT.pure]


/-! ## The bond part -/

/-- The bonds of the result of `+copy-lazy`, in the model (the expression of
`copyLazyL`). -/
noncomputable def bondPart (bf bs : List (Nat × Lazy CSet)) : CM (TreapMap mugF) (List (Nat × Lazy CSet)) :=
  if bs.isEmpty then pure bf else if bf.isEmpty then pure bs else do
    let merged ← Lazy.mergeBonds (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) bf
    pure (merged ++ bs.filter fun e => !(Lazy.seen (S := CSet) (fun e : Nat × Lazy CSet => e.1) bf e.1))

/-- The pair `[key e]` of a bond's noun. -/
def pairOfB : Noun → Noun
  | Noun.cell a b => C a (C a b)
  | _ => A 0

/-- The key of a bond's noun. -/
def keyOfB : Noun → Noun
  | Noun.cell a _ => a
  | _ => A 0

theorem turn_pairsB (bs bc : Noun) (bd : List (Nat × Lazy CSet)) :
    nock (C turn.battery (C (C (listN (bd.map bondE)) (C (C (C (A 0) (A 12)) (C (A 0) (A 6))) (C bs bc))) layer2))
      turn.battery = some (listN ((bd.map fun e => (A e.1, bondE e)).map pairNoun)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc pairOfB (bd.map bondE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, bondE, pairOfB])]
  simp [List.map_map, Function.comp_def, bondE, pairOfB, pairNoun]

theorem turn_keysB (bs bc : Noun) (bd : List (Nat × Lazy CSet)) :
    nock (C turn.battery (C (C (listN (bd.map bondE)) (C (C (A 0) (A 12)) (C bs bc))) layer2))
      turn.battery = some (listN ((bd.map fun e => e.1).map A)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc keyOfB (bd.map bondE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, bondE, keyOfB])]
  simp [List.map_map, Function.comp_def, bondE, keyOfB]

/-- **The bond part of `+copy-lazy`** (`clBX`, on the subject `[fork [[ned
ops] core]]`): `bondPart`, given the spin gate at every bond of `first` and
every later state. -/
theorem cl_bpart (hc : CompIn ctx) (h15 : slot? 15 ctx = some compTypes) (x : GenRest) (FN NO : Noun) (o : Nat)
    (sf ss : Sure CSet) (ff fs : List (Lazy.ForkE CSet)) (bf bs : List (Nat × Lazy CSet))
    (g : Gen (TreapMap mugF))
    (hgate : ∀ e ∈ bf, ∀ g' : Gen (TreapMap mugF), g.re ≤ g'.re → ∀ (NO' SAMPLE G' : Noun),
      ∀ FN' : Noun,
      nock (C clSGB (C (C (bondE e) (genNoun g' x))
        (C (HoonMap.toNoun bondE (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs))
          (C FN' (C NO' (C clBat (C SAMPLE (C comp.door (C G' ctx))))))))) clSGB
      = (mgB (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) e g').map
          fun r => C (bondE r.1) (genNoun r.2 x)) :
    nock (C FN (C NO (C clBat (C (C (A o) (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
      (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE)))))) (C comp.door (C (genNoun g x) ctx))))))
      clBX = (bondPart bf bs g).map fun r => C (listN (r.1.map bondE)) (genNoun r.2 x) := by
  have tF := lz_test bondE bf
  have tS := lz_test bondE bs
  have hL := comp_le_at
  generalize hSAM : C (A o) (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
      (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))) = SAM
  unfold clBX
  rcases tS with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
  · subst s1
    subst hSAM
    simp [nock_exec, s2, s3, bondPart, pure, StateT.pure]
  rcases tF with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  · subst f1
    subst hSAM
    simp [nock_exec, s2, s3, f2, f3, bondPart, pure, StateT.pure, s1]
  subst hSAM
  -- the merge
  have hT0 := turn_pairsB (C (A 0) lzBunt)
    (C FN (C NO (C clBat (C (C (A o) (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
      (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE)))))) (C comp.door (C (genNoun g x) ctx)))))) bs
  have hIdx := malt_gate _ _ (malt_index bondE (fun e : Nat × Lazy CSet => e.1) bs)
  unfold lzBunt at hT0
  simp only [bondPart, s1, f1, List.isEmpty_iff, if_false, bind, StateT.bind]
  generalize hidx : Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs = idx at hIdx hgate ⊢
  have hSpin := spin_gate_TI bondE bondE (fun g => genNoun g x) layer2 spinIn_layer2 clSGB
    (C ctLbBunt (genNoun g x))
    (C (HoonMap.toNoun bondE idx) (C FN (C NO (C clBat (C (C (A o) (C (C sf.toNoun (C (listN (ff.map forkE))
      (listN (bf.map bondE)))) (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))))
      (C comp.door (C (genNoun g x) ctx)))))))
    (fun e g => mgB idx e g) (fun g' => g.re ≤ g'.re) bf g
    (fun e he g' hle => hgate e he g' hle _ _ _ _) (fun e he g' r hle hr => Nat.le_trans hle (mgB_le hr))
    (Nat.le_refl _)
  rw [← mergeBonds_spinM] at hSpin
  have hsp := spin_arm_l2
  rw [spin_gate_eq] at hsp
  simp only [List.map_map] at hT0 hIdx
  have hm1 := malt_at
  have ht1 := turn.arm_at
  have hs1 := spin.arm_at
  have hc' : slot? 262143 ctx = some layer2 := hc
  cases eS : Lazy.mergeBonds idx bf g with
  | none =>
    rw [eS] at hSpin
    generalize layer2 = L2 at hc' hm1 ht1 hs1 hT0 hIdx hSpin hsp ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hs1,
      hsp, hSpin, h15, ct_lb_at, ct_lb_gate, ct_lb_bat, ct_lb_bunt, eS, buntGate]
  | some r =>
    obtain ⟨merged, g2⟩ := r
    rw [eS] at hSpin
    have hTk := turn_keysB (C (A 0) lzBunt)
      (C (listN (merged.map bondE)) (C (HoonMap.toNoun bondE idx) (C FN (C NO (C clBat (C (C (A o)
        (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
          (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))))
        (C comp.door (C (genNoun g2 x) ctx)))))))) bf
    unfold lzBunt at hTk
    simp only [List.map_map] at hTk
    obtain ⟨S0, hS0, hhas⟩ := seen_set (bf.map fun e => e.1)
    have hSilt := cm_silt_gate _ S0 hS0
    simp only [List.map_map] at hSilt
    have hSkip := skip_gate_map bondE layer2 clG5 (C (A 0) lzBunt)
      (C S0 (C (listN (merged.map bondE)) (C (HoonMap.toNoun bondE idx) (C FN (C NO (C clBat (C (C (A o)
        (C (C sf.toNoun (C (listN (ff.map forkE)) (listN (bf.map bondE))))
          (C ss.toNoun (C (listN (fs.map forkE)) (listN (bs.map bondE))))))
        (C comp.door (C (genNoun g2 x) ctx)))))))))
      (fun e => decide (e.1 ∈ bf.map fun e => e.1)) bs (fun e _ => by
        have := hhas e.1
        unfold clG5
        simp [nock_exec, hc, in_arm, in.arm_at, in.has.arm_at, has_in_arm, this, bondE])
    unfold lzBunt clG5 at hSkip
    have hW := weld_gate_list layer2 (merged.map bondE)
      ((bs.filter fun a => !decide (a.1 ∈ bf.map fun e => e.1)).map bondE)
    have hsl := silt.arm_at
    have hsk := skip.arm_at
    have hwl := weld.arm_at
    generalize layer2 = L2 at hc' hm1 ht1 hs1 hT0 hIdx hSpin hsp hTk hSilt hSkip hW hsl hsk hwl ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hs1,
      hsp, hSpin, h15, ct_lb_at, ct_lb_gate, ct_lb_bat, ct_lb_bunt, eS, buntGate, hTk, hsl, cm_silt_arm, hSilt,
      hsk, lp_skip_arm, hSkip, hwl, weld_arm, hW, seen_iff, pure, StateT.pure]

end Compiler
end Formalization
