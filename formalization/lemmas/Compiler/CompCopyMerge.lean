import lemmas.Compiler.CompCopyLib
import lemmas.Compiler.CompRunInvL

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
    (ihy : ∀ (m : Lazy CSet) (g : Gen (TreapMap mugF)), (∃ v, HoonMap.get idx e.1.1 = some v ∧ m = v.1.2) →
      nock (C clBat (C (C (A e.1.1) (C e.1.2.toNoun m.toNoun)) (compCore g x ctx))) clBat
        = (Lazy.copyLazyL e.1.1 e.1.2 m g).map (clEnc x))
    (ihn : ∀ (m : Lazy CSet) (g : Gen (TreapMap mugF)), (∃ v, HoonMap.get idx e.1.1 = some v ∧ m = v.2.2) →
      nock (C clBat (C (C (A e.2.1) (C e.2.2.toNoun m.toNoun)) (compCore g x ctx))) clBat
        = (Lazy.copyLazyL e.2.1 e.2.2 m g).map (clEnc x)) :
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
      have hy := ihy my g ⟨_, ev, rfl⟩
      simp only [compCore] at hy
      cases e1 : Lazy.copyLazyL oy y my g with
      | none =>
        rw [e1] at hy
        simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, mgF, ev, forkE,
          hy, e1, bind, StateT.bind]
      | some p =>
        obtain ⟨y', g1⟩ := p
        rw [e1] at hy
        have hn := ihn mn g1 ⟨_, ev, rfl⟩
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
    (ih : ∀ (m : Lazy CSet) (g : Gen (TreapMap mugF)), (∃ v, HoonMap.get idx e.1 = some v ∧ m = v.2) →
      nock (C clBat (C (C (A e.1) (C e.2.toNoun m.toNoun)) (compCore g x ctx))) clBat
        = (Lazy.copyLazyL e.1 e.2 m g).map (clEnc x)) :
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
    have hl := ih m g ⟨_, ev, rfl⟩
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

end Compiler
end Formalization
