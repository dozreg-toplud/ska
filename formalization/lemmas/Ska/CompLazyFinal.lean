import lemmas.Ska.CompLazyAgree
import lemmas.Ska.CompFinal

/-!
# The final pass over lazy needs with forks

`+coerce-lazy` in full (`coerceLazyL`: the sure need at the block of the
`next`, then the bonds, then the forks, each at its own block), and
`finishL`, the final pass of `+compile-scc-in` with `runL` (in the region
`~`, as `+compile-scc-in` calls `run`) and `coerceLazyL`.  On the fragment
`Frag` it is `finish` (`finishL_eq`), so `finish_bellContract'` holds of it
(`finishL_bellContract`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

mutual
/-- `+coerce-lazy`: the code that takes the subject held as `ned` apart for
the lazy need, in the block of each of its parts. -/
def coerceLazyL (ned : Need) (less : Cape) : Nat → Lazy S → CM Map Unit
  | o, mk s f b => do
    coerceLazy ned o s less
    if f.isEmpty && b.isEmpty then pure () else do
    coerceBonds ned less b
    coerceForks ned less f

/-- Its `roll` over the bonds. -/
def coerceBonds (ned : Need) (less : Cape) : List (Nat × Lazy S) → CM Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    coerceLazyL ned less o l
    coerceBonds ned less rest

/-- Its `roll` over the forks, the yes branch first. -/
def coerceForks (ned : Need) (less : Cape) : List (ForkE S) → CM Map Unit
  | [] => pure ()
  | ((oy, y), (on, n)) :: rest => do
    coerceLazyL ned less oy y
    coerceLazyL ned less on n
    coerceForks ned less rest
end

theorem coerceLazyL_ofSure (ned : Need) (less : Cape) (o : Nat) (s : Sure S) :
    (coerceLazyL ned less o (ofSure s) : CM Map Unit) = coerceLazy ned o s less := by
  simp [coerceLazyL, ofSure]

/-- The final pass of `member` in `+compile-scc-in`, as `finish`, with the
model of `run` over full lazy needs. -/
def finishL (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runL nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyL nedFinal less nex.th.there nex.laz g2).bind fun (_, g3) =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
          toStraight g4.blocks bak.1 nex.th.there

/-- **On a pure nomm without `%6` the final pass over full lazy needs is
the fork-free one.** -/
theorem finishL_eq {nm : Nomm} (hp : nm.pure = true) (h6 : noSix nm = true)
    (ord : NeedOrd) (less : Cape) (bake : Need → Need × List (Nat × Noun)) :
    finishL (S := S) (Map := Map) nm ord less bake = finish (S := S) nm ord less bake := by
  have e := runL_toL (S := S) (Map := Map) nm hp h6 CGoal.done []
  have e' : (runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) : Option (NextL S × Gen Map)) =
      (run nm (CGoal.done : CGoal S) (gen0 : Gen Map)).map fun p => (Next.toL p.1, p.2) := by
    rw [← map_apply]; exact congrFun e gen0
  unfold finishL finish
  rw [e']
  cases run nm (CGoal.done : CGoal S) (gen0 : Gen Map) with
  | none => rfl
  | some x =>
    simp only [Option.map_some, Option.bind_some, Next.toL_th, Next.toL_laz, coerceLazyL_ofSure]

/-- **The final pass over full lazy needs meets the contract** of its bell,
on the fragment, under the hypotheses of `finish_bellContract'`. -/
theorem finishL_bellContract {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {b : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits b.less) b.fol nm)
    (hf : Frag nm (CGoal.done : CGoal S)) {cape : Cape} {data : Noun} (hb : b.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map} (h : finishL (S := S) nm ord cape bake = some c')
    (N : Needs) : BellContract lib N b false c' := by
  rw [finishL_eq hp (frag_pure_noSix nm _ hf).2] at h
  exact finish_bellContract' hok hp hA hf hb hn hbake h N

end Comp
end SkaModel
end Formalization
