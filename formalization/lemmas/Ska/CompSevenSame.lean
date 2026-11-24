import lemmas.Ska.CompAboveX

/-!
# Nomms that compile alike: the `%7` parent of the proxy cases

README Gaps 12.2.  `runL` of `[7 p q]` runs `q` for the goal and then `p` for
the goal `q`'s run returns, and `runL` of `[4 p]` and of `[3 p]` ends, for
every goal, with a run of `p` and nothing after it.  So the two sides of

* `[7 a [7 b c]]` and `[7 [7 a b] c]` (`sameL_assoc`),
* `[7 a [4 p]]` and `[4 [7 a p]]` (`sameL_n7_n4`),
* `[7 a [3 p]]` and `[3 [7 a p]]` (`sameL_n7_n3`)

run the same steps of the compiler from every state for every goal, and they
compute the same product (`SameL`).  `SameL` is a congruence for `%7`, `%4`
and `%3`, whose runs read their parts only through `runL` of the parts.  The
final pass reads the nomm only through its run and its product, so the
contract carries over (`finishLF_bellContractSame`, through `RunOKU.congr`).

This gives the special theorems of `[7 [4 p] q]` and `[7 [3 p] q]` the `%7`
parent in both places: `finishLF_bellContract74S` covers every nomm that
`SameL` relates to `[7 [4 p] q]` with `p` and `q` in `FragX`, for example
`[7 [0 2] [7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]]` (an outer `%7`
whose first step is a slot: it is `[7 [4 [7 [0 2] [0 3]]] q]`) and
`[7 [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [1 0]]` (an outer `%7` whose last
step is a constant: it is `[7 [4 [0 3]] [7 [6 ...] [1 0]]]`).  It does not
give `%6`, cons, `%5` or `%10` as parents: their runs read the syntax of their
parts (`+past`, `+fork`, `+sect`), and the run of a branch that makes a proxy
needs the relation of README Gaps 12.2.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Two nomms that compile alike and compute alike**: the same run of
`runL` for every goal and region from every state, the same product on every
subject, and the same number of `%6`. -/
structure SameL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm nm' : Nomm) :
    Prop where
  run : ∀ (goal : CGoalL S) (region : List Nat), (runL nm goal region : CM Map (NextL S)) = runL nm' goal region
  eval : ∀ s, pureEval nm s = pureEval nm' s
  six : sixCount nm = sixCount nm'

theorem SameL.refl (nm : Nomm) : SameL S Map nm nm := ⟨fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem SameL.symm {nm nm' : Nomm} (h : SameL S Map nm nm') : SameL S Map nm' nm :=
  ⟨fun g r => (h.run g r).symm, fun s => (h.eval s).symm, h.six.symm⟩

theorem SameL.trans {a b c : Nomm} (h1 : SameL S Map a b) (h2 : SameL S Map b c) : SameL S Map a c :=
  ⟨fun g r => (h1.run g r).trans (h2.run g r), fun s => (h1.eval s).trans (h2.eval s), h1.six.trans h2.six⟩

/-! ## The runs -/

theorem runL_n7_assoc (a b c : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runL (Nomm.n7 a (Nomm.n7 b c)) goal region : CM Map (NextL S)) =
      runL (Nomm.n7 (Nomm.n7 a b) c) goal region := by
  simp only [runL_n7, bind_assoc]

theorem runL_n4_done (p : Nomm) (region : List Nat) :
    (runL (Nomm.n4 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
  conv => lhs; unfold runL

theorem runL_n4_pick (p : Nomm) (z o : Jmp) (region : List Nat) :
    (runL (Nomm.n4 p) (CGoalL.pick z o : CGoalL S) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region) := by
  conv => lhs; unfold runL

theorem runL_n4_next (p : Nomm) (laz : Lazy S) (th : Jmp) (region : List Nat) :
    (runL (Nomm.n4 p) (CGoalL.next laz th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨laz, th⟩
      let (pro, th') ← collPick th a
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
  conv => lhs; unfold runL
  rfl

theorem runL_n3_done (p : Nomm) (region : List Nat) :
    (runL (Nomm.n3 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let (o0, o1) ← doneBlocks
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
      runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
  conv => lhs; unfold runL

theorem runL_n3_pick (p : Nomm) (z o : Jmp) (region : List Nat) :
    (runL (Nomm.n3 p) (CGoalL.pick z o : CGoalL S) region : CM Map (NextL S)) = (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
  conv => lhs; unfold runL

theorem runL_n3_next (p : Nomm) (laz : Lazy S) (th : Jmp) (region : List Nat) :
    (runL (Nomm.n3 p) (CGoalL.next laz th) region : CM Map (NextL S)) =
      if noneEquivalentL laz then runL p (CGoalL.next laz th) region else (do
        let a ← collapseLazyAtomL ⟨laz, th⟩
        match a with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runL p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
  conv => lhs; unfold runL
  rfl

/-- **`[7 a [4 p]]` runs as `[4 [7 a p]]`** for every goal. -/
theorem runL_n7_n4 (a p : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runL (Nomm.n7 a (Nomm.n4 p)) goal region : CM Map (NextL S)) = runL (Nomm.n4 (Nomm.n7 a p)) goal region := by
  rw [runL_n7]
  cases goal with
  | done => simp only [runL_n4_done, runL_n7, bind_assoc]
  | pick z o => simp only [runL_n4_pick, runL_n7, bind_assoc]
  | next laz th =>
    simp only [runL_n4_next, runL_n7, bind_assoc]

/-- **`[7 a [3 p]]` runs as `[3 [7 a p]]`** for every goal. -/
theorem runL_n7_n3 (a p : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runL (Nomm.n7 a (Nomm.n3 p)) goal region : CM Map (NextL S)) = runL (Nomm.n3 (Nomm.n7 a p)) goal region := by
  rw [runL_n7]
  cases goal with
  | done => simp only [runL_n3_done, runL_n7, bind_assoc]
  | pick z o => simp only [runL_n3_pick, runL_n7, bind_assoc]
  | next laz th =>
    rw [runL_n3_next, runL_n3_next]
    by_cases hn : noneEquivalentL laz = true
    · simp only [hn, if_true, runL_n7]
    · simp only [hn, Bool.false_eq_true, if_false, runL_n7, bind_assoc]
      congr 1
      funext a' g
      rcases a' with _ | ⟨r, o⟩
      · rfl
      · simp only [bind_assoc]

/-! ## The relation -/

theorem sameL_assoc (a b c : Nomm) : SameL S Map (Nomm.n7 a (Nomm.n7 b c)) (Nomm.n7 (Nomm.n7 a b) c) :=
  ⟨runL_n7_assoc a b c, fun s => by
    show (pureEval a s).bind (fun x => (pureEval b x).bind (pureEval c)) =
      ((pureEval a s).bind (pureEval b)).bind (pureEval c)
    cases pureEval a s <;> rfl, by simp only [sixCount]; omega⟩

theorem sameL_n7_n4 (a p : Nomm) : SameL S Map (Nomm.n7 a (Nomm.n4 p)) (Nomm.n4 (Nomm.n7 a p)) :=
  ⟨runL_n7_n4 a p, fun s => by
    rw [pureEval_n4]
    show (pureEval a s).bind (pureEval (Nomm.n4 p)) = ((pureEval a s).bind (pureEval p)).bind incF
    cases pureEval a s with
    | none => rfl
    | some x => exact pureEval_n4 p x, by simp only [sixCount]⟩

theorem sameL_n7_n3 (a p : Nomm) : SameL S Map (Nomm.n7 a (Nomm.n3 p)) (Nomm.n3 (Nomm.n7 a p)) :=
  ⟨runL_n7_n3 a p, fun s => by
    rw [pureEval_n3]
    show (pureEval a s).bind (pureEval (Nomm.n3 p)) = ((pureEval a s).bind (pureEval p)).bind fun x => some (wut x)
    cases pureEval a s with
    | none => rfl
    | some x => exact pureEval_n3 p x, by simp only [sixCount]⟩

/-- `SameL` is a congruence for `%7`. -/
theorem SameL.n7 {p p' q q' : Nomm} (hp : SameL S Map p p') (hq : SameL S Map q q') :
    SameL S Map (Nomm.n7 p q) (Nomm.n7 p' q') :=
  ⟨fun goal region => by simp only [runL_n7, hp.run, hq.run], fun s => by
    show (pureEval p s).bind (pureEval q) = (pureEval p' s).bind (pureEval q')
    rw [hp.eval, funext hq.eval], by simp only [sixCount, hp.six, hq.six]⟩

/-- `SameL` is a congruence for `%4`. -/
theorem SameL.n4 {p p' : Nomm} (hp : SameL S Map p p') : SameL S Map (Nomm.n4 p) (Nomm.n4 p') :=
  ⟨fun goal region => by
    cases goal with
    | done => simp only [runL_n4_done, hp.run]
    | pick z o => simp only [runL_n4_pick, hp.run]
    | next laz th => simp only [runL_n4_next, hp.run], fun s => by rw [pureEval_n4, pureEval_n4, hp.eval],
   by simp only [sixCount, hp.six]⟩

/-- `SameL` is a congruence for `%3`. -/
theorem SameL.n3 {p p' : Nomm} (hp : SameL S Map p p') : SameL S Map (Nomm.n3 p) (Nomm.n3 p') :=
  ⟨fun goal region => by
    cases goal with
    | done => simp only [runL_n3_done, hp.run]
    | pick z o => simp only [runL_n3_pick, hp.run]
    | next laz th => simp only [runL_n3_next, hp.run], fun s => by rw [pureEval_n3, pureEval_n3, hp.eval],
   by simp only [sixCount, hp.six]⟩

/-! ## The final pass -/

/-- `RunOKU` reads the nomm only through its product and its number of
`%6`. -/
theorem RunOKU.congr {lib : Lib} {nm nm' : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKU lib nm' goal g0 g1 nex) (he : ∀ s, pureEval nm s = pureEval nm' s)
    (hs : sixCount nm = sixCount nm') : RunOKU lib nm goal g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    by rw [hs]; exact R.size, fun s h => (he s).trans (R.nec s h), R.ncond, R.econd,
    fun c ned σ O st t gul s0 s ag hn regs hh hN => by rw [he s]; exact R.sem c ned σ O st t gul s0 s ag hn regs hh hN⟩

/-- **The final pass meets the contract on a nomm that compiles and
computes as one whose run meets `RunOKU`.** -/
theorem finishLF_bellContractSame {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm nm' : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hs : SameL S Map nm nm')
    (hR : ∀ {nex : NextL S} {g4 : Gen Map}, runL nm' (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g4) →
      RunOKU (Map := Map) lib nm' CGoal.done gen0 g4 nex)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractU hok hp hA (fun h1 => (hR (by rw [← hs.run]; exact h1)).congr hs.eval hs.six)
    hbl hn hbake h N

/-- **The final pass meets the contract on every nomm that compiles and
computes as `[7 [4 p] q]`** with `p` and `q` in `FragX`, at most 255 `%6`,
nothing baked and a cape with no `[| |]`. -/
theorem finishLF_bellContract74S {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm p q : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hs : SameL S Map nm (Nomm.n7 (Nomm.n4 p) q)) (hfp : FragX (S := S) p) (hfq : FragX (S := S) q)
    (hcount : sixCount nm ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractSame hok hp hA hs (fun h1 => runOKU_seven4 lib (runX_ok lib hfp).2.1 (runX_semR lib hfp).2.1
    (runX_keeps hfp) (aboveX_of_fragX hfp) hfq (by rw [← hs.six]; exact hcount) h1) hbl hn hbake h N

/-- **The same for `[7 [3 p] q]`**, given `hq3` of `finishLF_bellContract73X`. -/
theorem finishLF_bellContract73S {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm p q : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hs : SameL S Map nm (Nomm.n7 (Nomm.n3 p) q)) (hfp : FragX (S := S) p) (hfq : FragX (S := S) q)
    (hq3 : ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nx, g1) →
      noneEquivalentL nx.laz = false)
    (hcount : sixCount nm ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractSame hok hp hA hs (fun h1 => runOKU_seven3 lib (runX_ok lib hfp).2.1 (runX_semR lib hfp).2.1
    (runX_keeps hfp) (aboveX_of_fragX hfp) hfq (by rw [← hs.six]; exact hcount) hq3 h1) hbl hn hbake h N

/-- **`[7 [0 2] [7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]]` meets the
contract**, not covered before: the target under an outer `%7` whose first
step is a slot.  It compiles and computes as `[7 [4 [7 [0 2] [0 3]]] q]`,
and `[7 [0 2] [0 3]]` is in `FragX` (`FragX.sevenFrom`). -/
theorem finishLF_bellContract_slotTarget {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n0 2)
      (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 6))) (Nomm.n0 1) (Nomm.n1 (A 5))))))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n0 2) (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
      (Nomm.n6 (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 6))) (Nomm.n0 1) (Nomm.n1 (A 5))))) ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContract74S hok rfl hA ((sameL_assoc _ _ _).trans ((sameL_n7_n4 _ _).n7 (SameL.refl _)))
    (FragX.sevenFrom (by decide) (FragX.frag fun _ => trivial))
    (FragX.six (FragX.five (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)) (FragX.frag fun _ => trivial)
      (FragX.frag fun _ => trivial)) (by decide) hbl hn hbake h N

/-- `[7 [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [1 0]]`, not covered before (an
outer `%7` whose last step is a constant), meets every hypothesis of
`finishLF_bellContract74S` on the formula: it compiles and computes as
`[7 [4 [0 3]] [7 [6 [0 1] [0 1] [1 0]] [1 0]]]`, whose second part is in
`FragX` (`FragX.seven`, `[1 0]` having no `%6`). -/
example : SameL S Map (Nomm.n7 (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
      (Nomm.n1 (A 0)))
      (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n7 (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))) (Nomm.n1 (A 0)))) ∧
    FragX (S := S) (Nomm.n0 3) ∧
    FragX (S := S) (Nomm.n7 (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))) (Nomm.n1 (A 0))) ∧
    (Nomm.n7 (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
      (Nomm.n1 (A 0))).pure = true ∧
    sixCount (Nomm.n7 (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
      (Nomm.n1 (A 0))) ≤ 255 :=
  ⟨(sameL_assoc _ _ _).symm, FragX.frag fun _ => trivial,
    FragX.seven (fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)),
    rfl, by decide⟩

/-- `[6 [0 1] [7 [4 [0 3]] [0 1]] [1 0]]` makes no proxy (its raw blocks:
the `%4` writes the register of the `don` block directly, `[inc v3 v2]` hop
to `[don v2]`) and is in `FragX` (`FragX.six` over `FragX.seven`), so
`finishLF_bellContractXU` covers it. -/
example : FragX (S := S) (Nomm.n6 (Nomm.n0 1) (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n0 1)) (Nomm.n1 (A 0))) :=
  FragX.six (FragX.frag fun _ => trivial) (FragX.seven (fun _ => trivial) (FragX.four (FragX.frag fun _ => trivial)))
    (FragX.frag fun _ => trivial)

end Comp
end SkaModel
end Formalization
