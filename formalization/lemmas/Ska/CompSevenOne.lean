import lemmas.Ska.CompMedeE

/-!
# `[7 [1 k] q]` with a `%6` in `q`: the top theorems

The run of `q` for `%done` returns a need with entries when `q` has a `%6`
(`[6 [0 2] [0 3] [0 1]]`: the fork of the two branches' needs).  `[1 k]`
runs for it: `+mede` writes `k` into the registers of the sure need and of
every entry (`runOKE_n1`), and `runOKG_sevenE` composes the two.  With
`runX_ok` for `q` this gives the top theorems for `[7 [1 k] q]` with `q` in
`FragX` (`finishLF_bellContract71`, `crash_iff71`), for example
`[7 [1 [0 7]] [6 [0 2] [0 3] [0 1]]]`.  The case is not yet a constructor of
`FragX`, so it is covered at the top only, not nested in other nomms.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem runL_n1_next_laz {k : Noun} {laz : Lazy S} {th : Jmp} {region : List Nat} {g g' : Gen Map}
    {nex : NextL S} (h : runL (Nomm.n1 k) (CGoalL.next laz th) region g = some (nex, g')) :
    nex.laz = ofSure Sure.bunt := by
  simp only [runL] at h
  obtain ⟨o, g1, _, h2⟩ := bind_some h
  have h2' : some ((⟨ofSure Sure.bunt, jmp0 o⟩ : NextL S), g1) = some (nex, g') := h2
  cases h2'; rfl

/-- **`[7 [1 k] q]` for `%done`**, from the relation of `q` for `%done`. -/
theorem runOKP_seven1 (lib : Lib) {k : Noun} {q : Nomm} (hq : OKP (Map := Map) lib (CGoal.done : CGoal S) q)
    (hcount : sixCount q ≤ 255) {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n7 (Nomm.n1 k) q) (CGoalL.done : CGoalL S) region g0 = some (nex, g2)) :
    RunOKP (Map := Map) lib (Nomm.n7 (Nomm.n1 k) q) CGoal.done g0 g2 nex := by
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := hq trivial trivial hcount b0 d0 hu h1
  have RE := runOKE_n1 lib h2 (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu) Rq.lo Rq.hi Rq.dist
    (fun r hr => (Rq.regs r hr).2) (fun e he => ⟨(Rq.eregs e he).1, fun r hr => ((Rq.eregs e he).2 r hr).2⟩)
    Rq.nodup (fun e he => by
      obtain ⟨_, b, th, hb⟩ := Rq.labs e he
      exact ⟨by have := Rq.hi; omega, [], Termin.hop th, hb⟩)
  have hl := runL_n1_next_laz h2
  have G : RunOKG (Map := Map) lib (Nomm.n7 (Nomm.n1 k) q) (CGoal.done : CGoal S) g0 g2 nex :=
    runOKG_sevenE Rq.toG RE (fun r hr => hr.elim) (fun e _ hm => by
      rw [hl, entries_ofSure] at hm; exact absurd hm List.not_mem_nil)
  exact RunOKG.toP (show NotNext (CGoal.done : CGoal S) from trivial) G

/-- **The final pass meets the contract on `[7 [1 k] q]` with `q` in `FragX`.** -/
theorem finishLF_bellContract71 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {k : Noun} {q : Nomm} (hp : (Nomm.n7 (Nomm.n1 k) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n1 k) q))
    (hf : FragX (S := S) q) (hcount : sixCount q ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n1 k) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' :=
  finishLF_bellContractR hok hp hA
    (fun h1 => runOKP_seven1 lib (runX_ok lib hf).1 hcount (by simp [gen0]) rfl upBelow_gen0 h1) hbl hn hbake h N

/-- **The compiled code of `[7 [1 k] q]` with `q` in `FragX` crashes exactly
when the nomm does.** -/
theorem crash_iff71 (lib : Lib) {k : Noun} {q : Nomm} (hf : FragX (S := S) q) (hcount : sixCount q ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Nomm.n7 (Nomm.n1 k) q) ord less bake = some c') {σ : Type}
    (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval (Nomm.n7 (Nomm.n1 k) q) s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval (Nomm.n7 (Nomm.n1 k) q) s = some v :=
  crash_iffR lib (fun h1 => runOKP_seven1 lib (runX_ok lib hf).1 hcount (by simp [gen0]) rfl upBelow_gen0 h1)
    hbake h O st s args t gul hP hsp

/-- `[7 [1 [0 7]] [6 [0 2] [0 3] [0 1]]]`: the `%6` makes a need with forks,
which `[1 k]` meets. -/
example : FragX (S := S) (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) :=
  FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)

end Comp
end SkaModel
end Formalization
