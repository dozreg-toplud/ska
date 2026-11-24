import lemmas.Ska.CompFragU

/-!
# Proxy runs under a fork-free `%next`: `OKNV`

README Gaps 12.2 (seventh session).  A part of a parent that runs for a
fork-free `%next` may run after parts that made proxies, so the keys of
`cond` may lie above the goal's registers (the head of a cons runs after its
tail, and the head register was allocated by `+split` before the tail made
its proxies).  The hypothesis a parent can give in general is that no
register of the goal's need is a key of `cond` (`hkg`), which `+split`
gives for the head and tail registers (they are fresh) whatever the tail
made since (its keys are fresh too, from its start on).

* `OKNV`: what the induction proves under a fork-free `%next sur th` with
  `th` passing no argument, from a state with `Clear`, `CondBelow` and
  `hkg`: `RunOKNV`.
* `RunOKN.toNV`: a run that makes no proxy meets `RunOKNV` when its blocks
  mention only registers below its end (`BelowIn`) and no key of the start's
  `cond` (`AboveIn` with that predicate), as `RunOKP.toV`.
* `okNV_fragX`: every run of `FragX` under such a `%next` meets `OKNV`
  (`runX_above` with the predicate "no key of the start's `cond`", which
  holds of the goal's need by `hkg` and from `re` on by `CondBelow`).
* `okNV_seven4`: `runOKNV_seven4` as `OKNV`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **What the induction proves under a fork-free `%next`**: every run meets
`RunOKNV`, from a state with `Clear` and `CondBelow` in which no register
of the goal's need is a key of `cond`. -/
abbrev OKNV (lib : Lib) (nm : Nomm) : Prop :=
  ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    (∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none) →
    runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    RunOKNV (Map := Map) lib nm sur th g0 g1 nex

/-- **A run under a fork-free `%next` that makes no proxy meets `RunOKNV`**
when its blocks mention only registers below its end and no key of the
start's `cond`, the keys of `cond` lie below `re` and the goal's need has no
key. -/
theorem RunOKN.toNV {lib : Lib} {nm : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKN lib nm sur th g0 g1 nex) (hb : BelowIn g0.bo g1)
    (ha : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g1) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none) :
    RunOKNV (Map := Map) lib nm sur th g0 g1 nex := by
  have nk : ∀ x, HoonMap.get g0.cond x = Option.none → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [R.cnd]; exact hx
  have nr : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g0.cond r = Option.none := fun r hr => by
    rcases R.regs r hr with e | e
    · exact hkg r e
    · exact condBelow_none hcb e.1
  refine ⟨R.ext, R.grow, condFresh_of_eq R.ext.1 R.cnd, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs,
    R.nodup, R.size, R.nec, fun r hr => nk r (nr r hr),
    fun e he r hr => nk r (condBelow_none hcb ((R.eregs e he).2 r hr).1), ?_⟩
  intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
  have u0 : ∀ x, x < g1.re → unproxy cf x = unproxy g1.cond x := unproxy_agree hcf
  have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g1.cond x = id x :=
    fun x hx => unproxy_none (nk x hx)
  have hlab : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(R.labs e he).1, Nat.lt_trans (R.labs e he).2.1 R.hi⟩
  refine R.sem c ned σ O st t gul s0 s ⟨fun o l u hnl => ?_, fun e he => ?_⟩ hned regs hh hn
  · rw [ag.1 o l u hnl]
    cases hg : HoonMap.get g1.blocks o with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (hb o b l u hg), renBlob_congr u1 (ha o b l u hg), renBlob_id]
  · obtain ⟨A, th, h1, h2, h3⟩ := ag.2 e he
    refine ⟨A, th, h1, ?_, h3⟩
    rw [h2, renJmp_congr u0 (hb e.1 _ (hlab e he).1 (hlab e he).2 h1).2.2,
      renJmp_congr u1 (ha e.1 _ (hlab e he).1 (hlab e he).2 h1).2.2, renJmp_id]

/-- **Every run of `FragX` under a fork-free `%next` meets `OKNV`.** -/
theorem okNV_fragX (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) : OKNV (S := S) (Map := Map) lib nm := by
  intro sur th region g0 g1 nex hj hth hok hcl hc b0 d0 hu _ hcb hkg h
  have gin : GoalIn g0.re (CGoal.next sur th) := ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩
  exact ((runX_ok (Map := Map) lib hf).2.1 hj hth hok hcl hc b0 d0 hu h).toNV
    (runX_below (goal := CGoal.next sur th) hf d0 gin hc h)
    (runX_above (goal := CGoal.next sur th) hf d0 gin ⟨hkg, jmpIn_nil hth⟩
      (fun r hr => condBelow_none hcb hr) hc h) hcb hkg

/-- **`[7 [4 p] q]` with `p` and `q` in `FragX` meets `OKNV`**
(`runOKNV_seven4`). -/
theorem okNV_seven4 (lib : Lib) {p q : Nomm} (hp : FragX (S := S) p) (hq : FragX (S := S) q) :
    OKNV (S := S) (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) :=
  fun hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h =>
    runOKNV_seven4 lib (runX_ok lib hp).2.1 (runX_semR lib hp).2.1 (runX_keeps hp) (aboveX_of_fragX hp) hq hcount
      hj hth hok hcl b0 d0 hu hcl0 hcb hkg h

end Comp
end SkaModel
end Formalization
