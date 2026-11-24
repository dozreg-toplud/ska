import lemmas.Ska.CompTailGC

/-!
# A pair of runs that may both call: `pairLC_ok`

README Gaps 12.20.  The cons `[p q]` and the inner part of the indirect call
`[2 p q]` (after `+kerf`) have one shape: `+split` (or the `%nok` block)
gives the two parts' needs `lp`, `lq` and a block `o` after them; the
second part `q` runs first in compile order for `%next lq jt` (`jt` is `o`,
or a block of `+past` behind `q` that parks `lp` in a bond when `q` is
hinted), then `+past` parks `q`'s need behind `p` when `p` is hinted
(`TailGC`), then `p` runs under its goal `Lh` (`ofSure lp`, or the bond goal
`mk bunt [] [(b, lp)]`), then `+copy`.  At run time: the copy block, `p`'s
code (`GoalSemCMD`, which may move the oracle's state and leaves its witness
`d` holding `w`), `q`'s code with the input need `pair ned d`, the bond block
(`p`'s front fills `lp` from `pair ned d`), the block `o`.

`pairLC_ok` composes them for any formula `f` whose `+mink` is built from the
parts' (`Mf`, `Mb`, with the last step `Fin`, `FinB`: the cell of the two
products for the cons, `+mink` on them for the call) and any block `o` whose
code meets the goal from the two products (`hA`, `hAB`).  Its head `p` and
tail `q` may both call: `p` meets `RunOKLC` under `Lh`, `q` meets `TailGC`.

* `TotalC`: a formula that never blocks and halts (what a call-free part's
  `MinkEq` gives), needed where a failure is found after the other part ran.
* `goalSemCM_bad`, `goalSemCM_monoK`.
* `pairLC_ok`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A formula that never blocks and halts** on the subjects of `P`. -/
def TotalC (lib : Lib) (P : Noun → Prop) (f : Noun) : Prop :=
  (∀ s gul n tm r, P s → minkF lib gul n tm s f = some r → r = Tone.two tm ∨ ∃ y, r = Tone.zero y) ∧
  (∀ s gul tm, P s → ∃ r, Mink lib gul tm s f r ∧ (r = Tone.two tm ∨ ∃ y, r = Tone.zero y))

theorem totalC_of_minkEq {lib : Lib} {P : Noun → Prop} {f : Noun} {nm : Nomm} (M : MinkEq lib P f nm) :
    TotalC lib P f := by
  have B : ∀ tm s, toneOf tm (pureEval nm s) = Tone.two tm ∨ ∃ y, toneOf tm (pureEval nm s) = Tone.zero y :=
    fun tm s => by
      cases pureEval nm s with
      | none => exact Or.inl rfl
      | some y => exact Or.inr ⟨y, rfl⟩
  refine ⟨fun s gul n tm r hs hm => ?_, fun s gul tm hs => ⟨_, (M s hs gul tm _).mpr rfl, B tm s⟩⟩
  rw [(M s hs gul tm r).mp ⟨n, hm⟩]
  exact B tm s

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- A tone that is a failure for a `%next` goal, where the code crashed. -/
theorem goalSemCM_bad {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {r : Tone} (hb : BadC (CGoal.next sur th) tm r)
    (H : ReturnsC lib O c gul Inv ν st regs t je (Tone.two tm)) :
    GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) r := by
  rcases hb with rfl | ⟨p, rfl, hp⟩
  · exact H
  · exact ⟨fun f => absurd f hp, fun _ => H⟩

theorem goalSemCM_monoK {K K' : Nat → Prop} (hK : ∀ x, K' x → K x) {st : σ} {regs : Map (Option Noun)}
    {t tm : Trace} {je : Jmp} : ∀ (goal : CGoal S) (r : Tone),
    GoalSemCM lib O c gul Inv ν K st regs t tm je goal r → GoalSemCM lib O c gul Inv ν K' st regs t tm je goal r
  | CGoal.done, _, H => H
  | CGoal.next _ _, Tone.zero _, H => ⟨fun hf => by
      obtain ⟨st', R, hI, hle, h1, h2, h3⟩ := H.1 hf
      exact ⟨st', R, hI, hle, h1, fun x hx => h2 x (hK x hx), h3⟩, H.2⟩
  | CGoal.next _ _, Tone.one _, H => H
  | CGoal.next _ _, Tone.two _, H => H
  | CGoal.pick _ _, Tone.zero _, H => ⟨fun h0 => by
      obtain ⟨st', R, hI, hle, h1, h2, h3⟩ := H.1 h0
      exact ⟨st', R, hI, hle, h1, fun x hx => h2 x (hK x hx), h3⟩, fun h1' => by
      obtain ⟨st', R, hI, hle, h1, h2, h3⟩ := H.2.1 h1'
      exact ⟨st', R, hI, hle, h1, fun x hx => h2 x (hK x hx), h3⟩, H.2.2⟩
  | CGoal.pick _ _, Tone.one _, H => H
  | CGoal.pick _ _, Tone.two _, H => H

end


/-! ## The composition -/

/-- **A pair of runs that may both call, under a fork-free `%next sur th`**
(see the header).  `Mf`, `Mb`: `+mink` on `f` runs `fh`, then `ft`, then the
last step `Fin` (forward, with less fuel) or `FinB` (backward).  `hjt`: the
second part runs into the block `o` and the first part's goal is `ofSure lp`
(then a first part whose product does not fit `lp` is caught before the
second part runs, so the second part must not block: `lp` fits everything or
`TotalC`), or into a bond block `[hop o]` at `g'.bo` and the first part's
goal is the bond goal.  `hhd`: the second part's need fits every subject
(it is parked behind the first part) or the first part does not block
(`TotalC`).  `hA`, `hAB`: the code from `o` meets the goal from the two
products.  `hnotF`, `hnotB`: a product that does not fit its part's need
makes the whole fail.  Both `sem` clauses go through one `core`. -/
theorem pairLC_ok {lib : Lib} {P : Noun → Prop} {f fh ft : Noun} {sur : Sure S} {th : Jmp}
    {g0 g' gb g1 g2 g3 : Gen Map} {lp lq : Sure S} {o : Nat} {jt : Jmp} {Lh : Lazy S} {Qh : Wit}
    {nexq nexp nex : NextL S}
    {Fin : Noun → Nat → Trace → Noun → Noun → Tone → Prop} {FinB : Noun → Trace → Noun → Noun → Tone → Prop}
    (Mf : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
      ∃ n', n' < n ∧ ∃ rh, minkF lib gul n' tm s fh = some rh ∧
        (((∀ q, rh ≠ Tone.zero q) ∧ r = rh) ∨ ∃ x, rh = Tone.zero x ∧ ∃ rt, minkF lib gul n' tm s ft = some rt ∧
          (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ Fin gul n' tm x y r)))
    (Mb : ∀ {s gul : Noun} {tm : Trace} {rh : Tone}, P s → Mink lib gul tm s fh rh →
      ((∀ q, rh ≠ Tone.zero q) → Mink lib gul tm s f rh) ∧
      ∀ x rt, rh = Tone.zero x → Mink lib gul tm s ft rt →
        ((∀ q, rt ≠ Tone.zero q) → Mink lib gul tm s f rt) ∧
        ∀ y r, rt = Tone.zero y → FinB gul tm x y r → Mink lib gul tm s f r)
    (hg : GoalOK g0 (CGoal.next sur th)) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hcb : CondBelow g0)
    (hlp : ∀ r, NMem lp.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hgb : Ext g' gb) (hgbU : GrowU g' gb) (hgbc : gb.cond = g'.cond) (hgbre : gb.re = g'.re)
    (hjt : (jt = jmp0 o ∧ Lh = ofSure lp ∧ ((∀ x, FitsS lp x) ∨ TotalC lib P ft)) ∨
      (jt = jmp0 g'.bo ∧ Lh = mk Sure.bunt [] [(g'.bo, ofSure lp)] ∧ g'.bo < gb.bo ∧
        HoonMap.get gb.blocks g'.bo = some ⟨[], [], Termin.hop (jmp0 o)⟩))
    (hhd : (∀ s, FitsS nexq.laz.sure s) ∨ TotalC lib P fh)
    (hq : TailGC (Map := Map) lib P ft lq jt gb g1 nexq)
    (hp : RunOKLC (Map := Map) lib P fh Lh nexq.th Qh g1 g2 nexp)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3))
    (hu : UpBelow g0) (d0 : g0.drop = false)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hnotF : ∀ gul n' tm x y r, (¬ FitsS lp x ∨ ¬ FitsS lq y) → Fin gul n' tm x y r →
      BadC (CGoal.next sur th) tm r)
    (hnotB : ∀ gul tm x y, (¬ FitsS lp x ∨ ¬ FitsS lq y) → ∃ r, FinB gul tm x y r ∧ BadC (CGoal.next sur th) tm r)
    (hA : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (n : Nat) (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun) (n' : Nat) (r : Tone), n' < n → Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y → Fin gul n' tm x y r →
        GoalSemCM lib O c gul Inv ν (Keep g0 g' (CGoal.next sur th)) st regs t tm (jmp0 o) (CGoal.next sur th) r)
    (hAB : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun), Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y → ∀ res, goJ lib O c gul st regs t (jmp0 o) = some res →
        ∃ r, FinB gul tm x y r ∧
          GoalSemCM lib O c gul Inv ν (Keep g0 g' (CGoal.next sur th)) st regs t tm (jmp0 o) (CGoal.next sur th) r) :
    RunOKGC lib P f (CGoal.next sur th) g0 g3 nex ∧ g0.bo ≤ nex.th.there := by
  -- the head's goal
  have hLs' : ∀ r, NMem Lh.sure.ned r → NMem lp.ned r := fun r hr => by
    rcases hjt with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · exact hr
    · exact absurd hr (by simp [Sure.bunt, NMem])
  have labLh : ∀ e ∈ entries Lh, e = (g'.bo, ofSure lp) ∧ g'.bo < gb.bo := fun e he => by
    rcases hjt with ⟨_, rfl, _⟩ | ⟨_, rfl, h', _⟩
    · rw [entries_ofSure] at he; cases he
    · rw [entries_bond1] at he; simp only [List.mem_singleton] at he; exact ⟨he, h'⟩
  have labLh' : ∀ k, k ∈ (entries Lh).map Prod.fst → k = g'.bo ∧ g'.bo < gb.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨rfl, h⟩ := labLh e he
    exact ⟨rfl, h⟩
  have jta : jt.args = [] := by rcases hjt with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have b0' := hpre.2.1
  have bgb := hgb.2.1
  have b1 := hq.ext.2.1
  have b2 := hp.bo
  have r0' := hpre.1
  have rgb := hgb.1
  have r1 := hq.ext.1
  have r2 := hp.re
  have k21 : ∀ k, k < g1.bo → k ∉ (entries Lh).map Prod.fst → HoonMap.get g2.blocks k = HoonMap.get g1.blocks k :=
    fun k hk hn => hp.keep k hk hn
  have lq' : ∀ e ∈ entries nexq.laz, gb.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(hq.labs e he).1, Nat.lt_of_le_of_lt (hq.labs e he).2.1 hq.hi⟩
  have lp' : ∀ e ∈ entries nexp.laz, ((e.1 = g'.bo ∧ g'.bo < gb.bo) ∨ g1.bo ≤ e.1) ∧ e.1 < g2.bo := fun e he => by
    rcases (hp.labs e he).1 with h | h
    · have := labLh' e.1 h
      exact ⟨Or.inl this, by omega⟩
    · have := hp.hi
      exact ⟨Or.inr h.1, by omega⟩
  have apF : ∀ e ∈ nexp.laz.fork, ∀ e' ∈ nexq.laz.fork, e.1.1 ≠ e'.1.1 := fun e he e' he' => by
    have a := lp' e.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he))
    have b := lq' e'.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he'))
    omega
  have apB : ∀ e ∈ nexp.laz.bond, ∀ e' ∈ nexq.laz.bond, e.1 ≠ e'.1 := fun e he e' he' => by
    have a := lp' e (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he))
    have b := lq' e' (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he'))
    omega
  have kc3 := (kc_copyL _ _).keep _ _ _ hc
  obtain ⟨n, hcp, rfl⟩ := copyL_apart_some apF apB hc
  obtain ⟨EC, eth, bo3, CM, CS⟩ := copy_ok hcp
  have gm : ∀ r, GMem (CGoal.next sur th : CGoal S) r → r < g0.re := fun r hr => hg.2 r hr
  have lpl : ∀ r, NMem lp.ned r → r < g'.re := fun r hr => by
    rcases hlp r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have lql : ∀ r, NMem lq.ned r → r < g'.re := fun r hr => by
    rcases hlq r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have mp : ∀ r, NMem nexp.laz.sure.ned r → NMem lp.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := fun r hr =>
    (hp.regs r hr).imp_left (hLs' r)
  have mq : ∀ r, NMem nexq.laz.sure.ned r → NMem lq.ned r ∨ (gb.re ≤ r ∧ r < g1.re) := hq.regs
  have l3 := EC.1
  have lowP : ∀ r, NMem nexp.laz.sure.ned r → r < g2.re := fun r hr => by
    rcases mp r hr with a | ⟨_, a⟩
    · have := lpl r a; omega
    · exact a
  have lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases mq r hr with a | ⟨_, a⟩
    · have := lql r a; omega
    · exact a
  have P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · rcases mp r h1 with a | a
      · rcases mq r h2 with b | b
        · exact hpq r a b
        · have := lpl r a; omega
      · rcases mq r h2 with b | b
        · have := lql r b; omega
        · omega
    · rcases hr with h | h
      · exact lowP r h
      · have := lowQ r h; omega
  obtain ⟨CD, CF, CB⟩ := CS P0
  have d2 : g2.drop = false := hp.drop.trans (hq.ext.2.2.1.trans (hgb.2.2.1.trans (hpre.2.2.1.trans d0)))
  have Dc := copy_down (goal := CGoal.next sur th) hcp hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  have G2 : GrowU g0 g2 := hgr.trans (hgbU.trans (hq.grow.trans hp.grow))
  have u2 : UpBelow g2 := G2.up hu
  have hp3 : Ext g2 g3 := EC
  have CF2 : CondFresh g0 g2 :=
    ((condFresh_of_eq hpre.1 hcnd).trans (condFresh_of_eq hgb.1 hgbc)).trans (hq.cfr.trans hp.cfr)
  have cb2 : CondBelow g2 := CF2.below hcb
  have nkq : ∀ r, NMem nexq.laz.sure.ned r → HoonMap.get g2.cond r = Option.none := fun r h => by
    rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h
  have thq : nexq.th.args = [] := nextArgs_nil hq.ent jta
  have thp : nexp.th.args = [] := nextArgs_nil hp.ent thq
  have AC : AboveIn (fun r => HoonMap.get g2.cond r = Option.none) g2.bo g3 :=
    (keepsA_copy (P := fun r => HoonMap.get g2.cond r = Option.none) (first := ⟨nexp.laz.sure, nexp.th⟩) d2
      ⟨hp.ncond, jmpIn_nil thp⟩ nkq (fun r hr => condBelow_none cb2 hr) hcp).1.ab _ (aboveIn_start _ g2)
  have BC : BelowIn g2.bo g3 :=
    (keeps_copy (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨fun r hr => lowP r hr, jmpIn_nil thp⟩
      (fun r hr => by have := lowQ r hr; omega) hcp).1.bel _ (belowIn_start g2)
  have fixC : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ k, g2.bo ≤ k → k < g3.bo → (HoonMap.get g3.blocks k).map (unproxyBlob cf) = HoonMap.get g3.blocks k := by
    intro cf hcf k h0 h1
    have u0 : ∀ x, x < g3.re → unproxy cf x = unproxy g3.cond x := unproxy_agree hcf
    have u1 : ∀ x, HoonMap.get g2.cond x = Option.none → unproxy g3.cond x = id x :=
      fun x hx => unproxy_none (by rw [kc3]; exact hx)
    cases hg : HoonMap.get g3.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BC k b h0 h1 hg), renBlob_congr u1 (AC k b h0 h1 hg), renBlob_id]
  have mid3 : ∀ k, k < g1.bo → k ∉ (entries Lh).map Prod.fst →
      HoonMap.get g3.blocks k = HoonMap.get g1.blocks k := fun k hk hn => by
    rw [hp3.2.2.2 k (by omega), k21 k hk hn]
  have low3 : ∀ k, k < g'.bo → HoonMap.get g3.blocks k = HoonMap.get g'.blocks k := fun k hk => by
    rw [mid3 k (by omega) (fun hm => by have := labLh' k hm; omega), hq.ext.2.2.2 k (by omega),
      hgb.2.2.2 k hk]
  have memN : ∀ e, e ∈ entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork) (nexp.laz.bond ++ nexq.laz.bond)) ↔
      e ∈ entries nexp.laz ∨ e ∈ entries nexq.laz := fun e => by
    rw [(entries_side_perm _ _ _).mem_iff, List.mem_append]
  have labN : ∀ k, k ∈ (entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork)
      (nexp.laz.bond ++ nexq.laz.bond))).map Prod.fst → g'.bo ≤ k ∧ k < g2.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    rcases (memN e).mp he with a | a
    · have := lp' e a; omega
    · have := lq' e a; omega
  -- the registers of the head's goal lie below the tail's start
  have nLs : ∀ r, NMem Lh.sure.ned r → r < g'.re := fun r hr => lpl r (hLs' r hr)
  -- the shared part of the two `sem` clauses
  have core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g3
        (mk n.laz (nexp.laz.fork ++ nexq.laz.fork) (nexp.laz.bond ++ nexq.laz.bond)) s0 s) →
      (∀ x, NMem ned x → g3.re ≤ x) →
      ∀ regs, HoldsS n.laz regs s → HoldsN ned regs s0 →
      ∃ R1, Agree c g0 g' ∧ (∀ st' : σ, AgreeL lib O c gul st' t cf ned g1 g2 nexp.laz s0 s) ∧
        (∀ x, NMem ned x → g2.re ≤ x) ∧
        HoldsS nexp.laz.sure R1 s ∧ HoldsN ned R1 s0 ∧
        goJ lib O c gul st regs t n.th = goJ lib O c gul st R1 t nexp.th ∧
        (∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem sur.ned z) → SkaModel.read z R1 = SkaModel.read z regs) ∧
        ∀ (x : Noun) (R2 : Map (Option Noun)) (d : Need) (w : Noun), Qh s x d w → FitsS Lh.sure x →
          HoldsN Lh.sure.ned R2 x → HoldsN d R2 w →
          (∀ z, ((z < g1.re ∨ NMem ned z) ∧ ¬ NMem Lh.sure.ned z) → SkaModel.read z R2 = SkaModel.read z R1) →
          (∀ st' : σ, AgreeU lib O c gul st' t cf (Need.pair ned d) gb g1 nexq.laz (C s0 w) s) ∧
          (∀ z, NMem (Need.pair ned d) z → g1.re ≤ z) ∧ HoldsS nexq.laz.sure R2 s ∧
          HoldsN (Need.pair ned d) R2 (C s0 w) ∧
          ∀ (st2 : σ) (R3 : Map (Option Noun)) (y : Noun), HoldsN lq.ned R3 y →
            (∀ z, ((z < gb.re ∨ NMem (Need.pair ned d) z) ∧ ¬ NMem lq.ned z) →
              SkaModel.read z R3 = SkaModel.read z R2) →
            (FitsS lp x → ∃ R4, HoldsN lp.ned R4 x ∧ HoldsN lq.ned R4 y ∧
              (∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem sur.ned z) → SkaModel.read z R4 = SkaModel.read z regs) ∧
              goJ lib O c gul st2 R3 t jt = goJ lib O c gul st2 R4 t (jmp0 o)) ∧
            (¬ FitsS lp x → goJ lib O c gul st2 R3 t jt = some (Tone.two t, st2)) := by
    intro cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf1 k (by omega)).trans ((hq.cfr.get_lt (by omega)).trans (by rw [hgbc, hcnd]))
    have agC : Agree c g2 g3 := fun k h0 h1 => by
      rw [(ag st).1 k (by omega) h1 (fun hm => by have := labN k hm; omega)]
      exact fixC cf hcf k h0 h1
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
    have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
      have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : ∀ st' : σ, AgreeL lib O c gul st' t cf ned g1 g2 nexp.laz s0 s := fun st' =>
      ((ag st').part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)).toL
    have agQ0 : Agree c g0 g' := fun k h0 h1 => by
      rw [(ag st).1 k h0 (by omega) (fun hm => by have := labN k hm; omega), low3 k h1]
      exact hfix cf hcf0 k h0 h1
    -- the composite's kept registers lie outside both parts' needs
    have nlpK : ∀ z, (z < g0.re ∨ NMem ned z) → ¬ GMem (CGoal.next sur th) z → ¬ NMem lp.ned z :=
      fun z k1 k2 hm => by
        rcases hlp z hm with b | ⟨b, b'⟩
        · exact k2 b
        · rcases k1 with k1 | k1
          · omega
          · have := hned z k1; omega
    have nlqK : ∀ z, (z < g0.re ∨ NMem ned z) → ¬ GMem (CGoal.next sur th) z → ¬ NMem lq.ned z :=
      fun z k1 k2 hm => by
        rcases hlq z hm with b | ⟨b, b'⟩
        · exact k2 b
        · rcases k1 with k1 | k1
          · omega
          · have := hned z k1; omega
    have keep1 : ∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem sur.ned z) → SkaModel.read z R1 = SkaModel.read z regs :=
      fun z ⟨k1, k2⟩ => u1 z (fun hm => by
          rcases mp z hm with a | ⟨a, _⟩
          · exact nlpK z k1 k2 a
          · rcases k1 with k1 | k1
            · omega
            · have := hned z k1; omega)
        (fun hm => by
          rcases mq z hm with a | ⟨a, _⟩
          · exact nlqK z k1 k2 a
          · rcases k1 with k1 | k1
            · omega
            · have := hned z k1; omega)
    refine ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, fun x R2 d w hqd fx hx2 hd2 k2 => ?_⟩
    have hdD : ∀ r, NMem d r → g1.re ≤ r ∧ r < g2.re := fun r hr => hp.dreg s x d w r hqd hr
    have nLsN : ∀ r, NMem ned r → ¬ NMem Lh.sure.ned r := fun r hr hm => by
      have := nLs r hm; have := hned r hr; omega
    have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, nLsN r hr⟩) hn1
    have nlq : ∀ r, NMem (Need.pair ned d) r → ¬ NMem lq.ned r := fun r hr hm => by
      have := lql r hm
      rcases hr with h | h
      · have := hned r h; omega
      · have := (hdD r h).1; omega
    -- the kept registers from `R3` back to `regs`
    have keep3 : ∀ (R3 : Map (Option Noun)),
        (∀ z, ((z < gb.re ∨ NMem (Need.pair ned d) z) ∧ ¬ NMem lq.ned z) → SkaModel.read z R3 = SkaModel.read z R2) →
        ∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem sur.ned z) → SkaModel.read z R3 = SkaModel.read z regs :=
      fun R3 k3 z ⟨k1, k2'⟩ => by
        rw [k3 z ⟨k1.imp (fun h => by omega) (fun h => Or.inl h), nlqK z k1 k2'⟩,
          k2 z ⟨k1.imp (fun h => by omega) id, fun hm => nlpK z k1 k2' (hLs' z hm)⟩]
        exact keep1 z ⟨k1, k2'⟩
    refine ⟨fun st' => ⟨fun k h0 h1 hnk => ?_, fun e he => ?_⟩, fun y hy => ?_,
      ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), fun hm => ?_⟩) hs1'.1, hs1'.2⟩, ⟨hn2, hd2⟩,
      fun st2 R3 y hy3 k3 => ?_⟩
    · -- the tail's `AgreeU`
      have hk : k ∉ (entries Lh).map Prod.fst := fun hm => by have := labLh' k hm; omega
      rw [(ag st').1 k (by omega) (by omega) (fun hm => by
        obtain ⟨e, he, e1'⟩ := List.mem_map.mp hm
        rcases (memN e).mp he with a | a
        · rcases (lp' e a).1 with b | b
          · omega
          · omega
        · exact hnk (by rw [← e1']; exact List.mem_map_of_mem a)), mid3 k h1 hk]
    · obtain ⟨A0, th0, b3, c3, f3⟩ := (ag st').2 e ((memN e).mpr (Or.inr he))
      have hk : e.1 ∉ (entries Lh).map Prod.fst := fun hm => by
        have := labLh' e.1 hm; have := lq' e he; omega
      refine ⟨A0, th0, by rw [← mid3 e.1 (lq' e he).2 hk]; exact b3, c3, ?_⟩
      exact (f3.pair d (fun r hr => by have := hdD r hr; omega) w).mono (by omega)
    · rcases hy with h | h
      · have := hned y h; omega
      · exact (hdD y h).1
    · -- a register of the tail's need is none of the head's goal's
      have := hLs' r hm
      rcases mq r hr with a | ⟨a, _⟩
      · exact hpq r this a
      · have := lpl r this; omega
    -- after the tail: at `jt`
    have hn3 : HoldsN (Need.pair ned d) R3 (C s0 w) :=
      HoldsN.agree _ (fun r hr => k3 r ⟨Or.inr hr, nlq r hr⟩) ⟨hn2, hd2⟩
    rcases hjt with ⟨rfl, hLe, _⟩ | ⟨rfl, hLe, hlt, hbb⟩
    · -- no bond: `lp` held since the head's end
      subst hLe
      refine ⟨fun _ => ⟨R3, HoldsN.agree _ (fun r hr => k3 r ⟨Or.inl (by have := lpl r hr; omega),
        hpq r hr⟩) hx2, hy3, keep3 R3 k3, rfl⟩, fun nf => absurd fx nf⟩
    · -- the bond block: the head's front fills `lp`
      have hmem : (g'.bo, ofSure lp) ∈ entries Lh := by rw [hLe, entries_bond1]; exact List.mem_singleton.mpr rfl
      obtain ⟨F, hF, SF⟩ := hp.front _ hmem
      have hb1 : HoonMap.get g1.blocks g'.bo = some ⟨[], [], Termin.hop (jmp0 o)⟩ := by
        rw [hq.ext.2.2.2 _ hlt]; exact hbb
      have hb2 := hF [] (Termin.hop (jmp0 o)) hb1
      rw [List.append_nil] at hb2
      have hb3 : HoonMap.get g3.blocks g'.bo = some ⟨[], F, Termin.hop (jmp0 o)⟩ := by
        rw [hp3.2.2.2 _ (by omega)]; exact hb2
      obtain ⟨Af, hcb', FS⟩ : ∃ Af, HoonMap.get c.blocks g'.bo = some ⟨[], Af, Termin.hop (jmp0 o)⟩ ∧
          FillSem lib O c gul st2 t (Need.pair ned d) g1.re lp Af (C s0 w) x := by
        rcases SF cf hcf2 with ⟨L', hL', FP⟩ | ⟨hn2', FP⟩
        · obtain ⟨A0, th'', hb3', hc3, hf3⟩ := (ag st2).2 (g'.bo, L') ((memN _).mpr (Or.inl hL'))
          rw [hb3] at hb3'
          simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3'
          obtain ⟨rfl, rfl⟩ := hb3'
          refine ⟨A0, by rw [hc3, renJmp_nil _ (show (jmp0 o).args = [] from rfl)], ?_⟩
          have := FP lib σ O c gul st2 t ned A0 s0 s x d w hned2 hqd (hf3.mono (by omega))
          rw [List.map_nil, List.append_nil] at this
          exact this
        · refine ⟨[] ++ F.map (renPole (unproxy cf)), ?_, FP lib σ O c gul st2 t ned [] s0 s x d w hned2 hqd
            fillSem_bunt_nil⟩
          rw [(ag st2).1 g'.bo (by omega) (by omega) (fun hm => by
            obtain ⟨e, he, e1'⟩ := List.mem_map.mp hm
            rcases (memN e).mp he with a | a
            · exact hn2' (List.mem_map.mpr ⟨e, a, e1'⟩)
            · have := lq' e a; omega), hb3]
          simp only [Option.map_some, unproxyBlob, renBlob, renFin, List.nil_append, List.map_nil,
            renJmp_nil _ (show (jmp0 o).args = [] from rfl)]
      obtain ⟨F1, F2⟩ := FS R3 hn3
      refine ⟨fun fxp => ?_, fun nfx => ?_⟩
      · obtain ⟨R4, r4, hl4, k4⟩ := F1 fxp
        have e4 : goJ lib O c gul st2 R3 t (jmp0 g'.bo) = goJ lib O c gul st2 R4 t (jmp0 o) := by
          have := r4 [] (Termin.hop (jmp0 o))
          simp only [List.append_nil] at this
          rw [goJ_jmp0 _ _ _ _ hcb', this, execBlob_hop]
        refine ⟨R4, hl4.1, HoldsN.agree _ (fun r hr => k4 r (Or.inr (by have := lql r hr; omega))
          (fun hm => hpq r hm hr)) hy3, fun z hz => ?_, e4⟩
        obtain ⟨k1, k2'⟩ := hz
        rw [k4 z (k1.elim (fun h => Or.inr (by omega)) (fun h => Or.inl (Or.inl h))) (nlpK z k1 k2')]
        exact keep3 R3 k3 z ⟨k1, k2'⟩
      · have := F2 nfx [] (Termin.hop (jmp0 o))
        simp only [List.append_nil] at this
        rw [goJ_jmp0 _ _ _ _ hcb', this]
  have hcase : ∀ x, ¬ FitsS Lh.sure x → ¬ FitsS lp x ∧ TotalC lib P ft := fun x hx => by
    rcases hjt with ⟨_, rfl, hfl⟩ | ⟨_, rfl, _⟩
    · exact ⟨hx, hfl.resolve_left (fun h => hx (h x))⟩
    · exact absurd (fitsS_bunt x) hx
  refine ⟨{
    ext := ⟨by omega, by omega, by rw [hp3.2.2.1, d2, d0], fun k hk => by rw [low3 k (by omega), hpre.2.2.2 k hk]⟩
    grow := G2.trans (Dc.grow.toU u2)
    cfr := CF2.trans (condFresh_of_eq EC.1 kc3)
    lo := Dc.lo
    hi := Dc.hi
    ent := Dc.entry
    regs := fun r hr => ?_
    dist := CD
    eregs := fun e he => ?_
    labs := fun e he => ?_
    nodup := ?_
    nec := fun s hs hf => ?_
    ncond := fun r hr => ?_
    econd := fun e he r hr => ?_
    sem := fun cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn => ?_
    semB := fun cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres => ?_ }, ?_⟩
  · rcases CM r hr with h | h | ⟨h, h'⟩
    · rcases mp r h with a | ⟨a, a'⟩
      · rcases hlp r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases mq r h with a | ⟨a, a'⟩
      · rcases hlq r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h'⟩
  · rcases (memN e).mp he with a | a
    · refine ⟨(hp.eregs e a).1, fun r hr => ?_⟩
      have hlpr : NMem lp.ned r → (GMem (CGoal.next sur th) r ∨ g0.re ≤ r) ∧ r < g3.re := fun h0 => by
        rcases hlp r h0 with b' | ⟨b', _⟩
        · exact ⟨Or.inl b', by have := gm r b'; omega⟩
        · exact ⟨Or.inr b', by have := lpl r h0; omega⟩
      rcases (hp.eregs e a).2 r hr with ⟨e0, he0, h0⟩ | h0 | h0
      · obtain ⟨rfl, _⟩ := labLh e0 he0; exact hlpr h0
      · exact hlpr (hLs' r h0)
      · exact ⟨Or.inr (by omega), by omega⟩
    · refine ⟨(hq.eregs e a).1, fun r hr => ⟨?_, by have := ((hq.eregs e a).2 r hr).2; omega⟩⟩
      rcases ((hq.eregs e a).2 r hr).1 with b | b
      · rcases hlq r b with b' | ⟨b', _⟩
        · exact Or.inl b'
        · exact Or.inr b'
      · exact Or.inr (by omega)
  · show g0.bo ≤ e.1 ∧ e.1 < n.th.there ∧ _
    rw [eth]
    simp only [jmp0]
    rcases (memN e).mp he with a | a
    · obtain ⟨_, th', z⟩ := hp.labs e a
      have := lp' e a
      exact ⟨by omega, by omega, th', by rw [hp3.2.2.2 _ (by omega)]; exact z⟩
    · obtain ⟨x, y, th', z⟩ := hq.labs e a
      have := hq.hi
      have hk : e.1 ∉ (entries Lh).map Prod.fst := fun hm => by have := labLh' e.1 hm; omega
      exact ⟨by omega, by omega, th', by rw [mid3 e.1 (by omega) hk]; exact z⟩
  · rw [((entries_side_perm _ _ _).map Prod.fst).nodup_iff, List.map_append, List.nodup_append]
    refine ⟨hp.nodup, hq.nodup, fun a ha b hb => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    have := lp' e he; have := lq' e' he'; omega
  · -- nec
    by_cases a : FitsS nexp.laz.sure s
    · have b : ¬ FitsS nexq.laz.sure s := fun b => hf ((CF s).mpr ⟨a, b⟩)
      have NQ := hq.nec s hs b
      have HT : TotalC lib P fh := hhd.resolve_left (fun h => b (h s))
      refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
      · obtain ⟨n', _, rh, hmh, H⟩ := Mf hs hm
        rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
        · rcases HT.1 s gul n' tm _ hs hmh with e | ⟨y, e⟩
          · exact Or.inl e
          · exact absurd e (hnz y)
        · rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
          · rcases NQ.1 gul n' tm _ hmt with e | ⟨q, e, _⟩
            · exact Or.inl e
            · exact absurd e (hnz q)
          · rcases NQ.1 gul n' tm _ hmt with e | ⟨q, e, hq'⟩
            · cases e
            · obtain rfl : y = q := by cases e; rfl
              exact hnotF gul n' tm x y r (Or.inr hq') hfin
      · obtain ⟨rh, hmh, hrh⟩ := HT.2 s gul tm hs
        rcases hrh with rfl | ⟨x, rfl⟩
        · exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e), Or.inl rfl⟩
        · obtain ⟨rt, hmt, hbt⟩ := NQ.2 gul tm
          rcases hbt with rfl | ⟨y, rfl, hy⟩
          · exact ⟨_, ((Mb hs hmh).2 x _ rfl hmt).1 (fun _ e => by cases e), Or.inl rfl⟩
          · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inr hy)
            exact ⟨r, ((Mb hs hmh).2 x _ rfl hmt).2 y r rfl hfr, hbr⟩
    · have NP := hp.nec s hs a
      refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
      · obtain ⟨n', _, rh, hmh, H⟩ := Mf hs hm
        rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
        · rcases NP.1 gul n' tm _ hmh with e | ⟨q, e, _⟩
          · exact Or.inl e
          · exact absurd e (hnz q)
        · rcases NP.1 gul n' tm _ hmh with e | ⟨q, e, hq'⟩
          · cases e
          · obtain rfl : x = q := by cases e; rfl
            obtain ⟨nfx, TT⟩ := hcase x hq'
            rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
            · rcases TT.1 s gul n' tm _ hs hmt with e | ⟨y, e⟩
              · exact Or.inl e
              · exact absurd e (hnz y)
            · exact hnotF gul n' tm x y r (Or.inl nfx) hfin
      · obtain ⟨rh, hmh, hbh⟩ := NP.2 gul tm
        rcases hbh with rfl | ⟨x, rfl, hx⟩
        · exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e), Or.inl rfl⟩
        · obtain ⟨nfx, TT⟩ := hcase x hx
          obtain ⟨rt, hmt, hrt⟩ := TT.2 s gul tm hs
          rcases hrt with rfl | ⟨y, rfl⟩
          · exact ⟨_, ((Mb hs hmh).2 x _ rfl hmt).1 (fun _ e => by cases e), Or.inl rfl⟩
          · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inl nfx)
            exact ⟨r, ((Mb hs hmh).2 x _ rfl hmt).2 y r rfl hfr, hbr⟩
  · rw [kc3]
    rcases CM r hr with h | h | ⟨h, h'⟩
    · exact hp.ncond r h
    · rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h
    · exact condBelow_none cb2 h
  · rw [kc3]
    rcases (memN e).mp he with a | a
    · exact hp.econd e a r hr
    · rw [hp.cfr.get_lt ((hq.eregs e a).2 r hr).2]; exact hq.econd e a r hr
  · -- forward
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    obtain ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, K⟩ := core cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
    obtain ⟨n', hn', rh, hmh, H⟩ := Mf hs hm
    have Gh := hp.sem cf hcf2 c ned σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rh hI htr
      hs hmh agP hned2 R1 hs1 hn1
    rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
    · exact goalSemCM_ret _ _ hnz (returnsC_step (Needs.le_refl _) e1 (returnsC_of_goalSemCMD hnz Gh))
    by_cases fx : FitsS Lh.sure x
    · obtain ⟨st1, R2, d, w, hI1, hν1, hqd, hx2, hd2, k2, e2⟩ := Gh.1 fx
      obtain ⟨agQ, hnQ, hsQ, hnQ', J⟩ := K x R2 d w hqd fx hx2 hd2 k2
      have htr1 := frames_mono hν1 htr
      have Gq := hq.sem cf hcf1 c (Need.pair ned d) σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st1 t
        tm (C s0 w) s rt hI1 htr1 hs hmt agQ hnQ R2 hsQ hnQ'
      have e12 := e1.trans e2
      rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
      · exact goalSemCM_ret _ _ hnz (returnsC_step hν1 e12 (returnsC_of_goalSemCM _ _ hnz Gq))
      by_cases fy : FitsS lq y
      · obtain ⟨st2, R3, hI2, hν2, hy3, k3, e3⟩ := Gq.1 fy
        obtain ⟨Jf, Jn⟩ := J st2 R3 y hy3 k3
        by_cases fxp : FitsS lp x
        · obtain ⟨R4, hx4, hy4, k4, e4⟩ := Jf fxp
          have A := hA c agQ0 σ Inv ν O n gul hS hF st2 R4 t tm x y n' r hn' hI2 (frames_mono hν2 htr1) fxp fy hx4
            hy4 hfin
          exact goalSemCM_step (Needs.le_trans hν1 hν2) k4 (e12.trans (e3.trans e4)) _ _
            (goalSemCM_monoK (fun z hz => ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) _ _ A)
        · exact goalSemCM_bad (hnotF gul n' tm x y r (Or.inl fxp) hfin)
            ⟨Tone.two t, st2, hI2, Needs.le_trans hν1 hν2, e12.trans (e3.trans (Jn fxp)),
              ToneRel.two (frames_mono hν2 htr1)⟩
      · exact goalSemCM_bad (hnotF gul n' tm x y r (Or.inr fy) hfin) (returnsC_step hν1 e12 (Gq.2 fy))
    · have R0 := Gh.2 fx
      obtain ⟨nfx, TT⟩ := hcase x fx
      rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
      · rcases TT.1 s gul n' tm _ hs hmt with e | ⟨y, e⟩
        · subst e
          exact goalSemCM_ret _ _ (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 R0)
        · exact absurd e (hnz y)
      · exact goalSemCM_bad (hnotF gul n' tm x y r (Or.inl nfx) hfin) (returnsC_step (Needs.le_refl _) e1 R0)
  · -- backward
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    obtain ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, K⟩ := core cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
    obtain ⟨rh, hmh, Gh⟩ := hp.semB cf hcf2 c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs agP hned2 R1 hs1 hn1
      res (by rw [← e1]; exact hres)
    cases rh with
    | one q =>
      exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e),
        goalSemCM_ret _ _ (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 Gh)⟩
    | two t' =>
      exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e),
        goalSemCM_ret _ _ (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 Gh)⟩
    | zero x =>
      by_cases fx : FitsS Lh.sure x
      · obtain ⟨st1, R2, d, w, hI1, hν1, hqd, hx2, hd2, k2, e2⟩ := Gh.1 fx
        obtain ⟨agQ, hnQ, hsQ, hnQ', J⟩ := K x R2 d w hqd fx hx2 hd2 k2
        have htr1 := frames_mono hν1 htr
        have e12 := e1.trans e2
        obtain ⟨rt, hmt, Gq⟩ := hq.semB cf hcf1 c (Need.pair ned d) σ Inv ν O gul hS hB st1 t tm (C s0 w) s hI1 htr1
          hs agQ hnQ R2 hsQ hnQ' res (by rw [← e12]; exact hres)
        have MB := (Mb hs hmh).2 x rt rfl hmt
        cases rt with
        | one q =>
          exact ⟨_, MB.1 (fun _ e => by cases e),
            goalSemCM_ret _ _ (fun _ e => by cases e) (returnsC_step hν1 e12 Gq)⟩
        | two t' =>
          exact ⟨_, MB.1 (fun _ e => by cases e),
            goalSemCM_ret _ _ (fun _ e => by cases e) (returnsC_step hν1 e12 Gq)⟩
        | zero y =>
          by_cases fy : FitsS lq y
          · obtain ⟨st2, R3, hI2, hν2, hy3, k3, e3⟩ := Gq.1 fy
            obtain ⟨Jf, Jn⟩ := J st2 R3 y hy3 k3
            by_cases fxp : FitsS lp x
            · obtain ⟨R4, hx4, hy4, k4, e4⟩ := Jf fxp
              have e14 := e12.trans (e3.trans e4)
              obtain ⟨r, hfr, A⟩ := hAB c agQ0 σ Inv ν O gul hS hB st2 R4 t tm x y hI2 (frames_mono hν2 htr1) fxp fy
                hx4 hy4 res (by rw [← e14]; exact hres)
              exact ⟨r, MB.2 y r rfl hfr, goalSemCM_step (Needs.le_trans hν1 hν2) k4 e14 _ _
                (goalSemCM_monoK (fun z hz => ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) _ _ A)⟩
            · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inl fxp)
              exact ⟨r, MB.2 y r rfl hfr, goalSemCM_bad hbr ⟨Tone.two t, st2, hI2, Needs.le_trans hν1 hν2,
                e12.trans (e3.trans (Jn fxp)), ToneRel.two (frames_mono hν2 htr1)⟩⟩
          · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inr fy)
            exact ⟨r, MB.2 y r rfl hfr, goalSemCM_bad hbr (returnsC_step hν1 e12 (Gq.2 fy))⟩
      · have R0 := Gh.2 fx
        obtain ⟨nfx, TT⟩ := hcase x fx
        obtain ⟨rt, hmt, hrt⟩ := TT.2 s gul tm hs
        have MB := (Mb hs hmh).2 x rt rfl hmt
        rcases hrt with rfl | ⟨y, rfl⟩
        · exact ⟨_, MB.1 (fun _ e => by cases e),
            goalSemCM_ret _ _ (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 R0)⟩
        · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inl nfx)
          exact ⟨r, MB.2 y r rfl hfr, goalSemCM_bad hbr (returnsC_step (Needs.le_refl _) e1 R0)⟩
  · rw [eth]; simp only [jmp0]; omega

end Comp
end SkaModel
end Formalization
