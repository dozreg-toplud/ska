import lemmas.Ska.CompLazyGoal
import lemmas.Ska.CompConsGH
import lemmas.Ska.CompCallParent

/-!
# The cons with the call in its tail

README Gaps 12.19.  The cons `[p d]` whose tail `d` calls (it is hinted) and
whose head `p` is call-free.  The run (`runLC` on a cons): `+split`, then
`+past` behind the tail parks the head's need `hed` in a bond behind a new
block `[hop o]` at the label `b` after the split (or does nothing when `hed`
asks nothing), the tail runs for `%next tel (jmp0 b)`, then the head runs for
`%next (mk bunt [] [(b, hed)]) th'` into the tail's code, then `+copy`.  At
run time the head runs first, then the call, then the bond block (the ops
the head put in front of it fill `hed` for the head's product from the
registers the head computed, `D s`, which the call keeps), then the `con`
block.

The raw blocks (`tools/hoon/lazydump.hoon`, case `%bnc`, subject
`[[4 0 1] 5]`, product `[6 6]`), which `finishLUC` meets (`#guard` below):
`0w0 mov v0 va, cel va, hed va vc, mov vc v6, tal va vb, mov vb v9, hop 8`;
`0w1 don v1`; `0w2 con v2 v3 v1, hop 1`; `0w3 mov v7 v2, hop 2` (the bond
block); `0w4 mov v4 v3, hop 3`; `0w5 nok v5 v6 v4, hop 4` (the call);
`0w7 inc v9 v7, hop 5` (the head); `0w8 mov v9 v5, hop 7` (the copy).
The case `%bnd` (`[[0 1] [2 [0 3] [0 2]]]`) is the `#guard` of
`CompCallParent.lean`: `0w3 mov v0 v2, hop 2`, the bond kept by the head and
filled by the final pass.

* `minkF_consT`, `mink_consT_bwd`, `mink_consT_crash`: `+mink` on a cell
  formula whose head is a pure part.
* `consNT_ok`: the composition (`RunOKGC` of the cons under a fork-free
  `%next`, both `sem` clauses), from the head's `RunOKL` and the tail's
  `RunOKGC`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

#guard monoOutC envR (Nomm.cons (Nomm.n4 (Nomm.n0 3)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 10, Pole.cel 10, Pole.hed 10 12, Pole.mov 12 6, Pole.tal 10 11,
      Pole.mov 11 9] (hp 8)),
    (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)), (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)), (5, bk [Pole.nok 5 6 4] (hp 4)), (6, none),
    (7, bk [Pole.inc 9 7] (hp 5)), (8, bk [Pole.mov 9 5] (hp 7)), (9, none)])

/-! ## `+mink` on a cons whose head is pure -/

/-- **`+mink` on a cell formula whose head is a cell with a pure value**: the
head's crash is the cons's, else the tail runs with one less fuel and its
tone, or the cell of the two products, is the cons's. -/
theorem minkF_consT {lib : Lib} {P : Noun → Prop} {p : Nomm} {fh ft : Noun} (hfh : ∃ a b, fh = C a b)
    (Mp : MinkEq lib P fh p) {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone} (hs : P s)
    (h : minkF lib gul n tm s (C fh ft) = some r) :
    ∃ n', n' < n ∧ ((pureEval p s = none ∧ r = Tone.two tm) ∨ ∃ x, pureEval p s = some x ∧
      ∃ rt, minkF lib gul n' tm s ft = some rt ∧
        (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ r = Tone.zero (C x y))) := by
  obtain ⟨a, b, rfl⟩ := hfh
  cases n with
  | zero => simp [minkF] at h
  | succ n' =>
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    cases eh : minkF lib gul n' tm s (C a b) with
    | none => rw [eh] at h; simp [tbind] at h
    | some rh =>
      rw [eh] at h
      refine ⟨n', Nat.lt_succ_self n', ?_⟩
      have e := (Mp s hs gul tm rh).mp ⟨n', eh⟩
      cases ep : pureEval p s with
      | none =>
        rw [ep] at e; subst e
        simp only [toneOf, tbind, Option.some.injEq] at h
        exact Or.inl ⟨rfl, h.symm⟩
      | some x =>
        rw [ep] at e; subst e
        refine Or.inr ⟨x, rfl, ?_⟩
        simp only [toneOf, tbind] at h
        cases et : minkF lib gul n' tm s ft with
        | none => rw [et] at h; simp at h
        | some rt =>
          rw [et] at h
          refine ⟨rt, rfl, ?_⟩
          cases rt with
          | zero y =>
            simp only [Option.some.injEq] at h
            exact Or.inr ⟨y, rfl, h.symm⟩
          | one q =>
            simp only [Option.some.injEq] at h
            exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
          | two t' =>
            simp only [Option.some.injEq] at h
            exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩

/-- **`+mink` on a cell formula whose head is a cell with a pure value,
backward**: from the head's value `x` and a run of the tail to `rt`, a run of
the cons, with the case split of `minkF_consT`. -/
theorem mink_consT_bwd {lib : Lib} {fh ft : Noun} (hfh : ∃ a b, fh = C a b) {s gul : Noun} {tm : Trace}
    {x : Noun} {rt : Tone} (hh : Mink lib gul tm s fh (Tone.zero x)) (ht : Mink lib gul tm s ft rt) :
    ∃ r, Mink lib gul tm s (C fh ft) r ∧
      (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ r = Tone.zero (C x y)) := by
  obtain ⟨a, b, rfl⟩ := hfh
  obtain ⟨n1, e1⟩ := hh
  obtain ⟨n2, e2⟩ := ht
  have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s (C a b) _ e1
  have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s ft _ e2
  cases rt with
  | zero y =>
    refine ⟨Tone.zero (C x y), ⟨max n1 n2 + 1, ?_⟩, Or.inr ⟨y, rfl, rfl⟩⟩
    rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']; rfl
  | one q =>
    refine ⟨Tone.one q, ⟨max n1 n2 + 1, ?_⟩, Or.inl ⟨(fun _ e => by cases e), rfl⟩⟩
    rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']; rfl
  | two t' =>
    refine ⟨Tone.two t', ⟨max n1 n2 + 1, ?_⟩, Or.inl ⟨(fun _ e => by cases e), rfl⟩⟩
    rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']; rfl

/-- `+mink` on a cell formula whose head is a cell crashes where the head's
pure value is none. -/
theorem mink_consT_crash {lib : Lib} {P : Noun → Prop} {p : Nomm} {fh ft : Noun} (hfh : ∃ a b, fh = C a b)
    (Mp : MinkEq lib P fh p) {s gul : Noun} {tm : Trace} (hs : P s) (e : pureEval p s = none) :
    Mink lib gul tm s (C fh ft) (Tone.two tm) :=
  mink_consC_crash hfh ((Mp s hs gul tm _).mpr (by rw [e]; rfl))

/-! ## The composition -/

/-- **The cons whose tail calls, under a fork-free `%next sur th`**: from
`+split` (`hpre`, `hblk`, the halves `lp`, `lq`), the gen `gb` after `+past`
behind the tail (`hjt`: no block, the tail running into the `con` block `o`
and the head's goal without entries, or the bond block `[hop o]` at `g'.bo`
and the head's goal `Lh` with the one entry `(g'.bo, lp)`), the tail's
`RunOKGC` for `%next lq jt`, the head's `RunOKL` under `Lh` into the tail's
code with `D`, `W`, and `+copy`: `RunOKGC` of the cons.  At run time the copy
block, the head's code (`GoalSemD`: `D s` holds `W s`), the tail's code with
the input need `pair ned (D s)` (so the call keeps `D s`), the bond block
(the head's front: its ops fill `lp` for the head's product from `pair ned
(D s)`), the `con` block.  Both `sem` clauses share `core`: the forward one
takes the tail's tone from `minkF_consT`, the backward one from the tail's
`semB` and builds the cons's `+mink` run by `mink_consT_bwd`. -/
theorem consNT_ok {lib : Lib} {P : Noun → Prop} {fh ft : Noun} {p : Nomm} {sur : Sure S} {th : Jmp}
    {g0 g' gb g1 g2 g3 : Gen Map} {lp lq : Sure S} {o : Nat} {jt : Jmp} {Lh : Lazy S}
    {D : Noun → Need} {W : Noun → Noun} {nexq nexp nex : NextL S}
    (hfh : ∃ a b, fh = C a b) (Mp : MinkEq lib P fh p)
    (hg : GoalOK g0 (CGoal.next sur th)) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hcb : CondBelow g0)
    (hlp : ∀ r, NMem lp.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hgb : Ext g' gb) (hgbU : GrowU g' gb) (hgbc : gb.cond = g'.cond) (hgbre : gb.re = g'.re)
    (hLs : Lh.sure.ned = Need.none) (hLf : ∀ v, FitsS Lh.sure v)
    (hjt : (jt = jmp0 o ∧ entries Lh = [] ∧ (∀ x, FitsS lp x) ∧ lp.ned = Need.none) ∨
      (jt = jmp0 g'.bo ∧ entries Lh = [(g'.bo, ofSure lp)] ∧ g'.bo < gb.bo ∧
        HoonMap.get gb.blocks g'.bo = some ⟨[], [], Termin.hop (jmp0 o)⟩))
    (hq : RunOKGC lib P ft (CGoal.next lq jt) gb g1 nexq)
    (hp : RunOKL (Map := Map) lib p Lh nexq.th D W g1 g2 nexp)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3))
    (hu : UpBelow g0) (d0 : g0.drop = false)
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → ¬ FitsS sur (C x y))
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y →
          GoalSem lib O c gul st (Keep g0 g' (CGoal.next sur th)) regs t (jmp0 o) (CGoal.next sur th)
            (some (C x y))) :
    RunOKGC lib P (C fh ft) (CGoal.next sur th) g0 g3 nex := by
  -- the labels of the head's goal
  have labLh : ∀ e ∈ entries Lh, e = (g'.bo, ofSure lp) ∧ g'.bo < gb.bo := fun e he => by
    rcases hjt with ⟨_, h, _⟩ | ⟨_, h, h', _⟩
    · rw [h] at he; cases he
    · rw [h] at he; simp only [List.mem_singleton] at he; exact ⟨he, h'⟩
  have labLh' : ∀ k, k ∈ (entries Lh).map Prod.fst → k = g'.bo ∧ g'.bo < gb.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨rfl, h⟩ := labLh e he
    exact ⟨rfl, h⟩
  have jta : jt.args = [] := by rcases hjt with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have nLs : ∀ r, ¬ NMem Lh.sure.ned r := fun r hr => by rw [hLs] at hr; exact hr
  have b0' := hpre.2.1
  have bgb := hgb.2.1
  have b1 := hq.ext.2.1
  have b2 := hp.bo
  have r0' := hpre.1
  have rgb := hgb.1
  have r1 := hq.ext.1
  have r2 := hp.re
  -- the blocks below `gb.bo` but the bond's, kept by the head
  have k21 : ∀ k, k < g1.bo → k ∉ (entries Lh).map Prod.fst → HoonMap.get g2.blocks k = HoonMap.get g1.blocks k :=
    fun k hk hn => hp.keep k hk hn
  -- the labels of the two runs are apart
  have lq' : ∀ e ∈ entries nexq.laz, gb.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(hq.labs e he).1, Nat.lt_trans (hq.labs e he).2.1 hq.hi⟩
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
  have mp : ∀ r, NMem nexp.laz.sure.ned r → g1.re ≤ r ∧ r < g2.re := fun r hr => by
    rcases hp.regs r hr with h | h
    · exact absurd h (nLs r)
    · exact h
  have mq : ∀ r, NMem nexq.laz.sure.ned r → NMem lq.ned r ∨ (gb.re ≤ r ∧ r < g1.re) := hq.regs
  have l3 := EC.1
  have lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases mq r hr with a | ⟨_, a⟩
    · have := lql r a; omega
    · exact a
  have P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · have := mp r h1
      rcases mq r h2 with b | ⟨b, b'⟩
      · have := lql r b; omega
      · omega
    · rcases hr with h | h
      · exact (mp r h).2
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
    (keeps_copy (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨fun r hr => (mp r hr).2, jmpIn_nil thp⟩
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
  -- the blocks of `g3` below `g1.bo` but the bond's are `g1`'s, below `g'.bo` they are `g'`'s
  have mid3 : ∀ k, k < g1.bo → k ∉ (entries Lh).map Prod.fst →
      HoonMap.get g3.blocks k = HoonMap.get g1.blocks k := fun k hk hn => by
    rw [hp3.2.2.2 k (by omega), k21 k hk hn]
  have low3 : ∀ k, k < g'.bo → HoonMap.get g3.blocks k = HoonMap.get g'.blocks k := fun k hk => by
    rw [mid3 k (by omega) (fun hm => by have := labLh' k hm; omega), hq.ext.2.2.2 k (by omega),
      hgb.2.2.2 k hk]
  -- the entries
  have memN : ∀ e, e ∈ entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork) (nexp.laz.bond ++ nexq.laz.bond)) ↔
      e ∈ entries nexp.laz ∨ e ∈ entries nexq.laz := fun e => by
    rw [(entries_side_perm _ _ _).mem_iff, List.mem_append]
  have labN : ∀ k, k ∈ (entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork)
      (nexp.laz.bond ++ nexq.laz.bond))).map Prod.fst → g'.bo ≤ k ∧ k < g2.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    rcases (memN e).mp he with a | a
    · have := lp' e a; omega
    · have := lq' e a; omega
  have ent0 : ∀ e0 ∈ entries Lh, e0.2.sure = lp := fun e0 he0 => by
    obtain ⟨rfl, _⟩ := labLh e0 he0; rfl
  -- the shared part of the two `sem` clauses
  have core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun), Forall2 (FrameRel lib (ν st)) t tm →
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g3
        (mk n.laz (nexp.laz.fork ++ nexq.laz.fork) (nexp.laz.bond ++ nexq.laz.bond)) s0 s) →
      (∀ x, NMem ned x → g3.re ≤ x) →
      ∀ regs, HoldsS n.laz regs s → HoldsN ned regs s0 →
      (pureEval p s = none → goJ lib O c gul st regs t n.th = some (Tone.two t, st)) ∧
      ∀ x, pureEval p s = some x → ∃ R2,
        (∀ st' : σ, AgreeU lib O c gul st' t cf (Need.pair ned (D s)) gb g1 nexq.laz (C s0 (W s)) s) ∧
        (∀ y, NMem (Need.pair ned (D s)) y → g1.re ≤ y) ∧
        HoldsS nexq.laz.sure R2 s ∧ HoldsN (Need.pair ned (D s)) R2 (C s0 (W s)) ∧
        goJ lib O c gul st regs t n.th = goJ lib O c gul st R2 t nexq.th ∧
        ∀ rt r, (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ r = Tone.zero (C x y)) →
          GoalSemCM lib O c gul Inv ν (fun z => (z < gb.re ∨ NMem (Need.pair ned (D s)) z) ∧
            ¬ GMem (CGoal.next lq jt) z) st R2 t tm nexq.th (CGoal.next lq jt) rt →
          GoalSemCM lib O c gul Inv ν (fun z => (z < g0.re ∨ NMem ned z) ∧ ¬ GMem (CGoal.next sur th) z)
            st regs t tm n.th (CGoal.next sur th) r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hh hn
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
      have := (mp r hm).2; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : AgreeL lib O c gul st t cf ned g1 g2 nexp.laz s0 s :=
      ((ag st).part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)).toL
    have Hp := hp.sem cf hcf2 c ned σ O st t gul s0 s agP hned2 R1 hs1 hn1
    -- the keys
    have agQ0 : Agree c g0 g' := fun k h0 h1 => by
      rw [(ag st).1 k h0 (by omega) (fun hm => by have := labN k hm; omega), low3 k h1]
      exact hfix cf hcf0 k h0 h1
    refine ⟨fun e => ?_, fun x ex => ?_⟩
    · rw [e] at Hp; exact e1.trans Hp
    rw [ex] at Hp
    obtain ⟨R2, -, hD2, k2, e2⟩ := Hp.1 (hLf x)
    have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, nLs r⟩) hn1
    have hdD : ∀ r, NMem (D s) r → g1.re ≤ r ∧ r < g2.re := hp.dreg s
    refine ⟨R2, fun st' => ⟨fun k h0 h1 hnk => ?_, fun e he => ?_⟩, fun y hy => ?_,
      ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), nLs r⟩) hs1'.1, hs1'.2⟩, ⟨hn2, hD2⟩, e1.trans e2,
      fun rt r rel GQ => ?_⟩
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
      exact (f3.pair (D s) (fun r hr => by have := hdD r hr; omega) (W s)).mono (by omega)
    · rcases hy with h | h
      · have := hned y h; omega
      · exact (hdD y h).1
    -- after the tail
    rcases rel with ⟨hnz, rfl⟩ | ⟨y, rfl, rfl⟩
    · exact goalSemCM_ret _ _ hnz (returnsC_step (Needs.le_refl _) (e1.trans e2) (returnsC_of_goalSemCM _ _ hnz GQ))
    by_cases fy : FitsS lq y
    case neg =>
      exact ⟨fun hf => absurd hf (hnot x y (Or.inr fy)), fun _ => returnsC_step (Needs.le_refl _) (e1.trans e2)
        (GQ.2 fy)⟩
    obtain ⟨st', R3, hI', hν, hl3, k3, e3⟩ := GQ.1 fy
    have htr' := frames_mono hν htr
    have nlq : ∀ r, NMem (Need.pair ned (D s)) r → ¬ NMem lq.ned r := fun r hr hm => by
      have := lql r hm
      rcases hr with h | h
      · have := hned r h; omega
      · have := (hdD r h).1; omega
    have hn3 : HoldsN (Need.pair ned (D s)) R3 (C s0 (W s)) :=
      HoldsN.agree _ (fun r hr => k3 r ⟨Or.inr hr, nlq r hr⟩) ⟨hn2, hD2⟩
    -- the kept registers
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
    have keep3 : ∀ z, (z < g0.re ∨ NMem ned z) ∧ ¬ GMem (CGoal.next sur th) z →
        SkaModel.read z R3 = SkaModel.read z regs := fun z ⟨k1, k2'⟩ => by
      rw [k3 z ⟨k1.imp (fun h => by omega) (fun h => Or.inl h), nlqK z k1 k2'⟩,
        k2 z ⟨k1.imp (fun h => by omega) id, nLs z⟩]
      refine u1 z (fun hm => ?_) (fun hm => ?_)
      · have := mp z hm
        rcases k1 with k1 | k1
        · omega
        · have := hned z k1; omega
      · rcases mq z hm with a | ⟨a, a'⟩
        · exact nlqK z k1 k2' a
        · rcases k1 with k1 | k1
          · omega
          · have := hned z k1; omega
    -- the code at the tail's jump
    have J : GoalSem lib O c gul st' (fun z => (z < g0.re ∨ NMem ned z) ∧ ¬ GMem (CGoal.next sur th) z) R3 t jt
        (CGoal.next sur th) (some (C x y)) := by
      rcases hjt with ⟨rfl, hLe, hfp, hln⟩ | ⟨rfl, hLe, hlt, hbb⟩
      · -- no block of `+past`: the `con` block
        have B := hblk c agQ0 σ O st' R3 t gul x y (hfp x) fy (by rw [hln]; trivial) hl3
        exact GoalSem.mono (fun r ⟨k1, k2'⟩ => ⟨k1.imp id (fun h => by have := hned r h; omega), k2'⟩) B
      · -- the bond block: the head's front fills `lp`
        have hmem : (g'.bo, ofSure lp) ∈ entries Lh := by rw [hLe]; exact List.mem_singleton.mpr rfl
        obtain ⟨F, hF, SF⟩ := hp.front _ hmem
        have hb1 : HoonMap.get g1.blocks g'.bo = some ⟨[], [], Termin.hop (jmp0 o)⟩ := by
          rw [hq.ext.2.2.2 _ hlt]; exact hbb
        have hb2 := hF [] (Termin.hop (jmp0 o)) hb1
        rw [List.append_nil] at hb2
        have hb3 : HoonMap.get g3.blocks g'.bo = some ⟨[], F, Termin.hop (jmp0 o)⟩ := by
          rw [hp3.2.2.2 _ (by omega)]; exact hb2
        obtain ⟨Af, hcb', FS⟩ : ∃ Af, HoonMap.get c.blocks g'.bo = some ⟨[], Af, Termin.hop (jmp0 o)⟩ ∧
            FillSem lib O c gul st' t (Need.pair ned (D s)) g1.re lp Af (C s0 (W s)) x := by
          rcases SF cf hcf2 with ⟨L', hL', FP⟩ | ⟨hn2', FP⟩
          · obtain ⟨A0, th'', hb3', hc3, hf3⟩ := (ag st').2 (g'.bo, L') ((memN _).mpr (Or.inl hL'))
            rw [hb3] at hb3'
            simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3'
            obtain ⟨rfl, rfl⟩ := hb3'
            refine ⟨A0, by rw [hc3, renJmp_nil _ (show (jmp0 o).args = [] from rfl)], ?_⟩
            have := FP lib σ O c gul st' t ned A0 s0 s x hned2 ex (hf3.mono (by omega))
            rw [List.map_nil, List.append_nil] at this
            exact this
          · refine ⟨[] ++ F.map (renPole (unproxy cf)), ?_, FP lib σ O c gul st' t ned [] s0 s x hned2 ex
              fillSem_bunt_nil⟩
            rw [(ag st').1 g'.bo (by omega) (by omega) (fun hm => by
              obtain ⟨e, he, e1'⟩ := List.mem_map.mp hm
              rcases (memN e).mp he with a | a
              · exact hn2' (List.mem_map.mpr ⟨e, a, e1'⟩)
              · have := lq' e a; omega), hb3]
            simp only [Option.map_some, unproxyBlob, renBlob, renFin, List.nil_append, List.map_nil,
              renJmp_nil _ (show (jmp0 o).args = [] from rfl)]
        obtain ⟨F1, F2⟩ := FS R3 hn3
        by_cases fx : FitsS lp x
        · obtain ⟨R4, r4, hl4, k4⟩ := F1 fx
          have e4 : goJ lib O c gul st' R3 t (jmp0 g'.bo) = goJ lib O c gul st' R4 t (jmp0 o) := by
            have := r4 [] (Termin.hop (jmp0 o))
            simp only [List.append_nil] at this
            rw [goJ_jmp0 _ _ _ _ hcb', this, execBlob_hop]
          have hy4 : HoldsN lq.ned R4 y :=
            HoldsN.agree _ (fun r hr => k4 r (Or.inr (by have := lql r hr; omega)) (fun hm => hpq r hm hr)) hl3
          have B := hblk c agQ0 σ O st' R4 t gul x y fx fy hl4.1 hy4
          refine GoalSem.transfer e4 (fun z hz => ?_)
            (GoalSem.mono (fun r ⟨k1, k2'⟩ => ⟨k1.imp id (fun h => by have := hned r h; omega), k2'⟩) B)
          obtain ⟨k1, k2'⟩ := hz
          exact k4 z (k1.elim (fun h => Or.inr (by omega)) (fun h => Or.inl (Or.inl h))) (nlpK z k1 k2')
        · have := F2 fx [] (Termin.hop (jmp0 o))
          simp only [List.append_nil] at this
          exact ⟨fun hf => absurd hf (hnot x y (Or.inl fx)), fun _ => by rw [goJ_jmp0 _ _ _ _ hcb', this]⟩
    exact goalSemCM_step hν keep3 (e1.trans (e2.trans e3)) _ _ (goalSemC_of_goalSem hI' htr' _ _ J)
  refine {
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
    semB := fun cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres => ?_ }
  · rcases CM r hr with h | h | ⟨h, h'⟩
    · have := mp r h; exact Or.inr ⟨by omega, by omega⟩
    · rcases mq r h with a | ⟨a, a'⟩
      · rcases hlq r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h'⟩
  · rcases (memN e).mp he with a | a
    · refine ⟨(hp.eregs e a).1, fun r hr => ⟨?_, ?_⟩⟩
      · rcases (hp.eregs e a).2 r hr with ⟨e0, he0, h0⟩ | b
        · rw [ent0 e0 he0] at h0
          rcases hlp r h0 with b' | ⟨b', _⟩
          · exact Or.inl b'
          · exact Or.inr b'
        · exact Or.inr (by omega)
      · rcases (hp.eregs e a).2 r hr with ⟨e0, he0, h0⟩ | b
        · rw [ent0 e0 he0] at h0; have := lpl r h0; omega
        · omega
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
    have step : ∀ {tm : Trace} {r : Tone}, (∀ x, pureEval p s = some x → ∀ rt,
        BadC (CGoal.next lq jt) tm rt →
        (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ r = Tone.zero (C x y)) →
        BadC (CGoal.next sur th) tm r) := fun x _ rt hb hr => by
      rcases hr with ⟨hn, rfl⟩ | ⟨y, rfl, rfl⟩
      · rcases hb with e | ⟨q, e, _⟩
        · exact Or.inl e
        · exact absurd e (hn q)
      · rcases hb with e | ⟨q, e, hq'⟩
        · cases e
        · cases e
          exact Or.inr ⟨_, rfl, hnot x _ (Or.inr hq')⟩
    by_cases a : FitsS nexp.laz.sure s
    · have b : ¬ FitsS nexq.laz.sure s := fun b => hf ((CF s).mpr ⟨a, b⟩)
      have NQ := hq.nec s hs b
      refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
      · obtain ⟨n', _, h | ⟨x, ex, rt, hmt, hr⟩⟩ := minkF_consT hfh Mp hs hm
        · rw [h.2]; exact Or.inl rfl
        · exact step x ex rt (NQ.1 gul n' tm rt hmt) hr
      · cases ex : pureEval p s with
        | none => exact ⟨_, mink_consT_crash hfh Mp hs ex, Or.inl rfl⟩
        | some x =>
          obtain ⟨rt, hmt, hb⟩ := NQ.2 gul tm
          obtain ⟨r, hmr, hr⟩ := mink_consT_bwd hfh ((Mp s hs gul tm _).mpr (by rw [ex]; rfl)) hmt
          exact ⟨r, hmr, step x ex rt hb hr⟩
    · have ex : pureEval p s = none := by
        rcases hp.nec s a with e | ⟨v, _, nf⟩
        · exact e
        · exact absurd (hLf v) nf
      refine ⟨fun gul n tm r hm => ?_, fun gul tm => ⟨_, mink_consT_crash hfh Mp hs ex, Or.inl rfl⟩⟩
      obtain ⟨n', _, h | ⟨x, ex', _⟩⟩ := minkF_consT hfh Mp hs hm
      · rw [h.2]; exact Or.inl rfl
      · rw [ex] at ex'; cases ex'
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
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3, hp.cfr.get_lt hk])
    have K := core cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hh hn
    obtain ⟨n', hn', h | ⟨x, ex, rt, hmt, hr⟩⟩ := minkF_consT hfh Mp hs hm
    · rw [h.2]; exact ⟨Tone.two t, st, hI, Needs.le_refl _, K.1 h.1, ToneRel.two htr⟩
    obtain ⟨R2, agQ, hnQ, hq2, hn2, e2, fin⟩ := K.2 x ex
    exact fin rt r hr (hq.sem cf hcf1 c (Need.pair ned (D s)) σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn'))
      st t tm (C s0 (W s)) s rt hI htr hs hmt agQ hnQ R2 hq2 hn2)
  · -- backward
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3, hp.cfr.get_lt hk])
    have K := core cf hcf c ned σ Inv ν O gul st t tm s0 s htr ag hned regs hh hn
    cases ex : pureEval p s with
    | none =>
      exact ⟨_, mink_consT_crash hfh Mp hs ex, ⟨Tone.two t, st, hI, Needs.le_refl _, K.1 ex, ToneRel.two htr⟩⟩
    | some x =>
      obtain ⟨R2, agQ, hnQ, hq2, hn2, e2, fin⟩ := K.2 x ex
      obtain ⟨rt, hmt, GQ⟩ := hq.semB cf hcf1 c (Need.pair ned (D s)) σ Inv ν O gul hS hB st t tm (C s0 (W s)) s
        hI htr hs agQ hnQ R2 hq2 hn2 res (by rw [← e2]; exact hres)
      obtain ⟨r, hmr, hr⟩ := mink_consT_bwd hfh ((Mp s hs gul tm _).mpr (by rw [ex]; rfl)) hmt
      exact ⟨r, hmr, fin rt r hr GQ⟩

/-! ## What the cons asks of its parts -/

/-- **What the cons whose tail calls asks of its head**: every run of the
head under the goal that `+past` makes behind the call (`mk bunt [] [(b,
hed)]`, the bond block `b` a `[hop jb]`), from a state with the hypotheses
of `OKNV` and the entry's registers allocated and no keys of `cond`, returns
a clean sure need and meets `RunOKL` for some `D` and `W`. -/
def BondOK (lib : Lib) (nm : Nomm) : Prop :=
  ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {hed : Sure S} {b : Nat} {th jb : Jmp},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → b ≠ th.there → b < g0.bo →
    HoonMap.get g0.blocks b = some ⟨[], [], Termin.hop jb⟩ → Distinct hed.ned →
    (∀ x, NMem hed.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    runL nm (CGoalL.next (mk Sure.bunt [] [(b, ofSure hed)]) th) region g0 = some (nex, g1) →
    Clean nex.laz.sure.ned ∧
      ∃ D W, RunOKL (Map := Map) lib nm (mk Sure.bunt [] [(b, ofSure hed)]) th D W g0 g1 nex

/-- **What the cons whose tail calls asks of its tail**: the code of every
run under a fork-free `%next` begins at a block the run made, so the head's
goal jumps elsewhere than the bond block of `+past`. -/
def EntNew (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    (∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none) →
    runLC env sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) → g0.bo ≤ nex.th.there

theorem entries_bond1 (b : Nat) (hed : Sure S) :
    entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]) = [(b, ofSure hed)] := by
  simp [entries, bondEntries, forkEntries, entries_ofSure]

/-! ## Heads -/

theorem runL_n01_next (laz : Lazy S) (th : Jmp) (region : List Nat) (g : Gen Map) :
    (runL (Nomm.n0 1) (CGoalL.next laz th) region g : Option (NextL S × Gen Map)) = some (⟨laz, th⟩, g) := by
  unfold runL
  simp only [show (1 : Nat) ≠ 0 by omega, if_false, if_true, simpleNextL, bind_apply, pure_apply,
    Option.bind_some]

/-- **`[0 1]` under `%next L th`**: the goal itself, every entry kept with
its need, `D = none`. -/
theorem runOKL_n01 (lib : Lib) {L : Lazy S} {th : Jmp} {g : Gen Map}
    (h1 : 1 ≤ th.there) (h2 : th.there < g.bo) (hd : Distinct L.sure.ned)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned) (hnd : ((entries L).map Prod.fst).Nodup)
    (hemp : ∀ e ∈ entries L, ∃ th', HoonMap.get g.blocks e.1 = some ⟨[], [], Termin.hop th'⟩)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g.cond r = Option.none) (W : Noun → Noun) :
    RunOKL (Map := Map) lib (Nomm.n0 1) L th (fun _ => Need.none) W g g ⟨L, th⟩ := by
  have ev : ∀ s, pureEval (Nomm.n0 1) s = some s := fun s => by simp [pureEval, slot?_one]
  refine ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ _ => rfl, GrowU.refl g, CondFresh.refl g, h1, h2, Or.inr rfl,
    fun r hr => Or.inl hr, hd, fun e he => ⟨hed e he, fun r hr => Or.inl ⟨e, he, hr⟩⟩,
    fun e he => ⟨Or.inl (List.mem_map_of_mem he), hemp e he⟩, hnd, by simp [sixCount],
    fun _ _ hr => hr.elim, fun s hs => Or.inr ⟨s, ev s, hs⟩, hnc, hec, fun e he => ?_, ?_⟩
  · refine ⟨[], fun B fin hb => by simpa using hb, fun cf _ => Or.inl ⟨e.2, he, ?_⟩⟩
    intro lib σ O c gul st t ned A s0 s v _ hev hfill
    rw [ev s] at hev
    cases hev
    simp only [List.map_nil, List.append_nil]
    exact hfill.pair Need.none (fun _ h => h.elim) (W s)
  · intro cf _ c ned σ O st t gul s0 s _ _ regs hh _
    show GoalSemD lib O c gul st _ regs t th L.sure th Need.none (W s) (pureEval (Nomm.n0 1) s)
    rw [ev s]
    exact ⟨fun _ => ⟨regs, hh.1, trivial, fun _ _ => rfl, rfl⟩, fun nf => absurd (fitsS_of_holdsS hh) nf⟩

/-- **`[0 axe]` with `1 ≤ axe` meets `BondOK`** (`runOKL_n01`, `runOKL_n0_run`). -/
theorem bondOK_n0 (lib : Lib) {axe : Nat} (ha : 1 ≤ axe) : BondOK (S := S) (Map := Map) lib (Nomm.n0 axe) := by
  intro region g0 g1 nex hed b th jb _ b0 d0 hu hcl hcb h1 h2 hne hb hbb hdh hen h
  have E := entries_bond1 b hed
  have hed' : ∀ e ∈ entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]), Distinct e.2.sure.ned := by
    rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact hdh
  have hnd : ((entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)])).map Prod.fst).Nodup := by
    rw [E]; simp
  have hemp : ∀ e ∈ entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]),
      ∃ th', HoonMap.get g0.blocks e.1 = some ⟨[], [], Termin.hop th'⟩ := by
    rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨jb, hbb⟩
  have hec : ∀ e ∈ entries (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]), ∀ r, NMem e.2.sure.ned r →
      HoonMap.get g0.cond r = Option.none := by
    rw [E]; intro e he r hr; simp only [List.mem_singleton] at he; subst he; exact (hen r hr).2
  rcases Nat.lt_or_ge axe 2 with lt | ge
  · obtain rfl : axe = 1 := by omega
    rw [runL_n01_next] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, _, _, runOKL_n01 (L := mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]) lib h1 h2 trivial hed' hnd
      hemp (fun r hr => hr.elim) hec (fun _ => A 0)⟩
  · have R := runOKL_n0_run (Map := Map) lib ge h h1 h2 trivial hed' hnd hemp (fun r hr => hr.elim) hec (fun _ => A 0)
    refine ⟨?_, _, _, R⟩
    rw [runL_n0_next ge] at h
    cases hf : fromL axe (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]) with
    | none => rw [hf] at h; cases h
    | some L' =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs := fromL_sure hf
      simp only [fromSure, show axe ≠ 0 by omega, show axe ≠ 1 by omega, if_false] at hs
      have hn : (mk (Sure.bunt : Sure S) [] [(b, ofSure hed)]).sure.ned = Need.none := rfl
      rw [if_pos hn] at hs
      simp only [Option.some.injEq] at hs
      show Clean L'.sure.ned
      rw [← hs]; trivial

/-- **`[4 p]` with `p` in `FragX` meets `BondOK`** (`runOKL_n4_none`, `clean_n4L`). -/
theorem bondOK_n4 (lib : Lib) {p : Nomm} (hp : FragX (S := S) p) : BondOK (S := S) (Map := Map) lib (Nomm.n4 p) := by
  intro region g0 g1 nex hed b th jb hcount b0 d0 hu hcl hcb h1 h2 hne hb hbb hdh hen h
  have E := entries_bond1 b hed
  refine ⟨clean_n4L (runX_clean hp) h, ?_⟩
  obtain ⟨d, R⟩ := runOKL_n4_none lib (runX_ok lib hp).2.1 (runX_semR lib hp).2.1 (runX_keeps hp)
    (aboveX_of_fragX hp) h hcount b0 d0 hu hcl h1 h2 rfl hcb
    (by rw [E]; simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]; exact fun e => hne e.symm)
    (by rw [E]; intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hb, [], _, hbb⟩)
    (by rw [E]; intro e he x hx; simp only [List.mem_singleton] at he; subst he; exact hen x hx)
  exact ⟨_, _, R⟩

/-! ## Tails -/

/-- **The indirect call with call-free parts meets `EntNew`**: its code
begins at the block of `+copy`, emitted after the `%nok` block and the two
runs (`indirect_prefixN`, the parts' `RunOKNV`, `copy_ok`). -/
theorem entNew_indirect (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) (env : CallEnv) :
    EntNew (S := S) (Map := Map) env (Nomm.n2 p q Option.none) := by
  intro sup sur th region g0 g' nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have hc : sixCount p + sixCount q ≤ 255 := hcount
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have h1 : simpleNextL (CGoalL.next (ofSure sur) th) g0 = some (⟨ofSure sur, th⟩, g0) := rfl
  obtain ⟨-, -, rfl, rfl, rfl, l2, r3, b3, d3, cn3, k3o, k3out, k3lo, hk2, G3, u3, cb3⟩ :=
    indirect_prefixN h1 h2 h3 d0 hu hcb b0 hj
  rw [runLC_eq env q (Nomm.noCall_of_pure q uq.pure)] at h4
  rw [pastL_pure _ _ up.pure, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  rw [runLC_eq env p (Nomm.noCall_of_pure p up.pure)] at h6
  have nk : ∀ x, g0.re ≤ x → HoonMap.get g3.cond x = Option.none := fun x hx => by
    rw [cn3]; exact condBelow_none hcb hx
  have Rq := uq.next (sur := lazyReg (g2.re + 1)) (th := jmp0 (g0.bo + 1)) ⟨by simp only [jmp0]; omega,
      by simp only [jmp0]; omega⟩ rfl
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; omega⟩ trivial (by omega) (by omega) d3 u3
    (hcl0.growU G3) cb3 (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact nk _ (by omega)) h4
  have Rp := up.next (sur := lazyReg g2.re) (th := nexF.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; have := Rq.ext.1; omega⟩ trivial
    (by omega) (by have := Rq.lo; have := Rq.hi; omega) (Rq.ext.2.2.1.trans d3) (Rq.grow.up u3)
    ((hcl0.growU G3).growU Rq.grow) (Rq.cfr.below cb3)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      rw [Rq.cfr.get_lt (by omega)]; exact nk _ (by omega)) h6
  have lq' : ∀ e ∈ entries nexF.laz, g3.bo ≤ e.1 ∧ e.1 < g4.bo := fun e he =>
    ⟨(Rq.labs e he).1, Nat.lt_trans (Rq.labs e he).2.1 Rq.hi⟩
  have lp' : ∀ e ∈ entries nexS.laz, g4.bo ≤ e.1 ∧ e.1 < g6.bo := fun e he =>
    ⟨(Rp.labs e he).1, Nat.lt_trans (Rp.labs e he).2.1 Rp.hi⟩
  have apF : ∀ e ∈ nexS.laz.fork, ∀ e' ∈ nexF.laz.fork, e.1.1 ≠ e'.1.1 := fun e he e' he' => by
    have a := lp' e.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he))
    have b := lq' e'.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he'))
    omega
  have apB : ∀ e ∈ nexS.laz.bond, ∀ e' ∈ nexF.laz.bond, e.1 ≠ e'.1 := fun e he e' he' => by
    have a := lp' e (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he))
    have b := lq' e' (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he'))
    omega
  obtain ⟨n, hcp, rfl⟩ := copyL_apart_some apF apB h7
  obtain ⟨_, eth, _⟩ := copy_ok hcp
  show g0.bo ≤ n.th.there
  rw [eth]
  simp only [jmp0]
  have := Rq.ext.2.1
  have := Rp.ext.2.1
  omega

/-! ## The cons from its run -/

/-- **The cons `[p d]` whose tail calls, under a fork-free `%next sur th`,
meets `RunOKGC`**, for a call-free head `p` with `UOK`, `+mink` on `fh` its
value and `BondOK`, and a hinted tail `d` with `UOKC` and `EntNew`, for the
formula `[fh ft]` with `fh` a cell, from any state with the hypotheses of
`OKNV`.  The run: `+split`, `+past` behind the tail (`pastL_hinted`: nothing
when the head's need asks nothing, the head then runs under a goal without
entries by `UOK.next`; else the bond block, and the head runs under the bond
goal by `BondOK`), the tail (`UOKC.run`), `+past` behind the head (nothing,
`pastL_pure`), the head, `+copy`; `consNT_ok` composes. -/
theorem consT_runN (lib : Lib) {p d : Nomm} {env : CallEnv} {P : Noun → Prop} {fh ft : Noun}
    (up : UOK (S := S) (Map := Map) lib p) (Mp : MinkEq lib P fh p) (Bp : BondOK (S := S) (Map := Map) lib p)
    (hfh : ∃ x y, fh = C x y) (Ud : UOKC (S := S) (Map := Map) lib env P ft d) (hd : hinted env.cod d = some true)
    (Ed : EntNew (S := S) (Map := Map) env d)
    (hcount : sixCount p + sixCount d ≤ 255) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.cons p d) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKGC lib P (C fh ft) (CGoal.next sur th) g0 g1 nex := by
  have e : (runLC env sup (Nomm.cons p d) (CGoalL.next (ofSure sur) th) region :
      CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ d region
        let nex2 ← runLC env sup d (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at h
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ up.pure, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  rw [runLC_eq env p (Nomm.noCall_of_pure p up.pure)] at h4
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok hs2
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hok.1 hok.2
  obtain ⟨G2, eo', lt2, _⟩ := split_down hs2 hj.1 hj.2 d0
  simp only at eo'
  subst eo
  have CS := clean_split hs2 hcl
  simp only at CS
  have c2 : g2.cond = g0.cond := (kc_split _).keep _ _ _ hs2
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (G2.toU hu).up hu
  have lt2' : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y a) E2.1
    · exact a
  have G2U : GrowU g0 g2 := G2.toU hu
  have cl2 : Clear g2 := hcl0.growU G2U
  have cf2 : CondFresh g0 g2 := condFresh_of_eq E2.1 c2
  have cb2 : CondBelow g2 := cf2.below hcb
  have nk2 : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → HoonMap.get g2.cond y = Option.none := fun n M y hy => by
    rw [c2]
    rcases M y hy with a | ⟨a, _⟩
    · exact hkg y a
    · exact condBelow_none hcb a
  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g2 :=
    (keepsA_split (P := fun r => HoonMap.get g0.cond r = Option.none) d0 hkg (jmpIn_nil hth)
      (fun r hr => condBelow_none hcb hr) hs2).1.ab _ (aboveIn_start _ g0)
  have BS : BelowIn g0.bo g2 :=
    (keeps_split d0 (fun r hr => hok.2 r hr) (jmpIn_nil hth) hs2).1.bel _ (belowIn_start g0)
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g2.bo → (HoonMap.get g2.blocks k).map (unproxyBlob cf) = HoonMap.get g2.blocks k := by
    intro cf hcf k h0 h1
    have u0 : ∀ x, x < g2.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
    have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
    cases hg : HoonMap.get g2.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1 hg), renBlob_congr u1 (AS k b h0 h1 hg), renBlob_id]
  have hblk : ∀ (c : Straight Map), Agree c g0 g2 →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS hed x → FitsS tel y → HoldsN hed.ned regs x →
        HoldsN tel.ned regs y →
          GoalSem lib O c gul st (Keep g0 g2 (CGoal.next sur th)) regs t (jmp0 g0.bo) (CGoal.next sur th)
            (some (C x y)) := by
    intro c hc σ O st regs t gul x y fx fy hx hy
    refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩
  have hnot : ∀ x y, ¬ FitsS hed x ∨ ¬ FitsS tel y → ¬ FitsS sur (C x y) := fun x y hn hf => by
    rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  have cq := Ud.clean (goal := CGoal.next tel nexh.th) trivial CS.2 h3
  rcases pastL_hinted hd hph with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
  · -- the head's need asks nothing: no block of `+past`
    subst nexh g2'
    have Rq := Ud.run (sup := sup) (goal := CGoal.next tel (jmp0 g0.bo)) (region := region) trivial rfl
      ⟨b0, by simp only [jmp0]; omega⟩ ⟨Dt, lt2' _ Mt⟩ CS.2 (by omega) (by omega) d2 u2 cl2 cb2 (nk2 _ Mt) h3
    have d3 : g3.drop = false := Rq.ext.2.2.1.trans d2
    have u3 : UpBelow g3 := Rq.grow.up u2
    have Rp := up.next (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
      ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) Rq.ext.1⟩ CS.1 (by omega)
      (by have := Rq.lo; have := Rq.hi; omega) d3 u3 (cl2.growU Rq.grow) (Rq.cfr.below cb2)
      (fun y hy => by rw [Rq.cfr.get_lt (lt2' _ Mh y hy)]; exact nk2 _ Mh y hy) h4
    have cp := up.clean (goal := CGoal.next hed nex2.th) CS.1 h4
    exact consNT_ok (Lh := ofSure hed) hfh Mp hok E2 G2U c2 hcb Mh Mt Dht (Ext.refl g2) (GrowU.refl g2) rfl rfl
      en (fun v => fitsS_trivial en es v) (Or.inl ⟨rfl, entries_ofSure hed, fun x => fitsS_trivial en es x, en⟩)
      Rq (Rp.toL (fun _ => A 0)) cq cp hcp hu d0 hnot hfix hblk
  · -- the head's need parked in a bond behind the tail
    subst nexh g2'
    have hbk : ∀ k, HoonMap.get ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region).blocks k =
        if k = g2.bo then some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ else HoonMap.get g2.blocks k := fun k => by
      simp only [tagged_blocks, Gen.emitted, d2, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
    have Eb : Ext g2 ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) :=
      (ext_emit g2 _).trans (ext_tagged _ _ _)
    have Gb : GrowU g2 ((g2.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).tagged g2.bo region) :=
      (growU_emit (b := ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) (fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; exact ⟨b0, lt2⟩) u2).trans
        (growU_tagged _ _ _)
    have Rq := Ud.run (sup := sup) (goal := CGoal.next tel (jmp0 g2.bo)) (region := region) trivial rfl
      ⟨by simp only [jmp0]; omega, by simp [jmp0, Gen.emitted]⟩
      ⟨Dt, fun y hy => by have := lt2' _ Mt y hy; simp [Gen.emitted]; omega⟩ CS.2 (by omega)
      (by simp [Gen.emitted]) (by simp [Gen.emitted, d2]) (Gb.up u2) (cl2.growU Gb)
      (fun k hk => by
        rw [tagged_cond] at hk
        have := cb2 k hk
        simp [Gen.emitted]; omega)
      (fun y hy => by rw [tagged_cond]; exact nk2 _ Mt y hy) h3
    have fr := Ed (sup := sup) (region := region) ⟨by simp only [jmp0]; omega, by simp [jmp0, Gen.emitted]⟩ rfl
      ⟨Dt, fun y hy => by have := lt2' _ Mt y hy; simp [Gen.emitted]; omega⟩ CS.2 (by omega)
      (by simp [Gen.emitted]) (by simp [Gen.emitted, d2]) (Gb.up u2) (cl2.growU Gb)
      (fun k hk => by
        rw [tagged_cond] at hk
        have := cb2 k hk
        simp [Gen.emitted]; omega)
      (fun y hy => by rw [tagged_cond]; exact nk2 _ Mt y hy) h3
    have fr' : g2.bo + 1 ≤ nex2.th.there := by simpa [Gen.emitted] using fr
    have d3 : g3.drop = false := Rq.ext.2.2.1.trans (by simp [Gen.emitted, d2])
    have u3 : UpBelow g3 := Rq.grow.up (Gb.up u2)
    have bo3 : g2.bo + 1 ≤ g3.bo := by simpa [Gen.emitted] using Rq.ext.2.1
    have re3 : g2.re ≤ g3.re := by simpa [Gen.emitted] using Rq.ext.1
    obtain ⟨cp, D, W, RL⟩ := Bp (region := region) (jb := jmp0 g0.bo) (by omega) (by omega) d3 u3
      ((cl2.growU Gb).growU Rq.grow) (Rq.cfr.below (by
        intro k hk
        rw [tagged_cond] at hk
        have := cb2 k hk
        simp [Gen.emitted]; omega)) Rq.lo Rq.hi (by omega) (by omega)
      (by rw [Rq.ext.2.2.2 _ (by simp [Gen.emitted]), hbk, if_pos rfl])
      Dh (fun x hx => ⟨by have := lt2' _ Mh x hx; omega, by
        rw [Rq.cfr.get_lt (by have := lt2' _ Mh x hx; simp [Gen.emitted]; omega), tagged_cond]
        exact nk2 _ Mh x hx⟩) h4
    exact consNT_ok (Lh := mk (Sure.bunt : Sure S) [] [(g2.bo, ofSure hed)]) hfh Mp hok E2 G2U c2 hcb Mh Mt Dht
      Eb Gb (by rw [tagged_cond]; rfl)
      (by simp [Gen.emitted]) rfl (fun v => fitsS_bunt v)
      (Or.inr ⟨rfl, entries_bond1 g2.bo hed, by simp [Gen.emitted], by rw [hbk, if_pos rfl]⟩)
      Rq RL cq cp hcp hu d0 hnot hfix hblk

end Comp
end SkaModel
end Formalization
