import lemmas.Ska.CompFragUN
import lemmas.Ska.CompConsN

/-!
# Two operands and cons with proxy runs under a fork-free `%next`

README Gaps 12.2 (seventh session).

* `AgreeU.part`: `AgreeP.part` with the blocks unproxied.
* `binaryNV_ok`: `binaryN_ok` with `RunOKNV` parts and `AgreeU`, for a
  fork-free `%next`.  The copy block mentions only the two sure needs'
  registers (no keys of `cond`, `ncond`) and fresh ones, so unproxying
  leaves it alone (`keepsA_copy` with the predicate "no key of `cond`",
  `keeps_copy`); the blocks before the two runs by hypothesis (`hfix`).
* `consNV_body`, `okNV_cons`: cons under a fork-free `%next` with parts
  that meet `OKNV` (`consN_body` with `OKNV` parts).  The `%con` block of
  `+split` meets `hfix` (`keepsA_split`, `keeps_split`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `AgreeU` of a part of the run, from `AgreeU` of the whole (`AgreeP.part`
with the blocks unproxied). -/
theorem AgreeU.part {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cf : Map (Nat × List Nat)} {ned : Need} {g0 g3 ga gb : Gen Map} {L La : Lazy S} {s0 s : Noun}
    (ag : AgreeU lib O c gul st t cf ned g0 g3 L s0 s) (h0 : g0.bo ≤ ga.bo) (eb : Ext gb g3)
    (hmem : ∀ e ∈ entries La, e ∈ entries L)
    (hout : ∀ k, ga.bo ≤ k → k < gb.bo → k ∈ (entries L).map Prod.fst → k ∈ (entries La).map Prod.fst)
    (hlab : ∀ e ∈ entries La, e.1 < gb.bo) :
    AgreeU lib O c gul st t cf ned ga gb La s0 s := by
  refine ⟨fun o h0' h1 hn => by
    rw [ag.1 o (Nat.le_trans h0 h0') (Nat.lt_of_lt_of_le h1 eb.2.1) (fun hm => hn (hout o h0' h1 hm)),
      eb.2.2.2 o h1], fun e he => ?_⟩
  obtain ⟨A, th, h1, h2, h3⟩ := ag.2 e (hmem e he)
  exact ⟨A, th, by rw [← eb.2.2.2 _ (hlab e he)]; exact h1, h2, h3.mono eb.1⟩

/-- **Two operands whose runs may make proxies, under a fork-free `%next`**
(`binaryN_ok` with `RunOKNV` parts).  The parts' `sem` are taken at the
whole run's later `cond` through `CondFresh.get_lt`; the copy block mentions
only the two sure needs' registers (no keys, `ncond`) and fresh ones
(`keepsA_copy` with the predicate "no key of `cond`", `keeps_copy`), so
unproxying leaves it alone; the blocks before the two runs are left alone by
hypothesis (`hfix`), which `+split` meets. -/
theorem binaryNV_ok {lib : Lib} {nm p q : Nomm} {sur : Sure S} {th : Jmp} {g0 g' g1 g2 g3 : Gen Map}
    {lp lq : Sure S} {o : Nat} {nexq nexp nex : NextL S} {f : Noun → Noun → Option Noun}
    (hev : ∀ s, pureEval nm s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => f x y)
    (hg : GoalOK g0 (CGoal.next sur th)) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hcb : CondBelow g0)
    (hlp : ∀ r, NMem lp.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hq : RunOKNV (Map := Map) lib q lq (jmp0 o) g' g1 nexq)
    (hp : RunOKNV (Map := Map) lib p lp nexq.th g1 g2 nexp)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3))
    (hu : UpBelow g0) (d0 : g0.drop = false) (hsz : sixCount p + sixCount q ≤ sixCount nm)
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → f x y = none ∨ ∃ v, f x y = some v ∧ GNot (CGoal.next sur th) v)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y →
          GoalSem lib O c gul st (Keep g0 g' (CGoal.next sur th)) regs t (jmp0 o) (CGoal.next sur th) (f x y)) :
    RunOKNV (Map := Map) lib nm sur th g0 g3 nex := by
  -- the labels of the two runs are apart
  have lq' : ∀ e ∈ entries nexq.laz, g'.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(hq.labs e he).1, Nat.lt_trans (hq.labs e he).2.1 hq.hi⟩
  have lp' : ∀ e ∈ entries nexp.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(hp.labs e he).1, Nat.lt_trans (hp.labs e he).2.1 hp.hi⟩
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
  have gm : ∀ r, GMem (CGoal.next sur th) r → r < g0.re := fun r hr => hg.2 r hr
  have lpl : ∀ r, NMem lp.ned r → r < g'.re := fun r hr => by
    rcases hlp r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have lql : ∀ r, NMem lq.ned r → r < g'.re := fun r hr => by
    rcases hlq r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have mp : ∀ r, NMem nexp.laz.sure.ned r → NMem lp.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := hp.regs
  have mq : ∀ r, NMem nexq.laz.sure.ned r → NMem lq.ned r ∨ (g'.re ≤ r ∧ r < g1.re) := hq.regs
  have l0 := hpre.1
  have l1 := hq.ext.1
  have l2 := hp.ext.1
  have l3 := EC.1
  have lowP : ∀ r, NMem nexp.laz.sure.ned r → r < g2.re := fun r hr => by
    rcases mp r hr with a | ⟨_, a⟩
    · have := lpl r a; omega
    · exact a
  have lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases mq r hr with a | ⟨_, a⟩
    · have := lql r a; omega
    · exact a
  have P : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · rcases mp r h1 with a | ⟨a, _⟩ <;> rcases mq r h2 with b | ⟨b, b'⟩
      · exact hpq r a b
      · have := lpl r a; omega
      · have := lql r b; omega
      · omega
    · rcases hr with h | h
      · exact lowP r h
      · have := lowQ r h; omega
  obtain ⟨CD, CF, CB⟩ := CS P
  have d2 : g2.drop = false := hp.ext.2.2.1.trans (hq.ext.2.2.1.trans (hpre.2.2.1.trans d0))
  have Dc := copy_down (goal := CGoal.next sur th) hcp hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  have u2 : UpBelow g2 := (hgr.trans (hq.grow.trans hp.grow)).up hu
  have Eq3 : Ext g1 g3 := hp.ext.trans EC
  have E'3 : Ext g' g3 := hq.ext.trans Eq3
  have bo01 := hpre.2.1
  have bo12 := hq.ext.2.1
  have bo23 := hp.ext.2.1
  have hp3 : Ext g2 g3 := EC
  have cb2 : CondBelow g2 := ((condFresh_of_eq hpre.1 hcnd).trans (hq.cfr.trans hp.cfr)).below hcb
  have nkq : ∀ r, NMem nexq.laz.sure.ned r → HoonMap.get g2.cond r = Option.none := fun r h => by
    rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h
  have thq : nexq.th.args = [] := nextArgs_nil hq.ent rfl
  have thp : nexp.th.args = [] := nextArgs_nil hp.ent thq
  have AC : AboveIn (fun r => HoonMap.get g2.cond r = Option.none) g2.bo g3 :=
    (keepsA_copy (P := fun r => HoonMap.get g2.cond r = Option.none) (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨hp.ncond, jmpIn_nil thp⟩ nkq (fun r hr => condBelow_none cb2 hr) hcp).1.ab _
      (aboveIn_start _ g2)
  have BC : BelowIn g2.bo g3 :=
    (keeps_copy (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨fun r hr => lowP r hr, jmpIn_nil thp⟩ (fun r hr => by have := lowQ r hr; omega) hcp).1.bel _
      (belowIn_start g2)
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
  refine {
    ext := hpre.trans E'3
    grow := hgr.trans (hq.grow.trans (hp.grow.trans (Dc.grow.toU u2)))
    cfr := ((condFresh_of_eq hpre.1 hcnd).trans hq.cfr).trans (hp.cfr.trans (condFresh_of_eq EC.1 kc3))
    lo := Dc.lo
    hi := Dc.hi
    ent := Dc.entry
    regs := fun r hr => ?_
    dist := CD
    eregs := fun e he => ?_
    labs := fun e he => ?_
    nodup := ?_
    size := ?_
    nec := fun s hs => ?_
    ncond := fun r hr => ?_
    econd := fun e he r hr => ?_
    sem := fun cf hcf c ned σ O st t gul s0 s ag hned regs hh hn => ?_ }
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
    · exact ⟨(hp.eregs e a).1, fun r hr => by have := (hp.eregs e a).2 r hr; omega⟩
    · exact ⟨(hq.eregs e a).1, fun r hr => by have := (hq.eregs e a).2 r hr; omega⟩
  · show g0.bo ≤ e.1 ∧ e.1 < n.th.there ∧ _
    rw [eth]
    simp only [jmp0]
    rcases (memN e).mp he with a | a
    · obtain ⟨x, y, th, z⟩ := hp.labs e a
      have := hp.hi
      exact ⟨by omega, by omega, th, by rw [hp3.2.2.2 _ (by omega)]; exact z⟩
    · obtain ⟨x, y, th, z⟩ := hq.labs e a
      have := hq.hi
      exact ⟨by omega, by omega, th, by rw [Eq3.2.2.2 _ (by omega)]; exact z⟩
  · rw [((entries_side_perm _ _ _).map Prod.fst).nodup_iff, List.map_append, List.nodup_append]
    refine ⟨hp.nodup, hq.nodup, fun a ha b hb => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    have := lp' e he; have := lq' e' he'; omega
  · rw [(entries_side_perm _ _ _).length_eq, List.length_append]
    have := hp.size; have := hq.size; omega
  · rw [hev]
    have hn : ¬ FitsS nexp.laz.sure s ∨ ¬ FitsS nexq.laz.sure s := by
      by_cases a : FitsS nexp.laz.sure s
      · exact Or.inr fun b => hs ((CF s).mpr ⟨a, b⟩)
      · exact Or.inl a
    cases ep : pureEval p s with
    | none => exact Or.inl rfl
    | some x =>
      cases eq : pureEval q s with
      | none => exact Or.inl rfl
      | some y =>
        simp only [Option.bind_some]
        rcases hn with a | a
        · rcases hp.nec s a with e | ⟨x', e, hx⟩
          · rw [ep] at e; cases e
          · rw [ep] at e; cases e
            exact hnot x y (Or.inl hx)
        · rcases hq.nec s a with e | ⟨y', e, hy⟩
          · rw [eq] at e; cases e
          · rw [eq] at e; cases e
            exact hnot x y (Or.inr hy)
  · rw [kc3]
    rcases CM r hr with h | h | ⟨h, h'⟩
    · exact hp.ncond r h
    · rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h
    · exact condBelow_none cb2 h
  · rw [kc3]
    rcases (memN e).mp he with a | a
    · exact hp.econd e a r hr
    · rw [hp.cfr.get_lt ((hq.eregs e a).2 r hr).2]; exact hq.econd e a r hr
  · -- the copy block
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf1 k (by omega)).trans ((hq.cfr.get_lt hk).trans (by rw [hcnd]))
    have agC : Agree c g2 g3 := fun k h0 h1 => by
      rw [ag.1 k (by omega) h1 (fun hm => by have := labN k hm; omega)]
      exact fixC cf hcf k h0 h1
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
    have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; omega
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
      have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : AgreeU lib O c gul st t cf ned g1 g2 nexp.laz s0 s :=
      ag.part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)
    have Hp := hp.sem cf hcf2 c ned σ O st t gul s0 s agP hned2 R1 hs1 hn1
    have agQ0 : Agree c g0 g' := fun k h0 h1 => by
      rw [ag.1 k h0 (by omega) (fun hm => by have := labN k hm; omega), E'3.2.2.2 k h1]
      exact hfix cf hcf0 k h0 h1
    -- the kept registers
    have keep1 : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ GMem (CGoal.next sur th) r →
        SkaModel.read r R1 = SkaModel.read r regs := by
      intro r k1 k2
      refine u1 r (fun hm => ?_) (fun hm => ?_)
      · rcases mp r hm with a | ⟨a, a'⟩
        · rcases hlp r a with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned r k1; omega
        · rcases k1 with k1 | k1
          · omega
          · have := hned r k1; omega
      · rcases mq r hm with a | ⟨a, a'⟩
        · rcases hlq r a with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned r k1; omega
        · rcases k1 with k1 | k1
          · omega
          · have := hned r k1; omega
    rw [hev]
    cases ep : pureEval p s with
    | none =>
      rw [ep] at Hp
      exact goalSem_crash (CGoal.next sur th) (by rw [eth] at e1 ⊢; exact e1.trans Hp)
    | some x =>
      rw [ep] at Hp
      simp only [Option.bind_some]
      by_cases fx : FitsS lp x
      · obtain ⟨R2, hl2, k2, e2⟩ := Hp.1 fx
        have hq2 : HoldsS nexq.laz.sure R2 s := by
          refine ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), ?_⟩) hs1'.1, hs1'.2⟩
          intro hm
          rcases mq r hr with a | ⟨a, _⟩
          · exact hpq r hm a
          · have := lpl r hm; omega
        have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, fun hm => by
          have := lpl r hm; have := hned r hr; omega⟩) hn1
        have agQ : AgreeU lib O c gul st t cf ned g' g1 nexq.laz s0 s :=
          ag.part bo01 Eq3 (fun e he => (memN e).mpr (Or.inr he))
            (fun k h0 h1 hm => by
              obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
              rcases (memN e).mp he with a | a
              · have := lp' e a; omega
              · exact List.mem_map_of_mem a)
            (fun e he => (lq' e he).2)
        have Hq := hq.sem cf hcf1 c ned σ O st t gul s0 s agQ hned1 R2 hq2 hn2
        cases eq : pureEval q s with
        | none =>
          rw [eq] at Hq
          exact goalSem_crash (CGoal.next sur th) (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans Hq))
        | some y =>
          rw [eq] at Hq
          simp only [Option.bind_some]
          by_cases fy : FitsS lq y
          · obtain ⟨R3, hq3, k3, e3⟩ := Hq.1 fy
            have hl3 : HoldsN lp.ned R3 x :=
              HoldsN.agree _ (fun r hr => k3 r ⟨Or.inl (lpl r hr), hpq r hr⟩) hl2
            have B := hblk c agQ0 σ O st R3 t gul x y fx fy hl3 hq3
            refine GoalSem.transfer (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans e3)) (fun r hk => ?_)
              (GoalSem.mono (fun r ⟨k1, k2⟩ => ⟨k1.imp id (fun h => by have := hned r h; omega), k2⟩) B)
            obtain ⟨k1, k2'⟩ := hk
            have nlq : ¬ NMem lq.ned r := fun hm => by
              rcases hlq r hm with b | ⟨b, b'⟩
              · exact k2' b
              · rcases k1 with k1 | k1
                · omega
                · have := hned r k1; omega
            have nlp : ¬ NMem lp.ned r := fun hm => by
              rcases hlp r hm with b | ⟨b, b'⟩
              · exact k2' b
              · rcases k1 with k1 | k1
                · omega
                · have := hned r k1; omega
            rw [k3 r ⟨k1.imp (fun h => by omega) id, nlq⟩, k2 r ⟨k1.imp (fun h => by omega) id, nlp⟩,
              keep1 r k1 k2']
          · exact goalSem_crash_or (hnot x y (Or.inr fy))
              (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans (Hq.2 fy)))
      · have hc2 := Hp.2 fx
        cases eq : pureEval q s with
        | none => exact goalSem_crash (CGoal.next sur th) (by rw [eth] at e1 ⊢; exact e1.trans hc2)
        | some y =>
          simp only [Option.bind_some]
          exact goalSem_crash_or (hnot x y (Or.inl fx)) (by rw [eth] at e1 ⊢; exact e1.trans hc2)

/-- **Cons for a fork-free `%next` with parts that may make proxies**, the
body after the goal is `%next` (`consN_body` with `OKNV` parts).  The tail
runs for the tail register(s) of `+split` and the head after it for the head
register(s): both are registers of the goal's need (no keys by `hkg`) or
fresh at the split, and the tail's proxies are fresh from its own start on,
so neither part's need has a key of `cond` when it runs.  The `%con` block
of `+split` mentions the goal's need and fresh registers, so unproxying by
any later `cond` leaves it alone (`hfix` of `binaryNV_ok`). -/
theorem consNV_body (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)
    (hq : OKNV (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (hcount : sixCount (Nomm.cons p q) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0) (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    RunOKNV (Map := Map) lib (Nomm.cons p q) sur th g0 g1 nex := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hqp, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
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
  simp only [sixCount] at hcount
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
  have Rq := hq (sur := tel) (th := jmp0 g0.bo) ⟨b0, by simp only [jmp0]; omega⟩ rfl ⟨Dt, lt2' _ Mt⟩ CS.2
    (by omega) (by omega) d2 u2 cl2 cb2 (nk2 _ Mt) h3
  have d3 : g3.drop = false := Rq.ext.2.2.1.trans d2
  have u3 : UpBelow g3 := Rq.grow.up u2
  have Rp := hp (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) Rq.ext.1⟩ CS.1 (by omega)
    (by have := Rq.lo; have := Rq.hi; omega) d3 u3 (cl2.growU Rq.grow) (Rq.cfr.below cb2)
    (fun y hy => by rw [Rq.cfr.get_lt (lt2' _ Mh y hy)]; exact nk2 _ Mh y hy) h4
  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g2 :=
    (keepsA_split (P := fun r => HoonMap.get g0.cond r = Option.none) d0 hkg (jmpIn_nil hth)
      (fun r hr => condBelow_none hcb hr) hs2).1.ab _ (aboveIn_start _ g0)
  have BS : BelowIn g0.bo g2 :=
    (keeps_split d0 (fun r hr => hok.2 r hr) (jmpIn_nil hth) hs2).1.bel _ (belowIn_start g0)
  refine binaryNV_ok (pureEval_cons p q) hok E2 (G2.toU hu) c2 hcb Mh Mt Dht Rq Rp (cq CS.2 h3) (cp CS.1 h4) hcp hu d0
    (by simp only [sixCount]; omega) (fun x y hn => Or.inr ⟨C x y, rfl, fun hf => ?_⟩) ?_
    (fun c hc σ O st regs t gul x y fx fy hx hy => ?_)
  · rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  · intro cf hcf k h0 h1
    have u0 : ∀ x, x < g2.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
    have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
    cases hg : HoonMap.get g2.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1 hg), renBlob_congr u1 (AS k b h0 h1 hg), renBlob_id]
  · refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩

/-- **Cons with parts that meet `OKNV` meets `OKNV`.** -/
theorem okNV_cons (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)
    (hq : OKNV (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) : OKNV (S := S) (Map := Map) lib (Nomm.cons p q) :=
  fun hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h => by
    rw [runL_cons_next] at h
    exact consNV_body lib hp hq cp cq hpp hqp hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h

/-- **A cons whose head and tail are in `FragX` or are `[7 [4 p] q]` with
`p`, `q` in `FragX`** meets `OKNV`, given that the sure needs of the parts'
runs are clean. -/
example (lib : Lib) {p q : Nomm} (hp : FragX (S := S) p) (hq : FragX (S := S) q) {q' : Nomm}
    (hq' : FragX (S := S) q') (cq : CleanN S Map (Nomm.n7 (Nomm.n4 p) q)) :
    OKNV (S := S) (Map := Map) lib (Nomm.cons (Nomm.n7 (Nomm.n4 p) q) q') :=
  okNV_cons lib (okNV_seven4 lib hp hq) (okNV_fragX lib hq') cq (CleanA.toN (runX_clean hq'))
    (by simp only [Nomm.pure, fragX_pure hp, fragX_pure hq, Bool.and_self]) (fragX_pure hq')

end Comp
end SkaModel
end Formalization
