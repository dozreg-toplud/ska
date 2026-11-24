import lemmas.Ska.CompFragM

/-!
# Two operands whose runs have lazy blocks

`binaryN_ok`: the shape of the cases `[5 p q]` and `[p q]` of `run` when
the runs of `p` and `q` are for fork-free `%next` goals and meet `RunOKN`,
so that their needs may have lazy blocks (from a `%6` in them).  `q` is
compiled first, for `%next lq (jmp0 o)`, then `p` for `%next lp nexq.th`,
then `+copy` puts the two lazy needs side by side: the lazy blocks of `p`
were allocated after those of `q`, so their labels are apart and
`+copy-lazy` merges only the sure needs (`copyL_apart_some`, from
`copyLazyL_apart`).  At runtime the copy block fills both sure needs, the
code of `p` runs and keeps the registers of `q`'s sure need and the input
registers that the fill ops of `q`'s lazy blocks read, and then the code of
`q` runs.

The result is `RunOKG`, the relation for any goal: for `%next` it is
`RunOKN` (`RunOKG.toN`), for `%done` and `%pick` it gives `RunOKP`
(`RunOKG.toP`).  The sure needs of the two runs must be clean, as for
`binary_ok`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation for any goal -/

/-- **The relation for one run of `runL` for any fork-free goal**: `RunOKN`
with the goal's registers and its `GNot` in place of the sure need's. -/
structure RunOKG (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cnd : g1.cond = g0.cond
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ GNot goal p
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ GMem goal r) regs t nex.th goal (pureEval nm s)

theorem RunOKG.toN {lib : Lib} {nm : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (h : RunOKG (Map := Map) lib nm (CGoal.next sur th) g0 g1 nex) : RunOKN (Map := Map) lib nm sur th g0 g1 nex :=
  ⟨h.ext, h.grow, h.cnd, h.lo, h.hi, h.ent, h.regs, h.dist, h.eregs, h.labs, h.nodup, h.size, h.nec, h.sem⟩

theorem RunOKG.toP {lib : Lib} {nm : Nomm} {goal : CGoal S} (hg : NotNext goal) {g0 g1 : Gen Map} {nex : NextL S}
    (h : RunOKG (Map := Map) lib nm goal g0 g1 nex) : RunOKP (Map := Map) lib nm goal g0 g1 nex := by
  refine ⟨h.ext, h.grow, h.cnd, h.lo, h.hi, h.ent, fun r hr => ?_, h.dist, h.eregs, h.labs, h.nodup, h.size,
    fun s hs => ?_, fun c ned σ O st t gul s0 s ag hned regs hh hn => ?_⟩
  · rcases h.regs r hr with a | a
    · exact (notNext_gmem hg r a).elim
    · exact a
  · rcases h.nec s hs with a | ⟨p, _, a⟩
    · exact a
    · exact (notNext_gnot hg p a).elim
  · exact goalSem_mono (fun r hr => ⟨hr, notNext_gmem hg r⟩) _ _ (h.sem c ned σ O st t gul s0 s ag hned regs hh hn)

/-! ## `+copy` of two lazy needs whose blocks are apart -/

theorem bond_mem_entries {e : Nat × Lazy S} : ∀ {b : List (Nat × Lazy S)}, e ∈ b → e ∈ bondEntries b
  | (o, l) :: rest, h => by
    simp only [bondEntries, List.mem_append, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (bond_mem_entries h)

theorem bondEntries_append : ∀ (b1 b2 : List (Nat × Lazy S)),
    bondEntries (b1 ++ b2) = bondEntries b1 ++ bondEntries b2
  | [], _ => rfl
  | (o, l) :: rest, b2 => by
    simp only [List.cons_append, bondEntries, bondEntries_append rest b2, List.append_assoc]

/-- The entries of two lazy needs put side by side are those of the two. -/
theorem entries_side_perm (s : Sure S) (l1 l2 : Lazy S) :
    (entries (mk s (l1.fork ++ l2.fork) (l1.bond ++ l2.bond))).Perm (entries l1 ++ entries l2) := by
  rw [entries_eq l1, entries_eq l2]
  simp only [entries, bondEntries_append, forkEntries_append, List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

/-- **`+copy` of two lazy needs whose blocks are apart** is the `+copy` of
their sure needs, with the forks and the bonds side by side. -/
theorem copyL_apart_some {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (hf : ∀ e ∈ first.laz.fork, ∀ e' ∈ second.fork, e.1.1 ≠ e'.1.1)
    (hb : ∀ e ∈ first.laz.bond, ∀ e' ∈ second.bond, e.1 ≠ e'.1)
    (h : copyL first second g = some (nex, g')) :
    ∃ n : Next S, copy ⟨first.laz.sure, first.th⟩ second.sure g = some (n, g') ∧
      nex = ⟨mk n.laz (first.laz.fork ++ second.fork) (first.laz.bond ++ second.bond), n.th⟩ := by
  rcases first with ⟨⟨s1, f1, b1⟩, th⟩
  simp only [fork_mk, bond_mk, sure_mk] at hf hb ⊢
  unfold copyL at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨laz, g1, h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [copyLazyL_apart _ s1 f1 b1 _ hf hb] at h1
  obtain ⟨⟨ned, ops⟩, g2, h2, h1⟩ := bind_some h1
  obtain ⟨u, g3, h3, h1⟩ := bind_some h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  refine ⟨⟨⟨ned, HoonSet.uni s1.lok second.sure.lok⟩, jmp0 g.bo⟩, ?_, rfl⟩
  simp only [copy, copyLazy, bind_apply, emit_apply, Option.bind_some, h2, h3, pure_apply]

/-- `AgreeP` of a part of the run, from `AgreeP` of the whole. -/
theorem AgreeP.part {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {g0 g3 ga gb : Gen Map} {L La : Lazy S} {s0 s : Noun}
    (ag : AgreeP lib O c gul st t ned g0 g3 L s0 s) (h0 : g0.bo ≤ ga.bo) (eb : Ext gb g3)
    (hmem : ∀ e ∈ entries La, e ∈ entries L)
    (hout : ∀ k, ga.bo ≤ k → k < gb.bo → k ∈ (entries L).map Prod.fst → k ∈ (entries La).map Prod.fst)
    (hlab : ∀ e ∈ entries La, e.1 < gb.bo) :
    AgreeP lib O c gul st t ned ga gb La s0 s := by
  refine ⟨fun o h0' h1 hn => (ag.1 o (Nat.le_trans h0 h0') (Nat.lt_of_lt_of_le h1 eb.2.1)
    (fun hm => hn (hout o h0' h1 hm))).trans (eb.2.2.2 o h1), fun e he => ?_⟩
  obtain ⟨A, th, h1, h2, h3⟩ := ag.2 e (hmem e he)
  exact ⟨A, th, by rw [← eb.2.2.2 _ (hlab e he)]; exact h1, h2, h3.mono eb.1⟩

/-! ## Two operands -/

/-- **Two operands whose runs have lazy blocks.** -/
theorem binaryN_ok {lib : Lib} {nm p q : Nomm} {goal : CGoal S} {g0 g' g1 g2 g3 : Gen Map}
    {lp lq : Sure S} {o : Nat} {nexq nexp nex : NextL S} {f : Noun → Noun → Option Noun}
    (hev : ∀ s, pureEval nm s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => f x y)
    (hg : GoalOK g0 goal) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hlp : ∀ r, NMem lp.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hq : RunOKN (Map := Map) lib q lq (jmp0 o) g' g1 nexq)
    (hp : RunOKN (Map := Map) lib p lp nexq.th g1 g2 nexp)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3))
    (hu : UpBelow g0) (d0 : g0.drop = false) (hsz : sixCount p + sixCount q ≤ sixCount nm)
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → f x y = none ∨ ∃ v, f x y = some v ∧ GNot goal v)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y → GoalSem lib O c gul st (Keep g0 g' goal) regs t (jmp0 o) goal (f x y)) :
    RunOKG (Map := Map) lib nm goal g0 g3 nex := by
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
  have gm : ∀ r, GMem goal r → r < g0.re := fun r hr => by
    cases goal with
    | next laz th => exact hg.2 r hr
    | _ => exact hr.elim
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
  have Dc := copy_down (goal := goal) hcp hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  have u2 : UpBelow g2 := (hgr.trans (hq.grow.trans hp.grow)).up hu
  have Eq3 : Ext g1 g3 := hp.ext.trans EC
  have E'3 : Ext g' g3 := hq.ext.trans Eq3
  have bo01 := hpre.2.1
  have bo12 := hq.ext.2.1
  have bo23 := hp.ext.2.1
  have hp3 : Ext g2 g3 := EC
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
    cnd := kc3.trans (hp.cnd.trans (hq.cnd.trans hcnd))
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
    sem := fun c ned σ O st t gul s0 s ag hned regs hh hn => ?_ }
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
  · -- the copy block
    have agC : Agree c g2 g3 := fun k h0 h1 => ag.1 k (by omega) h1 (fun hm => by have := labN k hm; omega)
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
    have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; omega
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
      have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : AgreeP lib O c gul st t ned g1 g2 nexp.laz s0 s :=
      ag.part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)
    have Hp := hp.sem c ned σ O st t gul s0 s agP hned2 R1 hs1 hn1
    have agQ0 : Agree c g0 g' := fun k h0 h1 =>
      (ag.1 k h0 (by omega) (fun hm => by have := labN k hm; omega)).trans (E'3.2.2.2 k h1)
    -- the kept registers
    have keep1 : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ GMem goal r →
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
      exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans Hp)
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
        have agQ : AgreeP lib O c gul st t ned g' g1 nexq.laz s0 s :=
          ag.part bo01 Eq3 (fun e he => (memN e).mpr (Or.inr he))
            (fun k h0 h1 hm => by
              obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
              rcases (memN e).mp he with a | a
              · have := lp' e a; omega
              · exact List.mem_map_of_mem a)
            (fun e he => (lq' e he).2)
        have Hq := hq.sem c ned σ O st t gul s0 s agQ hned1 R2 hq2 hn2
        cases eq : pureEval q s with
        | none =>
          rw [eq] at Hq
          exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans Hq))
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
        | none => exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans hc2)
        | some y =>
          simp only [Option.bind_some]
          exact goalSem_crash_or (hnot x y (Or.inl fx)) (by rw [eth] at e1 ⊢; exact e1.trans hc2)

end Comp
end SkaModel
end Formalization
