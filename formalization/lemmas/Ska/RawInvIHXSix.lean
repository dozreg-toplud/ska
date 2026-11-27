import lemmas.Ska.RawInvIHXBin
import lemmas.Ska.CompSixNext
import lemmas.Ska.CompSixNextRun

/-!
# Raw `+comp` output on `FragX`: the case `%6`

README Gaps 14, track D, step 2 of the class `FragX`.  The case `six` of
`RawIHX` and the induction over `FragX`.

* The frame of a sub-run (the blocks below its start are kept) comes from
  track C's `runX_ok` (`RunOKP.ext`, `RunOKN.ext`), with a dummy `lib0`:
  `runX_frameP` (`%done`, `%pick`), `runX_frameN` (`%next` with a clean
  need); `sip_upBelow` gives its `UpBelow`.
* **`rawX_sixTail`**: from the state after both branches, the two hop blocks
  `yes` and `nuh` (`sixGenL`, or a state with the same blocks, as `+sect`
  leaves it), the test for `%pick yes nuh` with the kills `K ∨ lazK yes ..
  ∨ lazK nuh ..` cut at that state's `bo`, and `+copy` of the test's result
  with the fork (`copyL_six_apart`: the copy block is a bare hop).  At `yes`
  the kill of the yes branch's sure need stands in for the root kill of its
  run, so a register live there is live at the branch's entry with the
  branch's kills.
* **`rawX_sixP`**: `%done` and `%pick` (`sixBody_apart`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X]

/-! ## Small facts -/

/-- A `Lib` for the relations of track C whose structural fields are all
that is used here. -/
def lib0 : Lib := ⟨fun _ _ => Option.none, fun _ => Option.none, fun _ _ => Option.none, fun _ => Noun.atom 0⟩

theorem sip_upBelow {g : Comp.Gen Map} (h : SIP X (upRk g.blocks) g.bo g) : UpBelow g := by
  intro u t hu
  have e := upRk_up hu
  obtain ⟨b, j, hb, -, -, -⟩ := hu
  have := h.rlo u (h.lab u b hb)
  omega

theorem sip_tagged {ρ : Nat → Nat} {lo : Nat} {g : Comp.Gen Map} (h : SIP X ρ lo g) (o : Nat) (rb : List Nat) :
    SIP X ρ lo (g.tagged o rb) := by
  unfold Gen.tagged
  split
  · exact h
  · exact ⟨h.drop, h.bo1, h.lab, h.regs, h.nd, h.cr, h.tr, h.jr, h.lob, h.rk, h.rlo, h.x⟩

theorem sixGenL_get_lt {g2 : Comp.Gen Map} {th0 th1 : Jmp} {rb : List Nat} {k : Nat} (hk : k < g2.bo) :
    HoonMap.get (sixGenL g2 th0 th1 rb).blocks k = HoonMap.get g2.blocks k := by
  simp only [sixGenL, tagged_blocks]
  rw [get_emitted_ne (by simp [emitted_bo]; omega), get_emitted_ne (by omega)]

/-- **The two hop blocks of `%6` keep the invariant.** -/
theorem sip_sixGenL {g2 : Comp.Gen Map} {th0 th1 : Jmp} {rb : List Nat} (h : SIP X (upRk g2.blocks) g2.bo g2)
    (a0 : th0.args = []) (a1 : th1.args = []) (t0 : th0.there < g2.bo) (t1 : th1.there < g2.bo) :
    SIP X (upRk (sixGenL g2 th0 th1 rb).blocks) (sixGenL g2 th0 th1 rb).bo (sixGenL g2 th0 th1 rb) := by
  obtain ⟨S1, -, -, -, -⟩ := sip_emit h (emitOK_hop a0 t0) (emit_apply _ _)
  obtain ⟨S2, -, -, -, -⟩ := sip_emit S1 (emitOK_hop a1 (by simp [emitted_bo]; omega)) (emit_apply _ _)
  exact sip_reRank (sip_tagged (sip_tagged S2 _ _) _ _) (fun k hk => h.none hk)
    (finKeep_of_eq fun x hx => sixGenL_get_lt hx)

/-- At a block that only hops, with no arguments, liveness goes on at the
target. -/
theorem liveK_hop {bl : Map Blob} {K : Nat → Nat → Prop} {k r : Nat} {b : Blob} {j : Jmp}
    (hb : HoonMap.get bl k = some b) (hbd : b.body = []) (hf : b.fin = Termin.hop j) (ha : j.args = [])
    (h : LiveK bl K k r) : LiveK bl K j.there r ∧ ¬ K k r := by
  refine ⟨?_, h.nk⟩
  obtain ⟨b', hb', hr⟩ := liveK_cases h
  rw [hb] at hb'; cases hb'
  rcases hr with ⟨-, hr⟩ | ⟨j', hj', hl, -⟩
  · rw [hbd, hf] at hr
    simp [OpsRF, finRegs, jmpRegs, ha] at hr
  · rw [hf] at hj'
    simp [getJmps] at hj'
    subst hj'; exact hl

theorem lazK_six0 {y n o a r : Nat} {s : Sure S} {l0 l1 : Lazy S} (h : lazK y l0 a r) :
    lazK o (mk s [((y, l0), (n, l1))] []) a r := by
  obtain ⟨e, he, rfl, h2⟩ := h
  exact lazK_ent (by rw [entries_six]; exact List.mem_append_left _ he) h2

theorem lazK_six1 {y n o a r : Nat} {s : Sure S} {l0 l1 : Lazy S} (h : lazK n l1 a r) :
    lazK o (mk s [((y, l0), (n, l1))] []) a r := by
  obtain ⟨e, he, rfl, h2⟩ := h
  exact lazK_ent (by rw [entries_six]; exact List.mem_append_right _ he) h2

/-! ## The frame of a sub-run, from track C -/

theorem runX_frameP {nm : Nomm} (hf : FragX (S := S) nm) {goal : CGoal S} (hn : NotNext goal) {region : List Nat}
    {g0 g1 : Comp.Gen Map} {nex : NextL S} (h : SIP X (upRk g0.blocks) g0.bo g0) (hj : GJ g0.bo goal)
    (ha : GArgs goal) (hc : sixCount nm ≤ 255) (hr : runL nm (CGoal.toL goal) region g0 = some (nex, g1)) :
    ∀ k, k < g0.bo → HoonMap.get g1.blocks k = HoonMap.get g0.blocks k := by
  have O := runX_ok (Map := Map) lib0 hf
  cases goal with
  | next => exact hn.elim
  | done => exact (O.1 hn hj hc h.bo1 h.drop (sip_upBelow h) hr).ext.2.2.2
  | pick z o => exact (O.2.2 z o ha.1 ha.2 hn hj hc h.bo1 h.drop (sip_upBelow h) hr).ext.2.2.2

theorem runX_frameN {nm : Nomm} (hf : FragX (S := S) nm) {sur : Sure S} {th : Jmp} {region : List Nat}
    {g0 g1 : Comp.Gen Map} {nex : NextL S} (h : SIP X (upRk g0.blocks) g0.bo g0)
    (hj : GJ g0.bo (CGoal.next sur th : CGoal S)) (ha : th.args = []) (hd : Distinct sur.ned) (hg : NB g0.re sur.ned)
    (hcl : Clean sur.ned) (hc : sixCount nm ≤ 255)
    (hr : runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    ∀ k, k < g0.bo → HoonMap.get g1.blocks k = HoonMap.get g0.blocks k :=
  ((runX_ok (Map := Map) lib0 hf).2.1 hj ha ⟨hd, hg⟩ hcl hc h.bo1 h.drop (sip_upBelow h) hr).ext.2.2.2

theorem gLiveK_frame {g0 g1 : Comp.Gen Map} {K : Nat → Nat → Prop} {goal : CGoal S} {x : Nat}
    (hd : DownBelowP g0.blocks g0.bo) (he : ∀ k, k < g0.bo → HoonMap.get g1.blocks k = HoonMap.get g0.blocks k)
    (hj : GJ g0.bo goal) (h : GLiveK g1.blocks K goal x) : GLiveK g0.blocks K goal x := by
  cases goal with
  | next laz th => exact ⟨(liveK_frameP hd he hj.2).mp h.1, h.2⟩
  | pick z o => exact h.imp (liveK_frameP hd he hj.1.2).mp (liveK_frameP hd he hj.2.2).mp
  | done => exact h

/-! ## The tail: the hop blocks, the test, the copy -/

/-- **The tail of `%6`.** -/
theorem rawX_sixTail {c : Nomm} (xc' : FragX (S := S) c) (ihc : RawIHX S Map X c) (hcc : sixCount c ≤ 255)
    {g2 gS g3 g4 : Comp.Gen Map} {x0 x1 xc nex : NextL S} {region rb : List Nat} {K : Nat → Nat → Prop}
    (h : SIP X (upRk g2.blocks) g2.bo g2) (t0 : x0.th.there < g2.bo) (t1 : x1.th.there < g2.bo)
    (a0 : x0.th.args = []) (a1 : x1.th.args = [])
    (hS : SameBlocks (sixGenL g2 x0.th x1.th rb) gS) (SS : SIP X (upRk gS.blocks) gS.bo gS)
    (hc : runL c (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region gS = some (xc, g3))
    (h5 : copyL xc (mk Sure.bunt [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) g3 = some (nex, g4)) :
    SIP X (upRk g4.blocks) g4.bo g4 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g4.bo ∧
      ∀ r, LiveK g4.blocks (fun a b => K a b ∨ lazK nex.th.there nex.laz a b) nex.th.there r →
        LiveK g2.blocks (fun a b => K a b ∨ lazK x0.th.there x0.laz a b) x0.th.there r ∨
        LiveK g2.blocks (fun a b => K a b ∨ lazK x1.th.there x1.laz a b) x1.th.there r := by
  have bS : gS.bo = g2.bo + 2 := by rw [hS.2.1]; simp
  have hb1 := h.bo1
  have hKc : KVan (fun a b => a < gS.bo ∧ (K a b ∨ lazK g2.bo x0.laz a b ∨ lazK (g2.bo + 1) x1.laz a b)) gS.bo :=
    ⟨fun k r hk e => by have := e.1; omega⟩
  obtain ⟨S3, a3, lo3, hi3, L3⟩ := ihc (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region gS g3 xc _ hKc SS
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ trivial
    ⟨⟨by simp [jmp0]; omega, by simp [jmp0]; omega⟩, ⟨by simp [jmp0], by simp [jmp0]; omega⟩⟩ ⟨rfl, rfl⟩
    (fun _ _ e => e) hcc trivial hc
  have Rc := runX_keeps xc' (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) SS.drop
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩ hcc hc
  rw [copyL_six_apart xc x0.laz x1.laz g2.bo (g2.bo + 1) g3 (fun e he => by
    have := (Rc.labs _ (fork_in_entries he)).1; omega)] at h5
  obtain ⟨⟨u, g5⟩, h6, e6⟩ := Option.map_eq_some_iff.mp h5
  simp only [Prod.mk.injEq] at e6
  have eg : g5 = g4 := e6.2
  subst eg
  have en := e6.1
  subst en
  obtain ⟨SE, -, eE, -, boE⟩ := sip_emit S3 (emitOK_hop a3 hi3) (emit_apply _ _)
  obtain ⟨S4, b', hb', e4, -, bo4⟩ := sip_addOps SE (opsOK_nil _) h6
  rw [eE, get_put_self] at hb'
  cases hb'
  have fr : ∀ k, k < g3.bo → HoonMap.get g5.blocks k = HoonMap.get g3.blocks k := fun k hk => by
    rw [e4, get_put_ne (by omega), eE, get_put_ne (by omega)]
  refine ⟨sip_reRank S4 (fun k hk => S3.none hk) (finKeep_of_eq fr), rfl, by simp [jmp0]; exact S3.bo1,
    by simp [jmp0]; omega, fun r hl => ?_⟩
  simp only [jmp0] at hl
  obtain ⟨hl1, nk⟩ := liveK_hop (by rw [e4]; exact get_put_self) (by simp [pre]) (by simp [pre]) a3 hl
  have n1 : ¬ NMem xc.laz.sure.ned r := fun e => nk (Or.inr (lazK_root e))
  have side : ∀ {a o1 o2 : Nat}, (lazK o1 xc.laz a r ∨
      lazK o2 (mk Sure.bunt [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] [] : Lazy S) a r) →
      lazK g3.bo (mk ⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩
        (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) a r := by
    intro a o1 o2 e
    have := lazK_side (o := g3.bo) (s := ⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩)
      n1 (fun e => by simp only [sure_mk, Sure.bunt, NMem] at e) e
    simpa only [fork_mk, bond_mk, List.append_nil] using this
  have hl2 := (liveK_frameP (S3.below g3.bo) fr hi3).mp hl1
  have hl3 := hl2.monoB (K' := fun a b => (a < gS.bo ∧ (K a b ∨ lazK g2.bo x0.laz a b ∨
      lazK (g2.bo + 1) x1.laz a b)) ∨ lazK xc.th.there xc.laz a b) fun a bb _ e => by
    rcases e with ⟨-, e | e | e⟩ | e
    · exact Or.inl e
    · exact Or.inr (side (o1 := 0) (o2 := 0) (Or.inr (lazK_six0 e)))
    · exact Or.inr (side (o1 := 0) (o2 := 0) (Or.inr (lazK_six1 e)))
    · exact Or.inr (side (o2 := 0) (Or.inl e))
  have fS : ∀ k, k < g2.bo → HoonMap.get gS.blocks k = HoonMap.get g2.blocks k := fun k hk => by
    rw [hS.2.2.2.2.2.2]; exact sixGenL_get_lt hk
  rcases L3 r hl3 with e | e
  · simp only [jmp0] at e
    have gy : HoonMap.get gS.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
      rw [hS.2.2.2.2.2.2]; exact sixGenL_get_y _ _ _ h.drop
    obtain ⟨e1, nk1⟩ := liveK_hop gy rfl rfl a0 e
    have nn : ¬ NMem x0.laz.sure.ned r := fun m => nk1 ⟨by omega, Or.inr (Or.inl (lazK_root m))⟩
    refine Or.inl (((liveK_frameP (h.below g2.bo) fS t0).mp e1).monoB fun a bb hb m => ?_)
    have := h.lab a bb hb
    rcases m with m | m
    · exact ⟨by omega, Or.inl m⟩
    · rcases lazK_cases m with m | ⟨e', he', rfl, m'⟩
      · exact absurd m nn
      · exact ⟨by omega, Or.inr (Or.inl (lazK_ent he' m'))⟩
  · simp only [jmp0] at e
    have gn : HoonMap.get gS.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
      rw [hS.2.2.2.2.2.2]; exact sixGenL_get_n _ _ _ h.drop
    obtain ⟨e1, nk1⟩ := liveK_hop gn rfl rfl a1 e
    have nn : ¬ NMem x1.laz.sure.ned r := fun m => nk1 ⟨by omega, Or.inr (Or.inr (lazK_root m))⟩
    refine Or.inr (((liveK_frameP (h.below g2.bo) fS t1).mp e1).monoB fun a bb hb m => ?_)
    have := h.lab a bb hb
    rcases m with m | m
    · exact ⟨by omega, Or.inl m⟩
    · rcases lazK_cases m with m | ⟨e', he', rfl, m'⟩
      · exact absurd m nn
      · exact ⟨by omega, Or.inr (Or.inr (lazK_ent he' m'))⟩

/-! ## `%done` and `%pick` -/

/-- **`%6` for `%done` or `%pick`**: `b` and `a` for the goal, the tail. -/
theorem rawX_sixP {c a b : Nomm} (xc' : FragX (S := S) c) (xa : FragX (S := S) a) (xb : FragX (S := S) b)
    (ihc : RawIHX S Map X c) (iha : RawIHX S Map X a) (ihb : RawIHX S Map X b)
    {goal : CGoal S} (hn : NotNext goal) {region : List Nat} {g0 g4 : Comp.Gen Map} {nex : NextL S}
    {K : Nat → Nat → Prop} (hK : KVan K g0.bo) (h : SIP X (upRk g0.blocks) g0.bo g0) (hg : GoalIn g0.re goal)
    (hj : GJ g0.bo goal) (ha : GArgs goal) (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (hr : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g4)) :
    SIP X (upRk g4.blocks) g4.bo g4 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g4.bo ∧
      ∀ r, LiveK g4.blocks (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
        GLiveK g0.blocks K goal r := by
  have hcp := fragX_pure xc'
  have hcl : GClean goal := by cases goal with | next => exact hn.elim | _ => trivial
  have hD : GDist goal := by cases goal with | next => exact hn.elim | _ => trivial
  have hm : ∀ (bl : Map Blob) r, Defd bl r → ¬ GMem goal r := fun _ r _ e => by
    cases goal with | next => exact hn.elim | _ => exact e
  rw [runL_n6_body _ _ _ hn] at hr
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, a0, a1, h3, hrest⟩ := sixBody_apart hcp hr
  obtain ⟨S1, -, -, hi1, L1⟩ := ihb goal region g0 g1 x1 K hK h hg hD hj ha (hm _) (by omega) hcl h1
  have R1 := runX_keeps xb h.drop hg (by omega) h1
  have F1 := runX_frameP xb hn h hj ha (by omega) h1
  have b1 := R1.keeps.bo
  obtain ⟨S2, -, -, hi2, L2⟩ := iha goal region g1 g2 x0 K (hK.mono b1) S1 (hg.mono R1.keeps.le) hD (hj.mono b1)
    ha (hm _) (by omega) hcl h2
  have R2 := runX_keeps xa S1.drop (hg.mono R1.keeps.le) (by omega) h2
  have F2 := runX_frameP xa hn S1 (hj.mono b1) ha (by omega) h2
  have b2 := R2.keeps.bo
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := R2.size; have := R1.size; simp only [lazyMax]; omega
  obtain ⟨S4, e4, l4, h4, L4⟩ := rawX_sixTail (K := K) xc' ihc (by omega) S2 hi2 (by omega) a0 a1
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩ (sip_sixGenL S2 a0 a1 hi2 (by omega)) h3 (hrest hbig)
  refine ⟨S4, e4, l4, h4, fun r hl => ?_⟩
  rcases L4 r hl with e | e
  · exact gLiveK_frame (h.below g0.bo) F1 hj (L2 r e)
  · exact L1 r ((liveK_frameP (S1.below g1.bo) F2 hi1).mp e)

end Raw
end SkaModel
end Formalization
