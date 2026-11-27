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

/-! ## A fork-free `%next`: `+fork-sure`, the branches, `+sect`, the tail -/

/-- **What the case `%6` under `%next` asks of the predicate `X`** beyond
`XOK`: it depends on the blocks only (`+sect` leaves the same blocks, not
the same map), and it holds after the three blocks of `+fork-sure` (two
fork blocks at `l`, `l + 1` that hop up with fresh registers to the join at
`l + 2`, whose parameters are the goal's need and which hops down to `t`). -/
class XSix (X : Map Blob → Prop) extends XOK X : Prop where
  ext : ∀ {bl bl' : Map Blob}, X bl → (∀ k, HoonMap.get bl' k = HoonMap.get bl k) → X bl'
  fork : ∀ {bl bl' : Map Blob} {l t R : Nat} {ned : Need} {a0 a1 : List Nat}, X bl →
    (∀ k b, HoonMap.get bl k = some b → k < l) →
    (∀ k b, HoonMap.get bl k = some b → ∀ j ∈ getJmps b.fin, j.there < l) →
    (∀ k b, HoonMap.get bl k = some b → BlobIn (· < R) b) →
    1 ≤ t → t < l → (∀ x ∈ flattenNeed ned, x < R) → (∀ x ∈ a0, R ≤ x) → (∀ x ∈ a1, R ≤ x) →
    (flattenNeed ned).Nodup → (∀ k, k < l → HoonMap.get bl' k = HoonMap.get bl k) →
    HoonMap.get bl' l = some ⟨[], [], Termin.hop ⟨a0.map some, l + 2⟩⟩ →
    HoonMap.get bl' (l + 1) = some ⟨[], [], Termin.hop ⟨a1.map some, l + 2⟩⟩ →
    HoonMap.get bl' (l + 2) = some ⟨flattenNeed ned, [], Termin.hop (jmp0 t)⟩ →
    (∀ k, l + 3 ≤ k → HoonMap.get bl' k = Option.none) → X bl'

instance : XSix (fun _ : Map Blob => True) where
  ext := fun _ _ => trivial
  fork := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial

theorem sip_sameBlocks {X : Map Blob → Prop} [XSix X] {g g' : Comp.Gen Map} (h : SIP X (upRk g.blocks) g.bo g)
    (hs : SameBlocks g g') : SIP X (upRk g'.blocks) g'.bo g' := by
  have E : ∀ k, HoonMap.get g'.blocks k = HoonMap.get g.blocks k := hs.2.2.2.2.2.2
  have R : upRk g'.blocks = upRk g.blocks := funext fun k => by unfold upRk; rw [E]
  have B : g'.bo = g.bo := hs.2.1
  rw [R, B]
  exact ⟨by rw [hs.2.2.2.1]; exact h.drop, by rw [B]; exact h.bo1,
    fun k b hb => by rw [B]; rw [E] at hb; exact h.lab k b hb,
    fun k b hb => by rw [hs.1]; rw [E] at hb; exact h.regs k b hb,
    fun o b hb => by rw [E] at hb; exact h.nd o b hb,
    fun o o' b b' r h1 h2 => by rw [E] at h1 h2; exact h.cr o o' b b' r h1 h2,
    fun k b hb => by rw [E] at hb; exact h.tr k b hb,
    fun k b hb => by rw [E] at hb; exact h.jr k b hb, by omega, h.rk, h.rlo, XSix.ext h.x E⟩

/-- At a fork block, then the join: a register live there and not in the
branch's copy of the need is live at the goal's continuation and not in
its need. -/
theorem liveK_fork {bl bl0 : Map Blob} {K : Nat → Nat → Prop} {o j t L : Nat} {sur s : Need} {r : Nat}
    (h0 : HoonMap.get bl o = some ⟨[], [], Termin.hop ⟨(flattenNeed s).map some, j⟩⟩)
    (hj : HoonMap.get bl j = some ⟨flattenNeed sur, [], Termin.hop (jmp0 t)⟩)
    (hd : DownBelowP bl0 L) (he : ∀ k, k < L → HoonMap.get bl k = HoonMap.get bl0 k) (ht : t < L)
    (h : LiveK bl K o r) (hn : ¬ NMem s r) : LiveK bl0 K t r ∧ ¬ NMem sur r := by
  obtain ⟨b, hb, hr⟩ := liveK_cases h
  rw [h0] at hb; cases hb
  rcases hr with ⟨-, hr⟩ | ⟨j', hj', hl, -⟩
  · simp only [OpsRF, defsOf, finRegs, jmpRegs] at hr
    rcases hr with hr | ⟨-, hr⟩
    · exact hr.elim
    · simp only [List.filterMap_map] at hr
      exact absurd ((mem_flatten s r).mp (by simpa using hr)) hn
  simp [getJmps] at hj'; subst hj'
  obtain ⟨b, hb, hr⟩ := liveK_cases hl
  rw [hj] at hb; cases hb
  rcases hr with ⟨-, hr⟩ | ⟨j'', hj'', hl', hnd⟩
  · simp [OpsRF, defsOf, finRegs, jmpRegs, jmp0] at hr
  simp [getJmps] at hj''; subst hj''
  refine ⟨(liveK_frameP hd he ht).mp hl', fun m => hnd ?_⟩
  exact mem_blockDefs.mpr (Or.inl ((mem_flatten sur r).mpr m))

/-- **`+fork-sure` keeps the invariant**, in the rank of the state after it
(the fork blocks hop up to the join), and defines only registers below the
old `re`. -/
theorem sip_forkSure {X : Map Blob → Prop} [XSix X] {sur : Sure S} {th : Jmp} {g0 gF : Comp.Gen Map}
    {s0 s1 : Sure S} (h : SIP X (upRk g0.blocks) g0.bo g0) (hn : NB g0.re sur.ned) (hd : Distinct sur.ned)
    (hf : ∀ y, Defd g0.blocks y → ¬ NMem sur.ned y) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hF : forkSure sur th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 2 } = some ((s0, s1), gF)) :
    SIP X (upRk gF.blocks) gF.bo gF ∧ ∀ r, Defd gF.blocks r → r < g0.re := by
  obtain ⟨-, -, -, -, -, -, -, hreg, hle, hbo, hdrop, -, -, hb0, hb1, hb2, hold⟩ := forkSure_spec hF h.drop
  have oth := forkSure_other hF h.drop
  have hnone : ∀ k, g0.bo + 3 ≤ k → HoonMap.get gF.blocks k = Option.none := fun k hk => by
    rw [oth k hk]; exact h.none (by omega)
  have cs : ∀ k b, HoonMap.get gF.blocks k = some b → (k < g0.bo ∧ HoonMap.get g0.blocks k = some b) ∨
      (k = g0.bo ∧ b = ⟨[], [], Termin.hop ⟨(flattenNeed s0.ned).map some, g0.bo + 2⟩⟩) ∨
      (k = g0.bo + 1 ∧ b = ⟨[], [], Termin.hop ⟨(flattenNeed s1.ned).map some, g0.bo + 2⟩⟩) ∨
      (k = g0.bo + 2 ∧ b = ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩) := by
    intro k b hb
    by_cases k0 : k < g0.bo
    · exact Or.inl ⟨k0, by rw [← hold k k0]; exact hb⟩
    by_cases e0 : k = g0.bo
    · subst e0; rw [hb0] at hb; exact Or.inr (Or.inl ⟨rfl, (Option.some.inj hb).symm⟩)
    by_cases e1 : k = g0.bo + 1
    · subst e1; rw [hb1] at hb; exact Or.inr (Or.inr (Or.inl ⟨rfl, (Option.some.inj hb).symm⟩))
    by_cases e2 : k = g0.bo + 2
    · subst e2; rw [hb2] at hb; exact Or.inr (Or.inr (Or.inr ⟨rfl, (Option.some.inj hb).symm⟩))
    rw [hnone k (by omega)] at hb; cases hb
  have hlo := h.lob
  have bF : gF.bo = g0.bo + 3 := hbo
  have rOld : ∀ k, k < g0.bo → upRk gF.blocks k = upRk g0.blocks k := fun k hk =>
    upRk_congr (by rw [hold k hk])
  have r0 : upRk gF.blocks g0.bo = 3 * (g0.bo + 2) + 1 := by
    unfold upRk; rw [hb0]; simp [show g0.bo < g0.bo + 2 by omega]
  have r1 : upRk gF.blocks (g0.bo + 1) = 3 * (g0.bo + 2) + 1 := by
    unfold upRk; rw [hb1]; simp [show g0.bo + 1 < g0.bo + 2 by omega]
  have r2 : upRk gF.blocks (g0.bo + 2) = 3 * (g0.bo + 2) := by
    unfold upRk; rw [hb2]; simp [jmp0, show ¬ (g0.bo + 2 < th.there) by omega]
  have rHi : ∀ k, g0.bo + 3 ≤ k → upRk gF.blocks k = 3 * k := fun k hk => by unfold upRk; rw [hnone k hk]
  have D : ∀ r, Defd gF.blocks r → r < g0.re := fun r d => by
    obtain ⟨k, bb, hb, m⟩ := defd_iff.mp d
    rcases cs k bb hb with ⟨-, hb'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact h.defd_lt (defd_iff.mpr ⟨k, bb, hb', m⟩)
    · simp [blockDefs] at m
    · simp [blockDefs] at m
    · simp only [blockDefs, List.filterMap_nil, List.append_nil] at m
      exact hn r ((mem_flatten _ r).mp m)
  refine ⟨⟨by rw [hdrop]; exact h.drop, by omega, fun k b hb => ?_, fun k b hb => ?_, fun o b hb => ?_,
    fun o o' b b' r e1 e2 ne m1 => ?_, fun k b hb => ?_, fun k b hb j hj => ?_, Nat.le_refl _,
    fun k hk => rHi k (by omega), fun x hx => ?_, ?_⟩, D⟩
  · rcases cs k b hb with ⟨k0, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  · rcases cs k b hb with ⟨-, hb'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (h.regs k b hb').mono fun x hx => Nat.lt_of_lt_of_le hx hle
    · exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => (hreg x (Or.inl hx)).2)
    · exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => (hreg x (Or.inr hx)).2)
    · exact ⟨fun x hx => Nat.lt_of_lt_of_le (hn x ((mem_flatten _ x).mp hx)) hle, RegsIn.nil _, jmpIn_jmp0 _ _⟩
  · rcases cs o b hb with ⟨-, hb'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact h.nd o b hb'
    · simp [blockDefs]
    · simp [blockDefs]
    · simpa [blockDefs] using flatten_nodup hd
  · intro m2
    rcases cs o b e1 with ⟨k0, hb'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases cs o' b' e2 with ⟨k0', hb''⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (try simp only [blockDefs, List.filterMap_nil, List.append_nil, List.not_mem_nil] at m1 m2) <;>
      first
      | exact h.cr o o' b b' r hb' hb'' ne m1 m2
      | exact hf r (defd_iff.mpr ⟨o, b, hb', m1⟩) ((mem_flatten _ r).mp m2)
      | exact hf r (defd_iff.mpr ⟨o', b', hb'', m2⟩) ((mem_flatten _ r).mp m1)
      | exact ne rfl
      | omega
  · rcases cs k b hb with ⟨-, hb'⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact h.tr k b hb'
    all_goals intro op hop; simp at hop
  · rcases cs k b hb with ⟨k0, hb'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have a := h.jr k b hb' j hj
      have b0 := h.rlo k k0
      have jt : j.there < g0.bo := by
        rcases Nat.lt_or_ge j.there g0.bo with e | e
        · exact e
        · have := h.rk j.there e
          omega
      rw [rOld k k0, rOld _ jt]; exact a
    · simp [getJmps] at hj; subst hj; dsimp only; rw [r0, r2]; omega
    · simp [getJmps] at hj; subst hj; dsimp only; rw [r1, r2]; omega
    · simp [getJmps] at hj; subst hj; simp only [jmp0]; rw [r2, rOld _ h2]; have := h.rlo _ h2; omega
  · by_cases k0 : x < g0.bo
    · rw [rOld x k0]; have := h.rlo x k0; omega
    · have : x = g0.bo ∨ x = g0.bo + 1 ∨ x = g0.bo + 2 := by omega
      rcases this with rfl | rfl | rfl
      · rw [r0]; omega
      · rw [r1]; omega
      · rw [r2]; omega
  · exact XSix.fork (l := g0.bo) (t := th.there) (R := g0.re) (ned := sur.ned) h.x h.lab (fun k b hb j hj => h.jlt hb hj) h.regs h1 h2
      (fun x hx => hn x ((mem_flatten _ x).mp hx)) (fun x hx => (hreg x (Or.inl ((mem_flatten _ x).mp hx))).1)
      (fun x hx => (hreg x (Or.inr ((mem_flatten _ x).mp hx))).1) (flatten_nodup hd) hold hb0 hb1 hb2 hnone

/-- **`%6` for a fork-free `%next`**: `+fork-sure`, `b` for the copy `s1`
into the fork block `o1`, `a` for `s0` into `o0`, `+sect` (the same blocks
as `sixGenL`, `sect_spec`), the tail.  A register live at a fork block and
not in its copy is live past the join at the goal's continuation and not in
the goal's need (`liveK_fork`). -/
theorem rawX_sixN {X : Map Blob → Prop} [XSix X] {c a b : Nomm} (xc' : FragX (S := S) c)
    (xa : FragX (S := S) a) (xb : FragX (S := S) b)
    (ihc : RawIHX S Map X c) (iha : RawIHX S Map X a) (ihb : RawIHX S Map X b)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Comp.Gen Map} {nex : NextL S}
    {K : Nat → Nat → Prop} (hK : KVan K g0.bo) (h : SIP X (upRk g0.blocks) g0.bo g0)
    (hg : GoalIn g0.re (CGoal.next sur th : CGoal S)) (hD : Distinct sur.ned)
    (hj : GJ g0.bo (CGoal.next sur th : CGoal S)) (hf : ∀ r, Defd g0.blocks r → ¬ NMem sur.ned r)
    (hcl : Clean sur.ned) (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (hr : runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g9)) :
    SIP X (upRk g9.blocks) g9.bo g9 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g9.bo ∧
      ∀ r, LiveK g9.blocks (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
        LiveK g0.blocks K th.there r ∧ ¬ NMem sur.ned r := by
  have hcp := fragX_pure xc'
  simp only [CGoal.toL] at hr
  rw [runL_n6_next, sixNextL_ofSure] at hr
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp hr
  obtain ⟨-, -, c0, c1, d0, d1, j01, hreg, -, hbo, -, -, -, hb0, hb1, hb2, hold⟩ :=
    forkSure_spec (sur := sur) hF h.drop
  obtain ⟨SF, dF⟩ := sip_forkSure h hg.1 hD hf hj.1 hj.2 hF
  have SF' : SIP X (upRk ({ gF with id := gF.id + 1 } : Comp.Gen Map).blocks)
      ({ gF with id := gF.id + 1 } : Comp.Gen Map).bo { gF with id := gF.id + 1 } :=
    ⟨SF.drop, SF.bo1, SF.lab, SF.regs, SF.nd, SF.cr, SF.tr, SF.jr, SF.lob, SF.rk, SF.rlo, SF.x⟩
  have b0 := h.bo1
  have bF : gF.bo = g0.bo + 3 := hbo
  have cl1 : Clean s1.ned := c1.clean hcl
  have cl0 : Clean s0.ned := c0.clean hcl
  -- the branch `b`
  have gb : GoalIn gF.re (CGoal.next s1 (jmp0 (g0.bo + 1)) : CGoal S) :=
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩
  have jb : GJ gF.bo (CGoal.next s1 (jmp0 (g0.bo + 1)) : CGoal S) := ⟨by simp [jmp0], by simp [jmp0]; omega⟩
  obtain ⟨SR, -, -, hiR, LR⟩ := ihb (CGoal.next s1 (jmp0 (g0.bo + 1))) (gF.id :: region) ({ gF with id := gF.id + 1 } : Comp.Gen Map) gR x1 K
    (hK.mono (show g0.bo ≤ gF.bo by omega)) SF' gb d1 jb rfl
    (fun r d m => by have := dF r d; have := (hreg r (Or.inr m)).1; omega) (by omega) cl1 hR
  have Rb := runX_keeps xb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) SF'.drop gb (by omega) hR
  have Fb := runX_frameN xb SF' jb rfl d1 gb.1 cl1 (by omega) hR
  have Ftb := runX_foot xb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) SF'.drop gb d1 (by omega) hR
  have lR : gF.re ≤ gR.re := Rb.keeps.le
  have bR : gF.bo ≤ gR.bo := Rb.keeps.bo
  -- the branch `a`
  have ga : GoalIn gR.re (CGoal.next s0 (jmp0 g0.bo) : CGoal S) :=
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩
  have ja : GJ gR.bo (CGoal.next s0 (jmp0 g0.bo) : CGoal S) := ⟨by simp [jmp0]; omega, by simp [jmp0]; omega⟩
  obtain ⟨SQ, -, -, hiQ, LQ⟩ := iha (CGoal.next s0 (jmp0 g0.bo)) (gF.id :: region) gR gQ x0 K
    (hK.mono (by omega)) SR ga d0 ja rfl (fun r d m => by
      rcases defd_of_wroteIn Ftb.wr d with d | ⟨-, e, -⟩
      · have := dF r d; have := (hreg r (Or.inl m)).1; omega
      · rcases e with e | e
        · have := (hreg r (Or.inl m)).2; simp only at e; omega
        · exact j01 r m e) (by omega) cl0 hQ
  have Ra := runX_keeps xa (goal := CGoal.next s0 (jmp0 g0.bo)) SR.drop ga (by omega) hQ
  have Fa := runX_frameN xa SR ja rfl d0 ga.1 cl0 (by omega) hQ
  -- `+sect`
  have cR : gR.cond = gF.cond := Rb.cnd
  rw [cR] at hS
  obtain ⟨ey, en, a0, a1, el, hsb⟩ := sect_spec SQ.drop (Ra.cnd.trans cR) hS
  subst ey en el
  have bQ : gR.bo ≤ gQ.bo := Ra.keeps.bo
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  obtain ⟨S9, e9, l9, h9, L9⟩ := rawX_sixTail (K := K) xc' ihc (by omega) SQ hiQ (by omega) a0 a1 hsb
    (sip_sameBlocks (sip_sixGenL SQ a0 a1 hiQ (by omega)) hsb) hC (hrest hbig)
  refine ⟨S9, e9, l9, h9, fun r hl => ?_⟩
  rcases L9 r hl with e | e
  · obtain ⟨e1, n0⟩ := LQ r e
    have e2 := (liveK_frameP (SF'.below _) Fb (show g0.bo < gF.bo by omega)).mp e1
    exact liveK_fork hb0 hb2 (h.below g0.bo) hold hj.2 e2 n0
  · have e1 := (liveK_frameP (SR.below gR.bo) Fa hiR).mp e
    obtain ⟨e2, n1⟩ := LR r e1
    exact liveK_fork hb1 hb2 (h.below g0.bo) hold hj.2 e2 n1

/-- **The case `six` of `RawIHX`.** -/
theorem rawX_six {X : Map Blob → Prop} [XSix X] {c a b : Nomm} (xc' : FragX (S := S) c)
    (xa : FragX (S := S) a) (xb : FragX (S := S) b)
    (ihc : RawIHX S Map X c) (iha : RawIHX S Map X a) (ihb : RawIHX S Map X b) :
    RawIHX S Map X (Nomm.n6 c a b) := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hf hc hcl hr
  have hc' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th => exact rawX_sixN xc' xa xb ihc iha ihb hK h hg hD hj (fun r d m => hf r d m) hcl hc' hr
  | done => exact rawX_sixP xc' xa xb ihc iha ihb (goal := CGoal.done) trivial hK h hg hj ha hc' hr
  | pick z o => exact rawX_sixP xc' xa xb ihc iha ihb (goal := CGoal.pick z o) trivial hK h hg hj ha hc' hr

/-! ## The induction -/

/-- **`RawIHX` on `FragX`**, for every predicate `X` of the blocks that the
steps keep (`XSix`). -/
theorem runX_rawIHX {X : Map Blob → Prop} [XSix X] {nm : Nomm} (hf : FragX (S := S) nm) :
    RawIHX S Map X nm := by
  induction hf with
  | frag hf => exact rawX_frag hf
  | six xc xa xb ihc iha ihb => exact rawX_six xc xa xb ihc iha ihb
  | four _ ih => exact rawX_four ih
  | three _ ih => exact rawX_three ih
  | seven hq _ ih => exact rawX_seven hq ih
  | cons xp xq ihp ihq => exact rawX_cons xp xq ihp ihq
  | five xp xq ihp ihq => exact rawX_five xp xq ihp ihq
  | ten xv xq ihv ihq => exact rawX_ten _ xv xq ihv ihq
  | sevenFrom ha _ ihq => exact rawX_sevenFrom ha ihq

end Raw
end SkaModel
end Formalization
