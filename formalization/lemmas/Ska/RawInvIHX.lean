import lemmas.Ska.RawInvFragX
import lemmas.Ska.RawInvTopX
import lemmas.Ska.CompFragX
import lemmas.Ska.CompSevenN
import lemmas.Ska.CompSevenSame

/-!
# Raw `+comp` output on `FragX`: the run-level invariant

README Gaps 14, track D, step 2 of the class `FragX` (a `%6` anywhere, no
calls).  The run-level invariant over `runL`, stated for the fork-free
goals `CGoal.toL goal` that the cases of `FragX` give their sub-runs.

* `lazK o laz`: the kills of a lazy need entered at `o`: each entry of the
  lazy tree (`(o, laz) :: entries laz`) first defines the registers of its
  sure need.  What `optIn_toStraight_prep` asks to be live at nothing.
* **`RawIHX X nm`**: every run of `runL nm` for a fork-free goal from a
  state with `SIP X (upRk g0.blocks) g0.bo` (blocks that hop up as `%6`
  makes them), when `nm` has at most 255 `%6` (as every theorem of track C
  on `FragX` asks), keeps that invariant in the end state's rank, returns a
  jump with no arguments to a label from `1` below the end's `bo`, and for every
  `K` that vanishes from `g0.bo` on leaves live at its entry, with the
  kills `K` and those of its result's lazy tree, only what its goal's
  continuation needs beyond the goal with the kills `K` (`GLiveK`).  Under
  `%done` nothing is live there, the hypothesis `hl` of
  `optIn_toStraight_prep`.
* The cases, whole cases of `FragX` at a time: `rawX_frag` (`run_rawUK`
  and `runL_frag`), `rawX_sevenFrom`, `rawX_seven`, `rawX_four`,
  `rawX_three`; cons, `%5` and `%10` are in `RawInvIHXBin.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X]

/-- **The kills of a lazy need entered at `o`**: each entry of its lazy
tree first defines the registers of its sure need. -/
def lazK (o : Nat) (laz : Lazy S) (x r : Nat) : Prop :=
  ∃ e ∈ (o, laz) :: entries laz, e.1 = x ∧ NMem e.2.sure.ned r

theorem lazK_ofSure {o : Nat} {s : Sure S} {x r : Nat} : lazK o (ofSure s) x r ↔ x = o ∧ NMem s.ned r := by
  unfold lazK
  rw [entries_ofSure]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    rw [List.mem_singleton] at he
    subst he
    exact ⟨h1.symm, h2⟩
  · rintro ⟨rfl, h2⟩
    exact ⟨_, List.mem_singleton_self _, rfl, h2⟩

/-- **The run-level invariant on `FragX`.** -/
def RawIHX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (X : Map Blob → Prop)
    (nm : Nomm) : Prop :=
  ∀ (goal : CGoal S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S) (K : Nat → Nat → Prop),
    KVan K g0.bo → SIP X (upRk g0.blocks) g0.bo g0 → GoalIn g0.re goal → GDist goal → GJ g0.bo goal →
    GArgs goal → (∀ r, Defd g0.blocks r → ¬ GMem goal r) → sixCount nm ≤ 255 → GClean goal →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) →
    SIP X (upRk g1.blocks) g1.bo g1 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g1.bo ∧
      ∀ r, LiveK g1.blocks (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
        GLiveK g0.blocks K goal r

/-- **The case `frag`**: a nomm of the first fragment, by `run_rawUK`. -/
theorem rawX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : RawIHX S Map X nm := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hfd _ _ hr
  rw [runL_frag (hf goal) region g0] at hr
  obtain ⟨⟨nex', g1'⟩, hr', e⟩ := Option.map_eq_some_iff.mp hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨S1, L1⟩ := run_rawUK (K := K) h hg hD hj ha hfd hr'
  obtain ⟨-, -, -, -, -, -, a1, lo1, hi1⟩ := sub_facts h hg hD hj ha hr'
  refine ⟨S1, a1, lo1, hi1, fun r hl => ?_⟩
  have hnk := hl.nk
  simp only [Next.toL] at hl hnk
  rcases L1 r (hl.mono fun x y h => Or.inl h) with e | e
  · exact absurd (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩)) hnk
  · exact e

/-! ## `[7 [0 axe] q]` -/

/-- `+from-sure` keeps every register of the need. -/
theorem fromSure_nmem {axe : Nat} {s s' : Sure S} (h : fromSure axe s = some s') {r : Nat}
    (hr : NMem s.ned r) : NMem s'.ned r := by
  unfold fromSure at h
  split at h
  · cases h
  split at h
  · rename_i hn
    rw [hn] at hr; exact hr.elim
  · simp only [Option.some.injEq] at h
    subst h
    exact nmem_fromPath_of _ axe r hr

/-- **`+from` keeps the kills**: each entry of the old lazy tree is one of
the new tree at the same label, whose sure need has the old one's
registers. -/
theorem lazK_fromL {axe : Nat} {l l' : Lazy S} (h : fromL axe l = some l') {o x r : Nat}
    (hk : lazK o l x r) : lazK o l' x r := by
  obtain ⟨e, he, rfl, hr⟩ := hk
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨(o, l'), List.mem_cons_self, rfl, fromSure_nmem (fromL_sure h) hr⟩
  · obtain ⟨l1, h1, h2⟩ := (fromL_ent axe l l' h).mem_left he
    exact ⟨(e.1, l1), List.mem_cons_of_mem _ h2, rfl, fromSure_nmem (fromL_sure h1) hr⟩

/-- **The case `sevenFrom`**: `q`, then `+from` on its lazy need, which
emits nothing and keeps the kills. -/
theorem rawX_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : RawIHX S Map X q) :
    RawIHX S Map X (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region g0 g1 nex K hK h hg hD hj hA hfd hc hcl hr
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha hr
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := ihq goal region g0 g1 nx K hK h hg hD hj hA hfd
    (by simpa only [sixCount, Nat.zero_add] using hc) hcl h1
  exact ⟨S1, a1, lo1, hi1, fun r hlv => L1 r (hlv.mono fun x y e => e.imp id (lazK_fromL hl))⟩

/-! ## `[7 p q]` with `q` in the first fragment -/

theorem KVan.mono {K : Nat → Nat → Prop} {lo lo' : Nat} (h : KVan K lo) (hl : lo ≤ lo') : KVan K lo' :=
  ⟨fun k r hk => h.van k r (Nat.le_trans hl hk)⟩

/-- **The case `seven`**: `q` of the first fragment (`run_rawUK`), then `p`
for its fork-free result. -/
theorem rawX_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : RawIHX S Map X p) :
    RawIHX S Map X (Nomm.n7 p q) := by
  intro goal region g0 g1 nex K hK h hg hD hj hA hfd hc hcl hr
  rw [runL_n7] at hr
  obtain ⟨nq', g2, h2, hr⟩ := bind_some hr
  rw [runL_frag (hq goal) region g0] at h2
  obtain ⟨⟨nq, g2'⟩, hq2, e⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨S2, L2⟩ := run_rawUK (K := K) h hg hD hj hA hfd hq2
  obtain ⟨-, b2, nb2, d2, s2, dd2, a2, lo2, hi2⟩ := sub_facts h hg hD hj hA hq2
  rw [Next.goal_toL] at hr
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := ihp nq.goal region _ g1 nex K (hK.mono b2) S2
    ⟨nb2, fun x hx => by rw [a2] at hx; cases hx⟩ d2 ⟨lo2, hi2⟩ a2 (defd_next h hfd s2 dd2)
    (by simp only [sixCount] at hc; omega) (run_clean q goal g0 _ nq hcl hq2) hr
  refine ⟨S1, a1, lo1, hi1, fun r hl => ?_⟩
  obtain ⟨hl', hn⟩ := L1 r hl
  rcases L2 r hl' with e | e
  · exact absurd e hn
  · exact e

/-! ## Re-ranking a state after steps that keep the old terminators -/

/-- The blocks of `g0` keep their terminators in `g`. -/
def FinKeep (g0 g : Comp.Gen Map) : Prop :=
  ∀ k, k < g0.bo → (HoonMap.get g.blocks k).map Blob.fin = (HoonMap.get g0.blocks k).map Blob.fin

theorem FinKeep.refl (g : Comp.Gen Map) : FinKeep g g := fun _ _ => rfl

theorem FinKeep.trans {g0 g1 g2 : Comp.Gen Map} (a : FinKeep g0 g1) (b : FinKeep g1 g2) (hb : g0.bo ≤ g1.bo) :
    FinKeep g0 g2 := fun k hk => (b k (by omega)).trans (a k hk)

theorem finKeep_of_grow {g g' : Comp.Gen Map} (G : Grow g g') : FinKeep g g' := fun k hk => by
  cases e0 : HoonMap.get g.blocks k with
  | none =>
    cases e1 : HoonMap.get g'.blocks k with
    | none => rfl
    | some b' =>
      rcases G.new k b' e1 with ⟨b, e, -, -⟩ | ⟨hlo, -, -⟩
      · rw [e0] at e; cases e
      · omega
  | some b =>
    obtain ⟨b', h', -, hf⟩ := G.keep k b hk e0
    rw [h']; simp [hf]

theorem finKeep_blocks {g g' : Comp.Gen Map} (e : g'.blocks = g.blocks) : FinKeep g g' := fun k _ => by rw [e]

theorem finKeep_put {g g' : Comp.Gen Map} {b : Blob} (e : g'.blocks = HoonMap.put g.blocks g.bo b) :
    FinKeep g g' := fun k hk => by rw [e, get_put_ne (by omega)]

/-- **A state with the invariant in the rank of an older state's blocks has
it in its own rank**, when the old blocks keep their terminators. -/
theorem sip_reRank {g0 g : Comp.Gen Map} (h : SIP X (upRk g0.blocks) g0.bo g)
    (hn : ∀ k, g0.bo ≤ k → HoonMap.get g0.blocks k = Option.none) (F : FinKeep g0 g) :
    SIP X (upRk g.blocks) g.bo g := by
  have E : ∀ k, upRk g.blocks k = upRk g0.blocks k := by
    intro k
    by_cases hk : k < g0.bo
    · exact upRk_congr (F k hk)
    · have n0 := hn k (Nat.le_of_not_lt hk)
      have r0 : upRk g0.blocks k = 3 * k := by unfold upRk; rw [n0]
      rw [r0]
      unfold upRk
      cases e1 : HoonMap.get g.blocks k with
      | none => rfl
      | some b =>
        obtain ⟨p, bd, f⟩ := b
        cases f with
        | hop j =>
          simp only
          split
          · rename_i hlt
            have := h.jr k _ e1 j (by simp [getJmps])
            rw [h.rk k (by omega), h.rk j.there (by omega)] at this
            omega
          · rfl
        | _ => rfl
  have hlo := h.lob
  refine ⟨h.drop, h.bo1, h.lab, h.regs, h.nd, h.cr, h.tr, fun k b hb j hj => by
      rw [E, E]; exact h.jr k b hb j hj, Nat.le_refl _, fun k hk => ?_, fun x hx => ?_, h.x⟩
  · rw [E]; exact h.rk k (by omega)
  · rw [E]
    by_cases e : x < g0.bo
    · have := h.rlo x e; omega
    · rw [h.rk x (by omega)]; omega

/-! ## A block, then the run of an operand of `FragX` -/

/-- **A block, then the run of an operand of `FragX` for a fresh register
`x`**: what is live at the run's entry, with the kills of the operand's
lazy tree, is live at the block and not `x`. -/
theorem rawX_tail {p : Nomm} (ihp : RawIHX S Map X p) {g0 g g1 g2 : Comp.Gen Map} {b : Blob} {x o : Nat}
    {nex : NextL S} {region : List Nat} {K : Nat → Nat → Prop} (hK : KVan K g0.bo)
    (h : SIP X (upRk g0.blocks) g0.bo g) (hn : ∀ k, g0.bo ≤ k → HoonMap.get g0.blocks k = Option.none)
    (F : FinKeep g0 g) (E : EmitOK g b) (hx : x < g.re) (hnx : ¬ Defd g.blocks x) (hxb : x ∉ blockDefs b)
    (hc : sixCount p ≤ 255) (he : (emit b : CM Map Nat) g = some (o, g1))
    (hr : runL p (CGoalL.next (ofSure (lazyReg x)) (jmp0 o)) region g1 = some (nex, g2)) :
    SIP X (upRk g2.blocks) g2.bo g2 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g2.bo ∧
      ∀ y, LiveK g2.blocks (fun a c => K a c ∨ lazK nex.th.there nex.laz a c) nex.th.there y →
        (BlockRF b y ∨ ∃ j ∈ getJmps b.fin, LiveK g.blocks K j.there y ∧ y ∉ blockDefs b) ∧ y ≠ x := by
  obtain ⟨S1, rfl, e1, q1, bo1⟩ := sip_emit h E he
  have hl := h.none (Nat.le_refl g.bo)
  have hlo := h.lob
  have S1' := sip_reRank S1 hn (F.trans (finKeep_put e1) hlo)
  obtain ⟨S2, a2, lo2, hi2, L2⟩ := ihp (CGoal.next (lazyReg x) (jmp0 g.bo)) region g1 g2 nex K (hK.mono (by omega)) S1'
    ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ trivial
    ⟨by simp [jmp0]; have := h.bo1; omega, by simp [jmp0]; omega⟩ rfl
    (fun r d hm => by
      simp only [GMem, lazyReg, NMem] at hm; subst hm
      rw [e1, defd_put hl] at d
      rcases d with d | d
      · exact hnx d
      · exact hxb d) hc trivial hr
  refine ⟨S2, a2, lo2, hi2, fun y hy => ?_⟩
  obtain ⟨hl', hn'⟩ := L2 y hy
  have he' : ∀ k, k < g.bo → HoonMap.get g1.blocks k = HoonMap.get g.blocks k := fun k hk => by
    rw [e1, get_put_ne (by omega)]
  exact ⟨liveK_unfoldP (by rw [e1]; exact get_put_self) (h.below g.bo) he' E.jd hl',
    fun e => hn' (by simp [lazyReg, NMem, e])⟩

/-! ## `%4` -/

/-- **The case `four`**: the block of `%4` (after the collapse of the goal's
need under `%next`), then the run of the operand, as `raw_n4`. -/
theorem rawX_four {p : Nomm} (ihp : RawIHX S Map X p) : RawIHX S Map X (Nomm.n4 p) := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hf hc _ hr
  simp only [sixCount] at hc
  have hn : ∀ k, g0.bo ≤ k → HoonMap.get g0.blocks k = Option.none := fun k hk => h.none hk
  cases goal with
  | done =>
    simp only [CGoal.toL] at hr
    unfold runL at hr
    obtain ⟨pro, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
    obtain ⟨arg, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
    obtain ⟨o, g4, h4, hr⟩ := bind_some hr
    have nd : ∀ x, g0.re ≤ x → ¬ Defd g3.blocks x := fun x hx d => by
      rw [b3, b2] at d; have := h.defd_lt d; omega
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_tail ihp hK S3 hn (finKeep_blocks (by rw [b3, b2]))
      (emitOK_one S3 rfl (fun x hx => by simp [Comp.poleRegs] at hx; omega)
      (nd _ (Nat.le_refl _)) rfl (fun j hj => by simp [getJmps] at hj) (fun j hj => by simp [getJmps] at hj)
      (by simp [FinIn]; omega)) (by omega) (nd _ (by omega)) (by rw [blockDefs_inc]; omega) hc h4 hr
    refine ⟨S1, a1, lo1, hi1, fun y hy => ?_⟩
    rcases L1 y hy with ⟨e | ⟨j, hj', -⟩, hne⟩
    · exact absurd (blockRF_inc (fun x hx => by simpa [finRegs] using hx) e) hne
    · simp [getJmps] at hj'
  | pick z o =>
    simp only [GJ] at hj
    simp only [CGoal.toL] at hr
    unfold runL at hr
    obtain ⟨pro, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
    obtain ⟨arg, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
    obtain ⟨o', g4, h4, hr⟩ := bind_some hr
    have nd : ∀ x, g0.re ≤ x → ¬ Defd g3.blocks x := fun x hx d => by
      rw [b3, b2] at d; have := h.defd_lt d; omega
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_tail ihp hK S3 hn (finKeep_blocks (by rw [b3, b2]))
      (emitOK_one S3 rfl (fun x hx => by simp [Comp.poleRegs] at hx; omega)
      (nd _ (Nat.le_refl _)) rfl
      (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl; exact ha.1; exact ha.2)
      (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> omega)
      (by simp [FinIn, JmpIn, ha.1, ha.2]; omega)) (by omega) (nd _ (by omega)) (by rw [blockDefs_inc]; omega) hc h4 hr
    refine ⟨S1, a1, lo1, hi1, fun y hy => ?_⟩
    rcases L1 y hy with ⟨e | ⟨j, hj', hl, -⟩, hne⟩
    · exact absurd (blockRF_inc (fun x hx => by simpa [finRegs, jmpRegs, ha.1, ha.2] using hx) e) hne
    · rw [b3, b2] at hl
      simp [getJmps] at hj'
      rcases hj' with rfl | rfl
      · exact Or.inl hl
      · exact Or.inr hl
  | next laz th =>
    have hjt : th.there < g0.bo := hj.2
    simp only [CGoal.toL] at hr
    rw [runL_n4_next] at hr
    obtain ⟨a, g2, h2, hr⟩ := bind_some hr
    have h2' : collapseLazyAtom ⟨laz, th⟩ g0 = some (a, g2) := by
      rw [← collapseLazyAtomL_toL]; exact h2
    obtain ⟨S2, l2, bo2, ha2, fr2, cn, cs⟩ := raw_collapse (K := K) h hg.1 hj.2 (fun y hy d => hf y d hy) h2'
    have F2 : FinKeep g0 g2 := finKeep_of_grow (collapse_down h2' hj.1 hj.2 h.bo1).1
    obtain ⟨⟨pro, th'⟩, g3, h3, hr⟩ := bind_some hr
    have P : SIP X (upRk g0.blocks) g0.bo g3 ∧ g2.re ≤ g3.re ∧ pro < g3.re ∧ ¬ Defd g3.blocks pro ∧ th' < g3.bo ∧
        g3.blocks = g2.blocks ∧ g3.bo = g2.bo ∧
        ∀ y, LiveK g3.blocks K th' y → y = pro ∨ (LiveK g0.blocks K th.there y ∧ ¬ NMem laz.ned y) := by
      cases a with
      | some x =>
        simp only [collPick, pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        obtain ⟨-, rl, nd, tl, -, lv⟩ := cs pro th' rfl
        exact ⟨S2, Nat.le_refl _, rl, nd, tl, rfl, rfl, lv⟩
      | none =>
        obtain ⟨hn0, rfl⟩ := cn rfl
        simp only [collPick] at h3
        obtain ⟨r, g4, h4, h3⟩ := bind_some h3
        obtain ⟨S4, rfl, q4, b4, o4⟩ := sip_re S2 h4
        rw [if_pos ha2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
        refine ⟨S4, by omega, by omega, fun d => by rw [b4] at d; have := h.defd_lt d; omega, by omega, b4, o4,
          fun y hl => Or.inr ⟨by rw [b4] at hl; exact hl, by rw [hn0]; exact id⟩⟩
    obtain ⟨S3, l3, prl, pnd, tl, b3, o3', lv3⟩ := P
    obtain ⟨arg, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S4, rfl, q4, b4, o4⟩ := sip_re S3 h4
    obtain ⟨o, g5, h5, hr⟩ := bind_some hr
    have F4 : FinKeep g0 g4 := F2.trans (finKeep_blocks (by rw [b4, b3])) bo2
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_tail ihp hK S4 hn F4 (emitOK_one S4 rfl (fun x hx => by simp [Comp.poleRegs] at hx; omega)
      (by rw [b4]; exact pnd) rfl (fun j hj' => by simp [getJmps] at hj'; rw [hj']; rfl)
      (fun j hj' => by simp [getJmps] at hj'; rw [hj']; simp [jmp0]; omega) (by simp [FinIn, JmpIn, jmp0]))
      (by omega) (fun d => by rw [b4] at d; have := S3.defd_lt d; omega) (by rw [blockDefs_inc]; omega) hc h5 hr
    refine ⟨S1, a1, lo1, hi1, fun y hy => ?_⟩
    rcases L1 y hy with ⟨e | ⟨j, hj', hl, hn'⟩, hne⟩
    · exact absurd (blockRF_inc (fun x hx => by simp [finRegs, jmpRegs, jmp0] at hx) e) hne
    · simp [getJmps] at hj'; subst hj'
      rw [b4] at hl
      rcases lv3 y hl with e | e
      · exact absurd e (fun e' => hn' (by rw [blockDefs_inc]; exact e'))
      · exact e

/-! ## `%3` -/

theorem finKeep_of_eq {g g' : Comp.Gen Map} (fr : ∀ x, x < g.bo → HoonMap.get g'.blocks x = HoonMap.get g.blocks x) :
    FinKeep g g' := fun k hk => by rw [fr k hk]

/-- **The case `three`**: the test block of `%3` (after `+forl` under
`%next`), then the run of the operand, as `raw_n3`. -/
theorem rawX_three {p : Nomm} (ihp : RawIHX S Map X p) : RawIHX S Map X (Nomm.n3 p) := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hf hc hcl hr
  simp only [sixCount] at hc
  have hn : ∀ k, g0.bo ≤ k → HoonMap.get g0.blocks k = Option.none := fun k hk => h.none hk
  cases goal with
  | done =>
    simp only [CGoal.toL] at hr
    rw [runL_n3_done] at hr
    obtain ⟨⟨o0, o1⟩, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, l2, rfl, rfl, bo2, fr2, n0, n1, dd2⟩ := raw_doneBlocks (K := K) h h2
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
    obtain ⟨oc, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_tail ihp hK S3 hn ((finKeep_of_eq fr2).trans (finKeep_blocks b3) (by omega))
      (emitOK_clq (show g2.re < g3.re by omega) rfl rfl
      (show (jmp0 g0.bo).there < g3.bo by simp [jmp0]; omega) (show (jmp0 (g0.bo + 1)).there < g3.bo by simp [jmp0]; omega))
      (show g2.re < g3.re by omega) (fun d => by rw [b3] at d; have := S2.defd_lt d; omega)
      (by simp [blockDefs, defsOf]) hc h4 hr
    refine ⟨S1, a1, lo1, hi1, fun y hy => ?_⟩
    rcases L1 y hy with ⟨e | ⟨j, hj', hl, -⟩, hne⟩
    · exact absurd (blockRF_clq rfl rfl e) hne
    · rw [b3] at hl
      simp [getJmps] at hj'
      rcases hj' with rfl | rfl
      · exact absurd hl (n0 y)
      · exact absurd hl (n1 y)
  | pick z o =>
    simp only [GJ] at hj
    simp only [CGoal.toL] at hr
    rw [runL_n3_pick] at hr
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re h h3
    obtain ⟨oc, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_tail ihp hK S3 hn (finKeep_blocks b3) (emitOK_clq (by omega) ha.1 ha.2 (by omega) (by omega))
      (by omega) (fun d => by rw [b3] at d; have := h.defd_lt d; omega) (by simp [blockDefs, defsOf]) hc h4 hr
    refine ⟨S1, a1, lo1, hi1, fun y hy => ?_⟩
    rcases L1 y hy with ⟨e | ⟨j, hj', hl, -⟩, hne⟩
    · exact absurd (blockRF_clq ha.1 ha.2 e) hne
    · rw [b3] at hl
      simp [getJmps] at hj'
      rcases hj' with rfl | rfl
      · exact Or.inl hl
      · exact Or.inr hl
  | next laz th =>
    simp only [CGoal.toL] at hr
    rw [runL_n3_next, noneEquivalentL_ofSure] at hr
    by_cases hne : noneEquivalent laz = true
    · rw [if_pos hne] at hr
      exact ihp (CGoal.next laz th) region g0 g1 nex K hK h hg hD hj ha hf hc hcl hr
    rw [if_neg hne] at hr
    obtain ⟨a, g2, h2, hr⟩ := bind_some hr
    have h2' : collapseLazyAtom ⟨laz, th⟩ g0 = some (a, g2) := by
      rw [← collapseLazyAtomL_toL]; exact h2
    obtain ⟨S2, l2, bo2, ha2, fr2, cn, cs⟩ := raw_collapse (K := K) h hg.1 hj.2 (fun y hy d => hf y d hy) h2'
    have F2 : FinKeep g0 g2 := finKeep_of_grow (collapse_down h2' hj.1 hj.2 h.bo1).1
    cases a with
    | none => cases hr
    | some x =>
      obtain ⟨r, o⟩ := x
      obtain ⟨-, rl, nd, tl, -, lv⟩ := cs r o rfl
      simp only at hr
      obtain ⟨⟨z, o'⟩, g3, h3, hr⟩ := bind_some hr
      obtain ⟨S3, q3, bo3, rfl, rfl, fr3, lz, lo', -⟩ := raw_forl (K := K) S2 rl nd tl h3
      obtain ⟨r', g4, h4, hr⟩ := bind_some hr
      obtain ⟨S4, rfl, q4, b4, o4⟩ := sip_re S3 h4
      obtain ⟨oc, g5, h5, hr⟩ := bind_some hr
      have F4 : FinKeep g0 g4 := (F2.trans (finKeep_of_eq fr3) bo2).trans (finKeep_blocks b4) (by omega)
      obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_tail ihp hK S4 hn F4 (emitOK_clq (by omega) rfl rfl (by simp [jmp0]; omega)
        (by simp [jmp0]; omega)) (by omega) (fun d => by rw [b4] at d; have := S3.defd_lt d; omega)
        (by simp [blockDefs, defsOf]) hc h5 hr
      refine ⟨S1, a1, lo1, hi1, fun y hy => ?_⟩
      rcases L1 y hy with ⟨e | ⟨j, hj', hl, -⟩, hne'⟩
      · exact absurd (blockRF_clq rfl rfl e) hne'
      · rw [b4] at hl
        simp [getJmps] at hj'
        have hl' : y ≠ r ∧ LiveK g2.blocks K o y := by
          rcases hj' with rfl | rfl
          · exact lz y hl
          · exact lo' y hl
        rcases lv y hl'.2 with e | e
        · exact absurd e hl'.1
        · exact e

end Raw
end SkaModel
end Formalization
