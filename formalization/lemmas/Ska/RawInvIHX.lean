import lemmas.Ska.RawInvFragX
import lemmas.Ska.RawInvTopX
import lemmas.Ska.CompFragX
import lemmas.Ska.CompSevenN

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
  makes them) keeps that invariant in the end state's rank, and for every
  `K` that vanishes from `g0.bo` on leaves live at its entry, with the
  kills `K` and those of its result's lazy tree, only what its goal's
  continuation needs beyond the goal with the kills `K` (`GLiveK`).  Under
  `%done` nothing is live there, the hypothesis `hl` of
  `optIn_toStraight_prep`.
* The cases, whole cases of `FragX` at a time: `rawX_frag` (`run_rawUK`
  and `runL_frag`).
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
    GArgs goal → (∀ r, Defd g0.blocks r → ¬ GMem goal r) →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) →
    SIP X (upRk g1.blocks) g1.bo g1 ∧
      ∀ r, LiveK g1.blocks (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
        GLiveK g0.blocks K goal r

/-- **The case `frag`**: a nomm of the first fragment, by `run_rawUK`. -/
theorem rawX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : RawIHX S Map X nm := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hfd hr
  rw [runL_frag (hf goal) region g0] at hr
  obtain ⟨⟨nex', g1'⟩, hr', e⟩ := Option.map_eq_some_iff.mp hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨S1, L1⟩ := run_rawUK (K := K) h hg hD hj ha hfd hr'
  refine ⟨S1, fun r hl => ?_⟩
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
  intro goal region g0 g1 nex K hK h hg hD hj hA hfd hr
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha hr
  obtain ⟨S1, L1⟩ := ihq goal region g0 g1 nx K hK h hg hD hj hA hfd h1
  exact ⟨S1, fun r hlv => L1 r (hlv.mono fun x y e => e.imp id (lazK_fromL hl))⟩

/-! ## `[7 p q]` with `q` in the first fragment -/

theorem KVan.mono {K : Nat → Nat → Prop} {lo lo' : Nat} (h : KVan K lo) (hl : lo ≤ lo') : KVan K lo' :=
  ⟨fun k r hk => h.van k r (Nat.le_trans hl hk)⟩

/-- **The case `seven`**: `q` of the first fragment (`run_rawUK`), then `p`
for its fork-free result. -/
theorem rawX_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : RawIHX S Map X p) :
    RawIHX S Map X (Nomm.n7 p q) := by
  intro goal region g0 g1 nex K hK h hg hD hj hA hfd hr
  rw [runL_n7] at hr
  obtain ⟨nq', g2, h2, hr⟩ := bind_some hr
  rw [runL_frag (hq goal) region g0] at h2
  obtain ⟨⟨nq, g2'⟩, hq2, e⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨S2, L2⟩ := run_rawUK (K := K) h hg hD hj hA hfd hq2
  obtain ⟨-, b2, nb2, d2, s2, dd2, a2, lo2, hi2⟩ := sub_facts h hg hD hj hA hq2
  rw [Next.goal_toL] at hr
  obtain ⟨S1, L1⟩ := ihp nq.goal region _ g1 nex K (hK.mono b2) S2
    ⟨nb2, fun x hx => by rw [a2] at hx; cases hx⟩ d2 ⟨lo2, hi2⟩ a2 (defd_next h hfd s2 dd2) hr
  refine ⟨S1, fun r hl => ?_⟩
  obtain ⟨hl', hn⟩ := L1 r hl
  rcases L2 r hl' with e | e
  · exact absurd e hn
  · exact e

end Raw
end SkaModel
end Formalization
