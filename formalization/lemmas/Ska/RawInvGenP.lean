import lemmas.Ska.RawInvGen
import lemmas.Ska.RawInvLiveK

/-!
# Raw `+comp` output: the invariant of a state, with ranks

README Gaps 14, track D, the class `FragX`.  `SI` asks every block of the
state to jump down and to have at most one parameter, which a state after a
`%6` under `%next` does not have (the fork blocks hop up to the join, which
has the parameters of a need).  A run of `run` (the first fragment) after
such a `%6` needs neither of the two of the old blocks: its new blocks jump
down from labels above every old one, and what it says of liveness only
asks that paths never come back to a block.

* `SIP X ρ lo g`: the fields of `SI` that do not mention jumps or
  parameters, the jumps going down in a rank `ρ` (`JDownR ρ`), `ρ k = 3 k`
  from the label `lo` on and `ρ x < 3 lo` below it, and a predicate `X` of
  the blocks that the two steps keep (`XOK X`: a new block as `+emit` puts
  it, under the facts that `EmitOK` gives; ops in front of a block).
* `Xstd`: `JDown`, `Par1` and `ArgsAbove`, the remaining fields of `SI`, so
  that `SI g ↔ SIP Xstd (3 * ·) 0 g` (`si_sip`, `sip_si`).
* `sip_reg`, `sip_re`, `sip_emit`, `sip_addOps`: `si_reg`, `si_re`,
  `si_emit`, `si_addOps` for `SIP`.
* Liveness by rank: `live_frameRk`, `live_unfoldRk`, `live_prependRk`
  (paths go down in `ρ`, so blocks of rank at least `M` are never seen
  from a label of rank below `M`); `DownBelowP` and `live_unfoldP`,
  `live_frameP`, the label forms that `SIP.below` gives at `g.bo` and above.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]

/-! ## Liveness by rank -/

theorem live_frameRk_to {ρ : Nat → Nat} {bl bl' : Map Blob} {M : Nat} (hd : JDownR ρ bl)
    (he : ∀ x, ρ x < M → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (h : Live bl' k r) (hk : ρ k < M) :
    Live bl k r := by
  induction h with
  | @here k b r hb hr => rw [he k hk] at hb; exact Live.here hb hr
  | @next k b j r hb hj _ hd' ih =>
    rw [he k hk] at hb
    exact Live.next hb hj (ih (Nat.lt_trans (hd k b hb j hj) hk)) hd'

theorem live_frameRk_of {ρ : Nat → Nat} {bl bl' : Map Blob} {M : Nat} (hd : JDownR ρ bl)
    (he : ∀ x, ρ x < M → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (h : Live bl k r) (hk : ρ k < M) :
    Live bl' k r := by
  induction h with
  | @here k b r hb hr => rw [← he k hk] at hb; exact Live.here hb hr
  | @next k b j r hb hj _ hd' ih =>
    have hlt := hd k b hb j hj
    rw [← he k hk] at hb
    exact Live.next hb hj (ih (Nat.lt_trans hlt hk)) hd'

/-- **Liveness below the rank `M` sees only the blocks below `M`.** -/
theorem live_frameRk {ρ : Nat → Nat} {bl bl' : Map Blob} {M : Nat} (hd : JDownR ρ bl)
    (he : ∀ x, ρ x < M → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (hk : ρ k < M) :
    Live bl' k r ↔ Live bl k r :=
  ⟨fun h => live_frameRk_to hd he h hk, fun h => live_frameRk_of hd he h hk⟩

theorem live_unfoldRk {ρ : Nat → Nat} {bl bl' : Map Blob} {k M : Nat} {b : Blob} (hk : HoonMap.get bl' k = some b)
    (hd : JDownR ρ bl) (he : ∀ x, ρ x < M → HoonMap.get bl' x = HoonMap.get bl x)
    (hj : ∀ j ∈ getJmps b.fin, ρ j.there < M) {r : Nat} (h : Live bl' k r) :
    BlockRF b r ∨ ∃ j ∈ getJmps b.fin, Live bl j.there r ∧ r ∉ blockDefs b := by
  obtain ⟨b', hb', hr⟩ := live_iff.mp h
  rw [hk] at hb'; cases hb'
  rcases hr with hr | ⟨j, hjm, hl, hn⟩
  · exact Or.inl hr
  · exact Or.inr ⟨j, hjm, (live_frameRk hd he (hj j hjm)).mp hl, hn⟩

/-- **Liveness at a block with ops in front**, when the blocks go down in a
rank. -/
theorem live_prependRk {ρ : Nat → Nat} {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole}
    (hb : HoonMap.get bl o = some b) (hd : JDownR ρ bl) {r : Nat}
    (h : Live (HoonMap.put bl o (pre A b)) o r) :
    (r ∉ b.par ∧ OpsRF A r) ∨ (r ∉ defsOf A ∧ Live bl o r) := by
  have he : ∀ x, ρ x < ρ o → HoonMap.get (HoonMap.put bl o (pre A b)) x = HoonMap.get bl x :=
    fun x hx => get_put_ne (fun e => by subst e; omega)
  rcases live_unfoldRk (b := pre A b) get_put_self hd he (fun j hj => hd o b hb j hj) h with
    ⟨hp, hr⟩ | ⟨j, hj, hl, hn⟩
  · simp only [pre] at hp hr
    rcases hr with hr | ⟨hn, hf⟩
    · rcases opsRF_append.mp hr with hr | ⟨hnA, hr⟩
      · exact Or.inl ⟨hp, hr⟩
      · exact Or.inr ⟨hnA, Live.here hb ⟨hp, Or.inl hr⟩⟩
    · rw [defsOf_append, List.mem_append, not_or] at hn
      exact Or.inr ⟨hn.1, Live.here hb ⟨hp, Or.inr ⟨hn.2, hf⟩⟩⟩
  · have hn' : r ∉ blockDefs b ∧ r ∉ defsOf A := ⟨fun e => hn (mem_blockDefs_pre.mpr (Or.inl e)),
      fun e => hn (mem_blockDefs_pre.mpr (Or.inr e))⟩
    exact Or.inr ⟨hn'.2, Live.next hb hj hl hn'.1⟩

/-- Blocks below `L` reach only blocks below `L`, by a rank in which every
block goes down. -/
def DownBelowP (bl : Map Blob) (L : Nat) : Prop :=
  ∃ ρ : Nat → Nat, JDownR ρ bl ∧ (∀ x, ρ x < 3 * L → x < L) ∧ ∀ x, x < L → ρ x < 3 * L

theorem JDown.belowP {bl : Map Blob} (h : JDown bl) (L : Nat) : DownBelowP bl L :=
  ⟨fun k => 3 * k, fun k b hb j hj => by have := h k b hb j hj; show 3 * _ < 3 * _; omega,
    fun x hx => by simp only at hx; omega, fun x hx => by simp only; omega⟩

theorem live_unfoldP {bl bl' : Map Blob} {k L : Nat} {b : Blob} (hk : HoonMap.get bl' k = some b)
    (hd : DownBelowP bl L) (he : ∀ x, x < L → HoonMap.get bl' x = HoonMap.get bl x)
    (hj : ∀ j ∈ getJmps b.fin, j.there < L) {r : Nat} (h : Live bl' k r) :
    BlockRF b r ∨ ∃ j ∈ getJmps b.fin, Live bl j.there r ∧ r ∉ blockDefs b :=
  let ⟨_, hd, h1, h2⟩ := hd
  live_unfoldRk hk hd (fun x hx => he x (h1 x hx)) (fun j hj' => h2 _ (hj j hj')) h

theorem live_frameP {bl bl' : Map Blob} {L : Nat} (hd : DownBelowP bl L)
    (he : ∀ x, x < L → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (hk : k < L) :
    Live bl' k r ↔ Live bl k r :=
  let ⟨_, hd, h1, h2⟩ := hd
  live_frameRk hd (fun x hx => he x (h1 x hx)) (h2 k hk)

/-! ## The invariant with ranks -/

/-- **What the two steps keep of a predicate `X` of the blocks.** -/
class XOK (X : Map Blob → Prop) : Prop where
  put : ∀ {bl : Map Blob} {l : Nat} {b : Blob}, X bl → (∀ k b', HoonMap.get bl k = some b' → k < l) →
    (∀ j ∈ getJmps b.fin, j.there < l) → b.par.length ≤ 1 →
    (∀ j ∈ getJmps b.fin, ∀ r, some r ∈ j.args → ∀ z bz, HoonMap.get (HoonMap.put bl l b) z = some bz →
      z ≤ j.there → ∀ x ∈ bz.par, x < r) →
    X (HoonMap.put bl l b)
  prep : ∀ {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole}, X bl → HoonMap.get bl o = some b →
    X (HoonMap.put bl o (pre A b))

/-- The fields of `SI` about jumps and parameters. -/
def Xstd (bl : Map Blob) : Prop := JDown bl ∧ Par1 bl ∧ ArgsAbove bl

instance : XOK (Xstd (Map := Map)) where
  put := fun hx hlab hj hp ha =>
    ⟨jdown_put hx.1 hj, par1_put hx.2.1 hp, argsAbove_put hx.2.2 hx.1 hlab fun j hj' r hr => ⟨hj j hj', ha j hj' r hr⟩⟩
  prep := fun hx hb => ⟨jdown_prepend hx.1 hb, par1_prepend hx.2.1 hb, argsAbove_prepend hx.2.2 hb⟩

instance : XOK (fun _ : Map Blob => True) where
  put := fun _ _ _ _ _ => trivial
  prep := fun _ _ => trivial

/-- **The invariant of a state, with the jumps going down in a rank `ρ`.** -/
structure SIP (X : Map Blob → Prop) (ρ : Nat → Nat) (lo : Nat) (g : Comp.Gen Map) : Prop where
  drop : g.drop = false
  bo1 : 1 ≤ g.bo
  lab : ∀ k b, HoonMap.get g.blocks k = some b → k < g.bo
  regs : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b
  nd : BlkNodup g.blocks
  cr : Cross g.blocks
  tr : NoTr g.blocks
  jr : JDownR ρ g.blocks
  lob : lo ≤ g.bo
  rk : ∀ k, lo ≤ k → ρ k = 3 * k
  rlo : ∀ x, x < lo → ρ x < 3 * lo
  x : X g.blocks

variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}

theorem si_sip {g : Comp.Gen Map} (h : SI g) : SIP Xstd (fun k => 3 * k) 0 g :=
  ⟨h.drop, h.bo1, h.lab, h.regs, h.nd, h.cr, h.tr, fun k b hb j hj => by
      have := h.jd k b hb j hj; show 3 * _ < 3 * _; omega,
    Nat.zero_le _, fun _ _ => rfl, fun x hx => absurd hx (Nat.not_lt_zero _), ⟨h.jd, h.p1, h.aa⟩⟩

theorem sip_si {g : Comp.Gen Map} (h : SIP Xstd ρ lo g) : SI g :=
  ⟨h.drop, h.bo1, h.lab, h.x.1, h.regs, h.nd, h.cr, h.tr, h.x.2.1, h.x.2.2⟩

theorem SIP.defd_lt {g : Comp.Gen Map} (h : SIP X ρ lo g) {r : Nat} (hd : Defd g.blocks r) : r < g.re := by
  obtain ⟨o, b, hb, hm⟩ := defd_iff.mp hd
  have R := h.regs o b hb
  rcases mem_blockDefs.mp hm with hm | hm
  · exact R.1 r hm
  · obtain ⟨op, hop, hdst⟩ := mem_defsOf.mp hm
    exact R.2.1 op hop r (dst_mem_regs hdst)

theorem SIP.none {g : Comp.Gen Map} (h : SIP X ρ lo g) {k : Nat} (hk : g.bo ≤ k) :
    HoonMap.get g.blocks k = Option.none := by
  cases e : HoonMap.get g.blocks k with
  | none => rfl
  | some b => have := h.lab k b e; omega

/-- From `g.bo` on, the blocks below a label reach only blocks below it. -/
theorem SIP.below {g : Comp.Gen Map} (h : SIP X ρ lo g) (L : Nat) (hL : g.bo ≤ L := by omega) :
    DownBelowP g.blocks L := by
  have := h.lob
  refine ⟨ρ, h.jr, fun x hx => ?_, fun x hx => ?_⟩
  · by_cases e : lo ≤ x
    · rw [h.rk x e] at hx; omega
    · have := h.rlo x (by omega); omega
  · by_cases e : lo ≤ x
    · rw [h.rk x e]; omega
    · have := h.rlo x (by omega); omega

theorem sip_reg {g : Comp.Gen Map} (h : SIP X ρ lo g) {k : Nat} (hk : g.re ≤ k) : SIP X ρ lo { g with re := k } :=
  ⟨h.drop, h.bo1, h.lab, fun o b hb => (h.regs o b hb).mono fun x hx => Nat.lt_of_lt_of_le hx hk,
    h.nd, h.cr, h.tr, h.jr, h.lob, h.rk, h.rlo, h.x⟩

theorem sip_re {g g' : Comp.Gen Map} {r : Nat} (h : SIP X ρ lo g) (hr : (re : CM Map Nat) g = some (r, g')) :
    SIP X ρ lo g' ∧ r = g.re ∧ g'.re = g.re + 1 ∧ g'.blocks = g.blocks ∧ g'.bo = g.bo := by
  rw [re_apply] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨sip_reg h (Nat.le_succ _), rfl, rfl, rfl, rfl⟩

theorem sip_emit {g g' : Comp.Gen Map} {b : Blob} {o : Nat} (h : SIP X ρ lo g) (E : EmitOK g b)
    (he : (emit b : CM Map Nat) g = some (o, g')) :
    SIP X ρ lo g' ∧ o = g.bo ∧ g'.blocks = HoonMap.put g.blocks g.bo b ∧ g'.re = g.re ∧ g'.bo = g.bo + 1 := by
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hb : (g.emitted b).blocks = HoonMap.put g.blocks g.bo b := by simp [Gen.emitted, h.drop]
  have hl := h.none (Nat.le_refl g.bo)
  have hlo := h.lob
  have hbo : (g.emitted b).bo = g.bo + 1 := by simp [Gen.emitted]
  refine ⟨⟨by simp [Gen.emitted, h.drop], by simp [Gen.emitted], ?_, ?_, ?_, ?_, ?_, ?_, by omega, h.rk, h.rlo, ?_⟩,
    rfl, hb, rfl, rfl⟩ <;> try rw [hb]
  · intro k b' hk
    rcases get_put_cases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · simp [Gen.emitted]
    · have := h.lab k b' hk; simp [Gen.emitted]; try omega
  · intro k b' hk
    rcases get_put_cases hk with ⟨-, rfl⟩ | ⟨-, hk⟩
    · exact E.regs
    · exact h.regs k b' hk
  · exact blkNodup_put h.nd E.nd
  · exact cross_put h.cr hl E.fresh
  · exact noTr_put h.tr E.tr
  · intro k b' hk j hj
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have hj' := E.jd j hj
      rw [h.rk g.bo (by omega)]
      by_cases e : lo ≤ j.there
      · rw [h.rk _ e]; omega
      · have := h.rlo j.there (by omega); omega
    · exact h.jr k b' hk j hj
  · exact XOK.put h.x h.lab E.jd E.p1 E.args

theorem sip_addOps {g g' : Comp.Gen Map} {o : Nat} {A : List Pole} {u : Unit} (h : SIP X ρ lo g) (P : OpsOK g A)
    (ha : addOps o A g = some (u, g')) :
    SIP X ρ lo g' ∧ ∃ b, HoonMap.get g.blocks o = some b ∧ g'.blocks = HoonMap.put g.blocks o (pre A b) ∧
      g'.re = g.re ∧ g'.bo = g.bo := by
  obtain ⟨b, hb, rfl⟩ := addOps_spec ha h.drop
  refine ⟨⟨h.drop, h.bo1, ?_, ?_, blkNodup_prepend h.nd hb P.nd P.fresh,
    cross_prepend h.cr hb P.fresh, noTr_prepend h.tr hb P.tr, ?_, h.lob, h.rk, h.rlo, XOK.prep h.x hb⟩,
    b, hb, rfl, rfl, rfl⟩
  · intro k b' hk
    rcases get_put_cases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
    · exact h.lab k b hb
    · exact h.lab k b' hk
  · intro k b' hk
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have R := h.regs k b hb
      exact ⟨R.1, P.regs.append R.2.1, R.2.2⟩
    · exact h.regs k b' hk
  · intro k b' hk j hj
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact h.jr k b hb j hj
    · exact h.jr k b' hk j hj

end Raw
end SkaModel
end Formalization
