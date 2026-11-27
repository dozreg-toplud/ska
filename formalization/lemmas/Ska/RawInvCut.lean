import lemmas.Ska.RawInvClosedRun
import lemmas.Ska.CompAboveRun
import lemmas.Ska.CompFinishF

/-!
# Raw `+comp` output: liveness cut at a set of labels

README Gaps 14.  When code after a run changes the run's goal targets (the
final pass puts ops in front of the branch blocks of a `%6`), the run's
liveness spec, which is about the state at its end, no longer applies to
the whole path.  The cut: a path from `k` either never enters `Z`
(`LiveAv`) or reaches a block of `Z` that is live (`live_cut`).  A path that
avoids the goal targets of a run stays in the run's own blocks
(`run_closed`), so it reads only registers those blocks mention
(`liveAv_region`, with `run_above` of track C).

`raw_coerce`: `+coerce-lazy` at one block on a fork-free need, from
`raw_sureLoop`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]

/-- Liveness along paths that do not enter `Z`. -/
inductive LiveAv (bl : Map Blob) (Z : Nat → Prop) : Nat → Nat → Prop
  | here {k : Nat} {b : Blob} {r : Nat} : ¬ Z k → HoonMap.get bl k = some b → BlockRF b r → LiveAv bl Z k r
  | next {k : Nat} {b : Blob} {j : Jmp} {r : Nat} : ¬ Z k → HoonMap.get bl k = some b → j ∈ getJmps b.fin →
      LiveAv bl Z j.there r → r ∉ blockDefs b → LiveAv bl Z k r

theorem LiveAv.notZ {bl : Map Blob} {Z : Nat → Prop} {k r : Nat} (h : LiveAv bl Z k r) : ¬ Z k := by
  cases h with
  | here hz _ _ => exact hz
  | next hz _ _ _ _ => exact hz

theorem LiveAv.forget {bl : Map Blob} {Z : Nat → Prop} {k r : Nat} (h : LiveAv bl Z k r) : Live bl k r := by
  induction h with
  | here _ hb hr => exact Live.here hb hr
  | next _ hb hj _ hd ih => exact Live.next hb hj ih hd

/-- **The cut.** -/
theorem live_cut {bl : Map Blob} (Z : Nat → Prop) {k r : Nat} (h : Live bl k r) :
    LiveAv bl Z k r ∨ ∃ z, Z z ∧ Live bl z r := by
  induction h with
  | @here k b r hb hr =>
    by_cases hz : Z k
    · exact Or.inr ⟨k, hz, Live.here hb hr⟩
    · exact Or.inl (LiveAv.here hz hb hr)
  | @next k b j r hb hj hl hd ih =>
    by_cases hz : Z k
    · exact Or.inr ⟨k, hz, Live.next hb hj hl hd⟩
    · rcases ih with e | e
      · exact Or.inl (LiveAv.next hz hb hj e hd)
      · exact Or.inr e

theorem liveAv_frame {bl bl' : Map Blob} {Z : Nat → Prop} {L : Nat} (hd : DownBelow bl L)
    (he : ∀ x, x < L → ¬ Z x → HoonMap.get bl' x = HoonMap.get bl x) {k r : Nat} (h : LiveAv bl' Z k r)
    (hk : k < L) : LiveAv bl Z k r := by
  induction h with
  | @here k b r hz hb hr => rw [he k hk hz] at hb; exact LiveAv.here hz hb hr
  | @next k b j r hz hb hj _ hd' ih =>
    rw [he k hk hz] at hb
    exact LiveAv.next hz hb hj (ih (Nat.lt_trans (hd k b hk hb j hj) hk)) hd'

theorem srcs_regs {op : Pole} {r : Nat} (h : r ∈ srcs op) : r ∈ Comp.poleRegs op := by
  cases op <;> simp [srcs, Comp.poleRegs] at h ⊢ <;> (try omega) <;> (try exact Or.inr h)

theorem jmpIn_regs {P : Nat → Prop} {j : Jmp} (hj : JmpIn P j) {r : Nat} (h : r ∈ jmpRegs j) : P r :=
  hj r (by simpa [jmpRegs] using h)

theorem finRegs_in {P : Nat → Prop} {f : Termin} (hf : FinIn P f) {r : Nat} (h : r ∈ finRegs f) : P r := by
  cases f with
  | clq s z o =>
    simp only [finRegs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hf.1
    · exact jmpIn_regs hf.2.1 h
    · exact jmpIn_regs hf.2.2 h
  | eqq l q z o =>
    simp only [finRegs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | rfl | h | h
    · exact hf.1
    · exact hf.2.1
    · exact jmpIn_regs hf.2.2.1 h
    · exact jmpIn_regs hf.2.2.2 h
  | brn s z o =>
    simp only [finRegs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hf.1
    · exact jmpIn_regs hf.2.1 h
    · exact jmpIn_regs hf.2.2 h
  | brz s z o =>
    simp only [finRegs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hf.1
    · exact jmpIn_regs hf.2.1 h
    · exact jmpIn_regs hf.2.2 h
  | lti n s z o =>
    simp only [finRegs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hf.1
    · exact jmpIn_regs hf.2.1 h
    · exact jmpIn_regs hf.2.2 h
  | hop t => exact jmpIn_regs hf h
  | jmp a v => exact hf r h
  | jmf a v n => exact hf r h
  | jsp a s => simp only [finRegs, List.mem_singleton] at h; subst h; exact hf
  | jsf a s n => simp only [finRegs, List.mem_singleton] at h; subst h; exact hf
  | don s => simp only [finRegs, List.mem_singleton] at h; subst h; exact hf
  | bom m => simp [finRegs] at h

/-- What a block reads first it mentions. -/
theorem blockRF_in {P : Nat → Prop} {b : Blob} (hb : BlobIn P b) {r : Nat} (h : BlockRF b r) : P r := by
  obtain ⟨-, h⟩ := h
  rcases h with h | ⟨-, h⟩
  · obtain ⟨op, hop, hr⟩ := opsRF_mem h
    exact hb.2.1 op hop r (srcs_regs (mem_aliasReads.mp hr))
  · exact finRegs_in hb.2.2 h

/-- **A path that avoids `Z` in a region closed up to `Z` reads only
registers the region mentions.** -/
theorem liveAv_region {bl : Map Blob} {Z R P : Nat → Prop}
    (hR : ∀ x b, R x → ¬ Z x → HoonMap.get bl x = some b → BlobIn P b ∧ ∀ j ∈ getJmps b.fin, R j.there ∨ Z j.there)
    {k r : Nat} (h : LiveAv bl Z k r) (hk : R k) : P r := by
  induction h with
  | @here k b r hz hb hr => exact blockRF_in (hR k b hk hz hb).1 hr
  | @next k b j r hz hb hj hl _ ih =>
    rcases (hR k b hk hz hb).2 j hj with e | e
    · exact ih e
    · exact absurd e hl.notZ

/-! ## `+coerce-lazy` at one block -/

/-- **`+coerce-lazy` on a fork-free need at block `o`**: ops in front of `o`
that read first only input registers and define every register of the
need, each once, and fresh ones. -/
theorem raw_coerce {S : Type} [HoonSet S] {ned : Need} {o : Nat} {laz : Sure S} {less : Cape}
    {g g' : Comp.Gen Map} {b : Blob} {u : Unit} (h : SI g) (hb : HoonMap.get g.blocks o = some b)
    (nn : NB g.re ned) (dl : Distinct laz.ned) (nl : NB g.re laz.ned)
    (ap : ∀ y, NMem ned y → ¬ NMem laz.ned y) (hf : ∀ y, NMem laz.ned y → ¬ Defd g.blocks y)
    (hc : coerceLazy ned o laz less g = some (u, g')) :
    SI g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
      (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
      (∀ y, OpsRF A y → NMem ned y) ∧ (∀ y, NMem laz.ned y → y ∈ defsOf A) ∧
      (∀ y ∈ defsOf A, NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) := by
  simp only [coerceLazy] at hc
  obtain ⟨lok, g1, hl, hc⟩ := bind_some hc
  obtain ⟨lk, -, el⟩ := Option.map_eq_some_iff.mp hl
  simp only [Prod.mk.injEq] at el
  obtain ⟨rfl, rfl⟩ := el
  obtain ⟨tgt, g2, ht, hc⟩ := bind_some hc
  have L := sureRequireLook_spec ht
  obtain ⟨k2, e2⟩ := L.gen
  have l2 := L.le
  have S2 : SI g2 := by rw [e2]; exact si_reg h (by rw [e2] at l2; exact l2)
  have b2 : g2.blocks = g.blocks := by rw [e2]
  have keepT : ∀ y, NMem laz.ned y → NMem tgt y := fun y hy => sureRequireLook_keeps ht hy
  have mT : ∀ y, NMem tgt y → NMem laz.ned y ∨ (g.re ≤ y ∧ y < g2.re) := L.mem
  obtain ⟨S3, bo3, l3, A, get3, rf3, cv3, df3⟩ := raw_sureLoop ned tgt g2 g' b u S2 (by rw [b2]; exact hb)
    (L.dist dl nl)
    (fun y hy => by rcases mT y hy with e | e
                    · have := nl y e; omega
                    · exact e.2)
    (fun y hy => by have := nn y hy; omega)
    (fun y hy ht' => by
      rcases mT y ht' with e | e
      · exact ap y hy e
      · have := nn y hy; omega)
    (fun y hy d => by
      rw [b2] at d
      rcases mT y hy with e | e
      · exact hf y e d
      · have := h.defd_lt d; omega) hc
  refine ⟨S3, by rw [bo3, e2], by omega, A, fun k => by rw [get3, b2], rf3, fun y hy => cv3 y (keepT y hy),
    fun y hy => ?_⟩
  rcases df3 y hy with e | e
  · rcases mT y e with e' | e'
    · exact Or.inl e'
    · exact Or.inr ⟨e'.1, by omega⟩
  · exact Or.inr ⟨by omega, e.2⟩

end Raw
end SkaModel
end Formalization
