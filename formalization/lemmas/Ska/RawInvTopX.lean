import lemmas.Ska.RawInvLiveK
import lemmas.Ska.RawInvOutR

/-!
# Raw `+comp` output with `%6` below the top: from the run's blocks to `OptIn`

README Gaps 14, the class `FragX`.  The final pass on a run of `FragX`
puts ops in front of the lazy entries (`+coerce-lazy` at every entry of the
result's lazy need) and then renames (`+to-straight`, which on `FragX` takes
its renaming path: no run of `FragX` makes a proxy, `okV_fragX`).

* **`optIn_toStraight_prep`**: the output meets `OptIn` when the raw blocks
  go down in the rank `upRk` (`DownRk`), pass arguments above the
  parameters by that rank (`ArgsAboveR`), and leave no register live at the
  entry once each lazy entry first defines its kills (`LiveK`); and the
  prologues define those kills, read first only input registers, and leave
  every register defined once (`BlkNodup`, `Cross`), with no trace hint op.
  These are the facts that `checkRunX` of `RawInvCheckX.lean` checks of the
  raw blocks, so what is left for `FragX` is their run-level induction and
  the prologue facts of `+coerce-lazy` over a lazy tree.
* **`liveK_prep`**: the composition step a parent needs when it puts ops in
  front of the lazy entries of a sub-run's result (`+copy`, `+split`): with
  prologues that define the old kills and read first only the new ones,
  liveness with the new kills after them is liveness with the old kills
  before them.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]

/-- **Prologues between two kill maps.**  When the ops `P k` define the
registers `K k` and read first only registers of `K' k`, a register live
with the kills `K'` after them is live with the kills `K` before them. -/
theorem liveK_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {K K' : Nat → Nat → Prop}
    (hK : ∀ k r, K k r → r ∈ defsOf (P k)) (hK' : ∀ k r, OpsRF (P k) r → K' k r) {k r : Nat}
    (h : LiveK bl' K' k r) : LiveK bl K k r := by
  induction h with
  | here hb hr hk =>
    obtain ⟨b0, h0, rfl⟩ := get_prep hP hb
    rcases blockRF_pre hr with h | ⟨hd, h⟩
    · exact absurd (hK' _ _ h) hk
    · exact LiveK.here h0 h fun h => hd (hK _ _ h)
  | next hb hj _ hd _ ih =>
    obtain ⟨b0, h0, rfl⟩ := get_prep hP hb
    exact LiveK.next h0 hj ih (fun hm => hd (mem_blockDefs_pre.mpr (Or.inl hm)))
      fun h => hd (mem_blockDefs_pre.mpr (Or.inr (hK _ _ h)))

theorem downRk_prep {ρ : Nat → Nat} {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl')
    (h : DownRk ρ bl) : DownRk ρ bl' := by
  intro k b' hb'
  obtain ⟨b, hb, rfl⟩ := get_prep hP hb'
  exact h k b hb

theorem jdownR_of_downRk {ρ : Nat → Nat} {bl : Map Blob} (h : DownRk ρ bl) : JDownR ρ bl :=
  fun k b hb j hj => ((h k b hb).2 j (by rw [← getJmps_eq]; exact hj)).2

theorem noTr_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') (h : NoTr bl)
    (hp : ∀ k op, op ∈ P k → trOp op = false) : NoTr bl' := by
  intro k b' hb' op hop
  obtain ⟨b, hb, rfl⟩ := get_prep hP hb'
  rcases List.mem_append.mp hop with e | e
  · exact hp k op e
  · exact h k b hb op e

variable [HoonMapKeys Map] [MapKeys Map]

/-- **`OptIn` after prologues at the lazy entries and `+to-straight`.** -/
theorem optIn_toStraight_prep {bl bl' : Map Blob} {P : Nat → List Pole} {K : Nat → Nat → Prop}
    {ned : Need} {o : Nat} {c' : Straight Map}
    (hP : Prep P bl bl') (hrk : DownRk (upRk bl) bl) (haa : ArgsAboveR (upRk bl) bl)
    (hK : ∀ k r, K k r → r ∈ defsOf (P k)) (hl : ∀ r, ¬ LiveK bl K o r)
    (hn : BlkNodup bl') (hx : Cross bl') (ht : NoTr bl')
    (hX : ∀ k r, OpsRF (P k) r → NMem ned r) (hin : ∀ r, NMem ned r → ¬ Defd bl' r)
    (h : toStraight bl' ned o = some c') : OptIn c'.blocks := by
  have e : upRk bl' = upRk bl := funext (upRk_prep hP)
  have rk' : DownRk (upRk bl') bl' := by rw [e]; exact downRk_prep hP hrk
  have aa' : ArgsAboveR (upRk bl') bl' := argsAboveR_upRk_prep hP haa
  exact optIn_toStraightR h rk' hn hx ht (downPar_of_argsR aa' (jdownR_of_downRk rk'))
    (fun r hr => live_entry_of_prep hP hK hl hX hr) hin

end Raw
end SkaModel
end Formalization
