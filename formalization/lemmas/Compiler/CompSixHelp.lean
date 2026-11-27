import lemmas.Compiler.CompRunSixN
import lemmas.Compiler.CompRunAllL

/-!
# The small helpers of the case `%6`: `+past-fork`, `+soft-less`,
# `+lazy-size`, `+lazy-big`, `+lazy-shut`

The nouns are printed by `tools/gen/sixhelp.py` (`pastFork softLess lazyBig
lazyShut lazySize`); each arm is tied to the pill by a kernel fact
(`pf_at`, `sl_at`, `lg_at`, `lsh_at`, `lsz_at`).  The trap of `+lazy-size`
is cut by hand into `lszTrap`, `lszFT` (the loop over the forks) and
`lszBT` (the loop over the bonds); `lsz_at` checks the cut.

* `+past-fork` (door arm `4061`, `comp_past_fork`): `pastFork noCode` on
  every lazy need, for every nomm on which `+hinted` returns, given the code
  table at axis `52` of the context (read by `+hinted` only at a direct
  call).
* `+soft-less` (door arm `52`, `comp_soft_less`): with an empty `soft` it
  rebuilds the need it is given (`softLess noSoft` is the identity).
* `+lazy-size` (`K` arm `348`, `lsz_gate`) is `lazySize`, and `+lazy-big`
  (`K` arm `11199`, `lg_gate`) is `lazyBig`, on every lazy need.
* `+lazy-shut` (door arm `218495`, `comp_lazy_shut`) is `lazyShut`, with
  `+kern` (`comp_kern_all`) on a big need.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The battery of `+pastFork` (door arm `4061`). -/
def pfBat : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x17774) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 2036)))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 24)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (C (C (A 0) (A 24)) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 24)) (C (A 0) (A 25))) (C (A 1) (A 0)))))) (C (C (A 0) (A 26)) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 26)) (C (A 0) (A 27))) (C (A 1) (A 0)))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 51)))) (C (A 0) (A 12)))))

def pfBunt : Noun :=
  (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))

def pfArm : Noun := C (A 8) (C (C (A 1) pfBunt) (C (C (A 1) pfBat) (C (A 0) (A 1))))

theorem pf_at : slot? 4061 comp.door = some pfArm := by kernel_rfl

theorem pf_arm (d : Noun) : nock d pfArm = some (C pfBat (C pfBunt d)) := by
  unfold pfArm; simp only [nock_exec]

/-! ## `+past-fork` -/

/-- The gate of its `+turn`: each fork need in a bond under its own label. -/
def pfG : Noun :=
  (C (C (C (A 0) (A 24)) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 24)) (C (A 0) (A 25))) (C (A 1) (A 0)))))) (C (C (A 0) (A 26)) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 26)) (C (A 0) (A 27))) (C (A 1) (A 0)))))))

theorem pf_bat_eq : pfBat = C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x17774) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 2036)))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 24)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) lzBunt) (C (A 0) lzBunt))) (C (C (A 1) pfG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 51)))) (C (A 0) (A 12)))) := rfl

/-- The model's map of `+past-fork` on one fork entry. -/
noncomputable def pfE (e : Lazy.ForkE CSet) : Lazy.ForkE CSet :=
  ((e.1.1, Lazy.mk Sure.bunt [] [(e.1.1, e.1.2)]), (e.2.1, Lazy.mk Sure.bunt [] [(e.2.1, e.2.2)]))

theorem pf_g (e : Lazy.ForkE CSet) (bs bc : Noun) :
    nock (C pfG (C (forkE e) (C bs bc))) pfG = some (forkE (pfE e)) := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  unfold pfG
  simp [nock_exec, forkE, pfE, lazy_toNoun_mk, bondE, Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none,
    HoonSet.toNoun_empty, listN]

theorem mapM_some_map {α β : Type} (f : α → β) : ∀ l : List α, l.mapM (fun a => some (f a)) = some (l.map f)
  | [] => rfl
  | a :: t => by simp [List.mapM_cons, mapM_some_map f t]

/-- **`+past-fork`** on every lazy need: `pastFork noCode`, for every nomm on
which `+hinted` returns (`hinted noCode nom ≠ none`) and every state noun. -/
theorem comp_past_fork (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (G : Noun) (laz : Lazy CSet) (nom : Nomm) (hnom : hinted noCode nom ≠ Option.none) :
    nock (C pfBat (C (C laz.toNoun nom.toNoun) (C comp.door (C G ctx)))) pfBat
      = (Lazy.pastFork noCode laz nom).map Lazy.toNoun := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  rcases e : hinted noCode nom with _ | b
  · exact absurd e hnom
  have hh := hd_gate compK cod nom b e
  obtain ⟨s, fk, bd⟩ := laz
  have ht := turn_gate_mapT forkE forkE layer2 homoIn_layer2 pfG (C (C (A 0) lzBunt) (C (A 0) lzBunt))
    (C pfBat (C (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) nom.toNoun)
      (C comp.door (C G ctx)))) (fun e => some (pfE e)) fk
    (fun e _ => by rw [pf_g]; rfl)
  rw [lazy_toNoun_mk]
  conv => { lhs; arg 2; rw [pf_bat_eq] }
  cases b
  · simp [nock_exec, Lazy.pastFork, e, h7, hcode, compK_hd, hd_arm, hh, loob, lazy_toNoun_mk]
  · simp [nock_exec, Lazy.pastFork, e, h7, hcode, compK_hd, hd_arm, hh, loob, lazy_toNoun_mk, hc, turn.arm_at,
      turn_arm, ht, mapM_some_map, pfE]
/-- The battery of `+softLess` (door arm `52`). -/
def slBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 27)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 6)) (C (C (A 0) (A 12)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (C (C (A 0) (A 24)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 7))))))) (C (C (A 0) (A 26)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 7))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 0) (A 12)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 7)))))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))

def slBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))

def slArm : Noun := C (A 8) (C (C (A 1) slBunt) (C (C (A 1) slBat) (C (A 0) (A 1))))

theorem sl_at : slot? 52 comp.door = some slArm := by kernel_rfl

theorem sl_arm (d : Noun) : nock d slArm = some (C slBat (C slBunt d)) := by
  unfold slArm; simp only [nock_exec]

/-! ## `+soft-less` -/

/-- The gate of its `+turn` over the forks: both needs through `+soft-less`. -/
def slSG : Noun :=
  (C (C (C (A 0) (A 24)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 7))))))) (C (C (A 0) (A 26)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 7))))))))

/-- The test `(~(has by soft.gen) o.e)` of its `+murn` over the bonds. -/
def slHas : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

/-- The gate of its `+murn` over the bonds: `~` on a bond of a soft call,
else the bond through `+soft-less`. -/
def slBG : Noun :=
  C (A 6) (C slHas (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 0) (A 12)) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 7))))))))))

theorem sl_bat_eq : slBat = C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 6)
    (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 27)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))
    (C (C (A 0) (A 6)) (C (C (A 0) (A 12)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8)
    (C (C (A 1) (C (C (A 0) lzBunt) (C (A 0) lzBunt))) (C (C (A 1) slSG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))
    (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) lzBunt)) (C (C (A 1) slBG)
    (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) := rfl

section
variable (hc : CompIn ctx) (x : GenRest) (hx : x.NoSoft) (G0 : Gen (TreapMap mugF))
include hc hx

mutual
/-- **`+soft-less` with an empty `soft`** rebuilds the need it is given
(`softLess noSoft` is the identity, `softLess_noSoft`). -/
theorem sl_all : ∀ (laz : Lazy CSet),
    nock (C slBat (C laz.toNoun (C comp.door (C (genNoun G0 x) ctx)))) slBat = some laz.toNoun
  | Lazy.mk s fk bd => by
    rw [lazy_toNoun_mk]
    have hT := turn_gate layer2 homoIn_layer2 slSG (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C slBat (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C comp.door (C (genNoun G0 x) ctx))))
      id (fk.map forkE) (fun y hy => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
        exact sl_forks fk e he _)
    have hM := murn_gate layer2 homoIn_layer2 slBG (C (A 0) lzBunt)
      (C slBat (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C comp.door (C (genNoun G0 x) ctx))))
      (fun y => C (A 0) y) (bd.map bondE) (fun y hy => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
        exact ⟨sl_bonds bd e he _, Or.inr ⟨_, _, rfl⟩⟩)
    have hfm : ((bd.map bondE).filterMap fun y => unitVal (C (A 0) y)) = bd.map bondE := by
      simp [unitVal]
    rw [hfm] at hM
    simp only [List.map_id] at hT
    conv => { lhs; arg 2; rw [sl_bat_eq] }
    have tF := lz_test forkE fk
    have tB := lz_test bondE bd
    rcases tF with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩ <;> rcases tB with ⟨t4, t5, t6⟩ | ⟨t4, t5, t6⟩ <;>
    · first | replace t1 := eq_false t1 | replace t1 := eq_true t1
      first | replace t4 := eq_false t4 | replace t4 := eq_true t4
      simp [nock_exec, t1, t2, t3, t4, t5, t6, hc, turn.arm_at, turn_arm, hT, crn_murn_arm, murn.arm_at, hM]

theorem sl_forks : ∀ (fk : List (Lazy.ForkE CSet)), ∀ e ∈ fk, ∀ L : Noun,
    nock (C slSG (C (forkE e) (C slBat (C L (C comp.door (C (genNoun G0 x) ctx)))))) slSG = some (forkE e)
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have ihy := sl_all y
      have ihn := sl_all n
      unfold slSG
      simp [nock_exec, forkE, ihy, ihn]
    · exact sl_forks rest e he'

theorem sl_bonds : ∀ (bd : List (Nat × Lazy CSet)), ∀ e ∈ bd, ∀ L : Noun,
    nock (C slBG (C (bondE e) (C slBat (C L (C comp.door (C (genNoun G0 x) ctx)))))) slBG
      = some (C (A 0) (bondE e))
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have ihl := sl_all l
      simp only [genNoun] at ihl
      have hhas := crn_has x ob (hx ob)
      unfold slBG slHas
      simp [nock_exec, bondE, ihl, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas, genNoun]
    · exact sl_bonds rest e he'
end

end

/-! ## `+lazy-size`, `+lazy-big` -/

def lszFT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 250)))) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 2001))) (C (A 0) (A 3))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 2003))) (C (A 0) (A 3))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 250) (C (A 0) (A 501))) (C (A 0) (A 1)))))))))))))

def lszBT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 251)))) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 251) (C (A 0) (A 503))) (C (A 10) (C (C (A 14) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 1005))) (C (A 0) (A 3))))))) (C (A 0) (A 1)))))))))))

def lszTrap : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 343) (C (A 0) (A 31)))))))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 6)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 1) lszFT) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 1) lszBT) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))))

def lszBat : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) lszTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))


def lszBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))

def lszArm : Noun := C (A 8) (C (C (A 1) lszBunt) (C (C (A 1) lszBat) (C (A 0) (A 1))))

/-- **The cut of `+lazy-size`** (`K` arm `348`) is the pill's. -/
theorem lsz_at : slot? 348 compK = some lszArm := by kernel_rfl

theorem lsz_arm (d : Noun) : nock d lszArm = some (C lszBat (C lszBunt d)) := by
  unfold lszArm; simp only [nock_exec]

/-- `lazy-max` is arm `343` of `K`: the constant `512`. -/
theorem lmax_at : slot? 343 compK = some (C (A 1) (A 512)) := by kernel_rfl

theorem compK_layer1 : slot? 131071 compK = some layer1 := by
  have h := slot_bit 65535 (by decide) 1 (by decide) compK
  rw [compK_layer2] at h
  rw [show (131071 : Nat) = 2 * 65535 + 1 from rfl, h]
  exact (slot_three layer2).symm.trans layer2_layer1

theorem lazyMax_eq : Lazy.lazyMax = 512 := rfl

mutual
/-- **The trap of `+lazy-size`** from the count `c` is `lazySizeGo c`. -/
theorem lsz_go : ∀ (laz : Lazy CSet) (c : Nat),
    nock (C lszTrap (C (A c) (C lszBat (C laz.toNoun compK)))) lszTrap = some (A (Lazy.lazySizeGo c laz))
  | Lazy.mk s fk bd, c => by
    have hF := lsz_forks fk (c + 1) s.toNoun (listN (bd.map bondE))
    have hB := lsz_bonds bd (Lazy.sizeForks (c + 1) fk) s.toNoun (listN (fk.map forkE))
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 c 512
    rw [lazy_toNoun_mk]
    by_cases h : c > Lazy.lazyMax
    · have h' : 512 < c := h
      simp only [Lazy.lazySizeGo, h, if_true]
      conv => { lhs; arg 2; unfold lszTrap }
      simp [nock_exec, compK_layer1, gth.arm_at, gth_arm, hg, lmax_at, h', loob]
    · have h' : ¬ 512 < c := h
      simp only [Lazy.lazySizeGo, h, if_false]
      conv => { lhs; arg 2; unfold lszTrap }
      simp [nock_exec, compK_layer1, gth.arm_at, gth_arm, hg, lmax_at, h', loob, hF, hB]

theorem lsz_forks : ∀ (fk : List (Lazy.ForkE CSet)) (c : Nat) (s b : Noun),
    nock (C lszFT (C lszTrap (C (A c) (C lszBat (C (C s (C (listN (fk.map forkE)) b)) compK))))) lszFT
      = some (A (Lazy.sizeForks c fk))
  | [], c, s, b => by
    unfold lszFT
    simp [nock_exec, Lazy.sizeForks]
  | ((oy, y), (on, n)) :: rest, c, s, b => by
    have h1 := lsz_go y c
    have h2 := lsz_go n (Lazy.lazySizeGo c y)
    have h3 := lsz_forks rest (Lazy.lazySizeGo (Lazy.lazySizeGo c y) n) s b
    conv => { lhs; arg 2; unfold lszFT }
    simp [nock_exec, Lazy.sizeForks, forkE, h1, h2, h3]

theorem lsz_bonds : ∀ (bd : List (Nat × Lazy CSet)) (c : Nat) (s f : Noun),
    nock (C lszBT (C lszTrap (C (A c) (C lszBat (C (C s (C f (listN (bd.map bondE)))) compK))))) lszBT
      = some (A (Lazy.sizeBonds c bd))
  | [], c, s, f => by
    unfold lszBT
    simp [nock_exec, Lazy.sizeBonds]
  | (ob, l) :: rest, c, s, f => by
    have h1 := lsz_go l c
    have h3 := lsz_bonds rest (Lazy.lazySizeGo c l) s f
    conv => { lhs; arg 2; unfold lszBT }
    simp [nock_exec, Lazy.sizeBonds, bondE, h1, h3]
end

/-- **`+lazy-size`** (`K` arm `348`) is `lazySize`. -/
theorem lsz_gate (laz : Lazy CSet) :
    nock (C lszBat (C laz.toNoun compK)) lszBat = some (A (Lazy.lazySize laz)) := by
  have h := lsz_go laz 0
  conv => { lhs; arg 2; unfold lszBat }
  simp [nock_exec, h, Lazy.lazySize]

/-- The battery of `+lazyBig` (K arm `11199`). -/
def lgBat : Noun :=
  (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 343) (C (A 0) (A 7)))))))) (C (A 0) (A 2))))))))

def lgBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))

def lgArm : Noun := C (A 8) (C (C (A 1) lgBunt) (C (C (A 1) lgBat) (C (A 0) (A 1))))

theorem lg_at : slot? 11199 compK = some lgArm := by kernel_rfl

theorem lg_arm (d : Noun) : nock d lgArm = some (C lgBat (C lgBunt d)) := by
  unfold lgArm; simp only [nock_exec]

/-- **`+lazy-big`** (`K` arm `11199`) is `lazyBig`. -/
theorem lg_gate (laz : Lazy CSet) :
    nock (C lgBat (C laz.toNoun compK)) lgBat = some (loob (Lazy.lazyBig laz)) := by
  have hs := lsz_gate laz
  have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 (Lazy.lazySize laz) 512
  unfold lgBat
  simp [nock_exec, compK_layer1, gth.arm_at, gth_arm, hg, lmax_at, lsz_at, lsz_arm, hs, Lazy.lazyBig, lazyMax_eq]

/-! ## `+lazy-shut` -/

/-- The battery of `+lazyShut` (door arm `218495`). -/
def lshBat : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2bbf) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bff) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 2)))))) (C (A 0) (A 2)))))))) (C (A 0) (A 62))))))))))) (C (C (A 0) (A 13)) (C (A 0) (A 30))))))

def lshBunt : Noun :=
  (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))

def lshArm : Noun := C (A 8) (C (C (A 1) lshBunt) (C (C (A 1) lshBat) (C (A 0) (A 1))))

theorem lsh_at : slot? 218495 comp.door = some lshArm := by kernel_rfl

theorem lsh_arm (d : Noun) : nock d lshArm = some (C lshBat (C lshBunt d)) := by
  unfold lshArm; simp only [nock_exec]


/-- **`+lazy-shut`** on every lazy need with an empty `soft`, whose walk from
`o` looks at no axis `0`: `lazyShut o` (`+kern` at `o` when the need is big,
else the need itself). -/
theorem comp_lazy_shut (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (g : Gen (TreapMap mugF))
    (o : Nat) (laz : Lazy CSet) (hP : WalkP (mdP x) o laz) :
    nock (C lshBat (C (C (A o) laz.toNoun) (compCore g x ctx))) lshBat
      = (lazyShut o laz g).map fun p => C p.1.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  have h15 := cr_ctx15 h7
  have hsl := sl_all hc x hx g laz
  have hlg := lg_gate laz
  have hk := comp_kern_all hc hl hm x g o laz hP
  have hD1 := sl_at
  have hD2 := comp_kern_at
  simp only [compCore] at hk ⊢
  unfold lazyShut
  rw [Lazy.softLess_noSoft]
  cases eb : Lazy.lazyBig laz
  · generalize comp.door = Dr at hsl hk hD1 hD2 ⊢
    nock_open lshBat
    simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, pure, StateT.pure]
  · cases ek : kern o laz g with
    | none =>
      rw [ek] at hk
      generalize comp.door = Dr at hsl hk hD1 hD2 ⊢
      nock_open lshBat
      simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD2, comp_kern_arm, hk, ek, bind,
        StateT.bind]
    | some r =>
      obtain ⟨r, g1⟩ := r
      rw [ek] at hk
      generalize comp.door = Dr at hsl hk hD1 hD2 ⊢
      nock_open lshBat
      simp [nock_exec, h7, lg_at, lg_arm, hlg, eb, loob, hD1, sl_arm, hsl, hD2, comp_kern_arm, hk, ek, bind,
        StateT.bind, h15, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, pure, StateT.pure, Lazy.toNoun_ofSure, lazyNoun,
        Sure.toNoun, Need.toNoun, Tag.this, HoonSet.toNoun_empty]

end Compiler
end Formalization
