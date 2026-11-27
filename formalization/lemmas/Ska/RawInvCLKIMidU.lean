import lemmas.Ska.RawInvCLKUSplit
import lemmas.Ska.RawInvCLKUCopy
import lemmas.Ska.RawInvCLKURun
import lemmas.Ska.RawInvCLKIMid
import lemmas.Glue.GuardCallsB

/-!
# Track G's mid-run fact, corrected and proved on `PlainN`

README Gaps 14 (b), track D.  Track G's `KIMid` (`Glue/GuardCallsB.lean`)
is FALSE in its run clause (`RawInvCLKIMidW.lean`: a goal with two bonds at
one label that share a register meets `GD`, and `cons [0 2] [0 3]` returns a
bond whose need holds that register twice).  Its true form, `KIMidX`, asks
of the goal what the state-free count of `RawInvCLKUBase.lean` carries: the
registers of the WHOLE tree are distinct and below `re` (`GX`), and the tree
has bonds and forks at distinct labels, its entries below `bo` (`LG`).  That
implies `GD` (`KIMidX.dn`), so track G's `RunG` can ask `GX` and `LG` (the
latter as `LabUniq` beside its `GFL`) in place of `GD`.

* `kuSteps`: the local steps (`RawInvCLKUSplit.lean`, `RawInvCLKUCopy.lean`);
  **`kuRun_plain`**: `KURun` of every run on `PlainN`, with no hypothesis.
* `GXL r l`, `GX r goal`; `gx_of_count` (the count keeps them).
* `lzS_iff_kimLz` (G's `LzS` and `kimLz` are the same predicate),
  `lzS_dn_of_gxl` (`GX` gives G's `LzS (DN r)`).
* **`KIMidX C env`**: the clauses `run` (on the class `C`, `GX ∧ LG` in and
  out), `split`, `into`, `past` (`GX` and `LL` of the parts), `dn`.
* **`kimidX_plain env : KIMidX PlainN env`**, with no hypothesis.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The induction with its steps -/

theorem kuSteps : KUSteps S Map :=
  ⟨kus_split, kus_into, kuc_copy, kuc_past, kus_mede, kuc_collapse, kuc_kerf, kus_forl, kus_doneBlocks⟩

/-- **Every run on `PlainN` has the state-free count and keeps `LG`.** -/
theorem kuRun_plain (env : CallEnv) :
    ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), KURun (runLC (S := S) (Map := Map) env sup nm) :=
  kuRun_plainOf env kuSteps

/-! ## Distinct registers across the tree -/

/-- **The registers of the whole tree are distinct and below `r`.** -/
def GXL (r : Nat) (l : Lazy S) : Prop := (sarR l).Nodup ∧ ∀ y ∈ sarR l, y < r

/-- The same of a goal (true of `%pick` and `%done`). -/
def GX (r : Nat) : CGoalL S → Prop
  | CGoalL.next laz _ => GXL r laz
  | _ => True

theorem gx_sarG {r : Nat} {goal : CGoalL S} (h : GX r goal) : (sarG goal).Nodup ∧ ∀ y ∈ sarG goal, y < r := by
  cases goal with
  | next laz th => exact h
  | pick z o => exact ⟨List.nodup_nil, fun y hy => absurd hy List.not_mem_nil⟩
  | done => exact ⟨List.nodup_nil, fun y hy => absurd hy List.not_mem_nil⟩

/-- **The count keeps distinctness and the bound.** -/
theorem gx_of_count {r r' : Nat} {ri ro : List Nat} (hn : ri.Nodup) (hb : ∀ y ∈ ri, y < r) (hr : r ≤ r')
    (hc : ∀ y, ro.count y ≤ ri.count y + fr r r' y) : ro.Nodup ∧ ∀ y ∈ ro, y < r' := by
  have c1 := count_le_one_of_nodup hn
  refine ⟨nodup_of_count fun y => ?_, fun y hy => ?_⟩
  · have := hc y
    by_cases hy : y ∈ ri
    · have : fr r r' y = 0 := by
        have := hb y hy; unfold fr; split <;> omega
      have := c1 y; omega
    · have := List.count_eq_zero.mpr hy; have := fr_le_one r r' y; omega
  · have h0 := List.count_pos_iff.mpr hy
    have := hc y
    by_cases hi : y ∈ ri
    · exact Nat.lt_of_lt_of_le (hb y hi) hr
    · have := List.count_eq_zero.mpr hi
      exact (fr_pos (a := r) (b := r') (by omega)).2

theorem gxl_parts {r : Nat} {a b : Lazy S} (h : (sarR a ++ sarR b).Nodup ∧ ∀ y ∈ sarR a ++ sarR b, y < r) :
    GXL r a ∧ GXL r b := by
  obtain ⟨hn, hb⟩ := h
  obtain ⟨na, nb, -⟩ := List.nodup_append.mp hn
  exact ⟨⟨na, fun y hy => hb y (List.mem_append_left _ hy)⟩, ⟨nb, fun y hy => hb y (List.mem_append_right _ hy)⟩⟩

theorem gxl_up {r r' : Nat} {l : Lazy S} (h : GXL r l) (hr : r ≤ r') : GXL r' l :=
  ⟨h.1, fun y hy => Nat.lt_of_lt_of_le (h.2 y hy) hr⟩

/-! ## Track G's `LzS` -/

theorem lzS_of_kimLz {Q : Sure S → Prop} {l : Lazy S} (h : kimLz Q l) : Glue.LzS Q l := by
  induction h with
  | mk h1 _ _ _ i2 i3 i4 => exact Glue.LzS.mk h1 i2 i3 i4

theorem kimLz_of_lzS {Q : Sure S → Prop} {l : Lazy S} (h : Glue.LzS Q l) : kimLz Q l := by
  induction h with
  | mk h1 _ _ _ i2 i3 i4 => exact kimLz.mk h1 i2 i3 i4

/-- **Track G's `LzS` is `kimLz`.** -/
theorem lzS_iff_kimLz {Q : Sure S → Prop} {l : Lazy S} : Glue.LzS Q l ↔ kimLz Q l :=
  ⟨kimLz_of_lzS, lzS_of_kimLz⟩

theorem kim_count_flatMap {f : Nat × Lazy S → List Nat} : ∀ {L : List (Nat × Lazy S)} {e : Nat × Lazy S},
    e ∈ L → ∀ y, (f e).count y ≤ (L.flatMap f).count y
  | [], _, h => absurd h List.not_mem_nil
  | a :: rest, e, h => fun y => by
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := kim_count_flatMap (f := f) h y; omega

theorem dn_of_count {r : Nat} {L : List Nat} {s : Sure S} (hL : L.Nodup ∧ ∀ y ∈ L, y < r)
    (hc : ∀ y, (flattenNeed s.ned).count y ≤ L.count y) : Glue.DN r s := by
  refine ⟨distinct_of_nodup (nodup_of_count fun y => Nat.le_trans (hc y) (count_le_one_of_nodup hL.1 y)),
    fun x hx => hL.2 x ?_⟩
  have h0 := List.count_pos_iff.mpr ((mem_flatten s.ned x).mpr hx)
  exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le h0 (hc x))

/-- **`GX` gives track G's `LzS (DN r)`**: every sure need of the tree has
distinct registers below `r`. -/
theorem lzS_dn_of_gxl {r : Nat} {l : Lazy S} (h : GXL r l) : Glue.LzS (Glue.DN r) l := by
  refine lzS_of_kimLz (kim_ofE (Q := Glue.DN r) l ?_ fun e he => ?_)
  · exact dn_of_count h fun y => by
      show _ ≤ (flattenNeed l.sure.ned ++ regsL (entries l)).count y
      rw [List.count_append]; omega
  · exact dn_of_count h fun y => by
      show _ ≤ (flattenNeed l.sure.ned ++ regsL (entries l)).count y
      rw [List.count_append]
      have := kim_count_flatMap (f := fun e : Nat × Lazy S => flattenNeed e.2.sure.ned) he y
      simp only [regsL] at this ⊢
      omega

/-! ## The corrected mid-run fact -/

/-- **Track G's `KIMid` with `GX ∧ LG` in place of `GD`** (on a class `C`
of nomms): runs, `+split`, `+into` and `+past` keep "the registers of the
whole tree distinct and below `re`" and "bonds and forks at distinct labels,
the entries below `bo`"; and that gives `GD`. -/
structure KIMidX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map]
    (C : Nomm → Prop) (env : CallEnv) : Prop where
  run : ∀ nm sup, C nm → ∀ (goal : CGoalL S) region (g g' : Comp.Gen Map) (x : NextL S),
    GX g.re goal → LG goal g → runLCM env true sup nm goal region g = some (x, g') →
    GX g'.re x.goal ∧ LG x.goal g'
  split : ∀ (nex : NextL S) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat), GXL g.re nex.laz →
    LL nex.laz g → splitL nex g = some (x, g') →
    GXL g'.re x.1 ∧ GXL g'.re x.2.1 ∧ LL x.1 g' ∧ LL x.2.1 g'
  into : ∀ (nex : NextL S) (axe : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat), GXL g.re nex.laz →
    LL nex.laz g → intoL nex axe g = some (x, g') →
    GXL g'.re x.1 ∧ GXL g'.re x.2.1 ∧ LL x.1 g' ∧ LL x.2.1 g'
  past : ∀ (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) (g g' : Comp.Gen Map)
    (x : NextL S), GXL g.re nex.laz → LL nex.laz g → pastL cod nex nom region g = some (x, g') →
    GXL g'.re x.laz ∧ LL x.laz g'
  dn : ∀ (r : Nat) (l : Lazy S), GXL r l → Glue.LzS (Glue.DN r) l

/-- The two halves of `+split` / `+into` from the count and the labels. -/
theorem kim_halves {m : CM Map (Lazy S × Lazy S × Nat)} {l : Lazy S}
    (hk : KUC (Map := Map) (sarR l) m (fun x => sarR x.1 ++ sarR x.2.1))
    (hlab : ∀ (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat), m g = some (x, g') → LabUniq l →
      (∀ e ∈ entries l, e.1 < g.bo) →
      LabUniq x.1 ∧ LabUniq x.2.1 ∧ (∀ e ∈ entries x.1, e.1 < g.bo) ∧ ∀ e ∈ entries x.2.1, e.1 < g.bo)
    {g g' : Comp.Gen Map} {x : Lazy S × Lazy S × Nat} (hg : GXL g.re l) (hl : LL l g) (h : m g = some (x, g')) :
    GXL g'.re x.1 ∧ GXL g'.re x.2.1 ∧ LL x.1 g' ∧ LL x.2.1 g' := by
  obtain ⟨le, bo, c⟩ := hk g x g' h
  obtain ⟨A, B⟩ := gxl_parts (gx_of_count hg.1 hg.2 le c)
  obtain ⟨u1, u2, q1, q2⟩ := hlab g g' x h hl.1 hl.2
  exact ⟨A, B, ⟨u1, fun e he => Nat.lt_of_lt_of_le (q1 e he) bo⟩, ⟨u2, fun e he => Nat.lt_of_lt_of_le (q2 e he) bo⟩⟩

/-- **Track G's mid-run fact, corrected, on `PlainN`**, with no hypothesis. -/
theorem kimidX_plain (env : CallEnv) : KIMidX S Map PlainN env where
  run := fun nm sup hp goal region g g' x hx hl h => by
    rw [runLCM_true env (plainN_noDirect nm hp) sup goal region] at h
    obtain ⟨lg, le, -, c⟩ := kuRun_plain env nm hp sup goal region g g' x hl h
    have G := gx_sarG hx
    exact ⟨gx_of_count G.1 G.2 le c, lg⟩
  split := fun nex g g' x hg hl h =>
    kim_halves (kus_split nex) (fun g g' x h u q => by
      obtain ⟨a, b, c⟩ := x; exact lab_splitL (Q := (· < g.bo)) h u q) hg hl h
  into := fun nex axe g g' x hg hl h =>
    kim_halves (kus_into nex axe) (fun g g' x h u q => by
      obtain ⟨a, b, c⟩ := x; exact lab_intoL (Q := (· < g.bo)) h u q) hg hl h
  past := fun cod nex nom region g g' x hg hl h => by
    obtain ⟨le, -, c⟩ := kuc_past cod nex nom region g x g' h
    exact ⟨gx_of_count hg.1 hg.2 le c, lab_pastL h hl.1 hl.2⟩
  dn := fun r l h => lzS_dn_of_gxl h

end Raw
end SkaModel
end Formalization
