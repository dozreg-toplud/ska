import lemmas.Ska.RawInvCheckCX
import lemmas.Glue.GuardCallsB

/-!
# Track G's `KIMid` is false: the witness

README Gaps 14 (b), track D.  The run clause of track G's `KIMid`
(`Glue/GuardCallsB.lean`) asks only `GD` of the goal: each sure need of
its tree has distinct registers below `re`.  The goal `kwGoal` meets it at
`re = 3`: its root is `bunt` and it has two bonds at the SAME label `1`,
with the needs `[0 1]` and `[2 0]` (register `0` in both).  The nomm
`[[0 2] [0 3]]` (`PlainN`, `NoSixC`) splits the goal (`hed` gets `0` and
`2`, `tel` gets `1` and `0`), runs `[0 3]` and `[0 2]`, and `+copy` merges
each of `first`'s two bonds at `1` with `second`'s last bond at `1`, so the
result's first bond needs `[0 0]`: register `0` twice in one sure need.

* `kw_bonds`: the needs of the result's bonds, by the kernel
  (`decide +kernel`: no `native_decide`, no axiom).
* `kw_gd`: the goal meets `GD 3`.
* **`kimid_false : ¬ Glue.KIMid LS FM envR`**.

The corrected fact is `KIMidX` (`RawInvCLKIMidU.lean`): `GX` (distinct
registers across the WHOLE tree) and `LG` (bonds at distinct labels) in
place of `GD`; it is proved on `PlainN` (`kimidX_plain`).
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

def kwS (a b : Nat) : Sure LS := ⟨Need.pair (Need.this a) (Need.this b), HoonSet.empty⟩

/-- Two bonds at label `1` sharing register `0`. -/
def kwGoal : CGoalL LS := CGoalL.next (mk Sure.bunt [] [(1, ofSure (kwS 0 1)), (1, ofSure (kwS 2 0))]) (jmp0 2)

def kwGen : Comp.Gen FM := { gB with re := 3 }

def kwNm : Nomm := Nomm.cons (Nomm.n0 2) (Nomm.n0 3)

/-- **The needs of the result's bonds** (the first holds `0` twice). -/
theorem kw_bonds : (runLCM (S := LS) (Map := FM) envR true Option.none kwNm kwGoal [] kwGen).map
    (fun p => p.1.laz.bond.map fun e => e.2.sure.ned) =
    some [Need.pair (Need.this 0) (Need.this 0), Need.pair (Need.this 2) (Need.this 0)] := by
  decide +kernel

theorem kw_dn {a b : Nat} (hab : a ≠ b) (ha : a < 3) (hb : b < 3) : Glue.DN 3 (kwS a b) := by
  refine ⟨⟨trivial, trivial, fun x hx hx' => ?_⟩, fun x hx => ?_⟩
  · simp only [NMem] at hx hx'; omega
  · simp only [kwS, NMem] at hx; omega

/-- **The goal meets `GD`.** -/
theorem kw_gd : Glue.GD kwGen.re kwGoal := by
  refine Glue.LzS.mk (Glue.dn_bunt 3) (fun e he => absurd he List.not_mem_nil)
    (fun e he => absurd he List.not_mem_nil) fun e he => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact Glue.lzS_ofSure (kw_dn (by decide) (by decide) (by decide))
  · exact Glue.lzS_ofSure (kw_dn (by decide) (by decide) (by decide))

/-- **Track G's `KIMid` is false** (its run clause, at `LS`, `FM`, `envR`). -/
theorem kimid_false : ¬ Glue.KIMid LS FM envR := by
  intro h
  have hb := kw_bonds
  cases hr : runLCM (S := LS) (Map := FM) envR true Option.none kwNm kwGoal [] kwGen with
  | none => rw [hr] at hb; cases hb
  | some p =>
    obtain ⟨x, g'⟩ := p
    have hz := h.run kwNm Option.none ⟨trivial, trivial⟩ kwGoal [] kwGen g' x kw_gd hr
    rw [hr] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    obtain ⟨⟨s, f, b⟩, th⟩ := x
    change Glue.LzS (Glue.DN g'.re) (mk s f b) at hz
    change List.map (fun e : Nat × Lazy LS => e.2.sure.ned) b = _ at hb
    cases hz with
    | mk _ _ _ hB =>
      match b, hb, hB with
      | e1 :: _, hb, hB =>
        simp only [List.map_cons, List.cons.injEq] at hb
        have hd := (hB e1 List.mem_cons_self).root.1
        rw [hb.1] at hd
        exact hd.2.2 0 (by simp [NMem]) (by simp [NMem])

end Raw
end SkaModel
end Formalization
