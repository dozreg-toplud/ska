import lemmas.Glue.GuardCallsX
import lemmas.Glue.NskProxy
import lemmas.Ska.RawInvCLPlainD

/-!
# The plain classes and the guard with calls over `KIMidX` (track G, fifteenth pass)

The entry leaves of the plain classes WITHOUT the false `KIMid` (misfit 8):
the proofs of `guardMonoC_plainE` (`Glue/ProxPlain.lean`),
`guardNaryC_plain` (`Glue/GuardNaryPlain.lean`) and `guardMonoC_noSixN`
(`Glue/ProxCalls.lean`), with `top_kerfAX` / `runGX_lcm`
(`Glue/GuardCallsX.lean`, no hypothesis) in place of `top_kerfA (hD env)` /
`runG_lcm (hD env)`; nothing else in the proofs changes.

* **`entryMono_plainKX`**: `EntryMono` on `PlainM`, NO hypothesis;
* **`entryNary_plainX`**: `EntryNary` on `PlainNC`, NO hypothesis;
* `guardMonoC_noSixNX` (from `KeyUndefC`, `NskEndC`), **`guardMonoC_noSixWX`**
  (from `KeyUndefC` (D) and the frame target `SDWEndC` (G)): `GuardMonoC` on
  `NoSixM`, the guard of the class with direct calls (with `StraightA`:
  `guardMonoC_noSixX`);
* `noSix_of_plainD`: track D's `PlainD` has no `%6`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## `PlainM`, `PlainNC` -/

/-- **`GuardMonoC` on `PlainM`** from `ProxEndN` (no `KIMid`). -/
theorem guardMonoC_plainEX (hP : ∀ env, ProxEndN S Map env) :
    GuardMonoC S Map PlainM := by
  intro env N bl nm c hf hs
  have hn : NoSixC nm := noSix_of_plain nm hf
  unfold finishLUCM at hs
  obtain ⟨⟨nex, g1⟩, h1, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨K, hI, hfo⟩ := top_kerfAX env hn h1 h2
  have P := hP env nm hf nex g1 g2 o sub h1 h2
  dsimp only at hs
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at hs
  simp only [flattenNeed, List.headD, List.length] at hs
  obtain ⟨start, hst, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hs
  have P0 := proxOKN_start P hst
  have B1 := blocksOKA_npN (blocksOKA_start hI.ok hfo.2 hst) P0
  have R := celAnn_renameN B1 (renA_proxN P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`EntryMono` on `PlainM`, with no hypothesis** (track D's
`optInMono_plain`, `readsInMono_plain`; `splitDefEnd_plain`). -/
theorem entryMono_plainKX (lib : Lib) : EntryMono S Map lib PlainM :=
  entryMono_of lib optInMono_plain readsInMono_plain (guardMonoC_plainEX fun env => proxEndN_of splitDefEnd_plain)

/-- **`GuardNaryC` on `PlainNC`** (no `KIMid`). -/
theorem guardNaryC_plainX : GuardNaryC S Map PlainNC := by
  intro env N bl cape bake nm ord c hf hs
  obtain ⟨hp, hbake⟩ : PlainN nm ∧ ∀ ned, bake ned = (ned, []) := hf
  unfold finishLFC at hs
  obtain ⟨⟨nex, g1⟩, h1, hA⟩ := Option.bind_eq_some_iff.mp hs
  simp only at hA
  split at hA
  · cases hA
  obtain ⟨⟨nedF, g2⟩, h2, hB⟩ := Option.bind_eq_some_iff.mp hA
  rw [hbake] at hB
  simp only [List.map_nil] at hB
  obtain ⟨⟨u3, g3⟩, h3, hC⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨⟨u4, g4⟩, h4, hT⟩ := Option.bind_eq_some_iff.mp hC
  cases u3; cases u4
  -- `InvA` through the top run
  have hn : NoSixC nm := noSix_of_plain nm hp
  have h1M : runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1) := by
    rw [runLCM_eq env true nm (by simp [plainN_noDirect nm hp])]; exact h1
  obtain ⟨K1, hI1, X1, hR1⟩ := (runGX_lcm env nm hn Option.none (fun _ _ => False) 1 0 CGoalL.done [] trivial
    ⟨trivial, trivial⟩).k _ gen0 nex g1 invA_gen0 (by simp [gen0]) (XB.refl _ _ _) h1M
  have h0 : 0 < g1.bo := Nat.lt_of_lt_of_le (by simp [gen0]) X1.1
  -- track D's `IL` for the entries' needs
  obtain ⟨J1, -⟩ := liveRun_plain_topOfL env (armsLL_of env splitSpecL intoSpecL) hp h1
  have I1 : IL (fun _ _ => False) (CGoalL.next nex.laz nex.th) g1 := J1
  obtain ⟨-, -, hent⟩ := (I1.goal : GoalL g1 (CGoalL.next nex.laz nex.th))
  -- `+need-ord-alloc-regs`
  have ND := nary_noKey hp h1 h2 h3 h4
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  have hb2 : g2.bo = g1.bo := by rw [e2]
  have hI2 : InvA K1 g2 := by rw [e2]; exact ⟨hI1.ok, hI1.drop, hI1.below, hI1.kin⟩
  -- `+coerce-lazy`
  have hL : ∀ e ∈ (nex.th.there, nex.laz) :: entries nex.laz,
      FL K1 g2.bo e.1 ∧ Distinct e.2.sure.ned ∧ NB g1.re e.2.sure.ned := by
    intro e he
    obtain ⟨-, ds, hr⟩ := hent e he
    refine ⟨?_, ds, fun y hy => (hr y hy).1⟩
    rw [hb2]
    rcases List.mem_cons.mp he with rfl | he
    · exact hR1.1
    · exact lzL_ent nex.laz hR1.2.2 e he
  obtain ⟨K3, hI3, X3, -⟩ := (kpa_coerceLazyL g1.re g2.re nedF cape nex.th.there nex.laz (K0 := K1) (b0 := g2.bo)
    (r0 := g2.re) hL mF l2 (Nat.le_refl _)).k K1 g2 () g3 hI2 (by rw [hb2]; exact h0) (XB.refl _ _ _) h3
  have hfo3 : FL K3 g3.bo nex.th.there := ((hL _ List.mem_cons_self).1).up X3
  -- the empty bake
  have h03 : 0 < g3.bo := Nat.lt_of_lt_of_le (by rw [hb2]; exact h0) X3.1
  obtain ⟨K4, hI4, X4, -⟩ := (KPA.addOps' (K0 := K3) (b0 := g3.bo) (r0 := g3.re)
    (guardedBody_of_noSplit noSplit_nil) hfo3).k K3 g3 () g4 hI3 h03 (XB.refl _ _ _) h4
  have hfo : FL K4 g4.bo nex.th.there := hfo3.up X4
  -- the proxy facts
  have s1 := ((ks_runLC (S := S) (Map := Map) env nm hp Option.none CGoalL.done []).k _ _ _ sds_gen0 h1).1
  have s2 : SDS g2 := by rw [e2]; exact s1
  have s3 := ((ks_coerceLazyL nedF cape nex.th.there nex.laz).k _ _ _ s2 h3).1
  have s4 := ((KS.addOps' (Map := Map) nex.th.there (sdBody_of_noSplit noSplit_nil)).k _ _ _ s3 h4).1
  have dq : ∀ k b, HoonMap.get g4.blocks k = some b → ∀ q ∈ b.body, ∀ x, aliasDst q = some x →
      Defd g4.blocks x := by
    intro k b hb q hq x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    exact ⟨(k, some i), b, q, hb, hi, hx⟩
  have P : ProxOKN g4.blocks g4.cond := by
    refine ⟨fun k b hb x hx => ND x ?_, fun k b hb p hpb s hs => ND s ?_⟩
    · rcases hx with hx | ⟨q, hq, hx⟩
      · exact ⟨(k, Option.none), b, hb, hx⟩
      · exact dq k b hb q hq x hx
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpb
      obtain ⟨j, -, q, hq, hx⟩ := s4 k b hb i p s hi hs
      exact dq k b hb q (List.mem_of_getElem? hq) s hx
  -- the final pass: the renaming path
  rw [toStraightF_run _ _ _ (isRun_needOrdAllocRegs h2)] at hT
  obtain ⟨start, hst, hT⟩ := Option.bind_eq_some_iff.mp hT
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hT
  have P0 := proxOKN_start P hst
  have B1 := blocksOKA_npN (blocksOKA_start hI4.ok hfo.2 hst) P0
  have R := celAnn_renameN B1 (renA_proxN P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`EntryNary` on `PlainNC`, with no hypothesis** (track D's
`optInNary_plain`, `readsInNary_plain`). -/
theorem entryNary_plainX (lib : Lib) : EntryNary S Map lib PlainNC :=
  entryNary_of lib optInNary_plain readsInNary_plain guardNaryC_plainX

/-! ## `NoSixM`: the guard of the class with direct calls -/

/-- **`GuardMonoC` on `NoSixM`** from `KeyUndefC` (D) and `NskEndC` (no `KIMid`). -/
theorem guardMonoC_noSixNX (hK : ∀ env, KeyUndefC S Map env)
    (hN : ∀ env, NskEndC S Map env) : GuardMonoC S Map NoSixM := by
  intro env N bl nm c hn hs
  unfold finishLUCM at hs
  obtain ⟨⟨nex, g1⟩, h1, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨K, hI, hfo⟩ := top_kerfAX env hn h1 h2
  have P := proxEndC_of (hK env) (hN env) hn h1 h2
  dsimp only at hs
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at hs
  simp only [flattenNeed, List.headD, List.length] at hs
  obtain ⟨start, hst, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hs
  have P0 := proxOKN_start P hst
  have B1 := blocksOKA_npN (blocksOKA_start hI.ok hfo.2 hst) P0
  have R := celAnn_renameN B1 (renA_proxN P0 _ _) hnew
  exact ⟨R.1, _, R.2⟩

/-- **`GuardMonoC` on `NoSixM`** from `KeyUndefC` (D) and the frame target
`SDWEndC` (G). -/
theorem guardMonoC_noSixWX (hK : ∀ env, KeyUndefC S Map env) (hW : ∀ env, SDWEndC S Map env) :
    GuardMonoC S Map NoSixM :=
  guardMonoC_noSixNX hK fun env => nskEndC_of (hK env) (hW env)

/-- **Track D's `PlainD` has no `%6`.** -/
theorem noSix_of_plainD : ∀ nm : Nomm, Raw.PlainD nm → NoSixC nm
  | Nomm.cons p q, h => ⟨noSix_of_plainD p h.1, noSix_of_plainD q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q _, h => ⟨noSix_of_plainD p h.1, noSix_of_plainD q h.2⟩
  | Nomm.n3 p, h => noSix_of_plainD p h
  | Nomm.n4 p, h => noSix_of_plainD p h
  | Nomm.n5 p q, h => ⟨noSix_of_plainD p h.1, noSix_of_plainD q h.2⟩
  | Nomm.n6 _ _ _, h => h.elim
  | Nomm.n7 p q, h => ⟨noSix_of_plainD p h.1, noSix_of_plainD q h.2⟩
  | Nomm.n10 _ v q, h => ⟨noSix_of_plainD v h.1, noSix_of_plainD q h.2⟩
  | Nomm.n11s _ _ _, h => h.elim
  | Nomm.n11d _ _ _ _, h => h.elim
  | Nomm.n12 _ _, h => h.elim
  | Nomm.mean _ _ _ _ _, h => h.elim

end Glue
end SkaModel
end Formalization
