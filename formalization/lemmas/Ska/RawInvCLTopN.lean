import lemmas.Ska.RawInvCLTopU
import lemmas.Ska.RawInvFinishX

/-!
# Raw `+comp` output with calls: the n-ary pass

README Gaps 14 (b), track D.  `finishLFC` (`+compile-scc-in`'s final pass
with `runLC`) on `PlainN`, nothing baked: the run under `%done` from
`gen0`, `+need-ord-alloc-regs` (fresh registers `nedF`), `+coerce-lazy`
(ops in front of the result's entries that define each entry's sure need
from `nedF`), the empty bake, then `+to-straight`, which on the run `nedF`
renames by `renReg ∘ unproxy` (`toStraightF_run`).  As in
`RawInvCLTopU.lean`, the proof goes through the unproxied blocks:

* `tn_sip`: `IL` and `SAB` of the run's state give `SIP` with no block
  predicate, so `coI_step` (`raw_coerceP`) of `FragX` runs `+coerce-lazy`
  unchanged; the invariant `CoD` adds where the definitions come from (old,
  an entry's need, or fresh), so that unproxying fixes them
  (`tn_step`);
* the liveness: the top run's `LiveC` under `%done` (nothing live at the
  entry once the entries define their needs) and `live_entry_of_prep` with
  the unproxied ops (they read first only `nedF`).

**Open (checked, not proved): `TopSAR`**, `SAB` of the raw blocks at the
end of the top run (checked on all 2,856 `PlainN` nomms of `enumCX`:
`chkSARun` of `RawInvCLCheckSA.lean`, 0 failures).

* **`optIn_finishLFC_of`**, **`readsIn_finishLFC_of`** (with
  `c.nargs = countArgs c.need`), from `SplitSpecL`, `IntoSpecL`, `TopSAR`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Open (checked on `PlainN`): `SAB` of the raw blocks at the end of the
top run.** -/
def TopSAR (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (nm : Nomm) : Prop :=
  ∀ (nex : NextL S) (g1 : Comp.Gen Map),
    runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) → SAB g1.blocks

/-- `IL` and single assignment give `SIP` with no block predicate. -/
theorem tn_sip {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) (hs : SAB g.blocks) :
    SIP (fun _ : Map Blob => True) (fun k => 3 * k) 0 g := by
  obtain ⟨d, b1, hb⟩ := hI.ats
  refine ⟨d, b1, fun k b h => (hb k b h).1, hI.regs, hs.nd, hs.cr, hs.tr, fun k b h j hj => ?_, Nat.zero_le _,
    fun _ _ => rfl, fun x hx => absurd hx (Nat.not_lt_zero _), trivial⟩
  have := (hb k b h).2.2.2 j (by rw [← getJmps_eq]; exact hj)
  show 3 * _ < 3 * _
  omega

/-- Where the definitions of the state come from during `+coerce-lazy`. -/
def CoD (R0 : Nat) (full : List (Nat × Lazy S)) (bl0 : Map Blob) (rest : List (Nat × Lazy S))
    (g : Comp.Gen Map) : Prop :=
  (∀ e ∈ rest, e ∈ full) ∧ ∀ y, Defd g.blocks y → Defd bl0 y ∨ (∃ e ∈ full, NMem e.2.sure.ned y) ∨ R0 ≤ y

/-- **One step of `+coerce-lazy` keeps `CoI` and `CoD`.** -/
theorem tn_step {R0 R : Nat} (hR0 : R0 ≤ R) {ned : Need} {less : Cape} {full : List (Nat × Lazy S)}
    {bl0 : Map Blob} {o : Nat} {l : Lazy S} {rest : List (Nat × Lazy S)} {g g' : Comp.Gen Map} {u : Unit}
    (hI : CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 ned R ((o, l) :: rest) g ∧
      CoD R0 full bl0 ((o, l) :: rest) g)
    (h : coerceLazy ned o l.sure less g = some (u, g')) :
    (CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 ned R rest g' ∧ CoD R0 full bl0 rest g') ∧
      CoerceStep ned g g' o l := by
  obtain ⟨C', st⟩ := coI_step hI.1 h
  refine ⟨⟨C', fun e he => hI.2.1 e (List.mem_cons_of_mem _ he), fun y d => ?_⟩, st⟩
  obtain ⟨S0, hR, hn, -, he⟩ := hI.1
  obtain ⟨⟨b, hb⟩, dl, hl⟩ := he (o, l) List.mem_cons_self
  obtain ⟨-, -, -, A, get1, -, -, df1⟩ := raw_coerceP S0 hb
    (fun y hy => by have := (hn y hy).1; omega) dl (fun y hy => by have := (hl y hy).1; omega)
    (fun y hy e => (hl y e).2.1 hy) (fun y hy => (hl y hy).2.2) h
  rcases (defd_of_ifget hb get1).mp d with d | d
  · exact hI.2.2 y d
  · rcases df1 y d with m | ⟨m, -⟩
    · exact Or.inr (Or.inl ⟨(o, l), hI.2.1 _ List.mem_cons_self, m⟩)
    · exact Or.inr (Or.inr (by omega))

variable [MapKeys Map]

/-- **The n-ary pass with calls on `PlainN`**: `OptIn`, `ReadsIn` at the
argument count, which is that of the need. -/
theorem tn_all (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm} (hp : PlainN nm)
    (hsa : TopSAR S Map env nm) {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) :
    OptIn c.blocks ∧ Compiler.ReadsIn c.nargs c.blocks ∧ c.nargs = countArgs c.need := by
  unfold finishLFC at h
  obtain ⟨⟨nex, g1⟩, h1, hA⟩ := Option.bind_eq_some_iff.mp h
  simp only at hA
  split at hA
  · cases hA
  obtain ⟨⟨nedF, g2⟩, h2, hB⟩ := Option.bind_eq_some_iff.mp hA
  rw [hbake] at hB
  simp only [List.map_nil] at hB
  obtain ⟨⟨u3, g3⟩, h3, hC⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨⟨u4, g4⟩, h4, hT⟩ := Option.bind_eq_some_iff.mp hC
  obtain ⟨J1, L1⟩ := liveRun_plain_topOfL env (armsLL_of env hS hI) hp h1
  have I1 : IL (fun _ _ => False) (CGoalL.next nex.laz nex.th) g1 := J1
  have SA1 := hsa nex g1 h1
  have S1 := tn_sip I1 SA1
  obtain ⟨-, hap, hent⟩ := (I1.goal : GoalL g1 (CGoalL.next nex.laz nex.th))
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  subst e2
  have l2' : g1.re ≤ k2 := l2
  -- `+coerce-lazy`
  have I0 : CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 nedF k2
      ((nex.th.there, nex.laz) :: entries nex.laz) { g1 with re := k2 } := by
    refine ⟨sip_reg S1 l2', Nat.le_refl _, fun r hr => ⟨(mF r hr).2, fun d => ?_⟩, hap, fun e he => ?_⟩
    · have := S1.defd_lt d; have := (mF r hr).1; omega
    · obtain ⟨⟨b, hb, -⟩, ds, hr⟩ := hent e he
      exact ⟨⟨b, hb⟩, ds, fun r hm => ⟨by have := (hr r hm).1; omega,
        fun m => by have := (hr r hm).1; have := (mF r m).1; omega, (hr r hm).2⟩⟩
  obtain ⟨⟨I3, D3⟩, P, pP, kP, rP, -⟩ := coerceLazyL_prepI (S := S) (Map := Map)
    (fun rest g => CoI (fun _ : Map Blob => True) (fun k => 3 * k) 0 nedF k2 rest g ∧
      CoD g1.re ((nex.th.there, nex.laz) :: entries nex.laz) g1.blocks rest g)
    (fun _ _ _ _ _ _ hI hs => tn_step l2' hI hs) ⟨I0, fun e he => he, fun y d => Or.inl d⟩ h3
  -- the empty bake
  have hd3 : g3.drop = false := I3.1.drop
  obtain ⟨S4, b4, hb4, e4, -, -⟩ := sip_addOps I3.1 (opsOK_nil g3) h4
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k => by
    rw [e4]
    by_cases e : k = nex.th.there
    · subst e; rw [get_put_self, hb4, pre_nil]
    · rw [get_put_ne e]
  have c4 : g4.cond = g1.cond := by
    obtain ⟨b4', -, e4'⟩ := addOps_spec h4 hd3
    have k3 : g3.cond = g1.cond := (kc_coerceLazyL nedF less _ _).keep { g1 with re := k2 } _ _ h3
    rw [e4']
    exact k3
  have pP4 : Prep P g1.blocks g4.blocks := fun k => by rw [get4 k]; exact pP k
  have dd4 : ∀ y, Defd g4.blocks y → Defd g3.blocks y := fun y d => by
    obtain ⟨o, b, hb, m⟩ := defd_iff.mp d
    exact defd_iff.mpr ⟨o, b, by rw [← get4]; exact hb, m⟩
  -- keys of `cond`
  have uD : ∀ x, Defd g4.blocks x → unproxy g4.cond x = x := fun x d => by
    rw [c4]
    apply unproxy_none
    cases e : HoonMap.get g1.cond x with
    | none => rfl
    | some v =>
      obtain ⟨k1, k2', k3, -, -⟩ := I1.cond x v e
      rcases D3.2 x (dd4 x d) with d1 | ⟨e', he', m⟩ | hx
      · exact absurd d1 k2'
      · exact absurd ⟨e', he', m⟩ k3
      · omega
  have uG : ∀ x, ((∃ e ∈ (nex.th.there, nex.laz) :: entries nex.laz, NMem e.2.sure.ned x) ∨ g1.re ≤ x) →
      unproxy g1.cond x = x := fun x hx => by
    apply unproxy_none
    cases e : HoonMap.get g1.cond x with
    | none => rfl
    | some v =>
      obtain ⟨k1, -, k3, -, -⟩ := I1.cond x v e
      rcases hx with hx | hx
      · exact absurd hx k3
      · omega
  -- the final pass
  rw [toStraightF_run _ _ _ (isRun_needOrdAllocRegs h2)] at hT
  obtain ⟨start, hst, hT⟩ := Option.bind_eq_some_iff.mp hT
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp hT
  rw [tu_proxRen] at hnew
  have D1 : Down g1.blocks := down_of_ats I1.ats
  have D4 : Down g4.blocks := downRk_prep pP4 (Down.rank D1)
  obtain ⟨-, R1, W1⟩ := stIn_of_ats I1.ats
  have args4 : ∀ k b j a, HoonMap.get g4.blocks k = some b → j ∈ getJmps b.fin → some a ∈ j.args →
      a ∈ blockDefs b := by
    intro k b j a hb hj ha
    obtain ⟨b0, hb0, rfl⟩ := get_prep pP4 hb
    exact mem_blockDefs_pre.mpr (Or.inl (SA1.args k b0 j a hb0 hj ha))
  have o1 : 1 ≤ nex.th.there := (D4 _ start hst).1
  have o0 : nex.th.there ≠ 0 := by omega
  have RD := rankDown_start (Down.rank D4) hst
  have gs8 := get_mapVals (renBlob (unproxy g4.cond)) (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)
  have hnew8 : ∀ k b', HoonMap.get new k = some b' →
      ∃ b, HoonMap.get (mapVals (renBlob (unproxy g4.cond))
          (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) k = some b ∧
        keepBlock (mapVals (renBlob (unproxy g4.cond)) (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start))
          (renReg ((flattenNeed nedF).headD 0) (flattenNeed nedF).length) k b = some (some b') := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := renameBlocks_get hnew hk
    refine ⟨renBlob (unproxy g4.cond) b, by rw [gs8, hb]; rfl, ?_⟩
    rw [keepBlock_ren RD gs8]; exact hkb
  have hst8 : HoonMap.get (unpM g4) nex.th.there = some (renBlob (unproxy g4.cond) start) := by
    simp only [unpM]; rw [get_mapVals, hst]; rfl
  have hbs0 : HoonMap.get (mapVals (renBlob (unproxy g4.cond))
      (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) 0 = some (renBlob (unproxy g4.cond) start) := by
    rw [gs8]; simp [HoonMap.get_put]
  have hbso : HoonMap.get (mapVals (renBlob (unproxy g4.cond))
      (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) nex.th.there = Option.none := by
    rw [gs8]; simp [HoonMap.get_put, HoonMap.get_del, o0]
  have hbsk : ∀ k, k ≠ 0 → k ≠ nex.th.there →
      HoonMap.get (mapVals (renBlob (unproxy g4.cond)) (HoonMap.put (HoonMap.del g4.blocks nex.th.there) 0 start)) k =
        HoonMap.get (unpM g4) k := fun k k0 ko => by
    simp only [unpM]; rw [gs8, get_mapVals]; simp [HoonMap.get_put, HoonMap.get_del, k0, ko]
  have hdB : DownRk id (unpM g4) := Down.rank (tu_down D4 _)
  -- the liveness at the entry
  have PP : Prep (fun k => (P k).map (renPole (unproxy g1.cond))) (unpM g1) (unpM g4) := by
    unfold unpM; rw [c4]; exact prep_mapVals pP4 _
  have hl : ∀ r, Live (unpM g4) nex.th.there r → NMem nedF r := fun r hr =>
    live_entry_of_prep PP (K := fun x y => (fun _ _ => False) x y ∨ lazK nex.th.there nex.laz x y)
      (fun k r hk => by
        rcases hk with hk | ⟨e, he, rfl, hm⟩
        · exact hk.elim
        · rw [defsOf_ren]
          exact List.mem_map.mpr ⟨r, kP e he r hm, uG r (Or.inl ⟨e, he, hm⟩)⟩)
      (fun r hk => L1 r hk)
      (fun k y hy => by
        obtain ⟨x, rfl, hx⟩ := opsRF_ren_back _ hy
        have hx' := rP k x hx
        rw [uG x (Or.inr (mF x hx').1)]
        exact hx') hr
  have hin : ∀ r, NMem nedF r → ¬ Defd (unpM g4) r := fun r hr d =>
    (I3.2.2.1 r hr).2 (dd4 r (tu_defd uD d))
  refine ⟨optIn_renOutR hst8 hbs0 hbso hbsk (renReg_inj _ _) (renReg_surj _ _) hnew8 hdB
    (tu_nodup uD S4.nd) (tu_cross uD S4.cr) (tu_noTr S4.tr _) (tu_downPar uD D4 S4.cr args4) hl hin, ?_, rfl⟩
  obtain ⟨-, -, -, -, c5⟩ := stOut_ren hst8 hbs0 hbso hbsk (renReg_inj _ _) (renReg_surj _ _) hnew8
    (renameBlocks_ren RD gs8 hnew) hdB (tu_arity (arityOK_prep pP4 R1) _) (tu_twoNA (twoNA_prep pP4 W1) _) hl
  refine readsIn_of_live fun r' hlv _ => ?_
  obtain ⟨r, rfl, hr⟩ := c5 r' hlv
  have hf : flattenNeed nedF = List.range' g1.re (k2 - g1.re) := flatten_needOrdAllocRegs ord g1 _ nedF h2
  have hm := (mem_flatten nedF r).mpr hr
  rw [hf, List.mem_range'_1] at hm
  show renReg ((flattenNeed nedF).headD 0) (flattenNeed nedF).length r < countArgs (needToOrd nedF)
  rw [countArgs_flatten, hf, List.length_range']
  obtain ⟨n, hn⟩ : ∃ n, k2 - g1.re = n + 1 := ⟨k2 - g1.re - 1, by omega⟩
  rw [hn, List.range'_succ, List.headD_cons]
  unfold renReg
  split <;> (try split) <;> omega

/-- **`OptIn` of the n-ary code with indirect calls on `PlainN`**, nothing
baked, from the specs of `+split` and `+into` and the open `TopSAR`. -/
theorem optIn_finishLFC_of (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm}
    (hp : PlainN nm) (hsa : TopSAR S Map env nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) : OptIn c.blocks :=
  (tn_all hS hI hp hsa hbake h).1

/-- **`ReadsIn` of the n-ary code with indirect calls on `PlainN`**, and its
argument count is that of its need. -/
theorem readsIn_finishLFC_of (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) {env : CallEnv} {nm : Nomm}
    (hp : PlainN nm) (hsa : TopSAR S Map env nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : finishLFC (S := S) (Map := Map) env nm ord less bake = some c) :
    Compiler.ReadsIn c.nargs c.blocks ∧ c.nargs = countArgs c.need :=
  (tn_all hS hI hp hsa hbake h).2

end Raw
end SkaModel
end Formalization
