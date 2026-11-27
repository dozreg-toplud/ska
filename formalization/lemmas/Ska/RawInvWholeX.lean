import lemmas.Ska.RawInvKernX
import lemmas.Ska.RawInvOutN
import lemmas.Ska.RawInvEApart
import lemmas.Ska.CompUnproxyTop

/-!
# Raw `+comp` output on `FragX`: the whole-subject pass

README Gaps 14, track D.  `finishLU` (`+compile-unary`, the version the
`%full` poke runs) on every nomm of `FragX`: the run, then `+kerf` (a hop
block `o` to the run's entry, and `+kern` from one fresh register `sub`,
with a proxy for `sub` at every lazy block other than `o`), then
`+to-straight`, which takes its map path whenever a proxy exists (on all
4,080 nomms of `enumX`).  On the input run `[sub]` the map path renames by
`ren ∘ unproxy` (`toStraightF_run`), which is not injective; by
`renameBlocks_ren` of track C its output is, label by label, the renaming
path by `ren` of the unproxied blocks.  So the proof goes through the
unproxied blocks `mapVals (renBlob u) g.blocks`:

* they are the raw blocks of the run plus the hop block, with ops in front
  (`Prep`) that are the walk's ops unproxied: they define each entry's
  sure need and read first only `sub` (`opsRF_ren_back`: a register read
  first after a renaming is the image of one read first before it);
* unproxying fixes every defined register (no defined register is a key
  of `cond`, `KI`), so `BlkNodup`, `Cross` and `NoTr` carry over from the
  walk's `SIP`;
* nothing is live at `o` once each lazy entry defines its sure need: the
  hop block reads nothing, and below `o` the blocks are the run's
  (`liveK_frame`, from `RawIHX` of the run).

**`optIn_finishLUX`**, **`optimize_keeps_finishLUX`**, and the instances
for a `%6` under a cons and nested `%6`s.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Renaming that need not be injective -/

/-- **A register read first after a renaming is the image of one read first
before it.** -/
theorem opsRF_ren_back {u : Nat → Nat} : ∀ (A : List Pole) {y : Nat}, OpsRF (A.map (renPole u)) y →
    ∃ x, u x = y ∧ OpsRF A x
  | [], _, h => h.elim
  | op :: A, y, h => by
    rw [List.map_cons] at h
    rcases h with h | ⟨hd, h⟩
    · rw [mem_aliasReads, srcs_ren] at h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      exact ⟨x, rfl, Or.inl (mem_aliasReads.mpr hx)⟩
    · obtain ⟨x, rfl, hx⟩ := opsRF_ren_back A h
      refine ⟨x, rfl, Or.inr ⟨fun e => hd ?_, hx⟩⟩
      rw [dst_ren, e]; rfl

theorem blockDefs_renBlob (u : Nat → Nat) (b : Blob) : blockDefs (renBlob u b) = (blockDefs b).map u := by
  have := defsOf_ren u b.body
  simp only [defsOf] at this
  simp only [blockDefs, renBlob, List.map_append, this]

theorem renBlob_pre (u : Nat → Nat) (A : List Pole) (b : Blob) :
    renBlob u (pre A b) = pre (A.map (renPole u)) (renBlob u b) := by
  simp [renBlob, pre, List.map_append]

/-! ## Liveness through the hop block of `+kerf` -/

/-- Below the hop block's label `bo` the blocks are the run's, which jump
below `bo`; a register outside the root's sure need that is live with the
kills of the lazy tree rooted at `bo` is live with those rooted at the run's
entry. -/
theorem liveK_frame {bl1 bl5 : Map Blob} {bo there : Nat} {laz : Lazy S} {r : Nat}
    (below : ∀ k, k < bo → HoonMap.get bl5 k = HoonMap.get bl1 k)
    (jlt : ∀ k b, HoonMap.get bl1 k = some b → ∀ j ∈ getJmps b.fin, j.there < bo)
    (hr : ¬ NMem laz.sure.ned r) {k : Nat} (h : LiveK bl5 (lazK bo laz) k r) :
    k < bo → LiveK bl1 (lazK there laz) k r := by
  have conv : ∀ x y, ¬ NMem laz.sure.ned y → lazK there laz x y → lazK bo laz x y := fun x y hy e => by
    obtain ⟨e, he, h1, h2⟩ := e
    rcases List.mem_cons.mp he with rfl | he'
    · exact absurd h2 hy
    · exact ⟨e, List.mem_cons_of_mem _ he', h1, h2⟩
  revert hr
  induction h with
  | here hb hrf hk =>
    intro hr hk'
    exact LiveK.here (by rw [← below _ hk']; exact hb) hrf fun e => hk (conv _ _ hr e)
  | next hb hj _ hd hk ih =>
    intro hr hk'
    have hb1 := hb
    rw [below _ hk'] at hb1
    exact LiveK.next hb1 hj (ih hr (jlt _ _ hb1 _ hj)) hd fun e => hk (conv _ _ hr e)

/-! ## The whole-subject pass -/

variable [MapKeys Map]

/-- **`OptIn` of the whole-subject final pass on `FragX`**, for every nomm
with at most 255 `%6`. -/
theorem optIn_finishLUX {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) {c' : Straight Map}
    (h : finishLU (S := S) (Map := Map) nm = some c') : OptIn c'.blocks := by
  unfold finishLU at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o, sub⟩, g7⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  have R : RunOKP (Map := Map) lib0 nm (CGoal.done : CGoal S) gen0 g1 nex :=
    (runX_ok lib0 hf).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
  obtain ⟨LA, LD⟩ := lazOK_run hf hc h1
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := runX_rawIHX_up (S := S) (Map := Map) hf CGoal.done [] gen0 g1 nex
    (fun _ _ => False) (KVan.none _) sip_gen0X trivial trivial trivial trivial (fun _ _ e => e) hc trivial h1
  have hl1 : ∀ r, ¬ LiveK g1.blocks (lazK nex.th.there nex.laz) nex.th.there r := fun r hl' =>
    L1 r (hl'.mono fun x y h => h.elim False.elim id)
  have hcnd : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by
    rw [R.cnd]; simp [gen0, HoonMap.get_empty]
  -- `+kerf`: the hop block
  simp only [kerf] at h2
  obtain ⟨o', ge, he, h2⟩ := bind_some h2
  have gee : ge = g1.emitted ⟨[], [], Termin.hop nex.th⟩ := by
    have he' := he
    rw [emit_apply] at he'
    simp only [Option.some.injEq, Prod.mk.injEq] at he'
    exact he'.2.symm
  obtain ⟨Se, eo, ee, qe, boe⟩ := sip_emit S1 (emitOK_hop a1 hi1) he
  obtain ⟨r, g3, h3, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨⟨e2o, e2s⟩, e2g⟩ := h2
  subst e2o e2s e2g eo
  rw [kern_eq] at h3
  obtain ⟨r0, g5, h5, h3⟩ := bind_some h3
  have c5 : g5.cond = g1.cond := by
    rw [re_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    rw [← h5.2, gee]; rfl
  obtain ⟨S5, er0, q5, b5, o5⟩ := sip_re Se h5
  subst er0
  obtain ⟨g6, g6', h6, h3⟩ := bind_some h3
  rw [get_apply] at h6
  simp only [Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rw [S5.drop] at h3
  simp only [Bool.false_eq_true, if_false] at h3
  obtain ⟨⟨⟩, g7', h7, h3⟩ := bind_some h3
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨e3r, e3g⟩ := h3
  subst e3r
  rw [walkLazy_flat, e3g] at h7
  have h7' : walkList (kernGate ge.re g1.bo) ((g1.bo, nex.laz) :: wentries nex.laz) g5 = some ((), g3) := by
    simp only [walkList]; exact h7
  -- the state before the walk
  have hbo5 : HoonMap.get g5.blocks g1.bo = some ⟨[], [], Termin.hop nex.th⟩ := by rw [b5, ee]; exact get_put_self
  have below5 : ∀ k, k < g1.bo → HoonMap.get g5.blocks k = HoonMap.get g1.blocks k := fun k hk => by
    rw [b5, ee, get_put_ne (by omega)]
  have dd5 : ∀ y, Defd g5.blocks y ↔ Defd g1.blocks y := fun y => by
    rw [b5, ee, defd_put (S1.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have I0 : KI (S := S) Xup (upRk g1.blocks) g1.bo ge.re ((g1.bo, nex.laz) :: wentries nex.laz) g5 := by
    refine ⟨S5, by omega, fun k v hv => ?_, fun y _ => by rw [c5, hcnd], fun d => ?_, ?_, fun e he => ?_⟩
    · rw [c5, hcnd] at hv; cases hv
    · have := S1.defd_lt ((dd5 _).mp d); omega
    · have LA' := List.pairwise_cons.mp LA
      exact needsApart_perm ((wentries_perm nex.laz).symm.cons _) (List.pairwise_cons.mpr ⟨LA'.1, LA'.2⟩)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨⟨_, hbo5⟩, R.dist, fun y hy => ⟨by have := (R.regs y hy).2; omega,
          fun d => LD (nex.th.there, nex.laz) List.mem_cons_self y hy ((dd5 y).mp d)⟩⟩
      · have hm : e ∈ entries nex.laz := (wentries_perm nex.laz).mem_iff.mp he'
        obtain ⟨-, lt, th', hb⟩ := R.labs e hm
        exact ⟨⟨_, by rw [below5 _ (by omega)]; exact hb⟩, (R.eregs e hm).1, fun y hy =>
          ⟨by have := ((R.eregs e hm).2 y hy).2; omega,
            fun d => LD e (List.mem_cons_of_mem _ hm) y hy ((dd5 y).mp d)⟩⟩
  obtain ⟨I7, P, pP, kP, rP, -⟩ := kernList_prep ge.re g1.bo _ g5 g3 I0 h7'
  obtain ⟨S7, -, ck7, dk7, ns7, -, -⟩ := I7
  -- the final pass: the map path is the renaming path of the unproxied blocks
  rw [toStraightF_run _ _ _ (by simp [isRun, flattenNeed])] at h
  simp only [flattenNeed, List.headD, List.length] at h
  obtain ⟨start, hst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, rfl⟩ := Option.map_eq_some_iff.mp h
  generalize hu : (fun r => if hasProxies g3.cond then unproxy g3.cond r else r) = u
  have uN : ∀ x, HoonMap.get g3.cond x = Option.none → u x = x := fun x hx => by
    rw [← hu]; simp only; split
    · exact unproxy_none hx
    · rfl
  have uK : ∀ x v, HoonMap.get g3.cond x = some v → u x = v.1 := fun x v hx => by
    have hp : hasProxies g3.cond = true := by
      unfold hasProxies
      cases e : HoonMapKeys.keys g3.cond with
      | nil =>
        have := (HoonMapKeys.mem_keys g3.cond x).mpr (by simp [hx])
        rw [e] at this; cases this
      | cons _ _ => rfl
    rw [← hu]; simp only [hp, if_true, unproxy, hx]
  have uLow : ∀ x, x ≤ ge.re → u x = x := fun x hx => uN x (by
    cases e : HoonMap.get g3.cond x with
    | none => rfl
    | some v => have := (ck7 x v e).1; omega)
  have uD : ∀ x, Defd g3.blocks x → u x = x := fun x d => uN x (dk7 x d)
  have hpr : proxRen g3.cond (hasProxies g3.cond) (renReg ge.re 1) = renReg ge.re 1 ∘ u := by
    rw [← hu]; rfl
  rw [hpr] at hnew
  -- ranks
  have rk5 : DownRk (upRk g5.blocks) g5.blocks := by
    have G : GrowU (gen0 : Comp.Gen Map) ge := by
      rw [gee]
      exact R.grow.trans (growU_emit (fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨lo1, hi1⟩) (R.grow.up upBelow_gen0))
    rw [b5]; exact downRk_of_growU G (fun k => by simp [gen0, HoonMap.get_empty]) (by simp [gen0])
  have RD := rankDown_start (downRk_prep pP rk5) hst
  have gs8 := get_mapVals (renBlob u) (HoonMap.put (HoonMap.del g3.blocks g1.bo) 0 start)
  have g8 := get_mapVals (renBlob u) g3.blocks
  have hnew8 : ∀ k b', HoonMap.get new k = some b' →
      ∃ b, HoonMap.get (mapVals (renBlob u) (HoonMap.put (HoonMap.del g3.blocks g1.bo) 0 start)) k = some b ∧
        keepBlock (mapVals (renBlob u) (HoonMap.put (HoonMap.del g3.blocks g1.bo) 0 start)) (renReg ge.re 1) k b =
          some (some b') := by
    intro k b' hk
    obtain ⟨b, hb, hkb⟩ := renameBlocks_get hnew hk
    refine ⟨renBlob u b, by rw [gs8, hb]; rfl, ?_⟩
    rw [keepBlock_ren RD gs8]; exact hkb
  -- the unproxied blocks are the raw blocks with the unproxied ops in front
  have P8 : Prep (fun k => (P k).map (renPole u)) g5.blocks (mapVals (renBlob u) g3.blocks) := by
    intro k
    rw [g8, pP k]
    cases hb : HoonMap.get g5.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      have fx : renBlob u b = b := by
        rw [renBlob_congr (P := (· < g5.re)) (v := id) (fun x hx => by simp only [id]; exact uLow x (by omega))
          (S5.regs k b hb), renBlob_id]
      rw [renBlob_pre, fx]
  have DB : ∀ k b8, HoonMap.get (mapVals (renBlob u) g3.blocks) k = some b8 →
      ∃ b, HoonMap.get g3.blocks k = some b ∧ b8 = renBlob u b ∧ blockDefs b8 = blockDefs b := by
    intro k b8 hk
    rw [g8] at hk
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hk
    refine ⟨b, hb, rfl, ?_⟩
    rw [blockDefs_renBlob]; exact map_fix (fun x hx => uD x (defd_iff.mpr ⟨k, b, hb, hx⟩))
  have dd8 : ∀ y, Defd (mapVals (renBlob u) g3.blocks) y → Defd g3.blocks y := fun y d => by
    obtain ⟨k, b8, hk, hm⟩ := defd_iff.mp d
    obtain ⟨b, hb, -, e⟩ := DB k b8 hk
    rw [e] at hm; exact defd_iff.mpr ⟨k, b, hb, hm⟩
  have bn8 : BlkNodup (mapVals (renBlob u) g3.blocks) := fun k b8 hk => by
    obtain ⟨b, hb, -, e⟩ := DB k b8 hk; rw [e]; exact S7.nd k b hb
  have bx8 : Cross (mapVals (renBlob u) g3.blocks) := fun k k' b8 b8' y hk hk' hne m m' => by
    obtain ⟨b, hb, -, e⟩ := DB k b8 hk
    obtain ⟨b', hb', -, e'⟩ := DB k' b8' hk'
    rw [e] at m; rw [e'] at m'
    exact S7.cr k k' b b' y hb hb' hne m m'
  have nt8 : NoTr (mapVals (renBlob u) g3.blocks) := fun k b8 hk op hop => by
    obtain ⟨b, hb, rfl, -⟩ := DB k b8 hk
    simp only [renBlob, List.mem_map] at hop
    obtain ⟨op0, h0, rfl⟩ := hop
    rw [tr_ren]; exact S7.tr k b hb op0 h0
  have g10 : g1.bo ≠ 0 := by have := S1.bo1; omega
  refine optIn_prepN (K := lazK g1.bo nex.laz) (ned := Need.this ge.re) P8 rk5 (argsAboveR_upRk_of_xup S5.x)
    (fun k y hk => ?_) (fun y hlv => ?_) bn8 bx8 nt8 (fun k y hy => ?_) (fun y hy d => ?_)
    (by rw [g8, hst]; rfl) (by rw [gs8]; simp [HoonMap.get_put])
    (by rw [gs8]; simp [HoonMap.get_put, HoonMap.get_del, g10])
    (fun k k0 ko => by rw [gs8, g8]; simp [HoonMap.get_put, HoonMap.get_del, k0, ko])
    (renReg_inj _ _) (renReg_surj _ _) hnew8
  · obtain ⟨e, he, rfl, hy⟩ := hk
    have he' : e ∈ (g1.bo, nex.laz) :: wentries nex.laz := by
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((wentries_perm _).mem_iff.mpr he)
    have yl : y < g1.re := by
      rcases List.mem_cons.mp he with rfl | he
      · exact (R.regs y hy).2
      · exact ((R.eregs e he).2 y hy).2
    rw [defsOf_ren, ← uLow y (by omega)]
    exact List.mem_map_of_mem (kP e he' y hy)
  · rcases hlv with ⟨hb, hrf, -⟩ | ⟨hb, hj, hl', -, hk⟩
    · rw [hbo5] at hb; cases hb
      simp [BlockRF, OpsRF, finRegs, jmpRegs, a1] at hrf
    · rw [hbo5] at hb; cases hb
      simp only [getJmps, List.mem_singleton] at hj
      subst hj
      exact hl1 y (liveK_frame below5 (fun k b hb j hj => S1.jlt hb hj)
        (fun hm => hk ⟨(g1.bo, nex.laz), List.mem_cons_self, rfl, hm⟩) hl' hi1)
  · obtain ⟨x, rfl, hx⟩ := opsRF_ren_back _ hy
    simp only [NMem]
    rcases rP k x hx with rfl | ⟨t, ht⟩
    · exact uLow _ (Nat.le_refl _)
    · exact uK x _ ht
  · simp only [NMem] at hy
    subst hy
    exact ns7 (dd8 _ d)

/-- **`+optimize` keeps the whole-subject code of `FragX`.** -/
theorem optimize_keeps_finishLUX (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) {c' s' : Straight Map}
    (h : finishLU (S := S) (Map := Map) nm = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') :
    Opt.Keeps c' s' :=
  optimize_keeps_optIn M (optIn_finishLUX hf hc h) ho

/-! ## Two instances (`#guard exLU` of `RawInvCheckX.lean`: `finishLU`
succeeds on both, through proxies, and its output passes `okOut`) -/

/-- `[[6 [0 2] [0 3] [0 1]] [0 1]]`, a `%6` under a cons. -/
theorem optIn_finishLUX_consSix {c' : Straight Map}
    (h : finishLU (S := S) (Map := Map) (Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1)) = some c') :
    OptIn c'.blocks :=
  optIn_finishLUX fragX_consSix (by decide) h

theorem optimize_keeps_consSixU (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat} {c' s' : Straight Map}
    (h : finishLU (S := S) (Map := Map) (Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1)) = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') :
    Opt.Keeps c' s' :=
  optimize_keeps_finishLUX M fragX_consSix (by decide) h ho

/-- `[6 [0 2] [6 [0 6] [0 3] [0 1]] [1 0]]`, a `%6` in a branch of a `%6`. -/
theorem optIn_finishLUX_sixSix {c' : Straight Map}
    (h : finishLU (S := S) (Map := Map) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n1 (A 0))) = some c') : OptIn c'.blocks :=
  optIn_finishLUX fragX_sixSix (by decide) h

theorem optimize_keeps_sixSixU (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat} {c' s' : Straight Map}
    (h : finishLU (S := S) (Map := Map) (Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n1 (A 0))) = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') :
    Opt.Keeps c' s' :=
  optimize_keeps_finishLUX M fragX_sixSix (by decide) h ho

end Raw
end SkaModel
end Formalization
