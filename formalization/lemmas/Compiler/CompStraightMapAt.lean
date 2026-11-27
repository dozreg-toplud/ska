import lemmas.Compiler.CompStraightMapPre

/-!
# `+to-straight` with proxies: the gate on every `cond`

README Gaps 20.  The hypotheses of `tsm_core` on the real core of the gate:
the two bunts by the kernel on a spine of free nouns (`tsm_rep_bunt_sp`,
`tsm_arg_bunt_sp`: a free noun is never returned whole by a slot there, so
the kernel reduces), `unproxy` (`tsm_unproxy`), `ren` (`tsnp_ren`) and the
slots.  Then the pushes with `cond` a nonempty treap (`tsnp_pre`: `proxies`
is `&`), the core (`tsmp_core`: the renaming path by `renReg r0 n-in ∘
unproxy cond`), the gate with proxies against `toStraightF_run`
(`tsmp_at`), and the gate on every `cond` (`ts_at_all`: `tsn_at` when
`hasProxies cond` is false).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The bunts, by the kernel on a spine of free nouns -/

/-- The blob bunt is `[~ ~ %bom ~]`. -/
theorem tsm_blob_bunt_eq : tsmBlobBunt = C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))) := by kernel_rfl

/-- **The bunt of the sample of `tsmGate`** in a core whose rest is fifteen
free nouns then `K`: `[[0 *blob] [~ [0 0]]]`. -/
theorem tsm_rep_bunt_sp (ord SB REN RUN N R0 INS PX UNG B T SAM D G c2 c6 : Noun) :
    nock (C ord (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (C RUN (C N (C R0 (C INS (C PX (C UNG (C B (C T (C SAM (C D (C G (C c2 (C c6 compK)))))))))))))))))) tsmRepBuntF
      = some (C (C (A 0) tsmBlobBunt) (C (A 0) (C (A 0) (A 0)))) :=
  nock_of_evalFuel (fuel := 5000) (by kernel_rfl)

/-- **The bunt of the sample of the `+spin` gate of `rewrite-args`** in the
same core: `[~ [0 0]]`. -/
theorem tsm_arg_bunt_sp (J SB REN RUN N R0 INS PX UNG B T SAM D G c2 c6 : Noun) :
    nock (C tsmArgBody (C J (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (C RUN (C N (C R0 (C INS (C PX (C UNG (C B (C T (C SAM (C D (C G (C c2 (C c6 compK))))))))))))))))))) tsmArgBuntF1
      = some (C (A 0) (C (A 0) (A 0))) :=
  nock_of_evalFuel (fuel := 5000) (by kernel_rfl)

/-- `K` at axis `7`: the context is `[c2 c6 K]`. -/
theorem ctx_of_slot7 {ctx : Noun} (h7 : slot? 7 ctx = some compK) : ∃ c2 c6, ctx = C c2 (C c6 compK) := by
  match ctx, h7 with
  | Noun.cell a (Noun.cell b d), h =>
    have hd : slot? 7 (C a (C b d)) = some d := by simp [nock_exec]
    rw [hd] at h
    exact ⟨a, b, by rw [Option.some.inj h]⟩
  | Noun.atom _, h => simp [nock_exec] at h
  | Noun.cell _ (Noun.atom _), h => simp [nock_exec] at h

/-! ## `proxies` from `cond` -/

/-- With proxies the noun of `cond` is a cell. -/
theorem hasProxies_cell (m : TreapMap mugF (Nat × List Nat)) (h : hasProxies m = true) :
    ∃ a b, HoonMap.toNoun condValNoun m = C a b := by
  unfold hasProxies at h
  cases e : HoonMapKeys.keys m with
  | nil => rw [e] at h; simp at h
  | cons k ks =>
    have hk := (HoonMapKeys.mem_keys m k).mp (by rw [e]; exact List.mem_cons_self)
    rw [hoonMap_toNoun]
    rw [hoonMap_get] at hk
    generalize m.1 = t at hk ⊢
    cases t with
    | nil => simp [Tr.get] at hk
    | node k' v l r => exact ⟨_, _, rfl⟩

/-- Without proxies `cond` is empty. -/
theorem hasProxies_none {m : TreapMap mugF (Nat × List Nat)} (h : hasProxies m = false) :
    ∀ k, HoonMap.get m k = Option.none := by
  intro k
  unfold hasProxies at h
  cases e : HoonMap.get m k with
  | none => rfl
  | some v =>
    have hk := (HoonMapKeys.mem_keys m k).mpr (by rw [e]; rfl)
    cases e2 : HoonMapKeys.keys m with
    | nil => rw [e2] at hk; simp at hk
    | cons _ _ => rw [e2] at h; simp at h

/-! ## The states and the pushes with proxies -/

/-- The gate `ren` as the gate of `+to-straight` pushed it, `proxies` being `PX`. -/
noncomputable def tsRenGP (PX BN D G ctx : Noun) (o : Nat) (NED : Noun) (l : List Nat) : Noun :=
  C tsRenBat (C (A 0) (tsS7P PX BN BN (tsS0N D G ctx o NED) (l.headD 0) (listNoun A l) l.length
    (loob (isRun l (l.headD 0) 0))))

/-- The state of the `|^` core, `proxies` being `PX`. -/
noncomputable def tsStP (PX SB B Bo BN D G ctx : Noun) (o : Nat) (NED : Noun) (l : List Nat) : Noun :=
  tsCoreStP PX SB (tsRenGP PX BN D G ctx o NED l) B Bo (tsS0N D G ctx o NED) (l.headD 0) (listNoun A l)
    l.length (loob (isRun l (l.headD 0) 0))

/-- **The pushes of `+to-straight`** on any input need with proxies: as
`tsn_pre`, with `proxies` `&`. -/
theorem tsnp_pre {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (ned : Need)
    (hp : hasProxies g.cond = true) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (HoonMap.get g.blocks o).bind fun start =>
          nock (tsStP (A 0) (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
            (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x)
            ctx o ned.toNoun (flattenNeed ned))
            (C (A 9) (C (A 190) (C (A 0) (A 1)))) := by
  have hb := genNoun_blocks g x
  obtain ⟨ca, cb, ec⟩ := hasProxies_cell g.cond hp
  have hcd : slot? 254 (genNoun g x) = some (C ca cb) := by
    simp only [genNoun, nock_exec, ec]
  have h1 := tsnp_pre1 hc (genNoun g x) _ o ned hb ca cb hcd
  have h2 := tsnp_pre2 hc (A 0) comp.door (genNoun g x) (HoonMap.toNoun Blob.toNoun g.blocks) o ned.toNoun
    ((flattenNeed ned).headD 0) (flattenNeed ned)
  have hget := getF_hoonMap Blob.toNoun g.blocks o
  simp only [compCore]
  change nock (tsS0N comp.door (genNoun g x) ctx o ned.toNoun) tsBat = _
  rw [h1, h2]
  cases e : HoonMap.get g.blocks o with
  | none =>
    rw [e] at hget
    exact tsnp_pre3_nil hc _ _ _ _ _ o _ _ _ _ _ hget
  | some start =>
    rw [e] at hget
    exact tsnp_pre3 hc _ _ _ _ _ _ _ _ o _ _ _ _ _ hget (delF_hoonMap Blob.toNoun g.blocks o)
      (putF_hoonMap Blob.toNoun (HoonMap.del g.blocks o) 0 start)

/-! ## The core and the gate with proxies -/

/-- **The `|^` core of `+to-straight` with proxies** on any need whose
registers are a run: the renaming path of the model by `renReg r0 n-in ∘
unproxy cond`. -/
theorem tsmp_core {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF))
    (x : GenRest) (o : Nat) (ned : Need) (start : Blob)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    nock (tsStP (A 0) (Blob.toNoun start) (HoonMap.toNoun Blob.toNoun (HoonMap.put (HoonMap.del g.blocks o) 0 start))
        (HoonMap.toNoun Blob.toNoun g.blocks) (HoonMap.toNoun Blob.toNoun g.blocks) comp.door (genNoun g x)
        ctx o ned.toNoun (flattenNeed ned)) (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = (renameBlocks (HoonMap.put (HoonMap.del g.blocks o) 0 start)
          (fun r => renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length (unproxy g.cond r))).map
          fun new => Straight.toNoun (⟨needToOrd ned, countArgs (needToOrd ned), new⟩ : Straight (TreapMap mugF)) := by
  have h15 := ts_types h7
  have hK7 := h7
  unfold tsStP tsRenGP tsCoreStP tsS7P tsS5P
  rw [hrun, loob_true]
  refine tsm_core _ _ _ _ _ _ _ _ _ _ _ (unproxy g.cond) (renReg ((flattenNeed ned).headD 0) (flattenNeed ned).length)
    ned (fun r => tsm_unproxy hc g x _ comp.door o _ r)
    (fun r => tsnp_ren hc (A 0) _ _ comp.door (genNoun g x) o _ _ _ _ _ r) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [tsS0N, tsSampleN, nock_exec]
  · simp [tsS0N, nock_exec, hc]
  · obtain ⟨c2, c6, rfl⟩ := ctx_of_slot7 h7
    intro J
    exact tsm_arg_bunt_sp J _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp [nock_exec]
  · simp [tsS0N, nock_exec, h15]
  · simp [tsS0N, nock_exec, h7]
  · obtain ⟨c2, c6, rfl⟩ := ctx_of_slot7 h7
    exact tsm_rep_bunt_sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **`+to-straight` with proxies** on any input need whose registers are
a run: the gate returns the noun of `toStraightF`. -/
theorem tsmp_at {ctx : Noun} (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF)) (x : GenRest)
    (o : Nat) (ned : Need) (hp : hasProxies g.cond = true)
    (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  rw [tsnp_pre hc g x o ned hp, toStraightF_run g.cond g.blocks o hrun]
  cases e : HoonMap.get g.blocks o with
  | none => rfl
  | some start =>
    simp only [Option.bind_some]
    rw [tsmp_core hc h7 g x o ned start hrun, Option.map_map]
    simp only [proxRen, hp, if_true]
    rfl

/-- **`+to-straight` on every `cond`** and any input need whose registers
are a run: the gate returns the noun of `toStraightF` (`tsn_at` without
proxies, `tsmp_at` with). -/
theorem ts_at_all {ctx : Noun} (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF)) (x : GenRest)
    (o : Nat) (ned : Need) (hrun : isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true) :
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun := by
  cases hp : hasProxies g.cond with
  | false => exact tsn_at h7 g x o ned (hasProxies_none hp) hrun
  | true => exact tsmp_at h7 g x o ned hp hrun

end Compiler
end Formalization
