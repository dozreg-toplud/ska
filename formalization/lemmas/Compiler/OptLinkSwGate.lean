import lemmas.Compiler.OptLinkSwWalkPlain

/-!
# `+switch-chains` linked: the walk, the gate, `SwitchLink`

```hoon
  |-  ^-  (map @uwoo blob-out)
  ?~  topo  out
  ?:  (~(has in done) i.topo)  $(topo t.topo)
  =/  cs=(list test)  (chain-of i.topo)
  ?:  (gte (lent cs) 4)
    ?>  ?=(^ cs)
    ..                          ::  a tagged chain (OptLinkSwWalkTag.lean)
  =/  ps=(list [p=@uwoo t=plain])  (plains-of i.topo)
  ?:  (lth (lent ps) 4)  $(topo t.topo)
  ?>  ?=(^ ps)
  ..                            ::  a plain chain (OptLinkSwWalkPlain.lean)
```

* `sw_walk`: **where `switchWalk` returns `r`, the walk returns the noun of
  `r`**, by induction on `topo`, through `sw_chain`, `sw_wtag`,
  `sw_plains`, `sw_wplain`.
* `sw_gate`: **where `switchChains fuel` returns `bs` on a treap of blocks
  with no `%lti`, the gate of `+switch-chains` returns the noun of `bs`**:
  `topo` (`bb_gate`), `rev` (`rev_gate` on `(sy topo)`), `uses`
  (`sw_uses`), `nex` (`sw_nex`), the walk.
* `switchLink`: `SwitchLink P` for every `P` whose `switch` is the model
  with some fuel; `opt_gate_sw`: **`+optimize` with only `AliasLink` as a
  hypothesis**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The walk -/

/-- **The walk of `+switch-chains`**: where `switchWalk` returns `r`, the
walk on the noun of `topo`, `out`, a set related to `done` and `nex`
returns the noun of `r`. -/
theorem sw_walk (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (T0 USES : Noun)
    (hU : UsesRel USES (Opt.usesOf bl)) (fuel : Nat) :
    ∀ (topo : List Nat) (out : TreapMap mugF Blob) (done : List Nat) (nex : Nat) (DONE : Noun)
      (r : TreapMap mugF Blob), SawRel DONE done → Opt.switchWalk bl rev fuel topo out done nex = some r →
    nock (swWk (HoonMap.toNoun Blob.toNoun bl) T0 (listNoun A topo) (jarN rev) USES (HoonMap.toNoun Blob.toNoun out)
      DONE (A nex)) swWalk = some (HoonMap.toNoun Blob.toNoun r) := by
  have hL := optC_layer2
  have hL1 := optC_layer1
  intro topo
  induction topo with
  | nil =>
    intro out done nex DONE r hD h
    simp only [Opt.switchWalk, Option.some.injEq] at h
    subst h
    unfold swWk
    conv => lhs; arg 2; unfold swWalk
    simp [nock_exec, listNoun]
  | cons o rest ih =>
    intro out done nex DONE r hD h
    have hh := saw_has hD o
    simp only [Opt.switchWalk] at h
    by_cases ho : o ∈ done
    · rw [if_pos ho] at h
      have ih' := ih out done nex DONE r hD h
      unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
      generalize optC = OC at hL ih'
      conv => lhs; arg 2; unfold swWalk
      simp [nock_exec, listNoun, swWHas, hL, in.arm_at, in_arm, in.has.arm_at, has_arm, hh, ho, loob, ih']
    · rw [if_neg ho] at h
      obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
      have hC := sw_chain bl rev T0 USES hU fuel o cs hcs
      have hlen := lent_gate layer2 (cs.map stestN)
      rw [← listNoun_map_listN, List.length_map] at hlen
      have hg4 := gte_gate layer1 gteIn_layer1 cs.length 4
      by_cases h4 : 4 ≤ cs.length
      · rw [if_pos h4] at h
        obtain ⟨⟨out1, done1⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨D1, hD1, hW⟩ := sw_wtag bl rev T0 USES fuel o rest out done DONE (A nex) hD cs out1 done1 ht
        have ih' := ih out1 done1 nex D1 r hD1 h
        rw [ih'] at hW
        have hcs0 : ∃ c0 cl, cs = c0 :: cl := by
          cases cs with
          | nil => simp at h4
          | cons c0 cl => exact ⟨c0, cl, rfl⟩
        obtain ⟨c0, cl, rfl⟩ := hcs0
        simp only [List.length_cons] at hg4 h4 hlen
        unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
        generalize optC = OC at hL hL1 hW hC
        conv => lhs; arg 2; unfold swWalk
        simp only [listNoun] at hC hW hlen
        simp [nock_exec, listNoun, swWHas, swWCs, swWGte, hL, hL1, in.arm_at, in_arm, in.has.arm_at, has_arm, hh,
          ho, loob, hC, lent.arm_at, lent_arm, hlen, gte.arm_at, gte_arm, hg4, h4, hW]
      · rw [if_neg h4] at h
        obtain ⟨ps, hps, h⟩ := Option.bind_eq_some_iff.mp h
        have hP := sw_plains bl rev T0 USES hU fuel o ps hps
        have hlp := lent_gate layer2 (ps.map spN)
        rw [← listNoun_map_listN, List.length_map] at hlp
        have hl4 := lth_gate layer1 decIn_layer1 ps.length 4
        by_cases hp4 : ps.length < 4
        · rw [if_pos hp4] at h
          have ih' := ih out done nex DONE r hD h
          unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
          generalize optC = OC at hL hL1 ih' hC hP
          conv => lhs; arg 2; unfold swWalk
          simp [nock_exec, listNoun, swWHas, swWCs, swWGte, swWPlain, hL, hL1, in.arm_at, in_arm, in.has.arm_at,
            has_arm, hh, ho, loob, hC, lent.arm_at, lent_arm, hlen, gte.arm_at, gte_arm, hg4, h4, hP, hlp,
            lth.arm_at, lth_arm, hl4, hp4, ih']
        · rw [if_neg hp4] at h
          obtain ⟨⟨out1, done1, nex1⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨D1, hD1, hW⟩ := sw_wplain bl rev T0 USES fuel o rest out done DONE (listNoun stestN cs) nex hD ps
            out1 done1 nex1 ht
          have ih' := ih out1 done1 nex1 D1 r hD1 h
          rw [ih'] at hW
          have hps0 : ∃ p0 pl, ps = p0 :: pl := by
            cases ps with
            | nil => simp at hp4
            | cons p0 pl => exact ⟨p0, pl, rfl⟩
          obtain ⟨p0, pl, rfl⟩ := hps0
          simp only [List.length_cons] at hl4 hp4 hlp
          unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
          generalize optC = OC at hL hL1 hW hC hP
          conv => lhs; arg 2; unfold swWalk
          simp only [listNoun] at hP hW hlp
          simp [nock_exec, listNoun, swWHas, swWCs, swWGte, swWPlain, hL, hL1, in.arm_at, in_arm, in.has.arm_at,
            has_arm, hh, ho, loob, hC, lent.arm_at, lent_arm, hlen, gte.arm_at, gte_arm, hg4, h4, hP, hlp,
            lth.arm_at, lth_arm, hl4, hp4, hW]

/-! ## The gate -/

/-- **`+switch-chains`**: where `switchChains fuel` returns `bs` on a treap of
blocks with no `%lti`, the gate on the noun of the blocks returns the noun of
`bs`. -/
theorem sw_gate (bl : TreapMap mugF Blob) (hl : NoLti bl) (fuel : Nat) (bs : TreapMap mugF Blob)
    (h : Opt.switchChains fuel bl = some bs) :
    nock (C swBodyCut (C (HoonMap.toNoun Blob.toNoun bl) optC)) swBodyCut = some (HoonMap.toNoun Blob.toNoun bs) := by
  unfold Opt.switchChains at h
  obtain ⟨topo, ht, hw⟩ := Option.bind_eq_some_iff.mp h
  have hbb := bb_gate bl hl fuel topo ht
  obtain ⟨TS, hsi, hTS⟩ := si_gate topo
  have hrev := rev_gate bl hl topo TS hTS
  obtain ⟨U, hu, hU⟩ := sw_uses bl hl (listNoun A topo) (jarN (Opt.revCfg bl topo))
  have hnex := sw_nex bl (listNoun A topo) (jarN (Opt.revCfg bl topo)) U
  have hwalk := sw_walk bl (Opt.revCfg bl topo) (listNoun A topo) U hU fuel topo bl [] (Opt.nexOf bl) (A 0) bs
    sawRel_nil hw
  rw [swS9_eq] at hnex
  have hL := optC_layer2
  have h4a := bb_at
  have h5a := rev_at
  have hsy := sy_at
  have hsya := sy_arm
  unfold swS2 at hu
  unfold swWk swSp swK9 swK8 swK7 swK6 swK5 swK4 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
  generalize optC = OC at hL hbb hrev hu hnex hwalk h4a h5a
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hbb hrev hu hnex hwalk ⊢
  conv => lhs; arg 2; unfold swBodyCut
  simp [nock_exec, hL, h4a, bb_arm, hbb, h5a, rev_arm, hsy, hsya, hsi, hrev, hu, hnex, hwalk]

/-! ## `SwitchLink` -/

/-- **`SwitchLink` holds** for every `P` whose `switch` is the model of
`+switch-chains` with some fuel. -/
theorem switchLink (P : Opt.Passes (TreapMap mugF)) (sfuel : Nat)
    (hP : ∀ bl, P.switch bl = Opt.switchChains sfuel bl) : SwitchLink P := by
  intro bl bs hl h
  rw [hP] at h
  rw [swBody_eq]
  exact sw_gate bl hl sfuel bs h

/-- **`+optimize`** with the models of `+trim-trace-hints` and
`+switch-chains`: `+alias` is the only hypothesis. -/
theorem opt_gate_sw (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P)
    (hPt : ∀ bl topo rev, P.trim bl topo rev = Opt.trimTraceHints bl topo rev) (sfuel : Nat)
    (hPs : ∀ bl, P.switch bl = Opt.switchChains sfuel bl)
    (fuel : Nat) (s s' : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (h : Opt.optimizeF fuel P s = some s') :
    nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun :=
  opt_gate_trim P hA hPt (switchLink P sfuel hPs) fuel s s' hl h

end Compiler
end Formalization
