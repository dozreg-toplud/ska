import lemmas.Compiler.OptLinkOnceAfter

/-!
# `+optimize-once` and `+optimize` linked

`+optimize-once` (arm `180` of `optC`): the body computes `topo` by
`+bb-topo` and `rev` by `+rev-cfg` with `(sy topo)`, runs the structural
loop (`oo_loop`) and then `ooAfter` (the steps of `OptLinkOnceAfter.lean`).

* `oo_pre`: the body up to `ooAfter`, where `bbTopo` and `structLoop` return.
* `oo_gate`: **where `optimizeOnce fuel P` returns `(again, s')` on a
  straight function whose blocks have no `%lti`, the gate returns `[again
  s']`**, given `AliasLink P` and `TrimLink P`.
* `optimizeOnce_noLti`: the round keeps `NoLti`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

@[nock_exec] theorem oo_arm (d : Noun) : nock d ooArm = some (C ooBody (C ooBunt d)) := by
  unfold ooArm ooHint; generalize ooBody = B; generalize ooBunt = U; simp [nock_exec]

/-- The body of `+optimize-once` up to `ooAfter`: `topo`, `rev` and the
structural loop. -/
theorem oo_pre (fuel : Nat) (s : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (topo0 : List Nat)
    (h0 : Opt.bbTopo fuel s.blocks = some topo0) (rl : List Nat × TreapMap mugF (List Nat) × TreapMap mugF Blob)
    (hs : Opt.structLoop fuel fuel s.blocks topo0 (Opt.revCfg s.blocks topo0) = some rl) :
    nock (C ooBody (C s.toNoun optC)) ooBody
      = nock (C (C (C (listNoun A rl.1) (jarN rl.2.1)) (blN rl.2.2))
          (C (jarN (Opt.revCfg s.blocks topo0)) (C (listNoun A topo0) (C ooBody (C s.toNoun optC))))) ooAfter := by
  have hn := oo_loop fuel s.need.toNoun s.nargs fuel s.blocks topo0 _ rl hl hs
  have hbb := bb_gate s.blocks hl fuel topo0 h0
  obtain ⟨TS, hsi, hTS⟩ := si_gate topo0
  have hrev := rev_gate s.blocks hl topo0 TS hTS
  have hL := optC_layer2
  have h4a := bb_at
  have h5a := rev_at
  have hsy := sy_at
  have hsya := sy_arm
  unfold ooL at hn
  unfold Straight.toNoun blN
  conv => lhs; arg 2; unfold ooBody
  generalize optC = OC at hL hn hbb hrev h4a h5a
  generalize HoonMap.toNoun Blob.toNoun s.blocks = BL at hn hbb hrev ⊢
  generalize ooLoop = LP at hn ⊢
  simp [nock_exec, hL, h4a, bb_arm, hbb, h5a, rev_arm, hsy, hsya, hsi, hrev, hn]

/-- **`+optimize-once`**: where `optimizeOnce fuel P` returns `r` on a
straight function whose blocks have no `%lti`, the gate returns `[again
s']`, given the links of `+alias` and `+trim-trace-hints`. -/
theorem oo_gate (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P) (hT : TrimLink P) (fuel : Nat)
    (s : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (r : Bool × Straight (TreapMap mugF))
    (h : Opt.optimizeOnce fuel P s = some r) :
    nock (C ooBody (C s.toNoun optC)) ooBody = some (C (flag r.1) r.2.toNoun) := by
  simp only [Opt.optimizeOnce, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨topo0, h0, rl, hs, ra, ha, bt, htr, bd, hd, r1, h1, r2, h2, r3, h3, rfl⟩ := h
  have hl0 : NoLti rl.2.2 := structLoop_noLti fuel fuel s.blocks topo0 _ rl hl hs
  have hla : NoLti ra.2 := (hA s.nargs rl.2.2 rl.2.1 rl.1 ra hl0 ha).1
  have hlt : NoLti bt := (hT ra.2 _ _ bt hla htr).1
  have hld : NoLti bd := noLti_dead hd hlt
  have hl1 : NoLti r1.2 := noLti_hops (ch := r1.1) (bl' := r1.2) h1 hld
  have hl2 : NoLti r2.2 := noLti_rub (ch := r2.1) (bl' := r2.2) h2 hl1
  rw [oo_pre fuel s hl topo0 h0 rl hs]
  have hsN : s.toNoun = C s.need.toNoun (C (A s.nargs) (HoonMap.toNoun Blob.toNoun s.blocks)) := rfl
  rw [hsN, oo_s0, oo_alias P hA _ _ _ _ _ _ _ ra hl0 ha, oo_skimrev _ _ _ _ _ _ _ hla,
    oo_trimdead P hT _ _ _ _ _ _ _ bd _ _ hla htr hd, oo_hops fuel _ _ _ _ _ _ _ _ _ h1,
    oo_rub _ _ _ _ _ _ _ _ _ _ h2, oo_rem fuel _ _ _ _ _ _ _ _ _ _ hl2 r3 h3, oo_fin]
  rfl

/-- The round keeps `NoLti`. -/
theorem optimizeOnce_noLti (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P) (hT : TrimLink P) (fuel : Nat)
    (s : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (r : Bool × Straight (TreapMap mugF))
    (h : Opt.optimizeOnce fuel P s = some r) : NoLti r.2.blocks := by
  simp only [Opt.optimizeOnce, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨topo0, h0, rl, hs, ra, ha, bt, htr, bd, hd, r1, h1, r2, h2, r3, h3, rfl⟩ := h
  have hl0 : NoLti rl.2.2 := structLoop_noLti fuel fuel s.blocks topo0 _ rl hl hs
  have hla : NoLti ra.2 := (hA s.nargs rl.2.2 rl.2.1 rl.1 ra hl0 ha).1
  have hlt : NoLti bt := (hT ra.2 _ _ bt hla htr).1
  have hld : NoLti bd := noLti_dead hd hlt
  have hl1 : NoLti r1.2 := noLti_hops (ch := r1.1) (bl' := r1.2) h1 hld
  have hl2 : NoLti r2.2 := noLti_rub (ch := r2.1) (bl' := r2.2) h2 hl1
  exact noLti_mid (ch := r3.1) (bl' := r3.2) h3 hl2

end Compiler
end Formalization
