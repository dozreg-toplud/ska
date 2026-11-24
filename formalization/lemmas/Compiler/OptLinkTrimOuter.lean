import lemmas.Compiler.OptLinkTrimInner

/-!
# `+trim-trace-hints`: the outer trap, `unsafe`

```hoon
  =|  [unsafe=(set key) out=(map @uwoo (map key @ud))]
  |-  ^-  (set key)
  ?~  topo  unsafe
  =/  b  (~(got by blocks) i.topo)
  =/  open=(map key @ud)
    %+  roll  (~(get ja rev) i.topo)
    |=  [p=@uwoo acc=(map key @ud)]
    %-  (~(uno by acc) (~(gut by out) p *(map key @ud)))
    |=([k=key v=@ud w=@ud] (max v w))
  =/  body  body.b
  ...
```

* `tr_rgate`: the gate of the `+roll` over the predecessors is `Cnt.join`
  with the counts of `out` at the predecessor (`cnt_uno`, `out_gut`).
* `tr_oturn`: a turn of the outer trap at a block of `topo` reaches the
  inner trap over its body with `open` the `trimOpen` of the model.
* `tr_otrap`: **where `trimWalk` returns, the outer trap returns a set of
  key nouns with the unsafe keys of the model** (`UnsRel`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The gate of the `+roll`** over the predecessors: the counts joined
with those of `out` at the predecessor. -/
theorem tr_rgate (S OUTN TC BL TOPO REV bN : Noun) (out : TreapMap mugF Opt.Cnt) (ho : OutRel OUTN out)
    (p : Nat) (N : Noun) (c : Opt.Cnt) (hc : CntRel N c) :
    ∃ N', nock (C trRGate (C (C (A p) N) (C bN (trOT S OUTN TC BL TOPO REV)))) trRGate = some N' ∧
      CntRel N' (c.join ((HoonMap.get out p).getD Opt.Cnt.empty)) := by
  obtain ⟨B, hgut, hB⟩ := out_gut ho p
  have hRS : slot? 0x3ffffff (C trRGate (C (C (A p) N) (C bN (trOT S OUTN TC BL TOPO REV)))) = some layer1 := by
    have h := optC_layer1
    unfold trOT trG
    generalize optC = OC at h
    simp [nock_exec, h]
  obtain ⟨OUT, hu, hO⟩ := cnt_uno hc hB hRS
  refine ⟨OUT, ?_, hO⟩
  have hL := optC_layer2
  have hua := uno_at
  have hout := uno_outer B (C by.battery (C N layer2))
  unfold trOT trG at hu ⊢
  conv => lhs; arg 2; unfold trRGate
  generalize optC = OC at hL hu hgut
  simp [nock_exec, trUnoB, hL, by.arm_at, by_arm, hua, uno_arm, by.gut.arm_at, gut_arm, hgut, hout, hu]

/-- **A turn of the outer trap** at a block of `topo`: the inner trap over
its body, `open` the counts the model starts the block with. -/
theorem tr_oturn (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (o : Nat) (b : Blob)
    (hb : HoonMap.get bl o = some b) (topo : List Nat) (out : TreapMap mugF Opt.Cnt) (S OUTN TC : Noun)
    (ho : OutRel OUTN out) :
    ∃ OPN, CntRel OPN (Opt.trimOpen rev out o) ∧
      nock (trOT S OUTN TC (HoonMap.toNoun Blob.toNoun bl) (listNoun A (o :: topo)) (jarN rev)) trOTrap
        = nock (trIT (listNoun Pole.toNoun b.body) OPN (Blob.toNoun b) S OUTN TC (HoonMap.toNoun Blob.toNoun bl)
            (listNoun A (o :: topo)) (jarN rev)) trITrap := by
  have hroll := roll_gate_rel A CntRel (fun p s => some (s.join ((HoonMap.get out p).getD Opt.Cnt.empty)))
    layer2 trRGate (A 0) (C (Blob.toNoun b) (trOT S OUTN TC (HoonMap.toNoun Blob.toNoun bl)
      (listNoun A (o :: topo)) (jarN rev))) (Opt.getJa rev o) Opt.Cnt.empty (A 0) (Opt.trimOpen rev out o)
    (fun p _ s N s' hR hs => by
      cases hs
      exact tr_rgate S OUTN TC _ _ _ _ out ho p N s hR) cntRel_nil
    (by rw [foldlM_some]; rfl)
  obtain ⟨OPN, hn, hO⟩ := hroll
  refine ⟨OPN, hO, ?_⟩
  rw [← listNoun_map_listN] at hn
  have hL := optC_layer2
  have hg := blocks_got bl o
  rw [hb] at hg
  have hj := jar_get rev o
  unfold trOT trG at hn
  unfold trIT trOT trG
  conv => lhs; arg 2; unfold trOTrap
  generalize optC = OC at hL hn
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hn ⊢
  generalize trITrap = IT at hn ⊢
  simp only [Option.map_some] at hg
  simp only [Blob.toNoun, listNoun] at hn hg
  simp [nock_exec, listNoun, trOGot, trORoll, trGetJa, trRBunt, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
    roll.arm_at, roll_arm, ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, hn, Blob.toNoun]

/-- **The outer trap**: where `trimWalk` returns, the trap returns a set of
key nouns with the unsafe keys of the model. -/
theorem tr_otrap (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TC : Noun) :
    ∀ (topo : List Nat) (out : TreapMap mugF Opt.Cnt) (uns : Opt.Uns) (S OUTN : Noun) (u' : Opt.Uns),
    UnsRel S uns → OutRel OUTN out → Opt.trimWalk bl rev topo out uns = some u' →
    ∃ S', nock (trOT S OUTN TC (HoonMap.toNoun Blob.toNoun bl) (listNoun A topo) (jarN rev)) trOTrap = some S' ∧
      UnsRel S' u' := by
  intro topo
  induction topo with
  | nil =>
    intro out uns S OUTN u' hu ho h
    simp only [Opt.trimWalk, Option.some.injEq] at h
    subst h
    refine ⟨S, ?_, hu⟩
    unfold trOT
    conv => lhs; arg 2; unfold trOTrap
    simp [nock_exec, listNoun]
  | cons o topo ih =>
    intro out uns S OUTN u' hu ho h
    simp only [Opt.trimWalk] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨OPN, hO, e1⟩ := tr_oturn bl rev o b hb topo out S OUTN TC ho
    obtain ⟨OPN', S1, h1, h2, e2⟩ := tr_ibody (Blob.toNoun b) OUTN TC (HoonMap.toNoun Blob.toNoun bl)
      (listNoun A (o :: topo)) (jarN rev) b.body _ uns OPN S hO hu
    obtain ⟨S2, OUTN2, h3, h4, e3⟩ := tr_iend o b topo _ _ out OPN' S1 OUTN TC
      (HoonMap.toNoun Blob.toNoun bl) (jarN rev) h1 h2 ho
    obtain ⟨S3, e4, h5⟩ := ih _ _ S2 OUTN2 u' h3 h4 h
    exact ⟨S3, by rw [e1, e2, e3, e4], h5⟩

end Compiler
end Formalization
