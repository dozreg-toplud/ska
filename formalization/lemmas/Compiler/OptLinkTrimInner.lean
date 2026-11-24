import lemmas.Compiler.OptLinkTrimRel
import lemmas.Hoon.IntIn

/-!
# `+trim-trace-hints`: the inner trap over a body, the end of a block

```hoon
  =/  body  body.b
  |-  ^-  (set key)
  ?^  body
    =/  op  i.body
    ?^  hint=(trace op)
      =/  n=@ud  (~(gut by open) key.u.hint 0)
      ?:  open.u.hint  $(body t.body, open (~(put by open) key.u.hint +(n)))
      ?:  (lte n 1)  $(body t.body, open (~(del by open) key.u.hint))
      $(body t.body, open (~(put by open) key.u.hint (dec n)))
    ?:  ?=(pole-not-crashing -.op)  $(body t.body)
    $(body t.body, unsafe (~(uni in unsafe) ~(key by open)))
  =?  unsafe  !?=(?(%clq %eqq %brz %hop) -.fin.b)
    (~(uni in unsafe) ~(key by open))
  ^$(topo t.topo, out (~(put by out) i.topo open))
```

`trOT` is the subject of the outer trap, `trIT` that of the inner trap; the
gate `trace` sits in both with its context `TC`.

* `tr_istep`: a turn of the inner trap on an op is `trimStep`, the step of
  the model's `trimBody`.
* `tr_ibody`: the inner trap over a body is `trimBody`, up to its end.
* `tr_iend`: the end of a block: the `=?` of `unsafe` (`finQuiet`) and the
  next turn of the outer trap with `out` put at the block.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The subjects -/

/-- The gate core of `+trim-trace-hints`. -/
def trG (BL TOPO REV : Noun) : Noun := C trBody (C (C BL (C TOPO REV)) optC)

/-- The subject of the outer trap: `[trOTrap [[unsafe out] [trace gate]]]`. -/
def trOT (S OUTN TC BL TOPO REV : Noun) : Noun :=
  C trOTrap (C (C S OUTN) (C (C trTraceB (C trSBunt TC)) (trG BL TOPO REV)))

/-- The subject of the inner trap: `[trITrap [body [open [b outer]]]]`. -/
def trIT (BODY OPN bN S OUTN TC BL TOPO REV : Noun) : Noun :=
  C trITrap (C BODY (C OPN (C bN (trOT S OUTN TC BL TOPO REV))))

theorem slot_tail_of' {k : Nat} {s y z : Noun} (h : slot? k s = some y) (h3 : slot? 3 y = some z) :
    slot? (2 * k + 1) s = some z := by
  cases y with
  | atom _ => simp [nock_exec] at h3
  | cell a b =>
    simp only [nock_exec, Option.some.injEq] at h3
    subst h3
    exact slot?_right h

theorem optC_layer1 : slot? 0x3ffff optC = some layer1 := by
  have h := slot_tail_of' optC_layer2 layer2_layer1
  simpa using h

/-! ## The model's step -/

/-- One op of the model's `trimBody`. -/
def trimStep (op : Pole) (c : Opt.Cnt) (u : Opt.Uns) : Opt.Cnt × Opt.Uns :=
  match Opt.traceKey op with
  | some (true, k) => (c.set k (c k + 1), u)
  | some (false, k) => (if c k ≤ 1 then c.set k 0 else c.set k (c k - 1), u)
  | none => if Opt.notCrashing op then (c, u) else (c, u.add c)

theorem trimBody_cons (op : Pole) (rest : List Pole) (c : Opt.Cnt) (u : Opt.Uns) :
    Opt.trimBody (op :: rest) c u = Opt.trimBody rest (trimStep op c u).1 (trimStep op c u).2 := by
  simp only [Opt.trimBody, trimStep]
  cases Opt.traceKey op with
  | none => cases Opt.notCrashing op <;> rfl
  | some p => obtain ⟨b, k⟩ := p; cases b <;> rfl

/-! ## A turn of the inner trap -/

/-- **A turn of the inner trap on an op** is `trimStep`. -/
theorem tr_istep (op : Pole) (rest : List Pole) (c : Opt.Cnt) (u : Opt.Uns)
    (OPN S bN OUTN TC BL TOPO REV : Noun) (hc : CntRel OPN c) (hu : UnsRel S u) :
    ∃ OPN' S', CntRel OPN' (trimStep op c u).1 ∧ UnsRel S' (trimStep op c u).2 ∧
      nock (trIT (listNoun Pole.toNoun (op :: rest)) OPN bN S OUTN TC BL TOPO REV) trITrap
        = nock (trIT (listNoun Pole.toNoun rest) OPN' bN S' OUTN TC BL TOPO REV) trITrap := by
  have hL := optC_layer2
  have hL1 := optC_layer1
  have htr := tr_trace op TC
  have hnc := tr_nct op
  unfold trIT trOT trG
  cases e : Opt.traceKey op with
  | none =>
    have ht : traceN op = A 0 := by simp [traceN, e]
    rw [ht] at htr
    cases hn : Opt.notCrashing op with
    | true =>
      refine ⟨OPN, S, by simpa [trimStep, e, hn] using hc, by simpa [trimStep, e, hn] using hu, ?_⟩
      rw [hn] at hnc
      conv => lhs; arg 2; unfold trITrap trITest trIStep trIHint trINoHint trIHintC
      generalize optC = OC at hL hL1
      simp [nock_exec, listNoun, htr, hnc, loob, trSkipK]
    | false =>
      obtain ⟨K, S', hk, hs, hS'⟩ := uns_add hu hc
      refine ⟨OPN, S', by simpa [trimStep, e, hn] using hc, by simpa [trimStep, e, hn] using hS', ?_⟩
      rw [hn] at hnc
      conv => lhs; arg 2; unfold trITrap trITest trIStep trIHint trINoHint trIHintC
      generalize optC = OC at hL hL1
      simp [nock_exec, listNoun, htr, hnc, loob, trWiden, hL, in.arm_at, in_arm, in.uni.arm_at, uni_in_arm,
        by.arm_at, by_arm, by.key.arm_at, hk, hs]
  | some p =>
    obtain ⟨b, k⟩ := p
    have ht : traceN op = C (A 0) (C (flag b) (keyN k)) := by simp [traceN, e]
    rw [ht] at htr
    have hg := cnt_gut hc k
    cases b with
    | true =>
      obtain ⟨N', hp, hN'⟩ := cnt_put hc k (c k + 1) (by omega)
      refine ⟨N', S, by simpa [trimStep, e] using hN', by simpa [trimStep, e] using hu, ?_⟩
      conv => lhs; arg 2; unfold trITrap trITest trIStep trIHint trINoHint trIHintC
      generalize optC = OC at hL hL1
      simp [nock_exec, listNoun, htr, flag, trHGut, trOpenK, hL, by.arm_at, by_arm, by.gut.arm_at, gut_arm, hg,
        by.put.arm_at, put_arm, hp]
    | false =>
      have hlte := lte_gate layer1 arith_layer1.2.2.2.1 (c k) 1
      have h1a := lte.arm_at
      by_cases hle : c k ≤ 1
      · obtain ⟨N', hd, hN'⟩ := cnt_del hc k
        refine ⟨N', S, by simpa [trimStep, e, hle] using hN', by simpa [trimStep, e] using hu, ?_⟩
        conv => lhs; arg 2; unfold trITrap trITest trIStep trIHint trINoHint trIHintC
        generalize optC = OC at hL hL1
        generalize layer1 = L1 at hL1 hlte h1a
        simp [nock_exec, listNoun, htr, flag, trHGut, trLte, trDelK, hL, hL1, by.arm_at, by_arm, by.gut.arm_at,
          gut_arm, hg, h1a, lte_arm, hlte, hle, loob, by.del.arm_at, del_arm, hd]
      · have hpos : 0 < c k := by omega
        have hdec := dec_gate layer1 (c k) hpos
        have h2a := dec.arm_at
        obtain ⟨N', hp, hN'⟩ := cnt_put hc k (c k - 1) (by omega)
        refine ⟨N', S, by simpa [trimStep, e, hle] using hN', by simpa [trimStep, e] using hu, ?_⟩
        conv => lhs; arg 2; unfold trITrap trITest trIStep trIHint trINoHint trIHintC
        generalize optC = OC at hL hL1
        generalize layer1 = L1 at hL1 hlte h1a hdec h2a
        simp [nock_exec, listNoun, htr, flag, trHGut, trLte, trDecK, hL, hL1, by.arm_at, by_arm, by.gut.arm_at,
          gut_arm, hg, h1a, lte_arm, hlte, hle, loob, h2a, dec_arm, hdec, by.put.arm_at, put_arm, hp]

/-- **The inner trap over a body** is `trimBody`, up to its end. -/
theorem tr_ibody (bN OUTN TC BL TOPO REV : Noun) : ∀ (body : List Pole) (c : Opt.Cnt) (u : Opt.Uns) (OPN S : Noun),
    CntRel OPN c → UnsRel S u →
    ∃ OPN' S', CntRel OPN' (Opt.trimBody body c u).1 ∧ UnsRel S' (Opt.trimBody body c u).2 ∧
      nock (trIT (listNoun Pole.toNoun body) OPN bN S OUTN TC BL TOPO REV) trITrap
        = nock (trIT (A 0) OPN' bN S' OUTN TC BL TOPO REV) trITrap := by
  intro body
  induction body with
  | nil => intro c u OPN S hc hu; exact ⟨OPN, S, hc, hu, rfl⟩
  | cons op rest ih =>
    intro c u OPN S hc hu
    obtain ⟨O1, S1, h1, h2, e1⟩ := tr_istep op rest c u OPN S bN OUTN TC BL TOPO REV hc hu
    obtain ⟨O2, S2, h3, h4, e2⟩ := ih _ _ O1 S1 h1 h2
    rw [trimBody_cons]
    exact ⟨O2, S2, h3, h4, e1.trans e2⟩

/-- The test `!?=(?(%clq %eqq %brz %hop) -.fin.b)`. -/
theorem tr_fint (fin : Termin) (a b c par body d : Noun) :
    nock (C a (C b (C c (C (C par (C body fin.toNoun)) d)))) trFinT = some (loob (!Opt.finQuiet fin)) := by
  unfold trFinT
  cases fin <;> simp [nock_exec, eqCode_atom, Termin.toNoun, Opt.finQuiet, loob, Tag.clq, Tag.eqq, Tag.brn,
    Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-- **The end of a block**: the `=?` of `unsafe` and the next turn of the
outer trap, `out` put at the block. -/
theorem tr_iend (o : Nat) (b : Blob) (topo : List Nat) (c : Opt.Cnt) (u : Opt.Uns) (out : TreapMap mugF Opt.Cnt)
    (OPN S OUTN TC BL REV : Noun) (hc : CntRel OPN c) (hu : UnsRel S u) (ho : OutRel OUTN out) :
    ∃ S' OUTN', UnsRel S' (if Opt.finQuiet b.fin then u else u.add c) ∧ OutRel OUTN' (HoonMap.put out o c) ∧
      nock (trIT (A 0) OPN (Blob.toNoun b) S OUTN TC BL (listNoun A (o :: topo)) REV) trITrap
        = nock (trOT S' OUTN' TC BL (listNoun A topo) REV) trOTrap := by
  have hL := optC_layer2
  obtain ⟨N', hp, hN'⟩ := out_put ho hc o
  have hf := tr_fint b.fin
  unfold trIT trOT trG Blob.toNoun
  cases hq : Opt.finQuiet b.fin with
  | true =>
    refine ⟨S, N', by simpa [hq] using hu, hN', ?_⟩
    rw [hq] at hf
    conv => lhs; arg 2; unfold trITrap trITest trIEnd trEUpd trENext
    generalize optC = OC at hL
    simp [nock_exec, listNoun, hf, loob, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hp]
  | false =>
    obtain ⟨K, S', hk, hs, hS'⟩ := uns_add hu hc
    refine ⟨S', N', by simpa [hq] using hS', hN', ?_⟩
    rw [hq] at hf
    conv => lhs; arg 2; unfold trITrap trITest trIEnd trEUpd trENext
    generalize optC = OC at hL
    simp [nock_exec, listNoun, hf, loob, trEUni, hL, in.arm_at, in_arm, in.uni.arm_at, uni_in_arm, by.arm_at,
      by_arm, by.key.arm_at, hk, hs, by.put.arm_at, put_arm, hp]

end Compiler
end Formalization
