import lemmas.Compiler.CompMapRegs

/-!
# `+chase` of the `|^` core of `+to-straight`

`+chase` (core arm `21`, battery axis `13` of `tsCoreBat`) is a gate whose
body is the trap `tsChaseBody`:

```hoon
|-  ^-  jmp
=/  b=blob  (~(got by blocks) there.j)
?.  ?=(%hop -.fin.b)  j
?.  (bypassable branch b)  j
?>  ?=(~ args.j)
$(j t.fin.b)
```

The loop may not return (a cycle of bypassable hops), and so may the model
`chase` (a `partial_fixpoint`).  The link has two directions: what `chase`
returns the loop returns (`ch_loop_of_chase`, by `chase.partial_correctness`),
and what the loop returns `chase` returns (`ch_chase_of_loop`, by induction
on the depth of calls, `iterN`, with an oracle that answers the loop's own
calls from `iterN k` and every other call from `nock`).  Both rest on one
step lemma for any such oracle (`ch_stepW`).

The core `CORE` of the loop is any noun with the blocks at `4094`, `layer2`
at `0x1ffffffff` and the arm `+bypassable` at `46`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **`+bypassable`** on `[branch b]`: `bypassable branch b`. -/
theorem ts_byp_gen (S : Noun) (br : Bool) (b : Blob) :
    nock (C tsBypBody (C (C (loob br) (Blob.toNoun b)) S)) tsBypBody = some (loob (bypassable br b)) := by
  obtain ⟨par, body, fin⟩ := b
  cases br <;>
  cases par with
  | cons r rs => simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob]
  | nil =>
    cases body with
    | cons op ops => simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob]
    | nil =>
      cases fin with
      | hop t =>
        obtain ⟨args, there⟩ := t
        cases args <;> simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob,
          Termin.toNoun, Jmp.toNoun, Tag.hop]
      | _ => simp [nock_exec, tsBypBody, Blob.toNoun, listNoun, bypassable, loob, Termin.toNoun, Tag.hop,
          Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-- The arm `+bypassable` of the core: the gate builder. -/
def tsBypArm : Noun := C (A 8) (C (C (A 1) tsGE) (C (C (A 1) tsBypBody) (C (A 0) (A 1))))

theorem ts_byp_arm (S : Noun) : nock S tsBypArm = some (C tsBypBody (C tsGE S)) := by
  unfold tsBypArm; generalize tsBypBody = B; simp [nock_exec]

/-- The trap of `+chase`. -/
def tsChaseBody : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 122)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 29) (C (A 0) (A 23))) (C (A 0) (A 3)))))) (C (A 0) (A 0))))) (C (A 0) (A 61))))) (C (A 0) (A 61)))))))

/-- The battery of the gate `+chase`: the trap, kicked. -/
def tsChaseBat : Noun := C (A 8) (C (C (A 1) tsChaseBody) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

theorem ts_chase_at : slot? 13 tsCoreBat
    = some (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (A 0)))) (C (C (A 1) tsChaseBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The subject of the trap of `+chase` on `[branch j]` in the core `CORE`. -/
def chL (br : Bool) (j : Jmp) (CORE : Noun) : Noun :=
  C tsChaseBody (C tsChaseBat (C (C (loob br) (Jmp.toNoun j)) CORE))

theorem ch_ne1 : by.arm ≠ tsChaseBody := by decide
theorem ch_ne2 : by.got.arm ≠ tsChaseBody := by decide
theorem ch_ne3 : by.got.battery ≠ tsChaseBody := by decide
theorem ch_ne4 : tsBypArm ≠ tsChaseBody := by decide
theorem ch_ne5 : tsBypBody ≠ tsChaseBody := by decide

/-- One step of the loop of `+chase`, with the loop's own call to `call`. -/
def chStep (call : Noun → Noun → Option Noun) (bs : TreapMap mugF Blob) (br : Bool) (CORE : Noun)
    (j : Jmp) : Option Noun :=
  (HoonMap.get bs j.there).bind fun b =>
    match b.fin with
    | Termin.hop t =>
        if bypassable br b then
          (if j.args = [] then call (chL br t CORE) tsChaseBody else Option.none)
        else some (Jmp.toNoun j)
    | _ => some (Jmp.toNoun j)

/-- **One step of the loop of `+chase`** under any oracle `call` that is
`nock` on every formula but the trap's. -/
theorem ch_stepW (call : Noun → Noun → Option Noun)
    (hcall : ∀ s f, f ≠ tsChaseBody → call s f = nock s f)
    (bs : TreapMap mugF Blob) (br : Bool) (CORE : Noun)
    (hB : slot? 4094 CORE = some (HoonMap.toNoun Blob.toNoun bs))
    (hL : slot? 0x1ffffffff CORE = some layer2) (hY : slot? 46 CORE = some tsBypArm) (j : Jmp) :
    nockW call (chL br j CORE) tsChaseBody = chStep call bs br CORE j := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have h1 := fun s => hcall s _ ch_ne1
  have h2 := fun s => hcall s _ ch_ne2
  have h3 := fun s => hcall s _ ch_ne3
  have h4 := fun s => hcall s _ ch_ne4
  have h5 := fun s => hcall s _ ch_ne5
  obtain ⟨args, there⟩ := j
  have hget := getF_hoonMap Blob.toNoun bs there
  unfold chStep chL
  conv => { lhs; arg 3; unfold tsChaseBody }
  generalize HoonMap.toNoun Blob.toNoun bs = BN at hB hget
  cases e : HoonMap.get bs there with
  | none =>
    have hg := got_gate_nil layer2 hgc (A there) BN (by rw [hget, e]; rfl)
    simp [nock_exec, Jmp.toNoun, hB, hL, h1, h2, h3, by_arm, by.arm_at, by.got.arm_at, got_arm, hg]
  | some b =>
    have hg := got_gate layer2 hgc (A there) BN (Blob.toNoun b) (by rw [hget, e]; rfl)
    have hby := fun S => ts_byp_gen S br b
    obtain ⟨par, body, fin⟩ := b
    cases fin with
    | hop t =>
      have hby' := hby
      cases hbp : bypassable br ⟨par, body, Termin.hop t⟩ <;> rw [hbp] at hby' <;>
        simp only [Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop] at hby' <;> cases args <;>
        simp [nock_exec, Jmp.toNoun, hB, hL, hY, h1, h2, h3, h4, h5, by_arm, by.arm_at, by.got.arm_at,
          got_arm, hg, hby', hbp, ts_byp_arm, Blob.toNoun, Termin.toNoun, Tag.hop, listNoun]
    | _ =>
      simp [nock_exec, Jmp.toNoun, hB, hL, h1, h2, h3, by_arm, by.arm_at, by.got.arm_at,
        got_arm, hg, Blob.toNoun, Termin.toNoun, Tag.hop,
        Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-- **What `chase` returns, the loop returns.** -/
theorem ch_loop_of_chase (bs : TreapMap mugF Blob) (br : Bool) (CORE : Noun)
    (hB : slot? 4094 CORE = some (HoonMap.toNoun Blob.toNoun bs))
    (hL : slot? 0x1ffffffff CORE = some layer2) (hY : slot? 46 CORE = some tsBypArm) :
    ∀ j j', chase bs br j = some j' → nock (chL br j CORE) tsChaseBody = some (Jmp.toNoun j') := by
  refine chase.partial_correctness bs br _ ?_
  intro ch ih j r h
  rw [nock_eq_nockW, ch_stepW nock (fun _ _ _ => rfl) bs br CORE hB hL hY j]
  unfold chStep
  cases e : HoonMap.get bs j.there with
  | none => simp [e] at h
  | some b =>
    simp only [e, Option.bind_some, bind, Option.bind] at h ⊢
    obtain ⟨par, body, fin⟩ := b
    cases fin with
    | hop t =>
      simp only at h ⊢
      cases hbp : bypassable br ⟨par, body, Termin.hop t⟩
      · simp only [hbp] at h ⊢
        simp at h; subst h; rfl
      · by_cases ha : j.args = []
        · simp only [hbp, ha] at h ⊢
          simp at h
          exact ih t r h
        · simp [hbp, ha] at h
    | _ => simp at h ⊢; subst h; rfl

/-- **What the loop returns, `chase` returns**, by induction on the depth
of calls. -/
theorem ch_chase_of_loop (bs : TreapMap mugF Blob) (br : Bool) (CORE : Noun)
    (hB : slot? 4094 CORE = some (HoonMap.toNoun Blob.toNoun bs))
    (hL : slot? 0x1ffffffff CORE = some layer2) (hY : slot? 46 CORE = some tsBypArm) :
    ∀ (k : Nat) (j : Jmp) (out : Noun), iterN k (chL br j CORE) tsChaseBody = some out →
      ∃ j', chase bs br j = some j' := by
  intro k
  induction k with
  | zero => intro j out h; simp [iterN] at h
  | succ k ih =>
    intro j out h
    let call' : Noun → Noun → Option Noun := fun s f => if f = tsChaseBody then iterN k s f else nock s f
    have hbel : ∀ s f, Below? (iterN k s f) (call' s f) := by
      intro s f
      by_cases hf : f = tsChaseBody
      · simp only [call', hf, if_true]; exact Below?.refl _
      · simp only [call', hf, if_false]; exact iterN_sound k s f
    have hcall : ∀ s f, f ≠ tsChaseBody → call' s f = nock s f := by
      intro s f hf; simp only [call', hf, if_false]
    have h2 := nockW_mono hbel _ _ out (by rw [iterN_succ] at h; exact h)
    rw [ch_stepW call' hcall bs br CORE hB hL hY j] at h2
    unfold chStep at h2
    rw [chase.eq_1]
    cases e : HoonMap.get bs j.there with
    | none => simp [e] at h2
    | some b =>
      simp only [e, Option.bind_some, bind, Option.bind] at h2 ⊢
      obtain ⟨par, body, fin⟩ := b
      cases fin with
      | hop t =>
        simp only at h2 ⊢
        cases hbp : bypassable br ⟨par, body, Termin.hop t⟩
        · simp [hbp]
        · by_cases ha : j.args = []
          · simp only [hbp, ha, if_true] at h2 ⊢
            simp only [call', if_true] at h2
            exact ih t out h2
          · simp [hbp, ha] at h2
      | _ => simp

/-- **`+chase`** in the loop: the noun of `chase bs br j`, a crash when
`chase` has no value (a missing block, a hop with arguments, or a cycle). -/
theorem ch_nock (bs : TreapMap mugF Blob) (br : Bool) (CORE : Noun)
    (hB : slot? 4094 CORE = some (HoonMap.toNoun Blob.toNoun bs))
    (hL : slot? 0x1ffffffff CORE = some layer2) (hY : slot? 46 CORE = some tsBypArm) (j : Jmp) :
    nock (chL br j CORE) tsChaseBody = (chase bs br j).map Jmp.toNoun := by
  cases e : chase bs br j with
  | some j' => exact ch_loop_of_chase bs br CORE hB hL hY j j' e
  | none =>
    cases h : nock (chL br j CORE) tsChaseBody with
    | none => rfl
    | some out =>
      obtain ⟨k, hk⟩ := iterN_complete h
      obtain ⟨j', hj⟩ := ch_chase_of_loop bs br CORE hB hL hY k j out hk
      rw [e] at hj; cases hj

end Compiler
end Formalization
