import lemmas.Compiler.SkaCore
import lemmas.KernelRfl

/-!
# `+msg-ca`

```hoon
++  msg-ca
  |=  [a=cape b=cape]
  ^-  cape
  =*  msg  .
  ?:  =(a b)  a
  ?:  |(?=(@ a) ?=(@ b))  &
  [(msg -.a -.b) (msg +.a +.b)]
```

against `msgCa` of `Ska/RunStep.lean`, on every two capes and in every
context: the gate reads nothing from its context.  Because of `=*  msg  .`
each recursion pushes the gate itself (`[8 [0 1] ...]`) and slams it with the
sample edited, so the recursion runs the same battery on the same context.

The generator names no noun of `+msg-ca`, so its battery is defined here
(`msgCaBat`, the noun at axis `12023` of `ana`, `msg_ca_bat_at`, checked by
the kernel); it is wanted as `msg_ca.*` at the next regeneration.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-- `?=(@ (slot x))`. -/
def msgCaAtom (x : Nat) : Noun := C (A 6) (C (C (A 3) (C (A 0) (A x))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))

/-- The test `|(?=(@ a) ?=(@ b))` of `+msg-ca`: `?:(?=(@ a) & ?:(?=(@ b) & |))`. -/
def msgCaTest : Noun :=
  C (A 6) (C (msgCaAtom 12) (C (C (A 1) (A 0)) (C (A 6) (C (msgCaAtom 13) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))

/-- A recursion of `+msg-ca`: push the gate, slam it on `[(slot x) (slot y)]`. -/
def msgCaRec (x y : Nat) : Noun :=
  C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (C (A 0) (A x)) (C (A 0) (A y)))) (C (A 0) (A 2)))))))

/-- The battery of the gate `+msg-ca`. -/
def msgCaBat : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 13))))
    (C (C (A 0) (A 12))
      (C (A 6) (C msgCaTest (C (C (A 1) (A 0)) (C (msgCaRec 56 58) (msgCaRec 57 59)))))))

/-- The battery is the pill's: the noun at axis `12023` of `ana`. -/
theorem msg_ca_bat_at : slot? 12023 ana = some msgCaBat := by kernel_rfl

theorem cape_toNoun_ne {a b : Cape} (h : a ≠ b) : a.toNoun ≠ b.toNoun :=
  fun e => h (SkaModel.Ana.Cape.toNoun_inj a b e)

/-- **`+msg-ca` computes `msgCa`** on every two capes, in every context
`ctx`: by induction on the first cape. -/
theorem msg_ca_gate (ctx : Noun) (a : Cape) : ∀ b : Cape,
    nock (C msgCaBat (C (C a.toNoun b.toNoun) ctx)) msgCaBat = some (msgCa a b).toNoun := by
  induction a with
  | yes =>
    intro b
    nock_open msgCaBat
    cases b <;> simp [nock_exec, msgCaTest, msgCaAtom, msgCa, Cape.toNoun, eqCode]
  | no =>
    intro b
    nock_open msgCaBat
    cases b <;> simp [nock_exec, msgCaTest, msgCaAtom, msgCa, Cape.toNoun, eqCode]
  | cell ah aT ihh iht =>
    intro b
    cases b with
    | yes =>
      nock_open msgCaBat
      simp [nock_exec, msgCaTest, msgCaAtom, msgCa, Cape.toNoun, eqCode]
    | no =>
      nock_open msgCaBat
      simp [nock_exec, msgCaTest, msgCaAtom, msgCa, Cape.toNoun, eqCode]
    | cell bh bT =>
      have h1 := ihh bh
      have h2 := iht bT
      by_cases e : Cape.cell ah aT = Cape.cell bh bT
      · cases e
        nock_open msgCaBat
        simp [nock_exec, msgCa, eqCode]
      · have e' := cape_toNoun_ne e
        simp only [Cape.toNoun] at e'
        nock_open msgCaBat
        rw [msgCa, if_neg e]
        simp [nock_exec, msgCaTest, msgCaAtom, msgCaRec, eqCode, Cape.toNoun, e', h1, h2]

end Compiler
end Formalization
