import lemmas.Ska.CompHintTree
import lemmas.Ska.CompHintFlat

/-!
# Instances of `CallTreeH` (README Gaps 24.12)

The contract at the top for three formulas with hints inside the class, and
`#guard`s that the model compiles them (`finishLUCH` is `some`, with the
environment of the dump, `envH`, `sndH`), so the contracts are not vacuous:

* `exNs`: `[11 %foo [2 [0 3] [0 2]]]` (a static hint not kept around an
  indirect call);
* `exCons`: `[[11 %foo [2 [0 3] [0 2]]] [0 3]]` (the hint as the head of a
  cons: hinted, so `+past` parks the tail's need);
* `exSeven`: `[7 [0 3] [11 [%foo [1 7]] [2 [0 1] [0 1]]]]` (a dynamic hint
  not kept, with a safe clue, as the `q` of `[7 p q]`).

None of the 39 dumped formulas is in the class: their hints not kept sit
around pure formulas (`[11 %foo [4 [0 3]]]`, `[11 [%foo [1 7]] [4 [0 3]]]`),
and the others are kept (`%bout`, `%xray`, `%spot`, `%hunk`, `%mean`, `%12`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `[1 k]` is a safe clue. -/
theorem ClueSafe.quote (lib : Lib) (P : Noun → Prop) (k : Noun) : ClueSafe lib P (C (A 1) k) :=
  ⟨fun _ h => ⟨k, quote_hq1 h⟩, fun _ => ⟨k, quote_hq2⟩⟩

/-- `%foo`, a tag neither `hint-static` nor `hint-dynamic`. -/
def tagFoo : Nat := 0x6f6f66

theorem foo_static : hintStatic tagFoo = false := by decide
theorem foo_dynamic : hintDynamic tagFoo = false := by decide

def indN (a b : Nat) : Nomm := Nomm.n2 (Nomm.n0 a) (Nomm.n0 b) Option.none
def indF (a b : Nat) : Noun := n3 (A 2) (slot a) (slot b)

def exNs : Nomm := Nomm.n11s tagFoo (indN 3 2) (A 0)
def exNsF : Noun := n3 (A 11) (A tagFoo) (indF 3 2)
def exCons : Nomm := Nomm.cons exNs (Nomm.n0 3)
def exConsF : Noun := C exNsF (slot 3)
def exSeven : Nomm := Nomm.n7 (Nomm.n0 3) (Nomm.n11d tagFoo (Nomm.n1 (A 7)) (indN 1 1) (A 0))
def exSevenF : Noun := n3 (A 7) (slot 3) (n3 (A 11) (C (A tagFoo) (C (A 1) (A 7))) (indF 1 1))

#guard (finishLUCH (S := LS) (Map := FM) envH sndH exNs).isSome
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exCons).isSome
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exSeven).isSome

section
variable {lib : Lib} {env : CallEnv} {N : Needs}

theorem callTreeH_ind (P : Noun → Prop) (a b : Nat) : CallTreeH lib env N P true (indF a b) (indN a b) :=
  CallTreeH.base (CallTreeD.ind (CallTreeD.n0 a) (CallTreeD.n0 b)) rfl

theorem callTreeH_exNs (P : Noun → Prop) : CallTreeH lib env N P true exNsF exNs :=
  CallTreeH.n11s (A 0) (callTreeH_ind P 3 2) foo_static rfl

theorem callTreeH_exCons (P : Noun → Prop) : CallTreeH lib env N P true exConsF exCons :=
  CallTreeH.cons (callTreeH_exNs P) (CallTreeH.base (CallTreeD.n0 3) rfl)

theorem callTreeH_exSeven (P : Noun → Prop) : CallTreeH lib env N P true exSevenF exSeven :=
  CallTreeH.seven (CallTreeH.base (CallTreeD.n0 3) rfl)
    (CallTreeH.n11d (A 0) (callTreeH_ind _ 1 1) foo_dynamic rfl (ClueSafe.quote lib _ (A 7)) rfl rfl rfl)

end

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The contract at the top of `[[11 %foo [2 [0 3] [0 2]]] [0 3]]`**, both halves, traces included. -/
theorem contract_exCons (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd exCons = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exConsF [s] c ∧ ContractBwd lib N s exConsF [s] c := by
  have H := finishLUCH_contractCallTreeH (S := S) lib (callTreeH_exCons (env := env) (N := N) (fun _ => True)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of `[7 [0 3] [11 [%foo [1 7]] [2 [0 1] [0 1]]]]`.** -/
theorem contract_exSeven (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd exSeven = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exSevenF [s] c ∧ ContractBwd lib N s exSevenF [s] c := by
  have H := finishLUCH_contractCallTreeH (S := S) lib (callTreeH_exSeven (env := env) (N := N) (fun _ => True)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
