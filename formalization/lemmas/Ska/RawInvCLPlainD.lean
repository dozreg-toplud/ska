import lemmas.Ska.CompSimBody

/-!
# The class with direct calls

README Gaps 14 (b), track D.  `PlainD`: `PlainN` with direct calls (`[2 p q]`
with any `info`): no `%6`, no hint.  Its runs are those of `runLCM env true`
(a direct call goes through `+mono-try-call`, `callDM`).  `plainN_plainD`.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Comp

/-- **No `%6`, no hint; indirect and direct calls.** -/
def PlainD : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => PlainD p
  | Nomm.n4 p => PlainD p
  | Nomm.n5 p q => PlainD p ∧ PlainD q
  | Nomm.cons p q => PlainD p ∧ PlainD q
  | Nomm.n7 p q => PlainD p ∧ PlainD q
  | Nomm.n10 _ v q => PlainD v ∧ PlainD q
  | Nomm.n2 p q _ => PlainD p ∧ PlainD q
  | _ => False

theorem plainN_plainD : ∀ (nm : Nomm), PlainN nm → PlainD nm
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n3 p, h => plainN_plainD p h
  | Nomm.n4 p, h => plainN_plainD p h
  | Nomm.n5 p q, h => ⟨plainN_plainD p h.1, plainN_plainD q h.2⟩
  | Nomm.cons p q, h => ⟨plainN_plainD p h.1, plainN_plainD q h.2⟩
  | Nomm.n7 p q, h => ⟨plainN_plainD p h.1, plainN_plainD q h.2⟩
  | Nomm.n10 _ v q, h => ⟨plainN_plainD v h.1, plainN_plainD q h.2⟩
  | Nomm.n2 p q Option.none, h => ⟨plainN_plainD p h.1, plainN_plainD q h.2⟩
  | Nomm.n2 _ _ (some _), h => h.elim
  | Nomm.n6 _ _ _, h => h.elim
  | Nomm.n11s _ _ _, h => h.elim
  | Nomm.n11d _ _ _ _, h => h.elim
  | Nomm.n12 _ _, h => h.elim
  | Nomm.mean _ _ _ _ _, h => h.elim

end Raw
end SkaModel
end Formalization
