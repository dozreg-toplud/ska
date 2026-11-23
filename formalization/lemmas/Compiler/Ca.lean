import lemmas.Hoon.Basic
import lemmas.Pill.Arm.Ca
import lemmas.Ska.Sock

/-!
The arms of the compiler's core `+ca` (operations on capes, near the top of
`desk/lib/nock-compilation.hoon`) compute track B's models in
`lemmas/Ska/Sock.lean`, on the nouns `Cape.toNoun`.

This file is a plain file, not a module, because the models are in plain
files; a plain file sees the bodies of the arm files.

The gates of `+ca` have the core of `+ca` as their context; those that call
`+con:ca` read it from there (`CaConIn`).  Proved here: `hed`, `tel`, `con`,
`all`, `int`, `uni`, `lack`.  Not here: `app` (it reads `+so`), `pat`, `lot`,
`yea` (they read `+cap`, `+mas`, `+peg`, `+weld` of `hoon.hoon` deep in the
context), and `dif`, which the generator does not name.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

abbrev CaConIn (c : Noun) : Prop := slot? ca.con.axis c = some ca.con.arm

theorem cape_toNoun_inj : ∀ {a b : Cape}, a.toNoun = b.toNoun → a = b
  | Cape.yes, Cape.yes, _ => rfl
  | Cape.no, Cape.no, _ => rfl
  | Cape.cell h t, Cape.cell h' t', e => by
    simp only [Cape.toNoun, Noun.cell.injEq] at e
    rw [cape_toNoun_inj e.1, cape_toNoun_inj e.2]
  | Cape.yes, Cape.no, e => by simp [Cape.toNoun] at e
  | Cape.yes, Cape.cell _ _, e => by simp [Cape.toNoun] at e
  | Cape.no, Cape.yes, e => by simp [Cape.toNoun] at e
  | Cape.no, Cape.cell _ _, e => by simp [Cape.toNoun] at e
  | Cape.cell _ _, Cape.yes, e => by simp [Cape.toNoun] at e
  | Cape.cell _ _, Cape.no, e => by simp [Cape.toNoun] at e

theorem cape_toNoun_eq (a b : Cape) : a.toNoun = b.toNoun ↔ a = b :=
  ⟨cape_toNoun_inj, fun h => h ▸ rfl⟩

/-! ## The arms build their gates -/

@[nock_exec] theorem ca_hed_arm (c : Noun) :
    nock c ca.hed.arm = some (C ca.hed.battery (C (A 1) c)) := by
  nock_open ca.hed.arm; simp only [nock_exec]

@[nock_exec] theorem ca_tel_arm (c : Noun) :
    nock c ca.tel.arm = some (C ca.tel.battery (C (A 1) c)) := by
  nock_open ca.tel.arm; simp only [nock_exec]

@[nock_exec] theorem ca_con_arm (c : Noun) :
    nock c ca.con.arm = some (C ca.con.battery (C (C (A 1) (A 1)) c)) := by
  nock_open ca.con.arm; simp only [nock_exec]

@[nock_exec] theorem ca_all_arm (c : Noun) :
    nock c ca.all.arm = some (C ca.all.battery (C (A 1) c)) := by
  nock_open ca.all.arm; simp only [nock_exec]

@[nock_exec] theorem ca_int_arm (c : Noun) :
    nock c ca.int.arm = some (C ca.int.battery (C (C (A 1) (A 1)) c)) := by
  nock_open ca.int.arm; simp only [nock_exec]

@[nock_exec] theorem ca_uni_arm (c : Noun) :
    nock c ca.uni.arm = some (C ca.uni.battery (C (C (A 1) (A 1)) c)) := by
  nock_open ca.uni.arm; simp only [nock_exec]

@[nock_exec] theorem ca_lack_arm (c : Noun) :
    nock c ca.lack.arm = some (C ca.lack.battery (C (C (A 1) (A 1)) c)) := by
  nock_open ca.lack.arm; simp only [nock_exec]

/-! ## The gates -/

theorem ca_hed_gate (ctx : Noun) (c : Cape) :
    nock (C ca.hed.battery (C c.toNoun ctx)) ca.hed.battery = some (Ca.hed c).toNoun := by
  nock_open ca.hed.battery
  cases c <;> simp [nock_exec, Cape.toNoun, Ca.hed]

theorem ca_tel_gate (ctx : Noun) (c : Cape) :
    nock (C ca.tel.battery (C c.toNoun ctx)) ca.tel.battery = some (Ca.tel c).toNoun := by
  nock_open ca.tel.battery
  cases c <;> simp [nock_exec, Cape.toNoun, Ca.tel]

@[nock_exec] theorem ca_con_gate (ctx : Noun) (h t : Cape) :
    nock (C ca.con.battery (C (C h.toNoun t.toNoun) ctx)) ca.con.battery
      = some (Ca.con h t).toNoun := by
  nock_open ca.con.battery
  cases h <;> cases t <;> simp [nock_exec, Cape.toNoun, Ca.con]

theorem ca_all_gate (ctx : Noun) : ∀ (c : Cape),
    nock (C ca.all.battery (C c.toNoun ctx)) ca.all.battery = some (Hoon.loob (Ca.all c))
  | Cape.yes => by nock_open ca.all.battery; simp [nock_exec, Cape.toNoun, Ca.all]
  | Cape.no => by nock_open ca.all.battery; simp [nock_exec, Cape.toNoun, Ca.all]
  | Cape.cell h t => by
    have ih := ca_all_gate ctx h
    have it := ca_all_gate ctx t
    nock_open ca.all.battery
    cases hh : Ca.all h <;> cases ht : Ca.all t <;>
      simp_all [nock_exec, Cape.toNoun, Ca.all]

theorem ca_int_gate (ctx : Noun) (hc : CaConIn ctx) : ∀ (a b : Cape),
    nock (C ca.int.battery (C (C a.toNoun b.toNoun) ctx)) ca.int.battery
      = some (Ca.int a b).toNoun
  | Cape.cell ah aT, Cape.cell bh bT => by
    have ih := ca_int_gate ctx hc ah bh
    have it := ca_int_gate ctx hc aT bT
    nock_open ca.int.battery
    by_cases e : Cape.cell ah aT = Cape.cell bh bT
    · rw [e]; simp [nock_exec, Ca.int]
    · have e' : ¬ (C ah.toNoun aT.toNoun = C bh.toNoun bT.toNoun) := by
        intro h; apply e
        exact cape_toNoun_inj (show (Cape.cell ah aT).toNoun = (Cape.cell bh bT).toNoun from h)
      rw [Ca.int, if_neg e]
      simp [nock_exec, Cape.toNoun, e', hc, ca_con_arm, ih, it]
  | Cape.yes, Cape.yes => by nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.yes, Cape.no => by nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.yes, Cape.cell _ _ => by
    nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.no, Cape.yes => by nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.no, Cape.no => by nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.no, Cape.cell _ _ => by
    nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.cell _ _, Cape.yes => by
    nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]
  | Cape.cell _ _, Cape.no => by
    nock_open ca.int.battery; simp [nock_exec, Cape.toNoun, Ca.int]

theorem ca_uni_gate (ctx : Noun) (hc : CaConIn ctx) : ∀ (a b : Cape),
    nock (C ca.uni.battery (C (C a.toNoun b.toNoun) ctx)) ca.uni.battery
      = some (Ca.uni a b).toNoun
  | Cape.cell ah aT, Cape.cell bh bT => by
    have ih := ca_uni_gate ctx hc ah bh
    have it := ca_uni_gate ctx hc aT bT
    nock_open ca.uni.battery
    by_cases e : Cape.cell ah aT = Cape.cell bh bT
    · rw [e]; simp [nock_exec, Ca.uni]
    · have e' : ¬ (C ah.toNoun aT.toNoun = C bh.toNoun bT.toNoun) := by
        intro h; apply e
        exact cape_toNoun_inj (show (Cape.cell ah aT).toNoun = (Cape.cell bh bT).toNoun from h)
      rw [Ca.uni, if_neg e]
      simp [nock_exec, Cape.toNoun, e', hc, ca_con_arm, ih, it]
  | Cape.yes, Cape.yes => by nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.yes, Cape.no => by nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.yes, Cape.cell _ _ => by
    nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.no, Cape.yes => by nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.no, Cape.no => by nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.no, Cape.cell _ _ => by
    nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.cell _ _, Cape.yes => by
    nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]
  | Cape.cell _ _, Cape.no => by
    nock_open ca.uni.battery; simp [nock_exec, Cape.toNoun, Ca.uni]

theorem ca_lack_gate (ctx : Noun) (hc : CaConIn ctx) : ∀ (a b : Cape),
    nock (C ca.lack.battery (C (C a.toNoun b.toNoun) ctx)) ca.lack.battery
      = some (Ca.lack a b).toNoun
  | Cape.no, b => by
    nock_open ca.lack.battery; cases b <;> simp [nock_exec, Cape.toNoun, Ca.lack]
  | Cape.yes, Cape.yes => by nock_open ca.lack.battery; simp [nock_exec, Cape.toNoun, Ca.lack]
  | Cape.yes, Cape.no => by nock_open ca.lack.battery; simp [nock_exec, Cape.toNoun, Ca.lack]
  | Cape.cell _ _, Cape.yes => by
    nock_open ca.lack.battery; simp [nock_exec, Cape.toNoun, Ca.lack]
  | Cape.cell _ _, Cape.no => by
    nock_open ca.lack.battery; simp [nock_exec, Cape.toNoun, Ca.lack]
  | Cape.yes, Cape.cell bh bT => by
    have ih := ca_lack_gate ctx hc Cape.yes bh
    have it := ca_lack_gate ctx hc Cape.yes bT
    nock_open ca.lack.battery
    simp [nock_exec, Cape.toNoun, Ca.lack, Ca.hed, Ca.tel, hc, ca_con_arm] at ih it ⊢
    simp [nock_exec, ih, it, ca_con_gate]
  | Cape.cell ah aT, Cape.cell bh bT => by
    have ih := ca_lack_gate ctx hc ah bh
    have it := ca_lack_gate ctx hc aT bT
    nock_open ca.lack.battery
    by_cases e : Cape.cell ah aT = Cape.cell bh bT
    · cases e; simp [nock_exec, Cape.toNoun, Ca.lack]
    · have e' : ¬ (C ah.toNoun aT.toNoun = C bh.toNoun bT.toNoun) := by
        intro h; apply e
        exact cape_toNoun_inj (show (Cape.cell ah aT).toNoun = (Cape.cell bh bT).toNoun from h)
      have e2 : ¬ (ah = bh ∧ aT = bT) := fun ⟨h1, h2⟩ => e (by rw [h1, h2])
      simp [nock_exec, Cape.toNoun, Ca.lack, Ca.hed, Ca.tel, e', e2, hc, ca_con_arm, ih, it]

end Compiler
end Formalization
