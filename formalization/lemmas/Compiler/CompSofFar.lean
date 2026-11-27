import lemmas.Compiler.CompSofEdit

/-!
# `+sound-far` (README Gaps 19, item (f))

K arm `5467`, gate battery `sfBat` (329 cells, `CompSofNouns.lean`).  The
gate tests `%none`/`%this` (yes at once), then under its `~+` (the dynamic
hint `[11 [%memo 1 0] ..]`, transparent) pushes the halves of the need and
runs the `?+` over the nomm: a recursive `$(..)` is `[9 2 10 ..]` on the
gate's core with `nom`, `ned` (and on `%2` `dep`) edited, so every call
runs `sfBat` on `[nom ned cod dep]` in `compK`.  On a direct `%2` with
`dep > 0` it reads `nomm:(~(got by cod) b)` (`got_gate` of `layer2`) and
`(dec dep)`; on `%10` it slams `+need-ord-edit` (`noe_gateK`).

* `CodeNomms cod CODE`: the noun `CODE` holds, for every bell with a nomm in
  the table `cod`, an entry whose head is that nomm.
* **`sf_at`**: one depth: where `sfAt cod dep rec` returns, the gate returns
  the same loobean, given the gate at `dep - 1` wherever `rec` returns.
* **`sf_gate`**: where `soundFar cod dep` returns, the gate returns its
  loobean, for every nomm, need and depth.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The code table read from `code.long-ska`**: every nomm of `cod` is the
head of the value at its bell in the map noun `CODE`. -/
def CodeNomms (cod : Bell → Option Nomm) (CODE : Noun) : Prop :=
  ∀ b m, cod b = some m → ∃ V, getF mugF b.toNoun CODE = some (C (A 0) V) ∧ slot? 2 V = some m.toNoun

theorem andO_cases {x y : Option Bool} {s : Bool} (h : andO x y = some s) :
    (x = some false ∧ s = false) ∨ (x = some true ∧ y = some s) := by
  rcases x with _ | _ | _ <;> simp_all [andO]

/-- On `%this` or `%none` the gate is yes at once. -/
theorem sf_triv (nomN CODE : Noun) (dep : Nat) {ned : NeedOrd} (h : ned = NeedOrd.this ∨ ned = NeedOrd.none) :
    nock (C sfBat (C (C nomN (C ned.toNoun (C CODE (A dep)))) compK)) sfBat = some (loob true) := by
  rcases h with rfl | rfl <;> (conv => lhs; arg 2; unfold sfBat) <;>
    simp [nock_exec, NeedOrd.toNoun, Tag.this, Tag.none, loob]

theorem ned_cases (ned : NeedOrd) :
    (ned = NeedOrd.this ∨ ned = NeedOrd.none) ∨ ∃ a b, ned = NeedOrd.pair a b ∨ ned = NeedOrd.both a b := by
  cases ned <;> simp

/-- One case of `+sound-far`: the tests, the hints, the recursive calls. -/
macro "sf_simp" : tactic => `(tactic|
  (simp [nock_exec, nock_ite, NeedOrd.toNoun, Nomm.toNoun, Tag.none, Tag.this, Tag.both, Tag.mean, ord_eqCode,
     wut_nomm_toNoun, hd_eq_nomm, eqCode_atom, loob, ite_some, *]))

/-- `sf_simp` with the unit of a call's `info` opened. -/
macro "sf_simpU" : tactic => `(tactic|
  (simp [nock_exec, nock_ite, NeedOrd.toNoun, Nomm.toNoun, Tag.none, Tag.this, Tag.both, Tag.mean, ord_eqCode,
     wut_nomm_toNoun, hd_eq_nomm, eqCode_atom, loob, ite_some, unitNoun, *]))

/-- **One depth of `+sound-far`**: where `sfAt cod dep rec` returns, the gate
returns the same loobean, given that the gate at `dep - 1` returns `rec`'s
value wherever `rec` returns. -/
theorem sf_at (cod : Bell → Option Nomm) (CODE : Noun) (hc : CodeNomms cod CODE) (dep : Nat)
    (rec : Nomm → NeedOrd → Option Bool)
    (hrec : ∀ m ned s, dep ≠ 0 → rec m ned = some s →
      nock (C sfBat (C (C m.toNoun (C ned.toNoun (C CODE (A (dep - 1))))) compK)) sfBat = some (loob s)) :
    ∀ (nom : Nomm) (ned : NeedOrd) (s : Bool), sfAt cod dep rec nom ned = some s →
      nock (C sfBat (C (C nom.toNoun (C ned.toNoun (C CODE (A dep)))) compK)) sfBat = some (loob s) := by
  intro nom
  induction nom with
  | cons p q ihp ihq =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt, ordHalves] at h
      rcases andO_cases h with ⟨h1, rfl⟩ | ⟨h1, h2⟩
      · have e1 := ihp _ _ h1
        clear ihp ihq h h1 hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        sf_simp
      · have e1 := ihp _ _ h1
        have e2 := ihq _ _ h2
        clear ihp ihq h h1 h2 hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        cases s <;> sf_simp
  | n6 p q r _ ihq ihr =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      rcases andO_cases h with ⟨h1, rfl⟩ | ⟨h1, h2⟩
      · have e1 := ihq _ _ h1
        clear ihq ihr h h1 hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        sf_simp
      · have e1 := ihq _ _ h1
        have e2 := ihr _ _ h2
        clear ihq ihr h h1 h2 hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        cases s <;> sf_simp
  | n10 ax v q ihv ihq =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      obtain ⟨⟨d, r⟩, he, h⟩ := Option.bind_eq_some_iff.1 h
      have hno := (noe_gateK ax _).trans (congrArg (Option.map _) he)
      simp only [NeedOrd.toNoun, Tag.both, Option.map_some] at hno
      have hK := compK_noe
      have hna := noe_arm
      rcases andO_cases h with ⟨h1, rfl⟩ | ⟨h1, h2⟩
      · have e1 := ihv _ _ h1
        clear ihv ihq h h1 hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        sf_simp
      · have e1 := ihv _ _ h1
        have e2 := ihq _ _ h2
        clear ihv ihq h h1 h2 hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        cases s <;> sf_simp
  | n7 p q _ ihq =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      have e1 := ihq _ _ h
      clear ihq h hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      cases s <;> sf_simp
  | n11s tag q body ihq =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      have e1 := ihq _ _ h
      clear ihq h hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      cases s <;> sf_simp
  | n11d tag hf q body _ ihq =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      have e1 := ihq _ _ h
      clear ihq h hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      cases s <;> sf_simp
  | mean p bl q body k _ ihq =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      have e1 := ihq _ _ h
      clear ihq h hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      cases s <;> sf_simp
  | n2 p q info _ _ =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      rcases info with _ | ⟨bl, k⟩
      · simp [sfAt] at h
        subst h
        clear hrec
        try simp only [NeedOrd.toNoun, Tag.both] at e1
        try simp only [NeedOrd.toNoun, Tag.both] at e2
        conv => lhs; arg 2; unfold sfBat
        sf_simpU
      · by_cases hd : dep = 0
        · subst hd
          simp [sfAt] at h
          subst h
          clear hrec
          try simp only [NeedOrd.toNoun, Tag.both] at e1
          try simp only [NeedOrd.toNoun, Tag.both] at e2
          conv => lhs; arg 2; unfold sfBat
          sf_simpU
        · simp [sfAt, hd] at h
          obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨V, hgot, hv⟩ := hc bl m hm
          have e1 := hrec m _ s hd hr
          have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
            bl.toNoun CODE V hgot
          have hL := compK_layer2
          have hL1 := compK_layer1
          have hba := by.arm_at
          have hbg := by.got.arm_at
          have hdc := dec_gate layer1 dep (Nat.pos_of_ne_zero hd)
          have hda := dec.arm_at
          have hd' : ¬ (0 = dep) := fun e => hd e.symm
          clear hrec h hr
          try simp only [NeedOrd.toNoun, Tag.both] at e1
          conv => lhs; arg 2; unfold sfBat
          cases s <;> sf_simpU
  | n0 ax =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      subst h
      clear hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      by_cases ha : ax = 0
      · subst ha; sf_simp
      · have ha' : ¬ (0 = ax) := fun e => ha e.symm
        sf_simp
  | n1 k =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      subst h
      clear hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      sf_simp
  | n3 p _ =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      subst h
      clear hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      sf_simp
  | n4 p _ =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      subst h
      clear hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      sf_simp
  | n5 p q _ _ =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      subst h
      clear hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      sf_simp
  | n12 p q _ _ =>
    intro ned s h
    rcases ned_cases ned with hn | ⟨a, b, rfl | rfl⟩
    · rcases hn with rfl | rfl <;> simp [sfAt] at h <;> subst h <;> exact sf_triv _ _ _ (by simp)
    all_goals
      simp [sfAt] at h
      subst h
      clear hrec
      try simp only [NeedOrd.toNoun, Tag.both] at e1
      try simp only [NeedOrd.toNoun, Tag.both] at e2
      conv => lhs; arg 2; unfold sfBat
      sf_simp

/-- **`+sound-far` is `soundFar`** where the model returns: for every
depth, nomm and need, the gate on `[nom ned CODE dep]` in `compK` returns
the model's loobean. -/
theorem sf_gate (cod : Bell → Option Nomm) (CODE : Noun) (hc : CodeNomms cod CODE) :
    ∀ (dep : Nat) (nom : Nomm) (ned : NeedOrd) (s : Bool), soundFar cod dep nom ned = some s →
      nock (C sfBat (C (C nom.toNoun (C ned.toNoun (C CODE (A dep)))) compK)) sfBat = some (loob s)
  | 0, nom, ned, s, h => sf_at cod CODE hc 0 _ (fun _ _ _ h0 => absurd rfl h0) nom ned s h
  | d + 1, nom, ned, s, h => sf_at cod CODE hc (d + 1) _ (fun m ned s _ hr => sf_gate cod CODE hc d m ned s hr) nom ned s h

end Compiler
end Formalization
