import lemmas.Compiler.OptLinkAlRn

/-!
# `+alias`: the noun of an `info-reg` and `join-reg` (phase 2 of the plan, README Gaps 13)

```hoon
  ++  join-reg
    |=  [a=info-reg b=info-reg]
    ^-  info-reg
    :*  &(is-cell.a is-cell.b)
        ?&  |(is-loob.a ?=([~ ?] has-imm.a))
            |(is-loob.b ?=([~ ?] has-imm.b))
        ==
        (~(int in hed-of.a) hed-of.b)
        (~(int in tel-of.a) tel-of.b)
        ?:(=(has-hed.a has-hed.b) has-hed.a ~)
        ?:(=(has-tel.a has-tel.b) has-tel.a ~)
        ?:(=(dec-of.a dec-of.b) dec-of.a ~)
        ?:(=(has-imm.a has-imm.b) has-imm.a ~)
    ==
```

* `infoN x lb hs ts`: the noun of an `info-reg` with the facts of `x`, the
  flag `lb` for `is-loob` and the sets `hs`, `ts` for `hed-of`, `tel-of`.
* `InfoRel N x`: `N` is such a noun with the sets holding the members of the
  lists (`SawRel`) and `is-loob` equal to `x.isLoob` wherever `x.loobImm` is
  false (header 2 of `Ska/OptAliasModel.lean`: `join-info` may set it under
  a loobean `has-imm`).
* `al_jreg`: **`join-reg` of two related nouns is related to `joinReg`**; its
  `is-loob` is exactly that of `joinReg`, which reads `is-loob` only beside
  `loobImm`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of an `info-reg`. -/
def infoN (x : Opt.InfoReg) (lb : Bool) (hs ts : Noun) : Noun :=
  C (flag x.isCell) (C (flag lb) (C hs (C ts (C (unitNoun A x.hasHed) (C (unitNoun A x.hasTel)
    (C (unitNoun A x.decOf) (unitNoun id x.hasImm)))))))

/-- An `info-reg` noun holds the facts of `x`. -/
def InfoRel (N : Noun) (x : Opt.InfoReg) : Prop :=
  ∃ lb hs ts, N = infoN x lb hs ts ∧ SawRel hs x.hedOf ∧ SawRel ts x.telOf ∧
    (lb || x.loobImm) = (x.isLoob || x.loobImm)

theorem unitNoun_inj' {α : Type} {f : α → Noun} (hf : ∀ x y, f x = f y → x = y) (o o' : Option α) :
    unitNoun f o = unitNoun f o' ↔ o = o' := by
  constructor
  · intro h
    cases o <;> cases o' <;> simp [unitNoun] at h ⊢
    exact hf _ _ h
  · rintro rfl; rfl

theorem unitNoun_A_inj (o o' : Option Nat) : unitNoun A o = unitNoun A o' ↔ o = o' :=
  unitNoun_inj' (fun _ _ h => Noun.atom.inj h) o o'

theorem unitNoun_id_inj (o o' : Option Noun) : unitNoun id o = unitNoun id o' ↔ o = o' :=
  unitNoun_inj' (fun _ _ h => h) o o'

theorem unitNoun_none {α : Type} (f : α → Noun) : unitNoun f none = A 0 := rfl

/-- `+int:in` of two sets of registers: the filter. -/
theorem sawRel_int {S T U : Noun} {l m : List Nat} (hS : SawRel S l) (hT : SawRel T m)
    (hU : IsSet mugF U) (hk : ∀ k, Has U k ↔ Has S k ∧ Has T k) : SawRel U (l.filter (· ∈ m)) := by
  refine ⟨hU, fun k => ?_⟩
  rw [hk, hS.2, hT.2]
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, ⟨n', hn', e⟩⟩
    have e' : n = n' := Noun.atom.inj e
    subst e'
    exact ⟨n, List.mem_filter.2 ⟨hn, by simpa using hn'⟩, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hn
    exact ⟨⟨n, h1, rfl⟩, ⟨n, by simpa using h2, rfl⟩⟩

/-- The core in which the arms of the `|^` core of `+alias` run: `optC`
where the core has it. -/
def alCtx (X G Y Z : Noun) : Noun := C X (C G (C Y (C Z optC)))

/-- The subject of the body of `join-reg`. -/
def alJRS (Na Nb X G Y Z : Noun) : Noun := C alJRegB (C (C Na Nb) (alCtx X G Y Z))

theorem al_jr_la (x : Opt.InfoReg) (lb : Bool) (hs ts Nb X G Y Z : Noun) :
    nock (alJRS (infoN x lb hs ts) Nb X G Y Z) alJRegLa = some (flag (lb || x.loobImm)) := by
  unfold alJRS infoN
  generalize alCtx X G Y Z = K
  generalize alJRegB = B
  rcases x with ⟨c, l, h, t, hh, ht, d, im⟩
  cases lb <;> rcases im with _ | ⟨_ | _ | n⟩ | ⟨p, q⟩ <;>
    simp [nock_exec, alJRegLa, flag, unitNoun, Opt.InfoReg.loobImm]

theorem al_jr_lb (x : Opt.InfoReg) (lb : Bool) (hs ts Na X G Y Z : Noun) :
    nock (alJRS Na (infoN x lb hs ts) X G Y Z) alJRegLb = some (flag (lb || x.loobImm)) := by
  unfold alJRS infoN
  generalize alCtx X G Y Z = K
  generalize alJRegB = B
  rcases x with ⟨c, l, h, t, hh, ht, d, im⟩
  cases lb <;> rcases im with _ | ⟨_ | _ | n⟩ | ⟨p, q⟩ <;>
    simp [nock_exec, alJRegLb, flag, unitNoun, Opt.InfoReg.loobImm]

theorem nock_cons_of (s F d : Noun) (hF : ∃ b c, F = C b c) :
    nock s (C F d) = (nock s F).bind fun left => (nock s d).bind fun right => some (C left right) := by
  obtain ⟨b, c, rfl⟩ := hF
  exact nock_cell s b c d

/-- **`join-reg`** of two nouns related to `a` and `b` is related to `joinReg a b`. -/
theorem al_jreg (X G Y Z : Noun) {Na Nb : Noun} {a b : Opt.InfoReg} (ha : InfoRel Na a)
    (hb : InfoRel Nb b) :
    ∃ N, nock (alJRS Na Nb X G Y Z) alJRegB = some N ∧ InfoRel N (Opt.joinReg a b) := by
  obtain ⟨la, ha', ta, rfl, hha, hta, hla⟩ := ha
  obtain ⟨lb, hb', tb, rfl, hhb, htb, hlb⟩ := hb
  obtain ⟨H, hH, hHs, hHk⟩ := int_in (mug := mugF) layer2 gorIn_morIn_layer2 ha' hb' hha.1 hhb.1
  obtain ⟨T, hT, hTs, hTk⟩ := int_in (mug := mugF) layer2 gorIn_morIn_layer2 ta tb hta.1 htb.1
  refine ⟨infoN (Opt.joinReg a b) ((la || a.loobImm) && (lb || b.loobImm)) H T, ?_,
    _, H, T, rfl, sawRel_int hha hhb hHs hHk, sawRel_int hta htb hTs hTk, ?_⟩
  · have hL := optC_layer2
    have f1 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF1
        = some (flag (a.isCell && b.isCell)) := by
      unfold alJRS infoN
      generalize alCtx X G Y Z = K
      generalize alJRegB = B
      cases a.isCell <;> cases b.isCell <;> simp [nock_exec, alJRegF1, flag]
    have f2 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF2
        = some (flag ((la || a.loobImm) && (lb || b.loobImm))) := by
      have h1 := al_jr_la a la ha' ta (infoN b lb hb' tb) X G Y Z
      have h2 := al_jr_lb b lb hb' tb (infoN a la ha' ta) X G Y Z
      generalize (la || a.loobImm) = u at h1
      generalize (lb || b.loobImm) = v at h2
      generalize alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z = S at h1 h2
      cases u <;> cases v <;> simp [nock_exec, alJRegF2, flag, h1, h2]
    have f3 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF3 = some H := by
      unfold alJRS infoN alCtx
      generalize optC = OC at hL
      generalize alJRegB = B
      simp [nock_exec, alJRegF3, hL, in.arm_at, in_arm, in.int.arm_at, int_in_arm, hH]
    have f4 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF4 = some T := by
      unfold alJRS infoN alCtx
      generalize optC = OC at hL
      generalize alJRegB = B
      simp [nock_exec, alJRegF4, hL, in.arm_at, in_arm, in.int.arm_at, int_in_arm, hT]
    have f5 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF5
        = some (unitNoun A (if a.hasHed = b.hasHed then a.hasHed else none)) := by
      unfold alJRS infoN
      generalize alCtx X G Y Z = K
      generalize alJRegB = B
      by_cases e : a.hasHed = b.hasHed <;> simp [nock_exec, alJRegF5, eqCode, unitNoun_A_inj, e, unitNoun_none]
    have f6 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF6
        = some (unitNoun A (if a.hasTel = b.hasTel then a.hasTel else none)) := by
      unfold alJRS infoN
      generalize alCtx X G Y Z = K
      generalize alJRegB = B
      by_cases e : a.hasTel = b.hasTel <;> simp [nock_exec, alJRegF6, eqCode, unitNoun_A_inj, e, unitNoun_none]
    have f7 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF7
        = some (unitNoun A (if a.decOf = b.decOf then a.decOf else none)) := by
      unfold alJRS infoN
      generalize alCtx X G Y Z = K
      generalize alJRegB = B
      by_cases e : a.decOf = b.decOf <;> simp [nock_exec, alJRegF7, eqCode, unitNoun_A_inj, e, unitNoun_none]
    have f8 : nock (alJRS (infoN a la ha' ta) (infoN b lb hb' tb) X G Y Z) alJRegF8
        = some (unitNoun id (if a.hasImm = b.hasImm then a.hasImm else none)) := by
      unfold alJRS infoN
      generalize alCtx X G Y Z = K
      generalize alJRegB = B
      by_cases e : a.hasImm = b.hasImm <;> simp [nock_exec, alJRegF8, eqCode, unitNoun_id_inj, e, unitNoun_none]
    conv => lhs; rw [show alJRegB = C alJRegF1 (C alJRegF2 (C alJRegF3 (C alJRegF4 (C alJRegF5 (C alJRegF6
      (C alJRegF7 alJRegF8)))))) from rfl]
    rw [nock_cons_of _ alJRegF1 _ ⟨_, _, rfl⟩, f1, nock_cons_of _ alJRegF2 _ ⟨_, _, rfl⟩, f2,
      nock_cons_of _ alJRegF3 _ ⟨_, _, rfl⟩, f3, nock_cons_of _ alJRegF4 _ ⟨_, _, rfl⟩, f4,
      nock_cons_of _ alJRegF5 _ ⟨_, _, rfl⟩, f5, nock_cons_of _ alJRegF6 _ ⟨_, _, rfl⟩, f6,
      nock_cons_of _ alJRegF7 _ ⟨_, _, rfl⟩, f7, f8]
    rfl
  · rw [hla, hlb]
    rfl
