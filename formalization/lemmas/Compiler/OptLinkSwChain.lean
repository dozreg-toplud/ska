import lemmas.Compiler.OptLinkSwTest

/-!
# `+switch-chains`: the gate `chain-of`

```hoon
  =/  chain-of
    |=  p=@uwoo
    ^-  (list test)
    =/  t=(unit test)  (test-of p)
    ?~  t  ~
    :-  u.t
    =/  nb=blob  (~(got by blocks) miss.u.t)
    ?.  &(?=(~ par.nb) ?=(~ body.nb))  ~
    =/  rev-miss  (~(get ja rev) miss.u.t)
    ?.  |(=(rev-miss ~[p y.u.t]) =(rev-miss ~[y.u.t p]))  ~
    =/  t2=(unit test)  (test-of miss.u.t)
    ?~  t2  ~
    ?.  =(s.u.t2 s.u.t)  ~
    $(p miss.u.t)
```

The gate runs on `[p S4]` (`swS4`, `test-of` at its head).  `sw_chain`:
**where `chainOf fuel` returns `cs`, the gate returns the noun of `cs`**, by
induction on the fuel, through `sw_test` at `p` and at `miss.u.t`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem listNoun_eq_pair2 (a b : Nat) : ∀ l : List Nat, (listNoun A l = C (A a) (C (A b) (A 0))) ↔ l = [a, b]
  | [] => by simp [listNoun]
  | [q] => by simp [listNoun]
  | [q, q'] => by simp [listNoun]
  | q :: q' :: q'' :: l => by simp [listNoun]

theorem listNoun_nil_iff {α : Type} (f : α → Noun) (l : List α) : (A 0 = listNoun f l) ↔ l = [] := by
  cases l <;> simp [listNoun]

/-- **The gate `chain-of`**: where `chainOf fuel` returns `cs`, the gate on
the noun of `p` returns the noun of `cs`. -/
theorem sw_chain (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TOPO USES : Noun)
    (hU : UsesRel USES (Opt.usesOf bl)) :
    ∀ (fuel p : Nat) (cs : List Opt.STest), Opt.chainOf bl rev fuel p = some cs →
    nock (C swCHB (C (A p) (swS4 (HoonMap.toNoun Blob.toNoun bl) TOPO (jarN rev) USES))) swCHB
      = some (listNoun stestN cs) := by
  intro fuel
  induction fuel with
  | zero => intro p cs h; simp [Opt.chainOf] at h
  | succ k ih =>
    intro p cs h
    simp only [Opt.chainOf] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    have hT := sw_test bl rev TOPO USES hU p
    rw [ht] at hT
    have hL := optC_layer2
    cases t with
    | none =>
      simp only [Option.some.injEq] at h
      subst h
      unfold toG at hT
      unfold swS4
      generalize swS3 _ _ _ _ = S3 at hT ⊢
      conv => lhs; arg 2; unfold swCHB
      simp [nock_exec, hT, unitNoun, listNoun]
    | some t =>
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨nb, hnb, hrest⟩ := Option.bind_eq_some_iff.mp hrest
      have hg := blocks_got bl t.miss
      rw [hnb] at hg
      obtain ⟨npar, nbody, nfin⟩ := nb
      simp only [Option.map_some, Blob.toNoun] at hg
      have hj := jar_get rev t.miss
      unfold toG at hT
      by_cases hc1 : npar = [] ∧ nbody = []
      · obtain ⟨rfl, rfl⟩ := hc1
        simp only [and_self, not_true_eq_false, if_false] at hrest
        by_cases hc2 : Opt.getJa rev t.miss = [p, t.y] ∨ Opt.getJa rev t.miss = [t.y, p]
        · simp only [hc2, not_true_eq_false, if_false] at hrest
          obtain ⟨t2, ht2, hrest⟩ := Option.bind_eq_some_iff.mp hrest
          have hT2 := sw_test bl rev TOPO USES hU t.miss
          rw [ht2] at hT2
          unfold toG at hT2
          cases t2 with
          | none =>
            simp only [Option.some.injEq] at hrest
            subst hrest
            unfold swS4 swS3 swG at *
            generalize optC = OC at hL hT hT2
            generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hT2
            conv => lhs; arg 2; unfold swCHB
            by_cases hc2a : Opt.getJa rev t.miss = [p, t.y]
            · rw [hc2a] at hj
              simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode]
            · have hc2b := hc2.resolve_left hc2a
              have hne : ¬ t.y = p := fun e => hc2a (by rw [hc2b, e])
              rw [hc2b] at hj
              simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode, hne, Ne.symm hne]
          | some t2 =>
            by_cases hs : t2.s = t.s
            · simp only [hs, ne_eq, not_true_eq_false, if_false] at hrest
              have ih' := ih t.miss rest hrest
              unfold swS4 swS3 swG at *
              generalize optC = OC at hL hT hT2 ih'
              generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hT2 ih'
              conv => lhs; arg 2; unfold swCHB
              by_cases hc2a : Opt.getJa rev t.miss = [p, t.y]
              · rw [hc2a] at hj
                simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                  ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode, hs, ih']
              · have hc2b := hc2.resolve_left hc2a
                have hne : ¬ t.y = p := fun e => hc2a (by rw [hc2b, e])
                rw [hc2b] at hj
                simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                  ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode, hs, ih', hne, Ne.symm hne]
            · simp only [hs, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at hrest
              subst hrest
              unfold swS4 swS3 swG at *
              generalize optC = OC at hL hT hT2
              generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT hT2
              conv => lhs; arg 2; unfold swCHB
              by_cases hc2a : Opt.getJa rev t.miss = [p, t.y]
              · rw [hc2a] at hj
                simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                  ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode, hs]
              · have hc2b := hc2.resolve_left hc2a
                have hne : ¬ t.y = p := fun e => hc2a (by rw [hc2b, e])
                rw [hc2b] at hj
                simp [nock_exec, hT, hT2, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
                  ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode, hs, hne, Ne.symm hne]
        · simp only [hc2, not_false_eq_true, if_true, Option.some.injEq] at hrest
          subst hrest
          have hc2' := hc2
          simp only [not_or] at hc2'
          unfold swS4 swS3 swG at *
          generalize optC = OC at hL hT
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT
          generalize Opt.getJa rev t.miss = RM at hj hc2'
          conv => lhs; arg 2; unfold swCHB
          simp [nock_exec, hT, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg,
            ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hj, stestN, eqCode, listNoun_eq_pair2, hc2'.1, hc2'.2]
      · simp only [hc1, not_false_eq_true, if_true, Option.some.injEq] at hrest
        subst hrest
        unfold swS4 swS3 swG at *
        generalize optC = OC at hL hT
        generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hT
        conv => lhs; arg 2; unfold swCHB
        by_cases hp : npar = []
        · subst hp
          have hb : ¬ nbody = [] := fun e => hc1 ⟨rfl, e⟩
          simp [nock_exec, hT, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, stestN, eqCode,
            listNoun_nil_iff, hb]
        · simp [nock_exec, hT, unitNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, stestN, eqCode,
            listNoun_nil_iff, hp]

end Compiler
end Formalization
