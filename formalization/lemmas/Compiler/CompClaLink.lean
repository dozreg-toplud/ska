import lemmas.Compiler.CompCtx

/-!
# `+collapse-lazy-atom` of the door of `+comp`, and `+none-equivalent`

`+collapse-lazy-atom` (door axis `13822`, core axis `21502`) checks that the
goal has no arguments, returns `~` when the lazy need is `+none-equivalent`
(arm `2811` of `K`, through `+levy` of layer 2), and otherwise takes the
need of the sure part (`+sure-require-look`) to one register `r`, emitting
a crash block for `there` when the need takes the noun apart, and walks the
lazy need with `ned.sure` set to `[%this r]` with a gate that moves `r` where
a block wants the noun whole and crashes where it wants its parts
(`+crash-need` with `%|`).  On `[sure ~ ~]` the walk is one slam of that
gate at `there`, so `+proxy` is not reached; the gate lemma `cla_gate` covers
it anyway.

The context is fixed by one hypothesis, `slot? 7 ctx = some compK`
(`CompCtx.lean`), which gives `CompIn`, `CompLib` and `CompMolds`.
None of the arms here writes `cache`, `soft` or `sofs`; the gate reads `soft`
through `+crash-need`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

def claG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 27))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1399) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 0) (A 2046)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 4)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 62)) (C (A 0) (A 5)))) (C (C (A 0) (A 2046)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 30)))) (C (C (C (A 0) (A 62)) (C (A 0) (A 2046))) (C (A 8) (C (C (A 9) (C (A 0xabb5a) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 0) (A 60)))) (C (A 0) (A 2))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 2)) (C (A 0) (A 13)))) (C (A 1) (A 0))))))) (C (A 0) (A 2))))))))))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 30)))) (C (C (C (A 0) (A 62)) (C (A 0) (A 2046))) (C (A 8) (C (C (A 9) (C (A 0xabb5a) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 0) (A 60)))) (C (A 0) (A 2))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0xaaae) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 1)) (C (A 0) (A 2))))) (C (A 0) (A 14))))) (C (A 0) (A 2))))))))))))))))))))))))))))))))

def claBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 54)))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2811) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (C (C (A 1) (A 0)) (C (A 0) (A 30))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1399) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 116))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 4)))) (C (C (C (A 0) (A 5)) (C (A 0) (A 1))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 0) (A 2)) (C (A 0) (A 3))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6d6f62)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 503) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 4))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6d6f62)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 247) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (C (A 0) (A 26)) (C (A 0) (A 3)))))))))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 3) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 2)) (C (A 0) (A 247)))) (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 31)))) (C (C (A 0) (A 126)) (C (A 8) (C (C (A 0) (A 247)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 4) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6)))) (C (A 0) (A 250)))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (C (A 7) (C (C (A 9) (C (A 4) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 254)))) (C (C (A 1) claG) (C (A 0) (A 1)))))))))) (C (A 0) (A 2))))))))))))))))))))))))))))))))) (C (A 0) (A 0)))))

def claArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0))))) (C (C (A 1) claBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6d6f74612d797a616c2d657370616c6c6f632d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

def neBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 24))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 48)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 49)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 25)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 25))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 51))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 102)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (A 6) (C (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))

def neArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) neBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x746e656c6176697571652d656e6f6e) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))))

theorem comp_cla_at : slot? 13822 comp.door = some claArm := by kernel_rfl

theorem compK_ne : slot? 2811 compK = some neArm := by kernel_rfl

/-- The arm `none-equivalent` builds its gate. -/
theorem ne_arm (d : Noun) : nock d neArm =
    some (C neBat (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) d)) := by
  unfold neArm; simp only [nock_exec]

/-! ## The test of `lok` -/

/-- The noun of a set is `~` or `[1 ~ ~]` exactly when the set is `small`;
otherwise it is a node of another shape. -/
theorem cs_small_cases (m : CSet) :
    (HoonSet.small m = true ∧ (HoonSet.toNoun m = A 0 ∨
      HoonSet.toNoun m = C (A 1) (C (A 0) (A 0)))) ∨
    (HoonSet.small m = false ∧ ∃ n l r, HoonSet.toNoun m = C n (C l r) ∧
      ¬(n = A 1 ∧ l = A 0 ∧ r = A 0)) := by
  have ht := cs_tree m
  have hp := cs_preorder m
  have hs := cs_isSet m
  have hsm := HoonSet.small_iff m
  generalize HoonSet.toNoun m = L at ht hp hs ⊢
  cases ht with
  | nil =>
    left
    refine ⟨hsm.2 ?_, Or.inl rfl⟩
    intro y hy
    have : (A y) ∈ preorder (A 0) := by rw [hp]; exact List.mem_map_of_mem hy
    simp [preorder] at this
  | @node n l r hl hr =>
    by_cases h : n = A 1 ∧ l = A 0 ∧ r = A 0
    · left
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hsm.2 ?_, Or.inr rfl⟩
      intro y hy
      have : (A y) ∈ preorder (C (A 1) (C (A 0) (A 0))) := by rw [hp]; exact List.mem_map_of_mem hy
      simpa [preorder] using this
    · right
      refine ⟨?_, n, l, r, rfl, h⟩
      cases e : HoonSet.small m
      · rfl
      · exfalso
        have hall := hsm.1 e
        have hone : ∀ z ∈ preorder (C n (C l r)), z = A 1 := by
          intro z hz
          rw [hp] at hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
          rw [hall y hy]
        have hn : n = A 1 := hone n (by simp [preorder])
        subst hn
        unfold IsSet at hs
        simp only [toMap] at hs
        cases hs with
        | node _ _ hgl hgr =>
          by_cases hl0 : l = A 0
          · have hr0 : r ≠ A 0 := fun hr0 => h ⟨rfl, hl0, hr0⟩
            cases hr with
            | nil => exact hr0 rfl
            | @node n' l' r' _ _ =>
              have h1 : n' = A 1 := hone n' (by simp [preorder])
              have := (hgr n' (A 0) (by simp only [toMap]; exact Get.here)).1
              exact this h1
          · cases hl with
            | nil => exact hl0 rfl
            | @node n' l' r' _ _ =>
              have h1 : n' = A 1 := hone n' (by simp [preorder])
              have := (hgl n' (A 0) (by simp only [toMap]; exact Get.here)).1
              exact this h1

/-! ## `+none-equivalent` on `[sure ~ ~]` -/

/-- `+levy` on `~` is `&`, whatever its gate. -/
theorem ne_levy_nil (c X : Noun) :
    nock (C levy.battery (C (C (A 0) X) c)) levy.battery = some (A 0) := by
  nock_open levy.battery
  simp only [nock_exec]
  nock_open levy.loop
  simp [nock_exec]

/-- `+none-equivalent` on a fork-free lazy need. -/
theorem ne_gate (s : Sure CSet) :
    nock (C neBat (C (lazyNoun s) compK)) neBat = some (loob (noneEquivalent s)) := by
  have hL := compK_layer2
  obtain ⟨ned, lok⟩ := s
  nock_open neBat
  rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
  all_goals cases ned with
    | pair p q =>
      obtain ⟨a, b, hp⟩ := cd_need_cell p
      simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hp, hl, hL, levy_arm,
        levy.arm_at, ne_levy_nil, noneEquivalent, hsm, eqCode_atom, Tag.none, Tag.both, Tag.this]
    | none =>
      first
      | simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, hL, levy_arm,
          levy.arm_at, ne_levy_nil, noneEquivalent, hsm, eqCode_atom, Tag.none]; done
      | rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, noneEquivalent, hsm,
                    eqCode_atom, Tag.none, Ne.symm hr0]
                · simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, noneEquivalent, hsm,
                    eqCode_atom, eqCode, Tag.none]
              · simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, noneEquivalent, hsm,
                  eqCode_atom, Tag.none, Ne.symm hl0]
            · simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, noneEquivalent, hsm,
                eqCode_atom, eqCode, Tag.none]
          · simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, noneEquivalent, hsm,
              eqCode_atom, Tag.none, Ne.symm hk]
        · simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, noneEquivalent, hsm,
            eqCode_atom, eqCode, Tag.none]
    | _ =>
      simp [nock_exec, lazyNoun, Sure.toNoun, Need.toNoun, hl, hL, levy_arm,
        levy.arm_at, ne_levy_nil, noneEquivalent, hsm, eqCode_atom, Tag.none, Tag.both, Tag.this]

/-! ## The gate of the walk -/

/-- The arm `proxy` builds its gate. -/
theorem comp_px_arm (d : Noun) : nock d pxArm = some (C pxBat (C (C (A 0) (A 0)) d)) := by
  unfold pxArm; simp only [nock_exec]

/-- The gate that `+collapse-lazy-atom` walks the lazy need with is
`collapseGate`, where the block `oLaz` is not a key of `soft` and no
looked-at axis is `0`. -/
theorem cla_gate (hc : CompIn ctx) (hl : CompLib ctx) (x : GenRest) (r o oLaz : Nat)
    (sur : Sure CSet) (g : Gen (TreapMap mugF)) (G0 NED B NEX : Noun) (hs : x.SoftOut oLaz)
    (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C claG (C (C (A oLaz) (C sur.toNoun (genNoun g x)))
      (C (A o) (C (A r) (C NED (C B (C NEX (C comp.door (C G0 ctx))))))))) claG
      = (collapseGate r o oLaz sur g).map fun p => genNoun p.2 x := by
  have hsrl := comp_sure_require_look (x := x) hc hl g sur h0
  have hD := comp_srl_at
  have hD2 := comp_add_ops_at
  have hD3 := comp_px_at
  have hD4 := comp_crn_at
  simp only [compCore] at hsrl
  cases e : sureRequireLook sur g with
  | none =>
    rw [e] at hsrl
    nock_open claG
    generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl ⊢
    simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind]
  | some p =>
    obtain ⟨ned, g1⟩ := p
    rw [e] at hsrl
    -- the source register: `r` in block `o`, a proxy elsewhere
    have hpx := comp_proxy hc x g1 r oLaz
    simp only [compCore] at hpx
    cases ned with
    | none =>
      nock_open claG
      generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx ⊢
      simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind, Need.toNoun,
        Tag.none, pure, StateT.pure]
    | this r' =>
      by_cases hr : r = r'
      · subst hr
        nock_open claG
        generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx ⊢
        simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind, Need.toNoun,
          Tag.none, Tag.this, pure, StateT.pure]
      · by_cases ho : oLaz = o
        · subst ho
          have hao := comp_add_ops x hc g1 oLaz [Pole.mov r r']
          simp only [compCore, listNoun, Pole.toNoun, Tag.mov] at hao
          nock_open claG
          generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hao ⊢
          simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind, Need.toNoun,
            Tag.none, Tag.this, pure, StateT.pure, hr, hD2, comp_add_ops_arm, hao]
        · cases ep : proxy r oLaz g1 with
          | none =>
            rw [ep] at hpx
            nock_open claG
            generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx ⊢
            simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind,
              Need.toNoun, Tag.none, Tag.this, pure, StateT.pure, hr, ho, hD3, comp_px_arm, hpx, ep]
          | some q =>
            obtain ⟨src, g2⟩ := q
            rw [ep] at hpx
            have hao := comp_add_ops x hc g2 oLaz [Pole.mov src r']
            simp only [compCore, listNoun, Pole.toNoun, Tag.mov] at hao
            nock_open claG
            generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hao ⊢
            simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind,
              Need.toNoun, Tag.none, Tag.this, pure, StateT.pure, hr, ho, hD3, comp_px_arm, hpx, ep,
              hD2, comp_add_ops_arm, hao]
    | pair p q =>
      obtain ⟨a, b, hp⟩ := cd_need_cell p
      by_cases ho : oLaz = o
      · subst ho
        have hcr := comp_crash_need hc x g1 oLaz (Sum.inr r) (Need.pair p q) hs
        simp only [compCore, crnAtomNoun, Need.toNoun, hp] at hcr
        nock_open claG
        generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hcr ⊢
        simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind, Need.toNoun,
          Tag.none, Tag.this, Tag.both, pure, StateT.pure, hp, hD4, comp_crn_arm, hcr]
      · cases ep : proxy r oLaz g1 with
        | none =>
          rw [ep] at hpx
          nock_open claG
          generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx ⊢
          simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind,
            Need.toNoun, Tag.none, Tag.this, Tag.both, pure, StateT.pure, hp, ho, hD3, comp_px_arm,
            hpx, ep]
        | some q =>
          obtain ⟨src, g2⟩ := q
          rw [ep] at hpx
          have hcr := comp_crash_need hc x g2 oLaz (Sum.inr src) (Need.pair p q) hs
          simp only [compCore, crnAtomNoun, Need.toNoun, hp] at hcr
          nock_open claG
          generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hcr ⊢
          simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind,
            Need.toNoun, Tag.none, Tag.this, Tag.both, pure, StateT.pure, hp, ho, hD3, comp_px_arm,
            hpx, ep, hD4, comp_crn_arm, hcr]
    | both rb hh tt =>
      by_cases ho : oLaz = o
      · subst ho
        have hcr := comp_crash_need hc x g1 oLaz (Sum.inr r) (Need.both rb hh tt) hs
        simp only [compCore, crnAtomNoun, Need.toNoun, Tag.both] at hcr
        nock_open claG
        generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hcr ⊢
        simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind, Need.toNoun,
          Tag.none, Tag.this, Tag.both, pure, StateT.pure, hD4, comp_crn_arm, hcr]
      · cases ep : proxy r oLaz g1 with
        | none =>
          rw [ep] at hpx
          nock_open claG
          generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx ⊢
          simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind,
            Need.toNoun, Tag.none, Tag.this, Tag.both, pure, StateT.pure, ho, hD3, comp_px_arm,
            hpx, ep]
        | some q =>
          obtain ⟨src, g2⟩ := q
          rw [ep] at hpx
          have hcr := comp_crash_need hc x g2 oLaz (Sum.inr src) (Need.both rb hh tt) hs
          simp only [compCore, crnAtomNoun, Need.toNoun, Tag.both] at hcr
          nock_open claG
          generalize comp.door = Dr at hD hD2 hD3 hD4 hsrl hpx hcr ⊢
          simp [nock_exec, hD, comp_srl_arm, hsrl, e, collapseGate, bind, StateT.bind,
            Need.toNoun, Tag.none, Tag.this, Tag.both, pure, StateT.pure, ho, hD3, comp_px_arm,
            hpx, ep, hD4, comp_crn_arm, hcr]

/-! ## `+collapse-lazy-atom` -/

theorem cla_ne_mk (s : Sure CSet) : Lazy.noneEquivalentL (Lazy.mk s [] []) = noneEquivalent s :=
  Lazy.noneEquivalentL_ofSure s

theorem cla_emit_drop (b : Blob) (g : Gen (TreapMap mugF)) : (cfEmitG b g).drop = g.drop := by
  unfold cfEmitG; split <;> rfl

/-- **`+collapse-lazy-atom` on `[sure ~ ~]`** is `collapseLazyAtomL`, in the
pill's context (`K` at axis `7`), where no looked-at axis is `0` and the
block where the walk starts (`there` of the goal, or the new crash block
after `+sure-require-look`) is not a key of `soft`. -/
theorem comp_collapse_lazy_atom (h7 : slot? 7 ctx = some compK) (x : GenRest)
    (g : Gen (TreapMap mugF)) (sur : Sure CSet) (th : Jmp)
    (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) (hs : x.SoftOut th.there)
    (hs' : ∀ n g', sureRequireLook sur g = some (n, g') → x.SoftOut g'.bo) :
    nock (C claBat (C (C (A 0x7478656e) (C (lazyNoun sur) th.toNoun)) (compCore g x ctx))) claBat
      = (collapseLazyAtomL (⟨Lazy.ofSure sur, th⟩ : NextL CSet) g).map
          fun p => C (unitNoun (fun q => C (A q.1) (A q.2)) p.1) (genNoun p.2 x) := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have h15 : slot? 15 ctx = some compTypes := by
    have := slot_spine (by omega) (by omega) h1 1
    simp only [show 2 ^ 1 * (7 + 1) - 1 = 15 from rfl,
      show 2 ^ 1 * (1 + 1) - 1 = 3 from rfl] at this
    rw [this]; rfl
  have hD0 := compK_ne
  have hD1 := comp_drop_at
  have hD2 := comp_srl_at
  have hD3 := comp_re_at
  have hD4 := comp_emit_at
  have hD5 := comp_wl_at
  obtain ⟨args, there⟩ := th
  simp only at hs
  simp only [compCore]
  cases args with
  | cons a rest =>
    nock_open claBat
    generalize comp.door = Dr at hD1 hD2 hD3 hD4 hD5 ⊢
    simp [nock_exec, Jmp.toNoun, listNoun, collapseLazyAtomL]
  | nil =>
  have hn := ne_gate sur
  cases hne0 : noneEquivalent sur
  case true =>
    nock_open claBat
    generalize comp.door = Dr at hD1 hD2 hD3 hD4 hD5 ⊢
    simp [nock_exec, h7, hD0, ne_arm, hn, hne0, Jmp.toNoun, listNoun, collapseLazyAtomL,
      Lazy.noneEquivalentL_ofSure, cla_ne_mk, pure, StateT.pure, unitNoun]
  case false =>
  have hsrl := comp_sure_require_look (x := x) hc hl g sur h0
  simp only [compCore] at hsrl
  obtain ⟨ned0, lok⟩ := sur
  simp only at h0 hsrl hs' hn hne0
  simp only [lazyNoun, Sure.toNoun] at hn hsrl
  cases e : sureRequireLook ⟨ned0, lok⟩ g with
  | none =>
    rw [e] at hsrl
    nock_open claBat
    generalize comp.door = Dr at hD1 hD2 hD3 hD4 hD5 hsrl ⊢
    simp [nock_exec, h7, hD0, ne_arm, hn, hne0, hD2, comp_srl_arm, hsrl, e, Jmp.toNoun, listNoun,
      collapseLazyAtomL, Lazy.noneEquivalentL_ofSure, cla_ne_mk, Lazy.ofSure, bind, StateT.bind,
      lazyNoun, Sure.toNoun]
  | some p =>
    obtain ⟨ned, g1⟩ := p
    rw [e] at hsrl
    have hbo := hs' ned g1 e
    cases ned with
    | this r =>
      cases hdr : g1.drop
      · have hgate := cla_gate hc hl x r there there ⟨Need.this r, lok⟩ g1 (genNoun g1 x)
          (Need.this r).toNoun claBat (C (A 0x7478656e) (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A there)))) hs h0
        obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun g1 x)
        cases eg : collapseGate r there there ⟨Need.this r, lok⟩ g1 with
        | none =>
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun g1 x)))
            (C (A there) (C (A r) (C (Need.this r).toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A there)))) (C comp.door (C (genNoun g1 x) ctx)))))))
            (genNoun g1 x) there ⟨Need.this r, lok⟩ none h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            hD2]
        | some q =>
          obtain ⟨u, g3⟩ := q
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun g1 x)))
            (C (A there) (C (A r) (C (Need.this r).toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A there)))) (C comp.door (C (genNoun g1 x) ctx)))))))
            (genNoun g1 x) there ⟨Need.this r, lok⟩ (some (genNoun g3 x)) h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            hD2]
      · nock_open claBat
        generalize comp.door = Dr at hD2 hsrl hD1 hD5 ⊢
        simp [nock_exec, hD2, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hn, hne0, hsrl, e, dropArm, cgModeNoun, hdr,
          lazyNoun, Sure.toNoun, Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun,
          collapseLazyAtomL, Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure,
          bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
          hD2]
    | none =>
      have hre := comp_re' ctx x g1
      cases hdr : g1.drop
      · have hgate := cla_gate hc hl x g1.re there there ⟨Need.this g1.re, lok⟩ { g1 with re := g1.re + 1 } (genNoun { g1 with re := g1.re + 1 } x)
          Need.none.toNoun claBat (C (A 0x7478656e) (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A there)))) hs h0
        obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun { g1 with re := g1.re + 1 } x)
        cases eg : collapseGate g1.re there there ⟨Need.this g1.re, lok⟩ { g1 with re := g1.re + 1 } with
        | none =>
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun { g1 with re := g1.re + 1 } x)))
            (C (A there) (C (A g1.re) (C Need.none.toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A there)))) (C comp.door (C (genNoun { g1 with re := g1.re + 1 } x) ctx)))))))
            (genNoun { g1 with re := g1.re + 1 } x) there ⟨Need.this g1.re, lok⟩ none h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hD3 hre hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD3, hre, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            re]
        | some q =>
          obtain ⟨u, g3⟩ := q
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun { g1 with re := g1.re + 1 } x)))
            (C (A there) (C (A g1.re) (C Need.none.toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A there)))) (C comp.door (C (genNoun { g1 with re := g1.re + 1 } x) ctx)))))))
            (genNoun { g1 with re := g1.re + 1 } x) there ⟨Need.this g1.re, lok⟩ (some (genNoun g3 x)) h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hD3 hre hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD3, hre, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            re]
      · nock_open claBat
        generalize comp.door = Dr at hD2 hD3 hre hsrl hD1 hD5 ⊢
        simp [nock_exec, hD2, hD3, hre, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hn, hne0, hsrl, e, dropArm, cgModeNoun, hdr,
          lazyNoun, Sure.toNoun, Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun,
          collapseLazyAtomL, Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure,
          bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
          re]
    | pair p q =>
      obtain ⟨pa, pb, hp⟩ := cd_need_cell p
      have hre := comp_re' ctx x g1
      have he := cf_emit (x := x) hc { g1 with re := g1.re + 1 } ⟨[], [], Termin.bom none⟩
      simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.bom, unitNoun] at he
      cases hdr : g1.drop

      · have hgate := cla_gate hc hl x g1.re g1.bo g1.bo ⟨Need.this g1.re, lok⟩ (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x)
          (Need.pair p q).toNoun claBat (C (A 0x7478656e) (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A g1.bo)))) hbo h0
        obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x)
        cases eg : collapseGate g1.re g1.bo g1.bo ⟨Need.this g1.re, lok⟩ (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) with
        | none =>
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x)))
            (C (A g1.bo) (C (A g1.re) (C (Need.pair p q).toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A g1.bo)))) (C comp.door (C (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x) ctx)))))))
            (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x) g1.bo ⟨Need.this g1.re, lok⟩ none h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hD3 hD4 hre he hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD3, hD4, hre, he, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hp, comp_emit_arm, cf_emit_g, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            re, cf_emit_g, cf_emitG_bo]
        | some q =>
          obtain ⟨u, g3⟩ := q
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x)))
            (C (A g1.bo) (C (A g1.re) (C (Need.pair p q).toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A g1.bo)))) (C comp.door (C (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x) ctx)))))))
            (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ { g1 with re := g1.re + 1 }) x) g1.bo ⟨Need.this g1.re, lok⟩ (some (genNoun g3 x)) h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hD3 hD4 hre he hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD3, hD4, hre, he, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hp, comp_emit_arm, cf_emit_g, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            re, cf_emit_g, cf_emitG_bo]
      · try simp only [hdr] at he
        try simp only [hdr] at hre
        nock_open claBat
        generalize comp.door = Dr at hD2 hD3 hD4 hre he hsrl hD1 hD5 ⊢
        simp [nock_exec, hD2, hD3, hD4, hre, he, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, hp, comp_emit_arm, cf_emit_g, hn, hne0, hsrl, e, dropArm, cgModeNoun, hdr,
          lazyNoun, Sure.toNoun, Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun,
          collapseLazyAtomL, Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure,
          bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
          re, cf_emit_g, cf_emitG_bo]
    | both rb hh tt =>
      have he := cf_emit (x := x) hc g1 ⟨[], [], Termin.bom none⟩
      simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.bom, unitNoun] at he
      cases hdr : g1.drop
      · have hgate := cla_gate hc hl x rb g1.bo g1.bo ⟨Need.this rb, lok⟩ (cfEmitG ⟨[], [], Termin.bom none⟩ g1) (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x)
          (Need.both rb hh tt).toNoun claBat (C (A 0x7478656e) (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A g1.bo)))) hbo h0
        obtain ⟨bunt, hwa⟩ := comp_wl_arm hm comp.door (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x)
        cases eg : collapseGate rb g1.bo g1.bo ⟨Need.this rb, lok⟩ (cfEmitG ⟨[], [], Termin.bom none⟩ g1) with
        | none =>
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x)))
            (C (A g1.bo) (C (A rb) (C (Need.both rb hh tt).toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A g1.bo)))) (C comp.door (C (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x) ctx)))))))
            (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x) g1.bo ⟨Need.this rb, lok⟩ none h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hD4 he hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD4, he, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, comp_emit_arm, cf_emit_g, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            cf_emit_g]
        | some q =>
          obtain ⟨u, g3⟩ := q
          rw [eg] at hgate
          have hw := fun h => comp_walk_lazy (ctx := ctx) comp.door claG
            (C (A 0) (C ctSuBunt (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x)))
            (C (A g1.bo) (C (A rb) (C (Need.both rb hh tt).toNoun (C claBat (C (C (A 0x7478656e)
              (C (lazyNoun ⟨ned0, lok⟩) (C (A 0) (A g1.bo)))) (C comp.door (C (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x) ctx)))))))
            (genNoun (cfEmitG ⟨[], [], Termin.bom none⟩ g1) x) g1.bo ⟨Need.this rb, lok⟩ (some (genNoun g3 x)) h
          try simp only [Option.map_none, Option.map_some] at hgate
          have hw' := hw hgate
          try simp only [lazyNoun, Sure.toNoun, Need.toNoun, Tag.this, Tag.none, Tag.both] at hw'
          try simp only [hp] at hw'
          try simp only [hdr] at hw'
          try simp only [hdr] at hwa
          try simp only [hdr] at he
          try simp only [hdr] at hre
          try simp only [hdr] at eg
          nock_open claBat
          generalize comp.door = Dr at hD2 hD4 he hsrl hD1 hD5 hwa hw' ⊢
          simp [nock_exec, hD2, hD4, he, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, comp_emit_arm, cf_emit_g, hwa, hw', hn, hne0, hsrl, e, h15, ct_su_at,
            ct_su_gate, ct_su_bat, ct_su_bunt, dropArm, cgModeNoun, hdr, lazyNoun, Sure.toNoun,
            Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun, collapseLazyAtomL,
            Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure, Lazy.walkLazy, eg,
            bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
            cf_emit_g]
      · nock_open claBat
        generalize comp.door = Dr at hD2 hD4 he hsrl hD1 hD5 ⊢
        simp [nock_exec, hD2, hD4, he, hD1, hD5, h7, hD0, ne_arm, comp_srl_arm, comp_emit_arm, cf_emit_g, hn, hne0, hsrl, e, dropArm, cgModeNoun, hdr,
          lazyNoun, Sure.toNoun, Need.toNoun, Tag.none, Tag.this, Tag.both, Jmp.toNoun, listNoun,
          collapseLazyAtomL, Lazy.noneEquivalentL_ofSure, cla_ne_mk, cla_emit_drop, Lazy.ofSure,
          bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, unitNoun,
          cf_emit_g]

end Compiler
end Formalization
