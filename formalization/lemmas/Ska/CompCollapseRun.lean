import lemmas.Ska.CompCollapseGate

/-!
# The run of `+collapse-lazy-atom` when the sure need is one register

README Gaps 12.2, the collapse case.  When the goal's sure need is
`this d` with looks at axis `1` only (as in
`[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]`, where `d` is the `rp` of the
`%5` of `q`), `+collapse-lazy-atom` takes `r = d` and `there = th.there`,
puts nothing at `th.there` (`+sure-require-look` of `this d` is `this d`
again), and walks the goal's entries with `collapseGate d th.there`
(`collapseL_this`): every entry gets ops that do what `CollP d` says for the
`cond` the walk ends with, `cond` grew only by proxies for `d`, and every
block other than the entries is kept, `th.there` included.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A step that only allocates registers is a walk over no block. -/
theorem WalkOKD.of_re {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} {r : Nat}
    (g : Gen Map) (k : Nat) (hk : g.re ≤ k) : WalkOKD (ProxyFor r) P g { g with re := k } [] :=
  ⟨rfl, rfl, hk, ProxyFor.of_eq hk rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- The gate at the goal's own block, for the need `this d`: nothing. -/
theorem collapseGate_self {d o : Nat} {lok : S} {g g' : Gen Map}
    (hl : ∀ x ∈ HoonSet.toList lok, x = 1)
    (h : collapseGate (S := S) (Map := Map) d o o ⟨Need.this d, lok⟩ g = some ((), g')) :
    ∃ k, g.re ≤ k ∧ g' = { g with re := k } := by
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  have e : ned = Need.this d := L.same hl
  subst e
  obtain ⟨kk, rfl⟩ := L.gen
  simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  exact ⟨kk, L.le, rfl⟩

/-- **`+collapse-lazy-atom` when the sure need is `this d`**: it returns
`(d, th.there)`, keeps every block outside the goal's entries (`th.there`
included), and walks the entries with `CollP d` for the `cond` it ends
with, which grew only by proxies for `d`. -/
theorem collapseL_this {laz : Lazy S} {th : Jmp} {d : Nat} {g0 g2 : Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtomL ⟨laz, th⟩ g0 = some (a, g2))
    (hs : laz.sure.ned = Need.this d) (hl : ∀ x ∈ HoonSet.toList laz.sure.lok, x = 1)
    (d0 : g0.drop = false)
    (hn : (th.there :: (entries laz).map Prod.fst).Nodup) :
    th.args = [] ∧ a = some (d, th.there) ∧ WalkOKD (ProxyFor d) (CollP (S := S) (Map := Map) d) g0 g2 (entries laz) := by
  unfold collapseLazyAtomL at h
  dsimp only at h
  by_cases ea : th.args ≠ []
  · rw [if_pos ea] at h; cases h
  rw [if_neg ea] at h
  have ea' : th.args = [] := by simpa using ea
  rcases laz with ⟨s, fk, bd⟩
  simp only [sure_mk] at hs hl
  have hne : noneEquivalentL (mk s fk bd) = false := by
    simp [noneEquivalentL, hs]
  rw [if_neg (by simp [hne])] at h
  obtain ⟨nedS, g1, h1, h⟩ := bind_some h
  have L := sureRequireLook_spec h1
  have eS : nedS = Need.this d := (L.same hl).trans hs
  subst eS
  obtain ⟨k1, hk1⟩ := L.gen
  have d1 : g1.drop = false := by rw [hk1]; exact d0
  simp only [sure_mk, fork_mk, bond_mk, bind_apply, pure_apply, Option.bind_some, get_apply, d1,
    Bool.false_eq_true, if_false] at h
  obtain ⟨⟨u, gW⟩, hW, hP⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  refine ⟨ea', rfl, ?_⟩
  -- the walk: nothing at `th.there`, then the forks and the bonds
  unfold walkLazy at hW
  obtain ⟨u1, gA, hA, hr⟩ := bind_some hW
  obtain ⟨k2, hk2, hgA⟩ := collapseGate_self hl hA
  have W0 : WalkOKD (ProxyFor d) (CollP (S := S) (Map := Map) d) g0 gA [] := by
    have := WalkOKD.of_re (P := CollP (S := S) (Map := Map) d) (r := d) g0 k2 (Nat.le_trans L.le hk2)
    rw [hgA, hk1]; exact this
  have dA : gA.drop = false := by rw [hgA]; exact d1
  have ct : ∀ a b c : Gen Map, ProxyFor d a b → ProxyFor d b c → ProxyFor d a c := fun _ _ _ x y => ProxyFor.trans x y
  have cb : ∀ a b : Gen Map, ProxyFor d a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k :=
    fun _ _ x _ hk => ProxyFor.get_lt x hk
  have hn' := (List.nodup_cons.mp hn).2
  simp only [entries, List.map_append] at hn' ⊢
  split at hr
  · rename_i hfb
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
    obtain ⟨rfl, rfl⟩ := hfb
    have h' : some ((), _) = some ((), gW) := hr
    cases h'
    simpa [bondEntries, forkEntries] using W0
  · obtain ⟨u2, gB, h2, h3⟩ := bind_some hr
    have WF := walkForks_okD (ProxyFor.refl d) ct cb (collP_mono d) (collapseGate_ok d th.there) fk _ gB h2 dA
      (List.nodup_append.mp hn').2.1
    have WB := walkBonds_okD (ProxyFor.refl d) ct cb (collP_mono d) (collapseGate_ok d th.there) bd gB gW h3
      (WF.drop.trans dA) (List.nodup_append.mp hn').1
    have W := (W0.trans ct cb (collP_mono d) WF (fun x hx => absurd hx List.not_mem_nil)).trans ct cb
      (collP_mono d) WB (by
        intro x hx hm
        simp only [List.nil_append] at hx
        exact nodup_disj hn' x hm hx)
    exact W.congr fun e => by
      simp only [List.nil_append, List.mem_append]
      exact Or.comm
