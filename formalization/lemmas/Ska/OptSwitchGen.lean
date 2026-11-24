import lemmas.Ska.OptSwitchPlainHyp

/-!
# `+switch-chains`: the chains of one walk, of either kind, described alike

Toward the walk over tagged and plain chains.  A chain the walk replaced is
described by a `GC`: its head `o`, the labels of `topo` after the head that
its region takes (`R`), the places outside it that its tree jumps to (`X`:
the hits and the final miss), the labels from `n1` up to `n2` it took from
`nex` (none for a tagged chain), the registers its tree and head may mention
(`S`) and the registers of its tests (`E`).  `GOK` lists what the walk needs
of it, all about the blocks before: the labels `o :: R` follow jumps
(`JLinked`), each of `X` is the target of a jump from one of them, a block of
`topo` that jumps into `R` is one of them, each of `S` is mentioned in one of
them, no block outside them mentions `E`, and `n1` is at least `nexOf bl`.

* `tagGC_ok`, `plainGC_ok`: a tagged chain of `chainOf` and a plain chain of
  `plainsOf`, at a member of `topo`, give a `GOK` chain (from `labs_into`,
  `tag_ment_bl`, `plabs_into`, `plain_off`).
* **`gc_disj`**: of two such chains, the later one (later head in `topo`, not
  in the earlier `R`) has its labels and its `X` outside the earlier `R`, the
  earlier one jumps nowhere in the later `R`, mentions none of the later
  `E`, and its head is not a label of the later one.  The argument is that of
  `chain_disj`, once for both kinds: walking the later labels along their
  jumps, a step into the earlier `R` would come from a label of the earlier
  chain, which the ranks of `topo` exclude.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- A chain the walk replaced, of either kind. -/
structure GC where
  o : Nat
  R : List Nat
  X : List Nat
  n1 : Nat
  n2 : Nat
  S : List Nat
  E : List Nat

/-- The region of a chain done: `R` and the labels it took from `nex`. -/
def GC.In (g : GC) (k : Nat) : Prop := k ∈ g.R ∨ (g.n1 ≤ k ∧ k < g.n2)

/-- Where the tree and head of a chain done may jump. -/
def GC.J (g : GC) (k : Nat) : Prop := g.In k ∨ k ∈ g.X

/-- One jump of `bl` from `x` to `y`. -/
def JStep (bl : Map Blob) (x y : Nat) : Prop :=
  ∃ b j, HoonMap.get bl x = some b ∧ j ∈ getJmps b.fin ∧ j.there = y

/-- Consecutive labels are joined by jumps. -/
def JLinked (bl : Map Blob) : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => JStep bl x y ∧ JLinked bl (y :: rest)

/-- **What the walk needs of a chain done**, about the blocks before. -/
structure GOK (bl : Map Blob) (topo : List Nat) (g : GC) : Prop where
  ho : g.o ∈ topo
  link : JLinked bl (g.o :: g.R)
  xt : ∀ x ∈ g.X, ∃ y ∈ g.o :: g.R, JStep bl y x
  into : ∀ k b j, k ∈ topo → HoonMap.get bl k = some b → j ∈ getJmps b.fin → j.there ∈ g.R → k ∈ g.o :: g.R
  home : ∀ r ∈ g.S, ∃ y ∈ g.o :: g.R, ∃ b, HoonMap.get bl y = some b ∧ r ∈ blobMentions b
  excl : ∀ k b, k ∉ g.o :: g.R → HoonMap.get bl k = some b → ∀ r ∈ blobMentions b, r ∉ g.E
  fresh : nexOf bl ≤ g.n1

section
variable {bl : Map Blob} {topo : List Nat}

theorem linked_all {P : Nat → Prop} (hP : ∀ x y, P x → JStep bl x y → P y) :
    ∀ (x : Nat) (L : List Nat), JLinked bl (x :: L) → P x → ∀ y ∈ x :: L, P y
  | x, [], _, hx, y, hy => by rw [List.mem_singleton.mp hy]; exact hx
  | x, z :: L, ⟨hs, hl⟩, hx, y, hy => by
    rcases List.mem_cons.mp hy with e | hy
    · rw [e]; exact hx
    · exact linked_all hP z L hl (hP x z hx hs) y hy

theorem gok_topo (ht : TopoOK bl topo) {g : GC} (H : GOK bl topo g) :
    (∀ x ∈ g.o :: g.R, x ∈ topo) ∧ ∀ x ∈ g.X, x ∈ topo := by
  have step : ∀ x y, x ∈ topo → JStep bl x y → y ∈ topo := by
    intro x y hx hs
    obtain ⟨b, j, hb, hj, rfl⟩ := hs
    exact (topo_jump ht hx hb hj).1
  have h1 := linked_all step g.o g.R H.link H.ho
  refine ⟨h1, fun x hx => ?_⟩
  obtain ⟨y, hy, hs⟩ := H.xt x hx
  exact step y x (h1 y hy) hs

/-- **Two chains of one walk, of either kind**: `X` the earlier, `Y` the
later. -/
theorem gc_disj (ht : TopoOK bl topo) {X Y : GC} (HX : GOK bl topo X) (HY : GOK bl topo Y)
    (hrk : rk topo X.o < rk topo Y.o) (hn : Y.o ∉ X.R) :
    (∀ x, (x ∈ Y.o :: Y.R ∨ x ∈ Y.X) → x ∈ topo ∧ x ∉ X.R ∧ rk topo X.o < rk topo x) ∧
    (∀ x, X.J x → x ∉ Y.R) ∧ (∀ r ∈ X.S, r ∉ Y.E) ∧ X.o ∉ Y.o :: Y.R := by
  have step : ∀ x y, (x ∈ topo ∧ x ∉ X.R ∧ rk topo X.o < rk topo x) → JStep bl x y →
      (y ∈ topo ∧ y ∉ X.R ∧ rk topo X.o < rk topo y) := by
    intro x y hx hs
    obtain ⟨hx, hxn, hxr⟩ := hx
    obtain ⟨b, j, hb, hj, rfl⟩ := hs
    obtain ⟨hy, hr⟩ := topo_jump ht hx hb hj
    refine ⟨hy, fun hin => ?_, by omega⟩
    rcases List.mem_cons.mp (HX.into x b j hx hb hj hin) with e | e
    · rw [e] at hxr; omega
    · exact hxn e
  have h1 : ∀ x ∈ Y.o :: Y.R, x ∈ topo ∧ x ∉ X.R ∧ rk topo X.o < rk topo x :=
    linked_all step Y.o Y.R HY.link ⟨HY.ho, hn, hrk⟩
  have hA : ∀ x, (x ∈ Y.o :: Y.R ∨ x ∈ Y.X) → x ∈ topo ∧ x ∉ X.R ∧ rk topo X.o < rk topo x := by
    intro x hx
    rcases hx with hx | hx
    · exact h1 x hx
    · obtain ⟨y, hy, hs⟩ := HY.xt x hx
      exact step y x (h1 y hy) hs
  have hXo : X.o ∉ Y.o :: Y.R := fun h => by have := (h1 _ h).2.2; omega
  have hXR : ∀ y ∈ X.o :: X.R, y ∉ Y.o :: Y.R := by
    intro y hy hyY
    obtain ⟨-, hn2, hr2⟩ := h1 y hyY
    rcases List.mem_cons.mp hy with e | e
    · rw [e] at hr2; omega
    · exact hn2 e
  have hXT := (gok_topo ht HX).1
  refine ⟨hA, fun x hx hxY => ?_, fun r hr hrE => ?_, hXo⟩
  · have hxT : x ∈ topo := (h1 x (List.mem_cons_of_mem _ hxY)).1
    rcases hx with (hx | hx) | hx
    · exact hXR x (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hxY)
    · have := nexOf_gt bl (ht.2.2.1 x hxT); have := HX.fresh; omega
    · obtain ⟨y, hy, b, j, hb, hj, rfl⟩ := HX.xt x hx
      exact hXR y hy (HY.into y b j (hXT y hy) hb hj hxY)
  · obtain ⟨y, hy, b, hb, hm⟩ := HX.home r hr
    exact HY.excl y b (hXR y hy) hb r hm hrE

end

/-! ## A tagged chain as a `GC` -/

/-- A tagged chain done, as a `GC`. -/
def tagGC (bl : Map Blob) (o : Nat) (t0 : STest) (tl : List STest) : GC :=
  ⟨o, (ilabs o (t0 :: tl)).tail, (t0 :: tl).map STest.hit ++ [tagMiss t0 tl], nexOf bl, nexOf bl,
    t0.s :: tagRegs (t0 :: tl), tagRegs (t0 :: tl)⟩

section
variable {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

theorem tag_linked : ∀ (p : Nat) (cs : List STest), ChainR bl rev p cs → JLinked bl (ilabs p cs)
  | _, [], _ => trivial
  | p, t :: rest, ⟨hto, _, hr⟩ => by
    obtain ⟨b, yb, l, r, hb, hfin, -, hyb, -, hyf, -⟩ := testOf_spec hto
    refine ⟨⟨b, ⟨[], t.y⟩, hb, by rw [hfin]; simp [getJmps], rfl⟩, ?_⟩
    have ih := tag_linked t.miss rest hr
    cases rest with
    | nil => trivial
    | cons t2 r2 => exact ⟨⟨yb, ⟨[], t.miss⟩, hyb, by rw [hyf]; simp [getJmps], rfl⟩, ih⟩

theorem tag_yes_step {p : Nat} {cs : List STest} (hc : ChainR bl rev p cs) {t : STest} (ht : t ∈ cs) :
    JStep bl t.y t.hit ∧ JStep bl t.y t.miss := by
  obtain ⟨q, hq⟩ := chainR_test hc t ht
  obtain ⟨_, yb, _, _, -, -, -, hyb, -, hyf, -⟩ := testOf_spec hq
  exact ⟨⟨yb, ⟨[], t.hit⟩, hyb, by rw [hyf]; simp [getJmps], rfl⟩,
    ⟨yb, ⟨[], t.miss⟩, hyb, by rw [hyf]; simp [getJmps], rfl⟩⟩

/-- **A tagged chain of `chainOf` at a member of `topo` is a `GOK` chain.** -/
theorem tagGC_ok (_ht : TopoOK bl topo) {n o : Nat} {t0 : STest} {tl : List STest} (ho : o ∈ topo)
    (h : chainOf bl (revCfg bl topo) n o = some (t0 :: tl)) : GOK bl topo (tagGC bl o t0 tl) := by
  have hc := chainOf_rev n o _ h
  refine ⟨ho, tag_linked o _ hc, fun x hx => ?_, fun k b j hk hb hj hth => labs_into rfl o _ hc k b j hk hb hj hth,
    fun r hr => ?_, fun k b hk hb r hr => ?_, Nat.le_refl _⟩
  · simp only [tagGC, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨t, ht', rfl⟩ | rfl
    · exact ⟨t.y, List.mem_cons_of_mem _ (y_mem_tail o _ t ht'), (tag_yes_step hc ht').1⟩
    · exact ⟨_, List.mem_cons_of_mem _ (y_mem_tail o _ _ (List.getLast_mem (List.cons_ne_nil t0 tl))),
        (tag_yes_step hc (List.getLast_mem (List.cons_ne_nil t0 tl))).2⟩
  · simp only [tagGC, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨b, -, -, -, hb, hf, -⟩ := testOf_spec hc.1
      exact ⟨o, List.mem_cons_self, b, hb, mentions_fin b _ (by rw [hf]; simp [finRegs])⟩
    · rw [tagRegs, List.mem_flatMap] at hr
      obtain ⟨t, ht', hrt⟩ := hr
      obtain ⟨q, hq⟩ := chainR_test hc t ht'
      obtain ⟨yb, hyb, cd, cr⟩ := test_count hq
      refine ⟨t.y, List.mem_cons_of_mem _ (y_mem_tail o _ t ht'), yb, hyb, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrt
      rcases hrt with rfl | rfl
      · exact List.count_pos_iff.mp (by omega)
      · exact List.count_pos_iff.mp (by omega)
  · exact tag_ment_bl hc k b (fun hI => hk (List.mem_cons_of_mem _ ((tagIn_iff o t0 tl k).mp hI))) hb r hr

end

/-! ## A plain chain as a `GC` -/

/-- A plain chain done, with the labels from `nex` up to `nex'`, as a `GC`. -/
def plainGC (o nex nex' : Nat) (p0 : Nat × SPlain) (pl : List (Nat × SPlain)) : GC :=
  ⟨o, pl.map Prod.fst, (p0 :: pl).map (fun t => t.2.hit) ++ [plainMiss p0 pl], nex, nex',
    p0.2.d :: plainRegs (p0 :: pl), plainRegs (p0 :: pl)⟩

section
variable {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

theorem plain_linked : ∀ (p : Nat) (ps : List (Nat × SPlain)), PlainR bl rev p ps → JLinked bl (ps.map Prod.fst)
  | _, [], _ => trivial
  | p, t :: rest, ⟨h1, hq, _, _, hr⟩ => by
    have ih := plain_linked t.2.miss rest hr
    cases rest with
    | nil => trivial
    | cons t2 r2 =>
      obtain ⟨b, l, r, hb, hfin, -⟩ := plainOf_spec hq
      exact ⟨⟨b, ⟨[], t.2.miss⟩, by rw [h1]; exact hb, by rw [hfin]; simp [getJmps], hr.1.symm⟩, ih⟩

theorem plain_steps {p : Nat} {ps : List (Nat × SPlain)} (hc : PlainR bl rev p ps) {t : Nat × SPlain}
    (ht : t ∈ ps) : JStep bl t.1 t.2.hit ∧ JStep bl t.1 t.2.miss := by
  obtain ⟨b, l, r, hb, hfin, -⟩ := plainOf_spec (plainR_mem hc t ht)
  exact ⟨⟨b, ⟨[], t.2.hit⟩, hb, by rw [hfin]; simp [getJmps], rfl⟩,
    ⟨b, ⟨[], t.2.miss⟩, hb, by rw [hfin]; simp [getJmps], rfl⟩⟩

/-- **A plain chain of `plainsOf` at a member of `topo` is a `GOK` chain**,
with any labels from `nex` up, `nex` at least `nexOf bl`. -/
theorem plainGC_ok (_ht : TopoOK bl topo) {n o nex nex' : Nat} {p0 : Nat × SPlain} {pl : List (Nat × SPlain)}
    (ho : o ∈ topo) (h : plainsOf bl (revCfg bl topo) n o = some (p0 :: pl)) (hnex : nexOf bl ≤ nex) :
    GOK bl topo (plainGC o nex nex' p0 pl) := by
  have hc := plainsOf_rev n o _ h
  have hmap : (p0 :: pl).map Prod.fst = o :: pl.map Prod.fst := by rw [List.map_cons, hc.1]
  have hlab : ∀ t ∈ p0 :: pl, t.1 ∈ o :: pl.map Prod.fst := fun t ht' => by
    rw [← hmap]; exact List.mem_map_of_mem ht'
  refine ⟨ho, ?_, fun x hx => ?_, fun k b j hk hb hj hth => ?_, fun r hr => ?_, fun k b hk hb r hr hrE => ?_, hnex⟩
  · have := plain_linked o _ hc
    rw [hmap] at this
    exact this
  · simp only [plainGC, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨t, ht', rfl⟩ | rfl
    · exact ⟨t.1, hlab t ht', (plain_steps hc ht').1⟩
    · have hl := List.getLast_mem (List.cons_ne_nil p0 pl)
      exact ⟨_, hlab _ hl, (plain_steps hc hl).2⟩
  · have := plabs_into rfl o (p0 :: pl) hc k b j hk hb hj hth
    rw [hmap] at this
    exact this
  · simp only [plainGC, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨b, l, r, hb, hfin, hlr, -⟩ := plainOf_spec hc.2.1
      refine ⟨o, List.mem_cons_self, b, hb, mentions_fin b _ ?_⟩
      rw [hfin]
      rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [finRegs]
    · unfold plainRegs at hr
      obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hr
      obtain ⟨b, -, -, hb, -, -, -, -, -, hc2⟩ := plain_head_count (plainR_mem hc t ht')
      exact ⟨t.1, hlab t ht', b, hb, List.count_pos_iff.mp (by omega)⟩
  · simp only [plainGC] at hrE
    unfold plainRegs at hrE
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hrE
    have h0 := plain_off (plainR_mem hc t ht') (fun e => hk (by rw [e]; exact hlab t ht')) hb
    have := List.count_pos_iff.mpr hr
    omega

end

end Opt
end SkaModel
end Formalization
