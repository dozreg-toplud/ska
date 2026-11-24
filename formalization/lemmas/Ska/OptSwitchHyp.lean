import lemmas.Ska.OptSwitchShape

/-!
# `+switch-chains`: `TagHyp` from `chain-of`, `+rev-cfg` and `TopoOK`

**`tagHyp_of`**: a chain that `chainOf` returns at a member `o` of `topo`,
with `rev = revCfg bl topo` and `TopoOK bl topo`, meets every field of
`TagHyp`.  No other fact on the blocks is needed (not `Acyclic`: the places
in `topo` serve as the rank).

* The labels of the chain in order, `o`, `y0`, `p1`, `y1`, …, `pk`, `yk` and
  the final miss (`ilabs`, `lastMiss`), are members of `topo` at strictly
  rising places (`labs_sorted`), since each is the target of a jump of the
  one before and `TopoOK` sends a jump of a member to a later member.  So
  they are distinct, which gives `nd`, `hy`, `ho`, `hoy` and the last two
  parts of `miss` (`tagIds` is a permutation of the labels after `y0`,
  `ilabs_perm`); `0` is first in `topo`, so it is none of them (`zero`).
* A block of `topo` that jumps to a label inside the region is a label of the
  chain (`labs_into`), since `chain-of` checked the predecessors of the yes
  sides (`[p]`) and of the no sides it went through (`[p, y]` in either
  order).  That gives `noI`.
* A hit is outside the region (`labs_hits`): a hit is later than its yes
  side, so it could only be a later label, and the predecessors of those are
  known; the one case where they allow it, a hit equal to its own no side,
  is excluded by the multiplicity of `+rev-cfg` (`revCfg_count`: the list of
  a block has an entry per jump, so the yes side would be listed twice where
  `chain-of` saw it once).
* `hr` and `ment` from `uses = 2` (`uses_ge2`: the mentions of a register in
  two blocks add up to at most its `uses`; for example `r = d0` of a later
  test would be mentioned twice in each of two yes sides).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## The place in `topo` as a rank -/

/-- The place of a label in `topo`. -/
def rk (topo : List Nat) (x : Nat) : Nat := topo.idxOf x

theorem topo_jump {bl : Map Blob} {topo : List Nat} (ht : TopoOK bl topo) {x : Nat} {b : Blob} {j : Jmp}
    (hx : x ∈ topo) (hb : HoonMap.get bl x = some b) (hj : j ∈ getJmps b.fin) :
    j.there ∈ topo ∧ rk topo x < rk topo j.there := by
  obtain ⟨hnd, -, -, -, hf⟩ := ht
  have hl : topo.idxOf x < topo.length := List.idxOf_lt_length_of_mem hx
  have hx' : topo[topo.idxOf x]? = some x := by
    rw [List.getElem?_eq_getElem hl, List.getElem_idxOf hl]
  obtain ⟨k, hk, hk'⟩ := hf _ x b j hx' hb hj
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk'
  refine ⟨List.mem_of_getElem? hk', ?_⟩
  unfold rk
  rw [← hkv, hnd.idxOf_getElem k hkl]
  exact hk

theorem rk_zero {bl : Map Blob} {topo : List Nat} (ht : TopoOK bl topo) : rk topo 0 = 0 := by
  obtain ⟨-, h0, -⟩ := ht
  cases topo with
  | nil => simp at h0
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp [rk]

/-! ## The chain with its `rev` checks -/

/-- The chain from `p`, with what `chain-of` checks of `rev` at each no side
it goes through. -/
def ChainR (bl : Map Blob) (rev : Map (List Nat)) : Nat → List STest → Prop
  | _, [] => True
  | p, t :: rest => testOf bl rev p = some (some t) ∧
      (rest ≠ [] → getJa rev t.miss = [p, t.y] ∨ getJa rev t.miss = [t.y, p]) ∧ ChainR bl rev t.miss rest

theorem chainOf_stepR {bl : Map Blob} {rev : Map (List Nat)} {n p : Nat} {t : STest} {rest : List STest}
    (h : ((HoonMap.get bl t.miss).bind fun nb =>
        if ¬ (nb.par = [] ∧ nb.body = []) then some [] else
        let rm := getJa rev t.miss
        if ¬ (rm = [p, t.y] ∨ rm = [t.y, p]) then some [] else
        (testOf bl rev t.miss).bind fun t2 =>
        match t2 with
        | none => some []
        | some t2 => if t2.s ≠ t.s then some [] else chainOf bl rev n t.miss) = some rest) :
    rest = [] ∨ ((getJa rev t.miss = [p, t.y] ∨ getJa rev t.miss = [t.y, p]) ∧
      chainOf bl rev n t.miss = some rest) := by
  obtain ⟨nb, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · simp at h; first | exact Or.inl h | exact Or.inl h.symm
  dsimp only at h
  split at h
  · simp at h; first | exact Or.inl h | exact Or.inl h.symm
  rename_i hrm
  simp only [Decidable.not_not] at hrm
  obtain ⟨t2o, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases t2o with
  | none => simp at h; first | exact Or.inl h | exact Or.inl h.symm
  | some t2 =>
    simp only at h
    split at h
    · simp at h; first | exact Or.inl h | exact Or.inl h.symm
    · exact Or.inr ⟨hrm, h⟩

theorem chainOf_rev {bl : Map Blob} {rev : Map (List Nat)} : ∀ (n p : Nat) (cs : List STest),
    chainOf bl rev n p = some cs → ChainR bl rev p cs
  | 0, _, _, h => by simp [chainOf] at h
  | n + 1, p, cs, h => by
    unfold chainOf at h
    obtain ⟨to, hto, h⟩ := Option.bind_eq_some_iff.mp h
    cases to with
    | none => simp at h; subst h; trivial
    | some t =>
    simp only at h
    obtain ⟨rest, hin, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases chainOf_stepR hin with rfl | ⟨hrm, hch⟩
    · exact ⟨hto, fun h => absurd rfl h, trivial⟩
    · exact ⟨hto, fun _ => hrm, chainOf_rev n t.miss rest hch⟩

theorem chainR_test {bl : Map Blob} {rev : Map (List Nat)} : ∀ {p : Nat} {cs : List STest}, ChainR bl rev p cs →
    ∀ t ∈ cs, ∃ q, testOf bl rev q = some (some t)
  | _, [], _, _, h => absurd h List.not_mem_nil
  | p, t :: _, ⟨hto, _, hr⟩, t', h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨p, hto⟩
    · exact chainR_test hr t' h

/-! ## The labels of a chain -/

/-- The labels of a chain from `p`: `p`, the yes side, then those of the
chain from the no side; without the final miss. -/
def ilabs : Nat → List STest → List Nat
  | _, [] => []
  | p, t :: rest => p :: t.y :: ilabs t.miss rest

/-- The final miss of a chain from `p`. -/
def lastMiss : Nat → List STest → Nat
  | p, [] => p
  | _, t :: rest => lastMiss t.miss rest

theorem lastMiss_tag : ∀ (t0 : STest) (tl : List STest), lastMiss t0.miss tl = tagMiss t0 tl
  | t0, [] => by simp [lastMiss, tagMiss]
  | t0, t1 :: tl => by
    rw [show lastMiss t0.miss (t1 :: tl) = lastMiss t1.miss tl from rfl, lastMiss_tag t1 tl]
    simp [tagMiss, List.getLast_cons]

theorem ilabs_perm : ∀ (t0 : STest) (tl : List STest), (ilabs t0.miss tl).Perm (tagIds (t0 :: tl))
  | t0, [] => by simp [ilabs, tagIds]
  | t0, t1 :: tl => by
    have ih := ilabs_perm t1 tl
    have e1 : tagIds (t0 :: t1 :: tl) =
        t1.y :: (tl.map STest.y ++ t0.miss :: (t1 :: tl).dropLast.map STest.miss) := by
      simp [tagIds, List.dropLast_cons_cons]
    have e2 : tagIds (t1 :: tl) = tl.map STest.y ++ (t1 :: tl).dropLast.map STest.miss := by
      simp [tagIds]
    rw [e1]
    rw [e2] at ih
    show (t0.miss :: t1.y :: ilabs t1.miss tl).Perm _
    exact (List.Perm.swap t1.y t0.miss _).trans ((((ih.cons t0.miss).trans List.perm_middle.symm)).cons t1.y)

theorem y_mem_tail : ∀ (p : Nat) (cs : List STest) (t : STest), t ∈ cs → t.y ∈ (ilabs p cs).tail
  | _, [], _, h => absurd h List.not_mem_nil
  | p, t0 :: rest, t, h => by
    show t.y ∈ t0.y :: ilabs t0.miss rest
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_of_mem_tail (y_mem_tail t0.miss rest t h))

section
variable {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

theorem labs_head (p : Nat) (cs : List STest) :
    ∃ L, ilabs p cs ++ [lastMiss p cs] = p :: L := by
  cases cs with
  | nil => exact ⟨[], rfl⟩
  | cons t rest => exact ⟨_, rfl⟩

/-- **The labels of a chain rise in `topo`.** -/
theorem labs_sorted (ht : TopoOK bl topo) : ∀ (p : Nat) (cs : List STest), ChainR bl rev p cs → p ∈ topo →
    (ilabs p cs ++ [lastMiss p cs]).Pairwise (fun a b => rk topo a < rk topo b) ∧
      ∀ x ∈ ilabs p cs ++ [lastMiss p cs], x ∈ topo
  | p, [], _, hp => ⟨List.pairwise_singleton _ _, by simp [ilabs, lastMiss, hp]⟩
  | p, t :: rest, ⟨hto, _, hr⟩, hp => by
    obtain ⟨b, yb, l, r, hb, hfin, -, hyb, -, hyf, -⟩ := testOf_spec hto
    obtain ⟨hy, h1⟩ := topo_jump ht hp hb (j := ⟨[], t.y⟩) (by rw [hfin]; simp [getJmps])
    obtain ⟨hm, h2⟩ := topo_jump ht hy hyb (j := ⟨[], t.miss⟩) (by rw [hyf]; simp [getJmps])
    simp only at hy h1 hm h2
    obtain ⟨hs, hin⟩ := labs_sorted ht t.miss rest hr hm
    have hge : ∀ x ∈ ilabs t.miss rest ++ [lastMiss t.miss rest], rk topo t.miss ≤ rk topo x := by
      obtain ⟨L, hL⟩ := labs_head t.miss rest
      rw [hL] at hs ⊢
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_refl _
      · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 x hx)
    refine ⟨?_, ?_⟩
    · show (p :: t.y :: (ilabs t.miss rest ++ [lastMiss t.miss rest])).Pairwise _
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hs)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1
        · have := hge x hx; omega
      · intro x hx; have := hge x hx; omega
    · intro x hx
      change x ∈ p :: t.y :: (ilabs t.miss rest ++ [lastMiss t.miss rest]) at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact hin x hx

theorem labs_gt (ht : TopoOK bl topo) {p : Nat} {cs : List STest} (hc : ChainR bl rev p cs) (hp : p ∈ topo) :
    (∀ x ∈ (ilabs p cs).tail, rk topo p < rk topo x) ∧ (cs ≠ [] → rk topo p < rk topo (lastMiss p cs)) := by
  cases cs with
  | nil => exact ⟨fun x hx => by simp [ilabs] at hx, fun h => absurd rfl h⟩
  | cons t rest =>
    have hs := (labs_sorted ht p (t :: rest) hc hp).1
    have e : ilabs p (t :: rest) ++ [lastMiss p (t :: rest)] =
        p :: ((t.y :: ilabs t.miss rest) ++ [lastMiss t.miss rest]) := rfl
    rw [e, List.pairwise_cons] at hs
    exact ⟨fun x hx => hs.1 x (List.mem_append_left _ hx),
      fun _ => hs.1 _ (List.mem_append_right _ (List.mem_singleton_self _))⟩

/-- **A block of `topo` that jumps inside the region is a label of the
chain.** -/
theorem labs_into (hrev : rev = revCfg bl topo) :
    ∀ (p : Nat) (cs : List STest), ChainR bl rev p cs → ∀ (k : Nat) (b : Blob) (j : Jmp), k ∈ topo →
      HoonMap.get bl k = some b → j ∈ getJmps b.fin → j.there ∈ (ilabs p cs).tail → k ∈ ilabs p cs
  | _, [], _, _, _, _, _, _, _, h => by simp [ilabs] at h
  | p, t :: rest, ⟨hto, hrm, hr⟩, k, b, j, hk, hb, hj, hth => by
    obtain ⟨-, -, -, -, -, -, hrevy, -⟩ := testOf_spec hto
    have hmem := revCfg_mem hk hb hj
    rw [← hrev] at hmem
    change j.there ∈ t.y :: ilabs t.miss rest at hth
    show k ∈ p :: t.y :: ilabs t.miss rest
    rcases List.mem_cons.mp hth with e | hth
    · rw [e, hrevy] at hmem
      simp only [List.mem_singleton] at hmem
      rw [hmem]; exact List.mem_cons_self
    · cases rest with
      | nil => simp [ilabs] at hth
      | cons t2 rest2 =>
        change j.there ∈ t.miss :: (ilabs t.miss (t2 :: rest2)).tail at hth
        rcases List.mem_cons.mp hth with e | hth
        · rw [e] at hmem
          rcases hrm (List.cons_ne_nil _ _) with h2 | h2 <;> rw [h2] at hmem <;>
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem <;>
            rcases hmem with rfl | rfl <;> simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (labs_into hrev t.miss (t2 :: rest2) hr k b j hk hb hj hth))

end

/-! ## The multiplicity of `+rev-cfg` -/

section
variable {bl : Map Blob} {topo : List Nat}

theorem addJa_count_mono {acc : Map (List Nat)} {k k' o x : Nat} :
    (getJa acc k).count x ≤ (getJa (addJa acc k' o) k).count x := by
  unfold addJa getJa
  simp only [HoonMap.get_put]
  split
  · rename_i e; subst e; simp only [Option.getD_some, List.count_cons]; omega
  · exact Nat.le_refl _

theorem inner_count_mono (o x k : Nat) : ∀ (js : List Jmp) (acc : Map (List Nat)),
    (getJa acc k).count x ≤ (getJa (js.foldl (fun acc j => addJa acc j.there o) acc) k).count x
  | [], _ => Nat.le_refl _
  | _ :: js, _ => Nat.le_trans addJa_count_mono (inner_count_mono o x k js _)

theorem inner_count_adds (o k : Nat) : ∀ (js : List Jmp) (acc : Map (List Nat)),
    (getJa acc k).count o + js.countP (fun j => decide (j.there = k)) ≤
      (getJa (js.foldl (fun acc j => addJa acc j.there o) acc) k).count o
  | [], _ => by simp
  | j :: js, acc => by
    simp only [List.foldl_cons, List.countP_cons]
    have ih := inner_count_adds o k js (addJa acc j.there o)
    have h1 : (getJa acc k).count o + (if decide (j.there = k) = true then 1 else 0) ≤
        (getJa (addJa acc j.there o) k).count o := by
      unfold addJa getJa
      simp only [HoonMap.get_put]
      by_cases e : k = j.there
      · subst e; simp [List.count_cons]
      · have e' : ¬ j.there = k := fun h => e h.symm
        simp [e, e']
    omega

theorem revStep_count_mono {acc : Map (List Nat)} {o x k : Nat} :
    (getJa acc k).count x ≤ (getJa (revStep bl topo acc o) k).count x := by
  unfold revStep
  split
  · split
    · exact inner_count_mono _ _ _ _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem revFold_count_mono {x k : Nat} : ∀ (ks : List Nat) (acc : Map (List Nat)),
    (getJa acc k).count x ≤ (getJa (ks.foldl (revStep bl topo) acc) k).count x
  | [], _ => Nat.le_refl _
  | _ :: ks, _ => Nat.le_trans revStep_count_mono (revFold_count_mono ks _)

theorem revFold_count_adds {o k : Nat} {b : Blob} (hmem : o ∈ topo) (hb : HoonMap.get bl o = some b) :
    ∀ (ks : List Nat) (acc : Map (List Nat)), o ∈ ks →
      (getJmps b.fin).countP (fun j => decide (j.there = k)) ≤ (getJa (ks.foldl (revStep bl topo) acc) k).count o
  | [], _, h => absurd h List.not_mem_nil
  | k' :: ks, acc, h => by
    simp only [List.foldl_cons]
    by_cases e : k' = o
    · subst e
      refine Nat.le_trans ?_ (revFold_count_mono ks _)
      unfold revStep
      rw [hb]; simp only [if_pos hmem]
      have := inner_count_adds k' k (getJmps b.fin) acc
      omega
    · exact revFold_count_adds hmem hb ks _ (by rcases List.mem_cons.mp h with h | h; exact absurd h.symm e; exact h)

/-- **The list of a block in `+rev-cfg` has an entry per jump**: a member of
`topo` is listed at `k` at least as many times as its end jumps to `k`. -/
theorem revCfg_count {o k : Nat} {b : Blob} (hmem : o ∈ topo) (hb : HoonMap.get bl o = some b) :
    (getJmps b.fin).countP (fun j => decide (j.there = k)) ≤ (getJa (revCfg bl topo) k).count o :=
  revFold_count_adds hmem hb _ _ ((MapKeys.mem_keys bl o).mpr (by simp [hb]))

end

/-! ## `uses` over two blocks -/

theorem sum_two {g : Nat → Nat} : ∀ {l : List Nat} {a b : Nat}, l.Nodup → a ∈ l → b ∈ l → a ≠ b →
    g a + g b ≤ (l.map g).sum
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: t, a, b, hn, ha, hb, hab => by
    rw [List.nodup_cons] at hn
    have e : ((x :: t).map g).sum = g x + (t.map g).sum := by simp
    rw [e]
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hab
    · rw [ha']; have := le_sum_of_mem' (List.mem_map_of_mem (f := g) hb'); omega
    · rw [hb']; have := le_sum_of_mem' (List.mem_map_of_mem (f := g) ha'); omega
    · have := sum_two (g := g) hn.2 ha' hb' hab; omega

/-- The mentions of a register in two blocks add up to at most its `uses`. -/
theorem uses_ge2 {bl : Map Blob} {y y' : Nat} {yb yb' : Blob} (hne : y ≠ y') (hy : HoonMap.get bl y = some yb)
    (hy' : HoonMap.get bl y' = some yb') (r : Nat) :
    (blobMentions yb).count r + (blobMentions yb').count r ≤ usesOf bl r := by
  unfold usesOf
  rw [List.count_flatMap]
  have h1 := sum_two (g := fun o => List.count r (((HoonMap.get bl o).map blobMentions).getD []))
    (MapKeys.nodup bl) ((MapKeys.mem_keys bl y).mpr (by simp [hy])) ((MapKeys.mem_keys bl y').mpr (by simp [hy'])) hne
  simp only [hy, hy', Option.map_some, Option.getD_some] at h1
  exact h1

/-- The yes side of a test mentions its `d` and its `r` twice each. -/
theorem test_count {bl : Map Blob} {rev : Map (List Nat)} {p : Nat} {t : STest}
    (h : testOf bl rev p = some (some t)) :
    ∃ yb, HoonMap.get bl t.y = some yb ∧ 2 ≤ (blobMentions yb).count t.d ∧ 2 ≤ (blobMentions yb).count t.r := by
  obtain ⟨b, yb, l, r, -, -, -, hyb, hpar, hfin, hlr, hbody, -, -⟩ := testOf_spec h
  obtain ⟨hdr, hsd, hsr⟩ := test_regs h
  refine ⟨yb, hyb, ?_⟩
  have e : yb = ⟨yb.par, yb.body, yb.fin⟩ := rfl
  rw [e, hpar, hfin]
  rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hbody with hb | hb <;> rw [hb] <;>
    simp [blobMentions, finRegs, jmpRegs, poleRegs, List.count_cons, hdr, Ne.symm hdr, hsd, hsr,
      Ne.symm hsd, Ne.symm hsr]

/-! ## The hits are outside the region -/

section
variable {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

/-- **No hit is inside the region.** -/
theorem labs_hits (ht : TopoOK bl topo) (hrev : rev = revCfg bl topo) :
    ∀ (p : Nat) (cs : List STest), ChainR bl rev p cs → p ∈ topo → ∀ t ∈ cs, t.hit ∉ (ilabs p cs).tail
  | _, [], _, _, _, h, _ => absurd h List.not_mem_nil
  | p, t :: rest, hc, hp, t', ht', hin => by
    obtain ⟨hto, hrm, hr⟩ := hc
    obtain ⟨b, yb, l, r, hb, hfin, -, hyb, -, hyf, -⟩ := testOf_spec hto
    obtain ⟨hy, h1⟩ := topo_jump ht hp hb (j := ⟨[], t.y⟩) (by rw [hfin]; simp [getJmps])
    obtain ⟨hm, h2⟩ := topo_jump ht hy hyb (j := ⟨[], t.miss⟩) (by rw [hyf]; simp [getJmps])
    simp only at hy h1 hm h2
    have hge : ∀ x ∈ ilabs t.miss rest, rk topo t.miss ≤ rk topo x := by
      intro x hx
      obtain ⟨L, hL⟩ := labs_head t.miss rest
      have hs := (labs_sorted ht t.miss rest hr hm).1
      have hx' : x ∈ ilabs t.miss rest ++ [lastMiss t.miss rest] := List.mem_append_left _ hx
      rw [hL] at hs hx'
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact Nat.le_refl _
      · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 x hx')
    change t'.hit ∈ t.y :: ilabs t.miss rest at hin
    by_cases et : t' = t
    · subst et
      obtain ⟨-, h3⟩ := topo_jump ht hy hyb (j := ⟨[], t'.hit⟩) (by rw [hyf]; simp [getJmps])
      simp only at h3
      rcases List.mem_cons.mp hin with e | hin
      · rw [e] at h3; omega
      cases rest with
      | nil => simp [ilabs] at hin
      | cons t2 rest2 =>
        change t'.hit ∈ t'.miss :: (ilabs t'.miss (t2 :: rest2)).tail at hin
        rcases List.mem_cons.mp hin with e | hin
        · -- a hit equal to its own no side: `rev` lists the yes side twice
          have hcnt := revCfg_count (k := t'.miss) hy hyb
          rw [← hrev, hyf] at hcnt
          have hpy : p ≠ t'.y := fun e2 => by rw [e2] at h1; omega
          rcases hrm (List.cons_ne_nil _ _) with h4 | h4 <;> rw [h4] at hcnt <;>
            simp [getJmps, e, List.count_cons, hpy, Ne.symm hpy] at hcnt
        · have h5 := labs_into hrev t'.miss (t2 :: rest2) hr t'.y yb ⟨[], t'.hit⟩ hy hyb
            (by rw [hyf]; simp [getJmps]) hin
          have := hge _ h5
          omega
    · have ht2 : t' ∈ rest := by
        rcases List.mem_cons.mp ht' with e | h
        · exact absurd e et
        · exact h
      have ih := labs_hits ht hrev t.miss rest hr hm t' ht2
      obtain ⟨q, hq⟩ := chainR_test hr t' ht2
      obtain ⟨-, yb', _, _, -, -, -, hyb', -, hyf', -⟩ := testOf_spec hq
      have hyt := y_mem_tail t.miss rest t' ht2
      have hlt := (labs_gt ht hr hm).1 _ hyt
      have hyT : t'.y ∈ topo :=
        (labs_sorted ht t.miss rest hr hm).2 _ (List.mem_append_left _ (List.mem_of_mem_tail hyt))
      obtain ⟨-, h3⟩ := topo_jump ht hyT hyb' (j := ⟨[], t'.hit⟩) (by rw [hyf']; simp [getJmps])
      simp only at h3
      rcases List.mem_cons.mp hin with e | hin
      · rw [e] at h3; omega
      cases rest with
      | nil => exact absurd ht2 List.not_mem_nil
      | cons t2 rest2 =>
        change t'.hit ∈ t.miss :: (ilabs t.miss (t2 :: rest2)).tail at hin
        rcases List.mem_cons.mp hin with e | hin
        · rw [e] at h3; omega
        · exact ih hin

end

/-! ## `TagHyp` -/

/-- **`TagHyp` from what the driver has**: a chain that `chainOf` returns at
a member `o` of `topo`, on `rev = revCfg bl topo` with `TopoOK bl topo`. -/
theorem tagHyp_of {bl : Map Blob} {topo : List Nat} {n o : Nat} {t0 : STest} {tl : List STest}
    (ht : TopoOK bl topo) (ho : o ∈ topo) (h : chainOf bl (revCfg bl topo) n o = some (t0 :: tl)) :
    TagHyp bl o t0 tl := by
  have hc := chainOf_rev n o _ h
  obtain ⟨hblocks, hhead⟩ := tagHyp_shape h
  obtain ⟨hS, hT⟩ := labs_sorted ht o (t0 :: tl) hc ho
  have hgt := labs_gt ht hc ho
  have hnd : (ilabs o (t0 :: tl) ++ [lastMiss o (t0 :: tl)]).Nodup :=
    hS.imp (fun h e => by subst e; omega)
  have e1 : ilabs o (t0 :: tl) ++ [lastMiss o (t0 :: tl)] =
      o :: t0.y :: (ilabs t0.miss tl ++ [tagMiss t0 tl]) := by
    show o :: t0.y :: (ilabs t0.miss tl ++ [lastMiss t0.miss tl]) = _
    rw [lastMiss_tag]
  rw [e1] at hnd
  obtain ⟨hn1, hn2⟩ := List.nodup_cons.mp hnd
  obtain ⟨hn3, hn4⟩ := List.nodup_cons.mp hn2
  have hperm := ilabs_perm t0 tl
  have hin_iff : ∀ k, TagIn t0 tl k ↔ k ∈ (ilabs o (t0 :: tl)).tail := by
    intro k
    show k = t0.y ∨ k ∈ tagIds (t0 :: tl) ↔ k ∈ t0.y :: ilabs t0.miss tl
    rw [List.mem_cons, hperm.mem_iff]
  have hnd' : (ilabs t0.miss tl).Nodup := (List.nodup_append.mp hn4).1
  have hmissI : tagMiss t0 tl ∉ ilabs t0.miss tl := fun hm =>
    (List.nodup_append.mp hn4).2.2 _ hm _ (List.mem_singleton_self _) rfl
  have hq0 : testOf bl (revCfg bl topo) o = some (some t0) := hc.1
  refine ⟨?_, ?_, ?_, ?_, ?_, hblocks, hhead, ?_, ?_, ?_, ?_, ?_⟩
  · exact hperm.nodup_iff.mp hnd'
  · exact fun hm => hn3 (List.mem_append_left _ (hperm.mem_iff.mpr hm))
  · exact fun hm => hn1 (List.mem_cons_of_mem _ (List.mem_append_left _ (hperm.mem_iff.mpr hm)))
  · exact fun e => hn1 (by rw [e]; exact List.mem_cons_self)
  · -- hr
    intro t ht'
    rcases List.mem_cons.mp ht' with e | ht'
    · rw [e]; exact Ne.symm (test_regs hq0).1
    · obtain ⟨q, hq⟩ := chainR_test hc t (List.mem_cons_of_mem _ ht')
      obtain ⟨yb0, hyb0, c0d, -⟩ := test_count hq0
      obtain ⟨yb, hyb, -, cr⟩ := test_count hq
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hud, -⟩ := testOf_spec hq0
      have hne : t.y ≠ t0.y := fun e => hn3 (List.mem_append_left _
        (by rw [← e]; exact List.mem_of_mem_tail (y_mem_tail t0.miss tl t ht')))
      intro e
      rw [e] at cr
      have := uses_ge2 hne hyb hyb0 t0.d
      omega
  · -- hits
    intro t ht'
    obtain ⟨q, hq⟩ := chainR_test hc t ht'
    obtain ⟨-, yb, _, _, -, -, -, hyb, -, hyf, -⟩ := testOf_spec hq
    have hyt := y_mem_tail o (t0 :: tl) t ht'
    have hyT : t.y ∈ topo := hT _ (List.mem_append_left _ (List.mem_of_mem_tail hyt))
    obtain ⟨hh, h3⟩ := topo_jump ht hyT hyb (j := ⟨[], t.hit⟩) (by rw [hyf]; simp [getJmps])
    simp only at hh h3
    have h4 := hgt.1 _ hyt
    refine ⟨ht.2.2.1 _ hh, fun hI => labs_hits ht rfl o (t0 :: tl) hc ho t ht' ((hin_iff _).mp hI),
      fun e => ?_⟩
    rw [e] at h3; omega
  · -- miss
    refine ⟨ht.2.2.1 _ (hT _ (by rw [e1]; simp)), fun hI => ?_, fun e => hn1 (by rw [← e]; simp)⟩
    rw [hin_iff] at hI
    change tagMiss t0 tl ∈ t0.y :: ilabs t0.miss tl at hI
    rcases List.mem_cons.mp hI with e | e
    · exact hn3 (by rw [← e]; simp)
    · exact hmissI e
  · -- noI
    intro k b j hk hkI hko hb hj hjI
    have hkT := ht.2.2.2.1 k hk
    have h5 := labs_into rfl o (t0 :: tl) hc k b j hkT hb hj ((hin_iff _).mp hjI)
    change k ∈ o :: (ilabs o (t0 :: tl)).tail at h5
    rcases List.mem_cons.mp h5 with e | e
    · exact hko e
    · exact hkI ((hin_iff _).mpr e)
  · -- ment
    intro k b _ hkI hb r hr hrT
    rw [tagRegs, List.mem_flatMap] at hrT
    obtain ⟨t, ht', hrt⟩ := hrT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrt
    obtain ⟨q, hq⟩ := chainR_test hc t ht'
    obtain ⟨yb, hyb, cd, cr⟩ := test_count hq
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hud, hur⟩ := testOf_spec hq
    have hne : k ≠ t.y := fun e => hkI ((hin_iff _).mpr (by rw [e]; exact y_mem_tail o _ t ht'))
    have h1 := uses_ge2 hne hb hyb r
    have h2 : 0 < (blobMentions b).count r := List.count_pos_iff.mpr hr
    rcases hrt with rfl | rfl <;> omega
  · -- zero
    intro hz
    have := hgt.1 0 ((hin_iff 0).mp hz)
    rw [rk_zero ht] at this
    omega

/-- **One tagged chain replaced keeps the code**, from what the driver has:
`switchTag` applied (with the blocks before as both `bl` and `out`) to a
chain that `chainOf` returns at a member `o` of `topo`, on
`rev = revCfg c.blocks topo` with `TopoOK c.blocks topo`. -/
theorem tag_keeps (c : Straight Map) {topo : List Nat} {out' : Map Blob} {fuel n o : Nat} {t0 : STest}
    {tl : List STest} {done done' : List Nat} (ht : TopoOK c.blocks topo) (ho : o ∈ topo)
    (hch : chainOf c.blocks (revCfg c.blocks topo) n o = some (t0 :: tl))
    (h : switchTag c.blocks c.blocks fuel o (t0 :: tl) done = some (out', done')) :
    Keeps c (withBlocks c out') :=
  tag_keeps_of c h (tagHyp_of ht ho hch)

end Opt
end SkaModel
end Formalization
