import lemmas.Ska.OptSwitchPlain

/-!
# `+switch-chains`: `PlainHyp` from `plains-of`, `+rev-cfg` and `TopoOK`

**`plainHyp_of`**: a plain chain `(o, t0) :: pl` that `plainsOf` returns at a
member `o` of `topo`, on `rev = revCfg bl topo` with `TopoOK bl topo`, with
`pl` not empty and `nex` at least `nexOf bl`, meets every field of
`PlainHyp`; so **`plain_keeps`**: one application of `switchPlain` keeps the
code under those hypotheses alone.  The analogue of `tagHyp_of`.

* `PlainR` keeps what `plains-of` checked at each step (`plainsOf_rev`): the
  test at each label, the one predecessor `[p]` of the next label, its empty
  parameters and one-op body, and the same `d`.
* The labels `o`, `q1`, …, `qk` and the final miss (`plast`) rise in `topo`
  (`plabs_sorted`), since each is the no side of the `%eqq` before
  (`topo_jump`).  That gives `nd`, `ho'`, the miss outside the region and
  `zero`; every member of `topo` is a block, below `nexOf bl`
  (`nexOf_gt`), which gives `old`, `ho` and the `nex` halves of `hits`,
  `miss`, `noI`.
* `plabs_into`: a block of `topo` that jumps to a test after the head is a
  label of the chain (the check `getJa rev t.miss = [p]`), which gives `noI`.
* `plabs_hits`: no hit is a test after the head.  A hit equal to the next
  label of its own test is excluded by `revCfg_count` (the test would be
  listed twice where `plains-of` saw `[p]`), a later label by `plabs_into` and
  the ranks, an earlier one by the ranks.
* `plain_head_count`: in the block of a test `r` is mentioned once by the
  `%eqq`, once by the body, not by the parameters (`uses = 2`), so the head
  has one `%imm` into `r0` and its other ops and parameters are off `r0`;
  every other block is off every test register (`plain_off`, `uses_ge2`),
  which gives the rest of `headB` and `ment`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## What `plain-of` checks -/

theorem immInto_spec {l r : Nat} : ∀ {body : List Pole} {mn : Noun} {md : Nat}, immInto l r body = some (mn, md) →
    Pole.imm mn md ∈ body ∧ (md = l ∨ md = r)
  | [], _, _, h => by simp [immInto] at h
  | op :: t, mn, md, h => by
    cases op with
    | imm n d =>
      simp only [immInto] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, by assumption⟩
      · have := immInto_spec h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    | _ => simp only [immInto] at h; have := immInto_spec h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- **The shape `plain-of` checks.** -/
theorem plainOf_spec {bl : Map Blob} {p : Nat} {t : SPlain} (h : plainOf bl p = some (some t)) :
    ∃ b l r, HoonMap.get bl p = some b ∧ b.fin = Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩ ∧
      ((l = t.d ∧ r = t.r) ∨ (l = t.r ∧ r = t.d)) ∧ t.r ≠ t.d ∧
      immInto l r b.body = some (A t.c, t.r) ∧ usesOf bl t.r = 2 := by
  unfold plainOf at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  all_goals try (simp at h; done)
  rename_i l r hit miss heq
  split at h
  · simp at h
  rename_i mn md himm
  split at h
  · simp at h
  rename_i c hc
  split at h
  · simp at h
  rename_i hlr
  split at h
  · simp at h
  rename_i hu
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨rfl, -⟩ := smallAtom_eq hc
  have hmd := (immInto_spec himm).2
  refine ⟨b, l, r, hb, heq, ?_, ?_, himm, by simpa using hu⟩
  · by_cases e : md = l
    · rw [if_pos e]; exact Or.inr ⟨e.symm, rfl⟩
    · rw [if_neg e]
      rcases hmd with h1 | h1
      · exact absurd h1 e
      · exact Or.inl ⟨rfl, h1.symm⟩
  · by_cases e : md = l
    · rw [if_pos e]; intro h1; exact hlr (e.symm.trans h1)
    · rw [if_neg e]; exact e

/-! ## Counting the mentions of a test register -/

theorem count_mem_flat {f : Pole → List Nat} {r : Nat} : ∀ {L : List Pole} {x : Pole}, x ∈ L →
    (f x).count r ≤ (L.flatMap f).count r
  | [], _, h => absurd h List.not_mem_nil
  | a :: L, x, h => by
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := count_mem_flat (f := f) (r := r) h; omega

theorem count_two_flat {f : Pole → List Nat} {r : Nat} : ∀ {L : List Pole} {x y : Pole}, x ∈ L → y ∈ L → x ≠ y →
    (f x).count r + (f y).count r ≤ (L.flatMap f).count r
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | a :: L, x, y, hx, hy, hxy => by
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hx with ex | hx <;> rcases List.mem_cons.mp hy with ey | hy
    · exact absurd (ex.trans ey.symm) hxy
    · rw [ex]; have := count_mem_flat (f := f) (r := r) hy; omega
    · rw [ey]; have := count_mem_flat (f := f) (r := r) hx; omega
    · have := count_two_flat (f := f) (r := r) hx hy hxy; omega

/-- In the block of a plain test, `r` is mentioned once by the `%eqq`, once by
the body and not by the parameters (`uses = 2`). -/
theorem plain_head_count {bl : Map Blob} {p : Nat} {t : SPlain} (h : plainOf bl p = some (some t)) :
    ∃ b l r, HoonMap.get bl p = some b ∧ b.fin = Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩ ∧
      ((l = t.d ∧ r = t.r) ∨ (l = t.r ∧ r = t.d)) ∧ Pole.imm (A t.c) t.r ∈ b.body ∧
      b.par.count t.r = 0 ∧ (b.body.flatMap poleRegs).count t.r = 1 ∧ 2 ≤ (blobMentions b).count t.r := by
  obtain ⟨b, l, r, hb, hfin, hlr, hrd, himm, hu⟩ := plainOf_spec h
  have hmem := (immInto_spec himm).1
  have hle := uses_ge hb t.r
  rw [hu] at hle
  have hfc : (finRegs b.fin).count t.r = 1 := by
    rw [hfin]
    rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [finRegs, jmpRegs, List.count_cons, hrd, Ne.symm hrd]
  have hbc : 1 ≤ (b.body.flatMap poleRegs).count t.r := by
    have := count_mem_flat (f := poleRegs) (r := t.r) hmem
    simpa [poleRegs] using this
  have e : (blobMentions b).count t.r =
      b.par.count t.r + (finRegs b.fin).count t.r + (b.body.flatMap poleRegs).count t.r := by
    simp only [blobMentions, List.count_append]
  refine ⟨b, l, r, hb, hfin, hlr, hmem, by omega, by omega, by omega⟩

/-- A block other than a plain test's does not mention its register. -/
theorem plain_off {bl : Map Blob} {q k : Nat} {t : SPlain} {b : Blob} (h : plainOf bl q = some (some t))
    (hk : k ≠ q) (hb : HoonMap.get bl k = some b) : (blobMentions b).count t.r = 0 := by
  obtain ⟨bq, -, -, hbq, -, -, -, -, -, hc2⟩ := plain_head_count h
  obtain ⟨-, -, -, -, -, -, -, -, hu⟩ := plainOf_spec h
  have := uses_ge2 hk hb hbq t.r
  omega

/-! ## The chain with its checks -/

/-- The plain chain from `p`, with what `plains-of` checks at each step. -/
def PlainR (bl : Map Blob) (rev : Map (List Nat)) : Nat → List (Nat × SPlain) → Prop
  | _, [] => True
  | p, t :: rest => t.1 = p ∧ plainOf bl p = some (some t.2) ∧
      (rest ≠ [] → getJa rev t.2.miss = [p] ∧ ∃ nb n x, HoonMap.get bl t.2.miss = some nb ∧ nb.par = [] ∧
        nb.body = [Pole.imm n x]) ∧
      (∀ t2 ∈ rest.head?, t2.2.d = t.2.d) ∧ PlainR bl rev t.2.miss rest

theorem plainsOf_rev {bl : Map Blob} {rev : Map (List Nat)} : ∀ (n p : Nat) (ps : List (Nat × SPlain)),
    plainsOf bl rev n p = some ps → PlainR bl rev p ps
  | 0, _, _, h => by simp [plainsOf] at h
  | n + 1, p, ps, h => by
    unfold plainsOf at h
    obtain ⟨to, hto, h⟩ := Option.bind_eq_some_iff.mp h
    cases to with
    | none => simp at h; subst h; trivial
    | some t =>
    simp only at h
    obtain ⟨rest, hin, rfl⟩ := Option.map_eq_some_iff.mp h
    have stop : rest = [] → PlainR bl rev p ((p, t) :: rest) := by
      intro e; subst e; exact ⟨rfl, hto, fun h => absurd rfl h, by simp, trivial⟩
    obtain ⟨nb, hnb, hin⟩ := Option.bind_eq_some_iff.mp hin
    split at hin
    · simp at hin; exact stop hin
    rename_i hpar
    split at hin
    · rename_i nn xx hbody
      split at hin
      · simp at hin; exact stop hin
      rename_i hrv
      obtain ⟨t2o, ht2o, hin⟩ := Option.bind_eq_some_iff.mp hin
      cases t2o with
      | none => simp at hin; exact stop hin
      | some t2 =>
        simp only at hin
        split at hin
        · simp at hin; exact stop hin
        rename_i hd
        have ih := plainsOf_rev n t.miss rest hin
        refine ⟨rfl, hto, fun _ => ⟨by simpa using hrv, nb, nn, xx, hnb, by simpa using hpar, hbody⟩, ?_, ih⟩
        intro t3 ht3
        cases rest with
        | nil => simp at ht3
        | cons t4 r4 =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ht3
          subst ht3
          have h4 := ih.2.1
          rw [ht2o] at h4
          simp only [Option.some.injEq] at h4
          rw [← h4]
          simpa using hd
    · simp at hin; exact stop hin

section
variable {bl : Map Blob} {rev : Map (List Nat)}

theorem plainR_mem : ∀ {p : Nat} {ps : List (Nat × SPlain)}, PlainR bl rev p ps →
    ∀ t ∈ ps, plainOf bl t.1 = some (some t.2)
  | _, [], _, _, h => absurd h List.not_mem_nil
  | _, _ :: _, ⟨h1, h2, _, _, hr⟩, t', h => by
    rcases List.mem_cons.mp h with e | h
    · rw [e, h1]; exact h2
    · exact plainR_mem hr t' h

theorem plainR_d : ∀ {p : Nat} {t : Nat × SPlain} {rest : List (Nat × SPlain)}, PlainR bl rev p (t :: rest) →
    ∀ u ∈ rest, u.2.d = t.2.d
  | _, _, [], _, _, h => absurd h List.not_mem_nil
  | _, _, t1 :: _, ⟨_, _, _, hd, hr⟩, u, h => by
    have e1 : t1.2.d = _ := hd t1 (by simp)
    rcases List.mem_cons.mp h with e | h
    · rw [e]; exact e1
    · rw [← e1]; exact plainR_d hr u h

/-- The final miss of a plain chain from `p`. -/
def plast : Nat → List (Nat × SPlain) → Nat
  | p, [] => p
  | _, t :: rest => plast t.2.miss rest

theorem plast_miss : ∀ (p0 : Nat × SPlain) (pl : List (Nat × SPlain)), plast p0.2.miss pl = plainMiss p0 pl
  | p0, [] => by simp [plast, plainMiss]
  | p0, t1 :: tl => by
    rw [show plast p0.2.miss (t1 :: tl) = plast t1.2.miss tl from rfl, plast_miss t1 tl]
    simp [plainMiss, List.getLast_cons]

theorem plabs_head {p : Nat} {ps : List (Nat × SPlain)} (hc : PlainR bl rev p ps) :
    ∃ L, ps.map Prod.fst ++ [plast p ps] = p :: L := by
  cases ps with
  | nil => exact ⟨[], rfl⟩
  | cons t rest =>
    refine ⟨rest.map Prod.fst ++ [plast t.2.miss rest], ?_⟩
    rw [List.map_cons, List.cons_append, hc.1]; rfl

/-- The tests of a plain chain after the first, as `PlainBlocks` states
them. -/
theorem plain_blocks : ∀ (p : Nat) (t : Nat × SPlain) (rest : List (Nat × SPlain)), PlainR bl rev p (t :: rest) →
    rest ≠ [] → PlainBlocks bl t.2.d (plast t.2.miss rest) rest
  | _, _, [], _, h => absurd rfl h
  | p, t, t1 :: r2, ⟨_, _, hnx, hd, hr⟩, _ => by
    obtain ⟨_, nb, n, x, hnb, hpar, hbody⟩ := hnx (List.cons_ne_nil _ _)
    have e1 : t1.1 = t.2.miss := hr.1
    have ed : t1.2.d = t.2.d := hd t1 (by simp)
    obtain ⟨b, l, r, hb, hfin, hlr, hrd, himm, -⟩ := plainOf_spec hr.2.1
    have hbn : nb = b := by rw [hnb] at hb; exact Option.some.inj hb
    rw [← hbn] at hfin himm
    have hm := (immInto_spec himm).1
    rw [hbody] at hm
    simp only [List.mem_singleton, Pole.imm.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨by rw [← ed]; exact hrd, ⟨l, r, ?_, by rw [← ed]; exact hlr⟩, ?_, fun hne => ?_⟩
    · rw [e1, hnb]
      have : nb = ⟨nb.par, nb.body, nb.fin⟩ := rfl
      rw [this, hpar, hbody, hfin]
    · cases r2 with
      | nil => rfl
      | cons t2 r3 => exact hr.2.2.2.2.1.symm
    · have ih := plain_blocks t.2.miss t1 r2 hr hne
      rw [ed] at ih
      exact ih

end

/-! ## The labels of a plain chain in `topo` -/

section
variable {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

/-- **The labels of a plain chain rise in `topo`.** -/
theorem plabs_sorted (ht : TopoOK bl topo) : ∀ (p : Nat) (ps : List (Nat × SPlain)), PlainR bl rev p ps →
    p ∈ topo → (ps.map Prod.fst ++ [plast p ps]).Pairwise (fun a b => rk topo a < rk topo b) ∧
      ∀ x ∈ ps.map Prod.fst ++ [plast p ps], x ∈ topo
  | p, [], _, hp => ⟨List.pairwise_singleton _ _, by simp [plast, hp]⟩
  | p, t :: rest, hc, hp => by
    obtain ⟨h1, hq, -, -, hr⟩ := hc
    obtain ⟨b, l, r, hb, hfin, -⟩ := plainOf_spec hq
    obtain ⟨hm, h2⟩ := topo_jump ht hp hb (j := ⟨[], t.2.miss⟩) (by rw [hfin]; simp [getJmps])
    simp only at hm h2
    obtain ⟨hs, hin⟩ := plabs_sorted ht t.2.miss rest hr hm
    have hge : ∀ x ∈ rest.map Prod.fst ++ [plast t.2.miss rest], rk topo t.2.miss ≤ rk topo x := by
      obtain ⟨L, hL⟩ := plabs_head hr
      rw [hL] at hs ⊢
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_refl _
      · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 x hx)
    have e : (t :: rest).map Prod.fst ++ [plast p (t :: rest)] =
        p :: (rest.map Prod.fst ++ [plast t.2.miss rest]) := by
      rw [List.map_cons, List.cons_append, h1]; rfl
    rw [e]
    refine ⟨List.Pairwise.cons (fun x hx => by have := hge x hx; omega) hs, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · exact hin x hx

theorem plabs_ge (ht : TopoOK bl topo) {p : Nat} {ps : List (Nat × SPlain)} (hc : PlainR bl rev p ps)
    (hp : p ∈ topo) : ∀ x ∈ ps.map Prod.fst, rk topo p ≤ rk topo x := by
  obtain ⟨hs, -⟩ := plabs_sorted ht p ps hc hp
  obtain ⟨L, hL⟩ := plabs_head hc
  rw [hL] at hs
  intro x hx
  have hx' : x ∈ p :: L := by rw [← hL]; exact List.mem_append_left _ hx
  rcases List.mem_cons.mp hx' with rfl | hx'
  · exact Nat.le_refl _
  · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 x hx')

/-- **A block of `topo` that jumps to a test after the head is a label of the
chain.** -/
theorem plabs_into (hrev : rev = revCfg bl topo) : ∀ (p : Nat) (ps : List (Nat × SPlain)), PlainR bl rev p ps →
    ∀ (k : Nat) (b : Blob) (j : Jmp), k ∈ topo → HoonMap.get bl k = some b → j ∈ getJmps b.fin →
      j.there ∈ (ps.map Prod.fst).tail → k ∈ ps.map Prod.fst
  | _, [], _, _, _, _, _, _, _, h => by simp at h
  | p, t :: rest, ⟨h1, _, hnx, _, hr⟩, k, b, j, hk, hb, hj, hth => by
    have hmem := revCfg_mem hk hb hj
    rw [← hrev] at hmem
    cases rest with
    | nil => simp at hth
    | cons t1 r2 =>
      have e1 : t1.1 = t.2.miss := hr.1
      simp only [List.map_cons, List.tail_cons, List.mem_cons] at hth
      rcases hth with e | hth
      · rw [e, e1, (hnx (List.cons_ne_nil _ _)).1] at hmem
        simp only [List.mem_singleton] at hmem
        rw [hmem, ← h1]; exact List.mem_cons_self
      · have := plabs_into hrev t.2.miss (t1 :: r2) hr k b j hk hb hj (by simpa using hth)
        exact List.mem_cons_of_mem _ this

/-- **No hit is a test after the head.** -/
theorem plabs_hits (ht : TopoOK bl topo) (hrev : rev = revCfg bl topo) :
    ∀ (p : Nat) (ps : List (Nat × SPlain)), PlainR bl rev p ps → p ∈ topo →
      ∀ t ∈ ps, t.2.hit ∉ (ps.map Prod.fst).tail
  | _, [], _, _, _, h, _ => absurd h List.not_mem_nil
  | p, t :: rest, hc, hp, t', ht', hin => by
    obtain ⟨h1, hq, hnx, -, hr⟩ := hc
    obtain ⟨b, l, r, hb, hfin, -⟩ := plainOf_spec hq
    obtain ⟨hm, h2⟩ := topo_jump ht hp hb (j := ⟨[], t.2.miss⟩) (by rw [hfin]; simp [getJmps])
    simp only at hm h2
    have hsr := plabs_sorted ht t.2.miss rest hr hm
    have hge := plabs_ge ht hr hm
    cases rest with
    | nil => simp at hin
    | cons t1 r2 =>
      have e1 : t1.1 = t.2.miss := hr.1
      simp only [List.map_cons, List.tail_cons, List.mem_cons] at hin
      rcases List.mem_cons.mp ht' with et | ht2
      · rw [et] at hin
        rcases hin with e | hin
        · have hcnt := revCfg_count (k := t.2.miss) hp hb
          rw [← hrev, hfin, (hnx (List.cons_ne_nil _ _)).1] at hcnt
          rw [e1] at e
          simp [getJmps, e] at hcnt
        · have h5 := plabs_into hrev t.2.miss (t1 :: r2) hr p b ⟨[], t.2.hit⟩ hp hb
            (by rw [hfin]; simp [getJmps]) (by simpa using hin)
          have := hge p h5
          omega
      · have ih := plabs_hits ht hrev t.2.miss (t1 :: r2) hr hm t' ht2
        obtain ⟨b', l', r', hb', hfin', -⟩ := plainOf_spec (plainR_mem hr t' ht2)
        have hT' : t'.1 ∈ topo := hsr.2 _ (List.mem_append_left _ (List.mem_map_of_mem ht2))
        obtain ⟨-, h3⟩ := topo_jump ht hT' hb' (j := ⟨[], t'.2.hit⟩) (by rw [hfin']; simp [getJmps])
        simp only at h3
        have h4 := hge t'.1 (List.mem_map_of_mem ht2)
        rcases hin with e | hin
        · rw [e, e1] at h3; omega
        · exact ih (by simpa using hin)

end

/-! ## `PlainHyp` -/

/-- **`PlainHyp` from what the driver has**: a plain chain that `plainsOf`
returns at a member `o` of `topo`, on `rev = revCfg bl topo` with
`TopoOK bl topo`, with a test after the head, and `nex` at least
`nexOf bl`. -/
theorem plainHyp_of {bl : Map Blob} {topo : List Nat} {n o nex : Nat} {p0 : Nat × SPlain}
    {pl : List (Nat × SPlain)} (ht : TopoOK bl topo) (ho : o ∈ topo)
    (h : plainsOf bl (revCfg bl topo) n o = some (p0 :: pl)) (hpl : pl ≠ []) (hnex : nexOf bl ≤ nex) :
    PlainHyp bl o nex p0 pl := by
  have hc := plainsOf_rev n o _ h
  obtain ⟨hS, hT⟩ := plabs_sorted ht o (p0 :: pl) hc ho
  have e1 : (p0 :: pl).map Prod.fst ++ [plast o (p0 :: pl)] = o :: (pl.map Prod.fst ++ [plainMiss p0 pl]) := by
    rw [List.map_cons, List.cons_append, hc.1, ← plast_miss]; rfl
  rw [e1] at hS hT
  have hnd : (o :: (pl.map Prod.fst ++ [plainMiss p0 pl])).Nodup := hS.imp (fun h e => by subst e; omega)
  obtain ⟨hn1, hn2⟩ := List.nodup_cons.mp hnd
  have hlt : ∀ x ∈ topo, x < nex := fun x hx => Nat.lt_of_lt_of_le (nexOf_gt bl (ht.2.2.1 x hx)) hnex
  have hrk : ∀ x ∈ pl.map Prod.fst ++ [plainMiss p0 pl], rk topo o < rk topo x := (List.pairwise_cons.mp hS).1
  have hTo : ∀ x ∈ pl.map Prod.fst ++ [plainMiss p0 pl], x ∈ topo := fun x hx => hT x (List.mem_cons_of_mem _ hx)
  have hq0 : plainOf bl o = some (some p0.2) := hc.2.1
  have hlab : ∀ t ∈ p0 :: pl, t.1 = o ∨ t.1 ∈ pl.map Prod.fst := by
    intro t ht'
    rcases List.mem_cons.mp ht' with e | e
    · left; rw [e]; exact hc.1
    · right; exact List.mem_map_of_mem e
  have hlabT : ∀ t ∈ p0 :: pl, t.1 ∈ topo ∧ rk topo o ≤ rk topo t.1 := by
    intro t ht'
    rcases hlab t ht' with e | e
    · rw [e]; exact ⟨ho, Nat.le_refl _⟩
    · exact ⟨hTo _ (List.mem_append_left _ e), Nat.le_of_lt (hrk _ (List.mem_append_left _ e))⟩
  obtain ⟨b, l, r, hb, hfin, hlr, hmem, hpar0, hbody1, -⟩ := plain_head_count hq0
  refine ⟨(List.nodup_append.mp hn2).1, fun k hk => hlt k (hTo k (List.mem_append_left _ hk)), hlt o ho,
    fun hm => hn1 (List.mem_append_left _ hm), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hr
    intro t ht'
    obtain ⟨-, -, -, -, -, -, hrd, -⟩ := plainOf_spec (plainR_mem hc t ht')
    rcases List.mem_cons.mp ht' with e | ht2
    · rw [e] at hrd ⊢; exact hrd
    · rw [← plainR_d hc t ht2]; exact hrd
  · -- blocks
    have := plain_blocks o p0 pl hc hpl
    rw [plast_miss] at this
    exact this
  · -- miss0
    cases pl with
    | nil => exact absurd rfl hpl
    | cons t1 rest => exact ⟨t1, rest, rfl, hc.2.2.2.2.1.symm⟩
  · -- headB
    refine ⟨b, l, r, hb, hfin, hlr, hmem, fun n1 n2 h1 h2 => ?_, fun r2 hr2 hrP => ?_,
      fun p hp hk r2 hr2 hrP => ?_⟩
    · refine Classical.byContradiction fun e => ?_
      have := count_two_flat (f := poleRegs) (r := p0.2.r) h1 h2 (fun h => e (by cases h; rfl))
      simp [poleRegs] at this
      omega
    · unfold plainRegs at hrP
      obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hrP
      rcases List.mem_cons.mp ht' with e | ht2
      · rw [e] at hr2
        have := List.count_pos_iff.mpr hr2
        omega
      · have hko : o ≠ t.1 := fun e => hn1 (List.mem_append_left _ (e ▸ List.mem_map_of_mem ht2))
        have h0 := plain_off (plainR_mem hc t (List.mem_cons_of_mem _ ht2)) hko hb
        have := List.count_pos_iff.mpr (show t.2.r ∈ blobMentions b by simp [blobMentions, hr2])
        omega
    · unfold plainRegs at hrP
      obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hrP
      rcases List.mem_cons.mp ht' with e | ht2
      · rw [e] at hr2
        have hne : p ≠ Pole.imm (A p0.2.c) p0.2.r := fun e2 => by subst e2; simp [plainKeep] at hk
        have h2 := count_two_flat (f := poleRegs) (r := p0.2.r) hp hmem hne
        have h3 := List.count_pos_iff.mpr hr2
        have h4 : (poleRegs (Pole.imm (A p0.2.c) p0.2.r)).count p0.2.r = 1 := by simp [poleRegs]
        omega
      · have hko : o ≠ t.1 := fun e => hn1 (List.mem_append_left _ (e ▸ List.mem_map_of_mem ht2))
        have h0 := plain_off (plainR_mem hc t (List.mem_cons_of_mem _ ht2)) hko hb
        have := List.count_pos_iff.mpr (show t.2.r ∈ blobMentions b from
          List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨p, hp, hr2⟩)))
        omega
  · -- hits
    intro t ht'
    obtain ⟨bt, _, _, hbt, hfint, -⟩ := plainOf_spec (plainR_mem hc t ht')
    obtain ⟨htT, hge⟩ := hlabT t ht'
    obtain ⟨hh, h3⟩ := topo_jump ht htT hbt (j := ⟨[], t.2.hit⟩) (by rw [hfint]; simp [getJmps])
    simp only at hh h3
    refine ⟨ht.2.2.1 _ hh, fun hI => ?_, fun e => ?_⟩
    · rcases hI with hI | hI
      · exact plabs_hits ht rfl o (p0 :: pl) hc ho t ht' (by simpa using hI)
      · have := hlt _ hh; omega
    · rw [e] at h3; omega
  · -- miss
    have hmT := hTo _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ⟨ht.2.2.1 _ hmT, fun hI => ?_,
      fun e => hn1 (by rw [← e]; exact List.mem_append_right _ (List.mem_singleton_self _))⟩
    rcases hI with hI | hI
    · exact (List.nodup_append.mp hn2).2.2 _ hI _ (List.mem_singleton_self _) rfl
    · have := hlt _ hmT; omega
  · -- noI
    intro k b' j hk hkI hko hb' hj hjI
    have hkT := ht.2.2.2.1 k hk
    rcases hjI with hjI | hjI
    · have h5 := plabs_into rfl o (p0 :: pl) hc k b' j hkT hb' hj (by simpa using hjI)
      rw [List.map_cons, hc.1, List.mem_cons] at h5
      rcases h5 with e | e
      · exact hko e
      · exact hkI (Or.inl e)
    · have := hlt _ (topo_jump ht hkT hb' hj).1; omega
  · -- ment
    intro k b' _ hkI hko hb' r2 hr2 hrP
    unfold plainRegs at hrP
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hrP
    have hkt : k ≠ t.1 := by
      rcases hlab t ht' with e | e
      · rw [e]; exact hko
      · exact fun e2 => hkI (Or.inl (e2 ▸ e))
    have h0 := plain_off (plainR_mem hc t ht') hkt hb'
    have := List.count_pos_iff.mpr hr2
    omega
  · -- zero
    intro hz
    rcases hz with hz | hz
    · have := hrk 0 (List.mem_append_left _ hz); rw [rk_zero ht] at this; omega
    · have := hlt o ho; omega

/-- **One plain chain replaced keeps the code**, from what the driver has:
`switchPlain` applied (with the blocks before as both `bl` and `out`) to a
plain chain that `plainsOf` returns at a member `o` of `topo`, with a test
after the head, on `rev = revCfg c.blocks topo` with `TopoOK c.blocks topo`,
and `nex` at least `nexOf c.blocks`. -/
theorem plain_keeps (c : Straight Map) {topo : List Nat} {out' : Map Blob} {fuel n o nex nex' : Nat}
    {p0 : Nat × SPlain} {pl : List (Nat × SPlain)} {done done' : List Nat} (ht : TopoOK c.blocks topo)
    (ho : o ∈ topo) (hps : plainsOf c.blocks (revCfg c.blocks topo) n o = some (p0 :: pl)) (hpl : pl ≠ [])
    (hnex : nexOf c.blocks ≤ nex)
    (h : switchPlain c.blocks c.blocks fuel o (p0 :: pl) done nex = some (out', done', nex')) :
    Keeps c (withBlocks c out') :=
  plain_keeps_of c h (plainHyp_of ht ho hps hpl hnex)

/-! ## The blocks after one plain chain, for the walk -/

/-- The region of a plain chain done: the tests after the head and the
labels taken from `nex` up to the next `nex`. -/
def PRg (nex nex' : Nat) (pl : List (Nat × SPlain)) (k : Nat) : Prop := k ∈ pl.map Prod.fst ∨ (nex ≤ k ∧ k < nex')

/-- Where a node of a plain chain's tree may jump: its region, its hits, its
final miss. -/
def PJ (nex nex' : Nat) (p0 : Nat × SPlain) (pl : List (Nat × SPlain)) (k : Nat) : Prop :=
  PRg nex nex' pl k ∨ (∃ t ∈ p0 :: pl, k = t.2.hit) ∨ k = plainMiss p0 pl

/-- What a node of a plain chain's tree may mention: `d` and the test
registers. -/
def PS (p0 : Nat × SPlain) (pl : List (Nat × SPlain)) (r : Nat) : Prop := r = p0.2.d ∨ r ∈ plainRegs (p0 :: pl)

/-- **The blocks after one plain chain**: the head as in `plain_tree`, its
appended root and every block in the region tree nodes (`NodeOK`), no other
label changed, none from the next `nex` up, given that `out` has none from
`nex` up. -/
theorem plain_tree2 {bl out out' : Map Blob} {fuel o nex nex' : Nat} {p0 : Nat × SPlain}
    {pl : List (Nat × SPlain)} {done done' : List Nat}
    (h : switchPlain bl out fuel o (p0 :: pl) done nex = some (out', done', nex'))
    (hold : ∀ k ∈ pl.map Prod.fst, k < nex) (ho : o < nex) (ho' : o ∉ pl.map Prod.fst)
    (hab : ∀ k, nex ≤ k → HoonMap.get out k = none) :
    ∃ b nb nf, HoonMap.get bl o = some b ∧
      HoonMap.get out' o = some ⟨b.par, b.body.filter (plainKeep p0.2.r) ++ nb, nf⟩ ∧
      NodeOK (PJ nex nex' p0 pl) (PS p0 pl) ⟨[], nb, nf⟩ ∧
      (∀ k bk, PRg nex nex' pl k → HoonMap.get out' k = some bk → NodeOK (PJ nex nex' p0 pl) (PS p0 pl) bk) ∧
      (∀ k, k ≠ o → ¬ PRg nex nex' pl k → HoonMap.get out' k = HoonMap.get out k) ∧
      (∀ k, nex' ≤ k → HoonMap.get out' k = none) ∧ nex ≤ nex' ∧ done' = pl.map Prod.fst ++ done := by
  unfold switchPlain at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨cas, hc, h⟩ := h
  generalize hf : freshIds (2 * cas.length - 2 + 1) ((pl.map Prod.fst).take (2 * cas.length - 2))
    (2 * cas.length - 2) nex = fr at h
  obtain ⟨ids, nex2⟩ := fr
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨nb, nf, ids2, nout⟩, hs, b, hb, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨hle, new, eids, -, hnew⟩ := freshIds_spec _ _ _ _ _ _ hf
  have hc' : casesOf ((p0 :: pl).map plainCase) = some cas := hc
  obtain ⟨-, hsp⟩ := cases_spec hc'
  have hcas : ∀ x ∈ cas, PJ nex nex2 p0 pl x.hit ∧ PS p0 pl x.r := by
    intro x hx
    have hf2 := (hsp x.c x).mp ⟨hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf2)
    exact ⟨Or.inr (Or.inl ⟨t, ht, rfl⟩), Or.inr (List.mem_map_of_mem ht)⟩
  have hids : ∀ k ∈ ids, PRg nex nex2 pl k := by
    intro k hk
    rw [eids] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inr (hnew k hk)
    · exact Or.inl (List.mem_of_mem_take hk)
  obtain ⟨used, eu, fr, nodes, root⟩ := stree_shape _ _ (PJ nex nex2 p0 pl) (PS p0 pl) (Or.inl rfl)
    (Or.inr (Or.inr rfl)) fuel cas ids _ nb nf ids2 nout hs (fun k hk => Or.inl (hids k hk)) hcas
  have hus : ∀ k ∈ used, PRg nex nex2 pl k := fun k hk => hids k (by rw [eu]; exact List.mem_append_left _ hk)
  have hRo : ∀ k, PRg nex nex2 pl k → k ≠ o := by
    intro k hk e
    subst e
    rcases hk with h1 | h1
    · exact ho' h1
    · omega
  refine ⟨b, nb, nf, hb, ?_, root, fun k bk hk hbk => ?_, fun k hko hkR => ?_, fun k hk => ?_, hle, rfl⟩
  · rw [HoonMap.get_put, if_pos rfl]
    refine congrArg some (congrArg (fun B => (⟨b.par, B ++ nb, nf⟩ : Blob)) (List.filter_congr fun op _ => ?_))
    cases op <;> rfl
  · rw [HoonMap.get_put, if_neg (hRo k hk)] at hbk
    by_cases hku : k ∈ used
    · obtain ⟨b2, hb2, ok⟩ := nodes k hku
      rw [hb2] at hbk; cases hbk; exact ok
    · rw [fr k hku, get_foldl_del] at hbk
      split at hbk
      · cases hbk
      · rename_i hkp
        rcases hk with hk | hk
        · exact absurd hk hkp
        · rw [hab k hk.1] at hbk; cases hbk
  · have hku : k ∉ used := fun h => hkR (hus k h)
    rw [HoonMap.get_put, if_neg hko, fr k hku, get_foldl_del, if_neg (fun h => hkR (Or.inl h))]
  · have hko : k ≠ o := fun e => by omega
    have hkp : k ∉ pl.map Prod.fst := fun h => by have := hold k h; omega
    have hku : k ∉ used := fun h => by
      rcases hus k h with h1 | h1
      · exact hkp h1
      · omega
    rw [HoonMap.get_put, if_neg hko, fr k hku, get_foldl_del, if_neg hkp]
    exact hab k (by omega)

end Opt
end SkaModel
end Formalization
