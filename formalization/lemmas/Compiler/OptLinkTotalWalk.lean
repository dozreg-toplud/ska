import lemmas.Compiler.OptLinkTotalBlock
import lemmas.Ska.OptAliasWalk
import lemmas.Ska.OptAliasInv
import lemmas.Ska.OptAliasSSADead

/-!
# `+alias` returns: the walk invariant

The state of the walk of `+alias` after a prefix `pre` of `topo`, **`WInv`**:
* `rev`: `ARev` (`OptAliasWalk.lean`: every block `rev.gen` lists is a member
  of `topo` that jumps to the block, the lists have no duplicates, a listed
  walked block is reachable);
* `none`: an unwalked block has no facts yet;
* `drop`: a walked block still listed for an unwalked one has facts (it was
  kept: a dropped block deleted its edges);
* `old`: `old r ≠ r` only for a register written by a kept walked block;
* `kept`: a block with facts `i` (**`KeptOK`**) is reachable, has closed facts
  and immediates with facts, its new block has a fact for the test register,
  its jumps pass at least the arity of their target and have facts for the
  arguments, it jumps to every unwalked block that still lists it, and
  `i (old r)` is set for every `r` of `SqR` (a parameter, an argument of the
  entry that no block defines, or a register that every path from `0`
  defines in an earlier block) or written by its body, under the *current*
  `old`.

The last field stays true because `old` changes only at the registers a
later block writes, and by `DefOnceR` such a register is not defined on
every path to an earlier block (`later_dst`: the path would run through the
later block, which `TopoOK` puts after).  The input, **`WIn`**: `TopoOK`,
`RevSound`, `DefFirst`, `DefOnceR`, `NoLti`, `ArityOK`, `TwoNA`, `ReadsIn n`.
The step (**`winv_step`**) gives the hypotheses of `aliasBlock_some` at a kept
block (`readS`: every read of a reachable block is in `SqR` or written before,
from `ReadsIn` and `DefFirst`), and a dropped block returns by `TopoOK`.
**`aliasWalk_winv`** and **`aliasRetN_of`**: `AliasRetN` for a `pick` that
picks a member.  The decidable form of `WInv` is checked at every step of
the walk on the examples and on the 4,080 raw outputs of `enumX`
(`AuditOptTotal.lean`, `winvB`).
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-- The registers of a body's ops. -/
abbrev dsts (b : Blob) : List Nat := b.body.filterMap Opt.aliasDst

/-- The registers block `q` (block `bq`) reads with a fact: a parameter, an
argument of the entry that no block defines, or a register that every path
from `0` to `q` defines in an earlier block. -/
def SqR (n : Nat) (bl : Map Blob) (q : Nat) (bq : Blob) (r : Nat) : Prop :=
  r ∈ bq.par ∨ (r ∉ Opt.allDefs bl ∧ r < n) ∨
    (r ∈ Opt.allDefs bl ∧ ∀ p, Opt.BPath bl (q :: p) →
      ∃ o' ∈ p, ∃ b', HoonMap.get bl o' = some b' ∧ r ∈ Opt.blockDefs b')

/-- **A kept walked block** `q` with facts `i`. -/
structure KeptOK (n : Nat) (bl : Map Blob) (pre : List Nat) (g : Opt.AGen Map) (q : Nat) (i : Opt.AInfo) :
    Prop where
  reach : Opt.Reach bl q
  imms : ∃ m, g.imms q = some m ∧ AClo i ∧ IClo i m
  blk : ∃ bq pb, HoonMap.get bl q = some bq ∧ HoonMap.get g.new q = some pb ∧ TestFact pb.fin i ∧
    (∀ j ∈ Opt.getJmps pb.fin, ∀ bt, HoonMap.get bl j.there = some bt → bt.par.length ≤ j.args.length ∧
      ∀ k u, k < bt.par.length → j.args[k]? = some (some u) → (i u).isSome) ∧
    (∀ t, t ∉ pre → q ∈ g.rev t → ∃ j ∈ Opt.getJmps pb.fin, j.there = t) ∧
    (∀ r, SqR n bl q bq r ∨ r ∈ dsts bq → (i (g.old r)).isSome)

/-- **The walk invariant** after the prefix `pre` of `topo`. -/
structure WInv (n : Nat) (bl : Map Blob) (topo pre : List Nat) (g : Opt.AGen Map) : Prop where
  rev : Opt.ARev bl topo pre g
  none : ∀ t, t ∉ pre → g.info t = none
  drop : ∀ t q, t ∉ pre → q ∈ g.rev t → q ∈ pre → (g.info q).isSome
  old : ∀ r, g.old r ≠ r → ∃ q b, q ∈ pre ∧ (g.info q).isSome ∧ HoonMap.get bl q = some b ∧ r ∈ dsts b
  kept : ∀ q i, g.info q = some i → KeptOK n bl pre g q i

/-- **The input of the walk.** -/
structure WIn (n : Nat) (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Prop where
  tok : Opt.TopoOK bl topo
  rs : Opt.RevSound bl topo rev
  first : Opt.DefFirst bl
  once : Opt.DefOnceR bl
  nolti : Opt.NoLti bl
  arity : ArityOK bl
  two : TwoNA bl
  reads : ReadsIn n bl

/-! ## Registers and sites -/

theorem dst_allDefs {bl : Map Blob} {q r : Nat} {b : Blob} (hb : HoonMap.get bl q = some b) (h : r ∈ dsts b) :
    r ∈ Opt.allDefs bl := by
  unfold Opt.allDefs
  refine List.mem_flatMap.2 ⟨q, (Opt.MapKeys.mem_keys bl q).2 (by simp [hb]), ?_⟩
  simp only [hb, Option.map_some, Option.getD_some, Opt.blockDefs, List.mem_append]
  exact Or.inr h

theorem site_dst {bl : Map Blob} {q r : Nat} {b : Blob} (hb : HoonMap.get bl q = some b) (h : r ∈ dsts b) :
    ∃ i, Opt.DefSite bl r (q, some i) := by
  obtain ⟨op, hop, hd⟩ := List.mem_filterMap.1 h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hop
  exact ⟨i, b, op, hb, hi, hd⟩

theorem site_defs {bl : Map Blob} {q r : Nat} {b : Blob} (hb : HoonMap.get bl q = some b)
    (h : r ∈ Opt.blockDefs b) : ∃ s, Opt.DefSite bl r (q, s) := by
  rcases List.mem_append.1 h with h | h
  · exact ⟨none, b, hb, h⟩
  · obtain ⟨i, hi⟩ := site_dst hb h; exact ⟨some i, hi⟩

theorem nodup_filterMap_idx {f : Pole → Option Nat} : ∀ (l : List Pole),
    (∀ (i j : Nat) (a b : Pole) (r : Nat), l[i]? = some a → l[j]? = some b → f a = some r → f b = some r → i = j) →
    (l.filterMap f).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    have ih := nodup_filterMap_idx l fun i j a b r ha hb hfa hfb => by
      have := h (i + 1) (j + 1) a b r (by simpa using ha) (by simpa using hb) hfa hfb
      omega
    rw [List.filterMap_cons]
    cases e : f x with
    | none => exact ih
    | some d =>
      refine List.nodup_cons.2 ⟨fun hd => ?_, ih⟩
      obtain ⟨op, hop, hd'⟩ := List.mem_filterMap.1 hd
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hop
      have := h 0 (j + 1) x op d rfl (by simpa using hj) e hd'
      omega

theorem dsts_nodup {bl : Map Blob} {o : Nat} {b : Blob} (hD : Opt.DefOnceR bl) (hR : Opt.Reach bl o)
    (hb : HoonMap.get bl o = some b) : (dsts b).Nodup := by
  refine nodup_filterMap_idx b.body fun i j a a' r ha ha' hfa hfa' => ?_
  have := hD r (o, some i) (o, some j) hR ⟨b, a, hb, ha, hfa⟩ hR ⟨b, a', hb, ha', hfa'⟩
  simpa using this

theorem idx_lt_pre {pre l : List Nat} {q : Nat} (h : q ∈ pre) : (pre ++ l).idxOf q < pre.length := by
  induction pre with
  | nil => cases h
  | cons a pre ih =>
    by_cases e : a = q
    · subst e; simp [List.idxOf_cons]
    · have h' : q ∈ pre := (List.mem_cons.1 h).resolve_left (Ne.symm e)
      have := ih h'
      simp only [List.cons_append, List.idxOf_cons, List.length_cons]
      have : (a == q) = false := by simpa using e
      rw [this]; simp only [cond_false]; omega

/-- **Every read of a reachable block** is in `SqR` or written before it in
the block (`ReadsIn` and `DefFirst`). -/
theorem readS {n : Nat} {bl : Map Blob} {o i r : Nat} {b : Blob} (hR : ReadsIn n bl) (hF : Opt.DefFirst bl)
    (ho : Opt.Reach bl o) (hb : HoonMap.get bl o = some b) (h : Opt.ReadAt b i r) :
    SqR n bl o b r ∨ r ∈ (b.body.take i).filterMap Opt.aliasDst := by
  by_cases hd : r ∈ Opt.allDefs bl
  · by_cases hp : r ∈ b.par
    · exact Or.inl (Or.inl hp)
    · by_cases ht : r ∈ (b.body.take i).filterMap Opt.aliasDst
      · exact Or.inr ht
      · refine Or.inl (Or.inr (Or.inr ⟨hd, fun p hp' => ?_⟩))
        rcases hF o p b hp' hb i r h hd with h1 | h1 | h1
        · exact absurd h1 hp
        · exact absurd h1 ht
        · exact h1
  · exact Or.inl (Or.inr (Or.inl ⟨hd, (hR o b i r ho hb h).resolve_left hd⟩))

/-- **A register a later block writes** is not one an earlier kept block
reads with a fact or writes. -/
theorem later_dst {n : Nat} {bl : Map Blob} {pre l : List Nat} {o q r : Nat} {b bq : Blob}
    (ht : Opt.TopoOK bl (pre ++ o :: l)) (hD : Opt.DefOnceR bl) (hop : o ∉ pre) (hoR : Opt.Reach bl o)
    (hb : HoonMap.get bl o = some b) (hr : r ∈ dsts b) (hq : q ∈ pre) (hqR : Opt.Reach bl q)
    (hbq : HoonMap.get bl q = some bq) (h : SqR n bl q bq r ∨ r ∈ dsts bq) : False := by
  obtain ⟨i, hsi⟩ := site_dst hb hr
  have hqo : q ≠ o := fun e => hop (e ▸ hq)
  rcases h with (h | ⟨h, -⟩ | ⟨-, h⟩) | h
  · have := hD r (q, none) (o, some i) hqR ⟨bq, hbq, h⟩ hoR hsi
    simp at this
  · exact h (dst_allDefs hb hr)
  · obtain ⟨p, hp⟩ := Opt.awi_reach_bpath hqR
    obtain ⟨o', ho', b', hb', hr'⟩ := h p hp
    obtain ⟨s, hs⟩ := site_defs hb' hr'
    have hR' := Opt.ssk_bpath_reach hp o' (List.mem_cons_of_mem _ ho')
    have e := hD r (o', s) (o, some i) hR' hs hoR hsi
    simp only [Prod.mk.injEq] at e
    rw [e.1] at ho'
    have h1 := (Opt.awi_bpath_idx ht hp rfl).2 o ho'
    have h2 : (pre ++ o :: l).idxOf o = pre.length := Opt.idxOf_pre hop
    have h3 := idx_lt_pre (l := o :: l) hq
    omega
  · obtain ⟨i', hsq⟩ := site_dst hbq h
    have := hD r (q, some i') (o, some i) hqR hsq hoR hsi
    simp only [Prod.mk.injEq] at this
    exact hqo this.1

/-! ## The end -/

theorem afold_walk {rev : Nat → List Nat} {o : Nat} (hn : ∀ o', (rev o').Nodup) (go cut t : Nat)
    (ht : t = go ∨ t = cut) (hm : o ∈ (Opt.aliasFold rev o go cut).2.1 t) :
    ∃ j' ∈ Opt.getJmps (Opt.aliasFold rev o go cut).1, j'.there = t := by
  have hj : Opt.getJmps (Opt.aliasFold rev o go cut).1 = [{ args := [], there := go }] := rfl
  rw [hj]
  by_cases e : t = go
  · exact ⟨_, List.mem_singleton_self _, e.symm⟩
  · have ec : t = cut := ht.resolve_left e
    subst ec
    have : go ≠ t := fun h => e h.symm
    simp only [Opt.aliasFold, if_neg this] at hm
    exact absurd hm (Opt.awr_del_gone hn)

theorem afold_args {rev : Nat → List Nat} {o go cut : Nat} :
    ∀ j' ∈ Opt.getJmps (Opt.aliasFold rev o go cut).1, ∀ u, some u ∉ j'.args := by
  intro j' hj u hu
  have hj' : Opt.getJmps (Opt.aliasFold rev o go cut).1 = [{ args := [], there := go }] := rfl
  rw [hj'] at hj
  rw [List.mem_singleton.1 hj] at hu
  cases hu

/-- **The end `+alias` makes, for the walk**: a fact for the test register,
arguments renamed from the old end's reads, and a jump to every block that
still lists it. -/
theorem afin_walk {old : Nat → Nat} {loc : Opt.AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat}
    {fin : Termin} {rf : Termin × (Nat → List Nat) × Bool} (h : Opt.aliasFin old loc rev f o fin = some rf)
    (hn : ∀ o', (rev o').Nodup) (hl : ∀ n s z o', fin ≠ Termin.lti n s z o') :
    TestFact rf.1 loc ∧ (∀ j' ∈ Opt.getJmps rf.1, ∀ u, some u ∈ j'.args → ∃ a ∈ Opt.finRegs fin, u = old a) ∧
    (∀ t, o ∈ rf.2.1 t → (∃ j ∈ Opt.getJmps fin, j.there = t) → ∃ j' ∈ Opt.getJmps rf.1, j'.there = t) := by
  -- the folds
  have F : ∀ (z o' : Jmp) go cut, ((go = z.there ∧ cut = o'.there) ∨ (go = o'.there ∧ cut = z.there)) →
      rf = Opt.aliasFold rev o go cut →
      TestFact rf.1 loc ∧ (∀ j' ∈ Opt.getJmps rf.1, ∀ u, some u ∈ j'.args → ∃ a ∈ Opt.finRegs fin, u = old a) ∧
      (∀ t, o ∈ rf.2.1 t → (∃ j ∈ [z, o'], j.there = t) → ∃ j' ∈ Opt.getJmps rf.1, j'.there = t) := by
    intro z o' go cut hgc e
    subst e
    refine ⟨trivial, fun j' hj u hu => absurd hu (afold_args j' hj u), fun t hm ⟨j, hj, hjt⟩ => ?_⟩
    refine afold_walk hn go cut t ?_ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> rcases hgc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (hjt.symm.trans e1.symm)
    · exact Or.inr (hjt.symm.trans e2.symm)
    · exact Or.inr (hjt.symm.trans e2.symm)
    · exact Or.inl (hjt.symm.trans e1.symm)
  -- a two-way end kept: no arguments, the same targets, `rev` unchanged
  have K : ∀ (z o' : Jmp), z.args = [] → o'.args = [] → ∀ fin', Opt.getJmps fin' = [z, o'] →
      rf = (fin', rev, f) ∨ rf = (fin', rev, true) →
      (∀ j' ∈ Opt.getJmps rf.1, ∀ u, some u ∈ j'.args → ∃ a ∈ Opt.finRegs fin, u = old a) ∧
      (∀ t, o ∈ rf.2.1 t → (∃ j ∈ [z, o'], j.there = t) → ∃ j' ∈ Opt.getJmps rf.1, j'.there = t) := by
    intro z o' hz ho fin' hj e
    have e1 : rf.1 = fin' := by rcases e with rfl | rfl <;> rfl
    rw [e1, hj]
    refine ⟨fun j' hj' u hu => ?_, fun t _ hj' => hj'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl
    · rw [hz] at hu; cases hu
    · rw [ho] at hu; cases hu
  cases fin with
  | clq s z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · rw [if_pos ha] at h; cases h
    · rw [if_neg ha] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      obtain ⟨ic, hic, hrf⟩ := Option.map_eq_some_iff.mp h
      by_cases c1 : (ic.isCell || ic.cellImm) = true
      · rw [if_pos c1] at hrf
        exact F z o' _ _ (Or.inl ⟨rfl, rfl⟩) hrf.symm
      · rw [if_neg c1] at hrf
        by_cases c2 : (ic.isLoob || ic.atomImm) = true
        · rw [if_pos c2] at hrf
          exact F z o' _ _ (Or.inr ⟨rfl, rfl⟩) hrf.symm
        · rw [if_neg c2] at hrf
          subst hrf
          obtain ⟨k1, k2⟩ := K z o' hz ho (Termin.clq (old s) z o') rfl (Or.inl rfl)
          exact ⟨by simp [TestFact, hic], k1, k2⟩
  | eqq l r z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · rw [if_pos ha] at h; cases h
    · rw [if_neg ha] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      by_cases c : old l ≠ old r
      · rw [if_pos c, Option.some.injEq] at h
        subst h
        obtain ⟨k1, k2⟩ := K z o' hz ho (Termin.eqq (old l) (old r) z o') rfl (Or.inl rfl)
        exact ⟨trivial, k1, k2⟩
      · rw [if_neg c, Option.some.injEq] at h
        exact F z o' _ _ (Or.inl ⟨rfl, rfl⟩) h.symm
  | brn s z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · rw [if_pos ha] at h; cases h
    · rw [if_neg ha] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      obtain ⟨ic, hic, hrf⟩ := Option.map_eq_some_iff.mp h
      split at hrf
      · split at hrf
        · subst hrf
          obtain ⟨k1, k2⟩ := K z o' hz ho (Termin.brz (old s) z o') rfl (Or.inr rfl)
          exact ⟨by simp [TestFact, hic], k1, k2⟩
        · subst hrf
          obtain ⟨k1, k2⟩ := K z o' hz ho (Termin.brn (old s) z o') rfl (Or.inl rfl)
          exact ⟨by simp [TestFact, hic], k1, k2⟩
      · exact F z o' _ _ (Or.inl ⟨rfl, rfl⟩) hrf.symm
      · exact F z o' _ _ (Or.inr ⟨rfl, rfl⟩) hrf.symm
      · subst hrf
        refine ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t hm ⟨j, hj, hjt⟩ => ?_⟩
        exfalso
        have hn1 := Opt.awr_del_nodup (k := o'.there) (o := o) hn
        simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · subst hjt; exact Opt.awr_del_gone hn1 hm
        · subst hjt; exact Opt.awr_del_gone hn (Opt.awr_del_sub hm)
  | brz s z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · rw [if_pos ha] at h; cases h
    · rw [if_neg ha] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      obtain ⟨ic, hic, hrf⟩ := Option.map_eq_some_iff.mp h
      split at hrf
      · subst hrf
        obtain ⟨k1, k2⟩ := K z o' hz ho (Termin.brz (old s) z o') rfl (Or.inl rfl)
        exact ⟨by simp [TestFact, hic], k1, k2⟩
      · exact F z o' _ _ (Or.inl ⟨rfl, rfl⟩) hrf.symm
      · exact F z o' _ _ (Or.inr ⟨rfl, rfl⟩) hrf.symm
  | hop t =>
    simp only [Opt.aliasFin, Option.some.injEq] at h
    subst h
    refine ⟨trivial, fun j' hj' u hu => ?_, fun t' _ ⟨j, hj, hjt⟩ => ?_⟩
    · simp only [Opt.getJmps, List.mem_singleton] at hj'
      subst hj'
      obtain ⟨x, hx, hxu⟩ := List.mem_map.1 hu
      cases x with
      | none => cases hxu
      | some a =>
        simp only [Option.map_some, Option.some.injEq] at hxu
        exact ⟨a, by simp [Opt.finRegs, Opt.jmpRegs]; exact hx, hxu.symm⟩
    · simp only [Opt.getJmps, List.mem_singleton] at hj
      subst hj
      exact ⟨_, List.mem_singleton_self _, hjt⟩
  | lti n s z o' => exact absurd rfl (hl n s z o')
  | jmp a v =>
    simp only [Opt.aliasFin, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t _ ⟨j, hj, _⟩ => by simp [Opt.getJmps] at hj⟩
  | jmf a v k =>
    simp only [Opt.aliasFin, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t _ ⟨j, hj, _⟩ => by simp [Opt.getJmps] at hj⟩
  | jsp a s =>
    simp only [Opt.aliasFin, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t _ ⟨j, hj, _⟩ => by simp [Opt.getJmps] at hj⟩
  | jsf a s k =>
    simp only [Opt.aliasFin, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t _ ⟨j, hj, _⟩ => by simp [Opt.getJmps] at hj⟩
  | don s =>
    simp only [Opt.aliasFin, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t _ ⟨j, hj, _⟩ => by simp [Opt.getJmps] at hj⟩
  | bom u =>
    simp only [Opt.aliasFin, Option.some.injEq] at h; subst h
    exact ⟨trivial, fun j' hj' => by simp [Opt.getJmps] at hj', fun t _ ⟨j, hj, _⟩ => by simp [Opt.getJmps] at hj⟩

end Compiler
end Formalization
