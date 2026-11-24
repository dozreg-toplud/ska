import lemmas.Ska.OptSwitchSimG
import lemmas.Ska.OptSwitchMulti

/-!
# `+switch-chains`: the plain chain, its walk and its tree

Toward one plain chain keeping the code (through `region_keepsG` of
`OptSwitchSimG.lean`).  A plain chain `(o, t0) :: pl` (`plainsOf`) tests one
register `d` against constants: the head `o` puts `c0` in `r0` somewhere in
its body and ends in an `%eqq` of `d` and `r0` to `hit0` and to the label of
the next test; each next test is a block with no parameters, the body
`[%imm c r]` and an `%eqq` of `d` and `r` to its hit and to the next label,
the last one's no side being the final miss (`PlainBlocks`).  For example on
`pla5` of `switchcheck.hoon` (dumped before and after the pass, 2026-11-24)
the head is block `0` with body `[%imm 9 r15]` and end `%eqq r15 r0` to `30`
and `32`, and the tests after it are `32`, `25`, `18`, `11` (constants 3, 7,
1, 5), the final miss `1`; after the pass block `0` has body `[]` (the
`filter` dropped the `%imm`) and end `%lti 5 r0` to `36` and `35`, and the
other nodes sit at `36`, `35`, `34`, `33` (from `nex = 33`) and at the old
labels `32`, `25`, `18`, `11`, as `switchPlain` computes.

* `plain_walk`: the code before, from the start of a test of the chain after
  the head, runs to `plainTarget` (the hit of the first test whose constant is
  the value of `d`, else the final miss), changing only the test registers.
* `plain_tree`: after `switchPlain`, the head's block is its parameters, its
  body without the `%imm` ops into `r0`, then the root's ops and end; the tree
  from the root takes `plainTarget` on every value of `d`; no other label
  changes but those of the chain after the head and those from `nex` up.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- The case a plain test makes. -/
def plainCase (t : Nat × SPlain) : SCase := ⟨t.2.c, t.2.hit, t.2.r⟩

/-- The target of a plain chain at the value `v` of its register. -/
def plainTarget (ps : List (Nat × SPlain)) (mis : Nat) (v : Noun) : Nat := pickHit (ps.map plainCase) mis v

theorem plainTarget_cons (t : Nat × SPlain) (rest : List (Nat × SPlain)) (mis : Nat) (v : Noun) :
    plainTarget (t :: rest) mis v = if v = A t.2.c then t.2.hit else plainTarget rest mis v := by
  unfold plainTarget pickHit
  by_cases e : v = A t.2.c <;> simp [List.find?_cons, e, plainCase]

theorem plainTarget_mem (ps : List (Nat × SPlain)) (mis : Nat) (v : Noun) :
    plainTarget ps mis v = mis ∨ ∃ t ∈ ps, plainTarget ps mis v = t.2.hit := by
  unfold plainTarget pickHit
  cases e : (ps.map plainCase).find? (fun x => decide (v = A x.c)) with
  | none => exact Or.inl rfl
  | some x =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some e)
    exact Or.inr ⟨t, ht, rfl⟩

/-- The registers the tests of a plain chain set. -/
def plainRegs (ps : List (Nat × SPlain)) : List Nat := ps.map fun t => t.2.r

/-- The final miss of a plain chain. -/
def plainMiss (p0 : Nat × SPlain) (pl : List (Nat × SPlain)) : Nat := ((p0 :: pl).getLast (List.cons_ne_nil _ _)).2.miss

/-- The blocks of the tests of a plain chain after its head. -/
def PlainBlocks (M : Map Blob) (d mis : Nat) : List (Nat × SPlain) → Prop
  | [] => False
  | t :: rest => t.2.r ≠ d ∧
      (∃ l r, HoonMap.get M t.1 = some ⟨[], [Pole.imm (A t.2.c) t.2.r], Termin.eqq l r ⟨[], t.2.hit⟩ ⟨[], t.2.miss⟩⟩ ∧
        ((l = d ∧ r = t.2.r) ∨ (l = t.2.r ∧ r = d))) ∧
      (match rest with
       | [] => t.2.miss = mis
       | t2 :: _ => t.2.miss = t2.1) ∧
      (rest ≠ [] → PlainBlocks M d mis rest)

/-- The jump of an `%eqq` of `d` and `r` (in either order) when `r` holds
`A c`. -/
theorem taken_eqq_plain {l r d rr : Nat} {regs : Map (Option Noun)} {v : Noun} {c hit mis : Nat}
    (hlr : (l = d ∧ r = rr) ∨ (l = rr ∧ r = d)) (hv : read d regs = some v) (hc : read rr regs = some (A c)) :
    taken regs (Termin.eqq l r ⟨[], hit⟩ ⟨[], mis⟩) = some (if v = A c then ⟨[], hit⟩ else ⟨[], mis⟩) := by
  rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [taken, hv, hc]
  · simp only [taken, hv, hc, Option.bind_some, Option.map_some]
    by_cases e : v = A c
    · simp [e]
    · simp [e, Ne.symm e]

section
variable {σ : Type}

/-- **The code before walks the plain chain** from the start of a test after
the head. -/
theorem plain_walk (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (d mis : Nat)
    (hm : (HoonMap.get c.blocks mis).isSome) :
    ∀ (ps : List (Nat × SPlain)) (q : Nat) (bq : Blob) (regs : Map (Option Noun)) (t : Trace) (st : σ) (v : Noun),
      PlainBlocks c.blocks d mis ps → (∀ p ∈ ps, (HoonMap.get c.blocks p.2.hit).isSome) →
      ps.head?.map Prod.fst = some q → HoonMap.get c.blocks q = some bq → Reach c.blocks q →
      read d regs = some v →
      ∃ es R' bT, HoonMap.get c.blocks (plainTarget ps mis v) = some bT ∧
        Steps lib O c gul ⟨q, bq, [], regs, t, st⟩ es ⟨plainTarget ps mis v, bT, [], R', t, st⟩ ∧
        Reach c.blocks (plainTarget ps mis v) ∧ ∀ k, k ∉ plainRegs ps → HoonMap.get R' k = HoonMap.get regs k
  | [], _, _, _, _, _, _, hb, _, _, _, _, _ => absurd hb id
  | p :: rest, q, bq, regs, t, st, v, hb, hhit, hq, hbq, hreach, hv => by
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hq
    subst hq
    obtain ⟨hrd, ⟨l, r, hby, hlr⟩, hnext, hrest⟩ := hb
    rw [hby] at hbq; cases hbq
    have hregs : ∀ k, k ∉ plainRegs (p :: rest) → k ≠ p.2.r ∧ k ∉ plainRegs rest := by
      intro k hk
      simp only [plainRegs, List.map_cons, List.mem_cons, not_or] at hk
      exact ⟨hk.1, hk.2⟩
    have s1 := Step.op (lib := lib) (O := O) (c := c) (gul := gul)
      (x := ⟨p.1, ⟨[], [Pole.imm (A p.2.c) p.2.r], Termin.eqq l r ⟨[], p.2.hit⟩ ⟨[], p.2.miss⟩⟩, [], regs, t, st⟩)
      rfl rfl rfl (execPole_imm lib O gul st (A p.2.c) p.2.r regs t)
    have hv1 : read d (store p.2.r (A p.2.c) regs) = some v := by rw [read_store_other (Ne.symm hrd)]; exact hv
    have htk := taken_eqq_plain (hit := p.2.hit) (mis := p.2.miss) hlr hv1 (read_store_self _ _ _)
    have hjm : ∀ j, j = (if v = A p.2.c then (⟨[], p.2.hit⟩ : Jmp) else ⟨[], p.2.miss⟩) →
        j ∈ getJmps (Termin.eqq l r ⟨[], p.2.hit⟩ ⟨[], p.2.miss⟩) := by
      intro j hj; subst hj; split <;> simp [getJmps]
    by_cases e : v = A p.2.c
    · rw [if_pos e] at htk
      obtain ⟨bh, hbh⟩ := Option.isSome_iff_exists.mp (hhit p List.mem_cons_self)
      have tgt : plainTarget (p :: rest) mis v = p.2.hit := by rw [plainTarget_cons, if_pos e]
      rw [tgt]
      refine ⟨_, _, bh, hbh, Steps.step s1 (Steps.step (Step.jump rfl rfl rfl htk hbh) (Steps.refl _)),
        Reach.jump (j := ⟨[], p.2.hit⟩) hreach hby (by simp [getJmps]), fun k hk => ?_⟩
      exact get_store_ne (hregs k hk).1 _ _
    · rw [if_neg e] at htk
      have tgt : plainTarget (p :: rest) mis v = plainTarget rest mis v := by rw [plainTarget_cons, if_neg e]
      rw [tgt]
      have hrm : Reach c.blocks p.2.miss := Reach.jump (j := ⟨[], p.2.miss⟩) hreach hby (by simp [getJmps])
      cases rest with
      | nil =>
        simp only at hnext
        subst hnext
        obtain ⟨bm, hbm⟩ := Option.isSome_iff_exists.mp hm
        exact ⟨_, _, bm, hbm, Steps.step s1 (Steps.step (Step.jump rfl rfl rfl htk hbm) (Steps.refl _)), hrm,
          fun k hk => get_store_ne (hregs k hk).1 _ _⟩
      | cons p2 rest2 =>
        simp only at hnext
        have hb2 := hrest (List.cons_ne_nil _ _)
        obtain ⟨-, ⟨l2, r2, hby2, -⟩, -, -⟩ := hb2
        have hrm2 : Reach c.blocks p2.1 := by rw [← hnext]; exact hrm
        obtain ⟨es, R', bT, hbT, hsT, hrT, hfr⟩ := plain_walk lib O c gul d mis hm (p2 :: rest2) p2.1 _
          (store p.2.r (A p.2.c) regs) t st v (hrest (List.cons_ne_nil _ _))
          (fun u hu => hhit u (List.mem_cons_of_mem _ hu)) rfl hby2 hrm2 hv1
        have hby2' : HoonMap.get c.blocks p.2.miss = some ⟨[], [Pole.imm (A p2.2.c) p2.2.r],
            Termin.eqq l2 r2 ⟨[], p2.2.hit⟩ ⟨[], p2.2.miss⟩⟩ := by rw [hnext]; exact hby2
        have hsT' : Steps lib O c gul ⟨p.2.miss, ⟨[], [Pole.imm (A p2.2.c) p2.2.r],
            Termin.eqq l2 r2 ⟨[], p2.2.hit⟩ ⟨[], p2.2.miss⟩⟩, [], store p.2.r (A p.2.c) regs, t, st⟩ es
            ⟨plainTarget (p2 :: rest2) mis v, bT, [], R', t, st⟩ := by rw [hnext]; exact hsT
        refine ⟨_, R', bT, hbT, Steps.step s1 (Steps.step (Step.jump rfl rfl rfl htk hby2') hsT'), hrT,
          fun k hk => ?_⟩
        rw [hfr k (hregs k hk).2]
        exact get_store_ne (hregs k hk).1 _ _

end

/-- The `filter` of `switchPlain`: an `%imm` into `r` is dropped. -/
def plainKeep (r : Nat) (op : Pole) : Bool :=
  match op with
  | Pole.imm _ dd => !(decide (dd = r))
  | _ => true

/-- **The plain chain against its tree**: after `switchPlain`, the head's
block is its parameters, its body without the `%imm` ops into `r0`, then the
root's ops and end; the tree takes the target of the chain on every value of
`d`; no label changes but the head, the labels of the tests after it and those
from `nex` up.  Given distinct labels of the tests after the head, below `nex`
as the head is, and test registers other than `d`. -/
theorem plain_tree {bl out out' : Map Blob} {fuel o nex nex' : Nat} {p0 : Nat × SPlain}
    {pl : List (Nat × SPlain)} {done done' : List Nat}
    (h : switchPlain bl out fuel o (p0 :: pl) done nex = some (out', done', nex'))
    (hnd : (pl.map Prod.fst).Nodup) (hold : ∀ k ∈ pl.map Prod.fst, k < nex) (ho : o < nex)
    (ho' : o ∉ pl.map Prod.fst) (hr : ∀ t ∈ p0 :: pl, t.2.r ≠ p0.2.d) :
    ∃ b nb nf, HoonMap.get bl o = some b ∧
      HoonMap.get out' o = some ⟨b.par, b.body.filter (plainKeep p0.2.r) ++ nb, nf⟩ ∧
      (∀ v, treeGo out' p0.2.d (plainRegs (p0 :: pl)) v fuel ⟨[], nb, nf⟩ =
        some (plainTarget (p0 :: pl) (plainMiss p0 pl) v)) ∧
      (∀ k, k ≠ o → k ∉ pl.map Prod.fst → k < nex → HoonMap.get out' k = HoonMap.get out k) ∧
      nex ≤ nex' ∧ done' = pl.map Prod.fst ++ done := by
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
  obtain ⟨hle, new, eids, hnnd, hnew⟩ := freshIds_spec _ _ _ _ _ _ hf
  have hc' : casesOf ((p0 :: pl).map plainCase) = some cas := hc
  obtain ⟨hpw, hsp⟩ := cases_spec hc'
  have hrc : ∀ x ∈ cas, x.r ≠ p0.2.d ∧ x.r ∈ plainRegs (p0 :: pl) := by
    intro x hx
    have hf2 := (hsp x.c x).mp ⟨hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf2)
    exact ⟨hr t ht, List.mem_map_of_mem ht⟩
  have hids : ∀ k ∈ ids, (nex ≤ k) ∨ k ∈ pl.map Prod.fst := by
    intro k hk
    rw [eids] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (hnew k hk).1
    · exact Or.inr (List.mem_of_mem_take hk)
  have hnd2 : ids.Nodup := by
    rw [eids]
    refine List.nodup_append.mpr ⟨hnnd, hnd.sublist (List.take_sublist _ _), fun a ha b hb e => ?_⟩
    have h1 := (hnew a ha).1
    have h2 := hold b (List.mem_of_mem_take hb)
    omega
  obtain ⟨used, eu, fr, go⟩ := stree_go _ _ _ fuel cas _ _ nb nf ids2 nout hs hpw hrc hnd2
  have hus : ∀ k ∈ used, (nex ≤ k) ∨ k ∈ pl.map Prod.fst := fun k hk =>
    hids k (by rw [eu]; exact List.mem_append_left _ hk)
  have huo : ∀ k ∈ used, k ≠ o := by
    intro k hk e
    subst e
    rcases hus k hk with h1 | h1
    · omega
    · exact ho' h1
  refine ⟨b, nb, nf, hb, ?_, fun v => ?_, fun k k1 k2 k3 => ?_, hle, rfl⟩
  · rw [HoonMap.get_put, if_pos rfl]
    refine congrArg some (congrArg (fun B => (⟨b.par, B ++ nb, nf⟩ : Blob)) (List.filter_congr fun op _ => ?_))
    cases op <;> rfl
  · rw [go _ (fun k hk => ?_) v, pickHit_cases hc']
    · rfl
    · rw [HoonMap.get_put, if_neg (huo k hk)]
  · have k4 : k ∉ used := fun hk => by
      rcases hus k hk with h1 | h1
      · omega
      · exact k2 h1
    rw [HoonMap.get_put, if_neg k1, fr k k4, get_foldl_del]
    simp only [k2, if_false]

/-- The labels inside a plain chain's region: the tests after the head, and
every label from `nex` up. -/
def PlainIn (nex : Nat) (pl : List (Nat × SPlain)) (k : Nat) : Prop := k ∈ pl.map Prod.fst ∨ nex ≤ k

/-- The ops the pass drops at the head `o`, and the ops it appends there. -/
def plainD (o r : Nat) (k : Nat) (p : Pole) : Bool := decide (k = o) && !plainKeep r p
def plainE (o : Nat) (nb : List Pole) (k : Nat) : List Pole := if k = o then nb else []

/-- **What one application of `switchPlain` at `o` needs of the chain**, all
of it about the blocks before. -/
structure PlainHyp (M : Map Blob) (o nex : Nat) (p0 : Nat × SPlain) (pl : List (Nat × SPlain)) : Prop where
  nd : (pl.map Prod.fst).Nodup
  old : ∀ k ∈ pl.map Prod.fst, k < nex
  ho : o < nex
  ho' : o ∉ pl.map Prod.fst
  hr : ∀ t ∈ p0 :: pl, t.2.r ≠ p0.2.d
  blocks : PlainBlocks M p0.2.d (plainMiss p0 pl) pl
  miss0 : ∃ t1 rest, pl = t1 :: rest ∧ p0.2.miss = t1.1
  headB : ∃ b l r, HoonMap.get M o = some b ∧ b.fin = Termin.eqq l r ⟨[], p0.2.hit⟩ ⟨[], p0.2.miss⟩ ∧
    ((l = p0.2.d ∧ r = p0.2.r) ∨ (l = p0.2.r ∧ r = p0.2.d)) ∧ Pole.imm (A p0.2.c) p0.2.r ∈ b.body ∧
    (∀ n n', Pole.imm n p0.2.r ∈ b.body → Pole.imm n' p0.2.r ∈ b.body → n = n') ∧
    (∀ r ∈ b.par, r ∉ plainRegs (p0 :: pl)) ∧
    (∀ p ∈ b.body, plainKeep p0.2.r p = true → ∀ r ∈ poleRegs p, r ∉ plainRegs (p0 :: pl))
  hits : ∀ t ∈ p0 :: pl, (HoonMap.get M t.2.hit).isSome ∧ ¬ PlainIn nex pl t.2.hit ∧ t.2.hit ≠ o
  miss : (HoonMap.get M (plainMiss p0 pl)).isSome ∧ ¬ PlainIn nex pl (plainMiss p0 pl) ∧ plainMiss p0 pl ≠ o
  noI : ∀ k b j, Reach M k → ¬ PlainIn nex pl k → k ≠ o → HoonMap.get M k = some b → j ∈ getJmps b.fin →
    ¬ PlainIn nex pl j.there
  ment : ∀ k b, Reach M k → ¬ PlainIn nex pl k → k ≠ o → HoonMap.get M k = some b → ∀ r ∈ blobMentions b,
    r ∉ plainRegs (p0 :: pl)
  zero : ¬ PlainIn nex pl 0

theorem plainD_off {o r k : Nat} (h : k ≠ o) (p : Pole) : plainD o r k p = false := by simp [plainD, h]

theorem gBody_plain (o r : Nat) (nb B : List Pole) :
    gBody (plainD o r) (plainE o nb) o B = B.filter (plainKeep r) ++ nb := by
  simp only [gBody, plainE, if_pos rfl]
  congr 1
  exact List.filter_congr fun p _ => by simp [plainD]

theorem plainRegs_head (p0 : Nat × SPlain) (pl : List (Nat × SPlain)) : p0.2.r ∈ plainRegs (p0 :: pl) := by
  simp [plainRegs]

section
variable {M out' : Map Blob} {o nex : Nat} {p0 : Nat × SPlain} {pl : List (Nat × SPlain)} {b : Blob}
  {nb : List Pole} {nf : Termin}

/-- The region of one plain chain. -/
theorem plain_region (H : PlainHyp M o nex p0 pl) (hb : HoonMap.get M o = some b)
    (hbo : HoonMap.get out' o = some ⟨b.par, b.body.filter (plainKeep p0.2.r) ++ nb, nf⟩)
    (hfr : ∀ k, k ≠ o → k ∉ pl.map Prod.fst → k < nex → HoonMap.get out' k = HoonMap.get M k) :
    RegionHypG M out' (PlainIn nex pl) (· = o) (fun k => k ∈ plainRegs (p0 :: pl)) (plainD o p0.2.r)
      (plainE o nb) := by
  obtain ⟨b1, l, r, hb1, -, -, -, hU, hpar, hkept⟩ := H.headB
  rw [hb] at hb1; cases hb1
  have hnI : ∀ k, ¬ PlainIn nex pl k → k ∉ pl.map Prod.fst ∧ k < nex := fun k hk =>
    ⟨fun h => hk (Or.inl h), Nat.lt_of_not_le fun h => hk (Or.inr h)⟩
  refine ⟨fun k hk hh => ?_, fun k hk => ?_, fun k hk => ⟨plainD_off hk, by simp [plainE, hk]⟩,
    fun k p hd => ?_, fun k b2 hh hb2 n r2 n' h1 h2 hd1 hd2 => ?_,
    fun k b2 j hr hk hh hb2 hj => H.noI k b2 j hr hk hh hb2 hj,
    fun k b2 hr hk hh hb2 r2 hm => H.ment k b2 hr hk hh hb2 r2 hm,
    fun k b2 hr hh hb2 => ?_, H.zero⟩
  · exact hfr k hh (hnI k hk).1 (hnI k hk).2
  · subst hk
    refine ⟨fun h => h.elim H.ho' (fun h' => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le H.ho h')), b, _, hb, hbo, rfl, ?_⟩
    rw [gBody_plain]
  · simp only [plainD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hd
    obtain ⟨-, hk⟩ := hd
    cases p with
    | imm n dd =>
      simp only [plainKeep, Bool.not_eq_false', decide_eq_true_eq] at hk
      exact ⟨n, dd, rfl, by rw [hk]; exact plainRegs_head p0 pl⟩
    | _ => simp [plainKeep] at hk
  · subst hh
    rw [hb] at hb2; cases hb2
    simp only [plainD, decide_true, Bool.true_and, plainKeep, Bool.not_not, decide_eq_true_eq] at hd1 hd2
    subst hd1
    exact hU n n' h1 h2
  · subst hh
    rw [hb] at hb2; cases hb2
    refine ⟨hpar, fun p hp hd r2 hr2 => hkept p hp ?_ r2 hr2⟩
    simp only [plainD, decide_true, Bool.true_and, Bool.not_eq_false'] at hd
    exact hd

end

/-- **The macro step at the head of a plain chain.** -/
theorem plain_head {σ : Type} (lib : Lib) (O : Oracle σ) (gul : Noun) (c : Straight Map) {out' : Map Blob}
    {o nex fuel : Nat} {p0 : Nat × SPlain} {pl : List (Nat × SPlain)} {b : Blob} {nb : List Pole} {nf : Termin}
    (H : PlainHyp c.blocks o nex p0 pl) (hb : HoonMap.get c.blocks o = some b)
    (hbo : HoonMap.get out' o = some ⟨b.par, b.body.filter (plainKeep p0.2.r) ++ nb, nf⟩)
    (hgo : ∀ v, treeGo out' p0.2.d (plainRegs (p0 :: pl)) v fuel ⟨[], nb, nf⟩ =
        some (plainTarget (p0 :: pl) (plainMiss p0 pl) v))
    (hfr : ∀ k, k ≠ o → k ∉ pl.map Prod.fst → k < nex → HoonMap.get out' k = HoonMap.get c.blocks k) :
    HeadStepG lib O gul c (withBlocks c out') (PlainIn nex pl) (· = o) (fun k => k ∈ plainRegs (p0 :: pl))
      (plainD o p0.2.r) (plainE o nb) := by
  obtain ⟨b1, l, r, hb1, hfin, hlr, himm0, -, -, -⟩ := H.headB
  rw [hb] at hb1; cases hb1
  intro x x' hA hh hp hq hbd hrd
  obtain ⟨⟨hl, hpe, ht, hst, hreach, hI, ⟨b0, b0', hb0, hb0', hf, -, ⟨pre, hpre, himm⟩, hb'⟩, hz, hag⟩, -⟩ := hA
  have hh' : x.lab = o := hh
  rw [hh'] at hb0 hb0' himm
  rw [hb] at hb0; cases hb0
  have hb0'' : HoonMap.get out' o = some b0' := hb0'
  rw [hbo] at hb0''; cases hb0''
  have hpre' : pre = b.body := by rw [hbd, List.append_nil] at hpre; exact hpre.symm
  have hc0 : read p0.2.r x.regs = some (A p0.2.c) :=
    himm _ _ (by rw [hpre']; exact himm0) (by simp [plainD, plainKeep])
  have hfx : x.b.fin = Termin.eqq l r ⟨[], p0.2.hit⟩ ⟨[], p0.2.miss⟩ := by rw [hf, hfin]
  obtain ⟨v, hv⟩ : ∃ v, read p0.2.d x.regs = some v := by
    refine hrd p0.2.d ⟨hp, hq, Or.inr ⟨hbd, ?_⟩⟩
    rw [hfx]; simp only [finReads]
    rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hdZ : p0.2.d ∉ plainRegs (p0 :: pl) := by
    intro h
    obtain ⟨t, ht, e⟩ := List.mem_map.mp h
    exact H.hr t ht e
  have hv' : read p0.2.d x'.regs = some v := by rw [hag.rd hdZ]; exact hv
  have htk := taken_eqq_plain (hit := p0.2.hit) (mis := p0.2.miss) hlr hv hc0
  rw [← hfx] at htk
  have hTI : ¬ PlainIn nex pl (plainTarget (p0 :: pl) (plainMiss p0 pl) v) ∧
      plainTarget (p0 :: pl) (plainMiss p0 pl) v ≠ o := by
    rcases plainTarget_mem (p0 :: pl) (plainMiss p0 pl) v with e | ⟨t, ht, e⟩
    · rw [e]; exact H.miss.2
    · rw [e]; exact (H.hits t ht).2
  have before : ∃ es R' bT, HoonMap.get c.blocks (plainTarget (p0 :: pl) (plainMiss p0 pl) v) = some bT ∧
      Steps lib O c gul x es ⟨plainTarget (p0 :: pl) (plainMiss p0 pl) v, bT, [], R', x.t, x.st⟩ ∧
      Reach c.blocks (plainTarget (p0 :: pl) (plainMiss p0 pl) v) ∧
      ∀ k, k ∉ plainRegs (p0 :: pl) → HoonMap.get R' k = HoonMap.get x.regs k := by
    have hbx : HoonMap.get c.blocks x.lab = some b := by rw [hh']; exact hb
    by_cases e : v = A p0.2.c
    · rw [if_pos e] at htk
      obtain ⟨bh, hbh⟩ := Option.isSome_iff_exists.mp (H.hits p0 List.mem_cons_self).1
      rw [plainTarget_cons, if_pos e]
      exact ⟨_, x.regs, bh, hbh, Steps.step (Step.jump hp hq hbd htk hbh) (Steps.refl _),
        Reach.jump (j := ⟨[], p0.2.hit⟩) hreach hbx (by rw [hfin]; simp [getJmps]), fun _ _ => rfl⟩
    · rw [if_neg e] at htk
      rw [plainTarget_cons, if_neg e]
      obtain ⟨t1, rest, hpl, hm0⟩ := H.miss0
      have hblk := H.blocks
      rw [hpl] at hblk
      obtain ⟨-, ⟨l1, r1, hby1, -⟩, -, -⟩ := hblk
      have hby1' : HoonMap.get c.blocks p0.2.miss = some ⟨[], [Pole.imm (A t1.2.c) t1.2.r],
          Termin.eqq l1 r1 ⟨[], t1.2.hit⟩ ⟨[], t1.2.miss⟩⟩ := by rw [hm0]; exact hby1
      have hrm : Reach c.blocks p0.2.miss :=
        Reach.jump (j := ⟨[], p0.2.miss⟩) hreach hbx (by rw [hfin]; simp [getJmps])
      obtain ⟨es, R', bT, hbT, hsT, hrT, hfr2⟩ := plain_walk lib O c gul p0.2.d (plainMiss p0 pl) H.miss.1 pl
        p0.2.miss _ x.regs x.t x.st v H.blocks (fun u hu => (H.hits u (List.mem_cons_of_mem _ hu)).1)
        (by rw [hpl, hm0]; rfl) hby1' hrm hv
      refine ⟨_, R', bT, hbT, Steps.step (Step.jump hp hq hbd htk hby1') hsT, hrT, fun k hk => hfr2 k ?_⟩
      intro h; apply hk; simp only [plainRegs, List.map_cons, List.mem_cons]; exact Or.inr h
  obtain ⟨es, R', bT, hbT, hsT, hrT, hfrT⟩ := before
  generalize hT : plainTarget (p0 :: pl) (plainMiss p0 pl) v = T at hbT hsT hrT hTI
  have hbT' : HoonMap.get (withBlocks c out').blocks T = some bT := by
    show HoonMap.get out' T = some bT
    rw [hfr T hTI.2 (fun h => hTI.1 (Or.inl h)) (Nat.lt_of_not_le fun h => hTI.1 (Or.inr h))]; exact hbT
  have hxb' : x'.b = ⟨[], nb, nf⟩ := by
    rw [hb', hq, hbd, hh', gBody_plain]; rfl
  have hp' : x'.params = [] := by rw [hpe, hp]
  have hx' : (⟨x'.lab, x'.b, [], x'.regs, x'.t, x'.st⟩ : Cfg σ Map) = x' := by rw [← hp']
  have hgo' : treeGo (withBlocks c out').blocks p0.2.d (plainRegs (p0 :: pl)) v fuel x'.b = some T := by
    rw [hxb', ← hT]; exact hgo v
  obtain ⟨r2, hr2, w, hg⟩ := treeGo_good lib O (withBlocks c out') gul fuel x'.lab x'.b x'.regs x'.t x'.st T bT
    hv' hgo' hbT'
  rw [hx'] at hg
  refine ⟨_, _, es, hsT, hg, ⟨⟨rfl, rfl, ht, hst, hrT, hTI.1, ⟨bT, bT, hbT, hbT', rfl, Or.inl rfl,
    ⟨[], rfl, fun _ _ h => absurd h List.not_mem_nil⟩, ?_⟩, fun k hk => by simp at hk, fun k hk => ?_⟩,
    fun _ _ p rest _ => plainD_off hTI.2 p⟩, ?_, ?_⟩
  · show bT = ⟨bT.par, gBody (plainD o p0.2.r) (plainE o nb) T bT.body, bT.fin⟩
    rw [gBody_off (fun p => plainD_off hTI.2 p) (by simp [plainE, hTI.2])]
  · have hk2 : k ≠ r2 := fun e => hk (by rw [e]; exact hr2)
    show HoonMap.get R' k = HoonMap.get (store r2 w x'.regs) k
    rw [get_store_ne hk2, hfrT k hk]
    exact hag k hk
  · show T ≠ x.lab
    rw [hh']; exact hTI.2
  · show T ≠ x'.lab
    rw [hl, hh']; exact hTI.2

/-- **One application of `switchPlain` keeps the code**, given `PlainHyp`
(with the blocks before as both `bl` and `out`, and any `nex` above the head
and the labels of the tests after it). -/
theorem plain_keeps_of (c : Straight Map) {out' : Map Blob} {fuel o nex nex' : Nat} {p0 : Nat × SPlain}
    {pl : List (Nat × SPlain)} {done done' : List Nat}
    (h : switchPlain c.blocks c.blocks fuel o (p0 :: pl) done nex = some (out', done', nex'))
    (H : PlainHyp c.blocks o nex p0 pl) : Keeps c (withBlocks c out') := by
  obtain ⟨b, nb, nf, hb, hbo, hgo, hfr, -, -⟩ := plain_tree h H.nd H.old H.ho H.ho' H.hr
  exact region_keepsG c out' (plain_region H hb hbo hfr)
    (fun lib _ O gul => plain_head lib O gul c H hb hbo hgo hfr)

end Opt
end SkaModel
end Formalization
