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

end Opt
end SkaModel
end Formalization
