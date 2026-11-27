import lemmas.Compiler.OptLinkTotalStart

/-!
# `+alias` returns: one kept block

**`aliasBlock_some`**: one block `o` of the walk that is kept (it has a
predecessor left, or it is the entry `0`) returns, from what the walk
invariant must give at `o`:
* `B1`, `B4`: its block `b` (`TopoOK`);
* `S1`, `B3`, `W2`: every predecessor has closed facts and immediates with
  facts;
* `S2` .. `S5`, `E1`, `I1` .. `I3`, `W1`: every predecessor has its new
  block, which jumps to `o`, its jumps to `o` pass at least `|b.par|`
  arguments, each with a fact, and a fact for the test register of a
  two-way end (`TestFact`);
* `W3` at `o`: a set `S` of registers, each a parameter of `b`, an argument
  of the entry (`old r < nargs` with no predecessor), or with a fact under
  `old` in every predecessor;
* the body and the end: every read is in `S` or written by an earlier op,
  `old` is the identity on the parameters and on the registers the body
  writes, which are written once (`DefOnceR`), and a two-way end passes no
  arguments (`TwoNA`).
Then the new state has, for `o`, closed facts, immediates with facts, a fact
for every register of `S` or written by the body under the new `old`, and
`old` is unchanged off the registers the body writes.  What is left of
`AliasRetN` is to derive these from the walk invariant `W0` .. `W3` and the
input (`DefFirst`, `DefOnceR`, `ReadsIn`, `ArityOK`, `TwoNA`, `TopoOK`), by
induction on the walk.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map]

theorem aclo_entry (nargs : Nat) : AClo (Opt.entryInfo nargs) := by
  intro k v x hk hx
  simp only [Opt.entryInfo] at hk
  split at hk
  · cases hk; exact absurd hx (iref_empty x)
  · cases hk

/-- **One kept block of the walk returns** (see the header). -/
theorem aliasBlock_some (pick : List Nat → Nat) (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (nargs : Nat)
    (bl : Map Blob) (g : Opt.AGen Map) (o : Nat) (b : Blob)
    (hb : HoonMap.get bl o = some b)
    (hk : g.rev o ≠ [] ∨ o = 0)
    (hinfo : ∀ q ∈ g.rev o, ∃ i m, g.info q = some i ∧ g.imms q = some m ∧ AClo i ∧ IClo i m)
    (hnew : ∀ q ∈ g.rev o, ∃ pb, HoonMap.get g.new q = some pb ∧ (∃ j ∈ Opt.getJmps pb.fin, j.there = o) ∧
      (∀ j ∈ Opt.getJmps pb.fin, j.there = o → b.par.length ≤ j.args.length ∧
        ∀ k u, k < b.par.length → j.args[k]? = some (some u) → ((g.info q).bind fun i => i u).isSome) ∧
      ∀ i, g.info q = some i → TestFact pb.fin i)
    (S : Nat → Prop)
    (hS : ∀ r, S r → r ∈ b.par ∨ (g.rev o = [] ∧ g.old r < nargs) ∨
      (g.rev o ≠ [] ∧ ∀ q ∈ g.rev o, ∀ i, g.info q = some i → (i (g.old r)).isSome))
    (hpar : ∀ x ∈ b.par, g.old x = x)
    (hold : ∀ d ∈ b.body.filterMap Opt.aliasDst, g.old d = d) (hnd : (b.body.filterMap Opt.aliasDst).Nodup)
    (hreads : ∀ i op, b.body[i]? = some op → ∀ r ∈ Opt.aliasReads op,
      S r ∨ r ∈ (b.body.take i).filterMap Opt.aliasDst)
    (hfin : ∀ s, s ∈ (Opt.finRegs b.fin).head? → twoWay b.fin = true → (∀ l r z o', b.fin ≠ Termin.eqq l r z o') →
      S s ∨ s ∈ b.body.filterMap Opt.aliasDst)
    (h2 : twoWay b.fin = true → ∀ j ∈ Opt.getJmps b.fin, j.args = []) :
    ∃ g', Opt.aliasBlock pick nargs bl g o = some g' ∧ ∃ loc im, g'.info o = some loc ∧ g'.imms o = some im ∧
      AClo loc ∧ IClo loc im ∧ (∀ r, S r ∨ r ∈ b.body.filterMap Opt.aliasDst → (loc (g'.old r)).isSome) ∧
      (∀ x, x ∉ b.body.filterMap Opt.aliasDst → g'.old x = g.old x) := by
  have hnot : ¬ (g.rev o = [] ∧ o ≠ 0) := by
    rintro ⟨h1, h2⟩; rcases hk with h | h
    · exact h h1
    · exact h2 h
  -- the start facts
  have I : ∃ info, (if g.rev o = [] then some (Opt.entryInfo nargs) else Opt.aliasStart g o (g.rev o)) = some info ∧
      AClo info ∧ (g.rev o = [] → info = Opt.entryInfo nargs) ∧
      (g.rev o ≠ [] → ∀ x, (∀ q ∈ g.rev o, ∀ i, g.info q = some i → (i x).isSome) → (info x).isSome) := by
    by_cases hp : g.rev o = []
    · rw [if_pos hp]; exact ⟨_, rfl, aclo_entry nargs, fun _ => rfl, fun h => absurd hp h⟩
    · rw [if_neg hp]
      obtain ⟨p, t, hpt⟩ : ∃ p t, g.rev o = p :: t := by
        cases e : g.rev o with
        | nil => exact absurd e hp
        | cons p t => exact ⟨p, t, rfl⟩
      have hm : ∀ q, q ∈ p :: t → q ∈ g.rev o := fun q hq => by rw [hpt]; exact hq
      obtain ⟨info, e, c, K⟩ := aliasStart_inv g o p t
        (fun q hq => by obtain ⟨i, m, hi, -, ci, -⟩ := hinfo q (hm q hq); exact ⟨i, hi, ci⟩)
        (fun ht => by
          obtain ⟨pb, hpb, hj, -, hT⟩ := hnew p (hm p List.mem_cons_self); exact ⟨pb, hpb, hj, hT⟩)
      refine ⟨info, by rw [hpt]; exact e, c, fun h => absurd h hp, fun _ x hx => K x fun q hq => hx q (hm q hq)⟩
  obtain ⟨info, ei, ci, i0, iK⟩ := I
  obtain ⟨im, eim, kim⟩ := aliasStartImms_inv g (g.rev o)
    (fun q hq => by obtain ⟨i, m, -, hm, -⟩ := hinfo q hq; simp [hm])
  obtain ⟨es, ees, kes, kes'⟩ := aliasEdges_inv g o (g.rev o)
    (fun q hq => by obtain ⟨pb, hpb, -⟩ := hnew q hq; simp [hpb])
  have hedge : ∀ e ∈ es, e.1 ∈ g.rev o ∧ b.par.length ≤ e.2.length ∧
      ∀ k u, k < b.par.length → e.2[k]? = some (some u) → ((g.info e.1).bind fun i => i u).isSome := by
    intro e he
    obtain ⟨hq, pb, hpb, j, hj, hjo, he2⟩ := kes e he
    obtain ⟨pb', hpb', -, hJ, -⟩ := hnew e.1 hq
    rw [hpb] at hpb'; cases hpb'
    obtain ⟨l1, l2⟩ := hJ j hj hjo
    exact ⟨hq, he2 ▸ l1, fun k u hk hu => l2 k u hk (he2 ▸ hu)⟩
  obtain ⟨loc0, ep, cp, gp, pp⟩ := aliasPars_inv g b.par es info ci
    (fun e he => by obtain ⟨i, m, hi, -, c, -⟩ := hinfo _ (hedge e he).1; exact ⟨i, hi, c⟩)
    (fun x hne hall => by
      by_cases hp : g.rev o = []
      · exfalso
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil es hne
        have := (hedge e he).1; rw [hp] at this; cases this
      · refine iK hp x fun q hq i hi => ?_
        obtain ⟨pb, hpb, ⟨j, hj, hjo⟩, -⟩ := hnew q hq
        obtain ⟨i', hi', hx⟩ := hall (q, j.args) (kes' q hq pb hpb j hj hjo)
        rw [hi] at hi'; cases hi'; exact hx)
    (fun e he => (hedge e he).2.1) (fun e he => (hedge e he).2.2)
  have B : BInv S { old := g.old, loc := loc0, imml := im } := by
    refine ⟨fun r hr => ?_, cp, fun n x hx => ?_⟩
    · show (loc0 (g.old r)).isSome
      rcases hS r hr with h | h | h
      · rw [hpar r h]; exact pp r h
      · refine gp _ ?_; rw [i0 h.1]; simp [Opt.entryInfo, h.2]
      · exact gp _ (iK h.1 _ h.2)
    · by_cases hp : g.rev o = []
      · rw [hp] at eim; simp only [Opt.aliasStartImms, Option.some.injEq] at eim; subst eim; cases hx
      · refine gp _ (iK hp x fun q hq i hi => ?_)
        obtain ⟨m, hm, hxm⟩ := kim n x hx q hq
        obtain ⟨i', m', hi', hm', -, cm⟩ := hinfo q hq
        rw [hi] at hi'; cases hi'; rw [hm] at hm'; cases hm'
        exact cm n x hxm
  obtain ⟨rb, eb, Bb, gb, ob⟩ := aliasBody_inv pick hpick b.body _ S B hreads hold hnd
  obtain ⟨rf, ef⟩ := Option.isSome_iff_exists.1 (aliasFin_some rb.2.old rb.2.loc g.rev g.folded o b.fin h2
    (fun s hs ht hne => Bb.av s (hfin s hs ht hne)))
  let g' : Opt.AGen Map :=
    { new := HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }
      old := rb.2.old
      info := Opt.updA g.info o (some rb.2.loc)
      imms := Opt.updA g.imms o (some rb.2.imml)
      rev := rf.2.1
      folded := rf.2.2 }
  refine ⟨g', ?_, rb.2.loc, rb.2.imml, ?_, ?_, Bb.clo, Bb.imm, ?_, ?_⟩
  · simp only [Opt.aliasBlock]
    rw [if_neg hnot, ei, Option.bind_some, eim, Option.bind_some, hb, Option.bind_some, ees, Option.bind_some, ep,
      Option.bind_some, eb, Option.bind_some, ef, Option.map_some]
  · exact updA_self _ _ _
  · exact updA_self _ _ _
  · exact Bb.av
  · exact ob

end Compiler
end Formalization
