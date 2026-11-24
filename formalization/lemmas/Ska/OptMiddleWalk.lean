import lemmas.Ska.OptMiddleAgr

/-!
# `+remove-empty-middle`: the bypassed parameters and the walks of the code before

`Byp bl k`: `k` is a parameter of an empty block that ends in a `%hop` and
whose parameters pass the `readers` test of `rewrite-hop` (only the block
itself mentions them).  `byp_owner`: a block that mentions such a `k` has it
as a parameter.

The walks: where the code after takes a rewritten jump, the code before walks
through the bypassed blocks.  On a branch (`jump_walk`) it takes hops that pass
nothing through blocks with no parameters, so its registers do not change.  On
a hop (`hop_walk`) it passes the arguments into each bypassed block and hops
out; its registers change only at the parameters of those blocks, which are
bypassable, and the arguments it holds pending at the end pass the same units
as the substituted arguments of the code after (`pass_sub`).  The walk needs
that the moves of the passes find their registers (the hypothesis `hargs`),
the check of `+eval-pass` of the code before (`PassOK`), and the counts that
`mkSub` checks.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

section
variable [MapKeys Map]

/-- `k` is a parameter of a bypassable block. -/
def Byp (bl : Map Blob) (k : Nat) : Prop :=
  ∃ m bm t, HoonMap.get bl m = some bm ∧ bm.body = [] ∧ bm.fin = Termin.hop t ∧ k ∈ bm.par ∧
    (bm.par.all fun p => (readersOf bl p).all (· = m)) = true

theorem mem_readersOf {bl : Map Blob} {o : Nat} {b : Blob} {k : Nat} (hb : HoonMap.get bl o = some b)
    (hk : k ∈ blobRegs b) : o ∈ readersOf bl k := by
  unfold readersOf
  rw [List.mem_filter]
  refine ⟨(MapKeys.mem_keys bl o).mpr (by simp [hb]), ?_⟩
  simp [hb, hk]

/-- **Only its own block mentions a bypassable parameter.** -/
theorem byp_owner {bl : Map Blob} {k o : Nat} {b : Blob} (hy : Byp bl k) (hb : HoonMap.get bl o = some b)
    (hk : k ∈ blobRegs b) : k ∈ b.par := by
  obtain ⟨m, bm, t, hm, -, -, hkm, hall⟩ := hy
  have h1 := List.all_eq_true.mp hall k hkm
  have h2 := List.all_eq_true.mp h1 o (mem_readersOf hb hk)
  have : o = m := of_decide_eq_true h2
  subst this
  rw [hb] at hm; cases hm; exact hkm

end

/-! ## Registers a block mentions -/

theorem mem_jmpRegs {j : Jmp} {k : Nat} : k ∈ jmpRegs j ↔ some k ∈ j.args := by
  simp [jmpRegs]

theorem jmp_finRegs {f : Termin} {j : Jmp} {k : Nat} (hj : j ∈ getJmps f) (hk : some k ∈ j.args) :
    k ∈ finRegs f := by
  have hk' : k ∈ jmpRegs j := mem_jmpRegs.mpr hk
  cases f <;> simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
  all_goals first
    | (rcases hj with rfl | rfl <;> simp [finRegs, hk'])
    | (subst hj; simpa [finRegs] using hk')
    | exact absurd hj id

theorem finReads_sub {f : Termin} {k : Nat} (h : k ∈ finReads f) : k ∈ finRegs f := by
  cases f <;> simp only [finReads, finRegs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
  all_goals first
    | exact h
    | exact Or.inl h
    | (rcases h with h | h <;> simp [h])
    | exact absurd h id

theorem poleReads_sub {gul : Noun} {p : Pole} {k : Nat} (h : k ∈ poleReads gul p) : k ∈ poleRegs p := by
  cases p <;> simp only [poleReads, poleRegs] at h ⊢ <;> (try split at h) <;> (try simp_all) <;>
    (rcases h with h | h <;> simp [h])

theorem fin_blobRegs {b : Blob} {k : Nat} (h : k ∈ finRegs b.fin) : k ∈ blobRegs b := by
  simp [blobRegs, h]

theorem op_blobRegs {b : Blob} {p : Pole} {rest : List Pole} {k : Nat} (hb : b.body = p :: rest)
    (h : k ∈ poleRegs p) : k ∈ blobRegs b := by
  simp only [blobRegs, hb, List.flatMap_cons, List.mem_append]
  exact Or.inr (Or.inl h)

theorem tail_blobRegs {b : Blob} {p : Pole} {rest : List Pole} {k : Nat} (hb : b.body = p :: rest)
    (h : k ∈ blobRegs { b with body := rest }) : k ∈ blobRegs b := by
  simp only [blobRegs, hb, List.flatMap_cons, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-! ## The rewrites -/

theorem rewriteJump_start {bl : Map Blob} {n : Nat} {j j' : Jmp} (h : rewriteJump bl n j = some j')
    (ha : j.args = []) : ∃ b, HoonMap.get bl j.there = some b := by
  cases n with
  | zero => simp [rewriteJump] at h
  | succ n =>
    simp only [rewriteJump, ha, ne_eq, not_true_eq_false, if_false] at h
    cases e : HoonMap.get bl j.there with
    | none => rw [e] at h; simp at h
    | some b => exact ⟨b, rfl⟩

theorem rewriteJump_args {bl : Map Blob} {n : Nat} {j j' : Jmp} (h : rewriteJump bl n j = some j')
    (ha : j.args ≠ []) : j' = j := by
  cases n with
  | zero => simp [rewriteJump] at h
  | succ n => simp only [rewriteJump, if_pos ha, Option.some.injEq] at h; exact h.symm

theorem rewriteHop_start {bl : Map Blob} {rd : Nat → List Nat} {n : Nat} {j j' : Jmp}
    (h : rewriteHop bl rd n j = some j') : ∃ b, HoonMap.get bl j.there = some b := by
  cases n with
  | zero => simp [rewriteHop] at h
  | succ n =>
    simp only [rewriteHop] at h
    cases e : HoonMap.get bl j.there with
    | none => rw [e] at h; simp at h
    | some b => exact ⟨b, rfl⟩

section Walk
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c : Straight Map}

/-- A pass, or nothing when there is nothing to pass. -/
theorem pass_steps {lab : Nat} {b : Blob} {A : List (Option Nat)} {R R1 : Map (Option Noun)} {t : Trace} {st : σ}
    (h : evalPass A b.par R = some R1) :
    ∃ es, Steps lib O c gul ⟨lab, b, A, R, t, st⟩ es ⟨lab, { b with par := [] }, [], R1, t, st⟩ := by
  by_cases hne : A ≠ [] ∨ b.par ≠ []
  · exact ⟨_, Steps.step (Step.pass (x := ⟨lab, b, A, R, t, st⟩) hne h) (Steps.refl _)⟩
  · simp only [not_or, ne_eq, Decidable.not_not] at hne
    obtain ⟨rfl, hp⟩ := hne
    rw [hp] at h
    simp [evalPass, evalPassLoop] at h
    subst h
    obtain ⟨p, bd, f⟩ := b
    simp only at hp; subst hp
    exact ⟨[], Steps.refl _⟩

/-- **The walk of a rewritten branch jump.** -/
theorem jump_walk : ∀ (n : Nat) (j j' : Jmp), rewriteJump c.blocks n j = some j' →
    ∀ b1, HoonMap.get c.blocks j.there = some b1 →
    ∃ b2, HoonMap.get c.blocks j'.there = some b2 ∧ j'.args = j.args ∧
      ∀ (R : Map (Option Noun)) (t : Trace) (st : σ), ∃ es,
        Steps lib O c gul ⟨j.there, b1, j.args, R, t, st⟩ es ⟨j'.there, b2, j'.args, R, t, st⟩
  | 0, _, _, h, _, _ => by simp [rewriteJump] at h
  | n + 1, j, j', h, b1, hb1 => by
    have done : j' = j → ∃ b2, HoonMap.get c.blocks j'.there = some b2 ∧ j'.args = j.args ∧
        ∀ (R : Map (Option Noun)) (t : Trace) (st : σ), ∃ es,
          Steps lib O c gul ⟨j.there, b1, j.args, R, t, st⟩ es ⟨j'.there, b2, j'.args, R, t, st⟩ := by
      intro e; subst e; exact ⟨b1, hb1, rfl, fun R t st => ⟨[], Steps.refl _⟩⟩
    simp only [rewriteJump] at h
    by_cases ha : j.args ≠ []
    · rw [if_pos ha] at h; exact done (Option.some.inj h).symm
    · rw [if_neg ha, hb1, Option.bind_some] at h
      simp only [ne_eq, Decidable.not_not] at ha
      by_cases hp : b1.par ≠ []
      · rw [if_pos hp] at h; cases h
      · rw [if_neg hp] at h
        simp only [ne_eq, Decidable.not_not] at hp
        by_cases hb : b1.body ≠ []
        · rw [if_pos hb] at h; exact done (Option.some.inj h).symm
        · rw [if_neg hb] at h
          simp only [ne_eq, Decidable.not_not] at hb
          cases hf : b1.fin with
          | hop t1 =>
            simp only [hf] at h
            by_cases ht : t1.args ≠ []
            · rw [if_pos ht] at h; exact done (Option.some.inj h).symm
            · rw [if_neg ht] at h
              simp only [ne_eq, Decidable.not_not] at ht
              obtain ⟨b1', hb1'⟩ := rewriteJump_start h ht
              obtain ⟨b2, hb2, ha2, hs⟩ := jump_walk n t1 j' h b1' hb1'
              refine ⟨b2, hb2, by rw [ha2, ht, ha], fun R t st => ?_⟩
              obtain ⟨es, hs⟩ := hs R t st
              exact ⟨_, Steps.step (step_hop (x := ⟨j.there, b1, j.args, R, t, st⟩) ha hp hb hf hb1') hs⟩
          | _ => simp only [hf] at h; exact done (Option.some.inj h).symm

variable [MapKeys Map]

/-- **The walk of a rewritten hop.** -/
theorem hop_walk (hpc : PassOK c.blocks) : ∀ (n : Nat) (V V' : Jmp),
    rewriteHop c.blocks (readersOf c.blocks) n V = some V' →
    ∀ (J : List (Option Nat)) (b1 : Blob) (R R' : Map (Option Noun)) (t : Trace) (st : σ),
    HoonMap.get c.blocks V.there = some b1 → J.map (argU R) = V.args.map (argU R') →
    (∀ k, some k ∈ J → k ∉ b1.par) → Agr (fun k => ¬ Byp c.blocks k) R R' →
    (∀ es z k, Steps lib O c gul ⟨V.there, b1, J, R, t, st⟩ es z → some k ∈ z.params →
      (HoonMap.get z.regs k).isSome) →
    ∃ es J2 b2 R2, Steps lib O c gul ⟨V.there, b1, J, R, t, st⟩ es ⟨V'.there, b2, J2, R2, t, st⟩ ∧
      HoonMap.get c.blocks V'.there = some b2 ∧ J2.map (argU R2) = V'.args.map (argU R') ∧
      (∀ k, some k ∈ J2 → k ∉ b2.par) ∧ Agr (fun k => ¬ Byp c.blocks k) R2 R'
  | 0, _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [rewriteHop] at h
  | n + 1, V, V', h, J, b1, R, R', t, st, hb1, hm, hck, hag, hargs => by
    have done : V' = V → ∃ es J2 b2 R2,
        Steps lib O c gul ⟨V.there, b1, J, R, t, st⟩ es ⟨V'.there, b2, J2, R2, t, st⟩ ∧
        HoonMap.get c.blocks V'.there = some b2 ∧ J2.map (argU R2) = V'.args.map (argU R') ∧
        (∀ k, some k ∈ J2 → k ∉ b2.par) ∧ Agr (fun k => ¬ Byp c.blocks k) R2 R' := by
      intro e; subst e; exact ⟨[], J, b1, R, Steps.refl _, hb1, hm, hck, hag⟩
    simp only [rewriteHop, hb1, Option.bind_some] at h
    by_cases hb : b1.body ≠ []
    · rw [if_pos hb] at h; exact done (Option.some.inj h).symm
    · rw [if_neg hb] at h
      simp only [ne_eq, Decidable.not_not] at hb
      cases hf : b1.fin with
      | hop t1 =>
        simp only [hf] at h
        by_cases hall : (b1.par.all fun p => (readersOf c.blocks p).all (· = V.there)) = true
        · rw [hall] at h
          simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
          obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
          have hlen : J.length = b1.par.length := by
            rw [← mkSub_len _ _ _ _ hs]; simpa using congrArg List.length hm
          have hsome := passLoop_some J b1.par R hlen (fun k hk => hargs [] _ k (Steps.refl _) hk)
          obtain ⟨R1, hR1⟩ := Option.isSome_iff_exists.mp hsome
          have hck0 : ∀ a ∈ J, ∀ k, a = some k → k ∉ b1.par := fun a ha k e => hck k (e ▸ ha)
          have hP := pass_sub b1.par J V.args R R1 R' _ s hR1 hck0 hs hm
          obtain ⟨b1', hb1'⟩ := rewriteHop_start h
          have hbyp : ∀ k ∈ b1.par, Byp c.blocks k := fun k hk => ⟨V.there, b1, t1, hb1, hb, hf, hk, hall⟩
          obtain ⟨es0, hs0⟩ := pass_steps (lib := lib) (O := O) (c := c) (gul := gul) (lab := V.there) (t := t)
            (st := st) (by rw [evalPass_ok hck0]; exact hR1)
          have hs1 : Steps lib O c gul ⟨V.there, b1, J, R, t, st⟩ (es0 ++ ([(V.there, t1.there)] ++ []))
              ⟨t1.there, b1', t1.args, R1, t, st⟩ :=
            steps_trans hs0 (Steps.step (step_hop (x := ⟨V.there, { b1 with par := [] }, [], R1, t, st⟩) rfl rfl hb hf
              hb1') (Steps.refl _))
          have hagr : ∀ a ∈ t1.args, argU R1 a = argU R' (passArg s a) := by
            intro a ha
            cases a with
            | none => rfl
            | some k =>
              have hkb : k ∈ blobRegs b1 := fin_blobRegs (jmp_finRegs (by simp [hf, getJmps]) ha)
              by_cases hk : k ∈ b1.par
              · obtain ⟨v, hv, hv'⟩ := (hP k).1 hk
                simp only [argU, passArg, hv, Option.getD_some]; exact hv'
              · obtain ⟨hv, hv'⟩ := (hP k).2 hk
                simp only [argU, passArg, hv, Option.getD_none]
                rw [hv']
                exact hag k (fun hy => hk (byp_owner hy hb1 hkb))
          have ih := hop_walk hpc n ⟨t1.args.map (passArg s), t1.there⟩ V' h t1.args b1' R1 R' t st hb1'
            (by rw [List.map_map]; exact List.map_congr_left hagr)
            (fun k hk => hpc V.there b1 t1 b1' hb1 (by simp [hf, getJmps]) hb1' k hk)
            (fun k hk => by
              have hk' : k ∉ b1.par := fun h => hk (hbyp k h)
              rw [((hP k).2 hk').2]; exact hag k hk)
            (fun es z k hz hk => hargs _ z k (steps_trans hs1 hz) hk)
          obtain ⟨es2, J2, b2, R2, hs2, hb2, hm2, hc2, hag2⟩ := ih
          exact ⟨_, J2, b2, R2, steps_trans hs1 hs2, hb2, hm2, hc2, hag2⟩
        · simp only [hall, Bool.not_false, if_true] at h
          exact done (Option.some.inj h).symm
      | _ => simp only [hf] at h; exact done (Option.some.inj h).symm

end Walk

/-! ## The jump the code after takes -/

section
variable [MapKeys Map]

/-- The jump after against the jump before. -/
def JRel (bl : Map Blob) (fuel : Nat) (f : Termin) (j j' : Jmp) : Prop :=
  j' = j ∨ rewriteJump bl fuel j = some j' ∨ (f = Termin.hop j ∧ rewriteHop bl (readersOf bl) fuel j = some j')

theorem taken_mid {bl : Map Blob} {fuel : Nat} {f f' : Termin} {R R' : Map (Option Noun)}
    (hf : middleFin bl (readersOf bl) fuel f = some f') (hR : ∀ k ∈ finRegs f, read k R' = read k R) :
    (∀ j, taken R f = some j → ∃ j', taken R' f' = some j' ∧ JRel bl fuel f j j') ∧
    (∀ j', taken R' f' = some j' → ∃ j, taken R f = some j ∧ JRel bl fuel f j j') := by
  cases f with
  | clq s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf
    obtain ⟨z', hz, o', ho, rfl⟩ := hf
    simp only [taken, hR s (by simp [finRegs])]
    cases read s R with
    | none => simp
    | some v => cases v <;> simp [JRel, hz, ho]
  | eqq l r z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf
    obtain ⟨z', hz, o', ho, rfl⟩ := hf
    simp only [taken, hR l (by simp [finRegs]), hR r (by simp [finRegs])]
    cases read l R with
    | none => simp
    | some a =>
      cases read r R with
      | none => simp
      | some b => by_cases e : a = b <;> simp [JRel, hz, ho, e]
  | brn s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf
    obtain ⟨z', hz, o', ho, rfl⟩ := hf
    simp only [taken, hR s (by simp [finRegs])]
    cases read s R with
    | none => simp
    | some v =>
      by_cases h0 : v = A 0
      · simp [JRel, hz, ho, h0]
      · by_cases h1 : v = A 1 <;> simp [JRel, hz, ho, h0, h1]
  | brz s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf
    obtain ⟨z', hz, o', ho, rfl⟩ := hf
    simp only [taken, hR s (by simp [finRegs])]
    cases read s R with
    | none => simp
    | some v => by_cases h0 : v = A 0 <;> simp [JRel, hz, ho, h0]
  | hop t =>
    simp only [middleFin, Option.map_eq_some_iff] at hf
    obtain ⟨t', ht, rfl⟩ := hf
    simp [taken, JRel, ht]
  | lti n s z o =>
    simp only [middleFin, Option.some.injEq] at hf
    subst hf
    simp only [taken, hR s (by simp [finRegs])]
    exact ⟨fun j hj => ⟨j, hj, Or.inl rfl⟩, fun j hj => ⟨j, hj, Or.inl rfl⟩⟩
  | jmp => simp only [middleFin, Option.some.injEq] at hf; subst hf; simp [taken]
  | jmf => simp only [middleFin, Option.some.injEq] at hf; subst hf; simp [taken]
  | jsp => simp only [middleFin, Option.some.injEq] at hf; subst hf; simp [taken]
  | jsf => simp only [middleFin, Option.some.injEq] at hf; subst hf; simp [taken]
  | don => simp only [middleFin, Option.some.injEq] at hf; subst hf; simp [taken]
  | bom => simp only [middleFin, Option.some.injEq] at hf; subst hf; simp [taken]

theorem finReads_mid {bl : Map Blob} {rd : Nat → List Nat} {fuel : Nat} {f f' : Termin}
    (hf : middleFin bl rd fuel f = some f') : finReads f' = finReads f := by
  cases f <;> simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hf
  all_goals first
    | (obtain ⟨_, -, _, -, rfl⟩ := hf; rfl)
    | (obtain ⟨_, -, rfl⟩ := hf; rfl)
    | (subst hf; rfl)

end

end Opt
end SkaModel
end Formalization
