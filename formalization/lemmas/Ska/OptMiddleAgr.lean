import lemmas.Ska.OptMiddleBlocks
import lemmas.Ska.OptRegLe
import lemmas.Ska.CompFrame

/-!
# Registers that agree on a set, for `+remove-empty-middle`

After `+remove-empty-middle` the code after skips the passes into the
bypassed blocks, so its registers equal those of the code before except at
the parameters of bypassable blocks (`Byp`), which only their own block
mentions (`byp_owner`, from the `readers` test).  `Agr S R R'`: the two
register files agree at every register of `S`.

* An op whose registers (`poleRegs`) lie in `S` does the same on files that
  agree on `S` (`execPole_agr`), and keeps the agreement.
* A pass reads its arguments only through `argU` (the unit an argument
  passes: poison for `~`, the register's entry otherwise); two passes whose
  arguments give the same units, and pass the check of `+eval-pass`, succeed
  together and agree on the parameters (`passLoop_agr`).
* `pass_sub`: after a pass, a parameter holds what the argument that `mkSub`
  maps it to passes; the other registers are unchanged.  This is the
  substitution of `rewrite-hop`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-- `R` and `R'` agree on `S`. -/
def Agr (S : Nat → Prop) (R R' : Map (Option Noun)) : Prop :=
  ∀ k, S k → HoonMap.get R k = HoonMap.get R' k

theorem Agr.rd {S : Nat → Prop} {R R' : Map (Option Noun)} (h : Agr S R R') {k : Nat} (hk : S k) :
    read k R' = read k R := by
  unfold read; rw [h k hk]

theorem Agr.put {S : Nat → Prop} {R R' : Map (Option Noun)} (h : Agr S R R') (d : Nat) (u : Option Noun) :
    Agr S (HoonMap.put R d u) (HoonMap.put R' d u) := by
  intro k hk; simp only [HoonMap.get_put]; split
  · rfl
  · exact h k hk

theorem Agr.store {S : Nat → Prop} {R R' : Map (Option Noun)} (h : Agr S R R') (d : Nat) (v : Noun) :
    Agr S (store d v R) (store d v R') := h.put d (some v)

theorem Agr.mapM {S : Nat → Prop} {R R' : Map (Option Noun)} (h : Agr S R R') : ∀ (v : List Nat),
    (∀ k ∈ v, S k) → v.mapM (read · R') = v.mapM (read · R)
  | [], _ => rfl
  | a :: v, hv => by
    simp only [List.mapM_cons, h.rd (hv a (by simp)),
      Agr.mapM h v (fun k hk => hv k (List.mem_cons_of_mem _ hk))]

/-! ## Ops -/

section
variable {σ : Type}

/-- Agreeing results of an op. -/
def PAg (S : Nat → Prop) : Option (Tone × Map (Option Noun) × Trace × σ) →
    Option (Tone × Map (Option Noun) × Trace × σ) → Prop
  | Option.none, Option.none => True
  | some (a, R, t, s), some (a', R', t', s') => a = a' ∧ t = t' ∧ s = s' ∧ Agr S R R'
  | _, _ => False

/-- Agreeing results of a local op. -/
def LAg (S : Nat → Prop) : Option (Tone × Map (Option Noun) × Trace) →
    Option (Tone × Map (Option Noun) × Trace) → Prop
  | Option.none, Option.none => True
  | some (a, R, t), some (a', R', t') => a = a' ∧ t = t' ∧ Agr S R R'
  | _, _ => False

theorem localPole_agr (lib : Lib) (gul : Noun) (p : Pole) {S : Nat → Prop} {R R' : Map (Option Noun)} (t : Trace)
    (h : Agr S R R') (hr : ∀ k ∈ poleRegs p, S k) :
    LAg S (localPole lib gul p R t) (localPole lib gul p R' t) := by
  cases p with
  | imm n d => simpa [localPole, LAg] using h.store d n
  | mov s d =>
    simp only [localPole, move]
    rw [← h s (hr s (by simp [poleRegs]))]
    cases HoonMap.get R s <;> simp [LAg, h.put]
  | inc s d =>
    simp only [localPole, h.rd (hr s (by simp [poleRegs]))]
    cases e : read s R with
    | none => simp [LAg]
    | some v => cases v <;> simp [LAg, h, h.store]
  | con a b d =>
    simp only [localPole, h.rd (hr a (by simp [poleRegs])), h.rd (hr b (by simp [poleRegs]))]
    cases read a R <;> cases read b R <;> simp [LAg, h.store]
  | hed s d =>
    simp only [localPole, h.rd (hr s (by simp [poleRegs]))]
    cases e : read s R with
    | none => simp [LAg]
    | some v => cases v <;> simp [LAg, h.store]
  | tal s d =>
    simp only [localPole, h.rd (hr s (by simp [poleRegs]))]
    cases e : read s R with
    | none => simp [LAg]
    | some v => cases v <;> simp [LAg, h.store]
  | cel q =>
    simp only [localPole, h.rd (hr q (by simp [poleRegs]))]
    cases e : read q R with
    | none => simp [LAg]
    | some v => cases v <;> simp [LAg, h]
  | lob q =>
    simp only [localPole, h.rd (hr q (by simp [poleRegs]))]
    cases e : read q R with
    | none => simp [LAg]
    | some v => by_cases hv : v = A 0 ∨ v = A 1 <;> simp [LAg, h, hv]
  | equ a b =>
    simp only [localPole, h.rd (hr a (by simp [poleRegs])), h.rd (hr b (by simp [poleRegs]))]
    cases read a R <;> cases read b R <;> simp [LAg, h]
  | hsp n f => simp [localPole, LAg, h]
  | hse n f => simp [localPole, LAg, h]
  | hdp n q f =>
    simp only [localPole]
    split
    · rw [h.rd (hr q (by simp [poleRegs]))]
      cases read q R <;> simp [LAg, h]
    · simp [LAg, h]
  | hde n q f =>
    simp only [localPole]
    split
    · cases popTrace t <;> simp [LAg, h]
    · simp [LAg, h]
  | hmp a v f =>
    simp only [localPole, h.mapM v (fun k hk => hr k (by simpa [poleRegs] using hk))]
    cases v.mapM (read · R) <;> simp [LAg, h]
  | hme a v f =>
    simp only [localPole]
    cases popTrace t <;> simp [LAg, h]
  | hcp n f => simp [localPole, LAg, h]
  | hce n f =>
    simp only [localPole]
    cases popTrace t <;> simp [LAg, h]
  | spy e q d =>
    simp only [localPole]
    split
    · simp [LAg, h]
    · rw [h.rd (hr e (by simp [poleRegs])), h.rd (hr q (by simp [poleRegs]))]
      cases read e R <;> cases read q R <;> simp only [Option.bind_none, Option.bind_some, LAg]
      rename_i ref pax
      cases lib.slam gul (C ref pax) <;> simp only [Option.bind_none, Option.bind_some, LAg]
      rename_i res
      cases scryDecode res <;> simp only [Option.bind_none, Option.bind_some, LAg]
      rename_i dr
      cases dr <;> simp [LAg, h, h.store]
  | nok u f d => simp [localPole, LAg]
  | cal a v d => simp [localPole, LAg]
  | caf a v d n => simp [localPole, LAg]
  | cam a v d k => simp [localPole, LAg]
  | csl a s d => simp [localPole, LAg]
  | csf a s d n => simp [localPole, LAg]
  | csm a s d k => simp [localPole, LAg]

theorem afterCall_agr (st : σ) {S : Nat → Prop} {R R' : Map (Option Noun)} (t : Trace) (d : Nat) (h : Agr S R R')
    (ton : Tone) : PAg S (afterCall st R t d ton) (afterCall st R' t d ton) := by
  cases ton <;> simp [afterCall, PAg, h, h.store]

/-- **An op whose registers lie in `S` does the same on files that agree on
`S`.** -/
theorem execPole_agr (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (p : Pole) {S : Nat → Prop}
    {R R' : Map (Option Noun)} (t : Trace) (h : Agr S R R') (hr : ∀ k ∈ poleRegs p, S k) :
    PAg S (execPole lib O gul st p R t) (execPole lib O gul st p R' t) := by
  have hloc : PAg S ((localPole lib gul p R t).map fun (ton, regs', trace') => (ton, regs', trace', st))
      ((localPole lib gul p R' t).map fun (ton, regs', trace') => (ton, regs', trace', st)) := by
    have := localPole_agr lib gul p t h hr
    revert this
    cases localPole lib gul p R t <;> cases localPole lib gul p R' t <;> simp [LAg, PAg]
  have call : ∀ (v : List Nat) (a : Bell) (mono : Bool) (d : Nat), (∀ k ∈ v, S k) →
      PAg S ((v.mapM (read · R)).bind fun vs =>
          (O.call st a mono vs t gul).bind fun (ton, st') => afterCall st' R t d ton)
        ((v.mapM (read · R')).bind fun vs =>
          (O.call st a mono vs t gul).bind fun (ton, st') => afterCall st' R' t d ton) := by
    intro v a mono d hv
    rw [h.mapM v hv]
    cases v.mapM (read · R) <;> simp only [Option.bind_none, Option.bind_some, PAg]
    rename_i vs
    cases O.call st a mono vs t gul <;> simp only [Option.bind_none, Option.bind_some, PAg]
    exact afterCall_agr _ t d h _
  have call1 : ∀ (s : Nat) (a : Bell) (d : Nat), S s →
      PAg S ((read s R).bind fun vs =>
          (O.call st a true [vs] t gul).bind fun (ton, st') => afterCall st' R t d ton)
        ((read s R').bind fun vs =>
          (O.call st a true [vs] t gul).bind fun (ton, st') => afterCall st' R' t d ton) := by
    intro s a d hv
    rw [h.rd hv]
    cases read s R <;> simp only [Option.bind_none, Option.bind_some, PAg]
    rename_i vs
    cases O.call st a true [vs] t gul <;> simp only [Option.bind_none, Option.bind_some, PAg]
    exact afterCall_agr _ t d h _
  cases p with
  | nok u f d =>
    simp only [execPole, h.rd (hr u (by simp [poleRegs])), h.rd (hr f (by simp [poleRegs]))]
    cases read u R <;> cases read f R <;> simp only [Option.bind_none, Option.bind_some, PAg]
    rename_i vu vf
    cases O.nok st vu vf gul <;> simp only [Option.bind_none, Option.bind_some, PAg]
    rename_i r; obtain ⟨ton, st'⟩ := r
    cases ton <;> simp [PAg, h, h.store]
  | cal a v d => exact call v a false d (fun k hk => hr k (by simp [poleRegs, hk]))
  | caf a v d n => exact call v a false d (fun k hk => hr k (by simp [poleRegs, hk]))
  | cam a v d k => exact call v a false d (fun k' hk => hr k' (by simp [poleRegs, hk]))
  | csl a s d => exact call1 s a d (hr s (by simp [poleRegs]))
  | csf a s d n => exact call1 s a d (hr s (by simp [poleRegs]))
  | csm a s d k => exact call1 s a d (hr s (by simp [poleRegs]))
  | _ => exact hloc

theorem PAg.fwd {S : Nat → Prop} {a b : Option (Tone × Map (Option Noun) × Trace × σ)} (h : PAg S a b) {ton : Tone}
    {R : Map (Option Noun)} {t : Trace} {s : σ} (ha : a = some (ton, R, t, s)) :
    ∃ R', b = some (ton, R', t, s) ∧ Agr S R R' := by
  subst ha
  match b, h with
  | some (a', R', t', s'), ⟨e1, e2, e3, e4⟩ => subst e1 e2 e3; exact ⟨R', rfl, e4⟩

theorem PAg.bwd {S : Nat → Prop} {a b : Option (Tone × Map (Option Noun) × Trace × σ)} (h : PAg S a b) {ton : Tone}
    {R' : Map (Option Noun)} {t : Trace} {s : σ} (hb : b = some (ton, R', t, s)) :
    ∃ R, a = some (ton, R, t, s) ∧ Agr S R R' := by
  subst hb
  match a, h with
  | some (a', R, t', s'), ⟨e1, e2, e3, e4⟩ => subst e1 e2 e3; exact ⟨R, rfl, e4⟩

end

/-! ## Passes -/

/-- The unit an argument passes. -/
def argU (R : Map (Option Noun)) : Option Nat → Option (Option Noun)
  | none => some none
  | some k => HoonMap.get R k

theorem evalPassLoop_cons (a : Option Nat) (as : List (Option Nat)) (p : Nat) (ps : List Nat)
    (R : Map (Option Noun)) :
    evalPassLoop (a :: as) (p :: ps) R = (argU R a).bind fun u => evalPassLoop as ps (HoonMap.put R p u) := by
  cases a with
  | none => simp [evalPassLoop, argU, poison]
  | some r =>
    simp only [evalPassLoop, argU, move]
    cases HoonMap.get R r <;> simp

theorem argU_put {R : Map (Option Noun)} {p : Nat} {u : Option Noun} {a : Option Nat}
    (h : ∀ k, a = some k → k ≠ p) : argU (HoonMap.put R p u) a = argU R a := by
  cases a with
  | none => rfl
  | some k => simp [argU, HoonMap.get_put, h k rfl]

theorem map_argU_put {R : Map (Option Noun)} {p : Nat} {u : Option Noun} : ∀ {as : List (Option Nat)},
    (∀ a ∈ as, ∀ k, a = some k → k ≠ p) → as.map (argU (HoonMap.put R p u)) = as.map (argU R)
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.map_cons, argU_put (h a (by simp)),
      map_argU_put (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- Agreeing results of a pass, on its parameters. -/
def OAg (P : List Nat) : Option (Map (Option Noun)) → Option (Map (Option Noun)) → Prop
  | Option.none, Option.none => True
  | some a, some b => ∀ k ∈ P, HoonMap.get a k = HoonMap.get b k
  | _, _ => False

theorem OAg.fwd {P : List Nat} {a b : Option (Map (Option Noun))} (h : OAg P a b) {R : Map (Option Noun)}
    (ha : a = some R) : ∃ R', b = some R' ∧ ∀ k ∈ P, HoonMap.get R k = HoonMap.get R' k := by
  subst ha; cases b with
  | none => cases h
  | some R' => exact ⟨R', rfl, h⟩

theorem OAg.bwd {P : List Nat} {a b : Option (Map (Option Noun))} (h : OAg P a b) {R' : Map (Option Noun)}
    (hb : b = some R') : ∃ R, a = some R ∧ ∀ k ∈ P, HoonMap.get R k = HoonMap.get R' k := by
  subst hb; cases a with
  | none => cases h
  | some R => exact ⟨R, rfl, h⟩

/-- **Two passes whose arguments pass the same units succeed together and
agree on the parameters.** -/
theorem passLoop_agr : ∀ (A A' : List (Option Nat)) (P : List Nat) (R R' : Map (Option Noun)),
    (∀ a ∈ A, ∀ k, a = some k → k ∉ P) → (∀ a ∈ A', ∀ k, a = some k → k ∉ P) →
    A.map (argU R) = A'.map (argU R') → OAg P (evalPassLoop A P R) (evalPassLoop A' P R')
  | [], [], P, R, R', _, _, _ => by cases P <;> simp [evalPassLoop, OAg]
  | [], _ :: _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, h => by simp at h
  | a :: as, a' :: as', [], R, R', _, _, _ => by simp [evalPassLoop, OAg]
  | a :: as, a' :: as', p :: ps, R, R', h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hh, ht⟩ := h
    rw [evalPassLoop_cons, evalPassLoop_cons, hh]
    cases e : argU R' a' with
    | none => simp [OAg]
    | some u =>
      simp only [Option.bind_some]
      have h1' : ∀ b ∈ as, ∀ k, b = some k → k ∉ ps :=
        fun b hb k hk hp => h1 b (by simp [hb]) k hk (by simp [hp])
      have h2' : ∀ b ∈ as', ∀ k, b = some k → k ∉ ps :=
        fun b hb k hk hp => h2 b (by simp [hb]) k hk (by simp [hp])
      have n1 : ∀ b ∈ as, ∀ k, b = some k → k ≠ p :=
        fun b hb k hk hp => h1 b (by simp [hb]) k hk (by simp [hp])
      have n2 : ∀ b ∈ as', ∀ k, b = some k → k ≠ p :=
        fun b hb k hk hp => h2 b (by simp [hb]) k hk (by simp [hp])
      have ih := passLoop_agr as as' ps (HoonMap.put R p u) (HoonMap.put R' p u) h1' h2'
        (by rw [map_argU_put n1, map_argU_put n2, ht])
      cases e1 : evalPassLoop as ps (HoonMap.put R p u) with
      | none =>
        rw [e1] at ih
        cases e2 : evalPassLoop as' ps (HoonMap.put R' p u) with
        | none => simp [OAg]
        | some _ => rw [e2] at ih; cases ih
      | some R1 =>
        rw [e1] at ih
        cases e2 : evalPassLoop as' ps (HoonMap.put R' p u) with
        | none => rw [e2] at ih; cases ih
        | some R1' =>
          rw [e2] at ih
          simp only [OAg] at ih ⊢
          intro k hk
          by_cases hkp : k ∈ ps
          · exact ih k hkp
          · rcases List.mem_cons.mp hk with rfl | hk'
            · rw [Comp.evalPassLoop_frame _ _ _ _ e1 k hkp, Comp.evalPassLoop_frame _ _ _ _ e2 k hkp]
              simp [HoonMap.get_put]
            · exact absurd hk' hkp

theorem evalPass_ok {A : List (Option Nat)} {P : List Nat} (h : ∀ a ∈ A, ∀ k, a = some k → k ∉ P)
    (R : Map (Option Noun)) : evalPass A P R = evalPassLoop A P R := by
  unfold evalPass
  rw [if_pos]
  rw [List.all_eq_true]
  intro a ha
  cases a with
  | none => rfl
  | some r => simpa using h _ ha r rfl

theorem mkSub_nil {V : List (Option Nat)} {s0 s : Nat → Option (Option Nat)} (h : mkSub [] V s0 = some s) :
    V = [] ∧ s = s0 := by
  cases V with
  | nil => simp only [mkSub, Option.some.injEq] at h; exact ⟨rfl, h.symm⟩
  | cons => simp [mkSub] at h

theorem mkSub_len : ∀ (P : List Nat) (V : List (Option Nat)) (s0 s : Nat → Option (Option Nat)),
    mkSub P V s0 = some s → V.length = P.length
  | [], V, s0, s, h => by rw [(mkSub_nil h).1]; rfl
  | p :: ps, [], s0, s, h => by simp [mkSub] at h
  | p :: ps, v :: vs, s0, s, h => by
    simp only [mkSub] at h
    simp [mkSub_len ps vs _ s h]

/-- **The substitution of `rewrite-hop`**: after a pass, a parameter holds what
the argument `mkSub` maps it to passes (on `R'`, if the arguments pass the
same units), and the other registers are as before. -/
theorem pass_sub : ∀ (P : List Nat) (A V : List (Option Nat)) (R R1 R' : Map (Option Noun))
    (s0 s : Nat → Option (Option Nat)),
    evalPassLoop A P R = some R1 → (∀ a ∈ A, ∀ k, a = some k → k ∉ P) → mkSub P V s0 = some s →
    A.map (argU R) = V.map (argU R') →
    ∀ k, (k ∈ P → ∃ v, s k = some v ∧ HoonMap.get R1 k = argU R' v) ∧
      (k ∉ P → s k = s0 k ∧ HoonMap.get R1 k = HoonMap.get R k)
  | [], A, V, R, R1, R', s0, s, he, _, hs, hm => by
    obtain ⟨rfl, rfl⟩ := mkSub_nil hs
    cases A with
    | nil =>
      simp only [evalPassLoop, if_true, Option.some.injEq] at he
      subst he; intro k; simp
    | cons => simp at hm
  | p :: ps, A, V, R, R1, R', s0, s, he, hn, hs, hm => by
    cases V with
    | nil => simp [mkSub] at hs
    | cons v vs =>
    cases A with
    | nil => simp at hm
    | cons a as =>
    simp only [mkSub] at hs
    simp only [List.map_cons, List.cons.injEq] at hm
    rw [evalPassLoop_cons] at he
    obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp he
    have hn' : ∀ b ∈ as, ∀ k, b = some k → k ∉ ps :=
      fun b hb k hk hp => hn b (by simp [hb]) k hk (by simp [hp])
    have hne : ∀ b ∈ as, ∀ k, b = some k → k ≠ p :=
      fun b hb k hk hp => hn b (by simp [hb]) k hk (by simp [hp])
    have ih := pass_sub ps as vs (HoonMap.put R p u) R1 R' _ s he hn' hs (by rw [map_argU_put hne, hm.2])
    intro k
    by_cases hk : k ∈ ps
    · exact ⟨fun _ => (ih k).1 hk, fun h => absurd (List.mem_cons_of_mem _ hk) h⟩
    · obtain ⟨h1, h2⟩ := (ih k).2 hk
      by_cases hkp : k = p
      · subst hkp
        refine ⟨fun _ => ⟨v, by rw [h1]; simp, ?_⟩, fun h => absurd List.mem_cons_self h⟩
        rw [h2, ← hm.1, hu]; simp [HoonMap.get_put]
      · refine ⟨fun h => ?_, fun _ => ⟨by rw [h1]; simp [hkp], by rw [h2]; simp [HoonMap.get_put, hkp]⟩⟩
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hkp
        · exact absurd h hk

/-- A pass succeeds when the counts agree and every argument register is
there. -/
theorem passLoop_some : ∀ (A : List (Option Nat)) (P : List Nat) (R : Map (Option Noun)),
    A.length = P.length → (∀ k, some k ∈ A → (HoonMap.get R k).isSome) → (evalPassLoop A P R).isSome
  | [], [], R, _, _ => by simp [evalPassLoop]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: as, p :: ps, R, hl, hs => by
    rw [evalPassLoop_cons]
    have hu : (argU R a).isSome := by
      cases a with
      | none => rfl
      | some k => exact hs k (by simp)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hu
    rw [hu, Option.bind_some]
    apply passLoop_some as ps _ (by simpa using hl)
    intro k hk
    simp only [HoonMap.get_put]
    split
    · rfl
    · exact hs k (by simp [hk])

/-- The arguments of a pass that pass the same units: if those before name
registers that are there, so do those after. -/
theorem argU_isSome : ∀ (A A' : List (Option Nat)) (R R' : Map (Option Noun)),
    A.map (argU R) = A'.map (argU R') → (∀ k, some k ∈ A → (HoonMap.get R k).isSome) →
    ∀ k, some k ∈ A' → (HoonMap.get R' k).isSome
  | [], [], _, _, _, _, _, hk => by simp at hk
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | a :: as, a' :: as', R, R', h, hs, k, hk => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hk with e | hk'
    · subst e
      have h1 := h.1
      simp only [argU] at h1
      rw [← h1]
      cases a with
      | none => rfl
      | some r => exact hs r (by simp)
    · exact argU_isSome as as' R R' h.2 (fun r hr => hs r (by simp [hr])) k hk'

end Opt
end SkaModel
end Formalization
