import lemmas.Ska.CompTop

/-!
# The renaming path of `+to-straight` keeps what the code does

`sim_block`: if every block of a program `c` jumps only to labels below its
own and at least `1` (`Sim.down`), then a program `c'` that holds, at each
label of a block of `c` that is not bypassed, that block with its registers
renamed by an injective `ren` and its jumps chased past the bypassed blocks,
does what `c` does from every block, on registers related by the renaming.
The proof is by induction on the label.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-! ## Registers under a renaming -/

/-- `R'` holds at `ren r` what `R` holds at `r`. -/
def RenRel (ren : Nat → Nat) (R R' : Map Noun) : Prop :=
  ∀ r, SkaModel.read (ren r) R' = SkaModel.read r R

def Inj (ren : Nat → Nat) : Prop := ∀ a b, ren a = ren b → a = b

section Ren
variable {ren : Nat → Nat}

theorem RenRel.store (hi : Inj ren) {R R' : Map Noun} (h : RenRel ren R R') (d : Nat) (v : Noun) :
    RenRel ren (store d v R) (store (ren d) v R') := by
  intro r
  by_cases e : r = d
  · subst e; simp [read_store_eq]
  · rw [read_store_ne (fun h' => e (hi _ _ h')), read_store_ne e, h r]

theorem RenRel.del (hi : Inj ren) {R R' : Map Noun} (h : RenRel ren R R') (p : Nat) :
    RenRel ren (HoonMap.del R p) (HoonMap.del R' (ren p)) := by
  intro r
  have hr := h r
  simp only [SkaModel.read, HoonMap.get_del] at hr ⊢
  by_cases e : r = p
  · subst e; simp
  · rw [if_neg (fun h' => e (hi _ _ h')), if_neg e]; exact hr

theorem RenRel.mapM {R R' : Map Noun} (h : RenRel ren R R') : ∀ (v : List Nat),
    (v.map ren).mapM (SkaModel.read · R') = v.mapM (SkaModel.read · R)
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.mapM_cons, h x, RenRel.mapM h xs]

/-- Related optional register maps. -/
def ORel (ren : Nat → Nat) : Option (Map Noun) → Option (Map Noun) → Prop
  | Option.none, Option.none => True
  | some a, some b => RenRel ren a b
  | _, _ => False

theorem evalPassLoop_ren (hi : Inj ren) : ∀ (args : List (Option Nat)) (par : List Nat) {R R' : Map Noun},
    RenRel ren R R' →
    ORel ren (evalPassLoop args par R) (evalPassLoop (args.map (Option.map ren)) (par.map ren) R')
  | [], par, R, R', h => by cases par <;> simp [evalPassLoop, ORel, h]
  | a :: args, [], _, _, h => by simp [evalPassLoop, ORel]
  | a :: args, p :: par, R, R', h => by
      cases a with
      | none =>
        simp only [evalPassLoop, List.map_cons, Option.map_none, Option.bind_some]
        exact evalPassLoop_ren hi args par (h.del hi p)
      | some r =>
        simp only [evalPassLoop, List.map_cons, Option.map_some, move]
        rw [h r]
        cases e : SkaModel.read r R with
        | none => simp [ORel]
        | some v => simpa using evalPassLoop_ren hi args par (h.store hi p v)

theorem contains_map (hi : Inj ren) (par : List Nat) (r : Nat) :
    (par.map ren).contains (ren r) = par.contains r := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨x, hx, e⟩ => hi _ _ e ▸ hx, fun h => ⟨r, h, rfl⟩⟩

theorem evalPass_ren (hi : Inj ren) (args : List (Option Nat)) (par : List Nat) {R R' : Map Noun}
    (h : RenRel ren R R') :
    ORel ren (evalPass args par R) (evalPass (args.map (Option.map ren)) (par.map ren) R') := by
  unfold evalPass
  split <;> split
  · exact evalPassLoop_ren hi args par h
  · rename_i h1 h2; exfalso; apply h2; rw [List.all_eq_true] at h1 ⊢
    intro x hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; have := h1 a ha
    cases a with
    | none => rfl
    | some r =>
      have h' : ¬ r ∈ par := by simpa using this
      simpa using (fun x hx e => h' (hi _ _ e ▸ hx) : ∀ x, x ∈ par → ¬ren x = ren r)
  · rename_i h1 h2; exfalso; apply h1; rw [List.all_eq_true] at h2 ⊢
    intro a ha; have := h2 _ (List.mem_map_of_mem ha)
    cases a with
    | none => rfl
    | some r =>
      have h' : ∀ x, x ∈ par → ¬ren x = ren r := by simpa using this
      simpa using (fun hr => h' r hr rfl : ¬ r ∈ par)
  · trivial

/-! ## Ops under a renaming -/

/-- Related results of an op. -/
def PRel (ren : Nat → Nat) {σ : Type} : Option (Tone × Map Noun × Trace × σ) →
    Option (Tone × Map Noun × Trace × σ) → Prop
  | Option.none, Option.none => True
  | some (a, R, t, s), some (a', R', t', s') => a = a' ∧ t = t' ∧ s = s' ∧ RenRel ren R R'
  | _, _ => False

/-- Related results of a local op. -/
def LRel (ren : Nat → Nat) : Option (Tone × Map Noun × Trace) → Option (Tone × Map Noun × Trace) → Prop
  | Option.none, Option.none => True
  | some (a, R, t), some (a', R', t') => a = a' ∧ t = t' ∧ RenRel ren R R'
  | _, _ => False

theorem localPole_ren (hi : Inj ren) (lib : Lib) (gul : Noun) (p : Pole) {R R' : Map Noun} (t : Trace)
    (h : RenRel ren R R') : LRel ren (localPole lib gul p R t) (localPole lib gul (renPole ren p) R' t) := by
  cases p with
  | imm n d => simpa [localPole, renPole, LRel] using h.store hi d n
  | mov s d =>
    simp only [localPole, renPole, move, h s]
    cases SkaModel.read s R <;> simp [LRel, h.store hi]
  | inc s d =>
    simp only [localPole, renPole, h s]
    cases e : SkaModel.read s R with
    | none => simp [LRel]
    | some v => cases v <;> simp [LRel, h, h.store hi]
  | con a b d =>
    simp only [localPole, renPole, h a, h b]
    cases SkaModel.read a R <;> cases SkaModel.read b R <;> simp [LRel, h.store hi]
  | hed s d =>
    simp only [localPole, renPole, h s]
    cases e : SkaModel.read s R with
    | none => simp [LRel]
    | some v => cases v <;> simp [LRel, h.store hi]
  | tal s d =>
    simp only [localPole, renPole, h s]
    cases e : SkaModel.read s R with
    | none => simp [LRel]
    | some v => cases v <;> simp [LRel, h.store hi]
  | cel q =>
    simp only [localPole, renPole, h q]
    cases e : SkaModel.read q R with
    | none => simp [LRel]
    | some v => cases v <;> simp [LRel, h]
  | lob q =>
    simp only [localPole, renPole, h q]
    cases e : SkaModel.read q R with
    | none => simp [LRel]
    | some v => by_cases hv : v = A 0 ∨ v = A 1 <;> simp [LRel, h, hv]
  | equ a b =>
    simp only [localPole, renPole, h a, h b]
    cases SkaModel.read a R <;> cases SkaModel.read b R <;> simp [LRel, h]
  | hsp n f => simp [localPole, renPole, LRel, h]
  | hse n f => simp [localPole, renPole, LRel, h]
  | hdp n q f =>
    simp only [localPole, renPole, h q]
    split
    · cases SkaModel.read q R <;> simp [LRel, h]
    · simp [LRel, h]
  | hde n q f =>
    simp only [localPole, renPole]
    split
    · cases popTrace t <;> simp [LRel, h]
    · simp [LRel, h]
  | hmp a v f =>
    simp only [localPole, renPole, h.mapM v]
    cases v.mapM (SkaModel.read · R) <;> simp [LRel, h]
  | hme a v f =>
    simp only [localPole, renPole]
    cases popTrace t <;> simp [LRel, h]
  | hcp n f => simp [localPole, renPole, LRel, h]
  | hce n f =>
    simp only [localPole, renPole]
    cases popTrace t <;> simp [LRel, h]
  | spy e q d =>
    simp only [localPole, renPole, h e, h q]
    split
    · simp [LRel, h]
    · cases SkaModel.read e R <;> cases SkaModel.read q R <;> simp only [Option.bind_none, Option.bind_some, LRel]
      rename_i ref pax
      cases lib.slam gul (C ref pax) <;> simp only [Option.bind_none, Option.bind_some, LRel]
      rename_i res
      cases scryDecode res <;> simp only [Option.bind_none, Option.bind_some, LRel]
      rename_i dr
      cases dr <;> simp [LRel, h, h.store hi]
  | nok u f d => simp [localPole, renPole, LRel]
  | cal a v d => simp [localPole, renPole, LRel]
  | caf a v d n => simp [localPole, renPole, LRel]
  | cam a v d k => simp [localPole, renPole, LRel]
  | csl a s d => simp [localPole, renPole, LRel]
  | csf a s d n => simp [localPole, renPole, LRel]
  | csm a s d k => simp [localPole, renPole, LRel]

theorem afterCall_ren (hi : Inj ren) {σ : Type} (st : σ) {R R' : Map Noun} (t : Trace) (d : Nat)
    (h : RenRel ren R R') (ton : Tone) : PRel ren (afterCall st R t d ton) (afterCall st R' t (ren d) ton) := by
  cases ton <;> simp [afterCall, PRel, h, h.store hi]

theorem execPole_local (lib : Lib) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (q : Pole)
    (R : Map Noun) (t : Trace)
    (h1 : ∀ u f d, q ≠ Pole.nok u f d) (h2 : ∀ a v d, q ≠ Pole.cal a v d) (h3 : ∀ a v d n, q ≠ Pole.caf a v d n)
    (h4 : ∀ a v d k, q ≠ Pole.cam a v d k) (h5 : ∀ a s d, q ≠ Pole.csl a s d)
    (h6 : ∀ a s d n, q ≠ Pole.csf a s d n) (h7 : ∀ a s d k, q ≠ Pole.csm a s d k) :
    execPole lib O gul st q R t = (localPole lib gul q R t).map fun (ton, regs', trace') => (ton, regs', trace', st) := by
  cases q with
  | nok u f d => exact absurd rfl (h1 u f d)
  | cal a v d => exact absurd rfl (h2 a v d)
  | caf a v d n => exact absurd rfl (h3 a v d n)
  | cam a v d k => exact absurd rfl (h4 a v d k)
  | csl a s d => exact absurd rfl (h5 a s d)
  | csf a s d n => exact absurd rfl (h6 a s d n)
  | csm a s d k => exact absurd rfl (h7 a s d k)
  | _ => rfl

theorem execPole_ren (hi : Inj ren) (lib : Lib) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (p : Pole)
    {R R' : Map Noun} (t : Trace) (h : RenRel ren R R') :
    PRel ren (execPole lib O gul st p R t) (execPole lib O gul st (renPole ren p) R' t) := by
  have hloc : ∀ q : Pole,
      PRel ren ((localPole lib gul q R t).map fun (ton, regs', trace') => (ton, regs', trace', st))
        ((localPole lib gul (renPole ren q) R' t).map fun (ton, regs', trace') => (ton, regs', trace', st)) := by
    intro q
    have := localPole_ren hi lib gul q t h
    revert this
    cases localPole lib gul q R t <;> cases localPole lib gul (renPole ren q) R' t <;> simp [LRel, PRel]
  cases p with
  | nok u f d =>
    simp only [execPole, renPole, h u, h f]
    cases SkaModel.read u R <;> cases SkaModel.read f R <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vu vf
    cases O.nok st vu vf gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i r; obtain ⟨ton, st'⟩ := r
    cases ton <;> simp [PRel, h, h.store hi]
  | cal a v d =>
    simp only [execPole, renPole, h.mapM v]
    cases v.mapM (SkaModel.read · R) <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vs
    cases O.call st a false vs t gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    exact afterCall_ren hi _ t d h _
  | caf a v d n =>
    simp only [execPole, renPole, h.mapM v]
    cases v.mapM (SkaModel.read · R) <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vs
    cases O.call st a false vs t gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    exact afterCall_ren hi _ t d h _
  | cam a v d k =>
    simp only [execPole, renPole, h.mapM v]
    cases v.mapM (SkaModel.read · R) <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vs
    cases O.call st a false vs t gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    exact afterCall_ren hi _ t d h _
  | csl a s d =>
    simp only [execPole, renPole, h s]
    cases SkaModel.read s R <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vs
    cases O.call st a true [vs] t gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    exact afterCall_ren hi _ t d h _
  | csf a s d n =>
    simp only [execPole, renPole, h s]
    cases SkaModel.read s R <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vs
    cases O.call st a true [vs] t gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    exact afterCall_ren hi _ t d h _
  | csm a s d k =>
    simp only [execPole, renPole, h s]
    cases SkaModel.read s R <;> simp only [Option.bind_none, Option.bind_some, PRel]
    rename_i vs
    cases O.call st a true [vs] t gul <;> simp only [Option.bind_none, Option.bind_some, PRel]
    exact afterCall_ren hi _ t d h _
  | _ =>
    rw [execPole_local, execPole_local]
    · exact hloc _
    all_goals (intros; simp [renPole])

end Ren

/-! ## Blocks under the renaming and the chasing -/

/-- The jumps of a terminator. -/
def finJumps : Termin → List Jmp
  | Termin.clq _ z o => [z, o]
  | Termin.eqq _ _ z o => [z, o]
  | Termin.brn _ z o => [z, o]
  | Termin.brz _ z o => [z, o]
  | Termin.lti _ _ z o => [z, o]
  | Termin.hop t => [t]
  | _ => []

/-- Every block is at a label of at least `1`, and jumps only to labels of
at least `1` below its own. -/
def Down (bl : Map Blob) : Prop :=
  ∀ k b, HoonMap.get bl k = some b → 1 ≤ k ∧ ∀ j ∈ finJumps b.fin, 1 ≤ j.there ∧ j.there < k

/-- A block renamed, with the terminator `fin`. -/
def renB (ren : Nat → Nat) (b : Blob) (fin : Termin) : Blob :=
  ⟨b.par.map ren, b.body.map (renPole ren), fin⟩

/-- `c'` is `c` renamed and chased: `bs` is the map `+chase` reads (the
blocks of `c` with the one at `o` moved to `0`), and each block of `c` at a
label other than `o` that is not bypassed is in `c'`, renamed, with its
terminator chased. -/
structure Sim (c c' : Straight Map) (bs : Map Blob) (ren : Nat → Nat) (o : Nat) : Prop where
  inj : Inj ren
  down : Down c.blocks
  bs_eq : ∀ k, k ≠ 0 → k ≠ o → HoonMap.get bs k = HoonMap.get c.blocks k
  bs_o : HoonMap.get bs o = Option.none
  kept : ∀ k b, HoonMap.get c.blocks k = some b → k ≠ o → bypassable true b = false →
    ∃ fin', chaseFin bs ren b.fin = some fin' ∧ HoonMap.get c'.blocks k = some (renB ren b fin')

theorem bypassable_shape {br : Bool} {b : Blob} (h : bypassable br b = true) :
    ∃ t, b = ⟨[], [], Termin.hop t⟩ := by
  rcases b with ⟨par, body, fin⟩
  cases par <;> cases body <;> cases fin <;> simp [bypassable] at h ⊢

theorem bypassable_false {br : Bool} {b : Blob} (h : bypassable br b = false) : bypassable true b = false := by
  rcases b with ⟨par, body, fin⟩
  cases br
  · cases par <;> cases body <;> cases fin <;> simp_all [bypassable]
  · exact h

section Chase
variable {c c' : Straight Map} {bs : Map Blob} {ren : Nat → Nat} {o : Nat}

theorem chase_spec (hs : Sim c c' bs ren o) (lib : Lib) {σ : Type} (O : Oracle σ) (gul : Noun) :
    ∀ n (j : Jmp) (br : Bool) (j' : Jmp), j.there < n → 1 ≤ j.there → chase bs br j = some j' →
    (∀ st (R : Map Noun) t, goJ lib O c gul st R t j = goJ lib O c gul st R t j') ∧ j'.there ≤ j.there ∧
      j'.there ≠ o ∧ ∃ b', HoonMap.get c.blocks j'.there = some b' ∧ bypassable br b' = false
  | 0, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, j, br, j', hn, h1, hc => by
    rw [chase] at hc
    have ho : j.there ≠ o := fun e => by rw [e, hs.bs_o] at hc; simp at hc
    rw [hs.bs_eq _ (by omega) ho] at hc
    cases hb : HoonMap.get c.blocks j.there with
    | none => rw [hb] at hc; simp at hc
    | some b =>
      rw [hb] at hc
      simp only [Option.bind_eq_bind, Option.bind_some] at hc
      split at hc
      · rename_i t heq
        by_cases hby : bypassable br b = true
        · rw [if_pos hby] at hc
          by_cases ha : j.args = []
          · rw [if_pos ha] at hc
            have hd := (hs.down _ _ hb).2 t (by simp [finJumps, heq])
            obtain ⟨hgo, hle, hno, b', hb', hby'⟩ := chase_spec hs lib O gul n t br j' (by omega) hd.1 hc
            obtain ⟨t', rfl⟩ := bypassable_shape hby
            simp only [Termin.hop.injEq] at heq
            subst heq
            refine ⟨fun st R tr => ?_, by omega, hno, b', hb', hby'⟩
            rw [← hgo]
            simp only [goJ, hb, Option.bind_some, ha]
            exact execBlob_hop _ _ _
          · rw [if_neg ha] at hc; simp at hc
        · rw [if_neg hby] at hc
          cases hc
          exact ⟨fun _ _ _ => rfl, Nat.le_refl _, ho, b, hb, by simpa using hby⟩
      · cases hc
        refine ⟨fun _ _ _ => rfl, Nat.le_refl _, ho, b, hb, ?_⟩
        rename_i hne
        rcases b with ⟨par, body, fin⟩
        cases par <;> cases body <;> cases fin <;> simp_all [bypassable]

/-- The jumps of a terminator go, on related registers, where their chased
renamed jumps go in `c'`. -/
def JGo (lib : Lib) {σ : Type} (O : Oracle σ) (c c' : Straight Map) (gul : Noun) (bs : Map Blob)
    (ren : Nat → Nat) (fin : Termin) : Prop :=
  ∀ j ∈ finJumps fin, ∀ br j', chase bs br j = some j' → ∀ st (R R' : Map Noun) t, RenRel ren R R' →
    goJ lib O c gul st R t j = goJ lib O c' gul st R' t (renJmp ren j')

theorem fin_sim {lib : Lib} {σ : Type} {O : Oracle σ} {gul : Noun} {fin fin' : Termin}
    (hc : chaseFin bs ren fin = some fin') (hj : JGo lib O c c' gul bs ren fin) (st : σ) {R R' : Map Noun}
    (t : Trace) (h : RenRel ren R R') :
    execBlob lib O c gul st R t ⟨[], [], fin⟩ [] = execBlob lib O c' gul st R' t ⟨[], [], fin'⟩ [] := by
  cases fin with
  | clq s z o =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o', ho, rfl⟩ := hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h s]
    cases SkaModel.read s R with
    | none => rfl
    | some v =>
      cases v
      · exact hj o (by simp [finJumps]) true o' ho st R R' t h
      · exact hj z (by simp [finJumps]) true z' hz st R R' t h
  | eqq l r z o =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o', ho, rfl⟩ := hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h l, h r]
    cases SkaModel.read l R with
    | none => rfl
    | some x =>
      cases SkaModel.read r R with
      | none => rfl
      | some y =>
        by_cases e : x = y
        · simp only [Option.bind_eq_bind, Option.bind_some, if_pos e]
          exact hj z (by simp [finJumps]) true z' hz st R R' t h
        · simp only [Option.bind_eq_bind, Option.bind_some, if_neg e]
          exact hj o (by simp [finJumps]) true o' ho st R R' t h
  | brn s z o =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o', ho, rfl⟩ := hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h s]
    cases SkaModel.read s R with
    | none => rfl
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      by_cases e0 : v = A 0
      · simp only [if_pos e0]; exact hj z (by simp [finJumps]) true z' hz st R R' t h
      · by_cases e1 : v = A 1
        · simp only [if_neg e0, if_pos e1]; exact hj o (by simp [finJumps]) true o' ho st R R' t h
        · simp only [if_neg e0, if_neg e1]
  | brz s z o =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨z', hz, o', ho, rfl⟩ := hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h s]
    cases SkaModel.read s R with
    | none => rfl
    | some v =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      by_cases e0 : v = A 0
      · simp only [if_pos e0]; exact hj z (by simp [finJumps]) true z' hz st R R' t h
      · simp only [if_neg e0]; exact hj o (by simp [finJumps]) true o' ho st R R' t h
  | hop j =>
    simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
    obtain ⟨j', hj', rfl⟩ := hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false]
    exact hj j (by simp [finJumps]) false j' hj' st R R' t h
  | jmp a v =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h.mapM v]
  | jmf a v n =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h.mapM v]
  | jsp a s =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h s]
  | jsf a s n =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h s]
  | don s =>
    simp only [chaseFin, Option.some.injEq] at hc; subst hc
    rw [execBlob, execBlob]; simp only [ne_eq, not_true_eq_false, or_self, if_false, h s]
  | bom m =>
    cases m with
    | none =>
      simp only [chaseFin, Option.some.injEq] at hc; subst hc
      rw [execBlob, execBlob]; simp
    | some x =>
      simp only [chaseFin, Option.bind_eq_some_iff, Option.some.injEq] at hc
      obtain ⟨j, _, rfl⟩ := hc
      rw [execBlob, execBlob]; simp
  | lti n s z o => simp [chaseFin] at hc

theorem body_sim {lib : Lib} {σ : Type} {O : Oracle σ} {gul : Noun} (hi : Inj ren) {fin fin' : Termin}
    (hf : ∀ (st : σ) (R R' : Map Noun) t, RenRel ren R R' →
      execBlob lib O c gul st R t ⟨[], [], fin⟩ [] = execBlob lib O c' gul st R' t ⟨[], [], fin'⟩ []) :
    ∀ (body : List Pole) (st : σ) (R R' : Map Noun) t, RenRel ren R R' →
      execBlob lib O c gul st R t ⟨[], body, fin⟩ [] =
        execBlob lib O c' gul st R' t ⟨[], body.map (renPole ren), fin'⟩ []
  | [], st, R, R', t, h => hf st R R' t h
  | p :: rest, st, R, R', t, h => by
    rw [execBlob_cons, List.map_cons, execBlob_cons]
    have := execPole_ren hi lib O gul st p t h
    revert this
    cases execPole lib O gul st p R t <;> cases execPole lib O gul st (renPole ren p) R' t <;>
      simp only [PRel, Option.bind_none, Option.bind_some, imp_self, false_implies]
    rename_i a b
    obtain ⟨ton, R1, t1, st1⟩ := a
    obtain ⟨ton', R1', t1', st1'⟩ := b
    rintro ⟨rfl, rfl, rfl, hR⟩
    cases ton
    · exact body_sim hi hf rest _ _ _ _ hR
    · rfl
    · rfl

/-- **A block and its renamed, chased copy do the same.** -/
theorem sim_block (hs : Sim c c' bs ren o) (lib : Lib) {σ : Type} (O : Oracle σ) (gul : Noun) :
    ∀ k b, HoonMap.get c.blocks k = some b → ∀ fin', chaseFin bs ren b.fin = some fin' →
    ∀ (st : σ) (R R' : Map Noun) t (params : List (Option Nat)), RenRel ren R R' →
    execBlob lib O c gul st R t b params =
      execBlob lib O c' gul st R' t (renB ren b fin') (params.map (Option.map ren)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro b hb fin' hf st R R' t params h
    have hj : JGo lib O c c' gul bs ren b.fin := by
      intro j hjm br j' hc st R R' t h
      have hd := (hs.down k b hb).2 j hjm
      obtain ⟨hgo, hle, hno, b', hb', hby⟩ :=
        chase_spec hs lib O gul (j.there + 1) j br j' (Nat.lt_succ_self _) hd.1 hc
      rw [hgo]
      obtain ⟨fin2, hf2, hc2⟩ := hs.kept _ _ hb' hno (bypassable_false hby)
      simp only [goJ, hb', hc2, Option.bind_some, renJmp]
      exact ih j'.there (by omega) b' hb' fin2 hf2 st R R' t j'.args h
    have hbody := body_sim (lib := lib) (O := O) (gul := gul) hs.inj
      (fun st R R' t h => fin_sim hf hj st t h)
    rcases b with ⟨par, body, fin⟩
    by_cases hp : params ≠ [] ∨ par ≠ []
    · have hp' : params.map (Option.map ren) ≠ [] ∨ par.map ren ≠ [] := by
        simpa [List.map_eq_nil_iff] using hp
      rw [execBlob, execBlob]
      simp only [renB] at hp' ⊢
      simp only [hp, hp', ↓reduceIte]
      have := evalPass_ren hs.inj params par h
      revert this
      cases evalPass params par R <;> cases evalPass (params.map (Option.map ren)) (par.map ren) R' <;>
        simp only [ORel, Option.bind_eq_bind, Option.bind_none, Option.bind_some, imp_self, false_implies]
      intro hR
      exact hbody body st _ _ t hR
    · simp only [not_or, ne_eq, Decidable.not_not] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hbody body st R R' t h

end Chase

end Comp
end SkaModel
end Formalization
