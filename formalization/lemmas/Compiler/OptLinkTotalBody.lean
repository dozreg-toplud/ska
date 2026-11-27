import lemmas.Compiler.OptLinkTotalAlias

/-!
# `+alias` returns: the body of a block

The body of a block is walked from the facts `loc` that the join and the
parameter loop give, with the renaming `old` and the immediates `imml`.
**`aliasBody_inv`**: the body returns once every register an op reads is in
a set `S` of registers whose image under `old` has a fact, or is written by
an earlier op of the body, provided the facts are closed (every register a
fact refers to has a fact, `AClo`), the immediates refer only to registers
with facts (`IClo`), `old` is the identity on the registers the body writes,
and these are written once.  At the end every register of `S` or written by
the body has a fact under the new `old` (so the end's test register has one,
`aliasFin_some`), the facts and the immediates are still closed, no fact is
lost, and `old` changed only on the registers the body writes.

This closes, at the level of one block, the places `O1` .. `O6` of the list
in `OptLinkTotalAlias.lean` (what each op needs is given by the ops before
it), and gives the closure of the facts of a walked block (`W2` of the walk
invariant) from the closure of its start facts.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The registers a fact refers to. -/
def IRef (v : Opt.InfoReg) (x : Nat) : Prop :=
  x ∈ v.hedOf ∨ x ∈ v.telOf ∨ v.hasHed = some x ∨ v.hasTel = some x ∨ v.decOf = some x

/-- **Closed facts**: every register a fact refers to has a fact. -/
def AClo (loc : Opt.AInfo) : Prop := ∀ k v x, loc k = some v → IRef v x → (loc x).isSome

/-- The immediates refer only to registers with facts. -/
def IClo (loc : Opt.AInfo) (im : Opt.AImms) : Prop := ∀ m x, x ∈ im m → (loc x).isSome

/-- **The body invariant** over the registers `S`: their images under `old`
have facts, the facts are closed, the immediates have facts. -/
structure BInv (S : Nat → Prop) (st : Opt.ABody) : Prop where
  av : ∀ r, S r → (st.loc (st.old r)).isSome
  clo : AClo st.loc
  imm : IClo st.loc st.imml

/-- No fact is lost. -/
def KGrow (a b : Opt.AInfo) : Prop := ∀ k, (a k).isSome → (b k).isSome

theorem kgrow_refl (a : Opt.AInfo) : KGrow a a := fun _ h => h

theorem kgrow_trans {a b c : Opt.AInfo} (h1 : KGrow a b) (h2 : KGrow b c) : KGrow a c := fun k h => h2 k (h1 k h)

theorem updA_self {α : Type} (f : Nat → α) (k : Nat) (v : α) : Opt.updA f k v k = v := by simp [Opt.updA]

theorem updA_ne {α : Type} (f : Nat → α) {k k' : Nat} (v : α) (h : k' ≠ k) : Opt.updA f k v k' = f k' := by
  simp [Opt.updA, h]

theorem kgrow_upd (m : Opt.AInfo) (d : Nat) (v : Opt.InfoReg) : KGrow m (Opt.updA m d (some v)) := by
  intro k h; by_cases e : k = d
  · subst e; simp [Opt.updA]
  · rw [updA_ne _ _ e]; exact h

theorem jabA_eq {m m' : Opt.AInfo} {k : Nat} {g : Opt.InfoReg → Opt.InfoReg} (h : Opt.jabA m k g = some m') :
    ∃ v, m k = some v ∧ m' = Opt.updA m k (some (g v)) := by
  simp only [Opt.jabA, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h; exact ⟨v, hv, rfl⟩

theorem jabA_of {m : Opt.AInfo} {k : Nat} {v : Opt.InfoReg} (g : Opt.InfoReg → Opt.InfoReg) (h : m k = some v) :
    Opt.jabA m k g = some (Opt.updA m k (some (g v))) := by
  simp [Opt.jabA, h]

/-- Updating a key with a fact whose references have facts after keeps the
facts closed. -/
theorem aclo_upd {m : Opt.AInfo} {d : Nat} {w : Opt.InfoReg} (hc : AClo m)
    (hw : ∀ x, IRef w x → (Opt.updA m d (some w) x).isSome) : AClo (Opt.updA m d (some w)) := by
  intro k v x hk hx
  by_cases e : k = d
  · subst e; rw [updA_self] at hk; cases hk; exact hw x hx
  · rw [updA_ne _ _ e] at hk; exact kgrow_upd m d w x (hc k v x hk hx)

/-- The same for `+jab`: the new fact refers to what the old one did, or to
registers with facts. -/
theorem aclo_jab {m : Opt.AInfo} {k : Nat} {v : Opt.InfoReg} {g : Opt.InfoReg → Opt.InfoReg} (hc : AClo m)
    (hk : m k = some v) (hg : ∀ x, IRef (g v) x → IRef v x ∨ (m x).isSome) : AClo (Opt.updA m k (some (g v))) := by
  refine aclo_upd hc fun x hx => ?_
  rcases hg x hx with h | h
  · exact kgrow_upd m k _ x (hc k v x hk h)
  · exact kgrow_upd m k _ x h

theorem iclo_grow {m m' : Opt.AInfo} {im : Opt.AImms} (h : IClo m im) (g : KGrow m m') : IClo m' im :=
  fun n x hx => g x (h n x hx)

theorem iref_empty (x : Nat) : ¬ IRef ({} : Opt.InfoReg) x := by
  simp [IRef]

/-- What one op keeps: the new state, the reads given. -/
def OpPost (S : Nat → Prop) (op : Pole) (st : Opt.ABody) (r : Option Pole × Opt.ABody) : Prop :=
  BInv (fun x => S x ∨ Opt.aliasDst op = some x) r.2 ∧ KGrow st.loc r.2.loc ∧
    (∀ x, Opt.aliasDst op ≠ some x → r.2.old x = st.old x)

theorem old_upd_ne {o : Nat → Nat} {d x : Nat} (v : Nat) (h : Opt.aliasDst op ≠ some x) (hd : Opt.aliasDst op = some d) :
    Opt.updA o d v x = o x := by
  have : x ≠ d := fun e => h (e ▸ hd)
  exact updA_ne _ _ this

/-- `old` updated at the destination to a register with a fact. -/
theorem opPost_drop {S : Nat → Prop} {op : Pole} {st : Opt.ABody} {d y : Nat} (hI : BInv S st)
    (hd : Opt.aliasDst op = some d) (hy : (st.loc y).isSome) (p : Option Pole) :
    OpPost S op st (p, { st with old := Opt.updA st.old d y }) := by
  refine ⟨⟨fun x hx => ?_, hI.clo, hI.imm⟩, kgrow_refl _, fun x hx => old_upd_ne y hx hd⟩
  by_cases e : x = d
  · subst e; simp only [updA_self]; exact hy
  · simp only [updA_ne _ _ e]
    rcases hx with hx | hx
    · exact hI.av x hx
    · exact absurd (hd.symm.trans hx) (fun h => e (Option.some.inj h).symm)

/-- A kept op that changes only `loc`, with `old` the identity at its
destination. -/
theorem opPost_loc {S : Nat → Prop} {op : Pole} {st : Opt.ABody} {loc' : Opt.AInfo} (hI : BInv S st)
    (hg : KGrow st.loc loc') (hc : AClo loc')
    (hd : ∀ d, Opt.aliasDst op = some d → st.old d = d ∧ (loc' d).isSome) (p : Option Pole) :
    OpPost S op st (p, { st with loc := loc' }) := by
  refine ⟨⟨fun x hx => ?_, hc, iclo_grow hI.imm hg⟩, hg, fun _ _ => rfl⟩
  rcases hx with hx | hx
  · exact hg _ (hI.av x hx)
  · obtain ⟨e, h⟩ := hd x hx; simp only; rw [e]; exact h

theorem opPost_same {S : Nat → Prop} {op : Pole} {st : Opt.ABody} (hI : BInv S st) (hn : Opt.aliasDst op = none)
    (p : Option Pole) : OpPost S op st (p, st) := by
  refine ⟨⟨fun x hx => ?_, hI.clo, hI.imm⟩, kgrow_refl _, fun _ _ => rfl⟩
  rcases hx with hx | hx
  · exact hI.av x hx
  · rw [hn] at hx; cases hx

theorem opPost_fresh {S : Nat → Prop} {op : Pole} {st : Opt.ABody} {d : Nat} (hI : BInv S st)
    (hd : Opt.aliasDst op = some d) (ho : st.old d = d) (p : Option Pole) :
    OpPost S op st (p, { st with loc := Opt.updA st.loc d (some {}) }) := by
  refine opPost_loc hI (kgrow_upd _ _ _) (aclo_upd hI.clo fun x hx => absurd hx (iref_empty x)) (fun d' hd' => ?_) p
  rw [hd] at hd'; cases hd'; exact ⟨ho, by simp [Opt.updA]⟩

/-- **One op returns and keeps the body invariant.** -/
theorem aliasOp_inv (pick : List Nat → Nat) (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (st : Opt.ABody)
    (op : Pole) {S : Nat → Prop} (hI : BInv S st) (hr : ∀ r ∈ Opt.aliasReads op, S r)
    (hd : ∀ d, Opt.aliasDst op = some d → st.old d = d) :
    ∃ res, Opt.aliasOp pick st op = some res ∧ OpPost S op st res := by
  cases op with
  | imm n d =>
    simp only [Opt.aliasOp]
    by_cases c : st.imml n ≠ []
    · rw [if_pos c]
      exact ⟨_, rfl, opPost_drop hI rfl (hI.imm n _ (hpick _ c)) none⟩
    · rw [if_neg c]
      refine ⟨_, rfl, ⟨⟨fun x hx => ?_, ?_, ?_⟩, kgrow_upd _ _ _, fun _ _ => rfl⟩⟩
      · rcases hx with hx | hx
        · exact kgrow_upd _ _ _ _ (hI.av x hx)
        · simp only [Opt.aliasDst, Option.some.injEq] at hx; subst hx; rw [hd _ rfl]; simp [Opt.updA]
      · exact aclo_upd hI.clo fun x hx => by simp [IRef] at hx
      · intro m x hx
        simp only at hx
        split at hx
        · simp only [Opt.insN] at hx
          split at hx
          · exact kgrow_upd _ _ _ _ (hI.imm m x hx)
          · rcases List.mem_cons.1 hx with e | hx
            · rw [e]; simp [Opt.updA]
            · exact kgrow_upd _ _ _ _ (hI.imm m x hx)
        · exact kgrow_upd _ _ _ _ (hI.imm m x hx)
  | mov s d =>
    have hs := hr s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d)
    exact ⟨_, rfl, opPost_drop hI rfl (hI.av s hs) none⟩
  | inc s d =>
    have hs := hI.av s (hr s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d))
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    cases hdec : ai.decOf with
    | some x =>
      refine ⟨_, rfl, opPost_drop hI rfl (hI.clo _ ai x hai ?_) none⟩
      simp [IRef, hdec]
    | none =>
      have h1 : (Opt.updA st.loc d (some {}) (st.old s)).isSome := kgrow_upd _ _ _ _ hs
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1
      rw [jabA_of _ hv]
      refine ⟨_, rfl, opPost_loc hI (kgrow_trans (kgrow_upd _ d _) (kgrow_upd _ _ _)) ?_ ?_ _⟩
      · have c0 : AClo (Opt.updA st.loc d (some {})) := aclo_upd hI.clo fun x hx => absurd hx (iref_empty x)
        refine aclo_jab (g := fun i => { i with decOf := some d }) c0 hv fun x hx => ?_
        simp only [IRef] at hx ⊢
        rcases hx with h | h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · cases h; exact Or.inr (by simp [Opt.updA])
      · intro d' hd'; simp only [Opt.aliasDst, Option.some.injEq] at hd'; subst hd'
        exact ⟨hd _ rfl, kgrow_upd _ _ _ _ (by simp [Opt.updA])⟩
  | con h t d =>
    have hm := mem_erase3 h t d
    have h1 := hI.av h (hr h (by simp only [Opt.aliasReads, Opt.aliasDst]; exact hm.1))
    have h2 := hI.av t (hr t (by simp only [Opt.aliasReads, Opt.aliasDst]; exact hm.2))
    obtain ⟨hi, ehi⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨ti, eti⟩ := Option.isSome_iff_exists.1 h2
    simp only [Opt.aliasOp, ehi, eti, Option.bind_some]
    split
    · rename_i c
      have hm' := List.mem_filter.1 (hpick _ c)
      refine ⟨_, rfl, opPost_drop hI rfl (hI.clo _ hi _ ehi ?_) none⟩
      exact Or.inl hm'.1
    · rename_i c
      let w : Opt.InfoReg := { hasHed := some (st.old h), hasTel := some (st.old t), isCell := true }
      have c0 : AClo (Opt.updA st.loc d (some w)) := aclo_upd hI.clo fun x hx => by
        simp only [IRef, w] at hx
        rcases hx with hx | hx | hx | hx | hx
        · cases hx
        · cases hx
        · cases hx; exact kgrow_upd _ _ _ _ h1
        · cases hx; exact kgrow_upd _ _ _ _ h2
        · cases hx
      obtain ⟨v1, ev1⟩ := Option.isSome_iff_exists.1 (kgrow_upd st.loc d w _ h1)
      rw [jabA_of _ ev1, Option.bind_some]
      have g1 := kgrow_trans (kgrow_upd st.loc d w) (kgrow_upd _ (st.old h) ({ v1 with hedOf := Opt.insN v1.hedOf d }))
      obtain ⟨v2, ev2⟩ := Option.isSome_iff_exists.1 (g1 _ h2)
      rw [jabA_of _ ev2]
      have dd : (Opt.updA st.loc d (some w) d).isSome := by simp [Opt.updA]
      have c1 : AClo (Opt.updA (Opt.updA st.loc d (some w)) (st.old h) (some { v1 with hedOf := Opt.insN v1.hedOf d })) :=
        aclo_jab (g := fun i => { i with hedOf := Opt.insN i.hedOf d }) c0 ev1 fun x hx => by
          simp only [IRef, Opt.insN] at hx ⊢
          rcases hx with hx | hx | hx | hx | hx
          · split at hx
            · exact Or.inl (Or.inl hx)
            · rcases List.mem_cons.1 hx with e | hx
              · rw [e]; exact Or.inr dd
              · exact Or.inl (Or.inl hx)
          · exact Or.inl (Or.inr (Or.inl hx))
          · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))
      refine ⟨_, rfl, opPost_loc hI (kgrow_trans g1 (kgrow_upd _ _ _)) ?_ ?_ _⟩
      · refine aclo_jab (g := fun i => { i with telOf := Opt.insN i.telOf d }) c1 ev2 fun x hx => ?_
        simp only [IRef, Opt.insN] at hx ⊢
        rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · split at hx
          · exact Or.inl (Or.inr (Or.inl hx))
          · rcases List.mem_cons.1 hx with e | hx
            · rw [e]; exact Or.inr (kgrow_upd _ _ _ _ dd)
            · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hx))))
      · intro d' hd'; simp only [Opt.aliasDst, Option.some.injEq] at hd'; subst hd'
        exact ⟨hd _ rfl, kgrow_upd _ _ _ _ (kgrow_upd _ _ _ _ dd)⟩
  | hed s d =>
    have hs := hI.av s (hr s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d))
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    cases hh : ai.hasHed with
    | some x =>
      refine ⟨_, rfl, opPost_drop hI rfl (hI.clo _ ai x hai ?_) none⟩
      simp [IRef, hh]
    | none =>
      let w : Opt.InfoReg := { hedOf := [st.old s] }
      have c0 : AClo (Opt.updA st.loc d (some w)) := aclo_upd hI.clo fun x hx => by
        simp only [IRef, w] at hx
        rcases hx with hx | hx | hx | hx | hx
        · simp only [List.mem_singleton] at hx; subst hx; exact kgrow_upd _ _ _ _ hs
        · cases hx
        · cases hx
        · cases hx
        · cases hx
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (kgrow_upd st.loc d w _ hs)
      rw [jabA_of _ hv]
      refine ⟨_, rfl, opPost_loc hI (kgrow_trans (kgrow_upd _ d _) (kgrow_upd _ _ _)) ?_ ?_ _⟩
      · refine aclo_jab (g := fun i => { i with hasHed := some d }) c0 hv fun x hx => ?_
        simp only [IRef] at hx ⊢
        rcases hx with h | h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · cases h; exact Or.inr (by simp [Opt.updA])
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · intro d' hd'; simp only [Opt.aliasDst, Option.some.injEq] at hd'; subst hd'
        exact ⟨hd _ rfl, kgrow_upd _ _ _ _ (by simp [Opt.updA])⟩
  | tal s d =>
    have hs := hI.av s (hr s (by simp only [Opt.aliasReads, Opt.aliasDst]; exact mem_erase2 s d))
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    cases hh : ai.hasTel with
    | some x =>
      refine ⟨_, rfl, opPost_drop hI rfl (hI.clo _ ai x hai ?_) none⟩
      simp [IRef, hh]
    | none =>
      let w : Opt.InfoReg := { telOf := [st.old s] }
      have c0 : AClo (Opt.updA st.loc d (some w)) := aclo_upd hI.clo fun x hx => by
        simp only [IRef, w] at hx
        rcases hx with hx | hx | hx | hx | hx
        · cases hx
        · simp only [List.mem_singleton] at hx; subst hx; exact kgrow_upd _ _ _ _ hs
        · cases hx
        · cases hx
        · cases hx
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (kgrow_upd st.loc d w _ hs)
      rw [jabA_of _ hv]
      refine ⟨_, rfl, opPost_loc hI (kgrow_trans (kgrow_upd _ d _) (kgrow_upd _ _ _)) ?_ ?_ _⟩
      · refine aclo_jab (g := fun i => { i with hasTel := some d }) c0 hv fun x hx => ?_
        simp only [IRef] at hx ⊢
        rcases hx with h | h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
        · cases h; exact Or.inr (by simp [Opt.updA])
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · intro d' hd'; simp only [Opt.aliasDst, Option.some.injEq] at hd'; subst hd'
        exact ⟨hd _ rfl, kgrow_upd _ _ _ _ (by simp [Opt.updA])⟩
  | cel p =>
    have hs := hI.av p (hr p (by simp [Opt.aliasReads, Opt.aliasDst, Opt.poleRegs]))
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · exact ⟨_, rfl, opPost_same hI rfl _⟩
    · rw [jabA_of _ hai]
      refine ⟨_, rfl, opPost_loc (op := Pole.cel p) hI (kgrow_upd _ _ _) (aclo_jab (g := fun i => { i with isCell := true }) hI.clo hai fun x hx => Or.inl hx) (fun d hd => by cases hd) _⟩
  | lob p =>
    have hs := hI.av p (hr p (by simp [Opt.aliasReads, Opt.aliasDst, Opt.poleRegs]))
    obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.1 hs
    simp only [Opt.aliasOp, hai, Option.bind_some]
    split
    · exact ⟨_, rfl, opPost_same hI rfl _⟩
    · rw [jabA_of _ hai]
      refine ⟨_, rfl, opPost_loc (op := Pole.lob p) hI (kgrow_upd _ _ _) (aclo_jab (g := fun i => { i with isLoob := true }) hI.clo hai fun x hx => Or.inl hx) (fun d hd => by cases hd) _⟩
  | equ l r =>
    simp only [Opt.aliasOp]; split
    · exact ⟨_, rfl, opPost_same hI rfl _⟩
    · exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hsp n f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hse n f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hdp n p f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hde n p f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hmp a v f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hme a v f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hcp n f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | hce n f => exact ⟨_, rfl, opPost_same hI rfl _⟩
  | spy e p d => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | nok u f d => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | cal a v d => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | caf a v d n => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | cam a v d k => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | csl a s d => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | csf a s d n => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩
  | csm a s d k => exact ⟨_, rfl, opPost_fresh hI rfl (hd d rfl) _⟩

theorem bInv_mono {S T : Nat → Prop} {st : Opt.ABody} (h : BInv S st) (hT : ∀ x, T x → S x) : BInv T st :=
  ⟨fun r hr => h.av r (hT r hr), h.clo, h.imm⟩

theorem dsts_cons (op : Pole) (l : List Pole) :
    (op :: l).filterMap Opt.aliasDst = (Opt.aliasDst op).toList ++ l.filterMap Opt.aliasDst := by
  cases h : Opt.aliasDst op <;> simp [List.filterMap_cons, h]

/-- **The body returns and keeps the body invariant**: every register an op
reads is in `S` or written by an earlier op, `old` is the identity on the
registers the body writes, and these are written once. -/
theorem aliasBody_inv (pick : List Nat → Nat) (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) :
    ∀ (ops : List Pole) (st : Opt.ABody) (S : Nat → Prop), BInv S st →
    (∀ i op, ops[i]? = some op → ∀ r ∈ Opt.aliasReads op, S r ∨ r ∈ (ops.take i).filterMap Opt.aliasDst) →
    (∀ d ∈ ops.filterMap Opt.aliasDst, st.old d = d) → (ops.filterMap Opt.aliasDst).Nodup →
    ∃ res, Opt.aliasBody pick ops st = some res ∧ BInv (fun x => S x ∨ x ∈ ops.filterMap Opt.aliasDst) res.2 ∧
      KGrow st.loc res.2.loc ∧ (∀ x, x ∉ ops.filterMap Opt.aliasDst → res.2.old x = st.old x)
  | [], st, S, hI, _, _, _ =>
    ⟨([], st), rfl, bInv_mono hI fun x hx => hx.elim id (fun h => by cases h), kgrow_refl _, fun _ _ => rfl⟩
  | op :: l, st, S, hI, hr, hold, hnd => by
    rw [dsts_cons] at hold hnd
    have hr0 : ∀ r ∈ Opt.aliasReads op, S r := fun r hr' => by
      rcases hr 0 op rfl r hr' with h | h
      · exact h
      · simp at h
    have hd0 : ∀ d, Opt.aliasDst op = some d → st.old d = d := fun d hd =>
      hold d (List.mem_append_left _ (by simp [hd]))
    obtain ⟨r1, e1, P1, g1, o1⟩ := aliasOp_inv pick hpick st op hI hr0 hd0
    have hnd' := (List.nodup_append.1 hnd)
    have hr' : ∀ i op', l[i]? = some op' → ∀ r ∈ Opt.aliasReads op',
        (S r ∨ Opt.aliasDst op = some r) ∨ r ∈ (l.take i).filterMap Opt.aliasDst := by
      intro i op' hi r hr'
      rcases hr (i + 1) op' (by simpa using hi) r hr' with h | h
      · exact Or.inl (Or.inl h)
      · rw [List.take_succ_cons, dsts_cons] at h
        rcases List.mem_append.1 h with h | h
        · exact Or.inl (Or.inr (by cases e : Opt.aliasDst op <;> simp_all))
        · exact Or.inr h
    have hold' : ∀ d ∈ l.filterMap Opt.aliasDst, r1.2.old d = d := by
      intro d hd
      have hne : Opt.aliasDst op ≠ some d := fun e => hnd'.2.2 d (by simp [e]) d hd rfl
      rw [o1 d hne]; exact hold d (List.mem_append_right _ hd)
    obtain ⟨r2, e2, P2, g2, o2⟩ := aliasBody_inv pick hpick l r1.2 _ P1 hr' hold' hnd'.2.1
    refine ⟨(r1.1.toList ++ r2.1, r2.2), by simp only [Opt.aliasBody, e1, Option.bind_some, e2, Option.map_some],
      bInv_mono P2 fun x hx => ?_, kgrow_trans g1 g2, fun x hx => ?_⟩
    · rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · rw [dsts_cons] at hx
        rcases List.mem_append.1 hx with h | h
        · exact Or.inl (Or.inr (by cases e : Opt.aliasDst op <;> simp_all))
        · exact Or.inr h
    · rw [dsts_cons] at hx
      have h1 : x ∉ l.filterMap Opt.aliasDst := fun h => hx (List.mem_append_right _ h)
      have h2 : Opt.aliasDst op ≠ some x := fun e => hx (List.mem_append_left _ (by simp [e]))
      rw [o2 x h1, o1 x h2]

end Compiler
end Formalization
