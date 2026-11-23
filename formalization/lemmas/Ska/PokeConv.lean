import lemmas.Ska.ConvAna

/-!
# The poke's code table from the converged graph

`+ska-poke` builds its code table from the pruned graph (`+prune-callgraph`:
the functions the root reaches through the callees), not from the whole final
graph of `+ska-callgraph`.  The frozen entries' answers come from their
callees (`FrozenOK`), so the frozen entries of pruned identities answer each
other: `skaCallgraph_prunedM` is `ConvergedGraphM` for them.

Across pokes, the code table is the one of the earlier pokes with the datums
of this poke added under the bells it does not have yet (`extendCode`, as
`new-code` of `+ska-poke` keeps the entry of a variant seen before).  `PokeInv` is what a poke
keeps of the persistent memo and of that table, and `skaPoke_sound` is the
analysis part of a poke: from `Ana.skaPoke ... = some ...` and `PokeInv`
before it, every bell of the poke's datums agrees with `+mink`, and
`PokeInv` holds after it.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## `+prune-callgraph` -/

theorem inCallees_mem {cs : M CalleeEntry Unit} {c : Ident} (h : InCallees cs c) :
    c ∈ (Treap.tap cs).map (·.1.id) := by
  obtain ⟨seat, hs⟩ := h
  obtain ⟨v, hv⟩ := (Treap.has_iff _ _).mp hs
  exact List.mem_map.mpr ⟨(⟨seat, c⟩, v), (Treap.mem_tap _ _ _).mpr hv, rfl⟩

/-- What the loop of `+prune-callgraph` keeps: its output is part of the
graph, holds what it held and the queue, and is closed under callees. -/
theorem pruneLoop_spec (g : Callgraph M) : ∀ (n : Nat) (q : List Ident) (out out' : Callgraph M),
    pruneLoop g n q out = some out' →
    (∀ i d, Treap.get out i = some d → Treap.get g i = some d) →
    (∀ i d, Treap.get out i = some d → ∀ c, InCallees d.callees c → Treap.has out c = true ∨ c ∈ q) →
    (∀ i d, Treap.get out' i = some d → Treap.get g i = some d) ∧
    (∀ i, Treap.has out i = true → Treap.has out' i = true) ∧
    (∀ c ∈ q, Treap.has out' c = true) ∧
    (∀ i d, Treap.get out' i = some d → ∀ c, InCallees d.callees c → Treap.has out' c = true)
  | 0, _, _, _, h, _, _ => by simp [pruneLoop] at h
  | _ + 1, [], out, out', h, hsub, hcl => by
    simp only [pruneLoop, Option.some.injEq] at h
    subst h
    refine ⟨hsub, fun _ h => h, fun c hc => by simp at hc, fun i d hd c hc => ?_⟩
    rcases hcl i d hd c hc with h | h
    · exact h
    · simp at h
  | n + 1, i :: q, out, out', h, hsub, hcl => by
    unfold pruneLoop at h
    split at h
    · rename_i hi
      obtain ⟨a1, a2, a3, a4⟩ := pruneLoop_spec g n q out out' h hsub (fun j d hd c hc => by
        rcases hcl j d hd c hc with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hi
          · exact Or.inr h)
      refine ⟨a1, a2, fun c hc => ?_, a4⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact a2 _ hi
      · exact a3 c hc
    · cases hgi : Treap.get g i with
      | none => rw [hgi] at h; cases h
      | some d =>
        rw [hgi] at h
        simp only [Option.bind_some] at h
        have hputHas : ∀ j, Treap.has (Treap.put out i d) j = true ↔ j = i ∨ Treap.has out j = true := by
          intro j; simp only [Treap.has_iff, Treap.get_put]; split <;> simp_all
        obtain ⟨a1, a2, a3, a4⟩ := pruneLoop_spec g n _ _ out' h
          (fun j dj hj => by
            rw [Treap.get_put] at hj
            split at hj
            · rename_i e; cases hj; rw [e]; exact hgi
            · exact hsub j dj hj)
          (fun j dj hj c hc => by
            rw [Treap.get_put] at hj
            split at hj
            · cases hj; exact Or.inr (List.mem_append_right _ (inCallees_mem hc))
            · rcases hcl j dj hj c hc with h | h
              · exact Or.inl ((hputHas c).mpr (Or.inr h))
              · rcases List.mem_cons.mp h with rfl | h
                · exact Or.inl ((hputHas _).mpr (Or.inl rfl))
                · exact Or.inr (List.mem_append_left _ h))
        refine ⟨a1, fun j hj => a2 j ((hputHas j).mpr (Or.inr hj)), fun c hc => ?_, a4⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact a2 _ ((hputHas _).mpr (Or.inl rfl))
        · exact a3 c (List.mem_append_left _ hc)

/-- **`+prune-callgraph`**: the pruned graph is part of the graph, holds the
root, and is closed under callees. -/
theorem pruneCallgraph_spec {n : Nat} {g pruned : Callgraph M} {root : Ident}
    (h : pruneCallgraph n g root = some pruned) :
    (∀ i d, Treap.get pruned i = some d → Treap.get g i = some d) ∧ Treap.has pruned root = true ∧
    (∀ i d, Treap.get pruned i = some d → ∀ c, InCallees d.callees c → Treap.has pruned c = true) := by
  obtain ⟨a1, _, a3, a4⟩ := pruneLoop_spec g n [root] Treap.empty pruned h
    (fun i d hd => by simp [Treap.get_empty] at hd) (fun i d hd => by simp [Treap.get_empty] at hd)
  exact ⟨a1, a3 root (List.mem_singleton_self _), a4⟩

/-! ## The `~(rep by pruned)` of `+ska-poke` -/

/-- One turn of the fold of `pokeMemo`. -/
def pokeStep (acc : M Bell (FDatum M) × Memo M) (e : Ident × FDatum M) : M Bell (FDatum M) × Memo M :=
  (Treap.put acc.1 ⟨e.2.less, e.1.2⟩ e.2,
   let me := memoFinalEntry e.1 e.2
   putMi acc.2 me.1 me.2)

theorem pokeMemo_eq (pruned : Callgraph M) (memo : Memo M) :
    pokeMemo pruned memo = (Treap.rap pruned).foldl pokeStep (Treap.empty, memo) := rfl

theorem pokeFold_spec : ∀ (l : List (Ident × FDatum M)) (acc : M Bell (FDatum M) × Memo M),
    (∀ bl d, Treap.get (l.foldl pokeStep acc).1 bl = some d →
      Treap.get acc.1 bl = some d ∨ ∃ e ∈ l, e.2 = d ∧ bl = ⟨d.less, e.1.2⟩) ∧
    (∀ bl, (Treap.get acc.1 bl).isSome → (Treap.get (l.foldl pokeStep acc).1 bl).isSome) ∧
    (∀ e ∈ l, (Treap.get (l.foldl pokeStep acc).1 ⟨e.2.less, e.1.2⟩).isSome) ∧
    (∀ f ms s ent, Treap.get (l.foldl pokeStep acc).2 f = some ms → Treap.get ms s = some ent →
      (∃ ms', Treap.get acc.2 f = some ms' ∧ Treap.get ms' s = some ent) ∨
      (∃ e ∈ l, ent = memoFinalEntry e.1 e.2 ∧ f = e.1.2))
  | [], acc => ⟨fun _ _ h => Or.inl h, fun _ h => h, fun _ h => by simp at h,
      fun _ ms _ _ h1 h2 => Or.inl ⟨ms, h1, h2⟩⟩
  | e :: l, acc => by
    obtain ⟨a1, a2, a3, a4⟩ := pokeFold_spec l (pokeStep acc e)
    simp only [List.foldl_cons]
    refine ⟨fun bl d hd => ?_, fun bl hb => a2 bl ?_, fun e' he' => ?_, fun f ms s ent h1 h2 => ?_⟩
    · rcases a1 bl d hd with h | ⟨e', he', h1, h2⟩
      · simp only [pokeStep, Treap.get_put] at h
        split at h
        · rename_i hk; cases h; exact Or.inr ⟨e, List.mem_cons_self, rfl, hk⟩
        · exact Or.inl h
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩
    · simp only [pokeStep, Treap.get_put]
      split
      · rfl
      · exact hb
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact a2 _ (by simp [pokeStep, Treap.get_put])
      · exact a3 e' he'
    · rcases a4 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨e', he', h3, h4⟩
      · rcases putMi_get e1 e2 with h | ⟨h3, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨e, List.mem_cons_self, h3, h4⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h3, h4⟩

/-- **What `pokeMemo` makes**: the datums by bell are the pruned entries under
their bells, every pruned entry's bell has one, and the new memo's entries
are the old memo's or the `+memo-final-entry` of pruned entries. -/
theorem pokeMemo_spec (pruned : Callgraph M) (memo : Memo M) :
    (∀ bl d, Treap.get (pokeMemo pruned memo).1 bl = some d →
      ∃ i, Treap.get pruned i = some d ∧ bl = ⟨d.less, i.2⟩) ∧
    (∀ i d, Treap.get pruned i = some d → (Treap.get (pokeMemo pruned memo).1 ⟨d.less, i.2⟩).isSome) ∧
    (∀ f ms s ent, Treap.get (pokeMemo pruned memo).2 f = some ms → Treap.get ms s = some ent →
      (∃ ms', Treap.get memo f = some ms' ∧ Treap.get ms' s = some ent) ∨
      (∃ i d, Treap.get pruned i = some d ∧ ent = memoFinalEntry i d ∧ f = i.2)) := by
  rw [pokeMemo_eq]
  obtain ⟨a1, _, a3, a4⟩ := pokeFold_spec (Treap.rap pruned) (Treap.empty, memo)
  refine ⟨fun bl d hd => ?_, fun i d hd => a3 (i, d) ((Treap.mem_rap _ _ _).mpr hd), fun f ms s ent h1 h2 => ?_⟩
  · rcases a1 bl d hd with h | ⟨e, he, rfl, rfl⟩
    · simp [Treap.get_empty] at h
    · exact ⟨e.1, (Treap.mem_rap _ _ _).mp he, rfl⟩
  · rcases a4 f ms s ent h1 h2 with h | ⟨e, he, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨e.1, e.2, (Treap.mem_rap _ _ _).mp he, h3, h4⟩

/-! ## Convergence on the pruned graph -/

/-- **The pruned entries are converged among themselves**: the frozen entries
of pruned identities form a `ConvergedGraphM` (their answers come from their
callees, which the pruned graph holds), for a memo whose entries are sound
for `code` and a root whose subject sock is not `%void`.  The pruned
identities, code requirements and products have normal capes, for a root and
memo entries that have. -/
theorem skaCallgraph_prunedM {lib : Lib} {code : Bell → Option Nomm} (env : Env R) (memoF : Memo M)
    (hmF : MemoWF memoF) (hmN : MemoNorm memoF) (hkey : MemoKeys memoF)
    (hok : ∀ m, MemEnt memoF m → MemoEntryOK lib code m)
    {n n' : Nat} {root : Ident} {reg reg' : R} {g pruned : Callgraph M} (hw : WellFormed root.1)
    (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void) (h : skaCallgraph env n root memoF reg = some (g, reg'))
    (hp : pruneCallgraph n' g root = some pruned) :
    ∃ G : Entry → Prop, ConvergedGraphM lib code (MemEnt memoF) G ∧
      (∀ i d, Treap.get pruned i = some d → G (entOf i d)) ∧
      (∀ e, G e → ∃ d, Treap.get pruned (e.more, e.fol) = some d ∧ e.d.less = d.less) ∧
      (∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod) ∧
      (∀ i d, Treap.get pruned i = some d → NormSock i.1 ∧ NormSock d.less ∧ NormSock d.prod) := by
  obtain ⟨F, hok', hcov, hsub, hwfp, hs, hnv, hnorm⟩ := skaCallgraph_frozen env memoF hmF hmN hw hnr hnvr h
  obtain ⟨psub, _, pcl⟩ := pruneCallgraph_spec hp
  have hgw := graphWF_stepsR hs graphWF_empty
  let G : Entry → Prop := fun e => F e ∧ Treap.has pruned (e.more, e.fol) = true
  have hGp : ∀ e, G e → ∃ d, Treap.get pruned (e.more, e.fol) = some d ∧ e.d.less = d.less := by
    intro e he
    obtain ⟨d, hd⟩ := (Treap.has_iff _ _).mp he.2
    obtain ⟨d', hd', hl⟩ := hsub e he.1
    rw [psub _ _ hd] at hd'; cases hd'
    exact ⟨d, hd, hl⟩
  refine ⟨G, fun e he => ?_, fun i d hd => ⟨hcov i d (psub i d hd), (Treap.has_iff _ _).mpr ⟨d, hd⟩⟩, hGp,
    fun e he => ?_, fun i d hd => hnorm i d (psub i d hd)⟩
  · obtain ⟨d, hd, _⟩ := hGp e he
    rcases hok' e he.1 with ⟨P, hP, hr⟩ | hm
    · refine Or.inl ⟨P, fun s f a hp => answers_mono (fun e' he' => ⟨he'.1, ?_⟩) (hP s f a hp), hr⟩
      have h2 : InCallees (gitG g (e.more, e.fol)).callees (e'.more, e'.fol) := he'.2
      have hgit : gitG g (e.more, e.fol) = d := by simp [gitG, Treap.gut, psub _ _ hd]
      rw [hgit] at h2
      exact pcl _ d hd _ h2
    · exact Or.inr (memoHit_hitEntry hkey hok (hnv _ d (psub _ _ hd)) hm)
  · obtain ⟨d, hd, _⟩ := hGp e he
    exact ⟨(hgw _ _ (show gCore g (e.more, e.fol) = some d.core by simp [gCore, psub _ _ hd])).1, hwfp e he.1⟩

/-! ## A poke -/

/-- The code table after a poke: the table `code` of the earlier pokes, and
the datums of the poke under the bells it does not have (a bell seen before
keeps its entry, as in `new-code` of `+ska-poke`). -/
def extendCode (code : Bell → Option Nomm) (dats : M Bell (FDatum M)) : Bell → Option Nomm := fun bl =>
  match code bl with
  | some nb => some nb
  | none => (Treap.get dats bl).map (·.nomm)

/-- **The invariant across pokes** of the persistent memo `memo` and of the
code table `code` of the earlier pokes: the memo's entries are stored under
their formulas, their bells have code, they are sound for the table, and
every bell's nomm satisfies `Annot` on the bell's code requirement. -/
structure PokeInv (lib : Lib) (memo : Memo M) (code : Bell → Option Nomm) : Prop where
  keys : MemoKeys memo
  bells : ∀ m, MemEnt memo m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb
  ok : ∀ m, MemEnt memo m → MemoEntryOK lib code m
  codeOK : CodeOK lib code
  /-- The memo's code requirements and products have normal capes. -/
  norm : ∀ m, MemEnt memo m → NormSock m.d.less ∧ NormSock m.d.prod
  /-- Every bell of the table has a normal cape. -/
  bellNorm : ∀ bl nb, code bl = some nb → NormSock bl.less
  /-- The memo's nomms have no `%10` at axis `0`, and its code requirements
  and products have nouns (`MemoDat`), as `+bake-graph` needs of `dat`. -/
  dat : MemoDat memo

theorem PokeInv.wf {lib : Lib} {memo : Memo M} {code : Bell → Option Nomm} (h : PokeInv lib memo code) :
    MemoWF memo := fun f ms s e h1 h2 => (h.ok _ ⟨f, ms, s, e, h1, h2, rfl⟩).wf

theorem PokeInv.memoNorm {lib : Lib} {memo : Memo M} {code : Bell → Option Nomm} (h : PokeInv lib memo code) :
    MemoNorm memo := fun f ms s e h1 h2 => h.norm _ ⟨f, ms, s, e, h1, h2, rfl⟩

/-- **Every bell of a table that satisfies `PokeInv` agrees with `+mink`** on
every subject that fits it. -/
theorem PokeInv.agree {lib : Lib} {memo : Memo M} {code : Bell → Option Nomm} (h : PokeInv lib memo code)
    {bl : Bell} {nb : Nomm} (hb : code bl = some nb) {x : Noun} (hx : Fits bl.less x) (gul : Noun) (t : Trace)
    (r : Tone) : Mink lib gul t x bl.fol r ↔ ∃ m, nommF lib gul code m t x nb = some r :=
  nomm_agree lib gul code h.codeOK (h.codeOK bl nb hb) hx t r

/-- Before the first poke: an empty memo and an empty table. -/
theorem PokeInv.init (lib : Lib) : PokeInv lib (Treap.empty : Memo M) (fun _ => none) where
  keys := fun f ms s ent h _ => by simp [Treap.get_empty] at h
  bells := fun _ ⟨_, _, _, _, h, _⟩ => by simp [Treap.get_empty] at h
  ok := fun _ ⟨_, _, _, _, h, _⟩ => by simp [Treap.get_empty] at h
  codeOK := fun _ _ h => by cases h
  norm := fun _ ⟨_, _, _, _, h, _⟩ => by simp [Treap.get_empty] at h
  bellNorm := fun _ _ h => by cases h
  dat := fun _ _ _ _ h _ => by simp [Treap.get_empty] at h

theorem _root_.Formalization.SkaModel.MemoEntryOK.mono_code {lib : Lib} {code code' : Bell → Option Nomm}
    (hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb') {m : Entry} (h : MemoEntryOK lib code m) :
    MemoEntryOK lib code' m where
  wf := h.wf
  prov := h.prov
  annot := h.annot.mono_code hcc

theorem extendCode_has {code : Bell → Option Nomm} {dats : M Bell (FDatum M)} :
    ∀ bl nb, code bl = some nb → ∃ nb', extendCode code dats bl = some nb' := by
  intro bl nb h
  unfold extendCode
  rw [h]
  exact ⟨nb, rfl⟩

/-- **The analysis part of a poke is sound.**  If `Ana.skaPoke` returns, on
a root with a well-formed subject sock and from a memo and code table that
satisfy `PokeInv`, then every bell of the poke's datums `dats` agrees with
`+mink` on every subject that fits it, run with the code table of the earlier
pokes extended by `dats`, and `PokeInv` holds of the new memo and that table
(so every bell of that table has a normal cape, as the compilation of a bell
assumes).

Termination is not part of this: `Ana.skaPoke` is fuelled, and the statement
is about every fuel that is enough for it to return (`some`).  The root's
subject sock is well formed, normal and not `%void` (the root of
`+ska-poke` is `[bus fol]` with `bus` from the caller, `&+sub` for a whole
subject, which is all three). -/
theorem skaPoke_sound {lib : Lib} (env : Env R) {n : Nat} {root : Ident} {memo memo' : Memo M} {reg reg' : R}
    {code : Bell → Option Nomm} {pruned : Callgraph M} {dats : M Bell (FDatum M)} {rd : FDatum M}
    (hinv : PokeInv lib memo code) (hw : WellFormed root.1) (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void)
    (h : skaPoke env n root memo reg = some (pruned, dats, memo', rd, reg')) :
    PokeInv lib memo' (extendCode code dats) ∧
    ∀ bl d, Treap.get dats bl = some d → ∀ x, Fits bl.less x → ∀ gul t r,
      (Mink lib gul t x bl.fol r ↔ ∃ m, nommF lib gul (extendCode code dats) m t x d.nomm = some r) := by
  unfold skaPoke at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨g, regG⟩, hg, pr, hpr, rd', _, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, hdats, hmemo, _, _⟩ := he
  subst hdats hmemo
  generalize hcd : extendCode code (pokeMemo pr memo).1 = code'
  have hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb' := by
    rw [← hcd]; exact extendCode_has
  have hok' : ∀ m, MemEnt memo m → MemoEntryOK lib code' m := fun m hm => (hinv.ok m hm).mono_code hcc
  obtain ⟨G, hG, hcovP, hGp, hwfG, hnP⟩ := skaCallgraph_prunedM (lib := lib) (code := code') env memo hinv.wf
    hinv.memoNorm hinv.keys hok' hw hnr hnvr hg hpr
  obtain ⟨d1, d2, d3⟩ := pokeMemo_spec pr memo
  have hdat : ∀ i d, Treap.get pr i = some d → ∃ nb, code' ⟨d.less, i.2⟩ = some nb := by
    intro i d hd
    rw [← hcd]
    unfold extendCode
    have := d2 i d hd
    split
    · exact ⟨_, rfl⟩
    · cases hn : Treap.get (pokeMemo pr memo).1 ⟨d.less, i.2⟩ with
      | none => rw [hn] at this; cases this
      | some d' => exact ⟨d'.nomm, rfl⟩
  have hhas : CodeHas code' G := by
    intro e he
    obtain ⟨d, hd, hl⟩ := hGp e he
    rw [hl]
    exact hdat _ d hd
  have hwf1 : ∀ e, G e → WellFormed e.more := fun e he => (hwfG e he).1
  have hcode : CodeOK lib code' := by
    intro bl nb hb
    have hb' := hb
    rw [← hcd] at hb'
    unfold extendCode at hb'
    split at hb'
    · rename_i nb0 hc0
      cases hb'
      exact (hinv.codeOK bl _ hc0).mono_code hcc
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hb'
      obtain ⟨i, hi, rfl⟩ := d1 bl d hd
      exact annot_of_graphM hG hhas hwf1 (hcovP i d hi)
  have hdatG := skaCallgraph_dat env memo hinv.wf hinv.memoNorm hinv.dat hw hnr hnvr hg
  have hpsub := (pruneCallgraph_spec hpr).1
  refine ⟨⟨fun f ms s ent h1 h2 => ?_, fun m hm => ?_, fun m hm => ?_, hcode, fun m hm => ?_,
    fun bl nb hb => ?_, fun f ms s ent h1 h2 => ?_⟩, ?_⟩
  · rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, _, rfl, rfl⟩
    · exact hinv.keys f ms' s ent e1 e2
    · rfl
  · obtain ⟨f, ms, s, ent, h1, h2, rfl⟩ := hm
    rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, hd, rfl, rfl⟩
    · obtain ⟨nb, hnb⟩ := hinv.bells _ ⟨f, ms', s, ent, e1, e2, rfl⟩
      exact hcc _ _ hnb
    · exact hdat i d hd
  · obtain ⟨f, ms, s, ent, h1, h2, rfl⟩ := hm
    rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, hd, rfl, rfl⟩
    · exact hok' _ ⟨f, ms', s, ent, e1, e2, rfl⟩
    · exact memoEntryOK_final hG hhas hwfG (hcovP i d hd) (fun bl nb h => ⟨nb, h⟩)
  · obtain ⟨f, ms, s, ent, h1, h2, rfl⟩ := hm
    rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, hd, rfl, rfl⟩
    · exact hinv.norm _ ⟨f, ms', s, ent, e1, e2, rfl⟩
    · exact ⟨(hnP i d hd).2.1, (hnP i d hd).2.2⟩
  · rw [← hcd] at hb
    unfold extendCode at hb
    split at hb
    · rename_i nb0 hc0
      exact hinv.bellNorm bl _ hc0
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨i, hi, rfl⟩ := d1 bl d hd
      exact (hnP i d hi).2.1
  · rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, hd, rfl, rfl⟩
    · exact hinv.dat f ms' s ent e1 e2
    · exact hdatG i d (hpsub i d hd)
  · intro bl d hd x hx gul t r
    obtain ⟨i, hi, rfl⟩ := d1 bl d hd
    exact nomm_agree lib gul code' hcode (annot_of_graphM hG hhas hwf1 (hcovP i d hi)) hx t r

/-- **The datums of a poke**: every datum by code bell has no `%10` at axis
`0`, and a code requirement and a product with a noun. -/
theorem skaPoke_dat {lib : Lib} (env : Env R) {n : Nat} {root : Ident} {memo memo' : Memo M} {reg reg' : R}
    {code : Bell → Option Nomm} {pruned : Callgraph M} {dats : M Bell (FDatum M)} {rd : FDatum M}
    (hinv : PokeInv lib memo code) (hw : WellFormed root.1) (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void)
    (h : skaPoke env n root memo reg = some (pruned, dats, memo', rd, reg')) :
    ∀ bl d, Treap.get dats bl = some d →
      bl.less = d.less ∧ Bake.NoAx0 d.nomm ∧ (∃ y, Fits d.less y) ∧ ∃ y, Fits d.prod y := by
  unfold skaPoke at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨g, regG⟩, hg, pr, hpr, rd', _, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, hdats, -, _, _⟩ := he
  subst hdats
  have hdatG := skaCallgraph_dat env memo hinv.wf hinv.memoNorm hinv.dat hw hnr hnvr hg
  intro bl d hd
  obtain ⟨i, hi, rfl⟩ := (pokeMemo_spec pr memo).1 bl d hd
  exact ⟨rfl, hdatG i d ((pruneCallgraph_spec hpr).1 i d hi)⟩

end Ana
end SkaModel
end Formalization
