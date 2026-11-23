import lemmas.Ska.BakeImp
import lemmas.Ska.PokeConv

/-!
# `+ska-poke` with its baking, across pokes

`Ana.skaPoke` (`Analysis.lean`) stops at the datums of a poke.  This file
models the rest of `+ska-poke` that the code table depends on: the `dat`
gate (`pokeDat`: this poke's datums by code bell, then the memo), the
`BEnv` of `+bake-graph` (`pokeEnv`), `+bake-graph` itself (`bakeGraph`,
`BakeGraph.lean`), `new-code` (`newCode`: the variants not already in
`code.lon`) and the write of `new-code` into `code.lon` (`addCode`).  The
SCC loop writes one entry per bell of `new-code`, with the variant's nomm and
the flags of `+eval-finalized`, which this file does not model (the flags do
not change what a bell's nomm stands for); `seek.lon` and `calls.lon` are the
`seek` and `calls` of the same entries, so the table keeps whole `VarEntry`s.

The state across pokes (`LongB`) is the memo, the code table and `vars.lon`.
The invariant `InvB` holds of it before the first poke and after every poke
(`skaPokeB_sound`): the memo is sound for some table of the analysis' nomms
(a ghost table, the `PokeInv` of `PokeConv.lean`), its entries are stored
under their code requirements (`LessKeys`, which makes `dat` give a datum of
the bell asked for), every bell of the real table has a nomm that satisfies
`Annot` on its bell (`CodeOK`), and every variant `vars.lon` lists has its
code bell's formula and an entry in the table (`VarsOK`).  So every bell of
the real table agrees with `+mink` on every subject that fits it
(`InvB.agree`).

The one assumption is `BakesImply` of each poke's `+bake-graph` (the question
called HImp): every bake the worklist ends with implies its code bell's code
requirement.  `BakeImp.lean` reduces it to the sites; it holds trivially of
the root, of jetted callees and in frozen mode, and a guard in `+bake-graph`
that falls back to `less.c` when `huge:so less.c bake` fails would make it
hold always.
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## The model -/

/-- `dat` of `+ska-poke`: the datum of a code bell from this poke's datums,
else from the memo (already updated by this poke), under the bell's formula
and code requirement. -/
def pokeDat (dats : M Bell (FDatum M)) (memo : Memo M) (b : Bell) : Option Datum :=
  match Treap.get dats b with
  | some d => some d.core
  | none => (Treap.get (gutMi memo b.fol) b.less).map fun e => e.2.core

/-- The parameters of `+bake-graph` in `+ska-poke`: the root bell is the
root datum's code requirement with the poke's formula. -/
def pokeEnv (jetted : Bell → Bool) (fold frozen : Bool) (vars : M Bell (M Bell Unit)) (root : Ident)
    (dats : M Bell (FDatum M)) (memo : Memo M) (rd : FDatum M) : BEnv M :=
  ⟨⟨rd.less, root.2⟩, pokeDat dats memo, jetted, vars, fold, frozen⟩

/-- `new-code`: the variants of `+bake-graph` that `code.lon` does not have. -/
def newCode (code : M Bell (VarEntry M)) (baked : M Bell (VarEntry M)) : M Bell (VarEntry M) :=
  (Treap.rap baked).foldl (fun acc e => if Treap.has code e.1 then acc else Treap.put acc e.1 e.2) Treap.empty

/-- The SCC loop's writes of `new-code` into `code.lon` (and `seek.lon`,
`calls.lon`). -/
def addCode (code nc : M Bell (VarEntry M)) : M Bell (VarEntry M) :=
  (Treap.rap nc).foldl (fun acc e => Treap.put acc e.1 e.2) code

/-- The parts of `long-ska` that the code table depends on. -/
structure LongB (M : Type → Type → Type) where
  memo : Memo M
  code : M Bell (VarEntry M)
  vars : M Bell (M Bell Unit)

/-- `+ska-poke` up to the code table: the analysis (`Ana.skaPoke`), the
bake, and the new code.  `jet` is the `jetted` gate, from `dat` and the
registrations of the poke (it also reads `call.cole.jets.lon` and the hot
jets, which it closes over); `fold` and `frozen` are the flags of
`bake-mode`.  The result is the root bell, the new state and the
registrations. -/
def skaPokeB (env : Env R) (jet : (Bell → Option Datum) → R → Bell → Bool) (fold frozen : Bool) (n : Nat)
    (root : Ident) (L : LongB M) (reg : R) : Option (Bell × LongB M × R) :=
  (skaPoke env n root L.memo reg).bind fun r =>
  let E := pokeEnv (jet (pokeDat r.2.1 r.2.2.1) r.2.2.2.2) fold frozen L.vars root r.2.1 r.2.2.1 r.2.2.2.1
  (bakeGraph E n).map fun bg =>
  (E.root, ⟨r.2.2.1, addCode L.code (newCode L.code bg.1), bg.2⟩, r.2.2.2.2)

/-! ## The invariant -/

/-- The nomms of a code table. -/
def realOf (code : M Bell (VarEntry M)) : Bell → Option Nomm := fun b => (Treap.get code b).map (·.nomm)

/-- The memo's entries are stored under their code requirements, as
`+put:mi` stores them. -/
def LessKeys (memo : Memo M) : Prop :=
  ∀ f ms s ent, Treap.get memo f = some ms → Treap.get ms s = some ent → ent.2.less = s

/-- Every variant that `vars` lists for a code bell has its formula and an
entry in the table. -/
def VarsOK (vars : M Bell (M Bell Unit)) (code : Bell → Option Nomm) : Prop :=
  ∀ c v, Treap.has (Treap.gut vars c Treap.empty) v = true → v.fol = c.fol ∧ ∃ nb, code v = some nb

/-- **The invariant across pokes** of the memo, the code table and `vars`. -/
structure InvB (lib : Lib) (L : LongB M) : Prop where
  ghost : ∃ code, PokeInv lib L.memo code
  lessKeys : LessKeys L.memo
  codeOK : CodeOK lib (realOf L.code)
  vars : VarsOK L.vars (realOf L.code)

theorem InvB.init (lib : Lib) : InvB lib (⟨Treap.empty, Treap.empty, Treap.empty⟩ : LongB M) where
  ghost := ⟨_, PokeInv.init lib⟩
  lessKeys := fun _ _ _ _ h _ => by simp [Treap.get_empty] at h
  codeOK := fun _ _ h => by simp [realOf, Treap.get_empty] at h
  vars := fun c v h => by simp [Treap.has, Treap.gut, Treap.get_empty] at h

/-- **Every bell of the real table agrees with `+mink`** on every subject
that fits it. -/
theorem InvB.agree {lib : Lib} {L : LongB M} (h : InvB lib L) {bl : Bell} {nb : Nomm}
    (hb : realOf L.code bl = some nb) {x : Noun} (hx : Fits bl.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x bl.fol r ↔ ∃ m, nommF lib gul (realOf L.code) m t x nb = some r :=
  nomm_agree lib gul _ h.codeOK (h.codeOK bl nb hb) hx t r

/-- One bake of each poke implies its code requirement (HImp). -/
def BakesImply (E : BEnv M) : Prop :=
  ∀ n st, bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E) = some st →
    ∀ c s, Treap.get st.bak c = some s → Sub s c.less

/-! ## Maps -/

theorem lessKeys_putMi {m : Memo M} (h : LessKeys m) (i : Ident) (d : FDatum M) : LessKeys (putMi m i d) := by
  intro f ms s ent h1 h2
  simp only [putMi, Treap.get_put] at h1
  split at h1
  · cases h1
    rw [Treap.get_put] at h2
    split at h2
    · cases h2; rename_i hs; exact hs.symm
    · unfold gutMi Treap.gut at h2
      cases hg : Treap.get m i.2 with
      | none => simp [hg, Treap.get_empty] at h2
      | some ms' => simp only [hg, Option.getD_some] at h2; exact h _ _ _ _ hg h2
  · exact h f ms s ent h1 h2

theorem lessKeys_pokeMemo (pruned : Callgraph M) {memo : Memo M} (h : LessKeys memo) :
    LessKeys (pokeMemo pruned memo).2 := by
  rw [pokeMemo_eq]
  suffices ∀ (l : List (Ident × FDatum M)) (acc : M Bell (FDatum M) × Memo M), LessKeys acc.2 →
      LessKeys (l.foldl pokeStep acc).2 from this _ _ h
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons e l ih => intro acc h; exact ih _ (lessKeys_putMi h _ _)

/-- A fold of `put` (skipping the keys `P` rejects) over pairs of a map `m`:
a key it puts has `m`'s value. -/
theorem foldl_putIf {ν : Type} (m : M Bell ν) (P : Bell → Bool) :
    ∀ (l : List (Bell × ν)) (acc : M Bell ν), (∀ e ∈ l, Treap.get m e.1 = some e.2) → ∀ b,
      Treap.get (l.foldl (fun acc e => if P e.1 then acc else Treap.put acc e.1 e.2) acc) b =
        if (!P b && l.any fun e => decide (e.1 = b)) = true then Treap.get m b else Treap.get acc b
  | [], acc, _, b => by simp
  | e :: l, acc, hl, b => by
    simp only [List.foldl_cons]
    rw [foldl_putIf m P l _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) b]
    have he := hl e List.mem_cons_self
    by_cases hb : e.1 = b
    · subst hb
      cases hp : P e.1
      · simp [Treap.get_put, he]
      · simp [hp]
    · have hd : decide (e.1 = b) = false := decide_eq_false hb
      simp only [List.any_cons, hd, Bool.false_or]
      cases P e.1 <;> simp [Treap.get_put, Ne.symm hb]

theorem any_rap {ν : Type} (m : M Bell ν) (b : Bell) :
    ((Treap.rap m).any fun e => decide (e.1 = b)) = (Treap.get m b).isSome := by
  cases h : Treap.get m b with
  | none =>
    simp only [Option.isSome_none, List.any_eq_false, decide_eq_true_eq]
    intro e he hb
    have := (Treap.mem_rap _ _ _).mp he
    rw [hb, h] at this
    cases this
  | some v =>
    simp only [Option.isSome_some, List.any_eq_true, decide_eq_true_eq]
    exact ⟨(b, v), (Treap.mem_rap _ _ _).mpr h, rfl⟩

theorem rap_ok {ν : Type} (m : M Bell ν) : ∀ e ∈ Treap.rap m, Treap.get m e.1 = some e.2 :=
  fun e he => (Treap.mem_rap _ _ _).mp he

/-- **The table after a poke**: an old entry is kept, a new one is the
variant's. -/
theorem addCode_get (code baked : M Bell (VarEntry M)) (b : Bell) :
    Treap.get (addCode code (newCode code baked)) b =
      match Treap.get code b with
      | some e => some e
      | none => Treap.get baked b := by
  have hnc : ∀ b', Treap.get (newCode code baked) b' =
      if Treap.has code b' = true then none else Treap.get baked b' := by
    intro b'
    have e2 := foldl_putIf baked (Treap.has code) (Treap.rap baked) Treap.empty (rap_ok baked) b'
    unfold newCode
    rw [e2, any_rap]
    cases Treap.has code b' <;> cases hg : Treap.get baked b' <;> simp [Treap.get_empty]
  have hadd : addCode code (newCode code baked) =
      (Treap.rap (newCode code baked)).foldl
        (fun acc e => if (fun _ => false) e.1 then acc else Treap.put acc e.1 e.2) code := by
    unfold addCode; rfl
  have e1 := foldl_putIf (M := M) (newCode code baked) (fun _ => false) (Treap.rap (newCode code baked)) code
    (rap_ok _) b
  rw [hadd, e1, any_rap, hnc]
  unfold Treap.has
  cases hc : Treap.get code b <;> cases hg : Treap.get baked b <;> simp [hc, hg]

theorem realOf_add (code baked : M Bell (VarEntry M)) (b : Bell) :
    realOf (addCode code (newCode code baked)) b =
      match realOf code b with
      | some nb => some nb
      | none => (Treap.get baked b).map (·.nomm) := by
  unfold realOf
  rw [addCode_get]
  cases Treap.get code b <;> rfl

theorem realOf_add_old {code baked : M Bell (VarEntry M)} :
    ∀ bl nb, realOf code bl = some nb → ∃ nb', realOf (addCode code (newCode code baked)) bl = some nb' := by
  intro bl nb h
  rw [realOf_add, h]
  exact ⟨nb, rfl⟩

/-! ## The final pass of `+bake-graph` -/

theorem finalFold_none (E : BEnv M) (st : BSt M) :
    ∀ l : List (Bell × Sock), l.foldl (finalStep E st) none = none
  | [] => rfl
  | _ :: l => finalFold_none E st l

/-- **What the final pass makes**: a variant of the result is an old one or
the folded nomm of a bake; every bake has its variant; `vars` gains only the
variants of the bakes. -/
theorem finalFold_spec (E : BEnv M) (st : BSt M) :
    ∀ (l : List (Bell × Sock)) (out0 out : M Bell (VarEntry M)) (vars0 vars : M Bell (M Bell Unit)),
      l.foldl (finalStep E st) (some (out0, vars0)) = some (out, vars) →
      (∀ v ve, Treap.get out v = some ve → Treap.get out0 v = some ve ∨
        ∃ e ∈ l, v = ⟨e.2, e.1.fol⟩ ∧ ∃ d sites, E.dat e.1 = some d ∧
          know E.fold d.nomm e.2 E.dat (bakeRes E st) = some (ve.nomm, sites)) ∧
      (∀ v, (Treap.get out0 v).isSome → (Treap.get out v).isSome) ∧
      (∀ e ∈ l, (Treap.get out ⟨e.2, e.1.fol⟩).isSome) ∧
      (∀ c v, Treap.has (Treap.gut vars c Treap.empty) v = true →
        Treap.has (Treap.gut vars0 c Treap.empty) v = true ∨ ∃ e ∈ l, e.1 = c ∧ v = ⟨e.2, c.fol⟩)
  | [], out0, out, vars0, vars, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ h => Or.inl h, fun _ h => h, fun _ h => absurd h List.not_mem_nil, fun _ _ h => Or.inl h⟩
  | e :: l, out0, out, vars0, vars, h => by
    simp only [List.foldl_cons] at h
    cases h1 : finalStep E st (some (out0, vars0)) e with
    | none => rw [h1, finalFold_none] at h; cases h
    | some p =>
    obtain ⟨out1, vars1⟩ := p
    rw [h1] at h
    obtain ⟨a1, a2, a3, a4⟩ := finalFold_spec E st l out1 out vars1 vars h
    simp only [finalStep, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h1
    obtain ⟨d, hd, ⟨nomm, sites⟩, hk, vs, _, he⟩ := h1
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun v ve hv => ?_, fun v hv => a2 v ?_, fun e' he' => ?_, fun c v hv => ?_⟩
    · rcases a1 v ve hv with h | ⟨e', he', h⟩
      · rw [Treap.get_put] at h
        split at h
        · rename_i hv'
          cases h
          exact Or.inr ⟨e, List.mem_cons_self, hv', d, sites, hd, hk⟩
        · exact Or.inl h
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h⟩
    · rw [Treap.get_put]; split
      · rfl
      · exact hv
    · rcases List.mem_cons.mp he' with rfl | he'
      · exact a2 _ (by simp [Treap.get_put])
      · exact a3 e' he'
    · rcases a4 c v hv with h | ⟨e', he', h⟩
      · simp only [Treap.has, Treap.gut, Treap.get_put] at h
        by_cases hc : c = e.1
        · subst hc
          simp only [if_true, Option.getD_some, Treap.get_put] at h
          split at h
          · rename_i hv'
            exact Or.inr ⟨e, List.mem_cons_self, rfl, hv'⟩
          · exact Or.inl (by simp only [Treap.has, Treap.gut]; exact h)
        · rw [if_neg hc] at h
          exact Or.inl (by simp only [Treap.has, Treap.gut]; exact h)
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h⟩

/-! ## The analysis part, what the bake needs of it -/

/-- **The datums of a poke**: each satisfies `Annot` on its code requirement
with the table of the earlier pokes extended by the datums, and its product
keeps the provenance invariant. -/
theorem skaPoke_dats {lib : Lib} (env : Env R) {n : Nat} {root : Ident} {memo memo' : Memo M} {reg reg' : R}
    {code : Bell → Option Nomm} {pruned : Callgraph M} {dats : M Bell (FDatum M)} {rd : FDatum M}
    (hinv : PokeInv lib memo code) (hw : WellFormed root.1) (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void)
    (h : skaPoke env n root memo reg = some (pruned, dats, memo', rd, reg')) :
    ∀ bl d, Treap.get dats bl = some d →
      Annot lib (extendCode code dats) (Fits bl.less) bl.fol d.nomm ∧
      ∀ y gul p, Fits bl.less y → Mink lib gul [] y bl.fol (Tone.zero p) → ProvR y d.prod d.map p := by
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
  obtain ⟨G, hG, hcovP, hGp, hwfG, _⟩ := skaCallgraph_prunedM (lib := lib) (code := code') env memo hinv.wf
    hinv.memoNorm hinv.keys hok' hw hnr hnvr hg hpr
  obtain ⟨d1, d2, _⟩ := pokeMemo_spec pr memo
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
  intro bl d hd
  obtain ⟨i, hi, rfl⟩ := d1 bl d hd
  exact ⟨annot_of_graphM hG hhas hwf1 (hcovP i d hi),
    fun y gul p hy hm => (prodRel_of_graphM hG hwf1 _ (hcovP i d hi) y gul p hy hm).1⟩

/-- **What `+know` needs of `dat` in a poke**: `DatOK`, and `Annot` of the
datum of every code bell it gives, on the code requirement, with the ghost
table after the poke. -/
theorem pokeDat_ok {lib : Lib} {code : Bell → Option Nomm} {dats : M Bell (FDatum M)} {memo : Memo M}
    (hinv : PokeInv lib memo code) (hlk : LessKeys memo)
    (hd : ∀ bl d, Treap.get dats bl = some d →
      Annot lib code (Fits bl.less) bl.fol d.nomm ∧
      ∀ y gul p, Fits bl.less y → Mink lib gul [] y bl.fol (Tone.zero p) → ProvR y d.prod d.map p) :
    DatOK lib (pokeDat dats memo) ∧
      ∀ t d, pokeDat dats memo t = some d → Annot lib code (Fits t.less) t.fol d.nomm := by
  -- a datum of `dat` is this poke's or a memo entry's, of the bell asked for
  have key : ∀ t d, pokeDat dats memo t = some d →
      Annot lib code (Fits t.less) t.fol d.nomm ∧
      ∀ y gul p, Fits t.less y → Mink lib gul [] y t.fol (Tone.zero p) → ProvR y d.prod d.map p := by
    intro t d h
    unfold pokeDat at h
    split at h
    · rename_i d' hd'
      cases h
      exact hd t d' hd'
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨ent, he, rfl⟩ := h
      unfold gutMi Treap.gut at he
      cases hm : Treap.get memo t.fol with
      | none => simp [hm, Treap.get_empty] at he
      | some ms =>
        simp only [hm, Option.getD_some] at he
        have hmem : MemEnt memo (entOf ent.1 ent.2) := ⟨t.fol, ms, t.less, ent, hm, he, rfl⟩
        have hok := hinv.ok _ hmem
        have hf : ent.1.2 = t.fol := hinv.keys _ _ _ _ hm he
        have hl : ent.2.less = t.less := hlk _ _ _ _ hm he
        have ha := hok.annot
        have hp := hok.prov
        simp only [entOf] at ha hp
        rw [hf] at ha hp
        rw [show (FDatum.core ent.2).less = t.less from hl] at ha hp
        exact ⟨ha, hp⟩
  exact ⟨datOK_of_prov fun b d h => (key b d h).2, fun t d h => (key t d h).1⟩

/-! ## A poke -/

/-- **`+ska-poke` keeps the invariant**, and the root bell it returns has an
entry in the table.  It assumes, of the poke, what `skaPoke_sound` assumes
(a root sock that is well formed, normal and not `%void`) and HImp for this
poke's `+bake-graph` (`himp`). -/
theorem skaPokeB_sound {lib : Lib} (env : Env R) {jet : (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {n : Nat} {root : Ident} {L L' : LongB M} {reg reg' : R} {rb : Bell}
    (hinv : InvB lib L) (hw : WellFormed root.1) (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void)
    (himp : ∀ pr dats memo' rd reg'', skaPoke env n root L.memo reg = some (pr, dats, memo', rd, reg'') →
      BakesImply (pokeEnv (jet (pokeDat dats memo') reg'') fold frozen L.vars root dats memo' rd))
    (h : skaPokeB env jet fold frozen n root L reg = some (rb, L', reg')) :
    InvB lib L' ∧ ∃ nb, realOf L'.code rb = some nb := by
  obtain ⟨code, hpi⟩ := hinv.ghost
  unfold skaPokeB at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨pr, dats, memo', rd, reg''⟩, hsk, ⟨baked, vars'⟩, hbg, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  dsimp only at hbg ⊢
  have himpE := himp pr dats memo' rd reg'' hsk
  generalize hE : pokeEnv (jet (pokeDat dats memo') reg'') fold frozen L.vars root dats memo' rd = E at hbg himpE
  -- the analysis
  obtain ⟨hpi', -⟩ := skaPoke_sound env hpi hw hnr hnvr hsk
  have hds := skaPoke_dats env hpi hw hnr hnvr hsk
  have hlk' : LessKeys memo' := by
    unfold skaPoke at hsk
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hsk
    obtain ⟨_, _, pr', _, _, _, he⟩ := hsk
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, -, rfl, -, -⟩ := he
    exact lessKeys_pokeMemo _ hinv.lessKeys
  obtain ⟨hdatOK, hA⟩ := pokeDat_ok hpi' hlk' hds
  have hEdat : E.dat = pokeDat dats memo' := by rw [← hE]; rfl
  have hEvars : E.vars = L.vars := by rw [← hE]; rfl
  rw [← hEdat] at hdatOK hA
  -- the bake
  unfold bakeGraph at hbg
  simp only [Option.bind_eq_some_iff] at hbg
  obtain ⟨st, hloop, hfin⟩ := hbg
  obtain ⟨f1, -, f3, f4⟩ := finalFold_spec E st _ _ _ _ _ hfin
  obtain ⟨qs, hI⟩ := bakeLoop_inv E n _ _ _ st (loopInv_init E) hloop
  generalize hc' : realOf (addCode L.code (newCode L.code baked)) = code'
  have hold : ∀ bl nb, realOf L.code bl = some nb → ∃ nb', code' bl = some nb' := by
    rw [← hc']; exact realOf_add_old
  have hbake : ∀ c s, Treap.get st.bak c = some s → ∃ nb, code' ⟨s, c.fol⟩ = some nb := by
    intro c s hs
    have := f3 (c, s) ((Treap.mem_rap _ _ _).mpr hs)
    obtain ⟨ve, hve⟩ := Option.isSome_iff_exists.mp this
    rw [← hc', realOf_add]
    cases hr : realOf L.code ⟨s, c.fol⟩ with
    | some nb => exact ⟨nb, rfl⟩
    | none =>
      have : Treap.get baked ⟨s, c.fol⟩ = some ve := by
        simpa [Treap.get_empty] using hve
      exact ⟨ve.nomm, by simp [this]⟩
  have hvars : ∀ c v, Treap.has (Treap.gut E.vars c Treap.empty) v = true → v.fol = c.fol ∧ ∃ nb, code' v = some nb := by
    intro c v hv
    rw [hEvars] at hv
    obtain ⟨hf, nb, hnb⟩ := hinv.vars c v hv
    exact ⟨hf, hold v nb hnb⟩
  have hcodeOK : CodeOK lib code' := by
    intro bl nb hb
    have hb' := hb
    rw [← hc', realOf_add] at hb'
    split at hb'
    · rename_i nb0 hr
      cases hb'
      exact (hinv.codeOK bl _ hr).mono_code hold
    · simp only [Option.map_eq_some_iff] at hb'
      obtain ⟨ve, hve, rfl⟩ := hb'
      rcases f1 bl ve hve with h0 | ⟨e, hel, rfl, d, sites, hd, hk⟩
      · simp [Treap.get_empty] at h0
      · have hs : Treap.get st.bak e.1 = some e.2 := (Treap.mem_rap _ _ _).mp hel
        have hva := variant_annot (code := extendCode code dats) (code' := code') hpi'.codeOK hdatOK hloop
          hvars hbake hd hs (hA e.1 d hd) hk
        exact hva.mono fun x hx => ⟨himpE n st hloop e.1 e.2 hs x hx, hx⟩
  refine ⟨⟨⟨_, hpi'⟩, hlk', ?_, ?_⟩, ?_⟩
  · show CodeOK lib (realOf (addCode L.code (newCode L.code baked)))
    rw [hc']; exact hcodeOK
  · show VarsOK vars' (realOf (addCode L.code (newCode L.code baked)))
    rw [hc']
    intro c v hv
    rcases f4 c v hv with h0 | ⟨e, hel, rfl, rfl⟩
    · exact hvars c v h0
    · have hs : Treap.get st.bak e.1 = some e.2 := (Treap.mem_rap _ _ _).mp hel
      exact ⟨rfl, hbake e.1 e.2 hs⟩
  · exact hbake E.root E.root.less hI.root

end Bake

end SkaModel
end Formalization
