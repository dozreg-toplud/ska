import lemmas.Compiler.OptLinkAlPrelude

/-!
# `+alias`: the state `gen` of the walk against the model's `AGen`

The relations that every phase of the walk (README Gaps 13, phases 7 to 16)
states its subject with.  `gen` is the noun

```hoon
  $:  new=(map @uwoo blob)  old=(map @uvre @uvre)
      info=(map @uwoo (map @uvre info-reg))  imms=(map @uwoo (jug * @uvre))
      info-local=(map @uvre info-reg)  imms-local=(jug * @uvre)
      rev=(jug @uwoo @uwoo)  folded=_|
  ==
```

(`genN`; axes `2 6 14 30 62 126 254 255` of `gen`, `gen` at axis `6` of
the walk's subject `alWS`).

* `InfoStoreRel`, `ImmsStoreRel`: `info.gen` and `imms.gen`, maps of labels
  to an `InfoMapRel` map and to an `ImmsRel` jug, with the keys of the
  model's `g.info`, `g.imms`.
* `GenRel g N`: **`gen` between two blocks**: `new` is the noun of `g.new`,
  `old` by `OldRel`, `info` and `imms` as above, `rev` by `JugRel`, `folded`
  the flag of `g.folded`; `info-local` and `imms-local` any nouns (the turn
  of a block overwrites them before it reads them).
* `GenRelL g loc imml N`: **`gen` inside a block**: `GenRel` with
  `info-local` related to `loc` (`InfoMapRel`) and `imms-local` to `imml`
  (`ImmsRel`).  The body and the end run on `{ g with old := st.old }` with
  `loc := st.loc`, `imml := st.imml` of the model's `ABody`.
* `genRel_start`: the start of the walk (`alGen0 R0`, `al_prelude`) is
  `GenRel` to the start state of `aliasM`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of `gen`: `[new old info imms info-local imms-local rev folded]`. -/
def genN (NEW OLD INFO IMMS LOC IMML REV F : Noun) : Noun :=
  C NEW (C OLD (C INFO (C IMMS (C LOC (C IMML (C REV F))))))

/-- The subject of the walk: the `|^` core of `+alias` with `gen` over the gate
of `+alias` (`n-args` at `60`, `blocks` at `122`, `rev` at `246`, `topo` at
`247`). -/
def alWS (GEN NA BL REV TOPO : Noun) : Noun :=
  C alBat (C GEN (C alBodyCut (C (C NA (C BL (C REV TOPO))) optC)))

/-- `info.gen`: a map of labels to maps of facts, the keys those of `g.info`. -/
def InfoStoreRel (N : Noun) (m : Nat → Option Opt.AInfo) : Prop :=
  IsMap mugF N ∧ (∀ k v, Get N k v → ∃ o x, k = A o ∧ m o = some x ∧ InfoMapRel v x) ∧
    ∀ o x, m o = some x → KIn N (A o)

/-- `imms.gen`: a map of labels to jugs of immediates, the keys those of `g.imms`. -/
def ImmsStoreRel (N : Noun) (m : Nat → Option Opt.AImms) : Prop :=
  IsMap mugF N ∧ (∀ k v, Get N k v → ∃ o x, k = A o ∧ m o = some x ∧ ImmsRel v x) ∧
    ∀ o x, m o = some x → KIn N (A o)

/-- **`gen` between two blocks** is the model's state `g`; `info-local` and
`imms-local` are any nouns. -/
def GenRel (g : Opt.AGen (TreapMap mugF)) (N : Noun) : Prop :=
  ∃ OLD INFO IMMS LOC IMML REV,
    N = genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag g.folded) ∧
    OldRel OLD g.old ∧ InfoStoreRel INFO g.info ∧ ImmsStoreRel IMMS g.imms ∧ JugRel REV g.rev

/-- **`gen` inside a block**: the model's state `g`, with `info-local` the
facts `loc` and `imms-local` the immediates `imml`. -/
def GenRelL (g : Opt.AGen (TreapMap mugF)) (loc : Opt.AInfo) (imml : Opt.AImms) (N : Noun) : Prop :=
  ∃ OLD INFO IMMS LOC IMML REV,
    N = genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML REV (flag g.folded) ∧
    OldRel OLD g.old ∧ InfoStoreRel INFO g.info ∧ ImmsStoreRel IMMS g.imms ∧ JugRel REV g.rev ∧
    InfoMapRel LOC loc ∧ ImmsRel IMML imml

theorem GenRelL.genRel {g : Opt.AGen (TreapMap mugF)} {loc : Opt.AInfo} {imml : Opt.AImms} {N : Noun}
    (h : GenRelL g loc imml N) : GenRel g N := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, REV, e, h1, h2, h3, h4, -, -⟩ := h
  exact ⟨OLD, INFO, IMMS, LOC, IMML, REV, e, h1, h2, h3, h4⟩

theorem infoStoreRel_nil : InfoStoreRel (A 0) (fun _ => none) :=
  ⟨IsMap.nil, fun _ _ h => absurd h Get_atom, fun _ _ h => by cases h⟩

theorem immsStoreRel_nil : ImmsStoreRel (A 0) (fun _ => none) :=
  ⟨IsMap.nil, fun _ _ h => absurd h Get_atom, fun _ _ h => by cases h⟩

/-- The start state of the walk of `aliasM` on the jar `rev`. -/
def alG0 (rev : TreapMap mugF (List Nat)) : Opt.AGen (TreapMap mugF) :=
  { new := HoonMap.empty, old := id, info := fun _ => none, imms := fun _ => none,
    rev := fun o => Opt.dedupN ((HoonMap.get rev o).getD []), folded := false }

theorem alGen0_genN (R0 : Noun) : alGen0 R0 = genN (A 0) (A 0) (A 0) (A 0) (A 0) (A 0) R0 (A 1) := rfl

/-- **The start of the walk**: `alGen0 R0` of `al_prelude` is `gen` of the
start state of `aliasM`. -/
theorem genRel_start {R0 : Noun} {rev : TreapMap mugF (List Nat)}
    (hR : JugRel R0 (fun o => Opt.dedupN ((HoonMap.get rev o).getD []))) : GenRel (alG0 rev) (alGen0 R0) :=
  ⟨A 0, A 0, A 0, A 0, A 0, R0, by simp [alGen0_genN, alG0, HoonMap.toNoun_empty, flag], oldRel_nil,
    infoStoreRel_nil, immsStoreRel_nil, hR⟩

end Compiler
end Formalization
