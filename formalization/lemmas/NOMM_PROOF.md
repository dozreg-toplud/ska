# Nomm Correctness Proof Shape

This note corresponds to `Formalization/Nomm.lean`.

The Lean file currently formalizes the post-analysis Nomm language and the
statement shape for future SKA correctness.  It deliberately does **not**
formalize the current SKA analyzer algorithm.  The algorithm in `desk/lib/skan.hoon`
is still being corrected, so an exact mechanization today would risk proving
facts about an unstable or known-buggy implementation.  The purpose of this file
is to keep the target theorem precise so the implementation can move toward it.

## What Exists Now

`Formalization/Nomm.lean` defines:

- `Cape`, `Sock`, `Sock.Matches`, and `Sock.Huge`, a minimal logical model of
  subject templates.
- `Bell`, the direct-call key consisting of a minimized subject template and a
  formula.
- `Nomm`, matching the post-`cook` `nomm-1` surface in `desk/sur/noir.hoon`.
- `AnalysisNomm`, a small record of the analysis-only constructors that
  `++ rewrite` lowers away: indirect/direct `%2` forms and static/dynamic hint
  forms.
- `NommEval`, the big-step semantics corresponding to `++ run-nomm-1`.
- `EquivalentUnder ctx sock formula code`, the semantic target:

```lean
forall {subject out}, Sock.Matches sock subject ->
  (Nock.Eval subject formula out ↔ NommEval ctx subject code out)
```

This says the original Nock formula and the produced Nomm body have exactly the
same terminating noun results for every concrete subject described by the sock.

## What Is Missing By Design

The missing piece is an analyzer relation, something like:

```lean
Analyzes ctx inputSock inputFormula output
```

where `output` contains:

```lean
structure AnalyzerOutput where
  analyzedSock : Sock
  analyzedFormula : Noun
  code : Nomm
```

That relation should eventually mirror the corrected SKA pipeline:

- `scan` / `fol-loop`: analyze a subject-template/formula pair into
  analysis-time `nomm` plus product sock/provenance information.
- memo and call registration: populate direct-call entries keyed by `bell`.
- `rewrite`: lower `%i2`, `%ds2`, `%dus2`, `%s11`, and `%d11` into `nomm-1`.
- `cook`: build the code table and formula-indexed lookup table.
- `match-sock`: choose a compiled entry whose required sock is applicable to the
  requested subject sock.

Until the algorithm stabilizes, `Analyzes` is intentionally left as a parameter.

## Analyzer Soundness Theorem

The future algorithm-level theorem is represented in Lean by:

```lean
def AnalyzerRelationSound
    (Analyzes : Context -> Sock -> Noun -> AnalyzerOutput -> Prop) : Prop :=
  forall {ctx inputSock inputFormula output},
    ContextCorrect ctx ->
    Analyzes ctx inputSock inputFormula output ->
    AnalyzerOutputCertificate ctx inputSock inputFormula output
```

The certificate contains three obligations:

- `formula_eq`: the selected entry is for the requested input formula.
- `applicable`: the selected entry's sock is usable for the requested subject
  sock.  This is the Lean version of the `match-sock` / `huge:so` check.
- `sound`: the selected Nomm body is equivalent to the selected Nock formula
  under the selected subject sock.

Once that certificate exists, `AnalyzerOutputCertificate.equivalent` gives the
actual input-level theorem:

```lean
EquivalentUnder ctx inputSock inputFormula output.code
```

## Proof Obligations For The Real Analyzer

The proof should be by induction over the stabilized analysis derivation, not by
induction over Nomm syntax alone.  The Nomm semantics are only the final target.

For each analyzer case:

- The emitted Nomm code must be shown equivalent to the Nock formula being
  analyzed.
- The computed product sock must soundly describe every possible result noun.
- Any crash-safety flag used to skip or reorder work must be justified against
  the successful-evaluation relation.
- Any provenance/source information used for memoization or direct calls must be
  connected to the subject-template interpretation.

Specific cases:

- Nock cell formulas use two sub-analysis induction hypotheses and pair the
  resulting products.
- `%0` requires a slot/product lemma: if a concrete subject matches the input
  sock and the analyzer says an axis is available, then Nock slot lookup and Nomm
  slot evaluation agree.
- `%1` is constant and should produce an exact known sock.
- `%2` indirect calls evaluate analyzed subject and formula subterms, then fall
  back to ordinary `Nock.Eval`.
- `%2` direct calls require the global code-table invariant: the referenced
  `bell` has a body equivalent to `bell.fol` under `bell.bus`, and the runtime
  subject produced by the call subject subterm matches `bell.bus`.
- `%3`, `%4`, `%5`, `%6`, `%7`, and `%10` use local induction hypotheses plus
  the matching Nock/Nomm semantic constructors.
- `%8` and `%9` must be proved semantics-preserving for their SKA rewrites:
  `%8` to `%7 [p %0 1] q`, and `%9` to `%7 q %2 [%0 1] %0 p`.
- `%11` static hints ignore the hint and preserve the body result.  Dynamic
  hints must additionally prove the hint expression evaluation required by
  `run-nomm-1` is crash-compatible with the source Nock hint rule.
- `%12` currently has no successful Nomm constructor, matching the current
  no-scry behavior; a future implementation that supports scry needs a semantics
  and proof obligation here.

Global invariants:

- Every entry in the code table is sound under its `bell`.
- Memoized and recursively discovered entries preserve the same invariant across
  the call graph or SCC being analyzed.
- `rewrite` preserves the meaning of analysis-time Nomm under the code-table
  assumptions it emits.
- `cook` preserves all per-entry soundness facts when it moves analysis output
  into lookup tables.
- `match-sock` returns the most applicable entry only if `Sock.Huge selected
  requested` holds; optimality is useful for performance, but soundness only
  needs applicability.
- Jets are trusted only through `JetCorrect`: every jet result must also be a
  valid ordinary Nock result.

## Intended End State

When SKA is stable, the next formalization step should define an inductive
`Analyzes` relation for the corrected algorithm and prove
`AnalyzerRelationSound Analyzes`.

At that point the final theorem for a concrete analyzer run is:

```lean
theorem analyzed_nomm_equivalent
    (hctx : ContextCorrect ctx)
    (hrun : Analyzes ctx inputSock inputFormula output) :
    EquivalentUnder ctx inputSock inputFormula output.code :=
  AnalyzerRelationSound.equivalent analyze_sound hctx hrun
```

The current Lean file is set up so that theorem can be stated without changing
the Nomm language semantics.
