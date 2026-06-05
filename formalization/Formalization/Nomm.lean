import Formalization.Nock

/-!
This module models the SKA `nomm`/`nomm-1` intermediate representation from
the Hoon sources as a Nock-like Lean IR.

Primary source correspondence:

* `desk/sur/sock.hoon`:
  `+$ cape  $~(| $@(? [cape cape]))`
  `+$ sock  $~(|+~ [=cape data=*])`

* `desk/lib/nock-compilation1.hoon`:
  `+$ nomm` is the analysis-time IR.  It has the ordinary Nock-shaped
  constructors plus analysis-only call/hint constructors such as `%i2`, `%ds2`,
  `%dus2`, `%s11`, and `%d11`.

* `desk/sur/noir.hoon`:
  `+$ nomm-1` is the post-`cook` IR consumed by `run-nomm-1`.  It is Nock-like,
  but `%2` carries optional direct-call metadata and an optional formula value:

    [%2 p=nomm-1 q=(unit nomm-1) info=(unit bell)]

  This file calls that post-analysis IR `Nomm`, because it is the representation
  whose semantics are stable enough to state equivalence against Nock.

* `desk/lib/skan.hoon`:
  `++ rewrite` lowers analysis-time `nomm` into `nomm-1`.
  `++ run-nomm-1` is mirrored by the relational `NommEval` below.

Proof idea, in prose:

This module does not prove correctness of the current SKA analyzer.  That is
intentional: the current Hoon algorithm is still being corrected, so formalizing
its exact control flow now would risk preserving known bugs.  Instead, this file
defines the Nomm language, its semantics, and the shape of the theorem a stable
analyzer must satisfy.

The desired SKA correctness theorem should say: if SKA analysis of an input
subject/formula pair produces a Nomm body under a subject template `sock`, then
for every concrete subject matching that sock, ordinary Nock evaluation of the
original formula terminates with a noun iff Nomm evaluation of the produced body
terminates with that same noun.

The proof would be by induction over the analysis derivation in `skan.hoon`.
Each Nock-like constructor is local: the proof appeals to the induction
hypotheses for subformulas and then uses the corresponding constructor of
`Nock.Eval` and `NommEval`.  Direct calls through `%2 ... info=(some bell)`
need the global code-table invariant: every `bell` registered by analysis has a
Nomm body that is already equivalent to `bell.fol` for subjects matching
`bell.bus`.  The `sock` side condition is exactly what justifies reusing that
registered body at a more specific runtime subject.  Indirect `%2` falls back to
ordinary Nock after evaluating both the subject and formula subexpressions, so
its proof composes the subexpression induction hypotheses with `Nock.Eval`.
Hints (`%11`) are observationally irrelevant except that dynamic hints evaluate
their hint expression first; the proof must show that this extra evaluation is
crash-compatible with the source Nock hint rule.  Scry (`%12`) has no successful
constructor here, matching the current `run-nomm-1` behavior.

The theorem names at the bottom package the final statement: `EquivalentUnder`
is the semantic equivalence under a subject template, and
`AnalysisCertificate.equivalent` shows how an analyzer certificate plus a
`match-sock`/`huge`-style applicability proof yields the desired input-level
equivalence.  `AnalyzerRelationSound` is the theorem shape for the future
algorithm-level proof: once an `Analyzes` relation mirrors the stable SKA
algorithm, its soundness proof must produce one of these certificates for every
analysis result.
-/

namespace Formalization
namespace Nomm

open Nock

-- `cape` describes which axes of a noun are known.  This is the structural
-- subset of `+$ cape` needed to state subject-template matching.
inductive Cape where
  | unknown : Cape
  | known : Cape
  | cell : Cape -> Cape -> Cape
  deriving DecidableEq, Repr

-- A `sock` is known-shape information plus template data.
structure Sock where
  cape : Cape
  data : Noun
  deriving DecidableEq, Repr

namespace Sock

-- `Matches s subject` means `subject` is compatible with the data known by
-- `s`.  Unknown cape leaves impose no constraint; known leaves require exact
-- noun equality; cell capes recurse into head and tail.
inductive MatchesCape : Cape -> Noun -> Noun -> Prop where
  | unknown {template subject} :
      MatchesCape Cape.unknown template subject
  | known {noun} :
      MatchesCape Cape.known noun noun
  | cell {leftCape rightCape leftTemplate rightTemplate leftSubject rightSubject} :
      MatchesCape leftCape leftTemplate leftSubject ->
      MatchesCape rightCape rightTemplate rightSubject ->
      MatchesCape (Cape.cell leftCape rightCape)
        (C leftTemplate rightTemplate)
        (C leftSubject rightSubject)

def Matches (sock : Sock) (subject : Noun) : Prop :=
  MatchesCape sock.cape sock.data subject

-- Hoon's `huge:so required actual` is used as an applicability test: every
-- subject represented by the more-specific runtime sock `actual` is also
-- represented by the code entry's required sock.
def Huge (required actual : Sock) : Prop :=
  forall {subject}, Matches actual subject -> Matches required subject

theorem huge_refl (sock : Sock) : Huge sock sock :=
  fun h => h

def exact (noun : Noun) : Sock :=
  { cape := Cape.known, data := noun }

theorem exact_matches {noun : Noun} : Matches (exact noun) noun :=
  MatchesCape.known

end Sock

-- `bell` in `desk/lib/nock-compilation1.hoon` and `desk/sur/noir.hoon` names a
-- direct-call target by the minimized subject template and formula.
structure Bell where
  bus : Sock
  fol : Noun
  deriving DecidableEq, Repr

-- Post-analysis `nomm-1`, with names chosen to expose the Nock opcode each
-- constructor corresponds to.  Opcode 8 and 9 do not appear here because SKA
-- rewrites them during analysis:
--
--   [%8 p q] => [%7 [p %0 1] q]
--   [%9 p q] => [%7 q %2 [%0 1] %0 p]
--
-- See `desk/sur/noir.hoon` comments for the same normalization.
inductive Nomm where
  | cell : Nomm -> Nomm -> Nomm
  | op0 : Nat -> Nomm
  | op1 : Noun -> Nomm
  | op2 : Nomm -> Option Nomm -> Option Bell -> Nomm
  | op3 : Nomm -> Nomm
  | op4 : Nomm -> Nomm
  | op5 : Nomm -> Nomm -> Nomm
  | op6 : Nomm -> Nomm -> Nomm -> Nomm
  | op7 : Nomm -> Nomm -> Nomm
  | op10 : Nat -> Nomm -> Nomm -> Nomm
  | op11Static : Nat -> Nomm -> Noun -> Nomm
  | op11Dynamic : Nat -> Nomm -> Nomm -> Noun -> Nomm
  | op12 : Nomm -> Nomm -> Nomm

-- Analysis-time Nomm constructors that `skan.hoon` eliminates with `++ rewrite`.
-- This is intentionally smaller than the full Hoon state: it records the syntax
-- whose lowering must be justified before `NommEval` applies.
inductive AnalysisNomm where
  | cooked : Nomm -> AnalysisNomm
  | indirect2 : AnalysisNomm -> AnalysisNomm -> AnalysisNomm
  | directSubject2 : AnalysisNomm -> Bell -> AnalysisNomm
  | directSubjectFormula2 : AnalysisNomm -> AnalysisNomm -> Bell -> AnalysisNomm
  | staticHint11 : Nat -> AnalysisNomm -> Noun -> AnalysisNomm
  | dynamicHint11 : Nat -> AnalysisNomm -> AnalysisNomm -> Noun -> AnalysisNomm

-- The runtime context abstracts the tables built by SKA:
-- * `code bell body` is the direct-call code table.
-- * `jet subject formula out` represents a trusted jet result, if any.
structure Context where
  code : Bell -> Nomm -> Prop
  jet : Noun -> Noun -> Noun -> Prop

-- Big-step semantics for `nomm-1`, following `++ run-nomm-1`.
-- Like `Nock.Eval`, this relation only derives successful executions.
inductive NommEval (ctx : Context) : Noun -> Nomm -> Noun -> Prop where
  | cell {subject left right leftOut rightOut} :
      NommEval ctx subject left leftOut ->
      NommEval ctx subject right rightOut ->
      NommEval ctx subject (Nomm.cell left right) (C leftOut rightOut)

  | op0 {subject axis out} :
      Slot axis subject out ->
      NommEval ctx subject (Nomm.op0 axis) out

  | op1 {subject noun} :
      NommEval ctx subject (Nomm.op1 noun) noun

  -- [%2 p ~ ~] is invalid/indirect without a formula, so it has no constructor.
  | op2_indirect {subject p q subject' formula out} :
      NommEval ctx subject p subject' ->
      NommEval ctx subject q formula ->
      Nock.Eval subject' formula out ->
      NommEval ctx subject (Nomm.op2 p (some q) none) out

  | op2_direct_code {subject p bell subject' target out} :
      NommEval ctx subject p subject' ->
      ctx.code bell target ->
      NommEval ctx subject' target out ->
      NommEval ctx subject (Nomm.op2 p none (some bell)) out

  | op2_direct_checked_code {subject p q bell subject' formula target out} :
      NommEval ctx subject p subject' ->
      NommEval ctx subject q formula ->
      formula = bell.fol ->
      ctx.code bell target ->
      NommEval ctx subject' target out ->
      NommEval ctx subject (Nomm.op2 p (some q) (some bell)) out

  | op2_direct_jet {subject p bell subject' out} :
      NommEval ctx subject p subject' ->
      ctx.jet subject' bell.fol out ->
      NommEval ctx subject (Nomm.op2 p none (some bell)) out

  | op2_direct_checked_jet {subject p q bell subject' formula out} :
      NommEval ctx subject p subject' ->
      NommEval ctx subject q formula ->
      formula = bell.fol ->
      ctx.jet subject' bell.fol out ->
      NommEval ctx subject (Nomm.op2 p (some q) (some bell)) out

  | op3 {subject p noun} :
      NommEval ctx subject p noun ->
      NommEval ctx subject (Nomm.op3 p) (wut noun)

  | op4 {subject p atom} :
      NommEval ctx subject p (A atom) ->
      NommEval ctx subject (Nomm.op4 p) (A (atom + 1))

  | op5 {subject p q left right} :
      NommEval ctx subject p left ->
      NommEval ctx subject q right ->
      NommEval ctx subject (Nomm.op5 p q) (eqCode left right)

  -- `run-nomm-1` branches on Hoon loobeans: `%&` is yes (`0`) and `%|` is no
  -- (`1`).  Other test nouns have no successful evaluation.
  | op6_yes {subject p q r out} :
      NommEval ctx subject p (A 0) ->
      NommEval ctx subject q out ->
      NommEval ctx subject (Nomm.op6 p q r) out

  | op6_no {subject p q r out} :
      NommEval ctx subject p (A 1) ->
      NommEval ctx subject r out ->
      NommEval ctx subject (Nomm.op6 p q r) out

  | op7 {subject p q subject' out} :
      NommEval ctx subject p subject' ->
      NommEval ctx subject' q out ->
      NommEval ctx subject (Nomm.op7 p q) out

  | op10 {subject axis replacement editedBase replacementOut baseOut out} :
      NommEval ctx subject replacement replacementOut ->
      NommEval ctx subject editedBase baseOut ->
      Edit axis replacementOut baseOut out ->
      NommEval ctx subject (Nomm.op10 axis replacement editedBase) out

  | op11_static {subject tag body q out} :
      NommEval ctx subject q out ->
      NommEval ctx subject (Nomm.op11Static tag q body) out

  | op11_dynamic {subject tag hint body q hintOut out} :
      NommEval ctx subject hint hintOut ->
      NommEval ctx subject q out ->
      NommEval ctx subject (Nomm.op11Dynamic tag hint q body) out

-- No `op12` constructor: current SKA execution treats scry as unsupported.

def JetCorrect (ctx : Context) : Prop :=
  forall {subject formula out}, ctx.jet subject formula out -> Nock.Eval subject formula out

def EquivalentUnder (ctx : Context) (sock : Sock) (formula : Noun)
    (code : Nomm) : Prop :=
  forall {subject out}, Sock.Matches sock subject ->
    (Nock.Eval subject formula out ↔ NommEval ctx subject code out)

def CodeCorrect (ctx : Context) : Prop :=
  forall {bell code}, ctx.code bell code -> EquivalentUnder ctx bell.bus bell.fol code

def ContextCorrect (ctx : Context) : Prop :=
  JetCorrect ctx ∧ CodeCorrect ctx

-- A stable analyzer should eventually be represented as a relation whose
-- constructors mirror the corrected SKA pipeline:
--
--   scan / fol-loop -> analysis-time `nomm`
--   rewrite / cook  -> post-analysis `Nomm`
--   match-sock      -> selected entry applicable to the requested subject sock
--
-- This file intentionally does not define that relation yet.  The current Hoon
-- analyzer is known to be in flux, so the relation is a parameter below.
structure AnalyzerOutput where
  analyzedSock : Sock
  analyzedFormula : Noun
  code : Nomm

-- A certificate for a single analyzer output.  This is what the eventual
-- analysis proof must produce, not an assumption about the language semantics.
structure AnalyzerOutputCertificate (ctx : Context) (inputSock : Sock)
    (inputFormula : Noun) (output : AnalyzerOutput) where
  -- The selected table entry is for the same input formula.  In `run-nomm-1`
  -- this is the lookup by `fols.bol` followed by `match-sock`.
  formula_eq : output.analyzedFormula = inputFormula

  -- The selected entry's required subject template is no more specific than the
  -- requested input template.  This is the `match-sock` / `huge:so` obligation.
  applicable : Sock.Huge output.analyzedSock inputSock

  -- The selected Nomm body is semantically equivalent at the selected template.
  -- This is the hard theorem produced by induction over the analyzer derivation
  -- plus global invariants for memoized/direct-call entries.
  sound : EquivalentUnder ctx output.analyzedSock output.analyzedFormula output.code

theorem AnalyzerOutputCertificate.equivalent {ctx : Context} {inputSock : Sock}
    {inputFormula : Noun} {output : AnalyzerOutput}
    (cert : AnalyzerOutputCertificate ctx inputSock inputFormula output) :
    EquivalentUnder ctx inputSock inputFormula output.code := by
  intro subject out hmatch
  have analyzedMatches : Sock.Matches output.analyzedSock subject :=
    cert.applicable hmatch
  simpa [cert.formula_eq] using cert.sound analyzedMatches

-- Future theorem shape for the corrected analyzer.
--
-- If `Analyzes ctx inputSock inputFormula output` is the stabilized analysis
-- relation, then proving `AnalyzerRelationSound Analyzes` is the missing
-- algorithm-level result.  It says the analyzer produces a semantic certificate
-- for every output, assuming the runtime code and jet context is itself correct.
def AnalyzerRelationSound
    (Analyzes : Context -> Sock -> Noun -> AnalyzerOutput -> Prop) : Prop :=
  forall {ctx inputSock inputFormula output},
    ContextCorrect ctx ->
    Analyzes ctx inputSock inputFormula output ->
    AnalyzerOutputCertificate ctx inputSock inputFormula output

theorem AnalyzerRelationSound.equivalent
    {Analyzes : Context -> Sock -> Noun -> AnalyzerOutput -> Prop}
    (sound : AnalyzerRelationSound Analyzes)
    {ctx : Context} {inputSock : Sock} {inputFormula : Noun}
    {output : AnalyzerOutput}
    (hctx : ContextCorrect ctx)
    (hanalyzes : Analyzes ctx inputSock inputFormula output) :
    EquivalentUnder ctx inputSock inputFormula output.code :=
  (sound hctx hanalyzes).equivalent

theorem equivalent_terminates {ctx : Context} {sock : Sock} {formula : Noun}
    {code : Nomm}
    (equiv : EquivalentUnder ctx sock formula code)
    {subject : Noun}
    (hmatch : Sock.Matches sock subject) :
    (∃ out, Nock.Eval subject formula out) ↔
      (∃ out, NommEval ctx subject code out) := by
  constructor
  · intro h
    rcases h with ⟨out, eval⟩
    exact ⟨out, (equiv hmatch).mp eval⟩
  · intro h
    rcases h with ⟨out, eval⟩
    exact ⟨out, (equiv hmatch).mpr eval⟩

theorem equivalent_same_results {ctx : Context} {sock : Sock} {formula : Noun}
    {code : Nomm}
    (equiv : EquivalentUnder ctx sock formula code)
    {subject : Noun}
    (hmatch : Sock.Matches sock subject) :
    (fun out => Nock.Eval subject formula out) =
      (fun out => NommEval ctx subject code out) := by
  funext out
  exact propext (equiv hmatch)

-- A small formal package for the same proof obligation, specialized to a single
-- Nomm body rather than an `AnalyzerOutput` record.  This is convenient when a
-- caller already has a selected code value and wants to state the equivalence
-- certificate directly.
structure AnalysisCertificate (ctx : Context) (inputSock : Sock)
    (inputFormula : Noun) (code : Nomm) where
  analyzedSock : Sock
  analyzedFormula : Noun
  formula_eq : analyzedFormula = inputFormula
  applicable : Sock.Huge analyzedSock inputSock
  sound : EquivalentUnder ctx analyzedSock analyzedFormula code

theorem AnalysisCertificate.equivalent {ctx : Context} {inputSock : Sock}
    {inputFormula : Noun} {code : Nomm}
    (cert : AnalysisCertificate ctx inputSock inputFormula code) :
    EquivalentUnder ctx inputSock inputFormula code := by
  intro subject out hmatch
  have analyzedMatches : Sock.Matches cert.analyzedSock subject :=
    cert.applicable hmatch
  simpa [cert.formula_eq] using cert.sound analyzedMatches

end Nomm
end Formalization
