import Lake
open Lake DSL

package formalization where
  version := v!"0.2.0"

/-- The trusted part: the Nock specification, `cue`, the pill and the
statements.  It has no proofs and imports nothing from `lemmas`. -/
@[default_target]
lean_lib core where
  globs := #[.submodules `core]

/-- Everything else: models, tactics and proofs. -/
@[default_target]
lean_lib lemmas where
  globs := #[.submodules `lemmas]
