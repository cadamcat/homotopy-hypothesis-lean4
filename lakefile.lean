import Lake
open Lake DSL

package HomotopyHypothesis where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- OpenAI's globular library, licensed under Apache-2.0; see `THIRD_PARTY.md`. -/
lean_lib OAI where
  globs := #[.submodules `OAI.CategoryTheory.Globular]

@[default_target]
lean_lib HomotopyHypothesis
