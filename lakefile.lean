import Lake
open Lake DSL

package «AVAnomalousRegularization» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

/-- The public formalization of Armstrong–Vicol, *Anomalous diffusion by fractal
homogenization*; supplies `AVenhance` and the vendored `Homogenization` carriers. -/
require AVAnomalousDiffusion from git
  "https://github.com/scottnarmstrong/AVAnomalousDiffusion.git" @
    "d4dbc7b11fbf350667013d5ac98a3686f44093f5"

@[default_target]
lean_lib «AVRegularity» where
  globs := #[.andSubmodules `AVRegularity]
  leanOptions := #[
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

/-- Mathlib-only statement of the main results, with one intentional `sorry` per theorem. -/
@[default_target]
lean_lib «AVRegularityChallenge» where
  roots := #[`AVRegularityChallenge]

/-- The Challenge statements proved from the library. -/
@[default_target]
lean_lib «AVRegularitySolution» where
  roots := #[`AVRegularitySolution]
