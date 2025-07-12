import Lake
open Lake DSL

package «PvsNPProof» where
  -- Basic Lean options mirroring the other RS projects
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

@[default_target]
lean_lib «PvsNP» where
  srcDir := "Src"
  roots := #[`PvsNP]

-- Also build the RecognitionScience module
lean_lib «RecognitionScience» where
  srcDir := "Src"
  roots := #[`RecognitionScience]
