import Lake
open Lake DSL

package «PvsNPProof» where
  -- Basic Lean options mirroring the other RS projects
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- Optimize build performance
  buildType := BuildType.release
  -- Enable build caching and parallel compilation
  moreLeanArgs := #[
    "--tstack=100000",
    "--threads=8",
    "-j", "8"  -- Parallel compilation
  ]
  moreServerArgs := #[
    "--tstack=100000"
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
