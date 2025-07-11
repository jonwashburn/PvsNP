import Lake
open Lake DSL

package «PvsNPProof» where
  -- Basic Lean options mirroring the other RS projects
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

-- Use ledger-foundation as a path dependency since it's in our repo
require RecognitionScience from "./ledger-foundation"

@[default_target]
lean_lib «PvsNP» where
  srcDir := "Src"
  roots := #[`PvsNP]
