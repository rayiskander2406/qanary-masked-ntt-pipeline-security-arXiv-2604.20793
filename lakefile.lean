import Lake
open Lake DSL

package qanaryPaper4 where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "322515540d7f"

-- Git dependency on Paper 3 artifact, pinned to the v1.0.0 tag.
-- Paper 3's public repo exposes `lean_lib QanaryUniversal` and `package qanaryUniversal`.
require qanaryUniversal from git
  "https://github.com/rayiskander2406/qanary-universal-masking-proofs-arXiv-2604.18717" @ "v1.0.0"

@[default_target]
lean_lib QanaryPaper4
