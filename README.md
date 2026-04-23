# QanaryPaper4

**Machine-Checked Pipeline Composition for Masked NTT Hardware**

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.30.0--rc1-blue)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-322515540d7f-green)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Sorry-Free](https://img.shields.io/badge/sorry-0-brightgreen)]()

Machine-checked universal proofs that first-order arithmetic masking
composes securely across pipelined Number Theoretic Transform (NTT)
stages.

This is the artifact repository for:

> R. Iskander, K. Kirah. "Fresh Masking Makes NTT Pipelines Composable:
> Machine-Checked Proofs for Arithmetic Masking in PQC Hardware."
> [arXiv:2604.20793](https://arxiv.org/abs/2604.20793), 2026.

## Context: Prior Papers in the Series

This artifact extends the proof suite of three earlier papers:

- **Paper 1** — R. Iskander, K. Kirah. "Structural Dependency Analysis
  for Masked NTT Hardware: Scalable Pre-Silicon Verification of
  Post-Quantum Cryptographic Accelerators." 2026. *QANARY tool paper.
  Introduces Theorem 3.9.1 (value-independence ⟹ constant marginal)
  and machine-checks it at q = 5 via SMT.*
- **Paper 2** — R. Iskander, K. Kirah. "Partial NTT Masking in
  Post-Quantum Cryptography Hardware: A Security Margin Analysis."
  [arXiv:2604.03813](https://arxiv.org/abs/2604.03813), 2026. *Uses
  Theorem 3.9.1 as a premise in its security margin analysis.*
- **Paper 3** — R. Iskander, K. Kirah. "From Finite Enumeration to
  Universal Proof: Ring-Theoretic Foundations for PQC Hardware
  Masking Verification."
  [arXiv:2604.18717](https://arxiv.org/abs/2604.18717), 2026. *Lifts
  Paper 1's Theorem 3.9.1 (r-free sub-theorem) to a universal Lean 4
  proof. Its artifact is available at
  [qanary-universal-masking-proofs-arXiv-2604.18717](https://github.com/rayiskander2406/qanary-universal-masking-proofs-arXiv-2604.18717).*

This artifact **depends on Paper 3's artifact** via a Lake git
dependency pinned to Paper 3's `v1.0.0` tag
(`require qanaryUniversal from git ... @ "v1.0.0"` in `lakefile.lean`).
`lake update` fetches it automatically — no manual clone required. See
[Building](#building) below.

## What This Artifact Proves

This artifact contributes two results that together establish the
core invariant of first-order pipeline security:

1. **Gate 1 — The r-bearing bridge (`t1_r_bearing`).** Paper 3's
   Theorem 3.9.1 was proved only for the r-free sub-theorem (no
   fresh randomness). Gate 1 lifts it to the full r-bearing model
   in five lines of Lean: value-independence over
   `(s₁, r) ∈ ZMod q × Fin ρ` implies a constant marginal histogram.
   Closes Paper 3's explicit limitation.
2. **Gate 2 — Butterfly wire count and pipeline composition.** The
   fundamental lemma `butterfly_wire_count_eq_one` proves that each
   of the four output wires of a Cooley-Tukey butterfly has exactly
   one fresh-mask value producing each output value. From this, the
   k-stage `ntt_pipeline_composition` theorem follows: for every
   stage, every wire, every secret pair, the bfMask count conditional
   on the other randomness is exactly one — the per-context
   uniformity invariant.

## Theorem Index

| ID  | Statement | File | Lean Identifier |
|-----|-----------|------|-----------------|
| T1-r | r-bearing value-independence ⟹ constant marginal histogram | `ProbBridge.lean` | `t1_r_bearing` |
| T1-r' | T1-r ⟹ `MutualInfoZero` (algebraic proxy for I(x;w)=0) | `ProbBridge.lean` | `value_independence_r_implies_mutual_info_zero` |
| T1-r'' | r-free ⟹ r-bearing value-independence (lifting) | `ProbBridge.lean` | `lift_preserves_vi` |
| Counterex | Pointwise butterfly VI is FALSE (concrete witness at q = 5) | `Basic.lean` | `butterfly_vi_pointwise_false` |
| G2-fund | Butterfly wire count equals 1 (fundamental lemma) | `Composition.lean` | `butterfly_wire_count_eq_one` |
| G2-cor | Butterfly marginal is secret-independent | `Composition.lean` | `butterfly_marginal_vi` |
| G2-inv | Stage-i pipeline state is invariant under `update` at stage j > i | `Composition.lean` | `pipelineStateAt_update_future` |
| G2-main | k-stage NTT pipeline satisfies per-context uniformity | `Composition.lean` | `ntt_pipeline_composition` |
| G2-bridge | k = 1 single-stage full marginal (both sides = 1) | `Composition.lean` | `single_stage_full_marginal` |

All theorems are **sorry-free** and **kernel-verified**; none use
`native_decide`. `reproduce.py` tracks 9 identifiers — the 9 listed
above.

## Building

Requires [elan](https://github.com/leanprover/elan). The Paper 3
artifact dependency is pulled automatically via Lake's git-dependency
mechanism (pinned to tag `v1.0.0`) — no manual sibling clone required.

```bash
# Install elan (if not already)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Clone and build this artifact
git clone https://github.com/rayiskander2406/qanary-masked-ntt-pipeline-security-arXiv-2604.20793
cd qanary-masked-ntt-pipeline-security-arXiv-2604.20793
lake build
```

First build fetches Mathlib and the pinned Paper 3 artifact (~30 min cold).
Subsequent builds are incremental. For faster cold starts, run
`lake exe cache get` before `lake build` to download the pre-built
Mathlib olean cache (~5 min total vs ~30 min).

## Reproduction

```bash
# Full verification: build + zero-sorry scan + theorem check (~30 min cold, <1 min warm)
python3 reproduce.py

# Quick check: skip build, verify existing artifacts (<5 seconds)
python3 reproduce.py --check
```

The script enforces nine logical pass gates; each gate expands into
one or more individual `check()` lines in the script output (for
example, gate 5 produces three `check()` entries, one each for
`sorry`, `admit`, and `axiom`):

| # | Check | Expected |
|---|-------|----------|
| 1 | `lean-toolchain` exists and pins `leanprover/lean4:` | pass |
| 2 | `lakefile.lean` pins Mathlib to commit `322515540d7f` | pass |
| 3 | `lakefile.lean` declares Paper 3 git dep pinned to `v1.0.0` | pass |
| 4 | `lake build` exits with code 0 (skipped with `--check`) | pass |
| 5 | Zero `sorry`, `admit`, or `axiom` occurrences in tracked `.lean` sources | 0 found |
| 6 | All 9 expected theorem identifiers present in correct files | 9/9 |
| 7 | Repository structure complete (13 required files) | 13/13 |
| 8 | No `.docx`, `.tex`, `.bib`, `.pdf` files tracked in git | clean |
| 9 | No AI attribution tokens in tracked sources | 0 found |

Any failure prints a detailed `[FAIL]` line and returns non-zero exit code.

## Project Structure

```
QanaryPaper4/
  Basic.lean          -- r-bearing wire model, butterfly model,
                         pipeline infrastructure, pointwise-VI
                         counterexample
  ProbBridge.lean     -- Gate 1: T1-r bearing bridge (closes Paper 3
                         r-free limitation)
  Composition.lean    -- Gate 2: butterfly_wire_count_eq_one,
                         butterfly_marginal_vi,
                         pipelineStateAt_update_future,
                         ntt_pipeline_composition,
                         single_stage_full_marginal
QanaryPaper4.lean     -- Root import
```

## Key Insight

The k-stage NTT pipeline composition theorem does *not* require
induction on k. Each stage's output wire has exactly one bfMask
producing each output value (fundamental lemma,
`butterfly_wire_count_eq_one`). Future-stage `Function.update`
operations leave earlier-stage outputs invariant
(`pipelineStateAt_update_future`). Combining these gives the
per-context uniformity property for any stage, any wire, any secret
pair.

The proof is essentially algebraic: each butterfly output wire
is affine in the fresh mask m (either `c - m` or `m`), and the
equation `c - m = v` (or `m = v`) has exactly one solution in Z_q
for any target v. No higher-order masking theorems, no cascading
induction, no Boolean-specific tools — only ZMod ring axioms.

## Scope and Limitations

- **ISW first-order probing only.** One probe per clock cycle. No
  glitch-extended models (Faust et al. 2018), no transition leakage
  (Hamming distance), no random probing.
- **Per-context uniformity, not full marginal.** `PipelineUniform`
  establishes the core algebraic invariant. A complete first-order
  probing security proof also requires summing this invariant over
  all contexts (product over stage randomness); that summation is
  formalized in Lean only for k = 1 (`single_stage_full_marginal`),
  not general k, because it needs a `Fintype` instance for
  `PipelineRandomness q k` (q^(3k) elements).
- **Idealized butterfly.** No Barrett reduction internals, no carry
  chains, no gate-level intermediates. Gate-level analysis is the
  responsibility of the QANARY tool (Paper 1).
- **Shared output mask.** Both output share pairs share a single
  fresh mask. Secure under first-order probing; second-order probing
  (two wires) can defeat this. Higher-order masking requires
  independent masks.
- **Butterfly inter-stage routing wires.** The formal property
  covers the 4 butterfly output wires. Intermediate wires from the
  inter-stage re-masking (e.g., `a₀ - rA`) are not explicitly
  enumerated; their security is trivial (rA is fresh and uniform)
  but not formalized.

## Reproducibility Notes

- **Pinned toolchain.** `lean-toolchain` pins `leanprover/lean4:v4.30.0-rc1`
  and `lakefile.lean` pins Mathlib to commit `322515540d7f`. Same
  versions as Paper 3, so a machine that can build Paper 3 can build
  Paper 4 without re-fetching dependencies.
- **Cold build time.** First `lake build` fetches Mathlib
  (~1.3 GB, ~25-40 minutes). Subsequent incremental builds complete
  in under 30 seconds.
- **Cache re-use.** `lake exe cache get` populates the pre-built
  Mathlib olean cache (~4 GB) and reduces cold build time to under
  5 minutes.
- **Paper 3 dependency.** Lake pulls Paper 3's artifact as a git
  dependency pinned to tag `v1.0.0` (see `lakefile.lean`). This makes
  builds bit-reproducible against a fixed snapshot of Paper 3's proof
  suite. `lake-manifest.json` captures the exact commit SHA Lake
  resolved the tag to, so the build is fully pinned even if the tag
  were ever force-moved upstream.
- **Platform.** Verified on macOS (Apple Silicon and Intel) and Linux
  x86_64. Windows is expected to work via WSL2.
- **Python version.** `reproduce.py` is Python 3 standard library
  only; no external packages required.

## Design Document

See [DESIGN.md](DESIGN.md) for the proof strategy, the Q1-Q4
resolutions from the triple external adversarial audit, the
relationship to prior art (ISW 2003, t-SNI 2016, PINI 2020, DOM
2016, Barthe et al. CCS 2015/2016), and a discussion of the open
scoping questions (higher-order, glitch model, full marginal at
general k).

## Citation

If you use this artifact, please cite the paper:

```bibtex
@article{IskanderKirah2026FreshMasking,
  author  = {Ray Iskander and Khaled Kirah},
  title   = {Fresh Masking Makes NTT Pipelines Composable:
             Machine-Checked Proofs for Arithmetic Masking
             in PQC Hardware},
  journal = {arXiv preprint},
  year    = {2026},
  eprint  = {2604.20793},
  archivePrefix = {arXiv},
  primaryClass  = {cs.CR},
}
```

See [CITATION.cff](CITATION.cff) for the machine-readable citation.

## License

MIT. See [LICENSE](LICENSE).

## Authors

Ray Iskander (Verdict Security), Khaled Kirah (Ain Shams University)
