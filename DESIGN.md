# Paper 4 Scaffold

## Title
"Fresh Masking Makes NTT Pipelines Composable: Machine-Checked Proofs for Arithmetic Masking in PQC Hardware"
([arXiv:2604.20793](https://arxiv.org/abs/2604.20793))

## One-Sentence Citation Summary
Iskander and Kirah proved that pipelined NTT stages with fresh per-stage masking are first-order probing secure, with a machine-checked Lean 4 proof universal over all positive moduli q.

## Status

| Component | File | Sorry Count | Status |
|-----------|------|-------------|--------|
| Basic definitions | `Basic.lean` | **0** | **Complete** |
| **T1-r (Gate 1)** | `ProbBridge.lean` | **0** | **PROVEN** |
| **butterfly_wire_count_eq_one** | `Composition.lean` | **0** | **PROVEN** — fundamental lemma |
| **butterfly_marginal_vi** | `Composition.lean` | **0** | **PROVEN** — corollary (both sides = 1) |
| **ntt_pipeline_composition** | `Composition.lean` | **0** | **PROVEN** — k-stage pipeline secure |
| pipelineStateAt_update_future | `Composition.lean` | **0** | **PROVEN** — invariance under future update |
| **Total** | 3 files | **0 sorry** | **ALL GATES CLOSED** |

## Build
- Lean toolchain: `leanprover/lean4:v4.30.0-rc1`
- Mathlib: `322515540d7f` (same as Paper 3)
- Dependency: `qanaryUniversal` via Lake git dep pinned to Paper 3 `v1.0.0` (see `lakefile.lean`)
- Build: 1,738 jobs, 0 errors, **0 warnings, 0 sorry**

## Gate 1: r-Bearing Bridge — CLOSED

T1-r is proven. The proof is 5 lines:
```lean
theorem t1_r_bearing ... := by
  unfold marginalHistogramR
  congr 1
  ext ⟨s₁, r⟩
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; rw [← hw s₁ r x x']; exact h
  · intro h; rw [hw s₁ r x x']; exact h
```

The key insight (inherited from Paper 3): `ValueIndependentR` makes the filter predicate identical for all x, so `Finset.filter` produces the same set, hence same cardinality.

`MutualInfoZero` is defined as an abbreviation for `HasConstantMarginalR`, with Observation 3.1 documenting the equivalence to I(x;w)=0 under uniform measure. Shannon entropy/mutual information is absent from Mathlib4 (only in PFR), so the algebraic proxy is the correct approach.

## Gate 2: NTT Stage Composition — CLOSED (2026-04-13)

### Key Discovery: Butterfly Wire Count = 1

`ButterflyValueIndependent` (pointwise, masks fixed) is FALSE for wires 0, 2.
The correct property is `ButterflyMarginalVI` (marginal over fresh mask m).

The fundamental lemma (`butterfly_wire_count_eq_one`) proves:
for ANY butterfly inputs, each output wire has exactly ONE bfMask
producing each value v. This is because:
- Wire 0 = c - m (translation bijection, card = 1)
- Wire 1 = m (identity, card = 1)
- Wire 2 = c' - m (translation bijection, card = 1)
- Wire 3 = m (identity, card = 1)

This is a NAMED CONTRIBUTION (not just a proof technique):
**The Cooley-Tukey butterfly with fresh output masking has a
uniform marginal over the mask, universally in Z_q for all q > 0.**

### Pipeline Composition = Corollary

`ntt_pipeline_composition` proves `PipelineUniform` for all k-stage
pipelines. The proof decomposes pipelineStateAt at each stage into
a butterflyOutput call, uses the invariance lemma to show earlier
stages are unaffected by `Function.update` at the current stage,
then applies `butterfly_wire_count_eq_one`.

No induction on k needed for the security property.
The induction in `pipelineStateAt_update_future` is structural
(showing invariance under future updates), not a security argument.

### Mathematical Resolution: Fresh Re-Masking

Adams Bridge does NOT perform fresh re-masking between NTT stages. Masking is active only in round 0; rounds 1-3 proceed unmasked. The composition theorem is about an **idealized pipeline** — it gives a prescriptive result:

> "If you design with fresh per-stage re-masking, composition holds. Adams Bridge violates this hypothesis — that is why it is insecure."

### Closest Composition Results in the Literature

Prior probing-security frameworks DO handle composition of masked
gadgets over arbitrary rings and fields — in particular, the
EasyCrypt formalizations by Barthe et al. (CCS 2015, CCS 2016) are
ring-generic. A blanket "Boolean-only" characterization of the
literature would be inaccurate.

The distinguishing contributions of this work, relative to the
closest prior art, are:

| Axis | Prior state of the art | This work |
|------|------------------------|-----------|
| Gadget topology | Abstract masked gadgets | Concrete Cooley-Tukey NTT butterfly |
| Composition mechanism | Generic refresh (ISW) / SNI composition | Pipeline-stage composition with inter-stage re-masking |
| Mechanization | Framework-level (EasyCrypt) or informal | Lean 4 + Mathlib, zero sorry, kernel-verified |
| Parametricity | Fixed fields or mostly-universal | Universal over all positive moduli q |
| Hardware integration | Standalone frameworks | Integrated with QANARY SDA + security margin analyses |

Historical references (for context; none of these contradict our
contribution, they set the landscape this work extends):

| Framework | Representative domain | Composition mechanism |
|-----------|-----------------------|------------------------|
| ISW 2003 | GF(2) private circuits | Refresh gadget |
| Barthe et al. CCS 2015/2016 | Software masking, ring-generic | EasyCrypt t-SNI composition |
| PINI (Cassiers, Standaert 2020) | Hardware masking | Trivial composition under PINI |
| DOM (Gross, Mangard, Korak, CHES 2016) | Hardware pipelines | Pipeline registers + fresh random |

### Q1–Q4 Resolved (2026-04-13)

| Q | Resolution |
|---|-----------|
| Q1 | Adams Bridge: zero output re-masking. Model: 1 bf mask + 2 re-mask/stage |
| Q2 | ISW 1st-order = 1 probe total/cycle. PipelineVI = ∀ stage ∀ wire |
| Q3 | Twiddles are public (FIPS ROM). Universally quantified |
| Q4 | Barrett internal to BFU. Composition = butterfly-only |

### CRITICAL DISCOVERY: Pointwise VI is False

`ButterflyValueIndependent` (pointwise, masks fixed) is FALSE for wires 0, 2.
Wire 0 = a + tw*b - m. Changing a changes the wire value.

The CORRECT property is `ButterflyMarginalVI` (marginal over m):
- Wire 0: |{m : a+tw*b-m = v}| = 1, regardless of (a,b)
- Wire 1: m itself, trivially independent of secrets
- This is the counting approach, not the pointwise approach

This shifts Gate 2 from an inductive composition proof to a
per-stage marginal independence proof. The composition is almost
trivial once `butterfly_marginal_vi` is proven.

### Addressing "Isn't This Trivial?"

A reviewer may observe that the core math is a one-line fact (c - m = v
has a unique solution in Z_q). The paper must address this head-on:

1. **Pointwise VI is false** — the "obvious" security property
   (ButterflyValueIndependent) is wrong. butterfly_vi_pointwise_false
   proves this with a concrete counterexample (q=5, tw=1). A designer
   who checks pointwise independence and declares their pipeline secure
   would be wrong. The correct property (marginal VI) is non-obvious.

2. **No prior formalization of this specific topology** — while
   Barthe et al.'s EasyCrypt framework handles ring-generic masked
   gadgets at the framework level, no prior work states or proves
   the arithmetic Z_q Cooley-Tukey butterfly pipeline composition
   theorem as a concrete machine-checked result. The gap addressed
   here is specificity to the NTT butterfly circuit topology under
   inter-stage re-masking, not the theoretical existence of
   arithmetic probing composition.

3. **The Lean artifact is FIPS-citable** — hardware designers seeking
   FIPS 140-3 certification can reference a machine-checked proof that
   their pipeline architecture is secure, rather than arguing informally.
   This has concrete regulatory value.

4. **The linearity observation IS the contribution** — recognizing that
   the CT butterfly is affine in the mask, and that this gives uniform
   marginals for free, is the insight. The paper frames this as "we
   observe that..." not "we discover that..."

### Remaining Open

5. **Q5: T6 interaction** — Does overapproximation compose? (Limitation, not theorem)

### Estimated Effort (ACTUAL)
- ~~Resolve Q1-Q4: 1 session~~ DONE
- ~~Fill PipelineValueIndependent: 1 session~~ DONE
- ~~Prove butterfly_marginal_vi: ~30min~~ DONE (translation bijection)
- ~~Prove ntt_pipeline_composition: ~2h~~ DONE (invariance + butterfly)
- Audit + paper writing: 2 sessions (10h)
- **Proofs complete in 3 sessions total. Paper writing remains.**

## Paper Structure

1. Introduction — The pipeline security problem; FIPS 140-3 motivation
2. Background — Paper 3 results (cite); gap in arithmetic masking literature
3. Preliminaries
   3.1 The r-bearing bridge (T1-r) — closes Paper 3 limitation, 5-line proof
   3.2 Butterfly model — idealized CT butterfly in Z_q
4. Per-Context Uniformity (Main Result)
   4.1 butterfly_wire_count_eq_one — fundamental lemma
   4.2 Why pointwise VI is false — the non-obvious trap (counterexample)
   4.3 Pipeline first-order security — PipelineUniform theorem
5. Application to Adams Bridge — two independent failures: intra-stage (Papers 1-2) + inter-stage (this work)
6. Implications — FIPS certification; design methodology; what designers can now cite
7. Limitations — higher-order; glitch model; nonlinear gadgets (Barrett); the trivial-math objection addressed honestly
8. Conclusion

## Key Mathlib Infrastructure Used

| What | Where |
|------|-------|
| PMF type | `Mathlib.Probability.ProbabilityMassFunction` |
| Fintype products | `Mathlib.Data.Fintype.Prod` (automatic for ZMod q × Fin ρ) |
| ZMod CommRing | `Mathlib.Data.ZMod.{Defs,Basic}` (unconditional) |
| ZMod Field | `Mathlib.Algebra.Field.ZMod` (when prime) |
| Finset.card_image | `Mathlib.Data.Finset.{Card,Image}` |
| Fin induction | `Init.Data.Fin.Lemmas` |
| Function composition | `Mathlib.Logic.Function.Basic` |

## Mathlib Gaps

| Gap | Impact | Workaround |
|-----|--------|------------|
| Shannon entropy | Cannot formalize I(x;w)=0 directly | `MutualInfoZero` algebraic proxy + Observation |
| Mutual information | Same | Same |
| PMF-IndepFun bridge | Cannot connect PMF independence to measure-theoretic | Document equivalence |
| List.foldl_comp | No pipeline composition lemma | Build custom for NTT pipeline |
