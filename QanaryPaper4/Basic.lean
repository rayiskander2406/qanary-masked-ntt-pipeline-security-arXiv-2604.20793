/-
  QanaryPaper4.Basic
  ==================
  Extended definitions for Paper 4: r-bearing wire functions,
  pipeline models, and butterfly stage formalization.

  Builds on QanaryUniversal.Basic (Paper 3 definitions).

  Paper: "Fresh Masking Makes NTT Pipelines Composable:
  Machine-Checked Proofs for Arithmetic Masking in PQC Hardware"
  (Iskander & Kirah, arXiv:2604.20793, 2026). See README.md for
  full citation.
-/

import QanaryUniversal.Basic
import Mathlib.Data.Fintype.Prod

open BigOperators Finset

/-! ## r-Bearing Wire Function Model

  Paper 3's WireFunction models the r-free sub-theorem:
    WireFunction q β := ZMod q → ZMod q → β
                        (s₀,       s₁)    ↦ output

  Paper 4 extends this to include fresh randomness r ∈ Fin ρ:
    WireFunctionR q ρ β := ZMod q → ZMod q → Fin ρ → β
                           (s₀,       s₁,      r)   ↦ output

  When ρ = 1 (trivial randomness), WireFunctionR degenerates to
  WireFunction (up to currying). -/

/-- A wire function with fresh randomness domain Fin ρ.
    Maps (s₀, s₁, r) to an output value.
    s₀ = x - s₁ under arithmetic masking (reparametrized by secret x). -/
def WireFunctionR (q : ℕ) (ρ : ℕ) (β : Type*) :=
  ZMod q → ZMod q → Fin ρ → β

/-- Value-independence under the r-bearing model.
    For every fixed mask s₁ and randomness r, varying the secret x
    does not change the wire output.

    This is the natural extension of Paper 3's ValueIndependent:
    the r-free condition holds for every fixed r. -/
def ValueIndependentR {q : ℕ} [NeZero q] {ρ : ℕ} {β : Type*}
    (w : WireFunctionR q ρ β) : Prop :=
  ∀ (s₁ : ZMod q) (r : Fin ρ) (x x' : ZMod q),
    w (arithReparam q x s₁) s₁ r = w (arithReparam q x' s₁) s₁ r

/-- Marginal histogram over (s₁, r) for the r-bearing model.
    Counts the number of (s₁, r) pairs that produce output v
    when the secret is x.

    P(w = v | x) = marginalHistogramR w x v / (q * ρ) -/
noncomputable def marginalHistogramR {q : ℕ} [NeZero q] {ρ : ℕ} {β : Type*}
    [DecidableEq β]
    (w : WireFunctionR q ρ β) (x : ZMod q) (v : β) : ℕ :=
  (Finset.univ (α := ZMod q × Fin ρ)).filter
    (fun p => w (arithReparam q x p.1) p.1 p.2 = v) |>.card

/-- Constant marginal under the r-bearing model.
    The full distributional security property:
    the histogram does not depend on x. -/
def HasConstantMarginalR {q : ℕ} [NeZero q] {ρ : ℕ} {β : Type*}
    [DecidableEq β]
    (w : WireFunctionR q ρ β) : Prop :=
  ∀ (x x' : ZMod q) (v : β),
    marginalHistogramR w x v = marginalHistogramR w x' v

/-- MutualInfoZero: algebraic proxy for I(x; w) = 0.

    Under uniform distribution on (s₁, r), the conditional
    distribution P(w = v | x) = marginalHistogramR w x v / (q * ρ).
    If this is constant in x, then I(x; w) = 0 by definition
    of mutual information.

    This predicate IS the content of I(x;w) = 0 without needing
    entropy definitions. The equivalence is documented in the paper
    as Observation 3.1. -/
abbrev MutualInfoZero {q : ℕ} [NeZero q] {ρ : ℕ} {β : Type*}
    [DecidableEq β]
    (w : WireFunctionR q ρ β) : Prop :=
  HasConstantMarginalR w

/-! ## NTT Butterfly Stage Model

  The Cooley-Tukey butterfly computes:
    a' = a + tw * b  (mod q)
    b' = a - tw * b  (mod q)

  Under first-order arithmetic masking with 2 shares:
    a = a₀ + a₁,  b = b₀ + b₁  (mod q)

  Each stage takes masked input shares and produces masked output
  shares, using a fresh mask m for re-sharing.

  IMPORTANT: This is an idealized model. Adams Bridge does NOT
  implement fresh re-masking between stages — that is why it is
  insecure. The composition theorem gives a prescriptive result:
  designs that DO use fresh re-masking get compositionality. -/

/-- A single NTT butterfly stage, parameterized by twiddle factor. -/
structure ButterflyStage (q : ℕ) where
  tw : ZMod q

/-- Output of a masked Cooley-Tukey butterfly.

    Input shares: (a₀, a₁) for a, (b₀, b₁) for b
    Fresh output mask: m
    Twiddle: tw

    Computes:
      a' = a₀ + a₁ + tw * (b₀ + b₁) = a + tw * b
      b' = a₀ + a₁ - tw * (b₀ + b₁) = a - tw * b

    Re-shares outputs with fresh mask m:
      out_a = (a' - m, m)
      out_b = (b' - m, m)

    Returns (out_a₀, out_a₁, out_b₀, out_b₁). -/
def butterflyOutput (q : ℕ) [NeZero q] (stage : ButterflyStage q)
    (a₀ a₁ b₀ b₁ m : ZMod q) :
    ZMod q × ZMod q × ZMod q × ZMod q :=
  let twb := stage.tw * (b₀ + b₁)
  let a' := a₀ + a₁ + twb
  let b' := a₀ + a₁ - twb
  (a' - m, m, b' - m, m)

/-- Select one of the 4 output wires by index. -/
def selectWire {α : Type*} (i : Fin 4) (out : α × α × α × α) : α :=
  match i with
  | ⟨0, _⟩ => out.1
  | ⟨1, _⟩ => out.2.1
  | ⟨2, _⟩ => out.2.2.1
  | ⟨3, _⟩ => out.2.2.2
  -- Lean's Fin 4 pattern matching covers all cases

/-- **Pointwise value-independence is FALSE for the butterfly.**

    Wire 0 = a + tw*b - m, which changes when the secret a changes
    (with masks fixed). This definition exists as a COUNTEREXAMPLE
    to document why ButterflyMarginalVI (in Composition.lean) is
    the correct security property, not this pointwise version.

    The correct property marginalizes over the fresh mask m.
    See: butterfly_marginal_vi, butterfly_wire_count_eq_one. -/
def ButterflyValueIndependent (q : ℕ) [NeZero q]
    (stage : ButterflyStage q) : Prop :=
  ∀ (wire : Fin 4)
    (a b a₁ b₁ m : ZMod q)
    (a' b' : ZMod q),
    selectWire wire (butterflyOutput q stage (a - a₁) a₁ (b - b₁) b₁ m) =
    selectWire wire (butterflyOutput q stage (a' - a₁) a₁ (b' - b₁) b₁ m)

/-- Pointwise value-independence fails: wire 0 depends on the secret.
    Witness: q=5, tw=1, a=0, b=0, a₁=0, b₁=0, m=0, a'=1, b'=0.
    Wire 0 under (a=0): 0+1*0-0 = 0. Wire 0 under (a'=1): 1+1*0-0 = 1. 0 ≠ 1. -/
theorem butterfly_vi_pointwise_false :
    ¬ ButterflyValueIndependent 5 ⟨1⟩ := by
  intro h
  have := h ⟨0, by omega⟩ 0 0 0 0 0 1 0
  simp [butterflyOutput, selectWire] at this
  exact absurd this (by decide)

/-! ## Pipeline Infrastructure

  Resolutions (Q1–Q4, session 2026-04-13):
  Q1: Adams Bridge uses zero output re-masking (the vulnerability).
      Idealized model uses 1 butterfly mask + 2 inter-stage re-masks.
  Q2: ISW first-order probing = one probe total per clock cycle.
      PipelineVI := ∀ stage, ∀ wire at that stage, value-independent.
  Q3: Twiddle factors are public (FIPS-defined ROM constants).
      Already universally quantified via ButterflyStage.tw.
  Q4: Barrett reduction is internal to each BFU. Composition scopes
      to butterfly stages only. -/

/-- A k-stage NTT pipeline: sequence of butterfly stages.
    Each stage has a public twiddle factor (Q3: FIPS-defined constant). -/
def NTTPipeline (q : ℕ) (k : ℕ) := Fin k → ButterflyStage q

/-- Fresh randomness for one pipeline stage.
    Q1 resolution: 1 butterfly output mask + 2 inter-stage re-masking masks. -/
structure StageRandomness (q : ℕ) where
  /-- Fresh mask used inside the butterfly for output re-sharing. -/
  bfMask : ZMod q
  /-- Fresh mask for a-path re-masking between stages. -/
  remaskA : ZMod q
  /-- Fresh mask for b-path re-masking between stages. -/
  remaskB : ZMod q
  deriving DecidableEq

/-- StageRandomness is a finite type (isomorphic to ZMod q × ZMod q × ZMod q). -/
noncomputable instance {q : ℕ} [NeZero q] : Fintype (StageRandomness q) :=
  Fintype.ofEquiv (ZMod q × ZMod q × ZMod q)
    { toFun := fun ⟨a, b, c⟩ => ⟨a, b, c⟩
      invFun := fun ⟨a, b, c⟩ => ⟨a, b, c⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }

/-- Fresh randomness for the entire k-stage pipeline. -/
def PipelineRandomness (q : ℕ) (k : ℕ) := Fin k → StageRandomness q

/-- The state flowing between pipeline stages: four shares (a₀, a₁, b₀, b₁).
    Invariant: a₀ + a₁ = a (the unmasked value), b₀ + b₁ = b. -/
abbrev PipelineState (q : ℕ) := ZMod q × ZMod q × ZMod q × ZMod q

/-- Apply inter-stage re-masking to decouple stages.
    Transforms (a₀, a₁, b₀, b₁) to (a₀ - rA, a₁ + rA, b₀ - rB, b₁ + rB).
    Preserves the sum invariant: (a₀ - rA) + (a₁ + rA) = a₀ + a₁.
    With rA, rB uniform and independent, the new shares are uniformly
    distributed conditioned on the unmasked values. -/
def remaskState {q : ℕ} [NeZero q]
    (state : PipelineState q) (rA rB : ZMod q) : PipelineState q :=
  (state.1 - rA, state.2.1 + rA,
   state.2.2.1 - rB, state.2.2.2 + rB)

/-- Compute pipeline state after executing stage i.
    Stage 0 applies the butterfly to the initial shares.
    Stage i+1 re-masks the output of stage i, then applies butterfly i+1.
    Q4 resolution: Barrett reduction is internal to each butterfly —
    the butterfly output is already modular-reduced. -/
def pipelineStateAt {q : ℕ} [NeZero q] {k : ℕ}
    (pipeline : NTTPipeline q k)
    (rands : PipelineRandomness q k)
    (init : PipelineState q) :
    (i : Fin k) → PipelineState q
  | ⟨0, h⟩ =>
    butterflyOutput q (pipeline ⟨0, h⟩)
      init.1 init.2.1 init.2.2.1 init.2.2.2
      (rands ⟨0, h⟩).bfMask
  | ⟨n + 1, h⟩ =>
    let prev := pipelineStateAt pipeline rands init ⟨n, Nat.lt_of_succ_lt h⟩
    let remasked := remaskState prev
      (rands ⟨n, Nat.lt_of_succ_lt h⟩).remaskA
      (rands ⟨n, Nat.lt_of_succ_lt h⟩).remaskB
    butterflyOutput q (pipeline ⟨n + 1, h⟩)
      remasked.1 remasked.2.1 remasked.2.2.1 remasked.2.2.2
      (rands ⟨n + 1, h⟩).bfMask

/-! ## Scope and Limitations (from triple external audit, 2026-04-13)

  **Leakage model:** ISW value-probing only (one probe per clock cycle).
  Glitch-extended models (robust probing, Faust et al. 2018),
  transition-based leakage (Hamming distance), and random probing
  are out of scope. Threshold implementation properties (non-completeness,
  uniformity in the TI sense) are not claimed.

  **Probe target space:** The formalized security property (PipelineUniform
  in Composition.lean) covers the 4 output wires of each butterfly stage.
  Intermediate wires from inter-stage re-masking (e.g., a₀ - rA) are NOT
  explicitly covered. Their security is trivial — rA is fresh and uniform,
  so a₀ - rA is uniformly distributed regardless of a₀ — but this
  argument is not formalized in Lean. A complete ISW compliance proof
  would require extending the probe target enumeration to include these
  routing boundaries.

  **Butterfly model:** Idealized (no Barrett reduction internals, no
  carry chains, no gate-level intermediates). The composition theorem
  applies to the algebraic butterfly; gate-level verification is
  Paper 1's (QANARY / Structural Dependency Analysis) responsibility.

  **Shared mask:** Both output pairs share a single fresh mask m.
  Under first-order probing (one probe), this is secure. Under
  second-order probing, observing wire 0 (a'-m) and wire 2 (b'-m)
  reveals a'-b'. Higher-order masking requires independent masks.

  **remaskA/B role:** The formal security proof (PipelineUniform) does
  not exercise remaskA/B directly — butterfly_wire_count_eq_one holds
  for ANY inputs. The re-masking serves the FULL marginal argument
  (not formalized): without it, input shares to stage i+1 would be
  deterministic functions of stage i's bfMask, preventing independent
  summation across stages. -/
