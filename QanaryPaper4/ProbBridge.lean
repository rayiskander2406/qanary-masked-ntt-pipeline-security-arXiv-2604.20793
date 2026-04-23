/-
  QanaryPaper4.ProbBridge
  =======================
  Gate 1: The r-bearing bridge.

  Proves that Paper 3's r-free value-independence theorem (T1)
  extends to the r-bearing model, closing the gap explicitly
  stated in Paper 3's limitations.

  Main result:
    T1-r: ValueIndependentR w → HasConstantMarginalR w

  This immediately gives MutualInfoZero w (= I(x; w) = 0)
  since MutualInfoZero is defined as HasConstantMarginalR.

  Paper reference: Section 3, "The r-Bearing Bridge"
-/

import QanaryPaper4.Basic

open BigOperators Finset

/-! ## T1-r: Value-Independence Implies Constant Marginal (r-bearing)

  Proof strategy:
  The filter set {(s₁, r) : w(x - s₁, s₁, r) = v} has the same
  cardinality for all x.

  For each fixed r, the inner filter {s₁ : w(x - s₁, s₁, r) = v}
  has the same cardinality by Paper 3's T1 argument (the predicate
  is the same for all x because ValueIndependentR holds pointwise).

  Therefore the product filter over (s₁, r) also has the same
  cardinality, since it decomposes as a disjoint union over r
  of equal-cardinality inner filters.

  Alternatively: the filter predicate itself is identical for all x
  (by ValueIndependentR), so the filter sets are equal, hence
  equal cardinality. This is the same proof structure as Paper 3's
  T1 — the r parameter is just an additional universal quantifier
  in the pointwise equality. -/

/-- **T1-r (r-bearing bridge).**
    If w is value-independent under the r-bearing model, then
    the marginal histogram over (s₁, r) is constant in x.

    Universal over: all q > 0, all ρ ≥ 0, all wire functions w,
    all output types β, all x, x', v. -/
theorem t1_r_bearing
    {q : ℕ} [NeZero q] {ρ : ℕ} {β : Type*} [DecidableEq β]
    (w : WireFunctionR q ρ β)
    (hw : ValueIndependentR w)
    (x x' : ZMod q) (v : β) :
    marginalHistogramR w x v = marginalHistogramR w x' v := by
  unfold marginalHistogramR
  congr 1
  ext ⟨s₁, r⟩
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; rw [← hw s₁ r x x']; exact h
  · intro h; rw [hw s₁ r x x']; exact h

/-- T1-r implies MutualInfoZero (which IS HasConstantMarginalR). -/
theorem value_independence_r_implies_mutual_info_zero
    {q : ℕ} [NeZero q] {ρ : ℕ} {β : Type*} [DecidableEq β]
    (w : WireFunctionR q ρ β)
    (hw : ValueIndependentR w) :
    MutualInfoZero w :=
  fun x x' v => t1_r_bearing w hw x x' v

/-! ## Lifting Paper 3's r-free results

  Paper 3's WireFunction q β is a special case of WireFunctionR q 1 β.
  We show the embedding preserves value-independence. -/

/-- Embed an r-free wire function into the r-bearing model with ρ = 1. -/
def liftToR {q : ℕ} {β : Type*} (w : WireFunction q β) :
    WireFunctionR q 1 β :=
  fun s₀ s₁ _ => w s₀ s₁

/-- Lifting preserves value-independence. -/
theorem lift_preserves_vi {q : ℕ} [NeZero q] {β : Type*}
    (w : WireFunction q β) (hw : ValueIndependent w) :
    ValueIndependentR (liftToR w) := by
  intro s₁ r x x'
  exact hw s₁ x x'

/-! ## Observation 3.1: MutualInfoZero ↔ I(x; w) = 0

  Under the uniform distribution on (s₁, r) ∈ ZMod q × Fin ρ:

    P(w = v | x) = marginalHistogramR w x v / (q * ρ)

  If this is constant in x (i.e., MutualInfoZero holds), then:

    P(w = v | x) = P(w = v)   for all x, v

  which means w and x are independent, hence I(x; w) = 0.

  Conversely, I(x; w) = 0 implies P(w = v | x) = P(w = v) for
  all x, v (for discrete distributions), hence MutualInfoZero.

  This equivalence is standard information theory. We state it
  as a formal observation rather than proving it in Lean, because
  Mathlib4 does not currently have Shannon entropy or mutual
  information definitions. (PFR project has them but they are
  not upstreamed.)

  When Mathlib eventually provides `measureEntropy` and
  `measureMutualInfo`, the equivalence becomes a one-theorem
  bridge. For now, MutualInfoZero is the correct algebraic proxy. -/
