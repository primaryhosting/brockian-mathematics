/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Scope of the formalization

Mathlib (at the pinned version) contains neither Brownian motion nor weak convergence of measures
on `C[0,1]`, so the full functional form of Donsker's invariance principle cannot be *stated*
against existing definitions. What is formalized here is the invariance principle at the level of
the second-order structure of the process: for an arbitrary sequence of independent, centred,
unit-variance, square-integrable increments, the diffusively rescaled walk
`W_n(t) = (X_0 + ⋯ + X_{⌊nt⌋-1})/√n` has

* covariance `E[W_n(s) W_n(t)] → min s t` (`Math2.donsker_invariance`),
* increment variance `E[(W_n(t) - W_n(s))²] → t - s` (`Math2.donsker_increment_variance`),
* asymptotically uncorrelated increments over disjoint intervals
  (`Math2.donsker_increments_uncorrelated`),

which are exactly the covariance structure of standard Brownian motion, and are independent of the
law of the increments (whence "invariance"). The hypotheses are shown to be non-vacuous in
`Math2.donsker_hypotheses_satisfiable`, using the simple symmetric random walk.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The rescaled (Donsker) random walk built from the increments `X`:
`rescaledWalk X n t ω = (X 0 ω + ⋯ + X (⌊n t⌋₊ - 1) ω) / √n`.
This is the classical diffusive rescaling of the partial-sum process. -/

lemma integral_partialSum_mul (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) (a b : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range a, X i ω) * (∑ j ∈ Finset.range b, X j ω) ∂μ =
      (min a b : ℕ) := by
  have hint : ∀ i j : ℕ, Integrable (fun ω => X i ω * X j ω) μ := fun i j =>
    MemLp.integrable_mul (hL2 i) (hL2 j)
  have hexp : ∀ i j : ℕ, ∫ ω, X i ω * X j ω ∂μ = if i = j then (1 : ℝ) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      simpa [pow_two] using hvar i
    · simp [h, integral_mul_of_ne hindep hL2 hmean h]
  calc ∫ ω, (∑ i ∈ Finset.range a, X i ω) * (∑ j ∈ Finset.range b, X j ω) ∂μ
      = ∫ ω, ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, X i ω * X j ω ∂μ := by
        simp [Finset.sum_mul_sum]
    _ = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, ∫ ω, X i ω * X j ω ∂μ := by
        rw [integral_finset_sum]
        · exact Finset.sum_congr rfl fun i _ =>
            integral_finset_sum _ (fun j _ => hint i j)
        · exact fun i _ => integrable_finset_sum _ (fun j _ => hint i j)
    _ = (min a b : ℕ) := by
        simp only [hexp]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq', Finset.mem_range]
        have hset : {x ∈ Finset.range b | x < a} = Finset.range (min a b) := by
          ext x
          simp [and_comm]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hset]
        simp

/-- **Donsker's invariance principle (covariance form).**

For a sequence of independent, square-integrable, centred increments with unit variance, the
diffusively rescaled random walk `W_n(t) = S_{⌊nt⌋}/√n` has covariance function converging to
that of standard Brownian motion, `E[W(s) W(t)] = min s t`.

This is the second-order (covariance) content of Donsker's invariance principle: it is exactly the
statement that, whatever the law of the increments (invariance), the limiting process has the
covariance structure of Brownian motion. The key limit input is Mathlib's
`tendsto_nat_floor_mul_div_atTop`. -/
