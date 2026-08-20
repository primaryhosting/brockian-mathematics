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

lemma memLp_rescaledWalk (hL2 : ∀ i, MemLp (X i) 2 μ) (n : ℕ) (r : ℝ) :
    MemLp (rescaledWalk X n r) 2 μ := by
  have h : MemLp (fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i ω) 2 μ := by
    have h0 := memLp_finset_sum' (Finset.range ⌊(n : ℝ) * r⌋₊) (fun i (_ : i ∈ _) => hL2 i)
    rwa [show (∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i)
      = (fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i ω) from
      funext fun ω => by simp] at h0
  show MemLp (fun ω => (∑ i ∈ Finset.range ⌊(n : ℝ) * r⌋₊, X i ω) / Real.sqrt n) 2 μ
  simpa [div_eq_inv_mul] using h.const_mul (Real.sqrt n)⁻¹

/-- The variance of an increment of the rescaled walk converges to the length of the time
interval, as for Brownian motion. -/
