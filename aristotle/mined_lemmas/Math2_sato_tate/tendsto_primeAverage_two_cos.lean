/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

theorem tendsto_primeAverage_two_cos (θ : ℕ → ℝ) (h : SatoTateWeak θ) :
    Tendsto (primeAverage θ fun t => 2 * Real.cos t) atTop (𝓝 0) := by
  have := h twoCosBCF
  rwa [show (∫ t, twoCosBCF t ∂satoTateMeasure) = 0 from satoTate_first_moment] at this

/-- Under the Sato–Tate law, the averages of `a_p²/p = (2 cos θ_p)²` over the primes tend to `1`. -/
