import Mathlib
/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard (centered, identity–covariance) Gaussian measure on `Fin n → ℝ`:
the `n`-fold product of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem smul_mem_of_abs_le_one {K : Set V} (hK : Convex ℝ K) (hKs : IsSymmetric K)
    {x : V} (hx : x ∈ K) {c : ℝ} (hc : |c| ≤ 1) : c • x ∈ K := by
  have h1 : (0:ℝ) ≤ (1 + c) / 2 := by cases abs_le.mp hc; linarith
  have h2 : (0:ℝ) ≤ (1 - c) / 2 := by cases abs_le.mp hc; linarith
  have h3 : (1 + c) / 2 + (1 - c) / 2 = 1 := by ring
  have hmem := hK hx (hKs x hx) h1 h2 h3
  convert hmem using 1
  module

end Basic

section OneDim

/-- In dimension one, a symmetric convex set containing a point `u` contains every point `v`
that is no further from the origin. -/
