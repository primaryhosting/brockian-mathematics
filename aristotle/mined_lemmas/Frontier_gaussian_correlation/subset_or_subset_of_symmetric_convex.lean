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

theorem subset_or_subset_of_symmetric_convex {K L : Set (Fin 1 → ℝ)}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (hKs : IsSymmetric K) (hLs : IsSymmetric L) :
    K ⊆ L ∨ L ⊆ K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp hcon.1
  obtain ⟨y, hyL, hyK⟩ := Set.not_subset.mp hcon.2
  rcases le_total |y 0| |x 0| with h | h
  · exact hyK (mem_of_abs_le_of_symmetric_convex hK hKs hxK h)
  · exact hxL (mem_of_abs_le_of_symmetric_convex hL hLs hyL h)

end OneDim

/-- For a probability measure, nested sets satisfy the correlation inequality trivially. -/
