import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/

lemma energy_lower_bound_real (h3 : 3 ≤ n) (v : ZMod n → ℝ) (hv : ∑ j : ZMod n, v j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j : ZMod n, (v j) ^ 2
      ≤ ∑ j : ZMod n, (v j - v (j + 1)) ^ 2 := by
  have hu : ∑ j : ZMod n, ((v j : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, hv, Complex.ofReal_zero]
  have := energy_lower_bound_complex h3 (fun j => (v j : ℂ)) hu
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using this

end LowerBound

section Eigenvector

variable {n : ℕ} [NeZero n]

/-- The Fiedler eigenvector of the cycle: the real part of the standard additive character. -/
