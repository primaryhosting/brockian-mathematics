import Mathlib
/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/

lemma two_sub_exp_sub_inv (n k : ℕ) :
    (2 : ℂ) - Complex.exp (2 * Real.pi * I * k / n) - (Complex.exp (2 * Real.pi * I * k / n))⁻¹
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / n with hθ
  have hexp : (2 * (Real.pi : ℂ) * I * k / n) = (θ : ℂ) * I := by
    rw [hθ]; push_cast; ring
  have hc : Complex.cos (θ : ℂ) = (Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I)) / 2 := by
    rw [Complex.cos]
  have hinv : (Complex.exp ((θ : ℂ) * I))⁻¹ = Complex.exp (-(θ : ℂ) * I) := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [hexp, hinv]
  push_cast [Complex.ofReal_cos]
  rw [hc]
  ring

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3` the eigenvalues of the graph Laplacian of
the cycle `C n` are exactly `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`. -/
