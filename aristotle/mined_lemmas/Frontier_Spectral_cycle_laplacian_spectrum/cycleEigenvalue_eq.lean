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

open Matrix Finset

/-- The graph Laplacian of the cycle `C n`, as the `n × n` circulant matrix (indexed by
`ZMod n`) with diagonal entries `2` and `-1` on the two cyclic off-diagonals. -/

lemma cycleEigenvalue_eq (k : ZMod n) :
    cycleEigenvalue n k = ((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) := by
  have hk : ((k.val : ℤ) : ZMod n) = k := by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring
  have h1 : ZMod.stdAddChar k
      = Complex.exp ((2 * (Real.pi : ℂ) * (k.val : ℕ) / n) * Complex.I) := by
    conv_lhs => rw [← hk]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have h2 : ZMod.stdAddChar (-k)
      = Complex.exp (-(2 * (Real.pi : ℂ) * (k.val : ℕ) / n) * Complex.I) := by
    conv_lhs => rw [show (-k) = (((-(k.val : ℤ)) : ℤ) : ZMod n) by rw [Int.cast_neg, hk]]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hc := Complex.two_cos ((2 * (Real.pi : ℂ) * (k.val : ℕ) / n))
  rw [cycleEigenvalue, h1, h2]
  push_cast [Complex.ofReal_cos]
  linear_combination hc

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian
of the cycle `C n` are exactly the numbers `2 - 2 cos (2 π k / n)` for `k ∈ Finset.range n`. -/
