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

open Matrix Polynomial

variable {n : ℕ} [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `shift n i j = 1` iff `i - j = 1`. -/

lemma root_sum_inv (k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
        + ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k)⁻¹
      = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hpow : (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
      = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.exp_neg, ← neg_mul, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  exact (Complex.two_cos _).symm

/-- Any `n`-th root of unity `ζ` gives an eigenvector `i ↦ ζ ^ i.val` of the cycle Laplacian,
with eigenvalue `2 - (ζ + ζ⁻¹)`. -/
