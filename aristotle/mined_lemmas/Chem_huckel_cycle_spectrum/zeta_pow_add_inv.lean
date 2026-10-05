import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma zeta_pow_add_inv {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ k + (zeta n ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  rw [zeta_pow_eq_exp hn k, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, neg_mul]
  ring

/-- The (unnormalized) discrete Fourier matrix: `F j k = ζ^(jk)`. -/
