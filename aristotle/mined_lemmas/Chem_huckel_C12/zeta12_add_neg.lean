import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma zeta12_add_neg (k : ZMod 12) : zeta12 k + zeta12 (-k) = (muC12 k : ℂ) := by
  have hθ : (k.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 12)
      = ((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hz : zeta12 k = Complex.exp (((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta12, w12, ← Complex.exp_nat_mul, hθ]
  have hzinv : zeta12 (-k) = Complex.exp (-((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I) := by
    have h1 : (zeta12 k)⁻¹ = zeta12 (-k) := inv_eq_of_mul_eq_one_right (zeta12_neg_mul k)
    rw [← h1, hz, ← Complex.exp_neg]
    ring_nf
  rw [hz, hzinv, muC12]
  push_cast
  rw [eq_comm, Complex.two_cos]
  ring_nf

