import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma w_pow_add_cos (k : ℕ) (hk : k ≤ 20) :
    w ^ k + w ^ (20 - k) = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) := by
  have h1 : w ^ k = Complex.exp ((2 * Real.pi * k / 20 : ℝ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have h2 : w ^ (20 - k) = Complex.exp (-(2 * Real.pi * k / 20 : ℝ) * Complex.I) := by
    rw [pow_sub₀ w w_ne_zero hk, w_pow_20, one_mul, h1, ← Complex.exp_neg]
    ring_nf
  rw [h1, h2, ← Complex.two_cos]
  push_cast
  ring

