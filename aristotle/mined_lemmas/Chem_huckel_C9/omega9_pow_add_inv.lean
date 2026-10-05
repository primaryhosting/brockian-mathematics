import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma omega9_pow_add_inv (k : ℕ) :
    omega9 ^ k + (omega9 ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ) := by
  have h : omega9 ^ k = Complex.exp ((2 * Real.pi * k / 9 : ℝ) * Complex.I) := by
    rw [omega9, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [h, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, ← neg_mul]
  ring

/-- Multiplying a vector by the adjacency matrix of `C₉` sums the two cyclic neighbours. -/
